import MassGap.WilsonReal
import MassGap.HaarMoments

/-!
# MassGap.InteractingTwoPoint — the shared-link two-point identity on `WilsonReal.sysInt`

The interacting system `WilsonReal.sysInt` carries seven links, `U : Fin 7 → G2`, and two plaquettes
whose boundaries both contain link `3`:

    bdInt 0 = [(0, true), (1, true), (2, false), (3, false)]
    bdInt 1 = [(3, true), (4, true), (5, false), (6, false)]

Writing `C₀ = U₀U₁U₂⁻¹` (`envC0`) and `C₁ = U₄U₅⁻¹U₆⁻¹` (`envC1`) for the two environments — the
links of each plaquette other than the shared one — the holonomies factor as `hol₀ = C₀ g⁻¹` and
`hol₁ = g C₁` when link `3` carries `g`. `hol0_factor` and `hol1_factor` state those factorisations.

`sysInt_shared_link_two_point` then integrates the product of the two traces over the shared link
against normalised Haar measure on `SU(2)`:

    ∫ tr(hol₀) · tr(hol₁) dU₃ = ½ · tr(C₀ C₁),

the right-hand side depending on the two environments only through their matrix product. The
`SU(2)` integral is discharged by `HaarMoments.haar_su2_shared_link`, which is proved from Schur
orthogonality rather than Peter–Weyl.

Scope: colour group `SU(2)`, this fixed seven-link configuration and this pair of plaquettes. The
identity is an equality of complex numbers; nothing here asserts that either side is nonzero, and
the product of the two separate marginals is not computed in this file. Every declaration is
checked with `#print axioms`.

DERIVED: `7` is the link count of `sysInt`; `0`–`6` are link indices and `0`, `1` plaquette indices;
`2` in `SU 2` and `Fin 2` is the colour count; `½` is `1/dim` for the defining representation of
`SU(2)`, the constant `haar_su2_shared_link` returns.

Build: `lake build MassGap.InteractingTwoPoint`.
-/

namespace MassGap.WilsonReal

open MassGap.SUN MassGap.WilsonLattice MeasureTheory MassGap.CompactGauge Matrix

/-- Plaquette `0`'s environment: the product of its links other than the shared link `3`, with the
orientations `bdInt 0` gives them, `U₀ · U₁ · U₂⁻¹`.

DERIVED: `7` is the link count of `sysInt`; `0`, `1`, `2` are link indices. -/
noncomputable def envC0 (U : Fin 7 → G2) : G2 := U 0 * U 1 * (U 2)⁻¹
/-- Plaquette `1`'s environment: the product of its links other than the shared link `3`, with the
orientations `bdInt 1` gives them, `U₄ · U₅⁻¹ · U₆⁻¹`.

DERIVED: `7` is the link count of `sysInt`; `4`, `5`, `6` are link indices. -/
noncomputable def envC1 (U : Fin 7 → G2) : G2 := U 4 * (U 5)⁻¹ * (U 6)⁻¹

/-- Plaquette `0`'s holonomy, with link `3` overwritten by `g`, equals `envC0 U * g⁻¹`. Proved by
unfolding `wilsonHol` along `bdInt 0 = [(0, true), (1, true), (2, false), (3, false)]`, where the
shared link occurs last and with reversed orientation.

DERIVED: `7` is the link count of `sysInt`; `2` in `SU 2` is the colour count; `0` is the plaquette
index and `3` the shared link index. -/
theorem hol0_factor (U : Fin 7 → G2) (g : SU 2) :
    wilsonHol bdInt 0 (Function.update U 3 g) = envC0 U * g⁻¹ := by
  have hb : bdInt 0 = [(0, true), (1, true), (2, false), (3, false)] := rfl
  simp only [wilsonHol, hb, envC0, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, if_false, Bool.false_eq_true, Function.update_self,
    Function.update_of_ne (show (0 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (1 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (2 : Fin 7) ≠ 3 by decide)]
  group

/-- Plaquette `1`'s holonomy, with link `3` overwritten by `g`, equals `g * envC1 U`. Proved by
unfolding `wilsonHol` along `bdInt 1 = [(3, true), (4, true), (5, false), (6, false)]`, where the
shared link occurs first and with forward orientation.

DERIVED: `7` is the link count of `sysInt`; `2` in `SU 2` is the colour count; `1` is the plaquette
index and `3` the shared link index. -/
theorem hol1_factor (U : Fin 7 → G2) (g : SU 2) :
    wilsonHol bdInt 1 (Function.update U 3 g) = g * envC1 U := by
  have hb : bdInt 1 = [(3, true), (4, true), (5, false), (6, false)] := rfl
  simp only [wilsonHol, hb, envC1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, if_false, Bool.false_eq_true, Function.update_self,
    Function.update_of_ne (show (4 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (5 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (6 : Fin 7) ≠ 3 by decide)]
  group

/-- The shared-link two-point identity on `sysInt`. For every configuration `U : Fin 7 → G2`, the
Haar integral over `g : SU 2` of `tr(hol₀(U[3 ↦ g])) · tr(hol₁(U[3 ↦ g]))` equals
`(1 / 2) * tr(envC0 U * envC1 U)`, an equality in `ℂ` between traces of `Matrix (Fin 2) (Fin 2) ℂ`.
Obtained by rewriting with `hol0_factor` and `hol1_factor` and applying
`HaarMoments.haar_su2_shared_link` to the two environments, so no Peter–Weyl theorem is used.

Only the shared link is integrated; the remaining six links stay free in `U`, and the right-hand
side sees the two environments only through the product `envC0 U * envC1 U`. The statement is an
identity: it makes no claim that either side is nonzero, and it does not compute the two separate
marginals.

DERIVED: `7` is the link count of `sysInt`; `2` in `SU 2` and in `Fin 2` is the colour count; `0`
and `1` are plaquette indices and `3` the shared link index; `1 / 2` is the `1 / dim` of Schur
orthogonality for the defining representation of `SU(2)`, supplied by `haar_su2_shared_link`. -/
theorem sysInt_shared_link_two_point (U : Fin 7 → G2) :
    ∫ g : SU 2, Matrix.trace ((wilsonHol bdInt 0 (Function.update U 3 g) : G2)
          : Matrix (Fin 2) (Fin 2) ℂ)
        * Matrix.trace ((wilsonHol bdInt 1 (Function.update U 3 g) : G2)
          : Matrix (Fin 2) (Fin 2) ℂ) ∂(probHaar (SU 2))
      = (1 / 2 : ℂ) * Matrix.trace ((envC0 U : Matrix (Fin 2) (Fin 2) ℂ)
          * (envC1 U : Matrix (Fin 2) (Fin 2) ℂ)) := by
  simp_rw [hol0_factor, hol1_factor]
  have e0 : ∀ g : SU 2, ((envC0 U * g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) ℂ)
      = (envC0 U : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) :=
    fun g => by rw [Submonoid.coe_mul]; rfl
  have e1 : ∀ g : SU 2, ((g * envC1 U : G2) : Matrix (Fin 2) (Fin 2) ℂ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * (envC1 U : Matrix (Fin 2) (Fin 2) ℂ) :=
    fun g => by rw [Submonoid.coe_mul]
  simp_rw [e0, e1]
  exact haar_su2_shared_link (envC0 U : Matrix (Fin 2) (Fin 2) ℂ)
    (envC1 U : Matrix (Fin 2) (Fin 2) ℂ)

#print axioms sysInt_shared_link_two_point

end MassGap.WilsonReal
