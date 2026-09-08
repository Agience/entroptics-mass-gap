import MassGap.WilsonReal
import MassGap.HaarMoments

/-!
# MassGap.InteractingTwoPoint — the first non-factorizing correlation on the interacting lattice

The interacting system `WilsonReal.sysInt` has two plaquettes that **share link 3** (`hol₀ = C₀·U₃⁻¹`,
`hol₁ = U₃·C₁`, with `C₀ = U₀U₁U₂⁻¹`, `C₁ = U₄U₅⁻¹U₆⁻¹` the other-link environments). Integrating out the
shared link couples them:
$$ \int_{SU(2)} \operatorname{tr}(\mathrm{hol}_0)\,\operatorname{tr}(\mathrm{hol}_1)\, dU_3
   = \tfrac12 \operatorname{tr}(C_0 C_1), $$
generically nonzero — while the product of the two marginals is `0` (each `∫ tr(g·C) = tr((∫g)C) = 0`).
This is the first genuinely **non-factorizing** correlation on the actual interacting lattice, reduced to
the machine-checked SU(2) two-point engine `HaarMoments.haar_su2_shared_link` (Schur orthogonality, no
Peter–Weyl). It is the connected-two-point mechanism `⟨φ_p φ_q⟩_c ≠ 0` whose exponential-in-separation
version is the mass gap. Foundational footprint. Build: `lake build MassGap.InteractingTwoPoint`.
-/

namespace MassGap.WilsonReal

open MassGap.SUN MassGap.WilsonLattice MeasureTheory MassGap.CompactGauge Matrix

/-- Plaquette-0 environment (its links other than the shared link 3): `U₀·U₁·U₂⁻¹`. -/
noncomputable def envC0 (U : Fin 7 → G2) : G2 := U 0 * U 1 * (U 2)⁻¹
/-- Plaquette-1 environment: `U₄·U₅⁻¹·U₆⁻¹`. -/
noncomputable def envC1 (U : Fin 7 → G2) : G2 := U 4 * (U 5)⁻¹ * (U 6)⁻¹

/-- Plaquette 0's holonomy factors as `C₀ · (shared link)⁻¹`. -/
theorem hol0_factor (U : Fin 7 → G2) (g : SU 2) :
    wilsonHol bdInt 0 (Function.update U 3 g) = envC0 U * g⁻¹ := by
  have hb : bdInt 0 = [(0, true), (1, true), (2, false), (3, false)] := rfl
  simp only [wilsonHol, hb, envC0, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, if_false, Bool.false_eq_true, Function.update_self,
    Function.update_of_ne (show (0 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (1 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (2 : Fin 7) ≠ 3 by decide)]
  group

/-- Plaquette 1's holonomy factors as `(shared link) · C₁`. -/
theorem hol1_factor (U : Fin 7 → G2) (g : SU 2) :
    wilsonHol bdInt 1 (Function.update U 3 g) = g * envC1 U := by
  have hb : bdInt 1 = [(3, true), (4, true), (5, false), (6, false)] := rfl
  simp only [wilsonHol, hb, envC1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, if_false, Bool.false_eq_true, Function.update_self,
    Function.update_of_ne (show (4 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (5 : Fin 7) ≠ 3 by decide),
    Function.update_of_ne (show (6 : Fin 7) ≠ 3 by decide)]
  group

/-- **The interacting shared-link two-point on `sysInt`: `∫ tr(hol₀)·tr(hol₁) dU₃ = ½ tr(C₀·C₁)`.**
Integrating out the shared link `3` couples the two plaquettes through their environments `C₀, C₁` — the
first genuinely non-factorizing correlation on the actual interacting lattice (the product of marginals is
`0`; the joint is `½ tr(C₀C₁)`, precisely because the plaquettes share the link). Via
`HaarMoments.haar_su2_shared_link`, all foundational, no Peter–Weyl. -/
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
