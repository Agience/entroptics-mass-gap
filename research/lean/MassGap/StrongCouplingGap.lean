import Mathlib
import MassGap.ClayCapstone
import MassGap.StrongCoupling

/-!
# Strong-coupling rate lemmas for the gauge-invariant transfer data

Every vector orthogonal to the vacuum is the class of an invariant observable `a` with `ν(a) = 0`
(`GNS.mk` is onto; `inner_vacGNS_mk_gaugeInv` gives the vacuum pairing `⟪Ω, [a]⟫ = ν(a)`). Its form
against the `2n`-th transfer power is the reflected-shifted pairing
(`GaugeInvariantAlgebra.gaugeInv_form_pow`). This module holds the rate bookkeeping for a bound of the
shape `C ρ^(j + 2 − U)` (`le_div_pow_mul_pow`), the positivity of `coreRate K β` at positive coupling
(`coreRate_pos`), and the gauge-invariant transfer data `Dg`.
-/

namespace MassGap.StrongCouplingGap

open MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.GNSCompare
open MassGap.ClayCapstone

/-- **A bound `C ρ^(j + 2 − U)` beyond `U` and `C` below it is a bound `(C / ρ^U) ρ^j` everywhere**,
for `0 < ρ ≤ 1`.

DERIVED: the `2` is the offset of the bound's exponent, the two base plaquettes of the cluster bound;
the `0` and `1` bound `ρ`. -/
theorem le_div_pow_mul_pow {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {C v : ℝ} (hC : 0 ≤ C) {U j : ℕ}
    (hbig : U ≤ j + 2 → v ≤ C * ρ ^ (j + 2 - U)) (hsmall : v ≤ C) :
    v ≤ C / ρ ^ U * ρ ^ j := by
  have hU : 0 < ρ ^ U := pow_pos hρ0 U
  have hUi : 0 ≤ (ρ ^ U)⁻¹ := inv_nonneg.mpr hU.le
  by_cases hj : U ≤ j + 2
  · have e : ρ ^ (j + 2) = ρ ^ (j + 2 - U) * ρ ^ U := by rw [← pow_add, Nat.sub_add_cancel hj]
    have hle : ρ ^ (j + 2) ≤ ρ ^ j :=
      MassGap.StrongCoupling.pow_le_pow_of_le_one_asm hρ0.le hρ1 (by omega)
    have e2 : ρ ^ (j + 2 - U) = ρ ^ (j + 2) * (ρ ^ U)⁻¹ := by
      rw [e, mul_assoc, mul_inv_cancel₀ hU.ne', mul_one]
    calc v ≤ C * ρ ^ (j + 2 - U) := hbig hj
      _ = C * (ρ ^ (j + 2) * (ρ ^ U)⁻¹) := by rw [e2]
      _ ≤ C * (ρ ^ j * (ρ ^ U)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hUi) hC
      _ = C / ρ ^ U * ρ ^ j := by rw [div_eq_mul_inv]; ring
  · have hle : ρ ^ U ≤ ρ ^ j :=
      MassGap.StrongCoupling.pow_le_pow_of_le_one_asm hρ0.le hρ1 (by omega)
    have h1 : 1 ≤ ρ ^ j * (ρ ^ U)⁻¹ := by
      rw [← div_eq_mul_inv]; exact (one_le_div hU).mpr hle
    calc v ≤ C := hsmall
      _ = C * 1 := by ring
      _ ≤ C * (ρ ^ j * (ρ ^ U)⁻¹) := mul_le_mul_of_nonneg_left h1 hC
      _ = C / ρ ^ U * ρ ^ j := by rw [div_eq_mul_inv]; ring

#print axioms le_div_pow_mul_pow

/-- `coreRate K β` is positive at positive coupling: every factor is.

DERIVED: the `0` is the coupling's lower end and the rate's. -/
theorem coreRate_pos (K : ℕ) {β : ℝ} (hβ : 0 < β) : 0 < MassGap.StrongCoupling.coreRate K β := by
  unfold MassGap.StrongCoupling.coreRate
  have h : 0 < Real.exp (2 * β) - 1 := by
    have := Real.add_one_le_exp (2 * β)
    linarith
  positivity

#print axioms coreRate_pos

variable {N : ℕ}

/-- The gauge-invariant transfer data at a state with the three state facts, named for the lemmas
below. `GaugeInvariantAlgebra.gaugeInvTransferData` at `SU N`.

DERIVED: `2` is the reflection plane's doubling; `4` is the dimension. -/
noncomputable abbrev Dg (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) :=
  MassGap.GaugeInvariantAlgebra.gaugeInvTransferData (G := MassGap.SUN.SU N) τ p ν hinv hpos hnu

/-- **The vacuum pairs with a class as the state does with its observable**:
`⟪Ω, [a]⟫ = ν(a)` at the gauge-invariant data. `TransferAssembly.inner_vacGNS_mk` with the data's
own arguments.

DERIVED: `2` is the reflection plane's doubling; `4` is the dimension. -/
theorem inner_vacGNS_mk_gaugeInv (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (a : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p)) :
    (inner ℝ (Dg τ p ν hinv hpos hnu).vacGNS (GNS.mk (Dg τ p ν hinv hpos hnu).toReflForm a) : ℝ)
      = ν (a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :=
  MassGap.TransferAssembly.inner_vacGNS_mk
    (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν
    (MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p) hinv
    (MassGap.GaugeInvariantAlgebra.reflPositiveOn_gaugeInv τ p hpos)
    (MassGap.WilsonTransferReduction.shiftCompat_of_nu_T τ (2 * p) ν hnu)
    (fun _ hf => MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg_shift_stable τ p hf)
    (MassGap.GaugeInvariantAlgebra.one_mem_gaugeInvHalfSpaceAlg τ p)
    (MassGap.WilsonTransferReduction.ishiftObsL_one τ)
    (MassGap.WilsonTransferReduction.norm_ishiftObsL_le τ)
    (MassGap.WilsonTransferReduction.norm_ireflObs_le τ (2 * p)) a

#print axioms inner_vacGNS_mk_gaugeInv

end MassGap.StrongCouplingGap
