import Mathlib
import MassGap.ClayCapstone
import MassGap.GeneralDecay

/-!
# The transfer spectral gap at strong coupling

At every `0 < β` with `coreRate 64 β < 1`, the transfer operator of the gauge-invariant theory at the
free-boundary limit state has the Clay spectral form with `ρ = coreRate 64 β`: self-adjoint, vacuum at
the top of the spectrum, the rest of the spectrum in `[0, ρ]` (`wilson_gaugeInv_clay_gap_strong_coupling`).

Every vector orthogonal to the vacuum is the class of an invariant observable `a` with `ν(a) = 0`
(`GNS.mk` is onto; `inner_vacGNS_mk_gaugeInv`). Its form against the `2n`-th transfer power is the
reflected-shifted pairing (`GaugeInvariantAlgebra.gaugeInv_form_pow`), which is the connected pairing
since `ν(S²ⁿ a) = ν(a) = 0`, and `GeneralDecay.nu_connected_shift_abs_le_obs` bounds it by a constant
depending on `a` times `ρ²ⁿ` (`le_div_pow_mul_pow`). `ClayCapstone.absolute_decay_of_form_decay` turns
that into decay of the class (`decay_of_orth`), `SecondEigenvalue.norm_le_of_absolute_iterate_bound`
into `‖Tq y‖ ≤ ρ ‖y‖`, and `ClayCapstone.clay_gap_of_rayleigh` into the spectrum.
-/

namespace MassGap.StrongCouplingGap

open MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.GNSCompare MassGap.ReflectionHalfSpace
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

/-- **Every vector orthogonal to the vacuum decays at rate `coreRate 64 β`.** It is the class of an
invariant observable `a` (`GNS.mk` is onto) with `ν(a) = 0` (`inner_vacGNS_mk_gaugeInv`). The form
of `a` against the `2n`-th transfer power is the reflected-shifted pairing
(`GaugeInvariantAlgebra.gaugeInv_form_pow`), which equals the connected pairing because
`ν(S²ⁿ a) = ν(a) = 0`; `GeneralDecay.nu_connected_shift_abs_le_obs` bounds it beyond its `U`, the
sup norm below it, and `le_div_pow_mul_pow` joins the two into `(C / ρᵁ) ρ²ⁿ`.
`ClayCapstone.absolute_decay_of_form_decay` gives the norm decay.

DERIVED: `16 * 4` is the box touch-degree bound; `2` is the reflection plane's doubling and the even
transfer power; `0` is the coupling's lower end, the excluded rank and the vacuum pairing; `1` is the
geometric threshold and the identity boundary configuration. -/
theorem decay_of_orth (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 < β) (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (y : GNS (Dg τ p ν hinv hpos hnu).toReflForm)
    (hy : (inner ℝ (Dg τ p ν hinv hpos hnu).vacGNS y : ℝ) = 0) :
    ∃ K : ℝ, ∀ n : ℕ, ‖((Dg τ p ν hinv hpos hnu).Tq ^ n) y‖
      ≤ K * MassGap.StrongCoupling.coreRate (16 * 4) β ^ n := by
  classical
  have hρ0 : 0 < MassGap.StrongCoupling.coreRate (16 * 4) β := coreRate_pos _ hβ
  obtain ⟨a, rfl⟩ : ∃ a, GNS.mk (Dg τ p ν hinv hpos hnu).toReflForm a = y :=
    Submodule.Quotient.mk_surjective _ y
  have hmean : ν (a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) = 0 := by
    rw [← inner_vacGNS_mk_gaugeInv τ p ν hinv hpos hnu a]; exact hy
  obtain ⟨S, hS, hloc⟩ := (Submodule.mem_inf.mp a.2).1
  obtain ⟨U, hU⟩ := MassGap.GeneralDecay.nu_connected_shift_abs_le_obs hN hβ.le τ p ν htend hr
    (a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) hS hloc
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = max (MassGap.StrongCoupling.coreConstG
      (2 * (‖(a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖
        * ‖(a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖)) (16 * 4) β U)
      (‖(a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖
        * ‖(a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))‖) := ⟨_, rfl⟩
  have hC : 0 ≤ Cm := by
    rw [hCm]; exact le_trans (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (le_max_right _ _)
  refine absolute_decay_of_form_decay (Dg τ p ν hinv hpos hnu) a hρ0.le
    (K := Cm / MassGap.StrongCoupling.coreRate (16 * 4) β ^ U) (fun n => ?_)
  have hform := MassGap.GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν hinv hpos hnu a (2 * n)
  have hshift : ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[2 * n]
      (a : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))) = 0 := by
    rw [MassGap.GaugeInvariantAlgebra.state_iterate_shift_eq ν τ hnu]; exact hmean
  rw [hform]
  refine le_div_pow_mul_pow hρ0 hr.le hC (fun hj => ?_) ?_
  · have h := hU (2 * n) hj
    rw [hshift, mul_zero, sub_zero] at h
    exact le_trans (le_abs_self _) (le_trans h
      (mul_le_mul_of_nonneg_right (hCm ▸ le_max_left _ _) (pow_nonneg hρ0.le _)))
  · refine le_trans (le_abs_self _) (le_trans (ν.abs_le_norm _) ?_)
    refine le_trans (norm_mul_le _ _) (le_trans ?_ (hCm ▸ le_max_right _ _))
    exact mul_le_mul (MassGap.WilsonTransferReduction.norm_ireflObs_le τ (2 * p) _)
      (MassGap.GeneralDecay.norm_iterate_ishiftObsL_le τ _ (2 * n)) (norm_nonneg _) (norm_nonneg _)

#print axioms decay_of_orth

/-- **Every vector orthogonal to the vacuum is contracted by `ρ = coreRate 64 β`**:
`‖Tq y‖ ≤ ρ ‖y‖`. `decay_of_orth` and `SecondEigenvalue.norm_le_of_absolute_iterate_bound`. This is M
stated per state: one transfer step lowers every state orthogonal to the vacuum by at least
`Δ = −log ρ`.

DERIVED: `16 * 4` is the box touch-degree bound; `2` is the reflection plane's doubling and the
density's ceiling; `0` is the coupling's lower end, the excluded rank and the vacuum pairing; `1` is
the geometric threshold and the identity boundary configuration. -/
theorem norm_Tq_le_of_orth (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 < β) (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (y : GNS (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm)
    (hy : (inner ℝ (wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0) :
    ‖(wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq y‖
      ≤ MassGap.StrongCoupling.coreRate (16 * 4) β * ‖y‖ := by
  have hinv := wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
  have hpos := wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
  have hnu := wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
    (tendsto_symCube_odd_of_mixCube τ p hN β ν htend)
  obtain ⟨K, hK⟩ := decay_of_orth τ p hN hβ hr ν htend hinv hpos hnu y hy
  exact MassGap.SecondEigenvalue.norm_le_of_absolute_iterate_bound
    (wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq
    (wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq_isSymmetric (coreRate_pos _ hβ).le hK

#print axioms norm_Tq_le_of_orth

/-- **The transfer spectral gap at strong coupling.** At `N ≠ 0`, `0 < β` with
`coreRate 64 β < 1`, and `ν` the `atTop` limit of the free box states along `mixCube`, the transfer
operator of the gauge-invariant data is self-adjoint with spectrum in `{1} ∪ [0, ρ]`,
`ρ = coreRate 64 β`, and `1` at the top: a gap `Δ = −log ρ > 0`.

Every vector `y` orthogonal to the vacuum decays at `ρ` (`decay_of_orth`), so
`‖Tq y‖ ≤ ρ ‖y‖` (`SecondEigenvalue.norm_le_of_absolute_iterate_bound`) and, by Cauchy–Schwarz,
`⟪Tq y, y⟫ ≤ ρ ‖y‖²`; `ClayCapstone.clay_gap_of_rayleigh` takes that Rayleigh ceiling on the vacuum
complement to the spectrum.

DERIVED: `16 * 4` is the box touch-degree bound; `4` is the spacetime dimension; `2` is the doubling
of the reflection plane and the density's ceiling; `0` is the coupling's lower end, the excluded rank
and the spectrum's bottom; `1` is the vacuum eigenvalue, the geometric threshold and the identity
boundary configuration. -/
theorem wilson_gaugeInv_clay_gap_strong_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 < β) (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    IsSelfAdjoint (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
      ∧ 0 < -Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β)
      ∧ spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β))))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))) 1 := by
  have hinv := wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
  have hpos := wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
  have hnu := wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
    (tendsto_symCube_odd_of_mixCube τ p hN β ν htend)
  have hρ0 := coreRate_pos (16 * 4) hβ
  refine clay_gap_of_rayleigh (wilsonGaugeInvMixCubeData τ p hN β ν htend) hρ0 hr
    (MassGap.GaugeInvariantAlgebra.positiveTransfer_gaugeInv τ p ν hinv hpos hnu
      (wilson_positiveTransfer_of_mixCube_limit τ p hN hβ.le ν htend)) (fun y hy => ?_)
  obtain ⟨K, hK⟩ := decay_of_orth τ p hN hβ hr ν htend hinv hpos hnu y hy
  have hn := MassGap.SecondEigenvalue.norm_le_of_absolute_iterate_bound
    (wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq
    (wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq_isSymmetric hρ0.le hK
  calc (inner ℝ ((wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq y) y : ℝ)
      ≤ ‖(wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq y‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ (MassGap.StrongCoupling.coreRate (16 * 4) β * ‖y‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = MassGap.StrongCoupling.coreRate (16 * 4) β * ‖y‖ ^ 2 := by ring

#print axioms wilson_gaugeInv_clay_gap_strong_coupling

end MassGap.StrongCouplingGap
