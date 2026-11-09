import Mathlib
import MassGap.EnergySeed
import MassGap.ApertureVolume

/-!
# MassGap.ApertureOne — the far input as dimming of the finite-size action

`ApertureVolume.clay_two` takes `NearWin` (near) and `ApertureBridge.PhysDefect L (1/1000)` (far). The defect is
the integral of the finite-size part of the mean action, `defectW N β n = ∫₀^β finiteSize N n`
(`EnergySeed.hasDerivAt_defectW'`, `EnergySeed.defectW_zero`), and `finiteSize = ⟨S⟩_{2n} − 16 ⟨S⟩_n` is the
volume times the shift of the plaquette one-point function between the side-`n` and side-`2n` tori. This module
reads `PhysDefect` as a dimming statement and states which dimming gives it and which does not.

## Dimming in the coupling distance gives the defect

At the physical side `n = 2^{kPhys L β + 2}` the side-`n` torus at a coupling `x < β` has physical side
`n · aRun 2 x`, larger than `L/2` by the factor `aRun 2 x / aRun 2 β`, which grows like `e^{(6π²/11)(β − x)}`. The
coupling distance `β − x` is the logarithmic distance of that torus beyond the reading scale.

* `defectW_le_of_dim`: at one side `n`, `finiteSize N n x ≤ A e^{−γ(β − x)}` on `[0, β)` with `0 < γ` gives
  `defectW N β n ≤ A/γ`.
* `DimFar L A γ`: eventually in `β`, at the physical side, that bound holds on `[0, β)`.
* `physDefect_of_dimFar`: `A/γ ≤ δ` and `DimFar L A γ` give `PhysDefect L δ`.
* `clay_two_dim`: `clay_two` with `DimFar L A γ`, `A/γ ≤ 1/1000`, as the far input.

## A finite-size part that does not dim excludes the defect

* `defectW_nonneg_pow`: `0 ≤ defectW 2 x (2^{m+2})` at every `x ≥ 0` (`ApertureWindow.stepD_nonneg`).
* `not_physDefect_of_coulomb`: a Coulomb-type finite-size part uniform in the side, `κ/x ≤ finiteSize 2 n x`
  for every `n` and every `x ≥ a > 0`, with `κ > 0`, excludes `PhysDefect L δ` at every `L` and every `δ`:
  `EnergySeed.defectW_log_growth` at the side `2^{kPhys L β + 2}` gives `defect ≥ κ (log β − log a)`.
* `not_dimFar_of_coulomb`: so it excludes `DimFar L A γ` at every `A/γ`.

The Coulomb form is the Gaussian count of a massless spectrum: `G`-valued Gaussian modes give
`finiteSize ≈ (dim G)·45/(2x)` (`EnergySeed` module docstring), at every side when nothing gives the modes a mass.

## What this says about one bridge

`NearWin`'s one-point content at one field is the square of the torus-minus-vacuum one-point shift,
`a⁸ (⟨O⟩_T − ⟨O⟩_∞)² ≤ C a⁸ R_∞`: a shift of the size of the reading, with one constant `C` for every torus
extent `≥ M₀ 2ᵏ`. The defect reads the shift times the volume `(L/a)⁴`, integrated over the couplings `[0, β]`.
At the free unit the one-point shift of a dimension-`Δ` field relative to its reading dims like `(a/L)^Δ`
(argued; the script measures `φ²`, `Δ = 2`, falling like `n⁻²`), and for the action density (`Δ = 4`) the
volume returns the factor `(L/a)⁴`: the product is scale-free (`κ/x` per unit coupling), and its integral over the window of
couplings at which the torus stays below the correlation length is `κ log(1/g²(L))`, a pure number of order
`dim G`. `PhysDefect L (1/1000)` needs that number below `1/1000`: the finite-size free energy of the torus of
side `L` must dim in `L/ξ`, which is the mass gap at the scale `L`. `DimFar` is that statement in coupling form;
`not_physDefect_of_coulomb` is its converse at the massless unit. A one-point bound relative to the reading with
a constant that dims in `L/s₀` is satisfied by the massless unit and does not give `PhysDefect`. The near and far
inputs read different quantities: local readings of the torus states at the couplings `dyBeta k` (UV and volume
control), and the volume-weighted one-point shift integrated over all couplings below `β` (the gap).

DERIVED (module-wide): `2` the gauge group `SU(2)` and the doubling; `16 = 2⁴` the copies; `0` the coupling at
which the defect vanishes; `1` the least `j` of `ApertureWindow.stepD_nonneg`; `2` in `kPhys + 2` from
`ApertureBridge.PhysDefect`; `8, 4, 2, 1` from `ApertureNearAll.defectW_eq`; `1/1000` the `RunSeed` threshold.
-/

noncomputable section

namespace MassGap.ApertureOne

open Real Filter Set MassGap MassGap.EnergySeed MassGap.PhysicalScaleSmall

variable {N : ℕ}

/-! ## 1. Dimming in the coupling distance -/

section Dim

/-- **The defect from a finite-size part that dims in the coupling distance.** -/
theorem defectW_le_of_dim (hN : N ≠ 0) {n : ℕ} {β A γ : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A) (hγ : 0 < γ)
    (h : ∀ x ∈ Ico 0 β, finiteSize N n x ≤ A * Real.exp (-γ * (β - x))) :
    ZoomSelfScale.defectW N β n ≤ A / γ := by
  have hd : ∀ x ∈ Icc (0 : ℝ) β,
      HasDerivAt (fun y => A / γ * (Real.exp (-γ * (β - y)) - Real.exp (-γ * β)))
        (A * Real.exp (-γ * (β - x))) x := fun x _ => by
    have h1 : HasDerivAt (fun y => -γ * (β - y)) (-γ * (-1)) x :=
      ((hasDerivAt_id x).const_sub β).const_mul (-γ)
    have h2 := ((h1.exp).sub_const (Real.exp (-γ * β))).const_mul (A / γ)
    refine h2.congr_deriv ?_
    field_simp
  have hb := defectW_le_of_budget hN
    (Φ := fun y => A / γ * (Real.exp (-γ * (β - y)) - Real.exp (-γ * β)))
    (φ := fun x => A * Real.exp (-γ * (β - x))) (by rw [defectW_zero]; simp) hd h β ⟨hβ, le_rfl⟩
  have he : 0 ≤ Real.exp (-γ * β) := (Real.exp_pos _).le
  have hq : 0 ≤ A / γ := div_nonneg hA hγ.le
  simp only [sub_self, mul_zero, Real.exp_zero] at hb
  nlinarith

/-- **The far input as dimming**: eventually in `β`, at the physical side and every coupling below `β`, the
finite-size part of the mean action is at most `A e^{−γ(β − x)}`. -/
def DimFar (L A γ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ x ∈ Ico 0 β, finiteSize 2 (2 ^ (kPhys L β + 2)) x ≤ A * Real.exp (-γ * (β - x))

/-- **Dimming gives the physical-side defect.** -/
theorem physDefect_of_dimFar {L A γ δ : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) (hδ : A / γ ≤ δ)
    (h : DimFar L A γ) : ApertureBridge.PhysDefect L δ := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hx hβ
  exact (defectW_le_of_dim (N := 2) (by norm_num) hβ hA hγ hx).trans hδ

open MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumCluster
  MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint MassGap.TorusCapstone in
/-- **The capstone with the far input as dimming.** -/
theorem clay_two_dim (hN : (2 : ℕ) ≠ 0) {M₀ : ℕ} {s₀ L A γ : ℝ} (hs₀ : 0 < s₀)
    (h8 : 8 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hNear : ApertureVolume.NearWin hN (dyBeta (one_le_of_ne_zero hN)) M₀ s₀)
    (hA : 0 ≤ A) (hγ : 0 < γ) (hAγ : A / γ ≤ 1 / 1000) (hF : DimFar L A γ) :
    ∃ hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ClayRoutes.ClayContinuumPair hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
          (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)
          (ContinuumSep.pairBoundSep_of_diagBoundSep hN
            (Renorm.connected hN (ExistenceReduceOwn.zOwn hN s₀ s₀)) 0
            (Renorm.connected_reflCompat hN (ExistenceReduceOwn.zOwn hN s₀ s₀) 0
              (ExistenceReduceOwn.zOwn_refl hN s₀ s₀)) hD) (5 * ℓ₀) :=
  ApertureVolume.clay_two hN hs₀ h8 hL hNear (physDefect_of_dimFar hA hγ hAγ hF)

end Dim

/-! ## 2. The massless obstruction -/

section Coulomb

/-- **The Wilson defect at a dyadic side `2^{m+2}` is nonnegative at every coupling `x ≥ 0`.** -/
theorem defectW_nonneg_pow (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ ZoomSelfScale.defectW 2 x (2 ^ (m + 2)) := by
  have e : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
  rw [ApertureNearAll.defectW_eq, e]
  linarith [ApertureWindow.stepD_nonneg 0 hx (Nat.one_le_two_pow (n := m + 1)),
    ApertureWindow.stepD_nonneg 1 hx (Nat.one_le_two_pow (n := m + 1)),
    ApertureWindow.stepD_nonneg 2 hx (Nat.one_le_two_pow (n := m + 1)),
    ApertureWindow.stepD_nonneg 3 hx (Nat.one_le_two_pow (n := m + 1))]

/-- **A Coulomb-type finite-size part uniform in the side excludes the physical-side defect.** -/
theorem not_physDefect_of_coulomb {L δ κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (h : ∀ (n : ℕ), 1 ≤ n → ∀ (x : ℝ), a ≤ x → κ * x⁻¹ ≤ finiteSize 2 n x) :
    ¬ ApertureBridge.PhysDefect L δ := by
  intro hP
  obtain ⟨β, hD, haβ, hlog⟩ := (hP.and ((eventually_ge_atTop a).and
    (Real.tendsto_log_atTop.eventually_gt_atTop (Real.log a + δ / κ)))).exists
  have hg := defectW_log_growth (N := 2) (by norm_num) (n := 2 ^ (kPhys L β + 2)) ha haβ
    (fun x hx => h _ Nat.one_le_two_pow x hx.1)
  have h0 := defectW_nonneg_pow (kPhys L β) ha.le
  have hk : δ < κ * (Real.log β - Real.log a) := by
    have h1 : δ / κ < Real.log β - Real.log a := by linarith
    rwa [div_lt_iff₀ hκ, mul_comm] at h1
  linarith

/-- **So it excludes the dimming far input at every `A/γ`.** -/
theorem not_dimFar_of_coulomb {L A γ κ a : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) (hκ : 0 < κ) (ha : 0 < a)
    (h : ∀ (n : ℕ), 1 ≤ n → ∀ (x : ℝ), a ≤ x → κ * x⁻¹ ≤ finiteSize 2 n x) : ¬ DimFar L A γ := fun hF =>
  not_physDefect_of_coulomb hκ ha h (physDefect_of_dimFar hA hγ le_rfl hF)

end Coulomb

end MassGap.ApertureOne

end

#print axioms MassGap.ApertureOne.defectW_le_of_dim
#print axioms MassGap.ApertureOne.physDefect_of_dimFar
#print axioms MassGap.ApertureOne.clay_two_dim
#print axioms MassGap.ApertureOne.defectW_nonneg_pow
#print axioms MassGap.ApertureOne.not_physDefect_of_coulomb
#print axioms MassGap.ApertureOne.not_dimFar_of_coulomb
