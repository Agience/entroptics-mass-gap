import Mathlib
import MassGap.TwistedTraceBoundN
import MassGap.CentreSectorSeed

/-!
# MassGap.SliceCentreAction — the centre `Z_N³` acting on every slice of a rectangular torus

Fix a transfer direction `μ` and transverse extents `T`. A slice configuration assigns an `SU(N)`
element to each spatial link `(ν, y)`, `ν ≠ μ`. The centre of `SU(N)` placed on the three transverse
directions, `G = Z_N³ = ({ν // ν ≠ μ} → Z_N)`, acts on slices: `g` multiplies every link in direction
`ν` whose `ν`-coordinate is `0` by the centre element `e(g ν) = exp(2πi g ν / N)`.

* `kT_act`: the action preserves the transfer kernel. A spatial plaquette meets the multiplied links
  of a direction in two opposite links or none, so its phases cancel (`plaq_phase`); a temporal
  plaquette meets them in its two spatial links, whose phases are conjugate.
* `centreAction`: it is a measure-preserving action of `Z_N³` on Haar measure
  (`FluxSectorFourier.CentreAction`).
* `card_cen`: `|G| = N³`.

So every step `i` of the corner path, whose slice is transverse to direction `i` with extents
`CentreSectorSeed.Tr n i`, carries the action, with its three transverse directions. The insertion of
`act g` at one time slice twists the time–space planes `(μ, ν)` by `e(g ν)` ('t Hooft's twist).
For `N = 2` and `g` a basis vector it multiplies by `−1` the links that
`CentreSectorSeed.centreFlip` multiplies; on the step-`0` slice with `g` vanishing on direction `3`
it multiplies the links that `TwistedTraceBoundN.act` multiplies, by the same phases.

The statements hold for every `N ≥ 1`. For `U(1)` the same action is a symmetry, with the full circle
in place of `Z_N`; the statements here are about the finite centre.

DERIVED (module-wide): `0` is the coordinate whose links are multiplied; `3` is the number of
transverse directions (`CentreSectorSeed.card_transverse`).
-/

noncomputable section

namespace MassGap.SliceCentreAction

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower
open MassGap.TwistedTraceBoundN (cz coe_cz cz_add cz_zero ee_mul_star smul_plaq smul_plaq_time
  wd_congr coe_inv)

/-- `e(k) = exp(2πik/N)`. -/
local notation "ee" => ZMod.stdAddChar

/-- **The centre on the three transverse directions**: `Z_N³`. -/
abbrev Cen (μ : Fin 4) (N : ℕ) : Type := {j : Fin 4 // j ≠ μ} → ZMod N

/-- Slice configurations. -/
abbrev Cfg (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (N : ℕ) : Type := SpT μ T → SUN.SU N

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-- The charge carried by a link: the phase of its direction if its own coordinate is `0`. -/
def lc (g : Cen μ N) (l : SpT μ T) : ZMod N := if (l.2 l.1).val = 0 then g l.1 else 0

theorem lc_add (g h : Cen μ N) (l : SpT μ T) : lc (g + h) l = lc g l + lc h l := by
  unfold lc; split_ifs <;> simp

theorem lc_zero (l : SpT μ T) : lc (0 : Cen μ N) l = 0 := by
  unfold lc; split_ifs <;> simp

theorem lc_step {ν ν' : {j : Fin 4 // j ≠ μ}} (h : ν' ≠ ν) (g : Cen μ N) (y : TT μ T) :
    lc g (ν, tsh μ T ν' y) = lc g (ν, y) := by
  show (if ((tsh μ T ν' y) ν).val = 0 then g ν else 0) = (if (y ν).val = 0 then g ν else 0)
  rw [CentreSectorSeed.tsh_ne (Ne.symm h)]

variable [NeZero N]

/-- **The centre action** of `Z_N³` on slice configurations. -/
def act (g : Cen μ N) (V : Cfg μ T N) : Cfg μ T N := fun l => cz (lc g l) * V l

theorem coe_act (g : Cen μ N) (V : Cfg μ T N) (l : SpT μ T) :
    ((act g V l : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
      = ee (lc g l) • ((V l : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  show ((cz (lc g l) * V l : SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) = _
  rw [Submonoid.coe_mul, coe_cz, smul_mul_assoc, Matrix.one_mul]

/-- The phases around a spatial plaquette cancel. -/
theorem plaq_phase (g : Cen μ N) (νa νb : {j : Fin 4 // j ≠ μ}) (y : TT μ T) :
    ee (lc g (νa, y)) * ee (lc g (νb, tsh μ T νa y)) * star (ee (lc g (νa, tsh μ T νb y)))
      * star (ee (lc g (νb, y))) = 1 := by
  by_cases hab : νa = νb
  · subst hab
    calc ee (lc g (νa, y)) * ee (lc g (νa, tsh μ T νa y)) * star (ee (lc g (νa, tsh μ T νa y)))
          * star (ee (lc g (νa, y)))
        = (ee (lc g (νa, y)) * star (ee (lc g (νa, y))))
          * (ee (lc g (νa, tsh μ T νa y)) * star (ee (lc g (νa, tsh μ T νa y)))) := by ring
      _ = 1 := by rw [ee_mul_star, ee_mul_star, one_mul]
  · rw [lc_step hab, lc_step (Ne.symm hab)]
    calc ee (lc g (νa, y)) * ee (lc g (νb, y)) * star (ee (lc g (νa, y))) * star (ee (lc g (νb, y)))
        = (ee (lc g (νa, y)) * star (ee (lc g (νa, y))))
          * (ee (lc g (νb, y)) * star (ee (lc g (νb, y)))) := by ring
      _ = 1 := by rw [ee_mul_star, ee_mul_star, one_mul]

theorem sp_act (g : Cen μ N) (V : Cfg μ T N) : spT μ T (act g V) = spT μ T V := by
  unfold spT
  refine Finset.sum_congr rfl fun νa _ => Finset.sum_congr rfl fun νb _ =>
    Finset.sum_congr rfl fun y _ => wd_congr ?_
  simp only [Submonoid.coe_mul, coe_inv, coe_act]
  rw [smul_plaq, plaq_phase, one_smul]

theorem tp_act (g : Cen μ N) (A : TT μ T → SUN.SU N) (V V' : Cfg μ T N) :
    tpT μ T A (act g V) (act g V') = tpT μ T A V V' := by
  unfold tpT
  refine Finset.sum_congr rfl fun νb _ => Finset.sum_congr rfl fun y _ => wd_congr ?_
  simp only [Submonoid.coe_mul, coe_inv, coe_act]
  rw [smul_plaq_time, ee_mul_star, one_smul]

theorem gk_act (g : Cen μ N) (β : ℝ) (V V' : Cfg μ T N) :
    gk μ T N β (act g V) (act g V') = gk μ T N β V V' := by
  unfold gk
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [tp_act]

/-- **The centre action preserves the transfer kernel.** -/
theorem kT_act (g : Cen μ N) (β : ℝ) (V V' : Cfg μ T N) :
    kT μ T N β (act g V) (act g V') = kT μ T N β V V' := by
  unfold kT; rw [sp_act, sp_act, gk_act]

theorem mp_act (g : Cen μ N) :
    MeasurePreserving (act (T := T) g) (hS μ T N) (hS μ T N) :=
  measurePreserving_pi (fun _ => probHaar (SUN.SU N)) (fun _ => probHaar (SUN.SU N))
    (fun l => measurePreserving_mul_left (probHaar (SUN.SU N)) (cz (lc g l)))

/-- **The centre action is a measure-preserving action of `Z_N³`.** -/
theorem centreAction :
    FluxSectorFourier.CentreAction (hS μ T N) (act (μ := μ) (T := T) (N := N)) where
  meas g := (mp_act g).measurable
  zero V := funext fun l => by simp only [act, lc_zero, cz_zero, one_mul]
  add g h V := funext fun l => by simp only [act, lc_add, cz_add, mul_assoc]
  mp := mp_act

/-- **The centre on three directions has `N³` elements.** -/
theorem card_cen : Fintype.card (Cen μ N) = N ^ 3 := by
  rw [Fintype.card_fun, CentreSectorSeed.card_transverse μ, ZMod.card]

/-- **Every iterate of the transfer is invariant under the action.** -/
theorem iter_act (β : ℝ) (k : ℕ) (g : Cen μ N) (V V' : Cfg μ T N) :
    iter (hS μ T N) (kT μ T N β) k (act g V) (act g V') = iter (hS μ T N) (kT μ T N β) k V V' :=
  TwistedTraceBoundN.iter_inv_act centreAction (fun g x y => kT_act g β x y) k g V V'

end MassGap.SliceCentreAction

end

#print axioms MassGap.SliceCentreAction.kT_act
#print axioms MassGap.SliceCentreAction.centreAction
#print axioms MassGap.SliceCentreAction.card_cen
#print axioms MassGap.SliceCentreAction.iter_act
