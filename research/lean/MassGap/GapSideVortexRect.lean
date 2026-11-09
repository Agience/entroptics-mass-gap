import Mathlib
import MassGap.GapSideVortexAntiDiagonal

/-!
# MassGap.GapSideVortexRect — the rectangular corner steps of the flux share: six of nine sheets reduce to the squaring, three to the cubic vortex and a transverse twisted doubling gap

`CentreSectorSeedN.fluxShareN 2 β n i` at corner step `i` lives on the torus `ext n (pathV i)`: extents `2n`
in the directions `j < i`, `n` in the others, transfer along `i`. Its single twists `e_ν` are 't Hooft sheets
in the plane `(i, ν)` (`GapSideTwistBridge.twistRatioN_eq`). Step `0` is the cubic torus, reached by the
vortex anti-diagonal (`GapSideVortexAntiDiagonal`). This module treats steps `1–3`.

## The objects

* `rhol L q U`, `ZRp L β ζ`: the rectangular Wilson torus with a plaquette pattern `ζ` multiplied into each
  plaquette holonomy. `ZRp L β 1 = RectWilson.ZR L 2 β` (`ZR_eq_ZRp`), `ZRp L β (tw L g) = ZRtw L μ 2 β g`.
* `sheetR L a b`: `−1` on the plaquettes of the plane `(a, b)` (both orientations) at `x_a = x_b = 0`.
  `zR L a b β = ZRp(sheetR)/ZR`, `vortexR = −log zR`.
* `Lc n i = ext n (pathV i)`, the torus of corner step `i`.

## What is proved

* `ZRp_perm`: `ZRp` is invariant under every relabelling of links that carries holonomies to holonomies.
  Instances: the unit translation (`rlinkShift`), and the exchange of two directions of equal extent
  (`linkSwap`).
* `tw_single_rect`, `ZRtw_single`: the `SU(2)` twist of `e_ν` at time `μ` is the sheet `(μ, ν)` moved one
  step along `μ`, so `ZRtw L μ 2 β e_ν = ZRp L β (sheetR L μ ν)`. `zR_symm`: the sheet ratio depends on the
  plane only. `zR_swap`: exchanging two directions of equal extent moves the sheet's plane.
* `twistRatioN_eq_zR`: `twistRatioN 2 β n i e_ν = zR (Lc n i) i ν β`.
* **`one_sub_zR_doubled`**: on the torus of step `i + 1`, the sheets in the planes `(i, ν)` are the twists of
  step `i` with the time doubled: `1 − zR (Lc n (i+1)) i ν ≤ 8 · fluxShareDoubledN 2 β n i`. With
  `CentreSectorSeedN.fluxShareDoubled_leN` the doubling squares the odds (`eight_fD_le`).
* **`fluxShare_steps`**: step-`0` flux share and the zero-flux defects of steps `0–2` at most `1/80000`, and the
  three sheets `(1, 2)`, `(1, 3)` of step `1` and `(2, 3)` of step `2` with `1 − zR ≤ 1/720000`, give the flux
  shares of steps `1–3` at most `1/80000`. Step `3` costs nothing new; step `2` one sheet; step `1` two.
* `one_sub_zR_le_fluxShare`: each residual sheet deficit is at most `8` times a flux share of `SectorRest`, so
  the residual is a strict part of `SectorRest`'s flux half.
* **`vortexR_double`**: for any two tori `L, L'`, `vortexR L' = 2 vortexR L + gapT L L'`, `gapT` the twisted
  doubling defect minus the untwisted one. For the residual sheets the doubled direction is transverse to the
  sheet, and the untwisted part is the corner defect of step `0` or `1` (`untwisted_zero`, `untwisted_one`).
* `vortexR_cubic`: on the cubic torus, `vortexR = GapSideVortexAntiDiagonal.vortexF` of the chain from `2β`.
* **`sectorSeed_of_vortex_rectRest`**, **`sectorSeed_of_vortex_rect`**: the feeds to
  `GapSideTwistFlat.FirstCrossingSectorSeed` with `RectRest` (three sheets and the zero-flux defects) or with
  `TransverseGap γ` and `TrivialRest` in place of `SectorRest`.

## What is open

* `TransverseGap γ`: the four transverse twisted doubling gaps at the first crossing. Each is
  `D^tw − D` along a direction transverse to the sheet; nothing here bounds it.
* `TrivialRest`: the zero-flux defects of the four steps, unchanged from `SectorRest`.
* `VortexStepNet`, `VortexChainEnd`: as in `GapSideVortexAntiDiagonal`, now for the planes `(1, 2)`, `(1, 3)`,
  `(2, 3)` as well as `(0, ν)`.

## Controls

`ZRp_perm`, `vortexR_double` and the bridge identities hold at every coupling and carry no sign. The squaring
(`fluxShareDoubled_leN`) is the sector form of reflection positivity: it transports a flux bound from step `i`
to step `i + 1`; it supplies no flux bound. `zR_zero`, `gapT_zero`: at `β = 0` every ratio is `1` and every gap
`0`, so the new premises are not empty.

DERIVED (module-wide): `8 = 2³ = |Z₂³|` (`SliceCentreAction.card_cen`); `720000 = 9 · 80000`, `9` the
single-twist union bound of `TwistDeficitUnionN` at `N = 2`; `79999 = 80000 − 1`, the floor of `1 − f`;
`3 > e` bounds `exp(trivialDefectN)` at `trivialDefectN ≤ 1`; `2 = 2¹` the doubling of one direction; `4 = 2²`
and `3 = 2 + 1` the multiplicities of the cubic vortex and of the gaps on the step-`2` sheet; `1/80000` and
`1/1000` are `CentreSectorSeedN.defectW_le_of_sectorsN`'s.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.GapSideVortexRect

open MeasureTheory Filter MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.MovedTorusDecimation
open MassGap.TwistedTraceBound (negOne)
open MassGap.SliceCentreAction (Cen act lc centreAction card_cen mp_act)
open MassGap.TwistedTraceBoundN (cz cz_zero)
open MassGap.GapSideTwistBridge (tw ZRtw)
open MassGap.ChainCoarseSeed (WilsonChain)

local notation "wd" => WilsonAction.wilsonDensity

/-! ## 1. The rectangular torus with a plaquette pattern -/

section Pattern

variable (L : Fin 4 → ℕ)

/-- The boundary word `U_i(x) U_j(x+i) U_i(x+j)⁻¹ U_j(x)⁻¹` on the rectangular torus. -/
def rhol (q : RPlaq L) (U : RLink L → SUN.SU 2) : SUN.SU 2 :=
  U (q.1.1, q.2) * U (q.1.2, rshift L q.1.1 q.2) * (U (q.1.1, rshift L q.1.2 q.2))⁻¹
    * (U (q.1.2, q.2))⁻¹

/-- **The rectangular `SU(2)` Wilson torus with the pattern `ζ`** multiplied into each plaquette. -/
def ZRp (β : ℝ) (ζ : RPlaq L → SUN.SU 2) : ℝ :=
  ∫ U : RLink L → SUN.SU 2, Real.exp (-β * ∑ q, wd (ζ q * rhol L q U))
    ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))

/-- **The centre sheet** in the plane `(a, b)`: `−1` on the `(a, b)` and `(b, a)` plaquettes at
`x_a = x_b = 0`. -/
def sheetR (a b : Fin 4) (q : RPlaq L) : SUN.SU 2 :=
  if (q.1 = (a, b) ∨ q.1 = (b, a)) ∧ (q.2 a).val = 0 ∧ (q.2 b).val = 0 then negOne else 1

/-- The sheet ratio `Z_tw/Z` of the rectangular torus. -/
def zR (a b : Fin 4) (β : ℝ) : ℝ := ZRp L β (sheetR L a b) / ZR L 2 β

/-- The vortex free energy of the rectangular torus. -/
def vortexR (a b : Fin 4) (β : ℝ) : ℝ := -Real.log (zR L a b β)

theorem continuous_rhol (q : RPlaq L) : Continuous fun U : RLink L → SUN.SU 2 => rhol L q U := by
  have h1 : Continuous fun U : RLink L → SUN.SU 2 => U (q.1.1, q.2) := continuous_apply _
  have h2 : Continuous fun U : RLink L → SUN.SU 2 => U (q.1.2, rshift L q.1.1 q.2) :=
    continuous_apply _
  have h3 : Continuous fun U : RLink L → SUN.SU 2 => U (q.1.1, rshift L q.1.2 q.2) :=
    continuous_apply _
  have h4 : Continuous fun U : RLink L → SUN.SU 2 => U (q.1.2, q.2) := continuous_apply _
  unfold rhol
  exact ((h1.mul h2).mul h3.inv).mul h4.inv

theorem continuous_integrand (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    Continuous fun U : RLink L → SUN.SU 2 => Real.exp (-β * ∑ q, wd (ζ q * rhol L q U)) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun q _ =>
    WilsonAction.continuous_wilsonDensity.comp (continuous_const.mul (continuous_rhol L q))))

theorem ZRp_pos (β : ℝ) (ζ : RPlaq L → SUN.SU 2) : 0 < ZRp L β ζ := by
  unfold ZRp
  rw [integral_pos_iff_support_of_nonneg (fun U => (Real.exp_pos _).le)
    (integrable_of_continuous (continuous_integrand L β ζ))]
  rw [show Function.support (fun U : RLink L → SUN.SU 2 =>
      Real.exp (-β * ∑ q, wd (ζ q * rhol L q U))) = Set.univ from
    Set.eq_univ_of_forall fun U => (Real.exp_pos _).ne', measure_univ]
  exact one_pos

theorem ZRp_zero (ζ : RPlaq L → SUN.SU 2) : ZRp L 0 ζ = 1 := by
  unfold ZRp
  simp

theorem hol_eq_rhol (U : RLink L → SUN.SU 2) (q : RPlaq L) : (sysR L 2).hol q U = rhol L q U := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  rw [hol_eq]
  rfl

/-- `ZR` is the pattern-free `ZRp`. -/
theorem ZR_eq_ZRp (β : ℝ) : ZR L 2 β = ZRp L β (fun _ => 1) := by
  unfold ZR LatticeGauge.System.partition LatticeGauge.System.boltz LatticeGauge.System.action
    LatticeGauge.System.vol ZRp
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show Real.exp (-β * ∑ q : RPlaq L, wd ((sysR L 2).hol q U))
    = Real.exp (-β * ∑ q : RPlaq L, wd (1 * rhol L q U))
  simp_rw [one_mul, hol_eq_rhol]

theorem ZR_pos (β : ℝ) : 0 < ZR L 2 β := by
  rw [ZR_eq_ZRp]
  exact ZRp_pos L β _

/-- `ZRtw` is `ZRp` of the twist. -/
theorem ZRtw_eq_ZRp {μ : Fin 4} (β : ℝ) (g : Cen μ 2) : ZRtw L μ 2 β g = ZRp L β (tw L g) := by
  unfold ZRtw ZRp
  simp_rw [hol_eq_rhol]

theorem zR_pos (a b : Fin 4) (β : ℝ) : 0 < zR L a b β :=
  div_pos (ZRp_pos L β _) (ZR_pos L β)

theorem zR_zero (a b : Fin 4) : zR L a b 0 = 1 := by
  unfold zR
  rw [ZR_eq_ZRp, ZRp_zero, ZRp_zero, div_one]

/-- The sheet deficit is at most the vortex free energy. -/
theorem one_sub_zR_le_vortexR (a b : Fin 4) (β : ℝ) : 1 - zR L a b β ≤ vortexR L a b β := by
  unfold vortexR
  have := Real.log_le_sub_one_of_pos (zR_pos L a b β)
  linarith

/-- The sheet depends on its plane only. -/
theorem sheetR_symm (a b : Fin 4) : sheetR L a b = sheetR L b a := by
  funext q
  unfold sheetR
  exact if_congr (by tauto) rfl rfl

theorem zR_symm (a b : Fin 4) (β : ℝ) : zR L a b β = zR L b a β := by
  unfold zR
  rw [sheetR_symm]

end Pattern

/-! ## 2. Relabellings of the links -/

section Relabel

variable {L : Fin 4 → ℕ}

variable (L) in
/-- The configuration relabelled by a permutation of the links: `U ↦ U ∘ e`. -/
def cfgPerm (e : Equiv.Perm (RLink L)) : (RLink L → SUN.SU 2) ≃ᵐ (RLink L → SUN.SU 2) :=
  (MeasurableEquiv.piCongrLeft (fun _ : RLink L => SUN.SU 2) e).symm

theorem cfgPerm_apply (e : Equiv.Perm (RLink L)) (U : RLink L → SUN.SU 2) (l : RLink L) :
    cfgPerm L e U l = U (e l) := rfl

theorem cfgPerm_mp (e : Equiv.Perm (RLink L)) :
    MeasurePreserving (cfgPerm L e) (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) := by
  have h : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : RLink L => SUN.SU 2) e)
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2))
      (Measure.pi fun _ : RLink L => probHaar (SUN.SU 2)) :=
    measurePreserving_piCongrLeft (μ := fun _ : RLink L => probHaar (SUN.SU 2)) e
  exact MeasurePreserving.symm _ h

/-- **A relabelling that carries holonomies to holonomies** moves the pattern. -/
theorem ZRp_perm (e : Equiv.Perm (RLink L)) (f : Equiv.Perm (RPlaq L))
    (h : ∀ q U, rhol L q (cfgPerm L e U) = rhol L (f q) U) (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ZRp L β ζ = ZRp L β (fun q => ζ (f.symm q)) := by
  unfold ZRp
  refine ((cfgPerm_mp e).integral_comp'
    (fun U : RLink L → SUN.SU 2 => Real.exp (-β * ∑ q, wd (ζ q * rhol L q U)))).symm.trans ?_
  congr 1
  funext U
  dsimp only
  simp only [h]
  rw [← Equiv.sum_comp f (fun q => wd (ζ (f.symm q) * rhol L q U))]
  simp only [Equiv.symm_apply_apply]

end Relabel

/-! ## 3. Translations, and the twist of a generator is the sheet -/

section Shift

variable {L : Fin 4 → ℕ}

theorem rshift_comm (κ i : Fin 4) (x : RSite L) :
    rshift L κ (rshift L i x) = rshift L i (rshift L κ x) := by
  by_cases h : κ = i
  · subst h; rfl
  · unfold rshift
    rw [Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
    exact Function.update_comm (Ne.symm h) _ _ _

theorem rshift_val (i j : Fin 4) (x : RSite L) :
    ((rshift L i x) j).val = if j = i then ((x j).val + 1) % L j else (x j).val := by
  by_cases h : j = i
  · subst h
    simp only [rshift, Function.update_self, if_true]
    exact val_finRotate _
  · simp only [rshift, Function.update_of_ne h, if_neg h]

theorem rshift_self_val_zero (μ : Fin 4) (x : RSite L) :
    ((rshift L μ x) μ).val = 0 ↔ (x μ).val + 1 = L μ := by
  rw [rshift_val, if_pos rfl]
  have hlt := (x μ).isLt
  constructor
  · intro h
    by_contra hne
    have h2 : (x μ).val + 1 < L μ := by omega
    rw [Nat.mod_eq_of_lt h2] at h
    omega
  · intro h
    rw [h, Nat.mod_self]

variable (L) in
/-- The unit translation along `κ`, as a permutation of sites. -/
def rsiteShift (κ : Fin 4) : Equiv.Perm (RSite L) where
  toFun := rshift L κ
  invFun := fun x => Function.update x κ ((finRotate (L κ)).symm (x κ))
  left_inv := fun x => by
    simp only [rshift, Function.update_self, Equiv.symm_apply_apply, Function.update_idem,
      Function.update_eq_self]
  right_inv := fun x => by
    simp only [rshift, Function.update_self, Equiv.apply_symm_apply, Function.update_idem,
      Function.update_eq_self]

variable (L) in
def rlinkShift (κ : Fin 4) : Equiv.Perm (RLink L) := Equiv.prodCongr (Equiv.refl _) (rsiteShift L κ)

variable (L) in
def rplaqShift (κ : Fin 4) : Equiv.Perm (RPlaq L) := Equiv.prodCongr (Equiv.refl _) (rsiteShift L κ)

theorem rlinkShift_apply (κ : Fin 4) (l : RLink L) : rlinkShift L κ l = (l.1, rshift L κ l.2) := rfl

theorem rplaqShift_apply (κ : Fin 4) (q : RPlaq L) : rplaqShift L κ q = (q.1, rshift L κ q.2) := rfl

theorem rhol_shift (κ : Fin 4) (q : RPlaq L) (U : RLink L → SUN.SU 2) :
    rhol L q (cfgPerm L (rlinkShift L κ) U) = rhol L (rplaqShift L κ q) U := by
  simp only [rhol, cfgPerm_apply, rlinkShift_apply, rplaqShift_apply]
  rw [rshift_comm κ q.1.1, rshift_comm κ q.1.2]

/-- **A translated pattern has the same partition function.** -/
theorem ZRp_shift (κ : Fin 4) (β : ℝ) (ζ : RPlaq L → SUN.SU 2) :
    ZRp L β (fun q => ζ (rplaqShift L κ q)) = ZRp L β ζ := by
  rw [ZRp_perm (rlinkShift L κ) (rplaqShift L κ) (rhol_shift κ) β]
  simp only [Equiv.apply_symm_apply]

/-- **For `SU(2)` the twist of the generator `e_ν` at time `μ` is the sheet `(μ, ν)` moved one step
along `μ`.** -/
theorem tw_single_rect (μ : Fin 4) (ν : {j : Fin 4 // j ≠ μ}) (q : RPlaq L) :
    tw L (μ := μ) (Pi.single ν (1 : ZMod 2)) q = sheetR L μ ν.1 (rplaqShift L μ q) := by
  obtain ⟨⟨a, b⟩, x⟩ := q
  have hr : ((rshift L μ x) μ).val = 0 ↔ (x μ).val + 1 = L μ := rshift_self_val_zero μ x
  have hν : ((rshift L μ x) ν.1).val = (x ν.1).val := by rw [rshift_val, if_neg ν.2]
  have hninv : negOne⁻¹ = negOne := GapSideTwistFlat.negOne_inv
  have hc1 : cz (1 : ZMod 2) = negOne := GapSideTwistBridge.cz_one_two
  rw [rplaqShift_apply]
  unfold tw sheetR
  simp only [hν, hr]
  by_cases h : a = μ ∧ b ≠ μ
  · rw [dif_pos h]
    obtain ⟨ha, hb⟩ := h
    by_cases hbν : b = ν.1
    · have hsub : (⟨b, hb⟩ : {j : Fin 4 // j ≠ μ}) = ν := Subtype.ext hbν
      simp only [lc, perp, hsub, Pi.single_eq_same]
      simp only [ha, hbν]
      subst hbν
      by_cases h0 : (x μ).val + 1 = L μ <;> by_cases hx : (x ν.1).val = 0 <;>
        simp [h0, hx, hc1, cz_zero]
    · have hne : (⟨b, hb⟩ : {j : Fin 4 // j ≠ μ}) ≠ ν := fun e => hbν (congrArg Subtype.val e)
      have hc : ¬ ((a, b) = (μ, ν.1) ∨ (a, b) = (ν.1, μ)) := by
        rintro (e | e)
        · exact hbν (Prod.mk.inj e).2
        · exact ν.2 ((Prod.mk.inj e).1.symm.trans ha)
      simp only [lc, perp, Pi.single_eq_of_ne hne, ite_self, cz_zero, hc, false_and, if_false]
  · rw [dif_neg h]
    by_cases h' : b = μ ∧ a ≠ μ
    · rw [dif_pos h']
      obtain ⟨hb, ha⟩ := h'
      by_cases haν : a = ν.1
      · have hsub : (⟨a, ha⟩ : {j : Fin 4 // j ≠ μ}) = ν := Subtype.ext haν
        simp only [lc, perp, hsub, Pi.single_eq_same]
        simp only [hb, haν]
        subst haν
        by_cases h0 : (x μ).val + 1 = L μ <;> by_cases hx : (x ν.1).val = 0 <;>
          simp [h0, hx, hc1, cz_zero, hninv]
      · have hne : (⟨a, ha⟩ : {j : Fin 4 // j ≠ μ}) ≠ ν := fun e => haν (congrArg Subtype.val e)
        have hc : ¬ ((a, b) = (μ, ν.1) ∨ (a, b) = (ν.1, μ)) := by
          rintro (e | e)
          · exact ha (Prod.mk.inj e).1
          · exact haν (Prod.mk.inj e).1
        simp only [lc, perp, Pi.single_eq_of_ne hne, ite_self, cz_zero, inv_one, hc, false_and,
          if_false]
    · rw [dif_neg h']
      have hc : ¬ ((a, b) = (μ, ν.1) ∨ (a, b) = (ν.1, μ)) := by
        rintro (e | e)
        · obtain ⟨e1, e2⟩ := Prod.mk.inj e
          exact h ⟨e1, e2 ▸ ν.2⟩
        · obtain ⟨e1, e2⟩ := Prod.mk.inj e
          exact h' ⟨e2, e1 ▸ ν.2⟩
      simp only [hc, false_and, if_false]

/-- **The twisted torus of a generator is the sheet torus.** -/
theorem ZRtw_single (μ : Fin 4) (ν : {j : Fin 4 // j ≠ μ}) (β : ℝ) :
    ZRtw L μ 2 β (Pi.single ν (1 : ZMod 2)) = ZRp L β (sheetR L μ ν.1) := by
  rw [ZRtw_eq_ZRp]
  have e : tw L (μ := μ) (Pi.single ν (1 : ZMod 2)) = fun q => sheetR L μ ν.1 (rplaqShift L μ q) :=
    funext fun q => tw_single_rect μ ν q
  rw [e, ZRp_shift]

end Shift

/-! ## 4. Exchanging two directions of equal extent -/

section Swap

variable {L : Fin 4 → ℕ} (c d : Fin 4) (hL : L c = L d)

include hL in
theorem L_swap (j : Fin 4) : L (Equiv.swap c d j) = L j := by
  rcases eq_or_ne j c with rfl | hc
  · rw [Equiv.swap_apply_left, hL]
  · rcases eq_or_ne j d with rfl | hd
    · rw [Equiv.swap_apply_right, hL]
    · rw [Equiv.swap_apply_of_ne_of_ne hc hd]

/-- The site with the coordinates `c` and `d` exchanged. -/
def swapSite (x : RSite L) : RSite L := fun j =>
  ⟨(x (Equiv.swap c d j)).val, lt_of_lt_of_eq (x _).isLt (L_swap c d hL j)⟩

theorem swapSite_val (x : RSite L) (j : Fin 4) :
    ((swapSite c d hL x) j).val = (x (Equiv.swap c d j)).val := rfl

theorem swapSite_invol : Function.Involutive (swapSite c d hL) := by
  intro x
  funext j
  apply Fin.ext
  rw [swapSite_val, swapSite_val, Equiv.swap_apply_self]

theorem swapSite_rshift (i : Fin 4) (x : RSite L) :
    swapSite c d hL (rshift L i x) = rshift L (Equiv.swap c d i) (swapSite c d hL x) := by
  funext j
  apply Fin.ext
  rw [swapSite_val, rshift_val, rshift_val, swapSite_val]
  by_cases h : j = Equiv.swap c d i
  · have h' : Equiv.swap c d j = i := by rw [h, Equiv.swap_apply_self]
    rw [if_pos h', if_pos h]
    exact congrArg (HMod.hMod ((x (Equiv.swap c d j)).val + 1)) (L_swap c d hL j)
  · have h' : Equiv.swap c d j ≠ i := fun e => h (Equiv.swap_apply_eq_iff.mp e)
    rw [if_neg h', if_neg h]

theorem linkSwap_invol :
    Function.Involutive (fun l : RLink L => (Equiv.swap c d l.1, swapSite c d hL l.2)) := by
  intro l
  simp only [Equiv.swap_apply_self, swapSite_invol c d hL l.2]

theorem plaqSwap_invol :
    Function.Involutive (fun q : RPlaq L =>
      ((Equiv.swap c d q.1.1, Equiv.swap c d q.1.2), swapSite c d hL q.2)) := by
  intro q
  simp only [Equiv.swap_apply_self, swapSite_invol c d hL q.2]

/-- The exchange of the directions `c, d` on links. -/
def linkSwap : Equiv.Perm (RLink L) := (linkSwap_invol c d hL).toPerm _

/-- The exchange of the directions `c, d` on plaquettes. -/
def plaqSwap : Equiv.Perm (RPlaq L) := (plaqSwap_invol c d hL).toPerm _

theorem rhol_swap (q : RPlaq L) (U : RLink L → SUN.SU 2) :
    rhol L q (cfgPerm L (linkSwap c d hL) U) = rhol L (plaqSwap c d hL q) U := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  simp only [rhol, cfgPerm_apply, linkSwap, plaqSwap, Function.Involutive.coe_toPerm,
    swapSite_rshift]

theorem sheetR_swap (a b : Fin 4) (q : RPlaq L) :
    sheetR L a b ((plaqSwap c d hL).symm q) = sheetR L (Equiv.swap c d a) (Equiv.swap c d b) q := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  unfold plaqSwap
  rw [Function.Involutive.toPerm_symm, Function.Involutive.coe_toPerm]
  unfold sheetR
  refine if_congr ?_ rfl rfl
  simp only [Prod.mk.injEq, swapSite_val, Equiv.swap_apply_eq_iff]

include hL in
/-- **Exchanging two directions of equal extent moves the plane of the sheet.** -/
theorem zR_swap (a b : Fin 4) (β : ℝ) :
    zR L a b β = zR L (Equiv.swap c d a) (Equiv.swap c d b) β := by
  unfold zR
  rw [ZRp_perm (linkSwap c d hL) (plaqSwap c d hL) (rhol_swap c d hL) β (sheetR L a b)]
  congr 2
  funext q
  exact sheetR_swap c d hL a b q

end Swap

/-! ## 5. The corner tori, and the doubled step -/

section Doubled

open MassGap.CentreSectorSeedN
open MassGap.CentreSectorSeed (Tr pathV)

/-- The torus of corner step `i` at side `n`. -/
abbrev Lc (n : ℕ) (i : Fin 4) : Fin 4 → ℕ := DoublingWilson.ext n (pathV i)

/-- **The step-`i` single twist is the sheet ratio of the step-`i` torus.** -/
theorem twistRatioN_eq_zR {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) :
    twistRatioN 2 β n i (Pi.single ν 1) = zR (Lc n i) i ν.1 β := by
  rw [GapSideTwistBridge.twistRatioN_eq hβ hn he i, ZRtw_single]
  rfl

/-- The twisted trace of a transfer iterate is the twisted torus with that time extent. -/
theorem twist_iter_eq_ZRtw {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ)
    (L' : Fin 4 → ℕ) (hT : tr L' i = T) (m : ℕ) (hL : L' i = m + m + 1 + 1) (g : Cen i 2) :
    FluxSectorBound.twist (hS i T 2) (iter (hS i T 2) (kT i T 2 β) m) (act g)
      = ZRtw L' i 2 β g := by
  subst hT
  rw [GapSideTwistBridge.twist_iter_eq_cycTw (bdd_kT two_ne_zero hβ) (kT_symm β) (mp_act g).measurable,
    GapSideTwistBridge.ZRtw_eq_cycTw two_ne_zero β g, hL]

/-- The trace of a transfer iterate is the torus with that time extent. -/
theorem hs_iter_eq_ZR {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ)
    (L' : Fin 4 → ℕ) (hT : tr L' i = T) (m : ℕ) (hL : L' i = 2 * (m + 1)) :
    hs (hS i T 2) (iter (hS i T 2) (kT i T 2 β) m) = ZR L' 2 β := by
  subst hT
  rw [ZR_eq_traceSeq (μ := i) (L := L') two_ne_zero hβ (m + 1) (by omega) hL]
  unfold traceSeq
  rw [hL, show 2 * (m + 1) / 2 - 1 = m by omega]

/-- `halfKN` of the doubled time is the iterate of order `2j + 1`. -/
theorem conv_halfKN_eq {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (i : Fin 4) :
    conv (hSN 2 (2 * (j + 1)) i) (halfKN 2 β (2 * (j + 1)) i) (halfKN 2 β (2 * (j + 1)) i)
      = iter (hS i (Tr (2 * (j + 1)) i) 2) (kT i (Tr (2 * (j + 1)) i) 2 β) (j + j + 1) := by
  have hk : Bdd (kT i (Tr (2 * (j + 1)) i) 2 β) := bdd_kT two_ne_zero hβ
  have e : halfKN 2 β (2 * (j + 1)) i = iter (hS i (Tr (2 * (j + 1)) i) 2)
      (kT i (Tr (2 * (j + 1)) i) 2 β) j := by
    unfold halfKN
    rw [show 2 * (j + 1) / 2 - 1 = j by omega]
  rw [e, ← iter_add hk j j]

theorem hs_conv_halfKN_eq_ZR {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (i : Fin 4) (L' : Fin 4 → ℕ)
    (hT : tr L' i = Tr (2 * (j + 1)) i) (hL : L' i = 2 * (2 * (j + 1))) :
    hs (hSN 2 (2 * (j + 1)) i)
        (conv (hSN 2 (2 * (j + 1)) i) (halfKN 2 β (2 * (j + 1)) i) (halfKN 2 β (2 * (j + 1)) i))
      = ZR L' 2 β := by
  rw [conv_halfKN_eq hβ j i]
  exact hs_iter_eq_ZR hβ i _ L' hT (j + j + 1) (by rw [hL]; ring)

theorem twist_conv_halfKN_eq_ZRtw {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (i : Fin 4) (L' : Fin 4 → ℕ)
    (hT : tr L' i = Tr (2 * (j + 1)) i) (hL : L' i = 2 * (2 * (j + 1))) (g : Cen i 2) :
    FluxSectorBound.twist (hSN 2 (2 * (j + 1)) i)
        (conv (hSN 2 (2 * (j + 1)) i) (halfKN 2 β (2 * (j + 1)) i) (halfKN 2 β (2 * (j + 1)) i))
        (act g)
      = ZRtw L' i 2 β g := by
  rw [conv_halfKN_eq hβ j i]
  exact twist_iter_eq_ZRtw hβ i _ L' hT (j + j + 1) (by rw [hL]; ring) g

theorem aux_ineq {H t S c : ℝ} (hH : 0 < H) (hc : c * 8 = 1) (h : H - t ≤ 8 * H - S) :
    1 - t / H ≤ 8 * ((H - c * S) / H) := by
  rw [show 8 * ((H - c * S) / H) = (8 * H - (c * 8) * S) / H by ring, hc, one_mul,
    show 1 - t / H = (H - t) / H by rw [sub_div, div_self hH.ne']]
  exact (div_le_div_iff_of_pos_right hH).mpr h

/-- **The sheets through the doubled time direction.** On the torus `L'` that doubles the time of step `i`,
every sheet in a plane `(i, ν)` has deficit at most `8` times the doubled flux share of step `i`. -/
theorem one_sub_zR_doubled {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4)
    (L' : Fin 4 → ℕ) (hT : tr L' i = Tr n i) (hL : L' i = 2 * n) (ν : {j : Fin 4 // j ≠ i}) :
    1 - zR L' i ν.1 β ≤ 8 * fluxShareDoubledN 2 β n i := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * (j + 1) := ⟨n / 2 - 1, by obtain ⟨k, rfl⟩ := he; omega⟩
  set ρ := hSN 2 (2 * (j + 1)) i with hρ
  set b := conv ρ (halfKN 2 β (2 * (j + 1)) i) (halfKN 2 β (2 * (j + 1)) i) with hbdef
  have htw : ∀ g : Cen i 2, FluxSectorBound.twist ρ b (act g) = ZRtw L' i 2 β g :=
    twist_conv_halfKN_eq_ZRtw hβ j i L' hT hL
  have hhs : hs ρ b = ZR L' 2 β := hs_conv_halfKN_eq_ZR hβ j i L' hT hL
  have hpos : 0 < hs ρ b := hs_conv_halfKN_pos (N := 2) hβ _ i
  have hB : Bdd b := (bdd_halfKN (N := 2) hβ _ i).conv (bdd_halfKN (N := 2) hβ _ i)
  have hmean := ZeroFluxSector.hs_zk_eq_mean hB
    (centreAction (μ := i) (T := Tr (2 * (j + 1)) i) (N := 2))
  rw [card_cen] at hmean
  have hdef : ∀ g : Cen i 2, 0 ≤ hs ρ b - FluxSectorBound.twist ρ b (act g) := fun g => by
    have := TwistDeficitUnionN.deficit_nonneg hB
      (centreAction (μ := i) (T := Tr (2 * (j + 1)) i) (N := 2)) g
    unfold TwistDeficitUnionN.deficit at this
    exact this
  have hsingle : hs ρ b - FluxSectorBound.twist ρ b (act (Pi.single ν (1 : ZMod 2)))
      ≤ ∑ g : Cen i 2, (hs ρ b - FluxSectorBound.twist ρ b (act g)) :=
    Finset.single_le_sum (f := fun g : Cen i 2 => hs ρ b - FluxSectorBound.twist ρ b (act g))
      (fun g _ => hdef g) (Finset.mem_univ _)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_cen, nsmul_eq_mul] at hsingle
  have hz : zR L' i ν.1 β = FluxSectorBound.twist ρ b (act (Pi.single ν (1 : ZMod 2))) / hs ρ b := by
    rw [htw, hhs]
    unfold zR
    rw [ZRtw_single]
  unfold fluxShareDoubledN
  rw [← hρ, ← hbdef, hmean, hz]
  exact aux_ineq hpos (by norm_num) (by push_cast at hsingle; linarith)

/-- **The doubling squares the odds**: step-`i` flux share and zero-flux defect at most `1/80000` give the
doubled flux share at most `1/5760000`. -/
theorem eight_fD_le {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4)
    (hf : fluxShareN 2 β n i ≤ 1 / 80000) (ht : trivialDefectN 2 β n i ≤ 1 / 80000) :
    8 * fluxShareDoubledN 2 β n i ≤ 1 / 720000 := by
  have hD := fluxShareDoubled_leN (N := 2) hβ n i
  have hf0 : 0 ≤ fluxShareN 2 β n i := by
    unfold fluxShareN
    exact div_nonneg (sub_nonneg.mpr (hs_trivKN_le (N := 2) hβ n i)) (hs_halfKN_pos (N := 2) hβ n i).le
  set f := fluxShareN 2 β n i
  have h1f : 0 < 1 - f := by linarith
  have hq : f / (1 - f) ≤ 1 / 79999 := by
    rw [div_le_div_iff₀ h1f (by norm_num)]
    linarith
  have hq0 : 0 ≤ f / (1 - f) := div_nonneg hf0 h1f.le
  have hexp : Real.exp (trivialDefectN 2 β n i) ≤ 3 := by
    have h1 : Real.exp (trivialDefectN 2 β n i) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    have := Real.exp_one_lt_d9
    linarith
  have hsq : (f / (1 - f)) ^ 2 ≤ (1 / 79999) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have hprod : (f / (1 - f)) ^ 2 * Real.exp (trivialDefectN 2 β n i) ≤ (1 / 79999) ^ 2 * 3 :=
    mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity)
  have : (1 / 79999 : ℝ) ^ 2 * 3 * 8 ≤ 1 / 720000 := by norm_num
  linarith

/-! ### The concrete corner tori -/

theorem tr_Lc_one (n : ℕ) : tr (Lc n 1) 0 = Tr n 0 := by
  funext ⟨j, hj⟩
  fin_cases j
  · exact absurd rfl hj
  all_goals simp [DoublingWilson.ext, pathV]

theorem tr_Lc_two (n : ℕ) : tr (Lc n 2) 1 = Tr n 1 := by
  funext ⟨j, hj⟩
  fin_cases j
  · simp [DoublingWilson.ext, pathV]
  · exact absurd rfl hj
  all_goals simp [DoublingWilson.ext, pathV]

theorem tr_Lc_three (n : ℕ) : tr (Lc n 3) 2 = Tr n 2 := by
  funext ⟨j, hj⟩
  fin_cases j
  · simp [DoublingWilson.ext, pathV]
  · simp [DoublingWilson.ext, pathV]
  · exact absurd rfl hj
  · simp [DoublingWilson.ext, pathV]

theorem Lc_one_zero (n : ℕ) : Lc n 1 0 = 2 * n := by simp [DoublingWilson.ext, pathV]
theorem Lc_two_one (n : ℕ) : Lc n 2 1 = 2 * n := by simp [DoublingWilson.ext, pathV]
theorem Lc_three_two (n : ℕ) : Lc n 3 2 = 2 * n := by simp [DoublingWilson.ext, pathV]
theorem Lc_two_01 (n : ℕ) : Lc n 2 0 = Lc n 2 1 := by simp [DoublingWilson.ext, pathV]
theorem Lc_three_02 (n : ℕ) : Lc n 3 0 = Lc n 3 2 := by simp [DoublingWilson.ext, pathV]
theorem Lc_three_12 (n : ℕ) : Lc n 3 1 = Lc n 3 2 := by simp [DoublingWilson.ext, pathV]

/-- The step-`0` corner torus is the cubic one. -/
theorem Lc_zero (n : ℕ) : Lc n 0 = fun _ => n := GapSideTwistBridge.ext_pathV_zero n

/-! ### Steps `1–3` -/

variable {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
include hβ hn he

/-- **Step 1**: the sheet `(1, 0)` comes from the doubled step `0`; the sheets `(1, 2)`, `(1, 3)` are inputs. -/
theorem fluxShare_one_le (h0 : fluxShareN 2 β n 0 ≤ 1 / 80000)
    (ht0 : trivialDefectN 2 β n 0 ≤ 1 / 80000)
    (h12 : 1 - 1 / 720000 ≤ zR (Lc n 1) 1 2 β) (h13 : 1 - 1 / 720000 ≤ zR (Lc n 1) 1 3 β) :
    fluxShareN 2 β n 1 ≤ 1 / 80000 := by
  have hD := eight_fD_le hβ n 0 h0 ht0
  have hs := TwistDeficitUnionN.fluxShareN_le_of_single (N := 2) hβ n 1 (δ := 1 / 720000)
    (by norm_num) (fun ν => by
      rw [twistRatioN_eq_zR hβ hn he]
      obtain ⟨j, hj⟩ := ν
      fin_cases j
      · have hd := one_sub_zR_doubled hβ hn he 0 (Lc n 1) (tr_Lc_one n) (Lc_one_zero n)
          ⟨1, by decide⟩
        dsimp only at hd
        show 1 - 1 / 720000 ≤ zR (Lc n 1) 1 0 β
        rw [zR_symm]
        linarith
      · exact absurd rfl hj
      · exact h12
      · exact h13)
  norm_num at hs
  linarith

/-- **Step 2**: the sheets `(2, 1)` and, by exchanging `0, 1`, `(2, 0)` come from the doubled step `1`; the
sheet `(2, 3)` is an input. -/
theorem fluxShare_two_le (h1 : fluxShareN 2 β n 1 ≤ 1 / 80000)
    (ht1 : trivialDefectN 2 β n 1 ≤ 1 / 80000)
    (h23 : 1 - 1 / 720000 ≤ zR (Lc n 2) 2 3 β) :
    fluxShareN 2 β n 2 ≤ 1 / 80000 := by
  have hD := eight_fD_le hβ n 1 h1 ht1
  have hd := one_sub_zR_doubled hβ hn he 1 (Lc n 2) (tr_Lc_two n) (Lc_two_one n) ⟨2, by decide⟩
  dsimp only at hd
  have hs := TwistDeficitUnionN.fluxShareN_le_of_single (N := 2) hβ n 2 (δ := 1 / 720000)
    (by norm_num) (fun ν => by
      rw [twistRatioN_eq_zR hβ hn he]
      obtain ⟨j, hj⟩ := ν
      fin_cases j
      · show 1 - 1 / 720000 ≤ zR (Lc n 2) 2 0 β
        rw [zR_swap 0 1 (Lc_two_01 n) 2 0 β,
          show Equiv.swap (0 : Fin 4) 1 2 = 2 by decide, show Equiv.swap (0 : Fin 4) 1 0 = 1 by decide,
          zR_symm]
        linarith
      · show 1 - 1 / 720000 ≤ zR (Lc n 2) 2 1 β
        rw [zR_symm]
        linarith
      · exact absurd rfl hj
      · exact h23)
  norm_num at hs
  linarith

/-- **Step 3**: every sheet comes from the doubled step `2`, after exchanging `0, 2` or `1, 2`. -/
theorem fluxShare_three_le (h2 : fluxShareN 2 β n 2 ≤ 1 / 80000)
    (ht2 : trivialDefectN 2 β n 2 ≤ 1 / 80000) :
    fluxShareN 2 β n 3 ≤ 1 / 80000 := by
  have hD := eight_fD_le hβ n 2 h2 ht2
  have hd := one_sub_zR_doubled hβ hn he 2 (Lc n 3) (tr_Lc_three n) (Lc_three_two n) ⟨3, by decide⟩
  dsimp only at hd
  have hs := TwistDeficitUnionN.fluxShareN_le_of_single (N := 2) hβ n 3 (δ := 1 / 720000)
    (by norm_num) (fun ν => by
      rw [twistRatioN_eq_zR hβ hn he]
      obtain ⟨j, hj⟩ := ν
      fin_cases j
      · show 1 - 1 / 720000 ≤ zR (Lc n 3) 3 0 β
        rw [zR_swap 0 2 (Lc_three_02 n) 3 0 β,
          show Equiv.swap (0 : Fin 4) 2 3 = 3 by decide, show Equiv.swap (0 : Fin 4) 2 0 = 2 by decide,
          zR_symm]
        linarith
      · show 1 - 1 / 720000 ≤ zR (Lc n 3) 3 1 β
        rw [zR_swap 1 2 (Lc_three_12 n) 3 1 β,
          show Equiv.swap (1 : Fin 4) 2 3 = 3 by decide, show Equiv.swap (1 : Fin 4) 2 1 = 2 by decide,
          zR_symm]
        linarith
      · show 1 - 1 / 720000 ≤ zR (Lc n 3) 3 2 β
        rw [zR_symm]
        linarith
      · exact absurd rfl hj)
  norm_num at hs
  linarith

/-- **The flux shares of steps `1–3` from step `0`, the zero-flux defects and three sheets.** -/
theorem fluxShare_steps (h0 : fluxShareN 2 β n 0 ≤ 1 / 80000)
    (ht : ∀ i : Fin 4, trivialDefectN 2 β n i ≤ 1 / 80000)
    (h12 : 1 - 1 / 720000 ≤ zR (Lc n 1) 1 2 β) (h13 : 1 - 1 / 720000 ≤ zR (Lc n 1) 1 3 β)
    (h23 : 1 - 1 / 720000 ≤ zR (Lc n 2) 2 3 β) :
    ∀ i : Fin 4, i ≠ 0 → fluxShareN 2 β n i ≤ 1 / 80000 := by
  have f1 := fluxShare_one_le hβ hn he h0 (ht 0) h12 h13
  have f2 := fluxShare_two_le hβ hn he f1 (ht 1) h23
  have f3 := fluxShare_three_le hβ hn he f2 (ht 2)
  intro i hi
  fin_cases i
  · exact absurd rfl hi
  · exact f1
  · exact f2
  · exact f3

omit hn he in
/-- **The residual is a part of `SectorRest`'s flux half**: each sheet deficit of step `i` is at most `8`
times the flux share of step `i`. -/
theorem one_sub_zR_le_fluxShare (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) (hn : 2 ≤ n) (he : Even n) :
    1 - zR (Lc n i) i ν.1 β ≤ 8 * fluxShareN 2 β n i := by
  rw [← twistRatioN_eq_zR hβ hn he i ν]
  have hA := hs_halfKN_pos (N := 2) hβ n i
  have hle : ∀ g : Cen i 2, 0 ≤ 1 - twistRatioN 2 β n i g := fun g => by
    rw [TwistDeficitUnionN.one_sub_twistRatioN hβ]
    exact div_nonneg (TwistDeficitUnionN.deficit_nonneg (bdd_halfKN hβ _ i) centreAction g) hA.le
  have hsum : 1 - twistRatioN 2 β n i (Pi.single ν 1)
      ≤ ∑ g : Cen i 2, (1 - twistRatioN 2 β n i g) :=
    Finset.single_le_sum (f := fun g => 1 - twistRatioN 2 β n i g) (fun g _ => hle g)
      (Finset.mem_univ _)
  have hsum2 : ∑ g : Cen i 2, (1 - twistRatioN 2 β n i g)
      = (2 : ℝ) ^ 3 - ∑ g, twistRatioN 2 β n i g := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_cen, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hS : ∑ g, twistRatioN 2 β n i g = (2 : ℝ) ^ 3 * (1 - fluxShareN 2 β n i) := by
    rw [fluxShareN_eq_mean hβ n i]
    push_cast
    ring
  rw [hsum2, hS] at hsum
  linarith

end Doubled

/-! ## 6. The transverse doubling: twice the vortex plus a twisted-minus-untwisted defect -/

section Transverse

open MassGap.CentreSectorSeedN
open MassGap.CentreSectorSeed (Tr pathV)
open MassGap.HolderBondMoving (ZF twistField fAct thol)

/-- **The transverse gap**: the doubling defect of the sheet torus from `L` to `L'` minus that of the
untwisted torus. -/
def gapT (L L' : Fin 4 → ℕ) (a b : Fin 4) (β : ℝ) : ℝ :=
  (2 * Real.log (ZRp L β (sheetR L a b)) - Real.log (ZRp L' β (sheetR L' a b)))
    - (2 * Real.log (ZR L 2 β) - Real.log (ZR L' 2 β))

/-- **Doubling the torus doubles the vortex free energy up to the gap** (exact, any two tori). -/
theorem vortexR_double (L L' : Fin 4 → ℕ) (a b : Fin 4) (β : ℝ) :
    vortexR L' a b β = 2 * vortexR L a b β + gapT L L' a b β := by
  unfold vortexR zR gapT
  rw [Real.log_div (ZRp_pos L β _).ne' (ZR_pos L β).ne',
    Real.log_div (ZRp_pos L' β _).ne' (ZR_pos L' β).ne']
  ring

theorem gapT_zero (L L' : Fin 4 → ℕ) (a b : Fin 4) : gapT L L' a b 0 = 0 := by
  unfold gapT
  rw [ZR_eq_ZRp, ZR_eq_ZRp, ZRp_zero, ZRp_zero, ZRp_zero, ZRp_zero]
  simp

/-- **The untwisted part of the gap from the cubic torus is the corner defect of step `0`.** -/
theorem untwisted_zero {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    2 * Real.log (ZR (fun _ => n) 2 β) - Real.log (ZR (Lc n 1) 2 β)
      = SectorDefect.dd (hSN 2 n 0) (halfKN 2 β n 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * (j + 1) := ⟨n / 2 - 1, by obtain ⟨k, rfl⟩ := he; omega⟩
  unfold SectorDefect.dd
  rw [GapSideTwistBridge.hs_halfKN_eq hβ hn he 0,
    hs_conv_halfKN_eq_ZR hβ j 0 (Lc (2 * (j + 1)) 1) (tr_Lc_one _) (Lc_one_zero _),
    GapSideTwistBridge.ext_pathV_zero]

/-- **The untwisted part of the gap from step `1` to step `2` is the corner defect of step `1`.** -/
theorem untwisted_one {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    2 * Real.log (ZR (Lc n 1) 2 β) - Real.log (ZR (Lc n 2) 2 β)
      = SectorDefect.dd (hSN 2 n 1) (halfKN 2 β n 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * (j + 1) := ⟨n / 2 - 1, by obtain ⟨k, rfl⟩ := he; omega⟩
  unfold SectorDefect.dd
  rw [GapSideTwistBridge.hs_halfKN_eq hβ hn he 1,
    hs_conv_halfKN_eq_ZR hβ j 1 (Lc (2 * (j + 1)) 2) (tr_Lc_two _) (Lc_two_one _)]

/-- The cubic `ZRp` is `HolderBondMoving.ZF` of the twisted field. -/
theorem ZRp_cubic (n : ℕ) (β : ℝ) (ζ : RPlaq (fun _ => n) → SUN.SU 2) :
    ZRp (fun _ => n) β ζ = ZF (d := 4) (N := n) (probHaar (SUN.SU 2)) (twistField β wd ζ) := by
  unfold ZRp ZF fAct twistField
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [neg_mul, Finset.mul_sum]
  rfl

/-- **On the cubic torus the sheet ratio is the chain's vortex ratio at step `0`.** -/
theorem zR_cubic (β : ℝ) (C : WilsonChain (2 * β)) (P : Plane) (n : ℕ) :
    zR (fun _ => n) P.1.1 P.1.2 β
      = GapSideVortexAntiDiagonal.Ztw C 0 P n / ElectricStepChain.Zh C 0 n := by
  unfold zR
  rw [ZRp_cubic, GapSideTwistBridge.ZR_cubic (N := 2) n β]
  unfold GapSideVortexAntiDiagonal.Ztw ElectricStepChain.Zh
  have e1 : twistField 1 (ChainFirstCrossing.halfField (C.W 0) ChainCoarseSeed.suTau)
      (GapSideTwistFlat.sheet P.1.1 P.1.2 negOne)
      = fun (q : TorusDoubling.TPlaq 4 n) g =>
        twistField β wd (sheetR (fun _ => n) P.1.1 P.1.2) q g + (-β) := by
    funext q g
    rw [GapSideVortexAntiDiagonal.halfField_zero_eq C]
    simp only [twistField]
    have : GapSideTwistFlat.sheet P.1.1 P.1.2 negOne q = sheetR (fun _ => n) P.1.1 P.1.2 q := rfl
    rw [this]
    ring
  have e2 : ChainCoarseSeed.uniformField (d := 4) (n := n)
      (ChainFirstCrossing.halfField (C.W 0) ChainCoarseSeed.suTau)
      = fun (q : TorusDoubling.TPlaq 4 n) g => (fun (_ : TorusDoubling.TPlaq 4 n) g => β * wd g) q g
        + (-β) := by
    funext q g
    rw [GapSideVortexAntiDiagonal.halfField_zero_eq C]
    rfl
  rw [e1, e2, GapSideVortexAntiDiagonal.ZF_add_const, GapSideVortexAntiDiagonal.ZF_add_const,
    mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- **The cubic vortex free energy is the anti-diagonal's.** -/
theorem vortexR_cubic (β : ℝ) (C : WilsonChain (2 * β)) (P : Plane) (n : ℕ) :
    vortexR (fun _ => n) P.1.1 P.1.2 β = GapSideVortexAntiDiagonal.vortexF C 0 P n := by
  unfold vortexR GapSideVortexAntiDiagonal.vortexF
  rw [zR_cubic]

end Transverse

/-! ## 7. The feeds -/

section Feed

open MassGap.CentreSectorSeedN MassGap.WilsonChainExists MassGap.ChainFirstCrossing
  MassGap.GapSideVortexAntiDiagonal
open MassGap.CentreSectorSeed (pathV)

/-- **What the rectangular reduction leaves**: at the first crossing, the three sheets `(1, 2)`, `(1, 3)` of
step `1` and `(2, 3)` of step `2` with deficit at most `1/720000`, and the zero-flux defects of all steps.

DERIVED: `3` the last direction of `Fin 4` (sheet index); `720000 = 9 · 80000`, `9` the single-twist union
bound at `N = 2`. Inherited: `1/1000`, `1/80000` from `CentreSectorSeedN.defectW_le_of_sectorsN`. -/
def RectRest : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    (1 - 1 / 720000 ≤ zR (Lc (2 ^ (k + 2)) 1) 1 2 β ∧ 1 - 1 / 720000 ≤ zR (Lc (2 ^ (k + 2)) 1) 1 3 β
      ∧ 1 - 1 / 720000 ≤ zR (Lc (2 ^ (k + 2)) 2) 2 3 β) ∧
      ∀ i : Fin 4, trivialDefectN 2 β (2 ^ (k + 2)) i ≤ 1 / 80000

/-- The zero-flux half of `SectorRest`. DERIVED: Inherited: `1/1000`, `1/80000` from
`CentreSectorSeedN.defectW_le_of_sectorsN`. -/
def TrivialRest : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    ∀ i : Fin 4, trivialDefectN 2 β (2 ^ (k + 2)) i ≤ 1 / 80000

/-- **The transverse gaps** at the first crossing: from the cubic torus to the step-`1` torus for the sheets
`(1, 2)`, `(1, 3)`, `(2, 3)`, and from the step-`1` to the step-`2` torus for `(2, 3)`, all at most `γ`.

DERIVED: `3` the last direction of `Fin 4` (sheet index). Inherited: `1/1000` the crossing seed of
`CentreSectorSeedN.defectW_le_of_sectorsN`. -/
def TransverseGap (γ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ k : ℕ, coarseDefect (wilsonChainOf (2 * β)) k ≤ 1 / 1000 →
    (∀ i < k, 1 / 1000 < coarseDefect (wilsonChainOf (2 * β)) i) →
    gapT (fun _ => 2 ^ (k + 2)) (Lc (2 ^ (k + 2)) 1) 1 2 β ≤ γ ∧
      gapT (fun _ => 2 ^ (k + 2)) (Lc (2 ^ (k + 2)) 1) 1 3 β ≤ γ ∧
      gapT (fun _ => 2 ^ (k + 2)) (Lc (2 ^ (k + 2)) 1) 2 3 β ≤ γ ∧
      gapT (Lc (2 ^ (k + 2)) 1) (Lc (2 ^ (k + 2)) 2) 2 3 β ≤ γ

/-- The step-`0` vortex bound of every plane, from the net and the chain end. -/
theorem vortexF_le {ε δ : ℝ} {β : ℝ} {k : ℕ}
    (hV : ∀ P : Plane, ∑ i ∈ Finset.range k,
      (holderExcessTw (wilsonChainOf (2 * β)) i P (2 ^ (k + 2 - i))
        - ElectricStepChain.holderExcess (wilsonChainOf (2 * β)) i (2 ^ (k + 2 - i))) ≤ ε)
    (hE : ∀ P : Plane, vortexF (wilsonChainOf (2 * β)) k P 4 ≤ δ) (P : Plane) :
    vortexF (wilsonChainOf (2 * β)) 0 P (2 ^ (k + 2)) ≤ ε + δ := by
  rw [vortex_antiDiagonal_crossing]
  linarith [hV P, hE P]

/-- **`SectorRest` from the vortex net, the chain end and `RectRest`.** -/
theorem sectorRest_of_rect {ε δ : ℝ} (hV : VortexStepNet ε) (hE : VortexChainEnd δ)
    (hb : 9 * (ε + δ) ≤ 1 / 80000) (hR : RectRest) : SectorRest := by
  unfold SectorRest
  filter_upwards [hV, hE, hR, eventually_ge_atTop (0 : ℝ)] with β hV hE hR hβ
  intro k hk hmin
  obtain ⟨⟨h12, h13, h23⟩, ht⟩ := hR k hk hmin
  have hn : 2 ≤ 2 ^ (k + 2) := DeltaLengthTower.two_le_two_pow (by omega : 1 ≤ k + 2)
  have he : Even (2 ^ (k + 2)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hF : ∀ ν : {j : Fin 4 // j ≠ 0},
      vortexF (wilsonChainOf (2 * β)) 0 (plane0 ν) (2 ^ (k + 2)) ≤ max 0 (ε + δ) := fun ν =>
    le_max_of_le_right (vortexF_le (hV k hk hmin) (hE k hk hmin) (plane0 ν))
  have hfl := fluxShareN_zero_le_of_vortex hβ k (le_max_left 0 (ε + δ)) hF
  have hm : 9 * max 0 (ε + δ) ≤ 1 / 80000 := by
    rcases le_total 0 (ε + δ) with h | h
    · rw [max_eq_right h]; exact hb
    · rw [max_eq_left h]; norm_num
  have h0 : fluxShareN 2 β (2 ^ (k + 2)) 0 ≤ 1 / 80000 := by linarith
  exact ⟨fluxShare_steps hβ hn he h0 ht h12 h13 h23, ht⟩

/-- **The refined feed**: `FirstCrossingSectorSeed` from the vortex net, the chain end and `RectRest`, which
replaces the flux shares of steps `1–3` in `SectorRest` by three sheets. -/
theorem sectorSeed_of_vortex_rectRest {ε δ : ℝ} (hV : VortexStepNet ε) (hE : VortexChainEnd δ)
    (hb : 9 * (ε + δ) ≤ 1 / 80000) (hR : RectRest) : GapSideTwistFlat.FirstCrossingSectorSeed :=
  sectorSeed_of_vortex hV hE hb (sectorRest_of_rect hV hE hb hR)

/-- **`RectRest` from the vortex net, the chain end, the transverse gaps and the zero-flux defects.** -/
theorem rectRest_of_transverse {ε δ γ : ℝ} (hV : VortexStepNet ε) (hE : VortexChainEnd δ)
    (hG : TransverseGap γ) (hT : TrivialRest) (hs : 0 ≤ ε + δ) (hγ : 0 ≤ γ)
    (hb : 4 * (ε + δ) + 3 * γ ≤ 1 / 720000) : RectRest := by
  have hpos : 0 ≤ 2 * (ε + δ) + 2 * γ :=
    add_nonneg (mul_nonneg zero_le_two hs) (mul_nonneg zero_le_two hγ)
  unfold RectRest
  filter_upwards [hV, hE, hG, hT] with β hV hE hG hT
  intro k hk hmin
  obtain ⟨g12, g13, g23a, g23b⟩ := hG k hk hmin
  have hF := vortexF_le (hV k hk hmin) (hE k hk hmin)
  have c : ∀ (a b : Fin 4) (hab : a < b),
      vortexR (fun _ => 2 ^ (k + 2)) a b β ≤ ε + δ := fun a b hab => by
    have := vortexR_cubic β (wilsonChainOf (2 * β)) ⟨(a, b), hab⟩ (2 ^ (k + 2))
    dsimp only at this
    rw [this]
    exact hF _
  set N := 2 ^ (k + 2)
  have s12 : 1 - zR (Lc N 1) 1 2 β ≤ 1 / 720000 := by
    have h1 := one_sub_zR_le_vortexR (Lc N 1) 1 2 β
    rw [vortexR_double (fun _ => N) (Lc N 1)] at h1
    have h2 := c 1 2 (by decide)
    linarith
  have s13 : 1 - zR (Lc N 1) 1 3 β ≤ 1 / 720000 := by
    have h1 := one_sub_zR_le_vortexR (Lc N 1) 1 3 β
    rw [vortexR_double (fun _ => N) (Lc N 1)] at h1
    have h2 := c 1 3 (by decide)
    linarith
  have s23 : 1 - zR (Lc N 2) 2 3 β ≤ 1 / 720000 := by
    have h1 := one_sub_zR_le_vortexR (Lc N 2) 2 3 β
    rw [vortexR_double (Lc N 1) (Lc N 2), vortexR_double (fun _ => N) (Lc N 1)] at h1
    have h2 := c 2 3 (by decide)
    linarith
  exact ⟨⟨by linarith, by linarith, by linarith⟩, hT k hk hmin⟩

/-- **The feed through the transverse gaps**: `FirstCrossingSectorSeed` from the vortex net, the chain end,
`TransverseGap γ` and `TrivialRest`, at `4(ε + δ) + 3γ ≤ 1/720000`. -/
theorem sectorSeed_of_vortex_rect {ε δ γ : ℝ} (hV : VortexStepNet ε) (hE : VortexChainEnd δ)
    (hG : TransverseGap γ) (hT : TrivialRest) (hs : 0 ≤ ε + δ) (hγ : 0 ≤ γ)
    (hb : 4 * (ε + δ) + 3 * γ ≤ 1 / 720000) : GapSideTwistFlat.FirstCrossingSectorSeed :=
  sectorSeed_of_vortex_rectRest hV hE (by linarith)
    (rectRest_of_transverse hV hE hG hT hs hγ hb)

/-- The parameter constraint of `sectorSeed_of_vortex_rect` is satisfiable. -/
theorem params_satisfiable : ∃ ε δ γ : ℝ, 0 ≤ ε + δ ∧ 0 ≤ γ ∧ 4 * (ε + δ) + 3 * γ ≤ 1 / 720000 :=
  ⟨0, 0, 0, by norm_num, le_rfl, by norm_num⟩

end Feed

end MassGap.GapSideVortexRect

end

#print axioms MassGap.GapSideVortexRect.ZR_eq_ZRp
#print axioms MassGap.GapSideVortexRect.ZRp_perm
#print axioms MassGap.GapSideVortexRect.tw_single_rect
#print axioms MassGap.GapSideVortexRect.ZRtw_single
#print axioms MassGap.GapSideVortexRect.zR_symm
#print axioms MassGap.GapSideVortexRect.zR_swap
#print axioms MassGap.GapSideVortexRect.zR_zero
#print axioms MassGap.GapSideVortexRect.twistRatioN_eq_zR
#print axioms MassGap.GapSideVortexRect.one_sub_zR_doubled
#print axioms MassGap.GapSideVortexRect.eight_fD_le
#print axioms MassGap.GapSideVortexRect.fluxShare_steps
#print axioms MassGap.GapSideVortexRect.one_sub_zR_le_fluxShare
#print axioms MassGap.GapSideVortexRect.vortexR_double
#print axioms MassGap.GapSideVortexRect.gapT_zero
#print axioms MassGap.GapSideVortexRect.untwisted_zero
#print axioms MassGap.GapSideVortexRect.untwisted_one
#print axioms MassGap.GapSideVortexRect.vortexR_cubic
#print axioms MassGap.GapSideVortexRect.sectorRest_of_rect
#print axioms MassGap.GapSideVortexRect.sectorSeed_of_vortex_rectRest
#print axioms MassGap.GapSideVortexRect.rectRest_of_transverse
#print axioms MassGap.GapSideVortexRect.sectorSeed_of_vortex_rect
#print axioms MassGap.GapSideVortexRect.params_satisfiable
