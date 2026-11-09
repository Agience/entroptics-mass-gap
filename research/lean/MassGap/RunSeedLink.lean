import Mathlib
import MassGap.ApertureBridge
import MassGap.VortexCondense
import MassGap.VortexStrong

/-!
# MassGap.RunSeedLink — the run seed at `SU(2)` as vortex free energies and the zero-flux defect at one physical size

`WDeltaRun.RunSeed 2` is `∃ L > 0, ApertureBridge.PhysDefect L (1/1000)` (`ApertureBridge.runSeed_iff_physDefect`).
`ZoomSelfScale.defectW 2 β n = 16 log ZR(n⁴) − log ZR((2n)⁴)` reads the untwisted partition function only
(`GapSideVortexRect.ZR_eq_ZRp`: `ZR = ZRp` at the trivial pattern); it carries the untwisted partition
functions themselves, which the sheet ratios `zR = ZRp(sheetR)/ZR` normalise away. This module proves that the seed is nevertheless equivalent to bounds on the vortex free
energies `vortexR = −log zR` together with the zero-flux doubling defect, all at one physical size.

## What is proved

* **The cubic vortex free energy in `vortexR` form** (`PhysVortexR`, `physVortexR_iff`). `PhysVortexR L ε` reads
  `vortexR (fun _ => 2^{kPhys L β + 2}) a b β ≤ ε` at every sheet plane `a < b`, eventually in `β`. It is
  `PhysicalScaleSmall.PhysVortex L ε` (`GapSideVortexRect.vortexR_cubic`).
* **Every sheet deficit from the defect at one side** (`one_sub_twistRatioN_le_fluxShare`, `zR_Lc_ge_of_defectW`,
  `zR_cubic_ge_of_defectW`, `vortexR_le_of_zR_ge`). Each centre twist ratio of a corner step has deficit at most
  `8` times that step's flux share (`CentreSectorSeedN.fluxShareN_eq_mean`, every deficit non-negative), and
  `CentreSectorSeedN.sectors_of_defectWN` bounds the flux share by `4δ` when `defectW 2 β n ≤ δ`, `68δ ≤ 2`. So every
  single-sheet ratio of every corner torus `Lc n i`, and of the cubic torus in every plane (`zR_swap`), is at least
  `1 − 32δ`, and its vortex free energy at most `32δ/(1 − 32δ)`.
* **The converse at the physical side** (`physVortexR_of_physDefect`, `physVortexRect_of_physDefect`,
  `physTrivial_of_physDefect`). `PhysDefect L δ` with `68δ ≤ 2`, `32δ < 1` gives `PhysVortexR L (32δ/(1 − 32δ))`
  and `ApertureBridge.PhysVortexRect L (32δ/(1 − 32δ))`; with `2δ ≤ 1/80000` it gives `ApertureBridge.PhysTrivial L`.
* **The sharp seed at a larger physical size** (`defectW_pow_sharp`, `physDefect_sharp_of_runSeed`). From
  `RunSeed 2` (seed side `n`, `n · aRun ≤ C`), at `L = 2^{j+1} C` the physical side is `2^m n` with `m ≥ j`, and
  `DoublingSharp.iterate_sharp` gives `PhysDefect L ((1/4)^{2^j}/250)`.
* **The equivalence** (`runSeed_iff_vortex`):
  `RunSeed 2 ↔ ∃ L > 0, PhysVortexR L (1/720000) ∧ PhysVortexRect L (1/720000) ∧ PhysTrivial L`.
  The direction `⇐` is `ApertureBridge.physRest_of_vortexRect` and `physDefect_of_physVortex`; the direction `⇒` is
  the converse above at `j = 4`, `δ = (1/4)^{16}/250 = 1/1073741824000`.

So the `RunSeed 2` input (which gives `hW` at `SU(2)`) is exactly three clauses at one physical size `L`,
eventually in `β`: the 't Hooft
vortex free energies of the cubic torus (six planes) and of the three residual rectangular sheets are at most
`1/720000`, and the zero-flux doubling defects `trivialDefectN` of the four corner steps are at most `1/80000`.

* **The strong-coupling hypothesis fails at weak coupling** (`not_dob_eventually`). `VortexStrong.vortexR_le_card`
  and `VortexStrong.condenses_vortexR_strong` take `4225 · rate β · e ≤ 1/128`; eventually in `β` that inequality is
  false (`rate β = 1 − e^{−2β} ≥ 2/3` at `β ≥ 1`). So the bare polymer gas of `VortexStrong` bounds no clause of
  `runSeed_iff_vortex`, each of which is eventual in `β`.

DERIVED (module-wide): `8 = 2³ = |Z₂³|` (`SliceCentreAction.card_cen`); `4δ = N³δ/2` at `N = 2` and `68 = 4 + 2⁶` from
`sectors_of_defectWN`; `32 = 8 · 4`; `2δ` the zero-flux bound of `sectors_of_defectWN`; `1/80000`, `9` and
`1/720000 = 1/(9 · 80000)` from `ApertureBridge.physRest_of_vortexRect` and `physDefect_of_physVortex`; `250`, `1/4`
from `DoublingSharp.iterate_sharp`; `j = 4` the least exponent with `32δ/(1 − 32δ) ≤ 1/720000`; `2^{j+1}` places
`2^j n` below the physical side (`physSide_spec`); `4225`, `1/128` from `VortexStrong`; `2/3 = 1 − 1/3`, `3 ≤ e²`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.RunSeedLink

open Filter MassGap MassGap.PhysicalScaleSmall MassGap.GapSideVortexRect
open MassGap.SliceCentreAction (Cen)

/-! ## 1. Every sheet ratio from the doubling defect at one side -/

section Side

/-- **Each centre twist deficit is at most `8` times the step's flux share** (`fluxShareN = 1 − 8⁻¹ Σ_g z_g`, every
`1 − z_g ≥ 0`). -/
theorem one_sub_twistRatioN_le_fluxShare {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (g : Cen i 2) :
    1 - CentreSectorSeedN.twistRatioN 2 β n i g ≤ 8 * CentreSectorSeedN.fluxShareN 2 β n i := by
  have hm := CentreSectorSeedN.fluxShareN_eq_mean (N := 2) hβ n i
  have hnn : ∀ h : Cen i 2, 0 ≤ 1 - CentreSectorSeedN.twistRatioN 2 β n i h := by
    intro h
    rw [TwistDeficitUnionN.one_sub_twistRatioN (N := 2) hβ n i h]
    exact div_nonneg (TwistDeficitUnionN.deficit_nonneg (CentreSectorSeedN.bdd_halfKN hβ _ i)
      SliceCentreAction.centreAction _) (CentreSectorSeedN.hs_halfKN_pos (N := 2) hβ n i).le
  have hs : ∑ h : Cen i 2, (1 - CentreSectorSeedN.twistRatioN 2 β n i h)
      = 8 * CentreSectorSeedN.fluxShareN 2 β n i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, SliceCentreAction.card_cen, hm,
      nsmul_eq_mul]
    push_cast
    ring
  rw [← hs]
  exact Finset.single_le_sum (fun h _ => hnn h) (Finset.mem_univ g)

/-- **Every single-sheet ratio of a corner torus from the defect**: `defectW 2 β n ≤ δ`, `68δ ≤ 2` give
`1 − 32δ ≤ zR (Lc n i) i ν β`. -/
theorem zR_Lc_ge_of_defectW {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : 68 * δ ≤ 2) (hd : ZoomSelfScale.defectW 2 β n ≤ δ) (i : Fin 4)
    (ν : {j : Fin 4 // j ≠ i}) : 1 - 32 * δ ≤ zR (Lc n i) i ν.1 β := by
  have hs := (CentreSectorSeedN.sectors_of_defectWN (N := 2) hβ hn he hδ0
    (by norm_num; linarith) hd i).1
  have h1 := one_sub_twistRatioN_le_fluxShare hβ n i (Pi.single ν 1)
  rw [twistRatioN_eq_zR hβ hn he i ν] at h1
  norm_num at hs
  linarith

/-- **Every sheet ratio of the cubic torus from the defect**, in every plane `a < b` (`zR_swap` moves the plane to
`(0, b)`, the step-`0` sheet). -/
theorem zR_cubic_ge_of_defectW {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : 68 * δ ≤ 2) (hd : ZoomSelfScale.defectW 2 β n ≤ δ)
    (P : MovedTorusDecimation.Plane) : 1 - 32 * δ ≤ zR (fun _ => n) P.1.1 P.1.2 β := by
  obtain ⟨⟨a, b⟩, hab⟩ := P
  have hab' : a < b := hab
  have hb : b ≠ 0 := fun h => by subst h; exact absurd hab' (Fin.not_lt_zero a)
  have h0 := zR_Lc_ge_of_defectW hβ hn he hδ0 hδ hd 0 ⟨b, hb⟩
  rw [Lc_zero] at h0
  show 1 - 32 * δ ≤ zR (fun _ => n) a b β
  by_cases ha : a = 0
  · subst ha
    exact h0
  · rw [zR_swap (L := fun _ => n) 0 a rfl a b β, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hb (ne_of_gt hab')]
    exact h0

/-- **The vortex free energy from a lower bound on the sheet ratio**: `1 − x ≤ zR`, `x < 1` give
`vortexR ≤ x/(1 − x)`. -/
theorem vortexR_le_of_zR_ge {L : Fin 4 → ℕ} {a b : Fin 4} {β x : ℝ} (hx : x < 1)
    (h : 1 - x ≤ zR L a b β) : vortexR L a b β ≤ x / (1 - x) := by
  have hz := zR_pos L a b β
  have hz0 : zR L a b β ≠ 0 := hz.ne'
  have h1x : 0 < 1 - x := by linarith
  unfold vortexR
  have hlog : Real.log (zR L a b β)⁻¹ ≤ (zR L a b β)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hz)
  rw [Real.log_inv] at hlog
  have key : (zR L a b β)⁻¹ - 1 ≤ x / (1 - x) := by
    rw [show (zR L a b β)⁻¹ - 1 = (1 - zR L a b β) / zR L a b β by field_simp,
      div_le_div_iff₀ hz h1x]
    nlinarith
  linarith

end Side

/-! ## 2. The physical side -/

section Phys

open MassGap.GapSideVortexAntiDiagonal MassGap.WilsonChainExists

/-- **The cubic vortex free energy at the physical side, in `vortexR` form**: eventually in `β`, at every sheet
plane `a < b`, `vortexR` of the cubic torus of side `2^{kPhys L β + 2}` is at most `ε`. -/
def PhysVortexR (L ε : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ P : MovedTorusDecimation.Plane,
    vortexR (fun _ => 2 ^ (kPhys L β + 2)) P.1.1 P.1.2 β ≤ ε

/-- **`PhysVortexR` is `PhysVortex`** (`vortexR_cubic`). -/
theorem physVortexR_iff {L ε : ℝ} : PhysVortexR L ε ↔ PhysVortex L ε := by
  have e : ∀ (β : ℝ) (P : MovedTorusDecimation.Plane),
      vortexR (fun _ => 2 ^ (kPhys L β + 2)) P.1.1 P.1.2 β
        = vortexF (wilsonChainOf (2 * β)) 0 P (2 ^ (kPhys L β + 2)) :=
    fun β P => vortexR_cubic β _ P _
  unfold PhysVortexR PhysVortex
  simp only [e]

/-- The physical side is even and at least `2`. -/
theorem side_facts (L β : ℝ) : 2 ≤ 2 ^ (kPhys L β + 2) ∧ Even (2 ^ (kPhys L β + 2)) :=
  ⟨DeltaLengthTower.two_le_two_pow (by omega), Nat.even_pow.mpr ⟨even_two, by omega⟩⟩

/-- **The cubic vortex free energy from the defect.** -/
theorem physVortexR_of_physDefect {L δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 68 * δ ≤ 2) (h32 : 32 * δ < 1)
    (h : ApertureBridge.PhysDefect L δ) : PhysVortexR L (32 * δ / (1 - 32 * δ)) := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hd hβ P
  exact vortexR_le_of_zR_ge h32
    (zR_cubic_ge_of_defectW hβ (side_facts L β).1 (side_facts L β).2 hδ0 hδ hd P)

/-- **The three residual rectangular sheets from the defect.** -/
theorem physVortexRect_of_physDefect {L δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 68 * δ ≤ 2) (h32 : 32 * δ < 1)
    (h : ApertureBridge.PhysDefect L δ) :
    ApertureBridge.PhysVortexRect L (32 * δ / (1 - 32 * δ)) := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hd hβ
  obtain ⟨hn, he⟩ := side_facts L β
  exact ⟨vortexR_le_of_zR_ge h32 (zR_Lc_ge_of_defectW hβ hn he hδ0 hδ hd 1 ⟨2, by decide⟩),
    vortexR_le_of_zR_ge h32 (zR_Lc_ge_of_defectW hβ hn he hδ0 hδ hd 1 ⟨3, by decide⟩),
    vortexR_le_of_zR_ge h32 (zR_Lc_ge_of_defectW hβ hn he hδ0 hδ hd 2 ⟨3, by decide⟩)⟩

/-- **The zero-flux defects from the defect** (`sectors_of_defectWN`: at most `2δ`). -/
theorem physTrivial_of_physDefect {L δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 68 * δ ≤ 2) (h2 : 2 * δ ≤ 1 / 80000)
    (h : ApertureBridge.PhysDefect L δ) : ApertureBridge.PhysTrivial L := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hd hβ i
  obtain ⟨hn, he⟩ := side_facts L β
  have := (CentreSectorSeedN.sectors_of_defectWN (N := 2) hβ hn he hδ0
    (by norm_num; linarith) hd i).2
  linarith

end Phys

/-! ## 3. The sharp seed at a larger physical size -/

section Sharp

open Real MassGap.DoublingRecursion MassGap.DoublingWilson MassGap.ZoomSelfScale

/-- **The sharp squarings of a seed along the dyadic sides**: `250 · defectW (2ᵏ n) ≤ (1/4)^{2ᵏ}`. -/
theorem defectW_pow_sharp {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h0 : defectW 2 β n ≤ 1 / 1000) (k : ℕ) :
    250 * defectW 2 β (2 ^ k * n) ≤ (1 / 4) ^ (2 ^ k) := by
  have hfr := factRep (N := 2) (by norm_num) hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xW 2 n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0]; exact h0
  have hi := DoublingSharp.iterate_sharp hx hp (by linarith) k
  rwa [WDeltaRun.Δ_corner] at hi

/-- **The run seed gives the defect at `(1/4)^{2^j}/250`** at the physical size `2^{j+1} C`. -/
theorem physDefect_sharp_of_runSeed (h : WDeltaRun.RunSeed 2) (j : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ApertureBridge.PhysDefect L ((1 / 4) ^ (2 ^ j) / 250) := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨2 ^ (j + 1) * C, by positivity, ?_⟩
  filter_upwards [hev, WeakCouplingWindow.eventually_aRun_le (N := 2) (by norm_num)
    (b := 2 ^ (j + 1) * C / 4) (by positivity), eventually_gt_atTop (0 : ℝ)] with β hβn ha hβ
  obtain ⟨n, ⟨b, hb⟩, hn2, hna, hd⟩ := hβn
  have hsp := (physSide_spec (L := 2 ^ (j + 1) * C) hβ (by linarith)).2
  have hapos : 0 < AsymptoticScaling.aRun 2 β := AsymptoticScaling.aRun_pos (by norm_num) hβ
  set K := kPhys (2 ^ (j + 1) * C) β + 2 with hK
  have hlt : (2 : ℝ) ^ j * (n : ℝ) < 2 ^ K := by
    by_contra hc
    replace hc := not_lt.mp hc
    have h1 : (2 : ℝ) ^ K * AsymptoticScaling.aRun 2 β ≤ 2 ^ j * C :=
      calc (2 : ℝ) ^ K * AsymptoticScaling.aRun 2 β
          ≤ (2 ^ j * (n : ℝ)) * AsymptoticScaling.aRun 2 β :=
            mul_le_mul_of_nonneg_right hc hapos.le
        _ = 2 ^ j * ((n : ℝ) * AsymptoticScaling.aRun 2 β) := by ring
        _ ≤ 2 ^ j * C := mul_le_mul_of_nonneg_left hna (by positivity)
    have e : (2 : ℝ) ^ (j + 1) * C = 2 * (2 ^ j * C) := by ring
    linarith
  subst hb
  have hltN : 2 ^ (j + b) < 2 ^ K := by
    rw [pow_add]
    exact_mod_cast hlt
  have hjb : j + b < K := by
    by_contra hc
    replace hc := not_lt.mp hc
    exact absurd (lt_of_lt_of_le hltN (Nat.pow_le_pow_right (by norm_num) hc)) (lt_irrefl _)
  have he : Even (2 ^ b) := by
    rcases b with _ | b
    · norm_num at hn2
    · exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hp := defectW_pow_sharp hβ.le hn2 he hd (K - b)
  rw [← pow_add, Nat.sub_add_cancel (by omega : b ≤ K)] at hp
  have hq : ((1 : ℝ) / 4) ^ (2 ^ (K - b)) ≤ (1 / 4) ^ (2 ^ j) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  show defectW 2 β (2 ^ K) ≤ (1 / 4) ^ (2 ^ j) / 250
  rw [le_div_iff₀ (by norm_num)]
  linarith

end Sharp

/-! ## 4. The equivalence -/

/-- **The run seed at `SU(2)` is the vortex free energies and the zero-flux defect at one physical size.** -/
theorem runSeed_iff_vortex :
    WDeltaRun.RunSeed 2 ↔ ∃ L : ℝ, 0 < L ∧ PhysVortexR L (1 / 720000) ∧
      ApertureBridge.PhysVortexRect L (1 / 720000) ∧ ApertureBridge.PhysTrivial L := by
  constructor
  · intro h
    obtain ⟨L, hL, hD⟩ := physDefect_sharp_of_runSeed h 4
    have hδv : ((1 : ℝ) / 4) ^ (2 ^ 4) / 250 = 1 / 1073741824000 := by norm_num
    rw [hδv] at hD
    have hε : 32 * (1 / 1073741824000 : ℝ) / (1 - 32 * (1 / 1073741824000)) ≤ 1 / 720000 := by
      norm_num
    refine ⟨L, hL, ?_, ?_, physTrivial_of_physDefect (by norm_num) (by norm_num) (by norm_num) hD⟩
    · exact Filter.Eventually.mono
        (physVortexR_of_physDefect (by norm_num) (by norm_num) (by norm_num) hD)
        fun β hβ P => (hβ P).trans hε
    · exact Filter.Eventually.mono
        (physVortexRect_of_physDefect (by norm_num) (by norm_num) (by norm_num) hD)
        fun β hβ => ⟨hβ.1.trans hε, hβ.2.1.trans hε, hβ.2.2.trans hε⟩
  · rintro ⟨L, hL, hV, hR, hT⟩
    have hV' := physVortexR_iff.mp hV
    exact ApertureBridge.runSeed_of_physDefect hL
      (ApertureBridge.physDefect_of_physVortex hV' (by norm_num) (by norm_num)
        (ApertureBridge.physRest_of_vortexRect hV' (by norm_num) (by norm_num) hR le_rfl hT))

/-! ## 5. The strong-coupling hypothesis at weak coupling -/

/-- **The Dobrushin hypothesis of `VortexStrong` fails eventually in `β`**: `1/128 < 4225 · rate β · e` at every
`β ≥ 1`. -/
theorem not_dob_eventually :
    ∀ᶠ β in atTop, 1 / 128 < 4225 * (ChunkActivity.rate β * Real.exp 1) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
  have h3 : 3 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hmul : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-2)
  have h4 : Real.exp (-2) ≤ 1 / 3 := by nlinarith
  have h5 : Real.exp (-(2 * β)) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  have hr : 2 / 3 ≤ ChunkActivity.rate β := by
    unfold ChunkActivity.rate
    linarith
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hre : 2 / 3 ≤ ChunkActivity.rate β * Real.exp 1 := by nlinarith
  linarith

end MassGap.RunSeedLink

end

#print axioms MassGap.RunSeedLink.one_sub_twistRatioN_le_fluxShare
#print axioms MassGap.RunSeedLink.zR_Lc_ge_of_defectW
#print axioms MassGap.RunSeedLink.zR_cubic_ge_of_defectW
#print axioms MassGap.RunSeedLink.vortexR_le_of_zR_ge
#print axioms MassGap.RunSeedLink.physVortexR_iff
#print axioms MassGap.RunSeedLink.side_facts
#print axioms MassGap.RunSeedLink.physVortexR_of_physDefect
#print axioms MassGap.RunSeedLink.physVortexRect_of_physDefect
#print axioms MassGap.RunSeedLink.physTrivial_of_physDefect
#print axioms MassGap.RunSeedLink.defectW_pow_sharp
#print axioms MassGap.RunSeedLink.physDefect_sharp_of_runSeed
#print axioms MassGap.RunSeedLink.runSeed_iff_vortex
#print axioms MassGap.RunSeedLink.not_dob_eventually
