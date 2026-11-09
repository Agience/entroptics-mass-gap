import Mathlib
import MassGap.PairCorrSharp
import MassGap.WeightedProfile15

noncomputable section

/-!
# MassGap.BoxGapBE — the side-15 box gap at the aRun peak for `SU(2)` and `SU(3)`, and what remains

## What it gives

1. `clay15_of_localGap`: `WeightedProfile15.clay15` with the box input `BoxPatch.BoxLocalGap hN β₀ 15 γ`
   in place of `BoxGap.BoxFibreGap hN β₀ 15 γ`. The weighted chain (`WeightedBox.irGapAt_weightedBox`)
   reads only the local gap; `BoxFibreGap` is one sufficient condition for it
   (`BoxGap.boxLocalGap_of_fibreGap`), the pair route (`BoxGap.boxLocalGap_of_pairDefect`) is another.
2. `boxLocalGap15_su3`: `BoxLocalGap (floorBeta 3) 15 (367/2500)` from the two-link correlation bound
   `PairCorrSharp.boxPairCorr_floor_su3` (`Δ = 2133/2500`). `floorBeta N = 17N²/(88π²)` is the peak of
   `AsymptoticScaling.aRun N`.
3. `boxPairCorr_su2_c`, `boxLocalGap15_su2`: for `SU(2)` at `β = 3/40`, the two fibre bounds
   `δ₁ ≤ 249/5000`, `δ₂ ≤ 129/1250` (`pairCheck_su2_single_c`, `pairCheck_su2_double_c`, `norm_num`
   on rationals), `Δ = 12δ₁ + 3δ₂ = 567/625` and `BoxLocalGap (3/40) 15 (58/625)`.
4. `clay_of_uvStep_su3`, `clay_of_uvStep_su2`: the continuum Clay statement from the UV step below the
   box's weighted rate at `β₀ = floorBeta 3` (`SU(3)`) and `β₀ = 3/40` (`SU(2)`), with E, N, Y. The box
   input of `clay15` is discharged at those couplings.
5. `exp_le_clusterRate`, `weightedRate_le`: every weighted box rate is at most `1/508` in lattice units,
   `weightedRate N β c ≤ (1/508)/aRun N β`, whatever the box constant `c`.
6. `irGapAt_weightedRate_strong`, `clay15_strong_without_box`: below a coupling `βsc > 0` the proved
   strong-coupling gap (`PeriodicStrongCoupling.periodic_gapAt_strong_coupling`) already gives
   `IRGapAt` at every weighted box rate, so there `clay15` holds without any box input. A box gap
   adds content only above the strong-coupling base.

## The coupling window

The tree's formal strong-coupling base holds where `coreRate 64 β < 1`, `β < 2.94·10⁻⁵`. The pair route
reaches `β = 3/40` for `SU(2)` (the gap `1 − Δ(β)` crosses `0.0759` at `β ≈ 0.07594`) and
`floorBeta 3 ≈ 0.1762` for `SU(3)` (crossing at `β ≈ 0.1821`): three to four orders of magnitude past
the base, at the peak of `aRun`, still on the strong-coupling side of the physical crossover
(Lean `β ≈ 1.1` at `N = 2`, `≈ 2.85` at `N = 3`).

## What does not follow

* No `BoxFibreGap` is proved; the box input is discharged in its local form, which is all `clay15`
  consumes.
* The gaps are for `N = 2` and `N = 3` only, through the Haar constants of
  `HaarMomentsSU2`, `HaarMomentsSU3`. For general `N` the linear bound
  (`PairCorr.pairCorrLinear_holds`, `Δ = 120960β`) reaches `γ ≥ 0.0759` only at `β ≤ 7.6·10⁻⁶`,
  inside the strong-coupling base, where (6) shows the box adds nothing.
* The UV step `RestoreShimsClay.UVBelowIR` at those couplings, and E, N, Y, stay open. The rate the UV step
  must stay below is small: in lattice units `min(c₀, 1)/508` with
  `c₀ = (a₁²/(15⁴K))(γ − 0.07589)`, `≈ 3.1·10⁻⁵` (`SU(2)`, `γ = 58/625`) and `≈ 1.3·10⁻⁴`
  (`SU(3)`, `γ = 367/2500`); with `aRun ≈ 0.610` at both couplings, `M₀ ≈ 5.1·10⁻⁵` and `≈ 2.1·10⁻⁴`.
  The loss budget along the dyadic tower from `aRun N β₀` must sum below that, through the crossover.
* Bakry–Émery on `SU(N)` is not used: the tree states its constant (`CondGap.beConst`) without the
  criterion, and the criterion bounds the gradient form, not the heat-bath form `Σ_l (1 − E_l)` of
  `BoxFibreGap`.

DERIVED (module-wide): `15` the box side of `WeightedProfile15`; `759/10000` its threshold, rounded up;
`4` the spacetime dimension; `0` the reflection plane, the excluded rank and the lower ends; `2`, `3`
the ranks; `508 = 4 · 127`, `127 = 6 · 21 + 1`, `21` the neighbour bound of `clusterRate 21`.
-/

namespace MassGap.BoxGapBE

open MassGap MassGap.BoxGap MassGap.WeightedProfile15 MassGap.WeightedProduct
open MassGap.PairCorrSharp MassGap.PairInterface MassGap.PairFibreAbstract MassGap.TiltedHaar
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open Filter Topology

variable {N : ℕ}

/-! ## 1. `clay15` from the local gap -/

section Local

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the box's local gap at side 15.** As
`WeightedProfile15.clay15`, with `BoxPatch.BoxLocalGap hN β₀ 15 γ` as the box input
(`WeightedBox.irGapAt_weightedBox`, `RestoreShimsClay.clay_continuum_of_irGap`, `ProfileData.toFamily`).

DERIVED: `2` the least rank with a non-zero Haar variance; `15` the box side; `759/10000` the rounded
threshold `thr15`; `0` the reflection plane and the excluded rank; `1` the least colour count and box
side; `4` the spacetime dimension. -/
theorem clay15_of_localGap (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀) (hγ : 759 / 10000 ≤ γ)
    (hbox : BoxPatch.BoxLocalGap hN β₀ 15 γ)
    (huv : ClayRoutes.UVBelowIR τ 0 hN β₀ βUV
      (MassGap.WeightedBox.weightedRate N β₀
        (MassGap.WeightedBox.weightedConst 15 P15.a₁ P15.a₂ P15.K P15.e γ)))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  ClayRoutes.clay_continuum_of_irGap hN2 hN Z τ hZ hB hL hβ₀ hUVβ₀
    (MassGap.WeightedBox.irGapAt_weightedBox τ 0 (by omega) hN hβ₀ (by norm_num)
      (lt_of_lt_of_le (by norm_num) hγ) K15_pos a15_ne (lt_of_lt_of_le thr15 hγ) hbox
      (fun j hnj => P15.toFamily hN β₀ (by norm_num) j hnj)).2 huv O G hconv hY

#print axioms clay15_of_localGap

end Local

/-! ## 2. The local gap at side 15 -/

section Box

/-- **`SU(3)` at the aRun peak: `BoxLocalGap (floorBeta 3) 15 (367/2500)`**
(`PairCorrSharp.boxPairCorr_floor_su3`, `BoxGap.boxPairDefect_of_pairCorr`,
`BoxGap.boxLocalGap_of_pairDefect`, which holds at every side).

DERIVED: `3` the rank; `15` the box side; `367/2500 = 1 − 2133/2500`. -/
theorem boxLocalGap15_su3 (h3 : (3 : ℕ) ≠ 0) :
    BoxPatch.BoxLocalGap h3 (floorBeta 3) 15 (367 / 2500) := by
  have h := boxLocalGap_of_pairDefect h3 15
    (boxPairDefect_of_pairCorr h3 (boxPairCorr_floor_su3 h3))
  have hg : (1 : ℝ) - 2133 / 2500 = 367 / 2500 := by norm_num
  rw [hg] at h
  exact h

#print axioms boxLocalGap15_su3

/-- **`SU(2)`, single pair at `β = 3/40`** (`n2 = 2`): `dstar ≤ 249/5000` at `τ = 2 · 3/40`,
`κ = 10 · 3/40`.

DERIVED: `4`, `1/8`, `0` are `HaarMomentsSU2.haarConsts_su2`'s `D`, `q4`, `t3`; `2`, `10` the single
pair's counts. CHOSEN: `3/40`, the three-digit rational below `β ≈ 0.07594`, where the pair route's
gap `1 − 12δ₁ − 3δ₂` crosses `0.0759` (the bounds at `3/40` are checked by `norm_num` in this
theorem); `1768/10000 ≥ √(1/32)`; `68/125 ≥ √M₂ = √0.29591…`; `249/5000` rounds `0.0497533…` up. -/
theorem pairCheck_su2_single_c :
    PairCheck 4 (1 / 8) 0 (1768 / 10000) (68 / 125) (2 * (3 / 40)) (10 * (3 / 40))
      (249 / 5000) := by
  norm_num [PairCheck, dstar, dstarNum, dstarDen, dstarE, dstarZ, M2bound, mbarBound, cR, cR3]

#print axioms pairCheck_su2_single_c

/-- **`SU(2)`, double pair at `β = 3/40`** (`n2 = 4`): `dstar ≤ 129/1250`.

DERIVED: `4`, `1/8`, `0` as in `pairCheck_su2_single_c`; `4`, `8` the double pair's counts. CHOSEN:
`3/40`, `1768/10000` as in `pairCheck_su2_single_c`; `5271/10000 ≥ √M₂`; `129/1250` rounds `0.1031809…`
up. -/
theorem pairCheck_su2_double_c :
    PairCheck 4 (1 / 8) 0 (1768 / 10000) (5271 / 10000) (4 * (3 / 40)) (8 * (3 / 40))
      (129 / 1250) := by
  norm_num [PairCheck, dstar, dstarNum, dstarDen, dstarE, dstarZ, M2bound, mbarBound, cR, cR3]

#print axioms pairCheck_su2_double_c

/-- **The `SU(2)` box pair correlation at `β = 3/40`**: `Δ = max(18 · 249/5000, 12 · 249/5000 +
3 · 129/1250) = 567/625` (`fibreBound_of_pairCheck`, `boxPairCorr_sharp`).

DERIVED: `2` the rank; `18`, `12`, `3` the defect row counts of `pairDeltaSharp`;
`567/625 = 0.9072` the larger branch. CHOSEN: `3/40` as in `pairCheck_su2_single_c`. -/
theorem boxPairCorr_su2_c (h2 : (2 : ℕ) ≠ 0) : BoxPairCorr h2 (3 / 40) (567 / 625) := by
  have hF1 : FibreBound (probHaar (SU 2)) (realFeature 2) (249 / 5000) (2 * (3 / 40))
      (10 * (3 / 40)) :=
    fibreBound_of_pairCheck h2 HaarMomentsSU2.haarConsts_su2 pairCheck_su2_single_c
  have hF2 : FibreBound (probHaar (SU 2)) (realFeature 2) (129 / 1250) (4 * (3 / 40))
      (8 * (3 / 40)) :=
    fibreBound_of_pairCheck h2 HaarMomentsSU2.haarConsts_su2 pairCheck_su2_double_c
  have h := boxPairCorr_sharp h2 (by norm_num) hF1 hF2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hmax : max (18 * (249 / 5000 : ℝ)) (12 * (249 / 5000) + 3 * (129 / 1250)) = 567 / 625 := by
    rw [max_eq_right (show (18 * (249 / 5000 : ℝ)) ≤ 12 * (249 / 5000) + 3 * (129 / 1250) by
      norm_num)]
    norm_num
  rw [hmax] at h
  exact h

#print axioms boxPairCorr_su2_c

/-- **`SU(2)` at `β = 3/40`: `BoxLocalGap (3/40) 15 (58/625)`** (`boxPairCorr_su2_c`,
`BoxGap.boxLocalGap_of_pairDefect`).

DERIVED: `2` the rank; `15` the box side; `58/625 = 1 − 567/625 = 0.0928`. CHOSEN: `3/40` as in
`pairCheck_su2_single_c`. -/
theorem boxLocalGap15_su2 (h2 : (2 : ℕ) ≠ 0) : BoxPatch.BoxLocalGap h2 (3 / 40) 15 (58 / 625) := by
  have h := boxLocalGap_of_pairDefect h2 15 (boxPairDefect_of_pairCorr h2 (boxPairCorr_su2_c h2))
  have hg : (1 : ℝ) - 567 / 625 = 58 / 625 := by norm_num
  rw [hg] at h
  exact h

#print axioms boxLocalGap15_su2

end Box

/-! ## 3. What remains: the UV step at the box's coupling -/

section Remains

open MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **`SU(3)`: the continuum Clay statement from the UV step at the aRun peak.** At
`β₀ = floorBeta 3`, `βUV ≤ β₀`: the UV step below the weighted rate of the side-15 box at
`γ = 367/2500`, and E, N, Y, give `ClayContinuum` (`clay15_of_localGap`, `boxLocalGap15_su3`).

DERIVED: `3` the rank; `15`, `367/2500` the side and gap of `boxLocalGap15_su3`; `0` the reflection
plane; `4` the spacetime dimension. -/
theorem clay_of_uvStep_su3 (h3 : (3 : ℕ) ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU 3) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep h3 (Renorm.connected h3 Z)) {L : ℝ} (hL : 0 < L)
    {βUV : ℝ} (hUV : βUV ≤ floorBeta 3)
    (huv : ClayRoutes.UVBelowIR τ 0 h3 (floorBeta 3) βUV
      (MassGap.WeightedBox.weightedRate 3 (floorBeta 3)
        (MassGap.WeightedBox.weightedConst 15 P15.a₁ P15.a₂ P15.K P15.e (367 / 2500))))
    (O : LField (MassGap.SUN.SU 3)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep h3 (Renorm.connected h3 Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum h3 Z τ hZ hB L :=
  clay15_of_localGap (by norm_num) h3 Z τ hZ hB hL (floorBeta_pos h3) hUV (by norm_num)
    (boxLocalGap15_su3 h3) huv O G hconv hY

#print axioms clay_of_uvStep_su3

/-- **`SU(2)`: the continuum Clay statement from the UV step at `β₀ = 3/40`.** The UV step below
the weighted rate of the side-15 box at `γ = 58/625`, and E, N, Y, give `ClayContinuum`
(`clay15_of_localGap`, `boxLocalGap15_su2`).

DERIVED: `2` the rank; `3/40`, `15`, `58/625` the coupling, side and gap of `boxLocalGap15_su2`; `0`
the reflection plane; `4` the spacetime dimension. -/
theorem clay_of_uvStep_su2 (h2 : (2 : ℕ) ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU 2) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep h2 (Renorm.connected h2 Z)) {L : ℝ} (hL : 0 < L)
    {βUV : ℝ} (hUV : βUV ≤ 3 / 40)
    (huv : ClayRoutes.UVBelowIR τ 0 h2 (3 / 40) βUV
      (MassGap.WeightedBox.weightedRate 2 (3 / 40)
        (MassGap.WeightedBox.weightedConst 15 P15.a₁ P15.a₂ P15.K P15.e (58 / 625))))
    (O : LField (MassGap.SUN.SU 2)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep h2 (Renorm.connected h2 Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum h2 Z τ hZ hB L :=
  clay15_of_localGap (by norm_num) h2 Z τ hZ hB hL (by norm_num) hUV (by norm_num)
    (boxLocalGap15_su2 h2) huv O G hconv hY

#print axioms clay_of_uvStep_su2

end Remains

/-! ## 4. Every box rate is small, and below the strong-coupling base the box adds nothing -/

section Rates

/-- **`clusterRate 21 c ≥ e^{−1/508}`** at every `c`: `min(c, 1) ≤ 1` in the exponent
`−min(c, 1)/(2 · 127)`, and the square root halves `1/254`.

DERIVED: `21` the neighbour bound; `127 = 6 · 21 + 1`; `254 = 2 · 127`; `508 = 2 · 254` from the
square root; `1` the clip of `min c 1`. -/
theorem exp_le_clusterRate (c : ℝ) :
    Real.exp (-(1 / 508)) ≤ HeatBathGapDecay.clusterRate 21 c := by
  unfold HeatBathGapDecay.clusterRate
  have h2 : Real.sqrt (Real.exp (-(1 / 254))) = Real.exp (-(1 / 508)) := by
    rw [show (-(1 / 254 : ℝ)) = -(1 / 508) + -(1 / 508) by norm_num, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [← h2]
  apply Real.sqrt_le_sqrt
  refine le_trans ?_ (le_max_right _ _)
  apply Real.exp_le_exp.mpr
  have hm : min c 1 ≤ 1 := min_le_right _ _
  have hd : min c 1 / (2 * ((6 * 21 + 1 : ℕ) : ℝ)) ≤ 1 / 254 := by
    rw [div_le_iff₀ (by norm_num)]
    push_cast
    linarith
  linarith

#print axioms exp_le_clusterRate

/-- **Every weighted box rate is at most `1/508` in lattice units**: at `0 < aRun N β`,
`weightedRate N β c ≤ (1/508)/aRun N β` (`exp_le_clusterRate`).

DERIVED: `508` as in `exp_le_clusterRate`; `0` the sign of the spacing. -/
theorem weightedRate_le {β : ℝ} (ha : 0 < MassGap.AsymptoticScaling.aRun N β) (c : ℝ) :
    MassGap.WeightedBox.weightedRate N β c ≤ (1 / 508) / MassGap.AsymptoticScaling.aRun N β := by
  unfold MassGap.WeightedBox.weightedRate
  apply div_le_div_of_nonneg_right _ ha.le
  have hlog := Real.log_le_log (Real.exp_pos _) (exp_le_clusterRate c)
  rw [Real.log_exp] at hlog
  linarith

#print axioms weightedRate_le

/-- **Below the strong-coupling base every box rate is already an IR rate.** At `1 ≤ N` there is
`βsc > 0` such that at every `0 < β₀ < βsc` and every box constant `c`,
`UVIRSplit.IRGapAt τ p hN β₀ (weightedRate N β₀ c)`: the proved gap at rate `coreRate 64 β₀`
(`PeriodicStrongCoupling.periodic_gapAt_strong_coupling`) is below `e^{−1/508} ≤ clusterRate 21 c`
once `coreRate 64 β₀ < e^{−1/508}`, which holds near `0` by continuity (`coreRate 64 0 = 0`).

DERIVED: `16 * 4` the periodic touch-degree bound; `21`, `508` as in `exp_le_clusterRate`; `1` the
least colour count; `0` the excluded rank and the lower ends. -/
theorem irGapAt_weightedRate_strong (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) :
    ∃ βsc > 0, ∀ β₀ : ℝ, 0 < β₀ → β₀ < βsc → ∀ c : ℝ,
      UVIRSplit.IRGapAt τ p hN β₀ (MassGap.WeightedBox.weightedRate N β₀ c) := by
  obtain ⟨b, hb, h⟩ := PeriodicStrongCoupling.periodic_gapAt_strong_coupling (N := N) τ p hN
  have hcont : Continuous (fun β : ℝ => StrongCoupling.coreRate (16 * 4) β) := by
    unfold StrongCoupling.coreRate
    fun_prop
  have h0 : StrongCoupling.coreRate (16 * 4) 0 = 0 := by
    simp [StrongCoupling.coreRate]
  have ht : Tendsto (fun β : ℝ => StrongCoupling.coreRate (16 * 4) β) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto 0
    simpa only [h0] using this
  have hev : ∀ᶠ β in 𝓝 (0 : ℝ), StrongCoupling.coreRate (16 * 4) β < Real.exp (-(1 / 508)) :=
    ht.eventually (gt_mem_nhds (Real.exp_pos _))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min b ε, lt_min hb hε, fun β₀ hβ₀ hlt c => ?_⟩
  have hβb : β₀ < b := lt_of_lt_of_le hlt (min_le_left _ _)
  have hβε : β₀ < ε := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨hc0, _, hg⟩ := h β₀ hβ₀ hβb
  have hcore : StrongCoupling.coreRate (16 * 4) β₀ < Real.exp (-(1 / 508)) := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos hβ₀]
    exact hβε
  have ha : 0 < MassGap.AsymptoticScaling.aRun N β₀ :=
    MassGap.AsymptoticScaling.aRun_pos hN1 hβ₀
  have hcr : 0 < HeatBathGapDecay.clusterRate 21 c :=
    lt_of_lt_of_le (Real.exp_pos _) (exp_le_clusterRate c)
  unfold UVIRSplit.IRGapAt MassGap.WeightedBox.weightedRate
  rw [div_mul_cancel₀ _ ha.ne', neg_neg, Real.exp_log hcr]
  exact GapStep.gapAt_mono _ hc0.le (hcore.le.trans (exp_le_clusterRate c)) hg

#print axioms irGapAt_weightedRate_strong

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **Below the strong-coupling base `clay15` needs no box.** At `2 ≤ N` there is `βsc > 0` such
that for `0 < β₀ < βsc`, `βUV ≤ β₀` and any box constant `c`, the UV step below
`weightedRate N β₀ c` and E, N, Y give `ClayContinuum` (`irGapAt_weightedRate_strong`,
`RestoreShimsClay.clay_continuum_of_irGap`). So a box gap carries content only at `β₀ ≥ βsc`.

DERIVED: `2` the least rank with a non-zero Haar variance; `0` the reflection plane, the excluded
rank and the lower ends; `4` the spacetime dimension. -/
theorem clay15_strong_without_box (hN2 : 2 ≤ N) (hN : N ≠ 0) (τ : Fin 4) :
    ∃ βsc > 0, ∀ (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
      (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) (L : ℝ), 0 < L →
      ∀ β₀ βUV c : ℝ, 0 < β₀ → β₀ < βsc → βUV ≤ β₀ →
      ClayRoutes.UVBelowIR τ 0 hN β₀ βUV (MassGap.WeightedBox.weightedRate N β₀ c) →
      ∀ (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ),
      ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
        (fun p q => G (ContinuumNontrivial.eDist p q)) →
      ShortDistanceY.AFShortDistance G → ClayRoutes.ClayContinuum hN Z τ hZ hB L := by
  obtain ⟨βsc, hβsc, h⟩ := irGapAt_weightedRate_strong τ 0 (by omega : 1 ≤ N) hN
  refine ⟨βsc, hβsc, ?_⟩
  intro Z hZ hB L hL β₀ βUV c hβ₀ hlt hUV huv O G hconv hY
  exact ClayRoutes.clay_continuum_of_irGap hN2 hN Z τ hZ hB hL hβ₀ hUV (h β₀ hβ₀ hlt c) huv O G
    hconv hY

#print axioms clay15_strong_without_box

end Rates

end MassGap.BoxGapBE
