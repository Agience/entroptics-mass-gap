import Mathlib
import MassGap.CentreSectorSeed
import MassGap.CentreSectorSeedN
import MassGap.HeatBathErgodic

/-!
# MassGap.CentreSectorSeedTwo — the SU(N) sector split at `N = 2` is the SU(2) sector split

`CentreSectorSeed` splits the SU(2) step kernel with the three centre flips of a slice, applied one
after another (`SectorDefect.evL`). `CentreSectorSeedN` splits the SU(N) step kernel with the centre
`Z_N³` of `SliceCentreAction`, averaging over the group (`ZeroFluxSector.zk`). At `N = 2` the two
are the same objects, not only up to relabelling.

**The flips are the generators of the action** (`centreFlip_eq_act`): the flip in direction `ν`
multiplies by `−1` the links of direction `ν` with `ν`-coordinate `0`, and `act (Pi.single ν 1)`
multiplies the same links by `e(1) = exp(πi) = −1` (`stdAddChar_one_two`).

**Even under every flip is invariant under the whole group** (`evL_eq_zk`, abstract). For a list `l`
of commuting involutions, each an element of a finite abelian action, and generating it:
* `evL b l` is right-invariant under every flip of `l` (`evL_right_inv_mem`), hence under the whole
  group, so averaging it over the group returns it (`zk_eq_of_right_inv`);
* averaging commutes with taking even parts: `zk (ev b (act h)) = zk b` (`zk_ev`, `zk_evL`).
So `evL b l = zk (evL b l) = zk b`. On a slice the three flips generate `Z_2³`
(`right_inv_act_of_flips`, by `Pi.single_induction`), so `evL b (flips) = zk b act` for every kernel
`b` (`evL_flips_eq_zk`).

**The bridges.** `halfKN 2 = halfK` (definitional), `trivKN 2 = trivK`, `fluxShareN 2 = fluxShare`,
`trivialDefectN 2 = trivialDefect`, `fluxShareDoubledN 2 = fluxShareDoubled`, the single-plane
twisted ratios
`twistRatioN 2 (Pi.single ν 1) = twistRatio [centreFlip ν]`, and the seed proposition
(`sectorSeedPowN_two_iff`).

**The SU(2) theorems as the `N = 2` instances.** Each theorem below has the statement of the
SU(2) theorem of the same name (in `CentreSectorSeed` or `FluxShareSquaring`) and is
proved from the `N`-form at `N = 2` and the bridges: `defectW_le_of_sectors`, `sectors_of_defectW`,
`seedExistsPow_iff_sectorSeedPow`, `fluxShareDoubled_le`. The one place the
statements differ is the hypothesis of necessity: `sectors_of_defectW` asks `δ ≤ 1/1000`, the
`N`-form asks `(4 + N⁶) δ ≤ 2`, which at `N = 2` is `δ ≤ 1/34`, so the `N`-form is the more general;
both return `4δ` and `2δ`. `fluxShare_eq_mean` writes the flux share as the mean over the eight
elements of `Z_2³`; `FluxShareSquaring.fluxShare_eq_mean` writes it over the eight sublists of the
flips, the same eight twisted traces.

DERIVED (module-wide): `2` is `N`; `1` is the generator of `Z_2`; `−1 = e(1)` at `N = 2`;
`68 = 4 + 2⁶` and `4 = 2³/2` are the `N`-form's constants at `N = 2`; `1/1000` is
`CentreSectorSeed.sectors_of_defectW`'s hypothesis.
-/

noncomputable section

namespace MassGap.CentreSectorSeedTwo

open MeasureTheory Filter MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.SectorDefect MassGap.FluxSectorBound MassGap.ZeroFluxSector
  MassGap.FluxSectorFourier

/-! ## 1. Even under commuting generating flips is the group average -/

section Abstract

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsProbabilityMeasure ρ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {act : G → X → X}

omit [MeasurableSpace X] in
/-- Taking the even part under `σ` keeps right-invariance under a `τ` commuting with `σ`. -/
theorem ev_right_inv {b : X → X → ℝ} {σ τ : X → X} (hc : ∀ x, σ (τ x) = τ (σ x))
    (hb : ∀ x y, b x (τ y) = b x y) (x y : X) : ev b σ x (τ y) = ev b σ x y := by
  simp only [ev]
  rw [hb x y, hc y, hb x (σ y)]

omit [MeasurableSpace X] in
/-- The even part under an involution is right-invariant under it. -/
theorem ev_self_right_inv {b : X → X → ℝ} {σ : X → X} (hσ : ∀ x, σ (σ x) = x) (x y : X) :
    ev b σ x (σ y) = ev b σ x y := by
  simp only [ev]
  rw [hσ y, add_comm]

omit [MeasurableSpace X] in
theorem evL_right_inv : ∀ (l : List (X → X)) (b : X → X → ℝ) (τ : X → X),
    (∀ σ ∈ l, ∀ x, σ (τ x) = τ (σ x)) → (∀ x y, b x (τ y) = b x y) →
    ∀ x y, evL b l x (τ y) = evL b l x y
  | [], _, _, _, hb => hb
  | σ :: l, b, τ, hc, hb =>
    evL_right_inv l (ev b σ) τ (fun ρ' hρ' => hc ρ' (List.mem_cons_of_mem σ hρ'))
      (ev_right_inv (hc σ List.mem_cons_self) hb)

/-- **The kernel even under every flip of `l` is right-invariant under each of them.** -/
theorem evL_right_inv_mem : ∀ (l : List (X → X)), Flips ρ l → ∀ (b : X → X → ℝ), ∀ σ ∈ l,
    ∀ x y, evL b l x (σ y) = evL b l x y
  | [], _, _, σ, h => by simp at h
  | τ :: l, hl, b, σ, h => by
    intro x y
    rcases List.mem_cons.mp h with h' | h'
    · rw [h']
      exact evL_right_inv l (ev b τ) τ
        (fun τ' hτ' => hl.2 τ' (List.mem_cons_of_mem τ hτ') τ List.mem_cons_self)
        (ev_self_right_inv (hl.1 τ List.mem_cons_self).invol) x y
    · exact evL_right_inv_mem l hl.tail (ev b τ) σ h' x y

omit [IsProbabilityMeasure ρ] [DecidableEq G] in
/-- **Averaging over the group absorbs an even part.** -/
theorem zk_ev (hA : CentreAction ρ act) (b : X → X → ℝ) (h : G) :
    zk (ev b (act h)) act = zk b act := by
  funext x y
  simp only [zk, ev]
  congr 1
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have e : ∑ g, b x (act h (act g y)) = ∑ g, b x (act g y) := by
    simp_rw [← hA.add]
    exact Equiv.sum_comp (Equiv.addLeft h) (fun g => b x (act g y))
  rw [e]
  ring

omit [IsProbabilityMeasure ρ] [DecidableEq G] in
theorem zk_evL (hA : CentreAction ρ act) : ∀ (l : List (X → X)) (b : X → X → ℝ),
    (∀ σ ∈ l, ∃ h, σ = act h) → zk (evL b l) act = zk b act
  | [], _, _ => rfl
  | σ :: l, b, hl => by
    obtain ⟨h, hσ⟩ := hl σ List.mem_cons_self
    rw [evL_cons, zk_evL hA l (ev b σ) (fun τ hτ => hl τ (List.mem_cons_of_mem _ hτ)), hσ,
      zk_ev hA]

omit [MeasurableSpace X] in
/-- **A kernel right-invariant under the whole group is its own group average.** -/
theorem zk_eq_of_right_inv (b : X → X → ℝ) (hb : ∀ g x y, b x (act g y) = b x y) :
    zk b act = b := by
  funext x y
  simp only [zk, hb, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (card_pos_real (G := G)).ne', one_mul]

/-- **Even under commuting generating flips is the group average**: if every flip of `l` is an
element of the action and right-invariance under the flips of `l` gives right-invariance under the
group, then `evL b l = zk b act`. -/
theorem evL_eq_zk (hA : CentreAction ρ act) (l : List (X → X)) (hl : Flips ρ l)
    (hmem : ∀ σ ∈ l, ∃ h, σ = act h)
    (hgen : ∀ b : X → X → ℝ, (∀ σ ∈ l, ∀ x y, b x (σ y) = b x y) →
      ∀ g x y, b x (act g y) = b x y)
    (b : X → X → ℝ) : evL b l = zk b act := by
  have hinv := hgen (evL b l) (evL_right_inv_mem l hl b)
  rw [← zk_eq_of_right_inv (evL b l) hinv, zk_evL hA l b hmem]

end Abstract

/-! ## 2. On a slice: the three flips generate `Z_2³` -/

section Slice

open MassGap.CentreSectorSeed (centreFlip flips flips_spec coe_centreFlip)
open MassGap.SliceCentreAction (Cen act lc coe_act centreAction)

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- `e(1) = −1` in `Z_2`. -/
theorem stdAddChar_one_two : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
  have h := ZMod.stdAddChar_coe (N := 2) 1
  simp only [Int.cast_one] at h
  rw [h]
  convert Complex.exp_pi_mul_I using 2
  push_cast
  ring

/-- The flip sign of a link is the phase of the generator in its direction. -/
theorem es_eq_stdAddChar (ν : {j : Fin 4 // j ≠ μ}) (l : SpT μ T) :
    CentreSectorSeed.es ν l = ZMod.stdAddChar (lc (Pi.single ν (1 : ZMod 2)) l) := by
  obtain ⟨d, y⟩ := l
  simp only [CentreSectorSeed.es, lc]
  by_cases hd : d = ν
  · by_cases hy : (y ν).val = 0
    · have h1 : (y d).val = 0 := by rw [hd]; exact hy
      rw [if_pos ⟨hd, hy⟩, if_pos h1, hd, Pi.single_eq_same, stdAddChar_one_two]
    · have h1 : ¬ (y d).val = 0 := by rw [hd]; exact hy
      rw [if_neg (fun h => hy h.2), if_neg h1, AddChar.map_zero_eq_one]
  · rw [if_neg (fun h => hd h.1)]
    split_ifs <;> simp [hd]

/-- **The centre flip in direction `ν` is the generator `Pi.single ν 1` of the centre action.** -/
theorem centreFlip_eq_act (ν : {j : Fin 4 // j ≠ μ}) :
    centreFlip (T := T) ν = act (μ := μ) (T := T) (N := 2) (Pi.single ν 1) := by
  funext V l
  apply Subtype.ext
  rw [coe_centreFlip, coe_act, es_eq_stdAddChar]

theorem mem_flips (ν : {j : Fin 4 // j ≠ μ}) : centreFlip (T := T) ν ∈ flips μ T :=
  List.mem_map.mpr ⟨ν, Finset.mem_toList.mpr (Finset.mem_univ ν), rfl⟩

theorem zmod_two_cases : ∀ m : ZMod 2, m = 0 ∨ m = 1 := by decide

/-- **Right-invariance under the three flips is right-invariance under `Z_2³`.** -/
theorem right_inv_act_of_flips {b : (SpT μ T → SUN.SU 2) → (SpT μ T → SUN.SU 2) → ℝ}
    (hb : ∀ σ ∈ flips μ T, ∀ x y, b x (σ y) = b x y) (g : Cen μ 2) :
    ∀ x y, b x (act g y) = b x y := by
  have hA := centreAction (μ := μ) (T := T) (N := 2)
  refine Pi.single_induction (fun g => ∀ x y, b x (act g y) = b x y) g ?_ ?_ ?_
  · intro x y
    rw [hA.zero]
  · intro f h hf hh x y
    rw [hA.add, hf, hh]
  · intro ν m x y
    rcases zmod_two_cases m with hm | hm
    · rw [hm, Pi.single_zero, hA.zero]
    · rw [hm, ← centreFlip_eq_act]
      exact hb _ (mem_flips ν) x y

/-- **The kernel even under the three flips of a slice is its `Z_2³` average.** -/
theorem evL_flips_eq_zk (b : (SpT μ T → SUN.SU 2) → (SpT μ T → SUN.SU 2) → ℝ) :
    evL b (flips μ T) = zk b (act (μ := μ) (T := T) (N := 2)) :=
  evL_eq_zk (ρ := hS μ T 2) centreAction (flips μ T) flips_spec
    (fun σ hσ => by
      obtain ⟨ν, -, rfl⟩ := List.mem_map.mp hσ
      exact ⟨_, centreFlip_eq_act ν⟩)
    (fun _ hb' => right_inv_act_of_flips hb') b

end Slice

/-! ## 3. The bridges -/

section Bridges

open MassGap.CentreSectorSeed (Tr hSi halfK trivK fluxShare trivialDefect centreFlip flips)
open MassGap.CentreSectorSeedN (hSN halfKN trivKN fluxShareN trivialDefectN twistRatioN
  fluxShareDoubledN SectorSeedPowN)
open MassGap.SliceCentreAction (Cen act)

/-- The step kernel at `N = 2` is the SU(2) step kernel. -/
theorem halfKN_two (β : ℝ) (n : ℕ) (i : Fin 4) : halfKN 2 β n i = halfK β n i := rfl

/-- **The zero-flux kernel at `N = 2` is the SU(2) trivial kernel.** -/
theorem trivKN_two (β : ℝ) (n : ℕ) (i : Fin 4) : trivKN 2 β n i = trivK β n i :=
  (evL_flips_eq_zk (halfK β n i)).symm

/-- **The flux share at `N = 2` is the SU(2) flux share.** -/
theorem fluxShareN_two (β : ℝ) (n : ℕ) (i : Fin 4) : fluxShareN 2 β n i = fluxShare β n i := by
  show (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivKN 2 β n i)) / hs (hSi n i) (halfK β n i)
    = (hs (hSi n i) (halfK β n i) - hs (hSi n i) (trivK β n i)) / hs (hSi n i) (halfK β n i)
  rw [trivKN_two]

/-- **The zero-flux defect at `N = 2` is the SU(2) trivial-sector defect.** -/
theorem trivialDefectN_two (β : ℝ) (n : ℕ) (i : Fin 4) :
    trivialDefectN 2 β n i = trivialDefect β n i := by
  show dd (hSi n i) (trivKN 2 β n i) = dd (hSi n i) (trivK β n i)
  rw [trivKN_two]

theorem fluxShareDoubledN_two (β : ℝ) (n : ℕ) (i : Fin 4) :
    fluxShareDoubledN 2 β n i = FluxShareSquaring.fluxShareDoubled β n i := by
  show (hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i))
      - hs (hSi n i) (zk (conv (hSi n i) (halfK β n i) (halfK β n i))
          (act (μ := i) (T := Tr n i) (N := 2))))
      / hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i))
    = (hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i))
      - hs (hSi n i) (evL (conv (hSi n i) (halfK β n i) (halfK β n i)) (flips i (Tr n i))))
      / hs (hSi n i) (conv (hSi n i) (halfK β n i) (halfK β n i))
  rw [evL_flips_eq_zk]

/-- **The single-plane twisted ratio at `N = 2` is the SU(2) single-flip ratio.** -/
theorem twistRatioN_single_two (β : ℝ) (n : ℕ) (i : Fin 4) (ν : {j : Fin 4 // j ≠ i}) :
    twistRatioN 2 β n i (Pi.single ν 1) = FluxShareSquaring.twistRatio β n i [centreFlip ν] := by
  show FluxSectorBound.twist (hSi n i) (halfK β n i) (act (T := Tr n i) (N := 2) (Pi.single ν 1))
      / hs (hSi n i) (halfK β n i)
    = FluxSectorBound.twist (hSi n i) (halfK β n i) (centreFlip ν) / hs (hSi n i) (halfK β n i)
  rw [centreFlip_eq_act]

theorem sectorSeedPowN_two_iff : SectorSeedPowN 2 ↔ CentreSectorSeed.SectorSeedPow := by
  unfold SectorSeedPowN CentreSectorSeed.SectorSeedPow
  simp only [fluxShareN_two, trivialDefectN_two]

end Bridges

/-! ## 4. The SU(2) theorems from the `N`-forms at `N = 2` -/

section Instances

open MassGap.CentreSectorSeed (Tr hSi halfK fluxShare trivialDefect)
open MassGap.CentreSectorSeedN (twistRatioN)
open MassGap.SliceCentreAction (Cen)

/-- `CentreSectorSeed.defectW_le_of_sectors`, from `defectW_le_of_sectorsN` at `N = 2`. -/
theorem defectW_le_of_sectors {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h : ∀ i : Fin 4, fluxShare β n i ≤ 1 / 80000 ∧ trivialDefect β n i ≤ 1 / 80000) :
    ZoomSelfScale.defectW 2 β n ≤ 1 / 1000 :=
  CentreSectorSeedN.defectW_le_of_sectorsN hβ hn he fun i => by
    rw [fluxShareN_two, trivialDefectN_two]; exact h i

/-- `CentreSectorSeed.sectors_of_defectW`, from `sectors_of_defectWN` at `N = 2`, whose hypothesis
`68 δ ≤ 2` the SU(2) hypothesis `δ ≤ 1/1000` implies. -/
theorem sectors_of_defectW {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) (hd : ZoomSelfScale.defectW 2 β n ≤ δ) (i : Fin 4) :
    fluxShare β n i ≤ 4 * δ ∧ trivialDefect β n i ≤ 2 * δ := by
  have h := CentreSectorSeedN.sectors_of_defectWN (N := 2) hβ hn he hδ0
    (by norm_num; linarith) hd i
  rw [fluxShareN_two, trivialDefectN_two] at h
  exact ⟨h.1.trans (le_of_eq (by push_cast; ring)), h.2⟩

/-- `CentreSectorSeed.seedExistsPow_iff_sectorSeedPow`, from the `N`-form at `N = 2`. -/
theorem seedExistsPow_iff_sectorSeedPow :
    DeltaLengthTower.SeedExistsPow 2 ↔ CentreSectorSeed.SectorSeedPow :=
  CentreSectorSeedN.seedExistsPow_iff_sectorSeedPowN.trans sectorSeedPowN_two_iff

/-- `FluxShareSquaring.fluxShareDoubled_le`, from the `N`-form. -/
theorem fluxShareDoubled_le {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    FluxShareSquaring.fluxShareDoubled β n i
      ≤ (fluxShare β n i / (1 - fluxShare β n i)) ^ 2 * Real.exp (trivialDefect β n i) := by
  rw [← fluxShareDoubledN_two, ← fluxShareN_two, ← trivialDefectN_two]
  exact CentreSectorSeedN.fluxShareDoubled_leN hβ n i

/-- **The SU(2) flux share is the mean deficit over the eight elements of `Z_2³`.** -/
theorem fluxShare_eq_mean {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    fluxShare β n i = 1 - (8 : ℝ)⁻¹ * ∑ g : Cen i 2, twistRatioN 2 β n i g := by
  rw [← fluxShareN_two, CentreSectorSeedN.fluxShareN_eq_mean hβ n i]
  norm_num

end Instances

end MassGap.CentreSectorSeedTwo

end

#print axioms MassGap.CentreSectorSeedTwo.evL_eq_zk
#print axioms MassGap.CentreSectorSeedTwo.centreFlip_eq_act
#print axioms MassGap.CentreSectorSeedTwo.evL_flips_eq_zk
#print axioms MassGap.CentreSectorSeedTwo.trivKN_two
#print axioms MassGap.CentreSectorSeedTwo.fluxShareN_two
#print axioms MassGap.CentreSectorSeedTwo.trivialDefectN_two
#print axioms MassGap.CentreSectorSeedTwo.twistRatioN_single_two
#print axioms MassGap.CentreSectorSeedTwo.sectorSeedPowN_two_iff
#print axioms MassGap.CentreSectorSeedTwo.sectors_of_defectW
#print axioms MassGap.CentreSectorSeedTwo.seedExistsPow_iff_sectorSeedPow
#print axioms MassGap.CentreSectorSeedTwo.fluxShareDoubled_le
#print axioms MassGap.CentreSectorSeedTwo.fluxShare_eq_mean
