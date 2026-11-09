import Mathlib
import MassGap.PhysicalScaleSmall
import MassGap.GapSideVortexRect
import MassGap.RefPassageLow
import MassGap.DiagBoundRunning

/-!
# MassGap.ApertureBridge — the remaining inputs of the pinned path at the plane plaquette, collected

This module collects the remainders of `ExistenceReduce.clay_canonical` (the single-factor `zCan` form; the
pinned target is now the per-field `ExistenceReduceOwn.clay_canonical_own`) at `N = 2`, `O = ExistencePosNonnull.planePlaq 2`,
`(t, ℓ) = (s₀, s₀)`. Its three hypotheses reduce in the tree to:

* `hpos` ⇐ `∃ c > 0, PassageLow.RefPassageLow hN M₀ (planePlaq 2) s₀ s₀ c` (`clay_canonical_planePlaq_low`);
* `hD` ⇐ `DiagBoundRunning.ScaleUpAlong` and `ShortDistanceRunning.PointCubeLocal` at `s₀`
  (`diagBoundSep_of_scaleUp_pointCubeLocal`);
* `hW` ⇐ `WDeltaRun.RunSeed 2`.

## What is proved

* **The `hW` remainder is the Wilson doubling defect at the physical side** (`PhysDefect`,
  `wDelta2_two_of_physDefect`, `physDefect_of_runSeed`, `runSeed_iff_physDefect`). `PhysDefect L δ` is
  `defectW 2 β (2^{kPhys L β + 2}) ≤ δ` eventually in `β`: the side-`2^{kPhys+2}` Wilson torus, of physical side
  in `(L/2, L]`, doubled to side `2^{kPhys+3}`, multiplies `Z` by `Z¹⁶` up to a factor `e^δ`. `RunSeed 2` holds iff
  `PhysDefect L (1/1000)` holds at some `L > 0`. So on the `RunSeed` route no remainder of `hW` is weaker than
  `PhysDefect`.
* **`PhysVortex ∧ PhysRest` is a strengthening of `PhysDefect`, and `PhysRest` follows from a tighter `PhysDefect`**
  (`physDefect_of_physSectorSeed`, `physSectorSeed_of_physDefect`, `physRest_of_physDefect`).
  `PhysSectorSeed L ⇒ PhysDefect L (1/1000)`, and `PhysDefect L (1/320000) ⇒ PhysSectorSeed L ⇒ PhysRest L`
  (`CentreSectorSeedN.sectors_of_defectWN`, `fluxShare ≤ 4δ`, `trivialDefect ≤ 2δ` at `N = 2`). With `PhysRest`
  in hand the closed-sheet bound `PhysVortex` is not needed: the defect alone gives `RunSeed 2`.
* **The flux shares of steps `1–3` are vortex free energies at the physical side** (`PhysVortexRect`,
  `PhysTrivial`, `physRest_of_vortexRect`). `PhysVortex L ε` (`9ε ≤ 1/80000`), the three rectangular sheet free
  energies `vortexR (Lc n 1) 1 2`, `vortexR (Lc n 1) 1 3`, `vortexR (Lc n 2) 2 3` at `n = 2^{kPhys+2}` at most
  `1/720000`, and the four zero-flux doubling defects give `PhysRest L`. The flux content of `PhysRest` is therefore
  closed-sheet free energies on the physical tori of shape `(2n, n, n, n)` and `(2n, 2n, n, n)`; what is not a
  vortex free energy is the zero-flux doubling defect `PhysTrivial`, which is `PhysDefect` within the zero-flux
  sector.
* **The collected inputs** (`Aperture`, `clay_canonical_aperture`). `Aperture hN M₀ s₀ L` is the conjunction
  of the four typed remainders, `RefPassageLow` at some `c > 0`, `ScaleUpAlong`, `PointCubeLocal` and
  `PhysDefect L (1/1000)`. `clay_canonical_aperture`: with `0 < s₀`, `4 s₀ < M₀ · aRun 2 1`, `0 < L`, it gives a
  witness of `hD` and the pinned `ClayContinuumPair` at window `5 · L/2`.

## What `Aperture` is

`Aperture` is defined as the conjunction of the four remainders. It is a restatement of what is left, not a
single bridge. The four clauses read four different quantities: the reference reading against its value on a
fixed torus (volume, `hpos`), the cube reading of the plaquette at a shorter scale against the reference (scale,
`hD`), the point readings of every field against the plaquette cube reading at the same scale (field, `hD`), and
the Wilson partition function under doubling of the physical torus (`hW`). No lemma in the tree derives one clause
from another, and `PassageLow.wTorus_lower_fails` shows that the gap, which `hW` supplies, does not give the
`hpos` clause.

`PointCubeLocal` and the pinned `hD` share the single field-independent factor `zCan`: every field is read against
the plane-plaquette cube reading. At the asymptotically free unit (argued, `DiagBoundGram`) the reading of
`√plaq` grows like `g₀⁻²` against the plaquette's, so `PointCubeLocal` at `L = [√plaq]` fails the same way as
`hD`. The clause that the aperture picture supports is per field: each field read against its own reference
reading. The pinned target at that normalisation is `ExistenceReduceOwn.clay_canonical_own`, and its capstone
from `RefPassageLow`, `ScaleUpOwnAlong ∧ PointCubeOwnAlong` and `PhysDefect` is
`ExistenceReduceOwn.clay_canonical_own_planePlaq`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.ApertureBridge

open Filter MassGap MassGap.PhysicalScaleSmall

/-! ## 1. The `hW` remainder: the Wilson doubling defect at the physical side -/

section Far

/-- **The Wilson doubling defect at the physical side**: eventually in `β`, the side-`2^{kPhys L β + 2}` Wilson
torus (physical side in `(L/2, L]`) has doubling defect `16 log Z(n) − log Z(2n)` at most `δ`.
DERIVED: `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the rank and the doubling. -/
def PhysDefect (L δ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ZoomSelfScale.defectW 2 β (2 ^ (kPhys L β + 2)) ≤ δ

/-- The run-seed body at `C = L` from the physical-side defect. -/
theorem physSeed_of_physDefect {L : ℝ} (hL : 0 < L) (h : PhysDefect L (1 / 1000)) :
    ∀ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ) * AsymptoticScaling.aRun 2 β ≤ L ∧ ZoomSelfScale.defectW 2 β n ≤ 1 / 1000 := by
  filter_upwards [h, eventually_physSide_le hL] with β hD hS
  refine ⟨2 ^ (kPhys L β + 2), ⟨_, rfl⟩, DeltaLengthTower.two_le_two_pow (by omega), ?_, hD⟩
  push_cast
  exact hS

/-- **`RunSeed 2` from the physical-side defect**, with `C = L`. -/
theorem runSeed_of_physDefect {L : ℝ} (hL : 0 < L) (h : PhysDefect L (1 / 1000)) :
    WDeltaRun.RunSeed 2 :=
  ⟨L, hL, physSeed_of_physDefect hL h⟩

/-- **`WDelta2 2` from the physical-side defect**, at every `ℓ₀ ≥ L/2`. -/
theorem wDelta2_two_of_physDefect {L : ℝ} (hL : 0 < L) (h : PhysDefect L (1 / 1000)) :
    ∀ ℓ₀ : ℝ, L ≤ 2 * ℓ₀ → DoublingClay2.WDelta2 2 ℓ₀ :=
  fun _ hℓ => WDeltaRun.wDelta2_of_seed_le (by norm_num) (physSeed_of_physDefect hL h) hℓ

/-- **`RunSeed 2` gives the physical-side defect** at `L = 2C`: the seed side `n ≤ C/a` is a power of two below
`2^{kPhys + 2}`, and `WDeltaRun.defectW_pow_le` carries the seed up to it. -/
theorem physDefect_of_runSeed (h : WDeltaRun.RunSeed 2) : ∃ L : ℝ, 0 < L ∧ PhysDefect L (1 / 1000) := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hev, WeakCouplingWindow.eventually_aRun_le (N := 2) (by norm_num) (b := 2 * C / 4)
    (by positivity), eventually_gt_atTop (0 : ℝ)] with β hβn ha hβ
  obtain ⟨n, ⟨b, hb⟩, hn2, hna, hd⟩ := hβn
  have hsp := (physSide_spec (L := 2 * C) hβ (by linarith)).2
  have hapos : 0 < AsymptoticScaling.aRun 2 β := AsymptoticScaling.aRun_pos (by norm_num) hβ
  have hlt : (n : ℝ) < (2 : ℝ) ^ (kPhys (2 * C) β + 2) := by
    by_contra hc
    have hc' : (2 : ℝ) ^ (kPhys (2 * C) β + 2) ≤ n := le_of_not_gt hc
    have := mul_le_mul_of_nonneg_right hc' hapos.le
    linarith
  have hltN : n < 2 ^ (kPhys (2 * C) β + 2) := by exact_mod_cast hlt
  subst hb
  have hle : b ≤ kPhys (2 * C) β + 2 := by
    by_contra hc
    have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) (le_of_lt (lt_of_not_ge hc))
    exact absurd (lt_of_lt_of_le hltN h2) (lt_irrefl _)
  have he : Even (2 ^ b) := by
    rcases b with _ | b
    · norm_num at hn2
    · exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hp := WDeltaRun.defectW_pow_le (N := 2) (by norm_num) hβ.le hn2 he hd (kPhys (2 * C) β + 2 - b)
  rwa [← pow_add, Nat.sub_add_cancel hle] at hp

/-- **`RunSeed 2` is the physical-side defect at some `L > 0`.** -/
theorem runSeed_iff_physDefect : WDeltaRun.RunSeed 2 ↔ ∃ L : ℝ, 0 < L ∧ PhysDefect L (1 / 1000) :=
  ⟨physDefect_of_runSeed, fun ⟨_, hL, h⟩ => runSeed_of_physDefect hL h⟩

/-- **The sector seed gives the defect** (`PhysicalScaleSmall.defectW_phys_le`). -/
theorem physDefect_of_physSectorSeed {L : ℝ} (h : PhysSectorSeed L) : PhysDefect L (1 / 1000) :=
  defectW_phys_le h

/-- **The defect at `1/320000` gives the sector seed** (`CentreSectorSeedN.sectors_of_defectWN` at `N = 2`:
flux share at most `4δ`, zero-flux defect at most `2δ`). -/
theorem physSectorSeed_of_physDefect {L : ℝ} (h : PhysDefect L (1 / 320000)) : PhysSectorSeed L := by
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with β hd hβ
  intro i
  have hs := CentreSectorSeedN.sectors_of_defectWN (N := 2) hβ
    (DeltaLengthTower.two_le_two_pow (by omega : 1 ≤ kPhys L β + 2))
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) (by norm_num) (by norm_num) hd i
  norm_num at hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- **`PhysRest` from the defect alone.** -/
theorem physRest_of_physDefect {L : ℝ} (h : PhysDefect L (1 / 320000)) : PhysRest L := by
  filter_upwards [physSectorSeed_of_physDefect h] with β hS
  exact ⟨fun i _ => (hS i).1, fun i => (hS i).2⟩

/-- **`PhysVortex ∧ PhysRest` gives the defect**: the vortex clause enters only through `PhysSectorSeed`. -/
theorem physDefect_of_physVortex {L ε : ℝ} (h : PhysVortex L ε) (hε : 0 ≤ ε) (hb : 9 * ε ≤ 1 / 80000)
    (hR : PhysRest L) : PhysDefect L (1 / 1000) :=
  physDefect_of_physSectorSeed (physSectorSeed_of_physVortex h hε hb hR)

end Far

/-! ## 2. The flux shares of steps `1–3` as vortex free energies at the physical side -/

section Rect

open MassGap.GapSideVortexAntiDiagonal

/-- **The rectangular closed-sheet free energies at the physical side**: eventually in `β`, at
`n = 2^{kPhys L β + 2}`, the sheets `(1, 2)`, `(1, 3)` on the step-`1` torus `(2n, n, n, n)` and `(2, 3)` on the
step-`2` torus `(2n, 2n, n, n)` have vortex free energy at most `ε`. DERIVED: `1`, `2`, `3` the sheet
directions, indices in `Fin 4`; `2` the rank and the block factor. -/
def PhysVortexRect (L ε : ℝ) : Prop :=
  ∀ᶠ β in atTop,
    GapSideVortexRect.vortexR (GapSideVortexRect.Lc (2 ^ (kPhys L β + 2)) 1) 1 2 β ≤ ε ∧
      GapSideVortexRect.vortexR (GapSideVortexRect.Lc (2 ^ (kPhys L β + 2)) 1) 1 3 β ≤ ε ∧
      GapSideVortexRect.vortexR (GapSideVortexRect.Lc (2 ^ (kPhys L β + 2)) 2) 2 3 β ≤ ε

/-- **The zero-flux doubling defects at the physical side.** DERIVED: `1/80000` the sector bound of
`PhysicalScaleSmall.PhysRest`, chosen in `CentreSectorSeedN` so that `15 · 5/80000 ≤ 1/1000`. -/
def PhysTrivial (L : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ i : Fin 4, CentreSectorSeedN.trivialDefectN 2 β (2 ^ (kPhys L β + 2)) i ≤ 1 / 80000

/-- **`PhysRest` from vortex free energies and the zero-flux defects**: the cubic closed-sheet bound, the three
rectangular closed-sheet bounds and `PhysTrivial`. -/
theorem physRest_of_vortexRect {L ε ε' : ℝ} (hV : PhysVortex L ε) (hε : 0 ≤ ε) (hb : 9 * ε ≤ 1 / 80000)
    (hR : PhysVortexRect L ε') (hε' : ε' ≤ 1 / 720000) (hT : PhysTrivial L) : PhysRest L := by
  filter_upwards [hV, hR, hT, eventually_ge_atTop (0 : ℝ)] with β hV hR hT hβ
  obtain ⟨r12, r13, r23⟩ := hR
  have hn : 2 ≤ 2 ^ (kPhys L β + 2) := DeltaLengthTower.two_le_two_pow (by omega)
  have he : Even (2 ^ (kPhys L β + 2)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h0 := fluxShareN_zero_le_of_vortex hβ (kPhys L β) hε (fun ν => hV (plane0 ν))
  have s12 := GapSideVortexRect.one_sub_zR_le_vortexR (GapSideVortexRect.Lc (2 ^ (kPhys L β + 2)) 1) 1 2 β
  have s13 := GapSideVortexRect.one_sub_zR_le_vortexR (GapSideVortexRect.Lc (2 ^ (kPhys L β + 2)) 1) 1 3 β
  have s23 := GapSideVortexRect.one_sub_zR_le_vortexR (GapSideVortexRect.Lc (2 ^ (kPhys L β + 2)) 2) 2 3 β
  exact ⟨GapSideVortexRect.fluxShare_steps hβ hn he (by linarith) hT (by linarith) (by linarith)
    (by linarith), hT⟩

end Rect

/-! ## 3. The field clause read against each field's own reading -/

section Own

open MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumCluster
  MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint

variable {N : ℕ}

/-- **Point readings against each field's own cube reading at the same scale.** For every list of fields and
every margin `d < s₀`, the unit-strength reflected point readings of configurations `d` above the plane and
pairwise `d`-separated are at most `C · a_k^{8n}` times the product over the list of each field's own cube-pair
reading at scale `d`. `ShortDistanceRunning.PointCubeLocalAlong` has `refReading(O)ⁿ`, one field for all.
DERIVED: `8 = 2 · 4` the two reflected copies times the plaquette dimension, the spacing power of
`PointCubeLocalAlong`; `0` the plane. -/
def PointCubeOwnAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (s₀ : ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → d < s₀ → ∃ C : ℝ,
    ∀ᶠ k in atTop, ∀ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      latSkRAlong hN βs (rho1Along hN βs) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n) * ∏ i, refReadingAlong hN βs (L i) d d k

/-- **The per-field scale clause**: `ScaleUpAlong` for every field, each against its own reference. -/
def ScaleUpOwnAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (s₀ : ℝ) : Prop :=
  ∀ O : LField (MassGap.SUN.SU N), DiagBoundRunning.ScaleUpAlong hN βs O s₀

/-- **On lists of one field the two forms agree**: the product of a constant list's own readings is the
`n`-th power of that field's reading. So `PointCubeOwnAlong` restricted to `L = fun _ => O` is
`PointCubeLocalAlong` at `O` restricted to the same lists; the two differ only on lists with other fields. -/
theorem prod_own_const (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (n : ℕ) (d : ℝ) (k : ℕ) :
    ∏ _i : Fin n, refReadingAlong hN βs O d d k = refReadingAlong hN βs O d d k ^ n := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Own

/-! ## 4. The collected inputs and the pinned path -/

section Pinned

open MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **The four remainders of the pinned path at the plane plaquette, collected.** The volume clause
(`RefPassageLow` at some `c > 0`), the scale clause (`ScaleUpAlong`), the field clause (`PointCubeLocal`) and the
physical-side defect. This is the conjunction of the remaining inputs, not a single bridge.
DERIVED: `2` the rank. Inherited: `1/1000` the seed of `WDeltaRun.RunSeed` (`runSeed_iff_physDefect`). -/
def Aperture (hN : (2 : ℕ) ≠ 0) (M₀ : ℕ) (s₀ L : ℝ) : Prop :=
  (∃ c : ℝ, 0 < c ∧ PassageLow.RefPassageLow hN M₀ (ExistencePosNonnull.planePlaq 2) s₀ s₀ c) ∧
    DiagBoundRunning.ScaleUpAlong hN (dyBeta (one_le_of_ne_zero hN)) (ExistencePosNonnull.planePlaq 2) s₀ ∧
    ShortDistanceRunning.PointCubeLocal hN (ExistencePosNonnull.planePlaq 2) s₀ ∧
    PhysDefect L (1 / 1000)

/-- **The pinned path from the collected inputs.** -/
theorem clay_canonical_aperture (hN : (2 : ℕ) ≠ 0) {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (hM : 2 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L) (A : Aperture hN M₀ s₀ L) :
    ∃ hD : ContinuumSep.DiagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq 2) s₀ s₀)) 0,
      ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧
        ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq 2) s₀ s₀) 0
          (ExistenceReduce.zCan_refl hN (ExistencePosNonnull.planePlaq 2) s₀ s₀)
          (ContinuumSep.pairBoundSep_of_diagBoundSep hN
            (Renorm.connected hN (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq 2) s₀ s₀)) 0
            (Renorm.connected_reflCompat hN
              (ExistenceReduce.zCan hN (ExistencePosNonnull.planePlaq 2) s₀ s₀) 0
              (ExistenceReduce.zCan_refl hN (ExistencePosNonnull.planePlaq 2) s₀ s₀)) hD) (5 * ℓ₀) := by
  obtain ⟨hP, hU, hC, hW⟩ := A
  have hD := DiagBoundRunning.diagBoundSep_of_scaleUp_pointCubeLocal hN _ hs₀ hU hC
  exact ⟨hD, L / 2, by positivity, PassageLow.clay_canonical_planePlaq_low le_rfl hN hs₀ hs₀ hM hP hD
    (by positivity) (wDelta2_two_of_physDefect hL hW (L / 2) (by linarith))⟩

end Pinned

end MassGap.ApertureBridge

end

#print axioms MassGap.ApertureBridge.physSeed_of_physDefect
#print axioms MassGap.ApertureBridge.runSeed_of_physDefect
#print axioms MassGap.ApertureBridge.wDelta2_two_of_physDefect
#print axioms MassGap.ApertureBridge.physDefect_of_runSeed
#print axioms MassGap.ApertureBridge.runSeed_iff_physDefect
#print axioms MassGap.ApertureBridge.physDefect_of_physSectorSeed
#print axioms MassGap.ApertureBridge.physSectorSeed_of_physDefect
#print axioms MassGap.ApertureBridge.physRest_of_physDefect
#print axioms MassGap.ApertureBridge.physDefect_of_physVortex
#print axioms MassGap.ApertureBridge.physRest_of_vortexRect
#print axioms MassGap.ApertureBridge.prod_own_const
#print axioms MassGap.ApertureBridge.clay_canonical_aperture
