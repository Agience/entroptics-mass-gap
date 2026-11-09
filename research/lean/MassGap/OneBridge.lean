import Mathlib
import MassGap.PreObserver
import MassGap.SlabMeasure
import MassGap.UniformAperture

/-!
# MassGap.OneBridge — the SU(N) capstone with its gap input as one named bridge on the Wilson box

`PreObserver.clayStatementAt_SU_noNT` reads its gap through `hfar : WDeltaRun.RunSeed N`, used only
through `SUInputs.gapEx'`: a rate `ρ ∈ (0, 1)` with `GapAt (transferN hN Φ hB 0 hphys 0) ρ`,
`Φ = energy0 W (SymPlaqClass N) (symPlaq_refl N)`, `hB = PreObserver.preB hN W hU`. This module
replaces that input by one hypothesis `OneBridge hN W hU hphys`, stated on the Wilson box of
`SlabMeasure`. Declarations live in the namespace `MassGap.OneBridgeSU`.

## 1. The observer's transfer reading (`optRate`, `gFlow`, `gObs`)

* `optRate D = sInf {ρ ≥ 0 | GapAt D ρ}`. `gapAt_optRate`: the infimum is a rate (`GapAt` is a closed
  condition in `ρ`; the set contains `1`, `TransferGap.gapAt_of_one_le_sq`). `optRate_le`,
  `optRate_nonneg`, `optRate_le_one`.
* `gFlow hN Φ hB τ hphys m = −log (optRate (transferN … m)) / dySpacing N m`: the gap of the flowed
  transfer at the dyadic step `m`, per unit of the step length. `gObs` is `gFlow` at the capstone's
  `Φ`, `hB`, the plane `0`. `gFlow_nonneg`.
* The index of `gFlow` is the time step of the continuum transfer `transferN … m` (built from the
  continuum kernel `kernF`), not a lattice spacing: the lattice limit is already taken inside `kernF`.
* `rate_of_gFlow_pos`: `0 < gFlow … m` gives `0 < optRate < 1` at step `m`, hence `GapAt` there.
  `gapAt_step`: a gap at one step is a gap at every step (`ObserverGapScale.flowClusterAbs_iff_gapAt`
  twice). `gapAt_of_noFade`: `NoFadeAtFineEnd (gFlow …) rLat` gives the gap at any step `m₀`, for every
  `rLat` (no sign condition: `gFlow ≥ 0`, so a positive ratio forces `gFlow > 0`).
  `gapAt_of_ratioInvariant`: `RatioInvariant (gFlow …) rLat q C` with `q > 0` gives it too.
* `gapAt_iff_rateFloor`: a gap at step `m₀` is equivalent to one `c > 0` with
  `optRate (transferN … m) ≤ e^{−c a_m}` at every step `m`. So on the observer's own transfer family
  `RatioInvariant` (a floor at every step) is read only at one step, and the gap at one step gives
  back a floor at every step in rate form.

This is the link asked for between `ApertureInvariance.RatioInvariant` and the capstone's input, at
`gLat := gObs` (the observer's transfer gap). It closes formally because `gObs` is defined from the
same `transferN` family; it carries no information about the Wilson measure. The tie to the measure is
in the volume link of Section 3.

## 2. Cells on `L²(π)` (`CellGramH`, `EdgeCellsM`)

`UniformAperture` states the cell coupling on a finite state space (`Slab`). The Wilson Doob slabs
are `SlabMeasure.SlabM` on `L²(π)`. Here the same Schur test runs on any real inner product space.

* `CellGramH P e ρc c`: every `g ⊥ e` is a sum of pairwise orthogonal pieces `vᵢ` with
  `‖P vᵢ‖² ≤ ρc² ‖vᵢ‖²` and `⟪P vᵢ, P vⱼ⟫² ≤ cᵢⱼ² ‖vᵢ‖² ‖vⱼ‖²`. `contrH_of_cellGramH`: with
  `RowSum c η`, `ContrH P e √(ρc² + η)`.
* `EdgeCellsM S ρc Ke A p q`: `CellGramH` on the slab `S` with `ShellCount` and `FaceEdgeCost` at `q`.
  `contrM_of_edgeCellsM`. `relFloorM_of_edgeCost`: edge cells at `q = edgeRate (σ m k) h ℓ` with a
  tension floor `σ m k ≥ σ₀ > h` and `ρc² + Ke A edgeSum p (edgeRate σ₀ h ℓ) < 1` give `RelFloorM` with
  a rate and a zoom independent of the aperture. As in `UniformAperture`, `EdgeCellsM` records no cell
  size or locality (one cell with `A = 0` is a slab rate `ContrM ρc`).

## 3. The bridge (`WilsonBox`, `OneBridgeData`, `OneBridge`)

`WilsonBox N`: a direction `μ`, transverse extents `T m k`, couplings `β m k ≥ 0`, a unit `a₀ > 0`.
At aperture `m` and zoom `k` the slab is the Doob slab of `2ᵏ` steps of the Wilson slice transfer
`perronKT μ (T m k) N hN (β m k)` (physical thickness `2ᵏ · a₀/2ᵏ = a₀`, the same at every `m`, `k`),
and the box gap is `gL m k = −log ratio / a_k` (`readsSlab`: it reads the slab, from
`SlabMeasure.readsSlabM_transfer`).

`OneBridgeData hN W hU hphys` collects:

* `box`, and the finite-volume input `ratio_pos`: every one-step Wilson rate `ratio` is positive.
* the observer's reading `rLat` in `(0, R]` (`hR`, `hr`); it is free and enters only as a unit.
* (A) `relFloor`: `RelFloorM` on the Wilson Doob slabs, rates `ρ m < 1` from zooms `K m` on. Its
  clause `ρ m < 1` is the finite-volume gap of the slab, including simplicity of the top eigenvalue in
  the form the chain reads (contraction on `1⊥`).
* (B) `uniform`: eventually in `m`, `ρ m ≤ ρ₀ < 1` and `K m ≤ K₀`. `ab_of_edgeCost` builds (A) and (B)
  from the cell coupling `EdgeCellsM` at a fixed `σ₀ > h` (Section 2).
* `volumeLink`: `FixedAperture.VolumeLink box.gL (gObs hN W hU hphys) rLat`. At every index `k`, a
  floor on the Wilson box gaps at spacing `a_k`, eventually in the aperture, is a floor on the
  observer's transfer gap at step `k`. This field is the only declaration tying the Wilson box to the
  flow `W` of the capstone; no theorem here or elsewhere proves it.

`OneBridge = Nonempty OneBridgeData`. `noFade_of_oneBridgeData`: (A), (B), the reading and the volume
link give `NoFadeAtFineEnd (gObs …) rLat` (`SlabMeasure.fixedApertureFloor_of_relFloorM`,
`RelativeGap.uniformInAperture_of_relFloor`, `FixedAperture.noFade_of_split`).
`gap_of_oneBridge`: the capstone's gap input. `oneBridge_of_edgeCost`: the bridge with (A) and (B)
from the cells.

## 4. The capstone

* `obsXNg` — `PreObserver.obsXN` with the gap `(ρ, hρ0, hρ1, hg)` as an input in place of `gapEx'`.
  `obsXNg_gap`, `obsXNg_SM`; `LinkC` at `obsXNg` is `LinkCPre` at the pre-observer and its `cvec` is
  `preCvec`, by definition.
* `clayStatementAt_SU_at_gap` — `PreObserver.clayStatementAt_SU_at` at `obsXNg`.
* `clayStatementAt_SU_noNT_gap` — `PreObserver.clayStatementAt_SU_noNT` with `hfar` replaced by a
  gap at step `0`.
* `clayStatementAt_SU_oneBridge` — `PreObserver.clayStatementAt_SU_noNT` with `hfar` replaced by
  `OneBridge hN W hU hphys`. The inputs `wC`, `hLC`, `hX` are stated at the pre-observer, which reads
  no gap, so their types do not mention the bridge.

Nothing here proves any field of `OneBridgeData` for the Wilson measure, or ties `W` to the Wilson box
other than through `volumeLink`. All four of `ratio_pos`, `relFloor`, `uniform`, `volumeLink` are open.

## 5. Strength of the bridge

`OneBridge` implies the step-0 gap (`gap_of_oneBridge`). It is not weaker than the gap: the box is free
— `T m k`, `β m k`, `a₀` are tied to no side `m·a₀`, no running coupling of `W`, no unit of the
observer, so the aperture index `m` is nominal and "volume link" names no infinite-volume limit.
Taking `T m k = T₀`, `β m k = β_k` with `ratio_k^{2^k}` fixed, (A) and (B) hold trivially and
`volumeLink` is a uniform floor on `gObs`, i.e. the right side of `gapAt_iff_rateFloor`; so, given a
lemma that the Wilson slab `ratio` takes every value in `(0,1)` as `β` varies (not in the tree),
`OneBridge` is equivalent to the gap. `volumeLink` alone is satisfied by any box with
`liminf_m gL m k = 0`; with (A), (B) and `ratio_pos` it forces `gObs > 0`. The slab thickness here is
`a₀` at every aperture (needed for `uniformInAperture_of_relFloor`'s `τ m ≤ T`), not
`SlabMeasure.readsSlabM_box`'s `LA a₀ m`. (A)'s uniformity over zooms `k ≥ K m` at fixed thickness is a
fine-spacing statement, not a finite-volume one. The `σ` of `relFloorM_of_edgeCost` is a parameter,
not the Wilson string tension. The bridge collects the open gap-side inputs in the owner's terms; the
content is the gap.

DERIVED (module-wide): `0` the plane, the step of the capstone's gap and the sign of every rate; `1`
the rate at which `GapAt` is automatic, the window `L` of `flowClusterAbs_iff_gapAt`, the least number
of steps; `2` the block factor of one zoom step (`2ᵏ` steps of length `a₀/2ᵏ`) and the `L²` exponent;
`2`, `8`, `4`, `16` as in `PreObserver`.
-/

noncomputable section

namespace MassGap.OneBridgeSU

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
  MassGap.PreObserver
open MassGap.SlabMeasure MassGap.FixedAperture MassGap.NoTransition MassGap.ApertureInvariance
  MassGap.SlabKernelOperator
open scoped Topology Matrix

/-! ## 1. The observer's transfer reading -/

section Rate

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The rates of `D`: `ρ ≥ 0` with `GapAt D ρ`. DERIVED: `0` the sign of a rate. -/
def rateSet (D : Transfer.TransferData A) : Set ℝ := {ρ | 0 ≤ ρ ∧ TransferGap.GapAt D ρ}

/-- **The least rate of `D`.** -/
def optRate (D : Transfer.TransferData A) : ℝ := sInf (rateSet D)

/-- `1` is a rate. DERIVED: `1` the rate at which `GapAt` is automatic. -/
theorem one_mem_rateSet (D : Transfer.TransferData A) : (1 : ℝ) ∈ rateSet D :=
  ⟨zero_le_one, TransferGap.gapAt_of_one_le_sq D (by norm_num)⟩

theorem rateSet_bdd (D : Transfer.TransferData A) : BddBelow (rateSet D) := ⟨0, fun _ h => h.1⟩

theorem optRate_nonneg (D : Transfer.TransferData A) : 0 ≤ optRate D :=
  le_csInf ⟨1, one_mem_rateSet D⟩ fun _ h => h.1

theorem optRate_le_one (D : Transfer.TransferData A) : optRate D ≤ 1 :=
  csInf_le (rateSet_bdd D) (one_mem_rateSet D)

theorem optRate_le (D : Transfer.TransferData A) {ρ : ℝ} (h0 : 0 ≤ ρ) (h : TransferGap.GapAt D ρ) :
    optRate D ≤ ρ :=
  csInf_le (rateSet_bdd D) ⟨h0, h⟩

/-- **The least rate is a rate.** -/
theorem gapAt_optRate (D : Transfer.TransferData A) : TransferGap.GapAt D (optRate D) := by
  intro x hx
  rcases (D.form_nonneg x).lt_or_eq with hp | hz
  · have key : Real.sqrt (D.form (D.T x) (D.T x) / D.form x x) ≤ optRate D := by
      refine le_csInf ⟨1, one_mem_rateSet D⟩ fun ρ hρ => ?_
      rw [Real.sqrt_le_left hρ.1, div_le_iff₀ hp]
      exact hρ.2 x hx
    have h2 := (Real.sqrt_le_left (optRate_nonneg D)).1 key
    rwa [div_le_iff₀ hp] at h2
  · have h := (one_mem_rateSet D).2 x hx
    rw [← hz] at h ⊢
    simpa using h

end Rate

section Flow

variable {N : ℕ}

/-- **The gap of the flowed transfer at step `m`**, per unit of the step length:
`−log (optRate (transferN … m)) / dySpacing N m`. -/
def gFlow (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hphys : Φ.PhysRange r) (m : ℕ) : ℝ :=
  -Real.log (optRate (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m)) / dySpacing N m

theorem gFlow_nonneg (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hphys : Φ.PhysRange r) (m : ℕ) : 0 ≤ gFlow hN Φ hB τ hphys m :=
  div_nonneg (neg_nonneg.2 (Real.log_nonpos (optRate_nonneg _) (optRate_le_one _)))
    (dySpacing_pos (one_le_of_ne_zero hN) m).le

/-- **A positive reading is a rate in `(0, 1)`** at that step. -/
theorem rate_of_gFlow_pos (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hphys : Φ.PhysRange r) {m : ℕ} (h : 0 < gFlow hN Φ hB τ hphys m) :
    0 < optRate (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m)
      ∧ optRate (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m) < 1 := by
  have hl : Real.log (optRate (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m)) < 0 := by
    have := (div_pos_iff_of_pos_right (dySpacing_pos (one_le_of_ne_zero hN) m)).1 h
    linarith
  have hpos : 0 < optRate (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m) := by
    rcases (optRate_nonneg (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m)).lt_or_eq
      with h0 | h0
    · exact h0
    · rw [← h0, Real.log_zero] at hl
      exact absurd hl (lt_irrefl 0)
  exact ⟨hpos, (Real.log_neg_iff hpos).1 hl⟩

/-- **A gap at one step is a gap at every step.** DERIVED: `1` the window `L`. -/
theorem gapAt_step (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hphys : Φ.PhysRange r) {m : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m) ρ) (m0 : ℕ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ' :=
  (ObserverGapScale.flowClusterAbs_iff_gapAt hN Φ hB τ
    (Flow.posPreserving_of_physRange hN Φ hphys τ) m0 one_pos).1
    ((ObserverGapScale.flowClusterAbs_iff_gapAt hN Φ hB τ
      (Flow.posPreserving_of_physRange hN Φ hphys τ) m one_pos).2 ⟨ρ, hρ0, hρ1, hg⟩)

/-- **A positive reading at one step is a gap at every step.** -/
theorem gapAt_of_gFlow_pos (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hphys : Φ.PhysRange r) {m : ℕ} (h : 0 < gFlow hN Φ hB τ hphys m) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ := by
  obtain ⟨h0, h1⟩ := rate_of_gFlow_pos hN Φ hB τ hphys h
  exact gapAt_step hN Φ hB τ hphys h0 h1 (gapAt_optRate _) m0

/-- **`NoFadeAtFineEnd` on the transfer reading gives the gap at every step**, for every `rLat`. -/
theorem gapAt_of_noFade (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hphys : Φ.PhysRange r) {rLat : ℕ → ℝ} (h : NoFadeAtFineEnd (gFlow hN Φ hB τ hphys) rLat)
    (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ := by
  obtain ⟨c, hc, hev⟩ := h
  obtain ⟨k, hk⟩ := hev.exists
  have hratio : 0 < gFlow hN Φ hB τ hphys k / rLat k := hc.trans_le hk
  have hg : 0 < gFlow hN Φ hB τ hphys k := by
    rcases (gFlow_nonneg hN Φ hB τ hphys k).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, zero_div] at hratio
      exact absurd hratio (lt_irrefl 0)
  exact gapAt_of_gFlow_pos hN Φ hB τ hphys hg m0

/-- **`RatioInvariant` on the transfer reading gives the gap at every step.** -/
theorem gapAt_of_ratioInvariant (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hphys : Φ.PhysRange r) {rLat : ℕ → ℝ} {q C : ℝ} (hq : 0 < q)
    (h : RatioInvariant (gFlow hN Φ hB τ hphys) rLat q C) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ := by
  obtain ⟨c, hc, hk⟩ := (ratioInvariant_iff_floor _ rLat).1 ⟨q, C, hq, h⟩
  exact gapAt_of_noFade hN Φ hB τ hphys ⟨c, hc, Eventually.of_forall hk⟩ m0

/-- **The gap at one step is a rate floor at every step**: `GapAt` at step `m₀` with `ρ ∈ (0, 1)` is
equivalent to one `c > 0` with `optRate (transferN … m) ≤ e^{−c a_m}` at every step `m`.

DERIVED: `1` the window `L`. -/
theorem gapAt_iff_rateFloor (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) :
    (∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ)
      ↔ ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ,
        optRate (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m)
          ≤ Real.exp (-c * dySpacing N m) := by
  constructor
  · rintro ⟨ρ, hρ0, hρ1, hg⟩
    have hcl := (ObserverGapScale.flowClusterAbs_iff_gapAt hN Φ hB τ
      (Flow.posPreserving_of_physRange hN Φ hphys τ) m0 one_pos).2 ⟨ρ, hρ0, hρ1, hg⟩
    obtain ⟨c, hc, hga⟩ := FlowCapstone.flow_gap_of_abs_cluster hN Φ hB τ
      (Flow.posPreserving_of_physRange hN Φ hphys τ) hcl
    exact ⟨c / 1, div_pos hc one_pos, fun m => optRate_le _ (Real.exp_pos _).le (hga m)⟩
  · rintro ⟨c, hc, hk⟩
    have hlt : Real.exp (-c * dySpacing N m0) < 1 := by
      rw [Real.exp_lt_one_iff, neg_mul]
      exact neg_lt_zero.mpr (mul_pos hc (dySpacing_pos (one_le_of_ne_zero hN) m0))
    refine ⟨Real.exp (-c * dySpacing N m0), Real.exp_pos _, hlt, ?_⟩
    exact TransferGap.gapAt_mono (pow_le_pow_left₀ (optRate_nonneg _) (hk m0) 2) (gapAt_optRate _)

end Flow

/-- **The capstone observer's transfer reading**: `gFlow` at
`Φ = energy0 W (SymPlaqClass N) (symPlaq_refl N)`, `hB = preB hN W hU`, the plane `0`.

DERIVED: `0` the plane. -/
def gObs {N : ℕ} (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) : ℕ → ℝ :=
  gFlow hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys

/-! ## 2. Cells on `L²(π)` -/

section Cells

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- **Cells with a Gram bound on `e⊥`.** -/
def CellGramH (P : E →L[ℝ] E) (e : E) (ρc : ℝ) (c : Fin n → Fin n → ℝ) : Prop :=
  ∀ g : E, inner ℝ g e = 0 → ∃ v : Fin n → E, g = ∑ i, v i ∧
    (∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) ∧
    (∀ i, ‖P (v i)‖ ^ 2 ≤ ρc ^ 2 * ‖v i‖ ^ 2) ∧
    (∀ i j, i ≠ j → inner ℝ (P (v i)) (P (v j)) ^ 2 ≤ c i j ^ 2 * ‖v i‖ ^ 2 * ‖v j‖ ^ 2)

theorem norm_sq_sum_eq (v : Fin n → E) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ∑ j, inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  exact Finset.sum_congr rfl fun i _ => inner_sum _ _ _

/-- Pairwise orthogonal pieces add their squared norms. -/
theorem norm_sq_sum_orth (v : Fin n → E) (h : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [norm_sq_sum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => h i j (Ne.symm hj))
    (fun hi => absurd (Finset.mem_univ i) hi), real_inner_self_eq_norm_sq]

/-- **The Schur test on the Gram matrix** in an inner product space. -/
theorem norm_sq_sum_le_gram (w u : Fin n → E) {D η : ℝ} (c : Fin n → Fin n → ℝ)
    (hc0 : ∀ i j, 0 ≤ c i j) (hsymm : ∀ i j, c i j = c j i)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ η)
    (hdiag : ∀ i, ‖w i‖ ^ 2 ≤ D * ‖u i‖ ^ 2)
    (hoff : ∀ i j, i ≠ j → inner ℝ (w i) (w j) ^ 2 ≤ c i j ^ 2 * ‖u i‖ ^ 2 * ‖u j‖ ^ 2) :
    ‖∑ i, w i‖ ^ 2 ≤ (D + η) * ∑ i, ‖u i‖ ^ 2 := by
  rw [norm_sq_sum_eq]
  have hi : ∀ i, ∑ j, inner ℝ (w i) (w j) ≤ D * ‖u i‖ ^ 2
      + ∑ j ∈ Finset.univ.erase i, c i j * (‖u i‖ ^ 2 + ‖u j‖ ^ 2) / 2 := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ (fun j => inner ℝ (w i) (w j)) (Finset.mem_univ i)]
    refine add_le_add ?_ (Finset.sum_le_sum fun j hj => ?_)
    · exact (real_inner_self_eq_norm_sq (w i)).le.trans (hdiag i)
    · exact UniformAperture.ip_le_of_sq (hc0 i j) (sq_nonneg _) (sq_nonneg _)
        (hoff i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  have hoffsum := UniformAperture.offdiag_sum_le (fun i => sq_nonneg ‖u i‖) c hsymm hrow
  calc ∑ i, ∑ j, inner ℝ (w i) (w j)
      ≤ ∑ i, (D * ‖u i‖ ^ 2
          + ∑ j ∈ Finset.univ.erase i, c i j * (‖u i‖ ^ 2 + ‖u j‖ ^ 2) / 2) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = D * ∑ i, ‖u i‖ ^ 2
          + ∑ i, ∑ j ∈ Finset.univ.erase i, c i j * (‖u i‖ ^ 2 + ‖u j‖ ^ 2) / 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ D * ∑ i, ‖u i‖ ^ 2 + η * ∑ i, ‖u i‖ ^ 2 := add_le_add le_rfl hoffsum
    _ = (D + η) * ∑ i, ‖u i‖ ^ 2 := by ring

/-- **The rate from the cell rate and the coupling**: `ContrH P e √(ρc² + η)`. -/
theorem contrH_of_cellGramH {P : E →L[ℝ] E} {e : E} {ρc η : ℝ} {c : Fin n → Fin n → ℝ}
    (hG : CellGramH P e ρc c) (hR : UniformAperture.RowSum c η) (hρη : 0 ≤ ρc ^ 2 + η) :
    ContrH P e (Real.sqrt (ρc ^ 2 + η)) := by
  obtain ⟨hc0, hsymm, hrow⟩ := hR
  refine ⟨Real.sqrt_nonneg _, fun g hg => ?_⟩
  obtain ⟨v, rfl, horth, hdiag, hoff⟩ := hG g hg
  have h1 : ‖P (∑ i, v i)‖ ^ 2 ≤ (ρc ^ 2 + η) * ‖∑ i, v i‖ ^ 2 := by
    rw [map_sum, norm_sq_sum_orth v horth]
    exact norm_sq_sum_le_gram (fun i => P (v i)) v c hc0 hsymm hrow hdiag hoff
  have h2 : ‖P (∑ i, v i)‖ ^ 2 ≤ (Real.sqrt (ρc ^ 2 + η) * ‖∑ i, v i‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hρη]
    exact h1
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h2

end Cells

/-- **The edge cells of a slab on `L²(π)`**: `CellGramH` on the mean-zero functions with a symmetric
coupling `c ≥ 0`, `ShellCount d A p` and `FaceEdgeCost c d Ke q`. -/
def EdgeCellsM (S : SlabM) (ρc Ke A : ℝ) (p : ℕ) (q : ℝ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → Fin n → ℝ) (d : Fin n → Fin n → ℕ), (∀ i j, 0 ≤ c i j) ∧
    (∀ i j, c i j = c j i) ∧ UniformAperture.ShellCount d A p ∧
    UniformAperture.FaceEdgeCost c d Ke q ∧ CellGramH S.P (oneLp S.π) ρc c

/-- **Edge cells give the slab rate** `cellRate ρc (Ke A edgeSum p q)`. -/
theorem contrM_of_edgeCellsM {S : SlabM} {ρc Ke A q : ℝ} {p : ℕ} (hKe : 0 ≤ Ke) (hA : 0 ≤ A)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (h : EdgeCellsM S ρc Ke A p q) :
    S.ContrM (UniformAperture.cellRate ρc (Ke * A * UniformAperture.edgeSum p q)) := by
  obtain ⟨n, c, d, hc0, hsymm, hd, hE, hG⟩ := h
  have hη : 0 ≤ Ke * A * UniformAperture.edgeSum p q :=
    mul_nonneg (mul_nonneg hKe hA) (UniformAperture.edgeSum_nonneg p hq0)
  exact (S.contrM_iff _).2 (contrH_of_cellGramH hG
    ⟨hc0, hsymm, fun i => UniformAperture.rowSum_le_of_edgeCost hKe hA hq0 hq1 hd hE i⟩
    (add_nonneg (sq_nonneg _) hη))

/-- **(A) with an aperture-independent rate from the edge cost, on `L²(π)`.** At every aperture
`m > 0` and zoom `k ≥ K₀`, edge cells at `q = edgeRate (σ m k) h ℓ`, a tension floor
`σ m k ≥ σ₀ > h`, and `ρc² + Ke A edgeSum p (edgeRate σ₀ h ℓ) < 1` give `RelFloorM` with the
constant rate `cellRate ρc (Ke A edgeSum p (edgeRate σ₀ h ℓ))` and the constant zoom `K₀`. -/
theorem relFloorM_of_edgeCost {S : ℕ → ℕ → SlabM} {σ : ℕ → ℕ → ℝ} {ρc Ke A σ₀ h ℓ : ℝ}
    {p K₀ : ℕ} (hρc : 0 < ρc) (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hℓ : 0 < ℓ) (hσ₀ : h < σ₀)
    (hσ : ∀ m, 0 < m → ∀ k, K₀ ≤ k → σ₀ ≤ σ m k)
    (h1 : ρc ^ 2 + Ke * A * UniformAperture.edgeSum p (NonAbelianForget.edgeRate σ₀ h ℓ) < 1)
    (hS : ∀ m, 0 < m → ∀ k, K₀ ≤ k →
      EdgeCellsM (S m k) ρc Ke A p (NonAbelianForget.edgeRate (σ m k) h ℓ)) :
    RelFloorM S (fun _ => UniformAperture.cellRate ρc
        (Ke * A * UniformAperture.edgeSum p (NonAbelianForget.edgeRate σ₀ h ℓ))) (fun _ => K₀) := by
  have hq0 := NonAbelianForget.edgeRate_nonneg σ₀ h ℓ
  have hq1 := NonAbelianForget.edgeRate_lt_one hσ₀ hℓ
  have hη : 0 ≤ Ke * A * UniformAperture.edgeSum p (NonAbelianForget.edgeRate σ₀ h ℓ) :=
    mul_nonneg (mul_nonneg hKe hA) (UniformAperture.edgeSum_nonneg p hq0)
  intro m hm
  refine ⟨UniformAperture.cellRate_pos hρc hη, UniformAperture.cellRate_lt_one hη h1,
    fun k hk => ?_⟩
  obtain ⟨n, c, d, hc0, hsymm, hd, hE, hG⟩ := hS m hm k hk
  exact (S m k).rho_le (contrM_of_edgeCellsM hKe hA hq0 hq1 ⟨n, c, d, hc0, hsymm, hd,
    UniformAperture.faceEdgeCost_mono hKe (NonAbelianForget.edgeRate_nonneg _ _ _)
      (EdgeCost.edgeRate_le_of_sigma_ge (hσ m hm k hk) hℓ.le) hE, hG⟩)

/-! ## 3. The bridge -/

/-- **The Wilson box**: a direction, transverse extents, couplings `≥ 0` at every aperture and zoom,
and a unit length `a₀ > 0`. -/
structure WilsonBox (N : ℕ) where
  μ : Fin 4
  T : ℕ → ℕ → {j : Fin 4 // j ≠ μ} → ℕ
  β : ℕ → ℕ → ℝ
  hβ : ∀ m k, 0 ≤ β m k
  a₀ : ℝ
  ha₀ : 0 < a₀

namespace WilsonBox

variable {N : ℕ} (B : WilsonBox N) (hN : N ≠ 0)

/-- The Perron kernel of the Wilson slice transfer at aperture `m`, zoom `k`. -/
def kern (m k : ℕ) : PerronKernel := perronKT B.μ (B.T m k) N hN (B.β m k) (B.hβ m k)

/-- The Doob slab of `2ᵏ` steps (physical thickness `a₀`). DERIVED: `2` the block factor. -/
def slab (m k : ℕ) : SlabM := (B.kern hN m k).slab (2 ^ k)

/-- The box gap `−log ratio / a_k`. -/
def gL (m k : ℕ) : ℝ := (B.kern hN m k).boxGap (aZ B.a₀ k)

/-- **The box gap reads the slab of thickness `a₀`**, when every one-step rate is positive.

DERIVED: `2` the block factor; `1` the least number of steps. -/
theorem readsSlab (hpos : ∀ m k, 0 < m → 0 < (B.kern hN m k).ratio) :
    ReadsSlabM (B.gL hN) (B.slab hN) (fun _ => B.a₀) :=
  readsSlabM_transfer (B.kern hN) B.ha₀ (fun _ k => 2 ^ k) (fun _ => B.a₀)
    (fun _ _ _ => Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ two_ne_zero))
    (fun _ _ _ => by
      simp only [aZ]
      push_cast
      field_simp)
    hpos

end WilsonBox

variable {N : ℕ}

/-- **The one bridge, as data.** The Wilson box, its finite-volume input `ratio_pos`, the observer's
reading `rLat ∈ (0, R]`, (A) `relFloor`, (B) `uniform`, and the volume link from the Wilson box gaps
to the capstone observer's transfer reading `gObs`.

DERIVED: `0` the sign of every rate. -/
structure OneBridgeData (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) where
  /-- The Wilson box. -/
  box : WilsonBox N
  /-- Finite volume: every one-step Wilson rate is positive. -/
  ratio_pos : ∀ m k, 0 < m → 0 < (box.kern hN m k).ratio
  /-- The observer's reading. -/
  rLat : ℕ → ℝ
  /-- Its upper bound. -/
  R : ℝ
  hR : 0 < R
  hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R
  /-- The slab rates of (A). -/
  ρ : ℕ → ℝ
  /-- The zooms of (A). -/
  K : ℕ → ℕ
  /-- (A): the relative floor at fixed physical aperture on the Wilson Doob slabs. -/
  relFloor : RelFloorM (box.slab hN) ρ K
  /-- (B): the rate bound. -/
  ρ₀ : ℝ
  ρ₀_lt_one : ρ₀ < 1
  /-- (B): the zoom bound. -/
  K₀ : ℕ
  /-- (B): uniformity in the aperture. -/
  uniform : ∀ᶠ m in atTop, ρ m ≤ ρ₀ ∧ K m ≤ K₀
  /-- The volume link from the Wilson box gaps to the observer's transfer reading. -/
  volumeLink : VolumeLink (box.gL hN) (gObs hN W hU hphys) rLat

/-- **The one bridge**: some `OneBridgeData`. -/
def OneBridge (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) : Prop :=
  Nonempty (OneBridgeData hN W hU hphys)

/-- **The bridge gives `NoFadeAtFineEnd` on the observer's transfer reading.**

DERIVED: `0` the least aperture. -/
theorem noFade_of_oneBridgeData {hN : N ≠ 0} {W : ConfFlow N} {t C : ℝ}
    {hU : ClassMoments hN W (SymPlaqClass N) t C} {r : ℝ}
    {hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r}
    (D : OneBridgeData hN W hU hphys) : NoFadeAtFineEnd (gObs hN W hU hphys) D.rLat := by
  have hρ₀ : 0 < D.ρ₀ := by
    obtain ⟨m, hm, hm0⟩ := (D.uniform.and (eventually_gt_atTop 0)).exists
    exact (D.relFloor m hm0).1.trans_le hm.1
  have hev : ∀ᶠ m in atTop, 0 < D.ρ m ∧ D.ρ m ≤ D.ρ₀ ∧ 0 < (fun _ : ℕ => D.box.a₀) m ∧
      (fun _ : ℕ => D.box.a₀) m ≤ D.box.a₀ ∧ D.K m ≤ D.K₀ := by
    filter_upwards [D.uniform, eventually_gt_atTop 0] with m hm hm0
    exact ⟨(D.relFloor m hm0).1, hm.1, D.box.ha₀, le_rfl, hm.2⟩
  exact noFade_of_split
    (fixedApertureFloor_of_relFloorM (D.box.readsSlab hN D.ratio_pos) D.relFloor D.hR D.hr)
    (RelativeGap.uniformInAperture_of_relFloor (τ := fun _ => D.box.a₀) D.K₀ D.hR hρ₀
      D.ρ₀_lt_one D.box.ha₀ hev)
    D.volumeLink

/-- **The capstone's gap input from the one bridge**: a rate `ρ ∈ (0, 1)` with
`GapAt (transferN hN Φ (preB hN W hU) 0 hphys 0) ρ`.

DERIVED: `0` the plane and the step. -/
theorem gap_of_oneBridge {hN : N ≠ 0} {W : ConfFlow N} {t C : ℝ}
    {hU : ClassMoments hN W (SymPlaqClass N) t C} {r : ℝ}
    {hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r}
    (h : OneBridge hN W hU hphys) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys 0) ρ :=
  h.elim fun D => gapAt_of_noFade hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0
    hphys (noFade_of_oneBridgeData D) 0

/-- **(A) and (B) on the Wilson box from the cell coupling**: edge cells on the Wilson Doob slabs at a
fixed `σ₀ > h` give `RelFloorM` and the uniform bounds, with a constant rate and zoom. -/
theorem ab_of_edgeCost (B : WilsonBox N) (hN : N ≠ 0) {σ : ℕ → ℕ → ℝ} {ρc Ke A σ₀ h ℓ : ℝ}
    {p K₀ : ℕ} (hρc : 0 < ρc) (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hℓ : 0 < ℓ) (hσ₀ : h < σ₀)
    (hσ : ∀ m, 0 < m → ∀ k, K₀ ≤ k → σ₀ ≤ σ m k)
    (h1 : ρc ^ 2 + Ke * A * UniformAperture.edgeSum p (NonAbelianForget.edgeRate σ₀ h ℓ) < 1)
    (hS : ∀ m, 0 < m → ∀ k, K₀ ≤ k →
      EdgeCellsM (B.slab hN m k) ρc Ke A p (NonAbelianForget.edgeRate (σ m k) h ℓ)) :
    ∃ ρ₀ : ℝ, ρ₀ < 1 ∧ RelFloorM (B.slab hN) (fun _ => ρ₀) (fun _ => K₀) := by
  have hq0 := NonAbelianForget.edgeRate_nonneg σ₀ h ℓ
  have hη : 0 ≤ Ke * A * UniformAperture.edgeSum p (NonAbelianForget.edgeRate σ₀ h ℓ) :=
    mul_nonneg (mul_nonneg hKe hA) (UniformAperture.edgeSum_nonneg p hq0)
  exact ⟨_, UniformAperture.cellRate_lt_one hη h1,
    relFloorM_of_edgeCost hρc hKe hA hℓ hσ₀ hσ h1 hS⟩

/-- **The one bridge with (A) and (B) from the cell coupling**: the Wilson box with positive one-step
rates, an observer reading in `(0, R]`, edge cells at a fixed `σ₀ > h`, and the volume link. -/
theorem oneBridge_of_edgeCost {hN : N ≠ 0} {W : ConfFlow N} {t C : ℝ}
    {hU : ClassMoments hN W (SymPlaqClass N) t C} {r : ℝ}
    {hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r}
    (B : WilsonBox N) (hpos : ∀ m k, 0 < m → 0 < (B.kern hN m k).ratio)
    {rLat : ℕ → ℝ} {R : ℝ} (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R)
    {σ : ℕ → ℕ → ℝ} {ρc Ke A σ₀ h ℓ : ℝ}
    {p K₀ : ℕ} (hρc : 0 < ρc) (hKe : 0 ≤ Ke) (hA : 0 ≤ A) (hℓ : 0 < ℓ) (hσ₀ : h < σ₀)
    (hσ : ∀ m, 0 < m → ∀ k, K₀ ≤ k → σ₀ ≤ σ m k)
    (h1 : ρc ^ 2 + Ke * A * UniformAperture.edgeSum p (NonAbelianForget.edgeRate σ₀ h ℓ) < 1)
    (hS : ∀ m, 0 < m → ∀ k, K₀ ≤ k →
      EdgeCellsM (B.slab hN m k) ρc Ke A p (NonAbelianForget.edgeRate (σ m k) h ℓ))
    (hV : VolumeLink (B.gL hN) (gObs hN W hU hphys) rLat) :
    OneBridge hN W hU hphys := by
  obtain ⟨ρ₀, hρ₀1, hA'⟩ := ab_of_edgeCost B hN hρc hKe hA hℓ hσ₀ hσ h1 hS
  exact ⟨{
    box := B
    ratio_pos := hpos
    rLat := rLat
    R := R
    hR := hR
    hr := hr
    ρ := fun _ => ρ₀
    K := fun _ => K₀
    relFloor := hA'
    ρ₀ := ρ₀
    ρ₀_lt_one := hρ₀1
    K₀ := K₀
    uniform := Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩
    volumeLink := hV }⟩

/-! ## 4. The capstone -/

section Capstone

/-- **`PreObserver.obsXN` with the gap as an input**: `observerOSDataSLinkedN` at the arguments of
`obsXN`, with `(ρ, hρ0, hρ1, hg)` in place of the choice from `gapEx'`.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsXNg (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    OSDataSLinked N (SymPlaqClass N) 0 r :=
  observerOSDataSLinkedN hN W (symPlaq_refl N) (symPlaq_nonneg hN)
    (SUInputs.symPlaq_cube_of_classMoments hN W hU) ht
    (zero_le_one.trans (SUInputs.one_le_of_classMoments hN W hU))
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)) SUInputs.q0_mem
    (SUInputs.unitCubeExpBound_of_cubeMomentsAt hN W ht (hU _ SUInputs.q0_mem)) 0 hphys 0 one_pos
    hρ0 hρ1 hg hnt

/-- **The Hamiltonian gap of `obsXNg`**, from its self-adjoint generator.

DERIVED: `0` the plane. -/
theorem obsXNg_gap (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    HamiltonianGap (obsXNg hN W ht hU hphys hρ0 hρ1 hg hnt).base :=
  hamiltonianGap_of_selfAdjoint _
    (observer_generator_isSelfAdjoint hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (preB hN W hU) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0))

/-- **The functional of `obsXNg` is `schwSFM`**, by definition. DERIVED: no numeral. -/
theorem obsXNg_SM (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      (obsXNg hN W ht hU hphys hρ0 hρ1 hg hnt).SM O g
        = schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g :=
  fun _ _ _ _ => rfl

/-- **`obsXNg` carries its Hilbert space**: `v = gvecT` of the pre-observer
(`ClayStatement.obsGen_flow`).

DERIVED: `0` the plane. -/
theorem obsXNg_obsGen (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0) :
    ObsGen hN W (SymPlaqClass N) (symPlaq_refl N) (obsXNg hN W ht hU hphys hρ0 hρ1 hg hnt) :=
  ⟨gvecT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0),
    fun _ => rfl, obsGen_flow hN W (SymPlaqClass N) (symPlaq_refl N) (preB hN W hU) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0)⟩

/-- **`LinkC` at `obsXNg` is `LinkCPre` at the pre-observer.** DERIVED: `0` the plane. -/
theorem obsXNg_linkC_iff (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0)
    (Cs : Composites N) (wC : TSepG Cs.Ix 0 → preH hN W hU hphys) :
    LinkC hN (obsXNg hN W ht hU hphys hρ0 hρ1 hg hnt) Cs wC
      ↔ LinkCPre hN 0 (preVac hN W hU hphys) (preTime hN W hU hphys) Cs wC :=
  Iff.rfl

/-- **The compact vectors of `obsXNg` are `preCvec`.** DERIVED: `0` the plane. -/
theorem obsXNg_cvec (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB hN W hU) 0 hphys 0) ρ)
    (hnt : ∃ u : preH hN W hU hphys, inner ℂ (preVac hN W hU hphys) u = 0 ∧ u ≠ 0)
    (Q : MarginMonoD N (SymPlaqClass N) 0 r) :
    (obsXNg hN W ht hU hphys hρ0 hρ1 hg hnt).cvec Q = preCvec hN W hU hphys Q :=
  rfl

/-- **`ClayStatementAt` at `SymPlaqClass N` at the observer `obsXNg`**: the proof of
`PreObserver.clayStatementAt_SU_at` with `obsXN … hfar hnt` replaced by `obsXNg … hg hnt`.

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane; `8`, `4` as in
`ScalarTie`; `3` the last slot of a rank-four index `α : Idx4`. -/
theorem clayStatementAt_SU_at_gap (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρg : ℝ} (hρ0 : 0 < ρg) (hρ1 : ρg < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) 0 hphys 0)
      ρg)
    (hnt : ∃ u : preH (ne_zero_of_two_le hN2) W hU hphys,
      inner ℂ (preVac (ne_zero_of_two_le hN2) W hU hphys) u = 0 ∧ u ≠ 0)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 →
      (obsXNg (ne_zero_of_two_le hN2) W ht hU hphys hρ0 hρ1 hg hnt).base.H)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hLC : LinkC (ne_zero_of_two_le hN2)
      (obsXNg (ne_zero_of_two_le hN2) W ht hU hphys hρ0 hρ1 hg hnt) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P)
            ((obsXNg (ne_zero_of_two_le hN2) W ht hU hphys hρ0 hρ1 hg hnt).cvec Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) := by
  have hConv := CompReduce.sepConv_of_comp (ne_zero_of_two_le hN2) ρ Cs e he2 hCO.1
  have hHS := LinkReduce.linkHS_of_comp (ne_zero_of_two_le hN2) W (SymPlaqClass N)
    (symPlaq_refl N) _ ρ Cs wC hLC e he1 he2 hX
  obtain ⟨Mb, Zc, hCT1, hCT2⟩ := hCT
  exact clayStatementAt_of_link hN2 W (SymPlaqClass N) (symPlaq_refl N)
    (obsXNg (ne_zero_of_two_le hN2) W ht hU hphys hρ0 hρ1 hg hnt) ρ G
    (LinkReduce.wOfC e wC)
    (obsXNg_SM (ne_zero_of_two_le hN2) W ht hU hphys hρ0 hρ1 hg hnt)
    (obsXNg_gap (ne_zero_of_two_le hN2) W ht hU hphys hρ0 hρ1 hg hnt)
    hRie ⟨rfl, hTie⟩ hConv
    (CompReduce.os0Sep_of_comp _ ρ Cs e he2 hCO.1 hCO.2.1)
    (CompReduce.os1Sep_of_comp _ ρ Cs e he2 hCO.1 hCO.2.2.1) hCov
    (linkTS_of_hs _ W (SymPlaqClass N) (symPlaq_refl N) _ ρ _ hConv hHS)
    (SUInputs.hnt_of_gram hN2 (ne_zero_of_two_le hN2) _ ρ _ hHS.1 hHS.2.2.1 G hK hAF)
    hK hAF hNG
    (CompReduce.tensorNondeg_of_comp _ hN2 ρ Cs e he1 he2 hCO.1 hCO.2.2.2.2)
    ⟨uniformBoundF_energy0 (ne_zero_of_two_le hN2) W (SymPlaqClass N) (symPlaq_refl N)
        (symPlaq_nonneg (ne_zero_of_two_le hN2))
        (SUInputs.symPlaq_cube_of_classMoments (ne_zero_of_two_le hN2) W hU),
      CutSU.cut_of_classMoments (ne_zero_of_two_le hN2) W ht
        (zero_le_one.trans (SUInputs.one_le_of_classMoments (ne_zero_of_two_le hN2) W hU)) hU⟩
    Cs wC ⟨Mb, Zc, hCT1, LinkReduce.topNorm_of_channelTie ρ Mb Zc hCT1 hCT2⟩ hWard hCD hCO hLC
    (LinkReduce.tIn_of_comp _ ρ Cs wC e he1 he2)
    (obsXNg_obsGen (ne_zero_of_two_le hN2) W ht hU hphys hρ0 hρ1 hg hnt)

/-- **`ClayStatementAt` at `SymPlaqClass N` from the inputs of `PreObserver.clayStatementAt_SU_noNT`
with `hfar` replaced by a rate `ρg ∈ (0, 1)` and
`GapAt (transferN hN Φ (preB hN W hU) 0 hphys 0) ρg`**; `wC`, `hLC`, `hX` are stated at the
pre-observer. The observer is `obsXNg … hnt` with `hnt` from `preNontrivial`.

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane; `8`, `4` as in
`ScalarTie`; `3` the last slot of a rank-four index `α : Idx4`. -/
theorem clayStatementAt_SU_noNT_gap (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    {ρg : ℝ} (hρ0 : 0 < ρg) (hρ1 : ρg < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN (ne_zero_of_two_le hN2)
      (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (preB (ne_zero_of_two_le hN2) W hU) 0 hphys 0)
      ρg)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_at_gap hN2 W ht hU hphys hρ0 hρ1 hg
    (preNontrivial hN2 W hU hphys ρ G hK hAF Cs wC e he1 he2 hLC) ρ hRie hTie hCov hCT G hK hAF
    hNG hWard Cs wC e he1 he2 hCD hCO hLC hX

/-- **`ClayStatementAt` at `SymPlaqClass N` from the one bridge**: the inputs of
`PreObserver.clayStatementAt_SU_noNT` with `hfar` replaced by `OneBridge hN W hU hphys`; the gap at
step `0` is `gap_of_oneBridge`. `wC`, `hLC`, `hX` are stated at the pre-observer.

DERIVED: `2` the least colour count and the limit of `TopNorm`; `0` the plane; `8`, `4` as in
`ScalarTie`; `3` the last slot of a rank-four index `α : Idx4`. -/
theorem clayStatementAt_SU_oneBridge (hN2 : 2 ≤ N) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments (ne_zero_of_two_le hN2) W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hOB : OneBridge (ne_zero_of_two_le hN2) W hU hphys)
    (ρ : RenormMix N) (hRie : ρ.Riemann)
    (hTie : ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1
        = Ztr k • (sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)).1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie ρ Mb Zc ∧ Tendsto (fun k => zAct (Zc k) epsC id * dySpacing N k ^ 4) atTop (𝓝 2))
    (G : ℝ → ℝ) (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hWard : WardT (ne_zero_of_two_le hN2) ρ)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → preH (ne_zero_of_two_le hN2) W hU hphys)
    (e : Idx4 → Cs.Ix) (he1 : ∀ α, Cs.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    (he2 : ∀ k α, (Cs.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    (hCD : CompData Cs) (hCO : CompOS (ne_zero_of_two_le hN2) Cs)
    (hLC : LinkCPre (ne_zero_of_two_le hN2) 0 (preVac (ne_zero_of_two_le hN2) W hU hphys)
      (preTime (ne_zero_of_two_le hN2) W hU hphys) Cs wC)
    (hX : ∀ (P : TSep 0) (Q : MarginMonoD N (SymPlaqClass N) 0 r),
      Tendsto (fun k => mixLatT (ne_zero_of_two_le hN2) ρ
          (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 k P.1 Q.1.1) (ultra : Filter ℕ)
          (𝓝 (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
            P.1 Q.1.1))
        ∧ inner ℂ (LinkReduce.wOfC e wC P) (preCvec (ne_zero_of_two_le hN2) W hU hphys Q)
          = (mixT (ne_zero_of_two_le hN2) ρ (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0
              P.1 Q.1.1 : ℂ)) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  clayStatementAt_SU_noNT_gap hN2 W ht hU hphys
    (Classical.choose_spec (gap_of_oneBridge hOB)).1
    (Classical.choose_spec (gap_of_oneBridge hOB)).2.1
    (Classical.choose_spec (gap_of_oneBridge hOB)).2.2
    ρ hRie hTie hCov hCT G hK hAF hNG hWard Cs wC e he1 he2 hCD hCO hLC hX

end Capstone

end MassGap.OneBridgeSU

end

#print axioms MassGap.OneBridgeSU.gapAt_optRate
#print axioms MassGap.OneBridgeSU.gFlow_nonneg
#print axioms MassGap.OneBridgeSU.rate_of_gFlow_pos
#print axioms MassGap.OneBridgeSU.gapAt_step
#print axioms MassGap.OneBridgeSU.gapAt_of_gFlow_pos
#print axioms MassGap.OneBridgeSU.gapAt_of_noFade
#print axioms MassGap.OneBridgeSU.gapAt_of_ratioInvariant
#print axioms MassGap.OneBridgeSU.gapAt_iff_rateFloor
#print axioms MassGap.OneBridgeSU.norm_sq_sum_orth
#print axioms MassGap.OneBridgeSU.norm_sq_sum_le_gram
#print axioms MassGap.OneBridgeSU.contrH_of_cellGramH
#print axioms MassGap.OneBridgeSU.contrM_of_edgeCellsM
#print axioms MassGap.OneBridgeSU.relFloorM_of_edgeCost
#print axioms MassGap.OneBridgeSU.WilsonBox.readsSlab
#print axioms MassGap.OneBridgeSU.noFade_of_oneBridgeData
#print axioms MassGap.OneBridgeSU.gap_of_oneBridge
#print axioms MassGap.OneBridgeSU.ab_of_edgeCost
#print axioms MassGap.OneBridgeSU.oneBridge_of_edgeCost
#print axioms MassGap.OneBridgeSU.obsXNg_gap
#print axioms MassGap.OneBridgeSU.clayStatementAt_SU_at_gap
#print axioms MassGap.OneBridgeSU.clayStatementAt_SU_noNT_gap
#print axioms MassGap.OneBridgeSU.clayStatementAt_SU_oneBridge
