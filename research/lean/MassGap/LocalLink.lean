import Mathlib
import MassGap.ClayFull
import MassGap.FlowCapstone
import MassGap.DoublingClay2
import MassGap.WDeltaRun
import MassGap.ApertureBridge
import MassGap.ApertureGap
import MassGap.StrongPhys

/-!
# MassGap.LocalLink — the local route's two inputs read in the observer's `ClayFull`

`ClayFull.clayFullAt_of_observer` builds clauses 1–6 of `ClayFullAt` for the observer's energy density
from ten inputs. The local route `ApertureVolume.clay_two` has two: the near statement `NearWin` and the
far statement `ApertureBridge.PhysDefect`. This module says which observer inputs those two supply.

## The far input supplies the observer's gap (input 4)

The far input is a statement about the Wilson torus at the physical side. Through
`ApertureBridge.runSeed_of_physDefect` it is `WDeltaRun.RunSeed 2`, and `RunSeed N` gives `WDelta2 N ℓ₀`
(`WDeltaRun.wDelta2_of_runSeed`), hence `FixedWindowDecay 0 0 hN (5ℓ₀)`
(`DoublingClay2.fixedWindowDecay_of_WDelta2`): a gap of the gauge-invariant Wilson transfer at every large
coupling, at a physical rate. The flowed field at step `k` is a gauge-invariant local function of the
same Wilson configuration (`Flow.map k`), so its smeared positive-time monomials are vectors of that
transfer; `FlowCapstone.flow_continuum_gap` reads the lattice gap on them and passes to the limit. The
result is `TransferGap.GapAt` of the observer's `transferN` at every step `m₀`, at rate
`exp(−(c/5ℓ₀)·a_{m₀}) < 1`: input 4, for every flow with the uniform bound and a physical range, at
`τ = 0` (`observerGap_of_runSeed`, `observerGapAt_of_runSeed`, `observerClusterAbs_of_runSeed`). The
proof reads nothing of the flow beyond `UniformBoundF` and `PhysRange`. At `N = 2` the far input itself
(`observerGapAt_of_physDefect`) and its sources `ApertureGap.FixedDiffraction` and `StrongPhys.PhysStrong`
give the same.

Only the gap field of `observerOSDataS` reads the step, the window and the rate. Inputs 7–10 are
therefore stated on the objects they read (`ObserverResidual`: `schwSFM`, the flowed time group `timeT`,
the compact vectors `gvecT`), and `observerResidual_iff` identifies them with the four clauses of the
observer's linked data at every step, window and rate.

## What the near input supplies

`NearWin` bounds the local readings by their own reference scale. Through `clay_two` it gives
`DiagBoundSep`, hence `PairBoundSep`, for `Renorm.connected zOwn`: the local reconstruction
`ContinuumSep.contTransferSep` at `zOwn` exists, with its vectors `vecOfSep P`,
`⟪vecOfSep P, vecOfSep Q⟫ = kernSep P Q`, and the step acting as `vecOfSep P ↦ vecOfSep (shift P)`
(`opT_vecOfSep`). Clause 8 (`LocalLink`) asks for those vectors inside the observer's space.
`localLinkOn_of_embed` reduces it to three statements:

* `LocalEmbedOn`: a linear isometry `J` from the local Hilbert space into the observer's space with
  `J ∘ opT_m = time a_m ∘ J` at every dyadic step `m`: the local transfer is the observer's time group
  restricted to the local vectors;
* `KernelConvergesSep` of the observer's field at the renormalisation to `G(|p − q|)`;
* `AFShortDistance G`.

The near input supplies none of the three; it supplies the space `J` starts from
(`localLinkOn_two_of_embed`). The tree has no reading of a flowed and a local field in one state at the
continuum, which `LocalEmbedOn` would be read from.

## The capstones

* `clayFullAt_of_runSeed`: `ClayFullAt` at `τ = 0` from the observer inputs 1–3, 5, 6, the far input
  `RunSeed N` in place of input 4, and `ObserverResidual` (7–10).
* `clayFull_of_runSeed`: `ClayFull` from those at every `N ≥ 2`.
* `clayFullAt_two_of_two`: at `SU(2)` from the local route's two inputs (`NearWin`, `PhysDefect`), the
  observer inputs 1–3, 5, 6, 7, `OS2Zero`, density, and for clause 8 `LocalEmbedOn` at `zOwn`, the kernel
  convergence and `AFShortDistance`.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.LocalLink

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup MassGap.ClayFull Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The far input gives the observer's gap -/

section Far

/-- **The flowed transfer is gapped at every step from the run seed.** For every flow with the uniform
bound and a physical range, at `τ = 0`: some `c, L > 0` have `GapAt (transferN … m) (e^{−(c/L) a_m})` at
every dyadic step `m`.

DERIVED: `2` the least rank of `gapAt_physical_of_fixedWindowDecay`; `0` the plane, the time axis and the
signs; `5` the window factor of `fixedWindowDecay_of_WDelta2`; `2` in `C ≤ 2C` its seed bound. -/
theorem observerGap_of_runSeed (hN2 : 2 ≤ N) (hN : N ≠ 0) (hfar : WDeltaRun.RunSeed N) (Φ : Flow N)
    (hB : UniformBoundF hN Φ) {r : ℝ} (hphys : Φ.PhysRange r) :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀ m : ℕ,
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB 0 hphys m)
        (Real.exp (-(c / L) * dySpacing N m)) := by
  obtain ⟨C, hC, hW⟩ := WDeltaRun.wDelta2_of_runSeed hN hfar
  have hW' := DoublingClay2.fixedWindowDecay_of_WDelta2 hN hC (hW C (by linarith))
  obtain ⟨c, hc, hg⟩ := FlowCapstone.flow_continuum_gap hN2 hN Φ hB 0
    (Flow.posPreserving_of_physRange hN Φ hphys 0) (by positivity : (0 : ℝ) < 5 * C) hW'
  exact ⟨c, 5 * C, hc, by positivity, hg⟩

/-- **Input 4 from the run seed**: at every step `m₀` some `ρ ∈ (0, 1)` has `GapAt (transferN … m₀) ρ`.

DERIVED: `2` the least rank; `0` the plane and the signs; `1` the top of `ρ`. -/
theorem observerGapAt_of_runSeed (hN2 : 2 ≤ N) (hN : N ≠ 0) (hfar : WDeltaRun.RunSeed N) (Φ : Flow N)
    (hB : UniformBoundF hN Φ) {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB 0 hphys m0) ρ := by
  obtain ⟨c, L, hc, hL, hg⟩ := observerGap_of_runSeed hN2 hN hfar Φ hB hphys
  refine ⟨_, Real.exp_pos _, ?_, hg m0⟩
  rw [Real.exp_lt_one_iff, neg_mul]
  exact neg_lt_zero.mpr (mul_pos (div_pos hc hL) (dySpacing_pos (one_le_of_ne_zero hN) m0))

/-- **The observer's clustering at every window from the run seed** (`flowClusterAbs_iff_gapAt`).

DERIVED: `2` the least rank; `0` the plane, the reference step and the sign of `L`. -/
theorem observerClusterAbs_of_runSeed (hN2 : 2 ≤ N) (hN : N ≠ 0) (hfar : WDeltaRun.RunSeed N)
    (Φ : Flow N) (hB : UniformBoundF hN Φ) {r : ℝ} (hphys : Φ.PhysRange r) {L : ℝ} (hL : 0 < L) :
    FlowCapstone.FlowClusterAbs hN Φ 0 r L :=
  (ObserverGapScale.flowClusterAbs_iff_gapAt hN Φ hB 0
    (Flow.posPreserving_of_physRange hN Φ hphys 0) 0 hL).mpr
    (observerGapAt_of_runSeed hN2 hN hfar Φ hB hphys 0)

/-- **Input 4 at `SU(2)` from the local route's far input** `PhysDefect L (1/1000)`.

DERIVED: `2` the rank; `0` the plane and the signs; `1/1000` the seed defect; `1` the top of `ρ`. -/
theorem observerGapAt_of_physDefect {L : ℝ} (hL : 0 < L) (hW : ApertureBridge.PhysDefect L (1 / 1000))
    (Φ : Flow 2) (hB : UniformBoundF two_ne_zero Φ) {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN two_ne_zero Φ hB 0 hphys m0) ρ :=
  observerGapAt_of_runSeed le_rfl two_ne_zero (ApertureBridge.runSeed_of_physDefect hL hW) Φ hB hphys m0

/-- **Input 4 at `SU(2)` from `ApertureGap.FixedDiffraction`.**

DERIVED: `2` the rank; `0` the plane and the signs; `1` the top of `ρ`. -/
theorem observerGapAt_of_fixedDiffraction {m C : ℝ} {d : ℕ} (h : ApertureGap.FixedDiffraction m C d)
    (Φ : Flow 2) (hB : UniformBoundF two_ne_zero Φ) {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN two_ne_zero Φ hB 0 hphys m0) ρ :=
  observerGapAt_of_runSeed le_rfl two_ne_zero (ApertureGap.runSeed_of_fixedDiffraction h) Φ hB hphys m0

/-- **Input 4 at `SU(2)` from `StrongPhys.PhysStrong`.**

DERIVED: `2` the rank; `0` the plane and the signs; `1` the top of `ρ`. -/
theorem observerGapAt_of_physStrong {ℓ₀ t₀ : ℝ} (h : StrongPhys.PhysStrong ℓ₀ t₀)
    (Φ : Flow 2) (hB : UniformBoundF two_ne_zero Φ) {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN two_ne_zero Φ hB 0 hphys m0) ρ :=
  observerGapAt_of_runSeed le_rfl two_ne_zero (StrongPhys.runSeed_of_physStrong h) Φ hB hphys m0

end Far

/-! ## 2. Clauses 7, 8 and `OS2Zero` read without the rate -/

section RateFree

/-- The connected three-point function of a Schwinger functional `S` at the field `O` (`cum3` with
`X.SM`, `X.O` replaced by `S`, `O`).

DERIVED: `1`, `2`, `3` the orders; `2` the cumulant coefficient. -/
def cum3S (S : {ι : Type} → [Fintype ι] → (ι → LField (MassGap.SUN.SU N)) → (ι → Decaying) → ℝ)
    (O : LField (MassGap.SUN.SU N)) (g h k : Decaying) : ℝ :=
  S (fun _ : Fin 3 => O) ![g, h, k]
    - S (fun _ : Fin 2 => O) ![g, h] * S (fun _ : Fin 1 => O) ![k]
    - S (fun _ : Fin 2 => O) ![g, k] * S (fun _ : Fin 1 => O) ![h]
    - S (fun _ : Fin 2 => O) ![h, k] * S (fun _ : Fin 1 => O) ![g]
    + 2 * S (fun _ : Fin 1 => O) ![g] * S (fun _ : Fin 1 => O) ![h] * S (fun _ : Fin 1 => O) ![k]

/-- `NonGaussian` for a Schwinger functional and a field.

DERIVED: `0` the Gaussian value. -/
def NonGaussianS (S : {ι : Type} → [Fintype ι] → (ι → LField (MassGap.SUN.SU N)) → (ι → Decaying) → ℝ)
    (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ g h k : Decaying, cum3S S O g h k ≠ 0

/-- `OS2Zero` for a Schwinger functional.

DERIVED: `0` the margin and the sign. -/
def OS2ZeroS (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4)
    (S : {ι : Type} → [Fintype ι] → (ι → LField (MassGap.SUN.SU N)) → (ι → Decaying) → ℝ) : Prop :=
  ∀ s : Finset (DMarginMono N τ 0), (∀ P ∈ s, ∀ i, (P.1.2 i).1 ∈ D) →
    ∀ c : DMarginMono N τ 0 → ℝ,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * S (pairFields τ P.1 Q.1) (pairFuns τ P.1 Q.1)

/-- `LocalLink` for a Hilbert space `H` with time translations `time` and a field `O`.

DERIVED: `4` in `Fin 4` the dimension. -/
def LocalLinkOn (hN : N ≠ 0) (τ : Fin 4) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (time : ℝ → H →L[ℂ] H) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (G : ℝ → ℝ) (w : ContinuumSep.SepMono N τ → H),
    (∀ P Q : ContinuumSep.SepMono N τ,
      inner ℂ (w P) (w Q) = (ContinuumSep.kernSep hN (Renorm.connected hN Z) τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : ContinuumSep.SepMono N τ),
        w (ContinuumSep.SepMono.shift hN τ m P) = time (dySpacing N m) (w P))
    ∧ ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
        (fun p q => G (ContinuumNontrivial.eDist p q))
    ∧ ShortDistanceY.AFShortDistance G

variable {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}

/-- DERIVED: no numeral. -/
theorem nonGaussian_iff (X : OSDataSLinked N D τ r) : NonGaussian X ↔ NonGaussianS X.SM X.O :=
  Iff.rfl

/-- DERIVED: no numeral. -/
theorem os2Zero_iff (X : OSDataSLinked N D τ r) : OS2Zero X ↔ OS2ZeroS D τ X.SM :=
  Iff.rfl

/-- DERIVED: no numeral. -/
theorem localLink_iff (hN : N ≠ 0) (X : OSDataSLinked N D τ r) :
    LocalLink hN X ↔ LocalLinkOn hN τ X.base.time X.O :=
  Iff.rfl

end RateFree

/-! ## 3. Clause 8 from an embedding of the local reconstruction -/

section Embed

variable (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hB : ContinuumSep.PairBoundSep hN ρ τ)
  (hR : ρ.ReflCompat τ)

/-- **The local transfer moves the local vectors**: `opT_m (vecOfSep P) = vecOfSep (shift_m P)`.

DERIVED: `1` the coefficient; `0` the imaginary component. -/
theorem opT_vecOfSep (m : ℕ) (P : ContinuumSep.SepMono N τ) :
    GNSHilbert.opT (ContinuumSep.contTransferSep hN ρ τ hB hR m)
        (ContinuumSep.vecOfSep hN ρ τ hB hR m P)
      = ContinuumSep.vecOfSep hN ρ τ hB hR m (ContinuumSep.SepMono.shift hN τ m P) := by
  unfold ContinuumSep.vecOfSep
  rw [GNSHilbert.opT_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show Finsupp.mapDomain (ContinuumSep.SepMono.shift hN τ m) (Finsupp.single P 1)
      = Finsupp.single (ContinuumSep.SepMono.shift hN τ m P) 1
    exact Finsupp.mapDomain_single
  · show (ContinuumSep.contTransferSep hN ρ τ hB hR m).T 0 = 0
    exact map_zero _

end Embed

/-- **The local reconstruction inside a Hilbert space with time translations.** A linear isometry `J`
from the Hilbert space of `ContinuumSep.contTransferSep` at `Renorm.connected Z` into `H` carrying the
local transfer at every dyadic step `m` to `time a_m`.

DERIVED: `0` the reference step; `4` in `Fin 4` the dimension. -/
def LocalEmbedOn (hN : N ≠ 0) (τ : Fin 4) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (time : ℝ → H →L[ℂ] H) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) : Prop :=
  ∃ J : GNSHilbert.H (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB
      (Renorm.connected_reflCompat hN Z τ hZ) 0).toReflForm →ₗᵢ[ℂ] H,
    ∀ (m : ℕ) (x : GNSHilbert.H (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB
      (Renorm.connected_reflCompat hN Z τ hZ) 0).toReflForm),
      J (GNSHilbert.opT (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB
          (Renorm.connected_reflCompat hN Z τ hZ) m) x)
        = time (dySpacing N m) (J x)

/-- **Clause 8 from the embedding, the kernel convergence and asymptotic freedom.**
`w P = J (vecOfSep P)`: `J` keeps inner products, so `⟪w P, w Q⟫ = kernSep P Q` (`inner_vecOfSep`), and
`J` intertwines the local step with `time a_m` (`opT_vecOfSep`).

DERIVED: `0` the reference step; `4` in `Fin 4` the dimension. -/
theorem localLinkOn_of_embed (hN : N ≠ 0) (τ : Fin 4) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (time : ℝ → H →L[ℂ] H) (O : LField (MassGap.SUN.SU N))
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.PairBoundSep hN (Renorm.connected hN Z) τ) (hE : LocalEmbedOn hN τ time Z hZ hB)
    (G : ℝ → ℝ)
    (hK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) : LocalLinkOn hN τ time O := by
  obtain ⟨J, hJ⟩ := hE
  have hR := Renorm.connected_reflCompat hN Z τ hZ
  refine ⟨Z, G, fun P => J (ContinuumSep.vecOfSep hN (Renorm.connected hN Z) τ hB hR 0 P),
    fun P Q => ?_, fun m P => ?_, hK, hY⟩
  · rw [LinearIsometry.inner_map_map]
    exact ContinuumSep.inner_vecOfSep hN (Renorm.connected hN Z) τ hB hR 0 P Q
  · show J (ContinuumSep.vecOfSep hN (Renorm.connected hN Z) τ hB hR m
        (ContinuumSep.SepMono.shift hN τ m P))
      = time (dySpacing N m) (J (ContinuumSep.vecOfSep hN (Renorm.connected hN Z) τ hB hR m P))
    rw [← opT_vecOfSep hN (Renorm.connected hN Z) τ hB hR m P]
    exact hJ m _

/-! ## 4. The observer's inputs 7–10, without the rate -/

section Residual

/-- **Inputs 7–10 of the observer, stated on the objects they read.** `NonGaussian` and `OS2Zero` of
`schwSFM` at the field `O`, `LocalLink` for the flowed time group `timeT`, density of the compact
vectors `gvecT`. None reads a step, a window or a rate: `observerResidual_iff`.

DERIVED: `0` the signs; `4` in `Fin 4` the dimension. -/
def ObserverResidual (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) (O : LField (MassGap.SUN.SU N))
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) : Prop :=
  NonGaussianS (schwSFM hN W (SymPlaqClass N) (symPlaq_refl N)) O
    ∧ LocalLinkOn hN τ (timeT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
        (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
          (symPlaq_cube hN W hW hcube)) τ
        (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys τ)) O
    ∧ OS2ZeroS (SymPlaqClass N) τ (schwSFM hN W (SymPlaqClass N) (symPlaq_refl N))
    ∧ Dense (Set.range (fun Q : MarginMonoD N (SymPlaqClass N) τ r =>
        gvecT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
          (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
            (symPlaq_cube hN W hW hcube)) τ
          (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys τ)
          Q.1))

/-- **Inputs 7–10 at any step, window and rate are `ObserverResidual`.**

DERIVED: `0` the signs; `1` the top of `ρ`; `4` in `Fin 4` the dimension. -/
theorem observerResidual_iff (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ SymPlaqClass N) (h : UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) τ r)
    (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube)) τ hphys m0) ρ) :
    (NonGaussian (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
      ∧ LocalLink hN (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
      ∧ OS2Zero (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
      ∧ Dense (Set.range (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT).cvec))
      ↔ ObserverResidual hN W hW hcube O τ hphys :=
  Iff.rfl

end Residual

/-! ## 5. The capstones with the far input in place of the gap -/

section Capstone

/-- **`ClayFullAt` from the run seed.** The observer inputs 1–3 (`hcube`, `hU`, `h`), 5 (`hNT`), 6
(`hpyth`), the far input `RunSeed N` in place of input 4, and inputs 7–10 (`ObserverResidual`), at
`τ = 0`.

DERIVED: `2` the least rank; `0` the plane, the reference step and the signs; `1` the window. -/
theorem clayFullAt_of_runSeed (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ SymPlaqClass N) (h : UnitCubeExpBound hN W O)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
      (∀ i, (F i).1 ∈ SymPlaqClass N ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (rotFam pyth F)
          = contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) F)
    (hfar : WDeltaRun.RunSeed N) (hres : ObserverResidual hN W hW hcube O 0 hphys) :
    ClayFullAt hN W (SymPlaqClass N) (symPlaq_refl N) := by
  obtain ⟨ρ, hρ0, hρ1, hg⟩ := observerGapAt_of_runSeed hN2 hN hfar
    (energy0 W (SymPlaqClass N) (symPlaq_refl N))
    (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW hcube)) hphys 0
  obtain ⟨hNG, hLL, hOS2Z, hdense⟩ :=
    (observerResidual_iff hN W hW hcube ht hC0 hU hO h 0 hphys hNT 0 one_pos hρ0 hρ1 hg).mpr hres
  exact clayFullAt_of_observer hN W hW hcube ht hC0 hU hO h 0 hphys 0 one_pos hρ0 hρ1 hg hNT hpyth
    hNG hLL hOS2Z hdense

/-- **The observer's inputs with the far input in place of the gap**, at one colour count: 1–3, 5, 6,
the run seed, and 7–10 without a rate.

DERIVED: `0` the plane and the signs; `4` in `Fin 4` the dimension. -/
def ObserverInputsFar (hN : N ≠ 0) (W : ConfFlow N) : Prop :=
  ∃ (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N),
        W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) (t C : ℝ) (_ : 0 < t) (_ : 0 ≤ C)
    (_ : ClassMoments hN W (SymPlaqClass N) t C) (O : LField (MassGap.SUN.SU N))
    (_ : O ∈ SymPlaqClass N) (_ : UnitCubeExpBound hN W O) (r : ℝ)
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (_ : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r),
    (∀ (ι : Type) [Fintype ι] (F : ι → SField N),
      (∀ i, (F i).1 ∈ SymPlaqClass N ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (rotFam pyth F)
          = contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) F)
    ∧ WDeltaRun.RunSeed N ∧ ObserverResidual hN W hW hcube O 0 hphys

/-- **`ClayFull` from the far input and the observer's remaining inputs at every `N ≥ 2`.**

DERIVED: `2` the least colour count. -/
theorem clayFull_of_runSeed
    (hin : ∀ N : ℕ, 2 ≤ N → ∃ (hN : N ≠ 0) (W : ConfFlow N), ObserverInputsFar hN W) :
    MassGap.ClayFull := by
  intro N hN2
  obtain ⟨hN, W, hW, hcube, t, C, ht, hC0, hU, O, hO, h, r, hphys, hNT, hpyth, hfar, hres⟩ := hin N hN2
  exact ⟨hN, W, SymPlaqClass N, symPlaq_refl N,
    clayFullAt_of_runSeed hN2 hN W hW hcube ht hC0 hU hO h hphys hNT hpyth hfar hres⟩

end Capstone

/-! ## 6. At `SU(2)` from the local route's two inputs -/

section Two

/-- **Clause 8 at `zOwn` from the local route's two inputs and the embedding.** `clay_two` supplies the
pair bound at `zOwn`, the space `LocalEmbedOn` starts from; `localLinkOn_of_embed` does the rest.

DERIVED: `2` the rank; `8` `clay_two`'s window; `0` the plane and the signs; `1/1000` the seed defect. -/
theorem localLinkOn_two_of_embed {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (time : ℝ → H →L[ℂ] H) (O : LField (MassGap.SUN.SU 2)) {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀)
    (h8 : 8 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1) (hL : 0 < L)
    (hNear : ApertureVolume.NearWin two_ne_zero (dyBeta (one_le_of_ne_zero two_ne_zero)) M₀ s₀)
    (hW : ApertureBridge.PhysDefect L (1 / 1000)) (G : ℝ → ℝ)
    (hE : ∀ hB : ContinuumSep.PairBoundSep two_ne_zero
        (Renorm.connected two_ne_zero (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀)) 0,
      LocalEmbedOn two_ne_zero 0 time (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀)
        (ExistenceReduceOwn.zOwn_refl two_ne_zero s₀ s₀) hB)
    (hK : ContinuumNontrivial.KernelConvergesSep two_ne_zero
      (Renorm.connected two_ne_zero (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀)) 0 O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) : LocalLinkOn two_ne_zero 0 time O := by
  obtain ⟨hD, -⟩ := ApertureVolume.clay_two two_ne_zero hs₀ h8 hL hNear hW
  have hB := ContinuumSep.pairBoundSep_of_diagBoundSep two_ne_zero
    (Renorm.connected two_ne_zero (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀)) 0
    (Renorm.connected_reflCompat two_ne_zero (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀) 0
      (ExistenceReduceOwn.zOwn_refl two_ne_zero s₀ s₀)) hD
  exact localLinkOn_of_embed two_ne_zero 0 time O _ (ExistenceReduceOwn.zOwn_refl two_ne_zero s₀ s₀) hB
    (hE hB) G hK hY

/-- **`ClayFullAt` at `SU(2)` from the local route's two inputs.** The far input `PhysDefect` supplies
input 4 (`observerGapAt_of_physDefect`); with the near input it supplies the local space at `zOwn`
(`localLinkOn_two_of_embed`). The rest: the observer inputs 1–3 (`hcube`, `hU`, `h`), 5 (`hNT`), 6
(`hpyth`), 7 (`hNG`), `OS2Zero`, density, and for clause 8 the embedding `LocalEmbedOn` of the local
space at `zOwn` into the flowed time group, the kernel convergence of `O` at `zOwn` to `G(|p − q|)` and
`AFShortDistance G`.

DERIVED: `2` the rank; `8` `clay_two`'s window; `0` the plane, the reference step and the signs;
`1/1000` the seed defect; `1` the window of the observer's gap. -/
theorem clayFullAt_two_of_two (W : ConfFlow 2)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg 2), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass 2, CubeMomentBound two_ne_zero W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments two_ne_zero W (SymPlaqClass 2) t C)
    {O : LField (MassGap.SUN.SU 2)} (hO : O ∈ SymPlaqClass 2) (h : UnitCubeExpBound two_ne_zero W O)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)).PhysRange r)
    (hNT : FlowConnectedNonzero two_ne_zero (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) 0 r)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField 2),
      (∀ i, (F i).1 ∈ SymPlaqClass 2 ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF two_ne_zero (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) (rotFam pyth F)
          = contSF two_ne_zero (energy0 W (SymPlaqClass 2) (symPlaq_refl 2)) F)
    {M₀ : ℕ} {s₀ L : ℝ} (hs₀ : 0 < s₀) (h8 : 8 * (s₀ + s₀) < M₀ * AsymptoticScaling.aRun 2 1)
    (hL : 0 < L)
    (hNear : ApertureVolume.NearWin two_ne_zero (dyBeta (one_le_of_ne_zero two_ne_zero)) M₀ s₀)
    (hFar : ApertureBridge.PhysDefect L (1 / 1000))
    (hNG : NonGaussianS (schwSFM two_ne_zero W (SymPlaqClass 2) (symPlaq_refl 2)) O)
    (hOS2Z : OS2ZeroS (SymPlaqClass 2) 0 (schwSFM two_ne_zero W (SymPlaqClass 2) (symPlaq_refl 2)))
    (hdense : Dense (Set.range (fun Q : MarginMonoD 2 (SymPlaqClass 2) 0 r =>
        gvecT two_ne_zero (energy0 W (SymPlaqClass 2) (symPlaq_refl 2))
          (uniformBoundF_energy0 two_ne_zero W (SymPlaqClass 2) (symPlaq_refl 2)
            (symPlaq_nonneg two_ne_zero) (symPlaq_cube two_ne_zero W hW hcube)) 0
          (Flow.posPreserving_of_physRange two_ne_zero (energy0 W (SymPlaqClass 2) (symPlaq_refl 2))
            hphys 0) Q.1)))
    (G : ℝ → ℝ)
    (hE : ∀ hB : ContinuumSep.PairBoundSep two_ne_zero
        (Renorm.connected two_ne_zero (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀)) 0,
      LocalEmbedOn two_ne_zero 0
        (timeT two_ne_zero (energy0 W (SymPlaqClass 2) (symPlaq_refl 2))
          (uniformBoundF_energy0 two_ne_zero W (SymPlaqClass 2) (symPlaq_refl 2)
            (symPlaq_nonneg two_ne_zero) (symPlaq_cube two_ne_zero W hW hcube)) 0
          (Flow.posPreserving_of_physRange two_ne_zero (energy0 W (SymPlaqClass 2) (symPlaq_refl 2))
            hphys 0))
        (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀) (ExistenceReduceOwn.zOwn_refl two_ne_zero s₀ s₀) hB)
    (hK : ContinuumNontrivial.KernelConvergesSep two_ne_zero
      (Renorm.connected two_ne_zero (ExistenceReduceOwn.zOwn two_ne_zero s₀ s₀)) 0 O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayFullAt two_ne_zero W (SymPlaqClass 2) (symPlaq_refl 2) :=
  clayFullAt_of_runSeed le_rfl two_ne_zero W hW hcube ht hC0 hU hO h hphys hNT hpyth
    (ApertureBridge.runSeed_of_physDefect hL hFar)
    ⟨hNG, localLinkOn_two_of_embed _ O hs₀ h8 hL hNear hFar G hE hK hY, hOS2Z, hdense⟩

end Two

end MassGap.LocalLink

end

#print axioms MassGap.LocalLink.observerGap_of_runSeed
#print axioms MassGap.LocalLink.observerGapAt_of_runSeed
#print axioms MassGap.LocalLink.observerClusterAbs_of_runSeed
#print axioms MassGap.LocalLink.observerGapAt_of_physDefect
#print axioms MassGap.LocalLink.observerGapAt_of_fixedDiffraction
#print axioms MassGap.LocalLink.observerGapAt_of_physStrong
#print axioms MassGap.LocalLink.nonGaussian_iff
#print axioms MassGap.LocalLink.os2Zero_iff
#print axioms MassGap.LocalLink.localLink_iff
#print axioms MassGap.LocalLink.opT_vecOfSep
#print axioms MassGap.LocalLink.localLinkOn_of_embed
#print axioms MassGap.LocalLink.observerResidual_iff
#print axioms MassGap.LocalLink.clayFullAt_of_runSeed
#print axioms MassGap.LocalLink.clayFull_of_runSeed
#print axioms MassGap.LocalLink.localLinkOn_two_of_embed
#print axioms MassGap.LocalLink.clayFullAt_two_of_two
