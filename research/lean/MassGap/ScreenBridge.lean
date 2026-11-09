import Mathlib
import MassGap.EffectiveDensityBound

/-!
# MassGap.ScreenBridge — the screen between the exact effective density and the box kernel

`EffectiveDensityBound.UnitOsc` (per-unit log-oscillation of an exact effective density) feeds `hW` through
`CrossingUnitOsc` and supplies the per-block constant of a coarse reading (`coarseRead_osc`). The coarse form of
`hpos` (1b), `CoarseBoundary.CoarseGibbsBound`, asks in addition for a screen `Q` that the torus state and the
infinite-volume state both leave invariant, through which the box kernel `wspec` is read as a coarse Gibbs reading.
This module builds the parts of that screen that are identities and states the part that is not.

## What is proved

* **The coarse screen of one exact step, on the torus** (`coarseQ`, `coarseQ_mul_effStep`, `coarseQ_invariant`,
  `coarseQ_coarse`). `coarseQ n ρ ζ f V` is the reading of `f` over the integrated fine variables `R` under the
  weight `ρ(glueStep(V, R))`: the conditional expectation of `f` given the coarse links `V`. Its denominator is the
  effective density, `coarseQ f V · effStep ρ V = ∫ f ρ dR`; integrated against the effective density it gives the
  fine integral, `∫ coarseQ f · ρ_eff dV = ∫ f ρ dU` (`measurePreserving_glueStep`, through
  `GapSideExactDecimation.integral_glue`); and it fixes every function of the coarse links. This is the
  state-level invariance of the coarse screen for the torus Wilson weight (unnormalised; the normalisations agree
  by `Z_effDens`).
* **Refinement screens are invariant for both states** (`Refines`, `Refines.periodic`, `Refines.torus`,
  `refines_wspec`, `refines_id`). `Refines Λ' Q`: `wspec Λ' ∘ Q = wspec Λ'`, a kernel identity with no state in
  it. The infinite-volume state then leaves `Q` invariant at every observable (`periodicState_dlr` twice), and the
  torus state at every observable whose `Q`-image and itself are local on a support that fits in the torus with
  the box `Λ'` (`torusState_dlr` twice). The two state clauses of `CoarseGibbsBound` are discharged by one kernel
  identity; the torus-to-limit passage is the one already in `periodicState_dlr`.
* **The coarse Gibbs bound from the shared Prop and a factored screen** (`cL_nonneg_of_unitOsc`, `EffScreen`,
  `coarseGibbsBound_of_effScreen`). `EffScreen hN M β F ρ cL Δ`: a refinement screen `Q` of a box `Λ'`, with
  `Q (wspec Λ F) = wRead μ h (ρ ζ ∘ join (c ·))` for coarse block variables `c ω : Fin m → SU 2`, a `join` that
  changes only the coarse link `e b` when block `b` changes, and `(1 − e^{−2 m cL}) δ ≤ Δ`. With `UnitOsc ρ cP cL`
  and `Banded ρ` it gives `CoarseGibbsBound hN M β F Δ`: positivity, integrability and the partition-function
  clause from the band, the per-block clause `cb = cL` from `UnitOsc.link`, the state clauses from `Refines`.
* **The pinned path** (`CoarseUnitOsc`, `EffScreenPixel`, `EffScreenOnePoint`, `boundPixel_of_effScreen`,
  `boundOnePoint_of_effScreen`, `clay_canonical_unitOsc`). `CoarseUnitOsc ρs cP cL`: eventually in `k`, the
  coarse-scale density `ρs k` (one fixed side `n`) is banded with `UnitOsc (ρs k) cP cL`, the constants fixed. With
  the factored screen at the pixel and one-point observables it gives `BoundPixel` and `BoundOnePoint` for
  `CoarseGibbsBound`, and `clay_canonical_unitOsc` is `ExistenceReduce.clay_canonical` with `hpos` replaced by
  `CoarseUnitOsc`, the factored screens and `ReadingFloor`; `hD`, `hW` unchanged.
* **Both items from the `UnitOsc` family** (`sectorSeed_of_crossingUnitOsc`, `unitOsc_feeds_both`).
  `CrossingUnitOsc cP` with `9 · 1024 cP ≤ 1/80000` and `SectorRest` gives `FirstCrossingSectorSeed`
  (`exactEffectiveSmall_of_crossingUnitOsc`, `sectorSeed_of_exactEffectiveSmall`). `unitOsc_feeds_both` gives the
  pinned conclusion and the sector seed together from `CoarseUnitOsc` (coarse scale) and `CrossingUnitOsc`
  (crossing scale), with the factored screens, `ReadingFloor`, `SectorRest`, `hD` and `hW`.

## What is not proved

* `UnitOsc ⇒ (1b)`: NO. The remainder is `EffScreenPixel ∧ EffScreenOnePoint` minus what `Refines` discharges,
  i.e. two clauses per observable:
  1. the factorisation `Q (wspec Λ F) ω = wRead μ h (ρ ζ ∘ join (c ω))` of a refinement screen through coarse
     block variables and the effective density;
  2. the smallness `(1 − e^{−2 m cL}) δ ≤ π √refMomentS`.
* Clause 1 fails for the conditional expectation given the coarse links (argued). A refinement screen of the box
  `Λ'` integrates the fine variables of `Λ'` given the coarse ones and the configuration outside `Λ'`, so its
  output reads the fine face `bdLinks Λ'` through the boundary plaquettes: the count returns at the outer face, as
  for `CoarseBoundary.spec_screen_eq`. A screen whose output reads coarse variables only would need the law of the
  fine variables given the coarse ones to be the same in both states without reference to the exterior, which is
  what the torus screen `coarseQ` has (one torus, one weight) and the infinite-volume state does not. Two type
  mismatches also stand between `coarseQ` and `wspec`: the decimation lives on `SU 2` tori of side `2^j n`, the
  pinned tori have odd extent `2 (2^{c+k} − 1) + 1` and gauge group `SU N`.
* Clause 2 does not follow from `UnitOsc` (argued). `UnitOsc` with fixed `cL` makes `1 − e^{−2 m cL}` a fixed
  number below one; `δ` is the range of the read observable, of order `‖f‖₁ · osc O`, and `√refMomentS` shrinks
  with the cell volume (the Doeblin-route mismatch).
* `FirstCrossingSectorSeed ⇒ WDelta2`: not in the tree. `WDelta2` comes from `WDeltaRun.RunSeed`, whose
  physical-size clause `n · aRun ≤ C` the crossing does not supply.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.ScreenBridge

open MeasureTheory Filter MassGap.CoarseBoundary MassGap.EffectiveDensityBound

/-! ## 1. The coarse screen of one exact step, on the torus -/

section Torus

open MassGap.CompactGauge MassGap.SUN MassGap.TorusDoubling MassGap.GapSideExactDecimation

/-- **The effective density of a banded family is positive.** -/
theorem effStep_pos {n : ℕ} {ρ : DensE (2 * n)} (hb : Banded ρ) (ζ : TPlaq 4 n → SU 2)
    (V : TLink 4 n → SU 2) : 0 < effStep n ρ ζ V := by
  obtain ⟨_, a, _, ha, hab⟩ := effStep_banded n hb ζ
  exact lt_of_lt_of_le ha (hab V).1

/-- **The coarse screen of one exact step**: the reading of `f` over the integrated fine variables under the
weight `ρ(glueStep(V, R))`, the conditional expectation of `f` given the coarse links `V`. -/
def coarseQ (n : ℕ) (ρ : DensE (2 * n)) (ζ : TPlaq 4 n → SU 2) (f : (TLink 4 (2 * n) → SU 2) → ℝ)
    (V : TLink 4 n → SU 2) : ℝ :=
  wRead (restM n) (fun R => f (glueStep n (V, R))) (fun R => ρ (pullTw ζ) (glueStep n (V, R)))

/-- **The denominator of the screen is the effective density.** -/
theorem coarseQ_mul_effStep {n : ℕ} {ρ : DensE (2 * n)} (hb : Banded ρ) (ζ : TPlaq 4 n → SU 2)
    (f : (TLink 4 (2 * n) → SU 2) → ℝ) (V : TLink 4 n → SU 2) :
    coarseQ n ρ ζ f V * effStep n ρ ζ V
      = ∫ R, f (glueStep n (V, R)) * ρ (pullTw ζ) (glueStep n (V, R)) ∂(restM n) := by
  have hp := effStep_pos hb ζ V
  unfold coarseQ wRead
  exact div_mul_cancel₀ _ hp.ne'

/-- **The torus state leaves the coarse screen invariant**: integrated against the effective density, the
screen gives the fine integral. -/
theorem coarseQ_invariant {n : ℕ} {ρ : DensE (2 * n)} (hb : Banded ρ) (ζ : TPlaq 4 n → SU 2)
    {f : (TLink 4 (2 * n) → SU 2) → ℝ}
    (hf : Integrable (fun U => f U * ρ (pullTw ζ) U) (piL (2 * n))) :
    ∫ V, coarseQ n ρ ζ f V * effStep n ρ ζ V ∂(piL n)
      = ∫ U, f U * ρ (pullTw ζ) U ∂(piL (2 * n)) := by
  rw [← integral_glue (measurePreserving_glueStep n) hf]
  refine integral_congr_ae (Eventually.of_forall fun V => ?_)
  exact coarseQ_mul_effStep hb ζ f V

/-- **The coarse screen fixes every function of the coarse links.** -/
theorem coarseQ_coarse {n : ℕ} {ρ : DensE (2 * n)} (hb : Banded ρ) (ζ : TPlaq 4 n → SU 2)
    (g : (TLink 4 n → SU 2) → ℝ) {f : (TLink 4 (2 * n) → SU 2) → ℝ}
    (hfg : ∀ V R, f (glueStep n (V, R)) = g V) (V : TLink 4 n → SU 2) : coarseQ n ρ ζ f V = g V := by
  have hp : 0 < ∫ R, ρ (pullTw ζ) (glueStep n (V, R)) ∂(restM n) := effStep_pos hb ζ V
  simp only [coarseQ, wRead, hfg, integral_const_mul]
  exact mul_div_cancel_right₀ _ hp.ne'

end Torus

/-! ## 2. Refinement screens are invariant for both states -/

section Refine

open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.PeriodicState MassGap.LocalClosing
open MassGap.DLRLimit (IsLocalOnC)

variable {N : ℕ}

/-- **`Q` refines the box kernel at `Λ'`**: `wspec Λ' ∘ Q = wspec Λ'`. -/
def Refines (hN : N ≠ 0) (β : ℝ) (Λ' : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)) : Prop :=
  ∀ G, wspec hN β Λ' (Q G) = wspec hN β Λ' G

/-- The identity refines every box kernel. -/
theorem refines_id (hN : N ≠ 0) (β : ℝ) (Λ' : Finset ILink) : Refines hN β Λ' (fun G => G) :=
  fun _ => rfl

/-- **A smaller box kernel refines a larger one.** -/
theorem refines_wspec (hN : N ≠ 0) (β : ℝ) {Λ₀ Λ' : Finset ILink} (hsub : Λ₀ ⊆ Λ') :
    Refines hN β Λ' (wspec hN β Λ₀) :=
  fun G => (periodicState_dlr_nested hN β hsub G).1

/-- **The infinite-volume state leaves a refinement screen invariant.** -/
theorem Refines.periodic {hN : N ≠ 0} {β : ℝ} {Λ' : Finset ILink}
    {Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)} (h : Refines hN β Λ' Q)
    (G : C(IConf (MassGap.SUN.SU N), ℝ)) : periodicState hN β (Q G) = periodicState hN β G := by
  rw [← periodicState_dlr hN β Λ' (Q G), h G, periodicState_dlr]

/-- **The torus state leaves a refinement screen invariant** at an observable whose image and itself are local
on a support that fits in the torus with the box. -/
theorem Refines.torus {hN : N ≠ 0} {β : ℝ} {Λ' : Finset ILink}
    {Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)} (h : Refines hN β Λ' Q)
    {M : ℕ} {S' : Finset ILink} {G : C(IConf (MassGap.SUN.SU N), ℝ)} (hQG : IsLocalOnC S' (Q G))
    (hG : IsLocalOnC S' G) (hfit : BoxFits M Λ' S') :
    torusState hN M β (Q G) = torusState hN M β G := by
  rw [← torusState_dlr hN M β Λ' S' (Q G) hQG hfit.1 hfit.2, h G,
    torusState_dlr hN M β Λ' S' G hG hfit.1 hfit.2]

end Refine

/-! ## 3. The coarse Gibbs bound from the shared Prop and a factored screen -/

section Bridge

open MassGap.SUN MassGap.TorusDoubling MassGap.GapSideExactDecimation
open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.PeriodicState MassGap.LocalClosing
open MassGap.DLRLimit (IsLocalOnC)

variable {N : ℕ}

/-- **The link constant of the shared Prop is nonnegative.** -/
theorem cL_nonneg_of_unitOsc {n : ℕ} {ρ : DensE n} {cP cL : ℝ} (h : UnitOsc ρ cP cL) (l : TLink 4 n) :
    0 ≤ cL := by
  have := h (Sum.inr l) (fun _ => 1) (fun _ => 1) (fun _ _ => rfl)
  simpa using this

/-- **A factored screen**: a refinement screen `Q` of a box `Λ'` whose image of the box kernel `wspec Λ F` is the
reading, over interior variables `z` with law `μ`, of an observable `h` with values in `[lo, lo + δ]` under the
weight `ρ ζ (join (c ω) z)`; `c ω : Fin m → SU 2` are coarse block variables and `join` changes only the coarse
link `e b` when block `b` changes; and `(1 − e^{−2 m cL}) δ ≤ Δ`. -/
def EffScreen (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) {n : ℕ} (ρ : DensE n)
    (cL Δ : ℝ) : Prop :=
  ∃ (Λ S Λ' S' : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ)) (m : ℕ)
    (e : Fin m → TLink 4 n) (c : IConf (MassGap.SUN.SU N) → Fin m → SU 2)
    (μ : Measure (IConf (MassGap.SUN.SU N))) (ζ : TPlaq 4 n → SU 2)
    (join : (Fin m → SU 2) → IConf (MassGap.SUN.SU N) → TLink 4 n → SU 2)
    (h : IConf (MassGap.SUN.SU N) → ℝ) (lo δ : ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ Refines hN β Λ' Q
    ∧ IsLocalOnC S' (Q (wspec hN β Λ F)) ∧ IsLocalOnC S' (wspec hN β Λ F) ∧ BoxFits M Λ' S'
    ∧ (∀ ω, Q (wspec hN β Λ F) ω = wRead μ h (fun z => ρ ζ (join (c ω) z)))
    ∧ (∀ z b (y y' : Fin m → SU 2), (∀ b', b' ≠ b → y b' = y' b') →
        ∀ l, l ≠ e b → join y z l = join y' z l)
    ∧ IsProbabilityMeasure μ ∧ (∀ y, Measurable (join y)) ∧ Measurable h
    ∧ (∀ z, lo ≤ h z ∧ h z ≤ lo + δ)
    ∧ (1 - Real.exp (-(2 * (m * cL)))) * δ ≤ Δ

/-- **The shared Prop and a factored screen give the coarse Gibbs bound.** -/
theorem coarseGibbsBound_of_effScreen {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {n : ℕ} {ρ : DensE n} {cP cL Δ : ℝ} (hU : UnitOsc ρ cP cL) (hb : Banded ρ)
    (hS : EffScreen hN M β F ρ cL Δ) : CoarseGibbsBound hN M β F Δ := by
  obtain ⟨Λ, S, Λ', S', Q, m, e, c, μ, ζ, join, h, lo, δ, hloc, hfit, hR, hQl, hGl, hfit', hfac,
    hjoin, hμ, hjm, hhm, hh, hle⟩ := hS
  haveI := hμ
  obtain ⟨hm, a, b, ha, hab⟩ := hb ζ
  have hw : ∀ (y : Fin m → SU 2) z, 0 < ρ ζ (join y z) := fun y z => lt_of_lt_of_le ha (hab _).1
  have hmeas : ∀ y : Fin m → SU 2, Measurable (fun z => ρ ζ (join y z)) := fun y => hm.comp (hjm y)
  have iw : ∀ y : Fin m → SU 2, Integrable (fun z => ρ ζ (join y z)) μ := fun y =>
    Integrable.mono' (integrable_const b) (hmeas y).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (hw y z)]
        exact (hab _).2)
  have ihw : ∀ y : Fin m → SU 2, Integrable (fun z => h z * ρ ζ (join y z)) μ := fun y =>
    Integrable.mono' (integrable_const ((|lo| + |lo + δ|) * b)) (hhm.mul (hmeas y)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hw y z)]
        have hz : |h z| ≤ |lo| + |lo + δ| := by
          rw [abs_le]
          have h1 := neg_abs_le lo
          have h2 := le_abs_self (lo + δ)
          have h3 := abs_nonneg lo
          have h4 := abs_nonneg (lo + δ)
          constructor <;> linarith [(hh z).1, (hh z).2]
        exact mul_le_mul hz (hab _).2 (hw y z).le (by positivity))
  have hZ : ∀ y : Fin m → SU 2, 0 < ∫ z, ρ ζ (join y z) ∂μ := fun y => by
    have h1 := integral_mono (integrable_const a) (iw y) (fun z => (hab (join y z)).1)
    rw [integral_const, probReal_univ, one_smul] at h1
    exact lt_of_lt_of_le ha h1
  refine ⟨Λ, S, Q, m, fun _ => SU 2, c, μ, h, fun y z => ρ ζ (join y z), fun _ => cL, lo, δ, hloc,
    hfit, hR.torus hQl hGl hfit', hR.periodic _, hfac, hw, iw, ihw, hZ, hh,
    fun z b y y' hy => hU.link ζ (e b) (join y z) (join y' z) (hjoin z b y y' hy),
    fun b => cL_nonneg_of_unitOsc hU (e b), ?_⟩
  have hs : ∑ _b : Fin m, cL = m * cL := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  show (1 - Real.exp (-(2 * ∑ _b : Fin m, cL))) * δ ≤ Δ
  rw [hs]
  exact hle

end Bridge

/-! ## 4. The pinned path -/

section Pixel

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing
open MassGap.SUN MassGap.GapSideExactDecimation

variable {N : ℕ}

/-- **The shared Prop at the coarse scale**: eventually in `k`, the side-`n` density `ρs k` is banded and has
per-unit oscillation `(cP, cL)`, with `n`, `cP`, `cL` fixed. -/
def CoarseUnitOsc {n : ℕ} (ρs : ℕ → DensE n) (cP cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, UnitOsc (ρs k) cP cL ∧ Banded (ρs k)

/-- **The factored screen at the pixel observable**, eventually in `k`, at `π · √(refMomentS)`. -/
def EffScreenPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, EffScreen hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k)
    (refObs (stateK hN k) O t ℓ k) (ρs k) cL
    (π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k))

/-- **The factored screen at the two one-point observables**, with bounds whose product with the cube weights
is at most `π · √(refMomentS)`. -/
def EffScreenOnePoint (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ Δ₀ Δ₁ : ℝ,
    EffScreen hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) (O.refl 0).1 (ρs k)
      cL Δ₀
    ∧ EffScreen hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) O.1 (ρs k) cL Δ₁
    ∧ |wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)| * Δ₀
        * (|wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)| * Δ₁)
      ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

theorem boundPixel_of_effScreen {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hS : EffScreenPixel hN c O t ℓ π ρs cL) : BoundPixel hN c O t ℓ π (CoarseGibbsBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  exact coarseGibbsBound_of_effScreen hk.1 hk.2 hs

theorem boundOnePoint_of_effScreen {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hS : EffScreenOnePoint hN c O t ℓ π ρs cL) :
    BoundOnePoint hN c O t ℓ π (CoarseGibbsBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  obtain ⟨Δ₀, Δ₁, h₀, h₁, hle⟩ := hs
  exact ⟨Δ₀, Δ₁, coarseGibbsBound_of_effScreen hk.1 hk.2 h₀,
    coarseGibbsBound_of_effScreen hk.1 hk.2 h₁, hle⟩

/-- **The pinned path with `hpos` replaced by the shared Prop at the coarse scale, the factored screens and the
floor**; `hD` and `hW` unchanged. -/
theorem clay_canonical_unitOsc (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hSP : EffScreenPixel hN c O t ℓ π₁ ρs cL) (hS1 : EffScreenOnePoint hN c O t ℓ π₂ ρs cL)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_coarseGibbs hN2 hN O ht c hκ hπ₁ hπ₂ hπκ (boundPixel_of_effScreen hU hSP)
    (boundOnePoint_of_effScreen hU hS1) hF hD hℓ hW

/-- **The `hW` side of the shared Prop**: `CrossingUnitOsc cP` with `9 · 1024 cP ≤ 1/80000` and the rest of the
sectors give the first-crossing sector seed. -/
theorem sectorSeed_of_crossingUnitOsc {cP : ℝ} (hX : CrossingUnitOsc cP) (hcP : 0 ≤ cP)
    (hb : 9 * (1024 * cP) ≤ 1 / 80000) (hR : GapSideVortexAntiDiagonal.SectorRest) :
    GapSideTwistFlat.FirstCrossingSectorSeed :=
  sectorSeed_of_exactEffectiveSmall (exactEffectiveSmall_of_crossingUnitOsc hX hcP le_rfl) hb hR

/-- **One `UnitOsc` family feeds both items**: at the coarse scale (`CoarseUnitOsc`, with the factored screens and
the floor) the pinned conclusion, at the crossing scale (`CrossingUnitOsc`, with the rest of the sectors) the
sector seed. -/
theorem unitOsc_feeds_both (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hSP : EffScreenPixel hN c O t ℓ π₁ ρs cL) (hS1 : EffScreenOnePoint hN c O t ℓ π₂ ρs cL)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    {cX : ℝ} (hX : CrossingUnitOsc cX) (hcX : 0 ≤ cX) (hbX : 9 * (1024 * cX) ≤ 1 / 80000)
    (hR : GapSideVortexAntiDiagonal.SectorRest)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀)
    ∧ GapSideTwistFlat.FirstCrossingSectorSeed :=
  ⟨clay_canonical_unitOsc hN2 hN O ht c hκ hπ₁ hπ₂ hπκ hU hSP hS1 hF hD hℓ hW,
    sectorSeed_of_crossingUnitOsc hX hcX hbX hR⟩

end Pixel

end MassGap.ScreenBridge

end

#print axioms MassGap.ScreenBridge.effStep_pos
#print axioms MassGap.ScreenBridge.coarseQ_mul_effStep
#print axioms MassGap.ScreenBridge.coarseQ_invariant
#print axioms MassGap.ScreenBridge.coarseQ_coarse
#print axioms MassGap.ScreenBridge.refines_id
#print axioms MassGap.ScreenBridge.refines_wspec
#print axioms MassGap.ScreenBridge.Refines.periodic
#print axioms MassGap.ScreenBridge.Refines.torus
#print axioms MassGap.ScreenBridge.cL_nonneg_of_unitOsc
#print axioms MassGap.ScreenBridge.coarseGibbsBound_of_effScreen
#print axioms MassGap.ScreenBridge.boundPixel_of_effScreen
#print axioms MassGap.ScreenBridge.boundOnePoint_of_effScreen
#print axioms MassGap.ScreenBridge.clay_canonical_unitOsc
#print axioms MassGap.ScreenBridge.sectorSeed_of_crossingUnitOsc
#print axioms MassGap.ScreenBridge.unitOsc_feeds_both
