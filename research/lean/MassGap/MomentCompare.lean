import Mathlib
import MassGap.RelativeScreen

/-!
# MassGap.MomentCompare — the moment clause of the relative screen

`RelativeScreen.EffScreenRelPixel` carries a moment clause
`√(1 − e^{−2 m cL}) (√V_T + √V_∞) ≤ π √refMomentS`, `V = state((F − s)²)`, at the composite `F` centred in
infinite volume. This module removes both moments from that clause: the infinite-volume one by the
two-sided ratio bound that the factorisation of the screen already carries, the torus one by reading the
pixel at the composite centred in the torus, whose torus second moment is `refMomentS` itself.

## What is proved

* **`refMomentS` is centred** (`refMomentS_eq`). `refMomentS σ O t ℓ k = σ k ((refObs (σ k))²)`: the second
  moment of the reflected pair with each field centred by its one-point value in `σ k` (the renormalisation
  of `refMomentS` is `connectedS σ 1`, which subtracts `σ k O`). It is the second moment of the composite
  centred in the torus, not of the uncentred pair.
* **A two-sided screen bounds one state's moment by the other's** (`state_ratio_le`). Two states invariant
  under `K` at `g`, and `ε K g ω' ≤ K g ω` at every pair `ω, ω'`, give `ε ν₂ g ≤ ν₁ g`.
  `sqrt_le_exp_mul`: `e^{−2x} V₂ ≤ V₁` gives `√V₂ ≤ e^x √V₁`.
* **The factorisation without its moment clause** (`EffScreenFac`, `effScreenRel_of_fac`).
  `EffScreenFac hN M β F ρ m` is `EffScreenRel` with the moment clause and the centre `s` removed; with the
  clause at any `s` it gives `EffScreenRel` back.
* **The infinite-volume moment is controlled by the torus moment** (`fac_ratio`, `fac_moment`). Under
  `UnitOsc ρ cP cL` and `Banded ρ` the factored screen is minorised between every two boundary
  conditions, `e^{−2 m cL} K((F − t)²)(ω') ≤ K((F − t)²)(ω)`, so at every `t`:
  `e^{−2 m cL} V_∞(t) ≤ V_T(t)` and `√V_∞(t) ≤ e^{m cL} √V_T(t)`.
* **The moment clause is a torus inequality** (`effScreenRel_of_fac_torus`): `EffScreenFac`, `UnitOsc`,
  `Banded` and `√(1 − e^{−2 m cL}) (1 + e^{m cL}) √V_T(s) ≤ Δ` give `EffScreenRel … Δ`.
  `fac_factor_le`: `√(1 − e^{−2x}) (1 + e^x) ≤ √(2x) (1 + e^x)` for `x ≥ 0`.
* **The pixel read at the torus-centred composite** (`centringK_eq`, `pixel_splitT`, `BoundPixelT`,
  `pixelPassage_of_boundT`, `clay_canonical_boundT`). The centring inside the infinite volume,
  `stateK(refObs stateK) − stateK(refObs stateTD)`, is minus the product `(W₀ Δ₀)(W₁ Δ₁)` of `centring_eq`
  (`stateK` is translation invariant). So `|refReading − refReadingS stateTD|` is at most the closing
  error at the torus-centred composite plus `|W₀ Δ₀| |W₁ Δ₁|`, and `BoundPixelT` (the closing bound at
  `refObs (stateTD hN c k)`) with `BoundOnePoint` gives `PixelPassage`.
* **The moment clause of the pixel discharged** (`EffScreenFacPixel`, `boundPixelT_of_fac`). At the
  torus-centred composite and `s = 0`, `V_T = refMomentS` exactly (`refMomentS_eq`), so the pixel clause
  is the scalar block condition `√(1 − e^{−2 m cL}) (1 + e^{m cL}) ≤ π` and nothing else.
* **The one-point moment clauses as torus inequalities** (`EffScreenFacOnePoint`, `boundOnePoint_of_fac`).
* **The pinned path** (`clay_canonical_unitOsc_fac`): `ExistenceReduce.clay_canonical` with `hpos` replaced
  by `CoarseUnitOsc`, `EffScreenFacPixel`, `EffScreenFacOnePoint` and `ReadingFloor`; `hD`, `hW` unchanged.
  No infinite-volume moment appears in any hypothesis.

## What is not proved

* The remainder of (1b) on this route is `EffScreenFacPixel ∧ EffScreenFacOnePoint`, per `k`:
  1. the factorisation of a refinement screen through `m` coarse blocks at the squared deviations of the
     torus-centred composite and of the two single-site fields (`EffScreenFac`, unchanged from clause 1 of
     `RelativeScreen`);
  2. the block condition `√(1 − e^{−2 m cL}) (1 + e^{m cL}) ≤ π₁` at the pixel screen; by `fac_factor_le` it
     holds once `m cL` is small against `π₁²`;
  3. the one-point product `|W₀| Δ₀ |W₁| Δ₁ ≤ π₂ √refMomentS` with
     `Δᵢ ≥ √(1 − e^{−2 mᵢ cL}) (1 + e^{mᵢ cL}) √(torus variance of the single-site field)`. At the torus means
     this compares the product of the two cube-weighted single-site deviations with the second moment of the
     smeared composite; no identity links them (argued: it is a ratio of a single-site to a smeared scale).
* The moment clause of `RelativeScreen.EffScreenRelPixel` at the infinite-volume-centred composite is not
  proved in that form; the route here replaces that composite by the torus-centred one, where the clause
  closes.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace MassGap.MomentCompare

open MeasureTheory Filter MassGap.TypicalBoundary MassGap.CoarseBoundary MassGap.RelativeScreen
open MassGap.DLRLimit (State)

/-! ## 1. A two-sided screen compares the two moments -/

section Generic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Two states under a two-sided screen**: invariance of both states under `K` at `g` and
`ε K g ω' ≤ K g ω` at every pair give `ε ν₂ g ≤ ν₁ g`. -/
theorem state_ratio_le (ν₁ ν₂ : State X) (K : C(X, ℝ) → C(X, ℝ)) (g : C(X, ℝ)) {ε : ℝ}
    (h₁ : ν₁ (K g) = ν₁ g) (h₂ : ν₂ (K g) = ν₂ g) (hmin : ∀ ω ω', ε * K g ω' ≤ K g ω) :
    ε * ν₂ g ≤ ν₁ g := by
  rw [← h₁, ← h₂]
  have hpt : ∀ ω', ε * K g ω' ≤ ν₁ (K g) := fun ω' =>
    MassGap.LocalClosing.ge_of_forall_ge ν₁ (fun ω => hmin ω ω')
  have h := MassGap.LocalClosing.le_of_forall_le ν₂ (g := ε • K g) (fun ω' => by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    exact hpt ω')
  rw [ν₂.map_smul] at h
  exact h

/-- `e^{−2x} V₂ ≤ V₁` gives `√V₂ ≤ e^x √V₁`. -/
theorem sqrt_le_exp_mul {V₁ V₂ x : ℝ} (h : Real.exp (-(2 * x)) * V₂ ≤ V₁) :
    Real.sqrt V₂ ≤ Real.exp x * Real.sqrt V₁ := by
  have h2 : Real.exp x * Real.exp x * Real.exp (-(2 * x)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, show x + x + -(2 * x) = 0 by ring, Real.exp_zero]
  have e : V₂ ≤ Real.exp x * Real.exp x * V₁ := by
    calc V₂ = (Real.exp x * Real.exp x * Real.exp (-(2 * x))) * V₂ := by rw [h2, one_mul]
      _ = (Real.exp x * Real.exp x) * (Real.exp (-(2 * x)) * V₂) := by ring
      _ ≤ (Real.exp x * Real.exp x) * V₁ := mul_le_mul_of_nonneg_left h (by positivity)
  calc Real.sqrt V₂ ≤ Real.sqrt (Real.exp x * Real.exp x * V₁) := Real.sqrt_le_sqrt e
    _ = Real.exp x * Real.sqrt V₁ := by
      rw [Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (Real.exp_pos x).le]

/-- **The block factor is small with `x`**: `√(1 − e^{−2x}) (1 + e^x) ≤ √(2x) (1 + e^x)`. -/
theorem fac_factor_le (x : ℝ) :
    Real.sqrt (1 - Real.exp (-(2 * x))) * (1 + Real.exp x)
      ≤ Real.sqrt (2 * x) * (1 + Real.exp x) := by
  have h := Real.add_one_le_exp (-(2 * x))
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (by positivity)

end Generic

/-! ## 2. The factorisation without its moment clause -/

section Factored

open MassGap.SUN MassGap.TorusDoubling MassGap.GapSideExactDecimation MassGap.EffectiveDensityBound
open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.PeriodicState MassGap.LocalClosing
  MassGap.ScreenBridge
open MassGap.DLRLimit (IsLocalOnC)

variable {N : ℕ}

/-- **The factored screen at the squared deviations, without a moment clause**: `EffScreenRel` with the
centre `s` and the clause `√(1 − e^{−2 m cL}) (√V_T + √V_∞) ≤ Δ` removed. -/
def EffScreenFac (hN : N ≠ 0) (M : ℕ) (β : ℝ) (F : C(IConf (MassGap.SUN.SU N), ℝ)) {n : ℕ}
    (ρ : DensE n) (m : ℕ) : Prop :=
  ∃ (Λ S Λ' S' : Finset ILink)
    (Q : C(IConf (MassGap.SUN.SU N), ℝ) → C(IConf (MassGap.SUN.SU N), ℝ))
    (e : Fin m → TLink 4 n) (c : IConf (MassGap.SUN.SU N) → Fin m → SU 2)
    (μ : Measure (IConf (MassGap.SUN.SU N))) (ζ : TPlaq 4 n → SU 2)
    (join : (Fin m → SU 2) → IConf (MassGap.SUN.SU N) → TLink 4 n → SU 2)
    (H : ℝ → IConf (MassGap.SUN.SU N) → ℝ) (C : ℝ → ℝ),
    IsLocalOnC S F ∧ BoxFits M Λ S ∧ Refines hN β Λ' Q ∧ Markov Q ∧ BoxFits M Λ' S'
    ∧ IsLocalOnC S' (Q (wspec hN β Λ F)) ∧ IsLocalOnC S' (wspec hN β Λ F)
    ∧ (∀ t, IsLocalOnC S' (Q (wspec hN β Λ (sqDev F t))))
    ∧ (∀ t, IsLocalOnC S' (wspec hN β Λ (sqDev F t)))
    ∧ (∀ t ω, Q (wspec hN β Λ (sqDev F t)) ω = wRead μ (H t) (fun z => ρ ζ (join (c ω) z)))
    ∧ (∀ z b (y y' : Fin m → SU 2), (∀ b', b' ≠ b → y b' = y' b') →
        ∀ l, l ≠ e b → join y z l = join y' z l)
    ∧ IsProbabilityMeasure μ ∧ (∀ y, Measurable (join y)) ∧ (∀ t, Measurable (H t))
    ∧ (∀ t z, 0 ≤ H t z ∧ H t z ≤ C t)

/-- The factorisation and the moment clause at some centre give `EffScreenRel`. -/
theorem effScreenRel_of_fac {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)}
    {n : ℕ} {ρ : DensE n} {m : ℕ} {cL Δ : ℝ} (hS : EffScreenFac hN M β F ρ m) (s : ℝ)
    (hle : Real.sqrt (1 - Real.exp (-(2 * (m * cL)))) * (Real.sqrt (torusState hN M β (sqDev F s))
        + Real.sqrt (periodicState hN β (sqDev F s))) ≤ Δ) :
    EffScreenRel hN M β F ρ m cL Δ := by
  obtain ⟨Λ, S, Λ', S', Q, e, c, μ, ζ, join, H, C, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15⟩ := hS
  exact ⟨Λ, S, Λ', S', Q, e, c, μ, ζ, join, H, C, s, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, hle⟩

/-- **The infinite-volume moment against the torus moment**: under `UnitOsc` and `Banded` the factored
screen is minorised between every two boundary conditions, so `e^{−2 m cL} V_∞(t) ≤ V_T(t)`. -/
theorem fac_ratio {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)} {n : ℕ}
    {ρ : DensE n} {m : ℕ} {cP cL : ℝ} (hU : UnitOsc ρ cP cL) (hb : Banded ρ)
    (hS : EffScreenFac hN M β F ρ m) (t : ℝ) :
    Real.exp (-(2 * (m * cL))) * periodicState hN β (sqDev F t)
      ≤ torusState hN M β (sqDev F t) := by
  obtain ⟨Λ, S, Λ', S', Q, e, c, μ, ζ, join, H, C, hloc, hfit, hR, hQ, hfit', hQl, hGl, hQl2,
    hGl2, hfac, hjoin, hμ, hjm, hHm, hH⟩ := hS
  haveI := hμ
  obtain ⟨hρm, a, b, ha, hab⟩ := hb ζ
  have hw : ∀ (y : Fin m → SU 2) z, 0 < ρ ζ (join y z) := fun y z => lt_of_lt_of_le ha (hab _).1
  have hmeas : ∀ y : Fin m → SU 2, Measurable (fun z => ρ ζ (join y z)) := fun y =>
    hρm.comp (hjm y)
  have iw : ∀ y : Fin m → SU 2, Integrable (fun z => ρ ζ (join y z)) μ := fun y =>
    Integrable.mono' (integrable_const b) (hmeas y).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (hw y z)]
        exact (hab _).2)
  have ihw : ∀ t (y : Fin m → SU 2), Integrable (fun z => H t z * ρ ζ (join y z)) μ := fun t y =>
    Integrable.mono' (integrable_const (C t * b)) ((hHm t).mul (hmeas y)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hw y z), abs_of_nonneg (hH t z).1]
        exact mul_le_mul (hH t z).2 (hab _).2 (hw y z).le ((hH t z).1.trans (hH t z).2))
  have hZ : ∀ y : Fin m → SU 2, 0 < ∫ z, ρ ζ (join y z) ∂μ := fun y => by
    have h1 := integral_mono (integrable_const a) (iw y) (fun z => (hab (join y z)).1)
    rw [integral_const, probReal_univ, one_smul] at h1
    exact lt_of_lt_of_le ha h1
  have hratio : ∀ (y y' : Fin m → SU 2) z,
      |Real.log (ρ ζ (join y z)) - Real.log (ρ ζ (join y' z))| ≤ m * cL := by
    intro y y' z
    have hosc : BlockOsc (Y := fun _ : Fin m => SU 2) (fun y => Real.log (ρ ζ (join y z)))
        (fun _ => cL) :=
      fun b' y y' hy => hU.link ζ (e b') (join y z) (join y' z) (hjoin z b' y y' hy)
    have h1 := abs_sub_le_sum hosc y y'
    have hs : ∑ _b : Fin m, cL = m * cL := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rwa [hs] at h1
  have hmin : ∀ ω ω', Real.exp (-(2 * (m * cL))) * Q (wspec hN β Λ (sqDev F t)) ω'
      ≤ Q (wspec hN β Λ (sqDev F t)) ω := by
    intro ω ω'
    rw [hfac, hfac]
    have r := fun z => ratio_of_log (hw (c ω') z) (hw (c ω) z) (hratio _ _ z)
    exact wRead_minor (hw _) (fun z => (r z).1) (fun z => (r z).2) (iw _) (iw _) (ihw t _)
      (ihw t _) (hZ _) (fun z => (hH t z).1)
  exact state_ratio_le (torusState hN M β) (periodicState hN β) (fun G => Q (wspec hN β Λ G))
    (sqDev F t)
    ((hR.torus (hQl2 t) (hGl2 t) hfit').trans
      (torusState_dlr hN M β Λ S _ (isLocalOnC_sqDev hloc t) hfit.1 hfit.2))
    ((hR.periodic _).trans (periodicState_dlr hN β Λ _)) hmin

/-- **`√V_∞(t) ≤ e^{m cL} √V_T(t)`** under the factored screen. -/
theorem fac_moment {hN : N ≠ 0} {M : ℕ} {β : ℝ} {F : C(IConf (MassGap.SUN.SU N), ℝ)} {n : ℕ}
    {ρ : DensE n} {m : ℕ} {cP cL : ℝ} (hU : UnitOsc ρ cP cL) (hb : Banded ρ)
    (hS : EffScreenFac hN M β F ρ m) (t : ℝ) :
    Real.sqrt (periodicState hN β (sqDev F t))
      ≤ Real.exp (m * cL) * Real.sqrt (torusState hN M β (sqDev F t)) :=
  sqrt_le_exp_mul (fac_ratio hU hb hS t)

/-- **The moment clause as a torus inequality**: the factored screen and
`√(1 − e^{−2 m cL}) (1 + e^{m cL}) √V_T(s) ≤ Δ` give `EffScreenRel … Δ`. -/
theorem effScreenRel_of_fac_torus {hN : N ≠ 0} {M : ℕ} {β : ℝ}
    {F : C(IConf (MassGap.SUN.SU N), ℝ)} {n : ℕ} {ρ : DensE n} {m : ℕ} {cP cL Δ : ℝ}
    (hU : UnitOsc ρ cP cL) (hb : Banded ρ) (hS : EffScreenFac hN M β F ρ m) (s : ℝ)
    (hle : Real.sqrt (1 - Real.exp (-(2 * (m * cL)))) * (1 + Real.exp (m * cL))
        * Real.sqrt (torusState hN M β (sqDev F s)) ≤ Δ) :
    EffScreenRel hN M β F ρ m cL Δ := by
  refine effScreenRel_of_fac hS s (le_trans ?_ hle)
  have h := fac_moment hU hb hS s
  have h0 := Real.sqrt_nonneg (1 - Real.exp (-(2 * (m * cL))))
  calc Real.sqrt (1 - Real.exp (-(2 * (m * cL))))
        * (Real.sqrt (torusState hN M β (sqDev F s)) + Real.sqrt (periodicState hN β (sqDev F s)))
      ≤ Real.sqrt (1 - Real.exp (-(2 * (m * cL))))
        * (Real.sqrt (torusState hN M β (sqDev F s))
          + Real.exp (m * cL) * Real.sqrt (torusState hN M β (sqDev F s))) :=
        mul_le_mul_of_nonneg_left (by linarith) h0
    _ = Real.sqrt (1 - Real.exp (-(2 * (m * cL)))) * (1 + Real.exp (m * cL))
        * Real.sqrt (torusState hN M β (sqDev F s)) := by ring

end Factored

/-! ## 3. The pixel read at the torus-centred composite -/

section Reading

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing

variable {N : ℕ}

/-- **`refMomentS` is the second moment of the composite centred in `σ`.** -/
theorem refMomentS_eq (σ : ℕ → State (Cfg N)) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (k : ℕ) :
    LightConePassage.refMomentS σ O t ℓ k = σ k (sqDev (refObs (σ k) O t ℓ k) 0) := by
  have h1 : Renorm.pref (connectedS σ (fun _ _ => (1 : ℝ))) k
      (Sum.elim (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))
        (pairFam 0 (ExistenceReduce.refMono O t ℓ) (ExistenceReduce.refMono O t ℓ))) = 1 := by
    simp [Renorm.pref, connectedS]
  have h2 : sqDev (refObs (σ k) O t ℓ k) 0 = refObs (σ k) O t ℓ k * refObs (σ k) O t ℓ k := by
    simp [sqDev]
  unfold LightConePassage.refMomentS latSkRS
  rw [h1, one_mul, h2]
  unfold latS
  rw [Fintype.prod_sum_type]
  rfl

/-- **The centring inside the infinite volume is minus the centring product**: `stateK` is translation
invariant, so the first-order terms of `centring_identity` cancel against the second-order one. -/
theorem centringK_eq (hN : N ≠ 0) (c k : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    stateK hN k (refObs (stateK hN k) O t ℓ k)
        - stateK hN k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)
      = -((wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)
          * (stateK hN k (O.refl 0).1 - RelativeDecay.stateTD hN c k (O.refl 0).1))
        * (wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)
          * (stateK hN k O.1 - RelativeDecay.stateTD hN c k O.1))) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hσ : ∀ (x : MassGap.InfiniteLattice.ISite) (F : C(Cfg N, ℝ)),
      stateK hN k (transObs x F) = stateK hN k F :=
    fun x F => ContinuumNontrivial.stateK_transObs hN k x F
  rw [refObs_eq, refObs_eq, smear_sub_eq ha, smear_sub_eq ha, smear_sub_eq ha, smear_sub_eq ha,
    centring_identity]
  simp only [(stateK hN k).map_sub, (stateK hN k).map_smul, (stateK hN k).map_one,
    state_smear _ hσ ha]
  ring

/-- **The pixel splits at the torus-centred composite**: the closing error there, plus the centring
inside the infinite volume. -/
theorem pixel_splitT (hN : N ≠ 0) (c k : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    |ExistenceReduce.refReading hN O t ℓ k - refReadingS (RelativeDecay.stateTD hN c) O t ℓ k|
      ≤ |stateK hN k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)
          - RelativeDecay.stateTD hN c k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)|
        + |stateK hN k (refObs (stateK hN k) O t ℓ k)
          - stateK hN k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)| := by
  rw [refReading_eq_refReadingS, refReadingS_eq, refReadingS_eq]
  have h := abs_sub_le (stateK hN k (refObs (stateK hN k) O t ℓ k))
    (stateK hN k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k))
    (RelativeDecay.stateTD hN c k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k))
  linarith

/-- **The closing bound at the torus-centred composite**: eventually in `k`, `B` holds for
`refObs (stateTD hN c k)` in the torus of `stateTD hN c k`, at `π · √(refMomentS)`. -/
def BoundPixelT (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ)
    (B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop) : Prop :=
  ∀ᶠ k in atTop, B (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k)
    (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)
    (π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k))

/-- **The pixel from a closing bound at the torus-centred composite and one-point bounds.** -/
theorem pixelPassage_of_boundT (hN : N ≠ 0)
    {B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop}
    (hcl : ∀ M β F Δ, B M β F Δ →
      |MassGap.PeriodicState.torusState hN M β F - MassGap.PeriodicState.periodicState hN β F| ≤ Δ)
    {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π₁ π₂ : ℝ} (hB : BoundPixelT hN c O t ℓ π₁ B)
    (h1 : CoarseBoundary.BoundOnePoint hN c O t ℓ π₂ B) :
    LightConePassage.PixelPassage hN (RelativeDecay.stateTD hN c) O t ℓ (π₁ + π₂) := by
  filter_upwards [hB, h1] with k hk hc
  obtain ⟨Δ₀, Δ₁, h₀, h₁, hle⟩ := hc
  have hp : |stateK hN k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)
      - RelativeDecay.stateTD hN c k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)|
      ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by
    rw [abs_sub_comm]
    exact hcl _ _ _ _ hk
  have d₀ : |stateK hN k (O.refl 0).1 - RelativeDecay.stateTD hN c k (O.refl 0).1| ≤ Δ₀ := by
    rw [abs_sub_comm]
    exact hcl _ _ _ _ h₀
  have d₁ : |stateK hN k O.1 - RelativeDecay.stateTD hN c k O.1| ≤ Δ₁ := by
    rw [abs_sub_comm]
    exact hcl _ _ _ _ h₁
  have hcK : |stateK hN k (refObs (stateK hN k) O t ℓ k)
      - stateK hN k (refObs (RelativeDecay.stateTD hN c k) O t ℓ k)|
      ≤ π₂ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by
    rw [centringK_eq, abs_neg, abs_mul, abs_mul, abs_mul]
    exact le_trans (mul_le_mul (mul_le_mul_of_nonneg_left d₀ (abs_nonneg _))
      (mul_le_mul_of_nonneg_left d₁ (abs_nonneg _)) (by positivity)
      (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans d₀))) hle
  calc |ExistenceReduce.refReading hN O t ℓ k - refReadingS (RelativeDecay.stateTD hN c) O t ℓ k|
      ≤ _ := pixel_splitT hN c k O t ℓ
    _ ≤ π₁ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)
        + π₂ * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) :=
        add_le_add hp hcK
    _ = (π₁ + π₂)
        * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k) := by ring

/-- **The pinned path with `hpos` read through a closing bound at the torus-centred composite,
one-point bounds and the floor.** -/
theorem clay_canonical_boundT (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {B : ℕ → ℝ → C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) → ℝ → Prop}
    (hcl : ∀ M β F Δ, B M β F Δ →
      |MassGap.PeriodicState.torusState hN M β F - MassGap.PeriodicState.periodicState hN β F| ≤ Δ)
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) (hB : BoundPixelT hN c O t ℓ π₁ B)
    (h1 : CoarseBoundary.BoundOnePoint hN c O t ℓ π₂ B)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  LightConePassage.clay_canonical_lightCone hN2 hN O ht c hκ (add_nonneg hπ₁ hπ₂) hπκ
    (pixelPassage_of_boundT hN hcl hB h1) hF hD hℓ hW

end Reading

/-! ## 4. The pinned path with the moment clauses discharged -/

section Pixel

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.LocalClosing
open MassGap.SUN MassGap.GapSideExactDecimation MassGap.EffectiveDensityBound MassGap.ScreenBridge

variable {N : ℕ}

/-- **The factored screen at the torus-centred composite**, eventually in `k`, with a block count `m`
satisfying the scalar block condition `√(1 − e^{−2 m cL}) (1 + e^{m cL}) ≤ π`. -/
def EffScreenFacPixel (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ m : ℕ, EffScreenFac hN (2 * (2 ^ (c + k) - 1) + 1)
    (dyBeta (one_le_of_ne_zero hN) k) (refObs (RelativeDecay.stateTD hN c k) O t ℓ k) (ρs k) m
    ∧ Real.sqrt (1 - Real.exp (-(2 * (m * cL)))) * (1 + Real.exp (m * cL)) ≤ π

/-- **The factored screens at the two single-site fields**, with torus-only moment bounds `Δ₀`, `Δ₁`
whose product with the cube weights is at most `π · √(refMomentS)`. -/
def EffScreenFacOnePoint (hN : N ≠ 0) (c : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ π : ℝ) {n : ℕ}
    (ρs : ℕ → DensE n) (cL : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ (Δ₀ Δ₁ s₀ s₁ : ℝ) (m₀ m₁ : ℕ),
    EffScreenFac hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) (O.refl 0).1
      (ρs k) m₀
    ∧ EffScreenFac hN (2 * (2 ^ (c + k) - 1) + 1) (dyBeta (one_le_of_ne_zero hN) k) O.1 (ρs k) m₁
    ∧ Real.sqrt (1 - Real.exp (-(2 * (m₀ * cL)))) * (1 + Real.exp (m₀ * cL))
        * Real.sqrt (RelativeDecay.stateTD hN c k (sqDev (O.refl 0).1 s₀)) ≤ Δ₀
    ∧ Real.sqrt (1 - Real.exp (-(2 * (m₁ * cL)))) * (1 + Real.exp (m₁ * cL))
        * Real.sqrt (RelativeDecay.stateTD hN c k (sqDev O.1 s₁)) ≤ Δ₁
    ∧ |wsum (dySpacing N k) ((ContinuumNontrivial.cubeTest t ℓ).reflect 0)| * Δ₀
        * (|wsum (dySpacing N k) (ContinuumNontrivial.cubeTest t ℓ)| * Δ₁)
      ≤ π * Real.sqrt (LightConePassage.refMomentS (RelativeDecay.stateTD hN c) O t ℓ k)

/-- **The pixel bound with its moment clause discharged**: at the torus-centred composite and `s = 0`
the torus moment is `refMomentS` (`refMomentS_eq`) and the infinite-volume one is at most
`e^{2 m cL}` times it (`fac_ratio`). -/
theorem boundPixelT_of_fac {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hS : EffScreenFacPixel hN c O t ℓ π ρs cL) : BoundPixelT hN c O t ℓ π (LayerBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  obtain ⟨m, hm, hπ⟩ := hs
  refine layerBound_of_relScreen (relScreen_of_effScreenRel hk.1 hk.2
    (effScreenRel_of_fac_torus hk.1 hk.2 hm 0 ?_))
  rw [refMomentS_eq (RelativeDecay.stateTD hN c) O t ℓ k]
  exact mul_le_mul_of_nonneg_right hπ (Real.sqrt_nonneg _)

theorem boundOnePoint_of_fac {hN : N ≠ 0} {c : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ π : ℝ}
    {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hS : EffScreenFacOnePoint hN c O t ℓ π ρs cL) :
    CoarseBoundary.BoundOnePoint hN c O t ℓ π (LayerBound hN) := by
  filter_upwards [hU, hS] with k hk hs
  obtain ⟨Δ₀, Δ₁, s₀, s₁, m₀, m₁, h₀, h₁, e₀, e₁, hle⟩ := hs
  exact ⟨Δ₀, Δ₁,
    layerBound_of_relScreen (relScreen_of_effScreenRel hk.1 hk.2
      (effScreenRel_of_fac_torus hk.1 hk.2 h₀ s₀ e₀)),
    layerBound_of_relScreen (relScreen_of_effScreenRel hk.1 hk.2
      (effScreenRel_of_fac_torus hk.1 hk.2 h₁ s₁ e₁)), hle⟩

/-- **The pinned path with `hpos` replaced by the shared Prop at the coarse scale, the factored screens
at the squared deviations with torus-only moment conditions, and the floor**; `hD` and `hW` unchanged. -/
theorem clay_canonical_unitOsc_fac (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) (c : ℕ) {π₁ π₂ κ : ℝ} (hκ : 0 < κ) (hπ₁ : 0 ≤ π₁) (hπ₂ : 0 ≤ π₂)
    (hπκ : π₁ + π₂ < κ) {n : ℕ} {ρs : ℕ → DensE n} {cP cL : ℝ} (hU : CoarseUnitOsc ρs cP cL)
    (hSP : EffScreenFacPixel hN c O t ℓ π₁ ρs cL) (hS1 : EffScreenFacOnePoint hN c O t ℓ π₂ ρs cL)
    (hF : LightConePassage.ReadingFloor (RelativeDecay.stateTD hN c) O t ℓ κ)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  clay_canonical_boundT hN2 hN O (fun _ _ _ _ h => h.closing) ht c hκ hπ₁ hπ₂ hπκ
    (boundPixelT_of_fac hU hSP) (boundOnePoint_of_fac hU hS1) hF hD hℓ hW

end Pixel

end MassGap.MomentCompare

end

#print axioms MassGap.MomentCompare.state_ratio_le
#print axioms MassGap.MomentCompare.sqrt_le_exp_mul
#print axioms MassGap.MomentCompare.fac_factor_le
#print axioms MassGap.MomentCompare.effScreenRel_of_fac
#print axioms MassGap.MomentCompare.fac_ratio
#print axioms MassGap.MomentCompare.fac_moment
#print axioms MassGap.MomentCompare.effScreenRel_of_fac_torus
#print axioms MassGap.MomentCompare.refMomentS_eq
#print axioms MassGap.MomentCompare.centringK_eq
#print axioms MassGap.MomentCompare.pixel_splitT
#print axioms MassGap.MomentCompare.pixelPassage_of_boundT
#print axioms MassGap.MomentCompare.clay_canonical_boundT
#print axioms MassGap.MomentCompare.boundPixelT_of_fac
#print axioms MassGap.MomentCompare.boundOnePoint_of_fac
#print axioms MassGap.MomentCompare.clay_canonical_unitOsc_fac
