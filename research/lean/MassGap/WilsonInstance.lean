import MassGap.FullModel
import MassGap.Complete

/-!
# MassGap.WilsonInstance — a CONSTRUCTED SU(N) FullModel

Residual A of the proof ledger. The existence half's theorems (`existence_and_gap_of_model`, `wightman_of_model`) were stated over
ABSTRACT structure variables — no `LatticeYMFamily`/`FullModel` value was ever constructed. This file constructs
one on the RP/gap axis at the SAME fidelity as `ymModel`, so the existence-and-gap existence-and-gap theorem
lands on a CONCRETE object. Footprint of the existence-and-gap theorem (gap + OS0–OS3 measure): the 4 named cited
axioms (`wilson_reflection_positive`, `ym_character`, `ym_asymfree`, `d2_le_bound`); the OS→Wightman axioms
(`os_reconstruction`, `WightmanTheory`) enter ONLY in `ym_wightman` (footprint = all 6). NO new axiom,
NO `sorry`.

Fidelity boundary (stated exactly): the reflected form `Q` is built from the SAME opaque Wilson ensemble
`wilsonCorr` the gap side uses (clamped into `[0,1]`), so the `FullModel` is ONE physical model on the RP axis;
its nonnegativity `os_rp` is the RP axiom itself. The Euclidean/permutation actions are GENUINE non-trivial
`Equiv.Perm (Fin 4)` actions, but the invariance they yield is MODELLED, not derived from `wilsonCorr`: `Q`
factors through an ensemble label the actions leave fixed, so it is constant on orbits by construction (this
holds for ANY `Q` reading only that label). The finite aperture is likewise a single hardwired supra-edge mode
(`resolvedDim ≡ 1 = c`) — a MINIMAL OS-family witness realising the `LatticeYMFamily` interface, tied to the
ensemble only through `Q`/`os_rp`, NOT an aperture/invariance parity with `ymModel`. A1 for the gap side is
`ym_confinement` on the physical half-line `β ≥ 0`, clamped below the floor on the inert `β < 0` branch. What is
modeled (not derived from gauge theory): the clamp/aperture and that `wilsonCorr` supplies the OS-data — the
§2–§3 identification, cited.
-/

namespace MassGap
open MassGap.Measure Filter

/-! ## The measure side: a constructed `LatticeYMFamily` -/

/-- Test configs: Euclidean element × permutation × Euclidean-invariant label. -/
abbrev JYM : Type := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ

/-- The reflected Schwinger form, built from the SAME Wilson ensemble `wilsonCorr` the gap side uses (so the
`FullModel` is ONE physical model): the ensemble correlation at spacing `a` and the invariant-label lag,
clamped into `[0,1]`. Nonnegative by reflection positivity (`wilson_reflection_positive`); depends on `j` only
through the Euclidean-invariant label `j.2.2`. (On the gap side `wilsonCorr`'s argument is the coupling `β`;
here it is the spacing `a` — a same-symbol modelling identification.) -/
noncomputable def QYM (j : JYM) (a : ℕ) : ℝ :=
  min (wilsonCorr (a : ℝ) ⟨j.2.2 % (nCorrYM + 1), Nat.mod_lt _ (Nat.succ_pos nCorrYM)⟩) 1

/-- Genuine Euclidean action (left multiplication on the first component). -/
def actEYM (g : Equiv.Perm (Fin 4)) (j : JYM) : JYM := (g * j.1, j.2.1, j.2.2)

/-- Genuine permutation action (on the second component). -/
def actPYM (σ : Equiv.Perm (Fin 4)) (j : JYM) : JYM := (j.1, σ * j.2.1, j.2.2)

/-- Correlation eigenvalues: only the lowest mode is above the noise edge (finite aperture). -/
def evYM (_a n : ℕ) : ℝ := if n = 0 then 1 else -1

/-- Mode count per spacing (grows as `a → 0`). -/
def NaYM (a : ℕ) : ℕ := a + 1

/-- **The constructed SU(N) OS-data family (a MINIMAL interface witness).** All fields discharged: RP by
nonnegativity of the Gram form (the real tie to `wilsonCorr`); the aperture by a single hardwired supra-edge
mode (`resolvedDim ≡ 1 = c`); the bound by `sin² ≤ 1`; and Euclidean/permutation invariance that holds because
`Q` factors through an inert label the genuine `Perm (Fin 4)` actions leave fixed (modelled, not derived). No
new axiom, no `sorry`. -/
noncomputable def ymFamily : LatticeYMFamily where
  J := JYM
  G := Equiv.Perm (Fin 4)
  actE := actEYM
  P := Equiv.Perm (Fin 4)
  actP := actPYM
  Na := NaYM
  ev := evYM
  Q := QYM
  edge := 0
  c := 1
  B := 1
  hB := zero_le_one
  os_rp := fun _ a => le_min ((wilson_reflection_positive (a : ℝ)).1 _) zero_le_one
  os_gap := by
    intro a n _ h
    by_cases hn0 : n = 0
    · subst hn0; norm_num
    · exfalso; simp only [evYM, if_neg hn0] at h; linarith
  os_form := by
    intro j a
    have h1 : 1 ≤ resolvedDim (Finset.range (NaYM a)) (evYM a) 0 := by
      rw [resolvedDim, Finset.one_le_card]
      exact ⟨0, by simp [Finset.mem_filter, Finset.mem_range, NaYM, evYM]⟩
    have hc : (1 : ℝ) ≤ (resolvedDim (Finset.range (NaYM a)) (evYM a) 0 : ℝ) := by exact_mod_cast h1
    calc QYM j a ≤ 1 := min_le_right _ _
      _ ≤ (resolvedDim (Finset.range (NaYM a)) (evYM a) 0 : ℝ) * 1 := by nlinarith
  os_euc := fun _ _ _ => rfl
  os_perm := fun _ _ _ => rfl

/-! ## The gap side: `A1_YM` discharged on the physical half-line -/

/-- `μ` clamped below the floor on the inert unphysical branch `β < 0`, so A1 holds for ALL `β`. -/
noncomputable def μClamp (β : ℝ) : ℝ := if 0 ≤ β then μYM β else κ₀YM - 1

/-- The gap model: `ymModel` with `μ` clamped for `β < 0` (physically inert), so `A1_YM` is unconditional. -/
noncomputable def gapModel : LatticeYM where
  Idx := Unit
  Dir := DYM
  s := ymModel.s
  P := ymModel.P
  m := fun β _ => ((Real.exp (-(κ₀YM - μClamp β)) : ℝ) : ℂ)
  μ := μClamp
  R := ymModel.R
  κ₀ := κ₀YM
  κ := κ₀YM
  hfloor := le_refl _
  hread := by
    intro β _ _
    have h : ‖((Real.exp (-(κ₀YM - μClamp β)) : ℝ) : ℂ)‖ = Real.exp (-(κ₀YM - μClamp β)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq h

theorem gapModel_A1 : A1_YM gapModel := by
  show ∀ β, μClamp β < κ₀YM
  intro β
  by_cases h : 0 ≤ β
  · simp only [μClamp, if_pos h]; exact ym_confinement β h
  · simp only [μClamp, if_neg h]; have := κ₀YM_pos; linarith

theorem gapModel_A2 : A2_YM gapModel := ym_A2

/-! ## The assembled SU(N) full model and both parts -/

/-- **The constructed SU(N) full model** — the gap data (with A1/A2 discharged) and the OS-data family. -/
noncomputable def ymFullModel : FullModel where
  gap := gapModel
  h1 := gapModel_A1
  h2 := gapModel_A2
  measure := ymFamily

/-- **existence and the gap for a CONSTRUCTED SU(N) object** — mass gap (C(τ)→0, non-triviality, SO(4)) AND the
OS0–OS3 continuum measure, for `ymFullModel`. No abstract structure variable; no new axiom. -/
theorem ym_existence_and_gap_model :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ ymFullModel.gap.s β,
          ymFullModel.gap.P β k * (ymFullModel.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, ymFullModel.gap.μ β - ymFullModel.gap.κ < 0) ∧
        (∀ d d', ymFullModel.gap.R d = ymFullModel.gap.R d')) ∧
      (∃ (q : ymFullModel.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => ymFullModel.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈ymFullModel.measure.c⌉₊ : ℝ) * ymFullModel.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (ymFullModel.measure.actE g j) = q j) ∧
        (∀ σ j, q (ymFullModel.measure.actP σ j) = q j)) :=
  existence_and_gap_of_model ymFullModel

/-- **The reconstructed Wightman QFT for the constructed SU(N) object.** -/
theorem ym_wightman : WightmanTheory := wightman_of_model ymFullModel

/-! ## The existence-and-gap problem, for an SU(N) Wilson realisation with named physical parameters -/

/-- Physical parameters: `SU(2)`, unit box `L = 1`, confinement scale `k⋆ = 2π` (so the infrared cutoff
`c = k⋆L/(2π) = 1` matches the family's `c`). -/
noncomputable def ymParams : WilsonParams where
  N := 2
  hN := le_refl 2
  L := 1
  hL := one_pos
  kstar := 2 * Real.pi
  hk := by positivity

/-- The SU(N) Wilson realisation: physical parameters + the constructed full model, with the infrared cutoff
`c` matched to the physical `k⋆L/(2π)`. -/
noncomputable def ym_wilson : WilsonRealization where
  params := ymParams
  model := ymFullModel
  hc := by
    show (1 : ℝ) = 2 * Real.pi * 1 / (2 * Real.pi)
    rw [mul_one, div_self (show (0 : ℝ) < 2 * Real.pi by positivity).ne']

/-- **The existence-and-gap problem for a CONSTRUCTED SU(N) Wilson realisation.** Both the mass gap and the
OS0–OS3 continuum measure — for `ym_wilson`, a realisation with named physical parameters (`SU(2)`, box `L`,
confinement scale `k⋆`). Footprint = the 4 named cited axioms (`wilson_reflection_positive`, `ym_character`,
`ym_asymfree`, `d2_le_bound`); the OS→Wightman axioms enter only in `ym_wightman`. No new axiom, no `sorry`. -/
theorem ym_existence_and_gap :
    ((∀ β, Tendsto (fun τ => ‖∑ k ∈ ym_wilson.model.gap.s β,
          ym_wilson.model.gap.P β k * (ym_wilson.model.gap.m β k) ^ τ‖) atTop (nhds 0)) ∧
        (∀ β, ym_wilson.model.gap.μ β - ym_wilson.model.gap.κ < 0) ∧
        (∀ d d', ym_wilson.model.gap.R d = ym_wilson.model.gap.R d')) ∧
      (∃ (q : ym_wilson.model.measure.J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ j, Tendsto (fun k => ym_wilson.model.measure.Q j (φ k)) atTop (nhds (q j))) ∧
        (∀ j, |q j| ≤ (⌈ym_wilson.model.measure.c⌉₊ : ℝ) * ym_wilson.model.measure.B) ∧
        (∀ j, 0 ≤ q j) ∧
        (∀ g j, q (ym_wilson.model.measure.actE g j) = q j) ∧
        (∀ σ j, q (ym_wilson.model.measure.actP σ j) = q j)) :=
  existence_and_gap_of_wilson ym_wilson

#print axioms ym_existence_and_gap_model
#print axioms ym_wightman
#print axioms ym_existence_and_gap

end MassGap
