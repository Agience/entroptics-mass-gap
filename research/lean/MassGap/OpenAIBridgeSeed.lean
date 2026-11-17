import Mathlib
import MassGap.OpenAIBridgeGlue
import MassGap.MeasuredSeed
import MassGap.PurityOddTimeWilson
import MassGap.OpenAIBridgeShift

/-!
# MassGap.OpenAIBridgeSeed — the seed clause of their route from the run seed

The seed clause `hseed` of `OpenAIBridgeGlue.placement_exists` asks, eventually along their volume
order and then in the spacing, for a nonnegative coupling and an even side `n ≥ 2` with
`n · mesh ≤ ℓ` on which the doubling defect of `ZRG g.image` at half their coupling is at most
`1/1000`. This module derives it from `MeasuredSeed.RunSeedAlong` on `SU(n+1)`.

## 1. Their partition function is ours

* `wilsonHol_mapR` — a group homomorphism commutes with every Wilson holonomy;
* `ZRG_image_eq_ZR` — when the image of their gauge group is `SU(n+1)` (`ImageIsSU`),
  `ZRG g.image L β = ZR L (n+1) β`: `imageEquivSU` carries their product Haar measure to ours
  (`map_imageEquivSU_eq_probHaar`) and the Boltzmann weights agree link by link
  (`wilsonDensityG_image_eq_SU`);
* `defectW_eq_image` — the doubling defect of `ZRG g.image` is `ZoomSelfScale.defectW`.

## 2. The seed clause

* `CouplingsAlong` — their half couplings eventually lie in every set of a filter `F`, along their
  order and then in the spacing;
* `MeshTracksRun` — their spacing is eventually at most `κ` times the run spacing `aRun` at half
  their coupling;
* `seedClause_of_runSeedAlong` — `RunSeedAlong (n+1) F`, `CouplingsAlong F`, `MeshTracksRun` and
  nonnegative couplings give `hseed` with `ℓ = κ C`.

The run seed `RunSeedAlong` is itself reduced to measured reads in `MeasuredSeed`.

## 3. On the running schedule

* `OnRunSchedule` — half their coupling is eventually at least `β₁ > 0` with run spacing equal to
  their spacing;
* `meshTracksRun_of_schedule`, `beta_nonneg_of_schedule`, `couplingsAlong_atTop_of_schedule` — the
  schedule gives `MeshTracksRun` with `κ = 1`, nonnegative couplings and `CouplingsAlong atTop`;
* `exists_schedule_beta`, `onRunSchedule_of_eq` — every family's spacing has a schedule coupling,
  and the family with that coupling is on the schedule;
* `seedClause_of_runSeed` — `RunSeed (n+1)` on the schedule gives `hseed`.
-/

namespace MassGap.OpenAIBridgeSeed

open MeasureTheory Filter
open MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge MassGap.RectWilson
  MassGap.RectWilsonG MassGap.OpenAIConfig MassGap.OpenAILink

/-! ## 1. Their partition function is ours -/

/-- A group homomorphism commutes with every Wilson holonomy:
`wilsonHol bd p (f ∘ U) = f (wilsonHol bd p U)` for any boundary word `bd`.

DERIVED: no numeral appears in the statement. -/
theorem wilsonHol_mapR {H K L P : Type} [Group H] [Group K] (f : H →* K)
    (bd : P → List (L × Bool)) (p : P) (U : L → H) :
    wilsonHol bd p (fun i => f (U i)) = f (wilsonHol bd p U) := by
  unfold wilsonHol
  generalize bd p = l
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    split_ifs <;> simp [map_inv]

/-- **Their partition function is ours**: when the image of their gauge group is `SU(n+1)` as a set
of matrices (`hg`), the rectangular Wilson partition function of `g.image` is `ZR` on `SU(n+1)` at
every extent and coupling. `imageEquivSU`, link by link, carries the product of `probHaar g.image`
to the product of `probHaar (SU(n+1))` (`map_imageEquivSU_eq_probHaar`); the holonomies correspond
by `wilsonHol_mapR`, the densities by `wilsonDensityG_image_eq_SU`.

DERIVED: `1` in `n + 1` is their matrix-size shift. -/
theorem ZRG_image_eq_ZR (g : OpenAIConfig.GaugeGroup) (hg : ImageIsSU g) (L : Fin 4 → ℕ) (β : ℝ) :
    ZRG g.image L β = ZR L (g.n + 1) β := by
  rw [← PurityOddTimeWilson.ZRG_SU_eq_ZR]
  have h1 : MeasurePreserving (imageEquivSU g hg) (probHaar g.image)
      (probHaar (MassGap.SUN.SU (g.n + 1))) := by
    have h0 := (imageEquivSU g hg).measurable.measurePreserving (probHaar g.image)
    rwa [map_imageEquivSU_eq_probHaar g hg] at h0
  have hT : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : RLink L => imageEquivSU g hg)
      (Measure.pi fun _ : RLink L => probHaar g.image)
      (Measure.pi fun _ : RLink L => probHaar (MassGap.SUN.SU (g.n + 1))) :=
    measurePreserving_pi _ _ (fun _ => h1)
  unfold ZRG System.partition System.vol
  refine Eq.trans ?_ (hT.integral_comp'
    (fun V : RLink L → MassGap.SUN.SU (g.n + 1) => (sysRG (MassGap.SUN.SU (g.n + 1)) L).boltz β V))
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show Real.exp (-β * ∑ p, MassGap.GaugeGroup.wilsonDensityG g.image (wilsonHol (rbd L) p U))
    = Real.exp (-β * ∑ p, MassGap.GaugeGroup.wilsonDensityG (MassGap.SUN.SU (g.n + 1))
        (wilsonHol (rbd L) p (fun i => imageMulEquivSU g hg (U i))))
  refine congrArg (fun s => Real.exp (-β * s)) (Finset.sum_congr rfl fun p _ => ?_)
  have hm := wilsonHol_mapR (imageMulEquivSU g hg).toMonoidHom (rbd L) p U
  simp only [MulEquiv.coe_toMonoidHom] at hm
  rw [hm]
  exact wilsonDensityG_image_eq_SU g _ _ rfl

/-- The doubling defect of `ZRG g.image` at side `n` is `ZoomSelfScale.defectW` on `SU(n+1)`.

DERIVED: `16` and `2` are the weights and the doubling of `defectW`; `1` in `n + 1` is their
matrix-size shift. -/
theorem defectW_eq_image (g : OpenAIConfig.GaugeGroup) (hg : ImageIsSU g) (β : ℝ) (n : ℕ) :
    16 * Real.log (ZRG g.image (fun _ => n) β) - Real.log (ZRG g.image (fun _ => 2 * n) β)
      = ZoomSelfScale.defectW (g.n + 1) β n := by
  rw [ZRG_image_eq_ZR g hg, ZRG_image_eq_ZR g hg]
  rfl

/-! ## 2. The seed clause -/

variable {g : OpenAIConfig.GaugeGroup}

/-- **Their half couplings follow `F`**: for every set `s` of the filter `F`, eventually along their
volume order and then in the spacing, half their coupling lies in `s`.

DERIVED: `2` halves their coupling to ours. -/
def CouplingsAlong (C : WilsonFamily g) (order : ℕ → ℕ) (F : Filter ℝ) : Prop :=
  ∀ s ∈ F, ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, C.beta N p / 2 ∈ s

/-- **Their spacing tracks the run spacing**: for some `κ > 0`, eventually along their volume order
and then in the spacing, their spacing is at most `κ · aRun (n+1)` at half their coupling.

DERIVED: `0` is the sign of `κ`; `2` halves their coupling; `1` in `n + 1` is their matrix-size
shift. -/
def MeshTracksRun (C : WilsonFamily g) (order : ℕ → ℕ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop,
    C.mesh N ≤ κ * AsymptoticScaling.aRun (g.n + 1) (C.beta N p / 2)

/-- **The seed clause of their route from the run seed.** Let the image of their gauge group be
`SU(n+1)` (`hg`). Suppose the run seed `MeasuredSeed.RunSeedAlong (n+1) F` along a filter `F` of
couplings, that their half couplings follow `F` (`CouplingsAlong`), that their spacing tracks the run
spacing (`MeshTracksRun`), and that their couplings are eventually nonnegative. Then for some
`ℓ > 0`, eventually along their order and then in the spacing, their coupling is nonnegative and the
seed holds on an even side `n ≥ 2` with `n · mesh ≤ ℓ`: the clause `hseed` of
`OpenAIBridgeGlue.placement_exists`. The side is the run seed's power of two; `ℓ = κ C` with `C` the
run seed's bound on `n · aRun`; the defect is `defectW` by `defectW_eq_image`.

DERIVED: `16` and `1000` are the seed; `2` halves their coupling, doubles the side and is the least
side; `0` the signs; `1` in `n + 1` is their matrix-size shift. -/
theorem seedClause_of_runSeedAlong (hg : ImageIsSU g) (C : WilsonFamily g) (order : ℕ → ℕ)
    {F : Filter ℝ} (hrun : MeasuredSeed.RunSeedAlong (g.n + 1) F)
    (hF : CouplingsAlong C order F) (hmesh : MeshTracksRun C order)
    (hβ : ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p ∧
      ∃ n : ℕ, 2 ≤ n ∧ Even n ∧ (n : ℝ) * C.mesh N ≤ ℓ ∧
        16 * Real.log (ZRG g.image (fun _ => n) (C.beta N p / 2))
          - Real.log (ZRG g.image (fun _ => 2 * n) (C.beta N p / 2)) ≤ 1 / 1000 := by
  obtain ⟨K, hK, hS⟩ := hrun
  obtain ⟨κ, hκ, hm⟩ := hmesh
  refine ⟨κ * K, mul_pos hκ hK, ?_⟩
  filter_upwards [hβ, hF _ hS, hm] with p hp1 hp2 hp3
  filter_upwards [hp1, hp2, hp3] with N h1 h2 h3
  obtain ⟨n, hpow, h2n, hnK, hd⟩ := h2
  refine ⟨h1, n, h2n, hpow.even h2n, ?_, ?_⟩
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (n : ℝ) * C.mesh N
        ≤ n * (κ * AsymptoticScaling.aRun (g.n + 1) (C.beta N p / 2)) :=
          mul_le_mul_of_nonneg_left h3 hn0
      _ = κ * (n * AsymptoticScaling.aRun (g.n + 1) (C.beta N p / 2)) := by ring
      _ ≤ κ * K := mul_le_mul_of_nonneg_left hnK hκ.le
  · rw [defectW_eq_image g hg]
    exact hd

/-! ## 3. On the running schedule -/

/-- **Their couplings follow the run**: `β₁ > 0`, and eventually in the spacing, at every volume,
half their coupling is at least `β₁` and the run spacing `aRun (n+1)` there is their spacing.

DERIVED: `0` is the sign of `β₁`; `2` halves their coupling; `1` in `n + 1` is their matrix-size
shift. -/
def OnRunSchedule (C : WilsonFamily g) (β₁ : ℝ) : Prop :=
  0 < β₁ ∧ ∀ᶠ N in atTop, ∀ p, β₁ ≤ C.beta N p / 2 ∧
    AsymptoticScaling.aRun (g.n + 1) (C.beta N p / 2) = C.mesh N

/-- On the running schedule their spacing tracks the run spacing with `κ = 1`.

DERIVED: no numeral. -/
theorem meshTracksRun_of_schedule {C : WilsonFamily g} (order : ℕ → ℕ) {β₁ : ℝ}
    (h : OnRunSchedule C β₁) : MeshTracksRun C order :=
  ⟨1, one_pos, Eventually.of_forall fun _ => h.2.mono fun N hN => by rw [one_mul, (hN _).2]⟩

/-- On the running schedule their couplings are eventually positive, hence nonnegative.

DERIVED: `0` the sign. -/
theorem beta_nonneg_of_schedule {C : WilsonFamily g} (order : ℕ → ℕ) {β₁ : ℝ}
    (h : OnRunSchedule C β₁) :
    ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p :=
  Eventually.of_forall fun p => h.2.mono fun N hN => by linarith [(hN p).1, h.1]

/-- **On the running schedule half their coupling tends to infinity.** On `[β₁, B]` the run spacing
has a positive minimum (`aRun_pos`, compactness), and their spacing tends to zero
(`OpenAIBridgeShift.tendsto_mesh`), so eventually half their coupling exceeds every `B`.

DERIVED: no numeral. -/
theorem couplingsAlong_atTop_of_schedule {C : WilsonFamily g} (order : ℕ → ℕ) {β₁ : ℝ}
    (h : OnRunSchedule C β₁) : CouplingsAlong C order atTop := by
  intro s hs
  obtain ⟨B, hB⟩ := mem_atTop_sets.mp hs
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (le_max_right B β₁)) (AsymptoticScaling.continuous_aRun (g.n + 1)).continuousOn
  have hm : 0 < AsymptoticScaling.aRun (g.n + 1) x :=
    AsymptoticScaling.aRun_pos (by omega) (lt_of_lt_of_le h.1 hx.1)
  have hev : ∀ᶠ N in atTop, C.mesh N < AsymptoticScaling.aRun (g.n + 1) x :=
    (OpenAIBridgeShift.tendsto_mesh C).eventually (gt_mem_nhds hm)
  refine Eventually.of_forall fun p => ?_
  filter_upwards [h.2, hev] with N hN hlt
  apply hB
  by_contra hc
  replace hc := not_le.mp hc
  have hmem : C.beta N p / 2 ∈ Set.Icc β₁ (max B β₁) := ⟨(hN p).1, hc.le.trans (le_max_left _ _)⟩
  have hle := isMinOn_iff.mp hmin _ hmem
  rw [(hN p).2] at hle
  linarith

/-- **The run schedule exists**: for every `β₁ > 0`, eventually in the spacing some coupling at least
`β₁` has run spacing equal to their spacing (`exists_beta_aRun_eq`, since their spacing tends to zero).
A family with `beta N p = 2 b N` is on the running schedule (`onRunSchedule_of_eq`).

DERIVED: `0` the sign of `β₁`; `1` in `n + 1` is their matrix-size shift. -/
theorem exists_schedule_beta (C : WilsonFamily g) {β₁ : ℝ} (hβ₁ : 0 < β₁) :
    ∃ b : ℕ → ℝ, ∀ᶠ N in atTop, β₁ ≤ b N ∧ AsymptoticScaling.aRun (g.n + 1) (b N) = C.mesh N := by
  classical
  have hpos : 0 < AsymptoticScaling.aRun (g.n + 1) β₁ := AsymptoticScaling.aRun_pos (by omega) hβ₁
  have hev := (OpenAIBridgeShift.tendsto_mesh C).eventually (gt_mem_nhds hpos)
  refine ⟨fun N => if hN : 0 < C.mesh N ∧ C.mesh N < AsymptoticScaling.aRun (g.n + 1) β₁ then
    Classical.choose (AsymptoticScaling.exists_beta_aRun_eq (by omega) hN.1 hN.2) else 0, ?_⟩
  filter_upwards [hev] with N hN
  have hm : 0 < C.mesh N := inv_pos.mpr (by exact_mod_cast (C.denominator N).pos)
  rw [dif_pos ⟨hm, hN⟩]
  exact Classical.choose_spec (AsymptoticScaling.exists_beta_aRun_eq (by omega) hm hN)

/-- A family whose coupling is twice a run-schedule coupling `b` is on the running schedule.

DERIVED: `2` doubles `b` to their coupling; `0` the sign of `β₁`; `1` in `n + 1` is their matrix-size
shift. -/
theorem onRunSchedule_of_eq {C : WilsonFamily g} {β₁ : ℝ} (hβ₁ : 0 < β₁) {b : ℕ → ℝ}
    (hb : ∀ᶠ N in atTop, β₁ ≤ b N ∧ AsymptoticScaling.aRun (g.n + 1) (b N) = C.mesh N)
    (hC : ∀ N p, C.beta N p = 2 * b N) : OnRunSchedule C β₁ :=
  ⟨hβ₁, hb.mono fun N hN p => by rw [hC, mul_div_cancel_left₀ _ two_ne_zero]; exact hN⟩

/-- **The seed clause on the running schedule.** If the image of their gauge group is `SU(n+1)`, the
run seed `WDeltaRun.RunSeed (n+1)` holds and their family is on the running schedule, then the clause
`hseed` of `OpenAIBridgeGlue.placement_exists` holds for some `ℓ > 0`.

DERIVED: `16` and `1000` are the seed; `2` halves their coupling, doubles the side and is the least
side; `0` the signs; `1` in `n + 1` is their matrix-size shift. -/
theorem seedClause_of_runSeed (hg : ImageIsSU g) (C : WilsonFamily g) (order : ℕ → ℕ) {β₁ : ℝ}
    (hrun : WDeltaRun.RunSeed (g.n + 1)) (h : OnRunSchedule C β₁) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ᶠ p in Filter.map order atTop, ∀ᶠ N in atTop, 0 ≤ C.beta N p ∧
      ∃ n : ℕ, 2 ≤ n ∧ Even n ∧ (n : ℝ) * C.mesh N ≤ ℓ ∧
        16 * Real.log (ZRG g.image (fun _ => n) (C.beta N p / 2))
          - Real.log (ZRG g.image (fun _ => 2 * n) (C.beta N p / 2)) ≤ 1 / 1000 :=
  seedClause_of_runSeedAlong hg C order ((MeasuredSeed.runSeedAlong_atTop_iff (N := g.n + 1)).mpr hrun)
    (couplingsAlong_atTop_of_schedule order h) (meshTracksRun_of_schedule order h)
    (beta_nonneg_of_schedule order h)

end MassGap.OpenAIBridgeSeed

#print axioms MassGap.OpenAIBridgeSeed.wilsonHol_mapR
#print axioms MassGap.OpenAIBridgeSeed.ZRG_image_eq_ZR
#print axioms MassGap.OpenAIBridgeSeed.defectW_eq_image
#print axioms MassGap.OpenAIBridgeSeed.seedClause_of_runSeedAlong
#print axioms MassGap.OpenAIBridgeSeed.meshTracksRun_of_schedule
#print axioms MassGap.OpenAIBridgeSeed.beta_nonneg_of_schedule
#print axioms MassGap.OpenAIBridgeSeed.couplingsAlong_atTop_of_schedule
#print axioms MassGap.OpenAIBridgeSeed.exists_schedule_beta
#print axioms MassGap.OpenAIBridgeSeed.onRunSchedule_of_eq
#print axioms MassGap.OpenAIBridgeSeed.seedClause_of_runSeed
