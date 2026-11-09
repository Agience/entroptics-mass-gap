import Mathlib
import MassGap.ObserverEnergyMClose
import MassGap.DobrushinGeneral

noncomputable section

/-!
# MassGap.ObserverEnergyMDob — M for the energy density from a coarse view in Dobrushin's class

`ObserverEnergyMClose` reduces M to `CoarseViewInBox`: the coarse view is a limit of periodic box
Gibbs states `wtV β P` whose oscillation-form influence `boxInfl` has row sums `≤ α`. This module
replaces the box Gibbs state by any state consistent with any finite specification whose
total-variation influence has row sums `≤ α` (`DobrushinGeneral`), and proves the same chain to M.

1. **The Dobrushin law of a state** (`DobLaw`, `dobLaw_cov`): `ν` read through a coarse map `χ` is a
   limit along a filter of extents of states `σ_j` on the periodic boxes, each invariant under a
   specification `S_j` whose TV influence matrix `C_j ≥ 0` has row sums `≤ α`. Then every pair of
   bounded local readers with `G_P` outside the `d`-step influence neighbourhood of `G_Q` (eventually
   along the filter) has `|ν(G_P G_Q ∘ χ) − ν(G_P ∘ χ) ν(G_Q ∘ χ)| ≤ 2B θ/(θ − α) · θ^{d+1} · a · 2B`
   (`DobrushinGeneral.cov_spatialS` on each box, passed to the limit).
2. **The hypothesis in the form the data support** (`CoarseViewDobrushin`): `CoarseViewInBox` with
   `BoxLaw` replaced by `DobLaw`. The influence is the TV coefficient of the coarse view's own
   single-link conditional laws; the conditionals are not required to come from a Wilson-plus-potential
   weight.
3. **The chain** (`latClusterRateOn_of_coarseViewDobrushin`, `energy_M_of_coarseViewDobrushin`,
   `energy_M_of_coarseViewDobrushin_86`): `LatClusterRateOn` at `θ^{lv}` for every `θ ∈ (α, 1]`, hence
   M under `η² < (1 − θ^{2 lv k})(1 − ρr²)`. At `α = 86/100`, `θ = 87/100`, every `η ≤ 29/100` passes
   for `lv · k ≥ 1` and `ρr² ≤ 13/20` (`eta_demand_86`); the measured `η = 0.093` passes.
4. **The box is an instance** (`dobLaw_of_boxLaw`, `coarseViewDobrushin_of_coarseViewInBox`): the heat
   baths of `wtV β P` form a specification, `boxInfl` is a TV influence matrix of it, and the box Gibbs
   state is invariant.
5. **Non-vacuity** (`boxInfl_zero`, `boxLaw_haar`, `dobLaw_witness_86`): the product Haar box state
   has a Dobrushin law of class `86/100` (its influence vanishes).

## Scope

`CoarseViewDobrushin` is a hypothesis here. It states that the observer's coarse view at one coarse
scale, on the readers of `S`, is consistent with a finite specification of TV row sum `≤ α < 1`. It is
not derived from the fine measure in this module or anywhere in the tree. The range of the
specification enters only through the `reach` separation clause.
-/

namespace MassGap.ObserverEnergyMDob

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV
  MassGap.ObserverEnergyGap MassGap.ObserverEnergyMClose MassGap.DobrushinGeneral Filter
open MassGap.WeightedTorus (wTorusState wExpect)
open MassGap.LocalPotential (LocalPot LocalPotFam potWeight wtV)
open MassGap.BoxDobrushinCoupling (OscLe boxInfl infl_wtV boxInfl_nonneg wtV_pos continuous_wtV
  gibbsState)
open MassGap.BoxDobrushin (qfun)
open MassGap.BoxDobrushinSpatial (reach)
open scoped Topology

/-! ## 1. The Dobrushin law of a state and its covariance decay -/

section DobLaw

/-- **The links of the periodic box of extent index `j`.**

DERIVED: `4` the spacetime dimension; `2`, `1` write the odd extent `2(j + 299999) + 1` and its
successor; `299999` the extent offset of `ObserverEnergyV.boxSys`. -/
abbrev BoxLk (j : ℕ) : Type := WilsonHypercubic.Link 4 (2 * (j + 299999) + 1 + 1)

/-- **The Dobrushin law of a state read through a coarse map, in TV class `α`**: there are
specifications `S j` on the box links and states `σ j` with `σ j` invariant under `S j`; `C j` is a
non-negative TV influence matrix of `S j` with row sums `≤ α`; and along the filter `𝒰` of extent
indices `σ j` converges on every continuous observable `G` (read on the torus) to `ν(G ∘ χ)`.

DERIVED: `2` the rank, the odd extent and the colour count; `299999` the extent offset; `1` the
successor writing the extent; `0` the sign of `C`. -/
def DobLaw (ν : MassGap.DLRLimit.State (Cfg 2)) (χ : C(Cfg 2, Cfg 2)) (𝒰 : Filter ℕ) (α : ℝ)
    (Cm : (j : ℕ) → BoxLk j → BoxLk j → ℝ) : Prop :=
  ∃ (S : (j : ℕ) → Spec 2 (BoxLk j))
    (σ : (j : ℕ) → MassGap.DLRLimit.State (BoxLk j → MassGap.SUN.SU 2)),
    (∀ j, SInfl (S j) (Cm j)) ∧ (∀ j l k, 0 ≤ Cm j l k) ∧ (∀ j l, ∑ k, Cm j l k ≤ α) ∧
    (∀ j, Invariant (S j) (σ j)) ∧ 𝒰.NeBot ∧
    ∀ G : C(Cfg 2, ℝ), Tendsto (fun j => σ j (tObs (2 * (j + 299999) + 1) G)) 𝒰
      (𝓝 (ν (G.comp χ)))

/-- **Covariance decay of a Dobrushin law.** If `ν` has a Dobrushin law of TV class `α` through `χ`,
`α < θ ≤ 1`, `G_P`, `G_Q` are local on `S_P`, `S_Q` with `|S_P| ≤ a` and `|G_P|, |G_Q| ≤ B`, and
eventually along the filter every torus link of `S_P` lies outside the `d`-step influence
neighbourhood of the torus image of `S_Q`, then
`|ν(G_P G_Q ∘ χ) − ν(G_P ∘ χ) ν(G_Q ∘ χ)| ≤ 2B θ/(θ − α) · θ^{d+1} · a · 2B`
(`DobrushinGeneral.cov_spatialS` on each box, passed to the limit).

DERIVED: `2` the oscillation `2B` and the rank; `299999` the extent offset; `1` the cap beyond `d`,
the successor writing the extent and the bound on `θ`; `0` the signs. -/
theorem dobLaw_cov {ν : MassGap.DLRLimit.State (Cfg 2)} {χ : C(Cfg 2, Cfg 2)} {𝒰 : Filter ℕ}
    {α : ℝ} {Cm : (j : ℕ) → BoxLk j → BoxLk j → ℝ} (hv : DobLaw ν χ 𝒰 α Cm) {θ : ℝ}
    (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) {GP GQ : C(Cfg 2, ℝ)} {SP SQ : Finset ILink}
    (hlP : IsLocalOn SP ⇑GP) (hlQ : IsLocalOn SQ ⇑GQ) {a : ℕ} (hcP : SP.card ≤ a) {B : ℝ}
    (hB0 : 0 ≤ B) (hbP : ∀ U, |GP U| ≤ B) (hbQ : ∀ U, |GQ U| ≤ B) (d : ℕ)
    (hfar : ∀ᶠ j in 𝒰, ∀ l ∈ SP.image (linkMod (2 * (j + 299999) + 1)),
      l ∉ reach (Cm j) (SQ.image (linkMod (2 * (j + 299999) + 1))) d) :
    |ν ((GP * GQ).comp χ) - ν (GP.comp χ) * ν (GQ.comp χ)|
      ≤ 2 * B * θ / (θ - α) * (θ ^ (d + 1) * (a * (2 * B))) := by
  obtain ⟨S, σ, hC, hC0, hrow, hinv, hU, hL⟩ := hv
  haveI := hU
  have hθ0 : 0 ≤ θ := by linarith
  refine le_of_tendsto (((hL (GP * GQ)).sub ((hL GP).mul (hL GQ))).abs) ?_
  filter_upwards [hfar] with j hj
  have e1 : σ j (tObs (2 * (j + 299999) + 1) (GP * GQ))
      = ex (σ j) (fun W => tObs (2 * (j + 299999) + 1) GP W * tObs (2 * (j + 299999) + 1) GQ W) :=
    (ex_mk (σ j) (cmul (tObs (2 * (j + 299999) + 1) GP).continuous
      (tObs (2 * (j + 299999) + 1) GQ).continuous)).symm
  have e2 : σ j (tObs (2 * (j + 299999) + 1) GP) = ex (σ j) (tObs (2 * (j + 299999) + 1) GP) :=
    (ex_mk (σ j) (tObs (2 * (j + 299999) + 1) GP).continuous).symm
  have e3 : σ j (tObs (2 * (j + 299999) + 1) GQ) = ex (σ j) (tObs (2 * (j + 299999) + 1) GQ) :=
    (ex_mk (σ j) (tObs (2 * (j + 299999) + 1) GQ).continuous).symm
  show |σ j (tObs (2 * (j + 299999) + 1) (GP * GQ))
      - σ j (tObs (2 * (j + 299999) + 1) GP) * σ j (tObs (2 * (j + 299999) + 1) GQ)| ≤ _
  rw [e1, e2, e3]
  have hvP := oscLe_tObs hlP hbP (j + 299999)
  have hvQ := oscLe_tObs hlQ hbQ (j + 299999)
  have hc := cov_spatialS (hinv j) (hC j) (hC0 j) (hrow j) hα0 hαθ hθ1
    (tObs (2 * (j + 299999) + 1) GP).continuous (tObs (2 * (j + 299999) + 1) GQ).continuous hvP hvQ
    (SQ.image (linkMod (2 * (j + 299999) + 1))) (by linarith : (0 : ℝ) ≤ 2 * B)
    (fun l hl => if_neg hl) (fun l => by split_ifs <;> linarith) d
    (fun l hl => hj l (by
      by_contra h
      exact hl (if_neg h)))
  refine hc.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 _))
    (div_nonneg (by nlinarith) (by linarith)))
  exact sum_indicator_le _ (by linarith) (Finset.card_image_le.trans hcP)

#print axioms dobLaw_cov

end DobLaw

/-! ## 2. The hypothesis in TV form, and the chain to M -/

section Chain

/-- **The observer's coarse view is in Dobrushin's TV class, on the pairs of `S`.** There are TV
influence matrices `Cₖ`, filters `𝒰ₖ` of extents and coarse maps `χₖ` with:

* eventually in the fine step `k`, the step-`k` state read through `χₖ` has a Dobrushin law of TV
  class `α` with influence `Cₖ` (`DobLaw (stateK k) χₖ 𝒰ₖ α Cₖ`): it is a limit of box states each
  consistent with a specification whose single-link conditionals have TV row sums `≤ α`;
* for every pair `P, Q ∈ S` a support bound `a` and a sup bound `Mb` such that at every time separation
  `n`, eventually in `k`, the reflected smeared product of `P` and the smeared product of `Q` shifted by
  `aₘ₀ n` are `G_P ∘ χₖ`, `G_Q ∘ χₖ` for readers local on `S_P`, `S_Q` (`|S_P| ≤ a`) with
  `|G_P|, |G_Q| ≤ Mb`, and eventually along `𝒰ₖ` the torus image of `S_P` lies outside the
  `lv · n`-step influence neighbourhood (for `Cₖ`) of the torus image of `S_Q`.

This is `ObserverEnergyMClose.CoarseViewInBox` with the box Gibbs law of oscillation class `α`
replaced by an invariant state of any specification of TV class `α`.

DERIVED: `2` is the rank; `299999` the extent offset; `0` the reflection plane; `4` in `Fin 4` is the
spacetime dimension; `1` the successor writing the extent. -/
def CoarseViewDobrushin (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 lv : ℕ) (α : ℝ)
    (S : Set (MarginMono 2 τ r)) : Prop :=
  ∃ (Cm : ℕ → (j : ℕ) → BoxLk j → BoxLk j → ℝ) (𝒰 : ℕ → Filter ℕ) (χ : ℕ → C(Cfg 2, Cfg 2)),
    (∀ᶠ k in atTop, DobLaw (stateK two_ne k) (χ k) (𝒰 k) α (Cm k)) ∧
    ∀ P ∈ S, ∀ Q ∈ S, ∃ (a : ℕ) (Mb : ℝ), ∀ n : ℕ, ∀ᶠ k in atTop,
      ∃ (GP GQ : C(Cfg 2, ℝ)) (SP SQ : Finset ILink),
        IsLocalOn SP ⇑GP ∧ IsLocalOn SQ ⇑GQ ∧ SP.card ≤ a ∧
        (∀ U, |GP U| ≤ Mb) ∧ (∀ U, |GQ U| ≤ Mb) ∧
        LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1)) = GP.comp (χ k) ∧
        prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1)) = GQ.comp (χ k) ∧
        ∀ᶠ j in 𝒰 k, ∀ l ∈ SP.image (linkMod (2 * (j + 299999) + 1)),
          l ∉ reach (Cm k j) (SQ.image (linkMod (2 * (j + 299999) + 1))) (lv * n)

/-- **The coarse view in Dobrushin's TV class gives lattice clustering at `θ^{lv}`** for every
`θ ∈ (α, 1]`, with constant `2B θ/(θ − α) · θ · a · 2B`, `B = max(Mb, 0)` (`dobLaw_cov` at
`d = lv · n`; `latSF_pair_eq`, `prodSmear_empty`, `FlowCapstone.mono_empty`).

DERIVED: `2` the rank and the oscillation `2B`; `0` the reflection plane and the signs; `1` the unit
observable and the cap beyond `d`. -/
theorem latClusterRateOn_of_coarseViewDobrushin {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 lv : ℕ}
    {α : ℝ} {S : Set (MarginMono 2 τ r)} (hV : CoarseViewDobrushin Φ τ r m0 lv α S) {θ : ℝ}
    (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) :
    LatClusterRateOn two_ne Φ τ r m0 (θ ^ lv) S := by
  obtain ⟨Cm, 𝒰, χ, hlaw, hread⟩ := hV
  intro P hPS Q hQS
  obtain ⟨a, Mb, h⟩ := hread P hPS Q hQS
  refine ⟨2 * max Mb 0 * θ / (θ - α) * θ * (a * (2 * max Mb 0)), fun n => ?_⟩
  filter_upwards [hlaw, h n] with k hk hrk
  obtain ⟨GP, GQ, SP, SQ, hlP, hlQ, hcP, hbP, hbQ, hP, hQ, hfar⟩ := hrk
  have e1 : latSF two_ne Φ k (pairFam τ P.1 (Mono.shift (timeVec 2 m0 τ n) Q.1))
      = stateK two_ne k ((GP * GQ).comp (χ k)) := by
    rw [latSF_pair_eq, ContinuousMap.mul_comp, ← hP, ← hQ]
  have e2 : latSF two_ne Φ k (pairFam τ P.1 (emptyMono 2))
      = stateK two_ne k ((GP * 1).comp (χ k)) := by
    rw [latSF_pair_eq, ContinuousMap.mul_comp, ContinuousMap.one_comp, ← hP, mono_empty,
      prodSmear_empty]
  have e3 : latSF two_ne Φ k (pairFam τ (emptyMono 2) (Mono.shift (timeVec 2 m0 τ n) Q.1))
      = stateK two_ne k ((GQ * 1).comp (χ k)) := by
    rw [latSF_pair_eq, ContinuousMap.mul_comp, ContinuousMap.one_comp, ← hQ, mono_empty,
      prodSmear_empty, mul_comm]
    rfl
  rw [e1, e2, e3, mul_one, mul_one]
  have hb := dobLaw_cov hk hα0 hαθ hθ1 hlP hlQ hcP (le_max_right Mb 0)
    (fun U => (hbP U).trans (le_max_left _ _)) (fun U => (hbQ U).trans (le_max_left _ _))
    (lv * n) hfar
  refine hb.trans (le_of_eq ?_)
  rw [pow_succ, pow_mul]
  ring

#print axioms latClusterRateOn_of_coarseViewDobrushin

/-- **M for the energy density from the coarse view in Dobrushin's TV class.**
`CoarseViewDobrushin` of class `α` on a set `S ∋ ∅` with `lv ≥ 1` influence steps per time step, any
`θ ∈ (α, 1)`, and the leakage inputs on `coarseSpan S` at time `k ≥ 1` with `ρr² < 1` and
`η² < (1 − θ^{2 lv k})(1 − ρr²)` give `FlowClusterAbs` (`latClusterRateOn_of_coarseViewDobrushin`,
`ObserverEnergyMClose.energy_M_of_rate_leak`).

DERIVED: `2` is the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `θ`,
`lv`, `k`, `L` and the rates. -/
theorem energy_M_of_coarseViewDobrushin {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv) {α θ : ℝ}
    (hV : CoarseViewDobrushin (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv α S)
    (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ < 1)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ((θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L := by
  have hθ0 : 0 ≤ θ := by linarith
  exact energy_M_of_rate_leak hc0 hc n R D hD s hs hB τ hphys m0 S hS (pow_nonneg hθ0 lv)
    (pow_lt_one₀ hθ0 hθ1 hlv.ne') (latClusterRateOn_of_coarseViewDobrushin hV hα0 hαθ hθ1.le) hk
    hρr hη hL hLw

#print axioms energy_M_of_coarseViewDobrushin

/-- **The η demand at a rate `θ`, reduced to one step.** For `0 ≤ θ ≤ 1`, `lv · k ≥ 1` and
`ρr² ≤ 13/20`, the bound `η² < (1 − θ²) · 7/20` gives `η² < (1 − θ^{2 lv k})(1 − ρr²)`.

DERIVED: `13/20` the largest `ρr²` kept, `7/20 = 1 − 13/20`; `1` the least `lv · k`; `2` the form's
degree; `0`, `1` bracket `θ`. -/
theorem eta_of_margin {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {lv k : ℕ} (hlk : 1 ≤ lv * k)
    {ρr η : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20) (hη : η ^ 2 < (1 - θ ^ 2) * (7 / 20)) :
    η ^ 2 < (1 - ((θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) := by
  have h1 : (θ ^ lv) ^ k ≤ θ := by
    rw [← pow_mul]
    calc θ ^ (lv * k) ≤ θ ^ 1 := pow_le_pow_of_le_one hθ0 hθ1 hlk
      _ = θ := pow_one _
  have h0 : 0 ≤ (θ ^ lv) ^ k := by positivity
  have h2 : ((θ ^ lv) ^ k) ^ 2 ≤ θ ^ 2 := by nlinarith
  have h3 : 0 ≤ 1 - θ ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 1 - ρr ^ 2),
    mul_nonneg h3 (sub_nonneg.2 hρr)]

#print axioms eta_of_margin

/-- **The η demand at `α = 0.86`.** At `θ = 87/100` (just above the measured TV row with rectangle
partners, `0.86`), `lv · k ≥ 1` and `ρr² ≤ 13/20`, every `η` with `η² ≤ (29/100)²` satisfies
`η² < (1 − θ^{2 lv k})(1 − ρr²)`: `0.0841 < (1 − 0.7569) · 0.35 = 0.085085`.

DERIVED: `87/100` the rate, `86/100 < 87/100`; `29/100` the largest `η` kept; `13/20`, `7/20` as in
`eta_of_margin`; `1` the least `lv · k`; `2` the degree. -/
theorem eta_demand_86 {lv k : ℕ} (hlk : 1 ≤ lv * k) {ρr η : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hη : η ^ 2 ≤ (29 / 100) ^ 2) :
    η ^ 2 < (1 - (((87 / 100 : ℝ) ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) :=
  eta_of_margin (by norm_num) (by norm_num) hlk hρr (by linarith)

#print axioms eta_demand_86

/-- **The η demand at `α = 0.9`.** At `θ = 91/100`, every `η` with `η² ≤ (24/100)²` passes:
`0.0576 < (1 − 0.8281) · 0.35 = 0.060165`.

DERIVED: `91/100` the rate, `9/10 < 91/100`; `24/100` the largest `η` kept; the rest as in
`eta_demand_86` (`13/20` as in `eta_of_margin`). -/
theorem eta_demand_90 {lv k : ℕ} (hlk : 1 ≤ lv * k) {ρr η : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hη : η ^ 2 ≤ (24 / 100) ^ 2) :
    η ^ 2 < (1 - (((91 / 100 : ℝ) ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) :=
  eta_of_margin (by norm_num) (by norm_num) hlk hρr (by linarith)

#print axioms eta_demand_90

/-- **M from the coarse view in Dobrushin's TV class at `α = 0.86`, at the measured leakage.** If
the coarse view is in TV class `86/100` with `lv ≥ 1`, and the leakage inputs hold at time `k ≥ 1`
with `η = 0.093` and `ρr² ≤ 13/20`, then `FlowClusterAbs` holds (`energy_M_of_coarseViewDobrushin`
at `θ = 87/100`, `eta_demand_86`).

DERIVED: `86/100` the TV row with rectangle partners read at `2.56 r0`; `87/100`, `13/20` as in
`eta_demand_86`; `93/1000` the leakage `η = 0.093` measured at one coarse step; `2` the rank; `1/6`
the dominance bound; `0` and `1` bracket `lv`, `k`, `L`. -/
theorem energy_M_of_coarseViewDobrushin_86 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv)
    (hV : CoarseViewDobrushin (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv (86 / 100) S)
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr
      (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_coarseViewDobrushin hc0 hc n R D hD s hs hB τ hphys m0 S hS hlv hV (by norm_num)
    (by norm_num : (86 / 100 : ℝ) < 87 / 100) (by norm_num) hk (by linarith)
    (eta_demand_86 (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hlv.ne' hk.ne')) hρr
      (by norm_num)) hL hLw

#print axioms energy_M_of_coarseViewDobrushin_86

end Chain

/-! ## 3. The box is an instance -/

section Box

/-- **A box law is a Dobrushin law** with the box influence `boxInfl`: the heat baths of
`wtV β (Fp.P M)` form a specification (`heatSpec`), `boxInfl` is a TV influence matrix of it
(`infl_wtV`, `sInfl_heat`), the box Gibbs state is invariant (`invariant_gibbs`), and it is the
periodic state `wTorusState (potWeight β Fp)` on torus readings, by definition.

DERIVED: `2` the rank, the odd extent and the colour count; `299999` the extent offset; `1` the
successor and the least extent; `0` the sign of `β`. -/
theorem dobLaw_of_boxLaw {ν : MassGap.DLRLimit.State (Cfg 2)} {χ : C(Cfg 2, Cfg 2)} {β : ℝ}
    {Fp : LocalPotFam 2} {𝒰 : Filter ℕ} {α : ℝ} (hv : BoxLaw ν χ β Fp 𝒰 α) :
    DobLaw ν χ 𝒰 α (fun j => boxInfl β (Fp.P (2 * (j + 299999) + 1))) := by
  obtain ⟨hβ0, hrow, hU, hL⟩ := hv
  refine ⟨fun j => heatSpec (wtV_pos β (Fp.P (2 * (j + 299999) + 1)))
      (continuous_wtV β (Fp.P (2 * (j + 299999) + 1))),
    fun j => gibbsState (wtV_pos β (Fp.P (2 * (j + 299999) + 1)))
      (continuous_wtV β (Fp.P (2 * (j + 299999) + 1))),
    fun j => sInfl_heat _ _ (infl_wtV two_ne hβ0 (Fp.P (2 * (j + 299999) + 1))),
    fun j => boxInfl_nonneg hβ0 (Fp.P (2 * (j + 299999) + 1)),
    fun j l => hrow (2 * (j + 299999) + 1) (by omega) l,
    fun j => invariant_gibbs _ _, hU, fun G => ?_⟩
  exact hL G

#print axioms dobLaw_of_boxLaw

/-- **`CoarseViewInBox` implies `CoarseViewDobrushin`** at the same class `α`, with `Cₖ` the box
influence matrices (`dobLaw_of_boxLaw`; the reader clause is the same).

DERIVED: `2` the rank; `299999` the extent offset; `1` the successor writing the extent. -/
theorem coarseViewDobrushin_of_coarseViewInBox {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 lv : ℕ}
    {α : ℝ} {S : Set (MarginMono 2 τ r)} (hV : CoarseViewInBox Φ τ r m0 lv α S) :
    CoarseViewDobrushin Φ τ r m0 lv α S := by
  obtain ⟨β, Fp, 𝒰, χ, hlaw, hread⟩ := hV
  exact ⟨fun k j => boxInfl (β k) ((Fp k).P (2 * (j + 299999) + 1)), 𝒰, χ,
    hlaw.mono fun k hk => dobLaw_of_boxLaw hk, hread⟩

#print axioms coarseViewDobrushin_of_coarseViewInBox

end Box

/-! ## 4. Non-vacuity -/

section NonVacuity

/-- **The influence of the product Haar box vanishes**: at `β = 0` with the empty potential every
entry of `boxInfl` is `0`.

DERIVED: `0` the coupling and the entries; `2` the rank; `4`, `1` the dimension and the successor. -/
theorem boxInfl_zero (M : ℕ) (l k : WilsonHypercubic.Link 4 (M + 1)) :
    boxInfl 0 (zeroFam.P M) l k = 0 := by
  unfold boxInfl
  split_ifs
  · rfl
  · have hm : (zeroFam.P M).mix l k = 0 := by
      haveI : IsEmpty (zeroFam.P M).ι := inferInstanceAs (IsEmpty Empty)
      unfold LocalPot.mix
      rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
    rw [hm]
    simp [qfun]

#print axioms boxInfl_zero

/-- **The product Haar box state has a box law of every class `α ≥ 0`** along the principal filter at
`j₀`, read through the identity.

DERIVED: `0` the coupling and the sign of `α`; `2` the rank; `299999` the extent offset; `1` the
successor writing the extent. -/
theorem boxLaw_haar {α : ℝ} (hα0 : 0 ≤ α) (j0 : ℕ) :
    BoxLaw (wTorusState (potWeight 0 zeroFam) (2 * (j0 + 299999) + 1)) (ContinuousMap.id _) 0
      zeroFam (pure j0) α := by
  refine ⟨le_rfl, fun M _ l => ?_, inferInstance, fun G => ?_⟩
  · rw [Finset.sum_eq_zero fun k _ => boxInfl_zero M l k]
    exact hα0
  · rw [ContinuousMap.comp_id]
    exact tendsto_pure_nhds (fun j => wTorusState (potWeight 0 zeroFam) (2 * (j + 299999) + 1) G) j0

#print axioms boxLaw_haar

/-- **A witness of class `86/100`**: the product Haar box state has a Dobrushin law of TV class
`86/100` (`boxLaw_haar`, `dobLaw_of_boxLaw`).

DERIVED: `86/100` the class; `0` the coupling and the index; `2`, `299999`, `1` as in
`boxLaw_haar`. -/
theorem dobLaw_witness_86 :
    DobLaw (wTorusState (potWeight 0 zeroFam) (2 * (0 + 299999) + 1)) (ContinuousMap.id _)
      (pure 0) (86 / 100) (fun j => boxInfl 0 (zeroFam.P (2 * (j + 299999) + 1))) :=
  dobLaw_of_boxLaw (boxLaw_haar (by norm_num) 0)

#print axioms dobLaw_witness_86

end NonVacuity

end MassGap.ObserverEnergyMDob
