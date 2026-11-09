import Mathlib
import MassGap.ObserverEnergyGap
import MassGap.BoxDobrushinSpatial

noncomputable section

/-!
# MassGap.ObserverEnergyMClose — M for the energy density from one coarse view in a Dobrushin box

`ObserverEnergyGap.energy_M_of_coarseV_leak` gives M from statement V, whose rate is the dynamic
box rate `vRate q`. `BoxDobrushinSpatial.box_cov_spatial` gives covariance decay `θ^{d+1}` in the
`d`-step influence neighbourhood for every box weight whose Dobrushin row sums are `≤ α < θ`. This
module joins the two and isolates what remains as one proposition.

1. **M from any coarse rate** (`energy_M_of_rate_leak`): lattice clustering on a set `S ∋ ∅` at rate
   `0 ≤ ρ < 1` and the leakage inputs with `η² < (1 − ρ^{2k})(1 − ρr²)` give `FlowClusterAbs`.
2. **The box law of a state** (`BoxLaw`, `boxLaw_cov`): a state `ν` read through a coarse map `χ` is a
   limit of periodic box Gibbs states `wTorusState (potWeight β Fp)` whose influence matrix
   `boxInfl β (Fp.P M)` has row sums `≤ α`. Then every pair of bounded local readers `G_P`, `G_Q` with
   `G_P` outside the `d`-step influence neighbourhood of `G_Q` (eventually along the filter of
   extents) has `|ν(G_P G_Q ∘ χ) − ν(G_P ∘ χ) ν(G_Q ∘ χ)| ≤ 2B θ/(θ − α) · θ^{d+1} · a · 2B`.
3. **The identification that remains** (`CoarseViewInBox`): at every large fine step `k` the observer's
   coarse view `stateK k (· ∘ χₖ)` has a box law of row-sum class `α`, and on the pairs of `S` the
   reflected and shifted smeared products are `G_P ∘ χₖ`, `G_Q ∘ χₖ` for bounded local readers whose
   supports are `lv · n` influence steps apart at time separation `n`.
4. **The chain** (`latClusterRateOn_of_coarseViewInBox`, `energy_M_of_coarseViewInBox`,
   `energy_M_of_coarseViewInBox_79`): `CoarseViewInBox` gives `LatClusterRateOn` at `θ^{lv}` for every
   `θ ∈ (α, 1]`, hence M under `η² < (1 − θ^{2 lv k})(1 − ρr²)`. In the proved class (Lean
   `β ≤ 1/40`, local norm `≤ 1/16`, `α = 39/40`) at `θ = 79/80` the measured `η = 0.093` passes for
   every `lv · k ≥ 1` and `ρr² ≤ 13/20` (`eta_margin_79`).
5. **Non-vacuity of the box law** (`zeroFam`, `boxLaw_self`): the box Gibbs state itself, read through
   the identity, has a box law of class `39/40` along the principal filter of its own extent.

## Scope

`CoarseViewInBox` is a hypothesis here. It is the renormalisation content at one coarse scale: that
the coarse configuration's law, on the readers of `S`, is a box Gibbs law in a Dobrushin class. It is
not derived from the fine measure in this module or anywhere in the tree.
-/

namespace MassGap.ObserverEnergyMClose

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumCluster MassGap.ContinuumFlow
  MassGap.FlowCapstone MassGap.ObserverGapScale MassGap.ObserverClay MassGap.ObserverFlow
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyM MassGap.ObserverEnergyV
  MassGap.ObserverEnergyGap Filter
open MassGap.WeightedTorus (wTorusState wExpect)
open MassGap.LocalPotential (LocalPot LocalPotFam potWeight wtV)
open MassGap.PeriodicState (torusObs)
open MassGap.BoxDobrushinCoupling (OscLe boxInfl infl_wtV boxInfl_nonneg rowSum_box wtV_pos
  continuous_wtV)
open MassGap.BoxDobrushinSpatial (reach cov_spatial)
open scoped Topology

/-! ## 1. M from any coarse rate -/

section Rate

/-- **M for the energy density from lattice clustering at any coarse rate.** Clustering on a set
`S ∋ ∅` at rate `0 ≤ ρ < 1` (`LatClusterRateOn`) and the leakage inputs on `coarseSpan S` at time
`k ≥ 1` with `ρr² < 1` and `η² < (1 − (ρ^k)²)(1 − ρr²)` give `FlowClusterAbs`
(`flow_coarse_decay`, `gapAt_of_coarse_decay_leak`, `energy_M_iff_gap`).

DERIVED: `2` is the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `ρ`,
`k`, `L` and the rates; `1` the vacuum coefficient. -/
theorem energy_M_of_rate_leak {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcl : LatClusterRateOn two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 ρ S)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - (ρ ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L := by
  have hvac : (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0).vac ∈ coarseSpan S :=
    Finsupp.single_mem_supported ℝ (1 : ℝ) hS
  exact (energy_M_iff_gap hc0 hc n R D hD s hs hB τ hphys m0 hLw).mpr
    (gapAt_of_coarse_decay_leak _ (coarseSpan S) hvac hk hρ0 hρ1 hρr hη
      (flow_coarse_decay two_ne _ hB τ _ m0 S hcl) hL)

#print axioms energy_M_of_rate_leak

end Rate

/-! ## 2. The box law of a state and its covariance decay -/

section BoxLaw

/-- **The torus reading of an `ℤ⁴` observable as a continuous function of the box links.**

DERIVED: `4` is the spacetime dimension; `1` the successor writing the extent; `2` the rank. -/
def tObs (M : ℕ) (G : C(Cfg 2, ℝ)) :
    C(WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU 2, ℝ) :=
  ⟨torusObs M G, MassGap.HeatBath.continuous_torusObs M G⟩

/-- **A bounded local reader has oscillation `2B` on its torus support and `0` off it**
(`HeatBathLocal.readsNot_of_isLocalOn`).

DERIVED: `2` the two values compared and the rank; `1` the odd extent `2j + 1`; `0` the oscillation
off the support. -/
theorem oscLe_tObs {G : C(Cfg 2, ℝ)} {T : Finset ILink} (hG : IsLocalOn T ⇑G) {B : ℝ}
    (hB : ∀ U, |G U| ≤ B) (j : ℕ) :
    OscLe (tObs (2 * j + 1) G)
      (fun l => if l ∈ T.image (linkMod (2 * j + 1)) then 2 * B else 0) := by
  intro W l g
  show |torusObs (2 * j + 1) G (Function.update W l g) - torusObs (2 * j + 1) G W|
    ≤ (if l ∈ T.image (linkMod (2 * j + 1)) then 2 * B else 0)
  by_cases hl : l ∈ T.image (linkMod (2 * j + 1))
  · rw [if_pos hl]
    have h1 : |torusObs (2 * j + 1) G (Function.update W l g)| ≤ B := hB _
    have h2 : |torusObs (2 * j + 1) G W| ≤ B := hB _
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  · rw [if_neg hl, MassGap.HeatBathLocal.readsNot_of_isLocalOn hG j l hl W g, sub_self, abs_zero]

#print axioms oscLe_tObs

/-- A constant on a finset, summed over all links, is at most `a c` when the finset has `≤ a`
elements.

DERIVED: `0` the value off the finset and the sign of `c`. -/
theorem sum_indicator_le {Lk : Type} [Fintype Lk] [DecidableEq Lk] (T : Finset Lk) {c : ℝ}
    (hc : 0 ≤ c) {a : ℕ} (hT : T.card ≤ a) :
    ∑ l, (if l ∈ T then c else 0) ≤ a * c := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hc

#print axioms sum_indicator_le

/-- **The box law of a state read through a coarse map, in Dobrushin class `α`**: `β ≥ 0`; the box
influence matrix `boxInfl β (Fp.P M)` has row sums `≤ α` at every extent `M ≥ 1`; and along the
filter `𝒰` of extent indices the periodic box Gibbs states of `Wilson(β) × e^{Fp}` converge on every
continuous observable `G` to `ν(G ∘ χ)`. The class is the Dobrushin condition itself, not a coupling
window: any `β`, `Fp` meeting the row-sum bound qualify.

DERIVED: `2` is the rank; `299999` the extent offset of `ObserverEnergyV.boxSys`; `1` the successor
writing the extent and the least extent; `0` the sign of `β`. -/
def BoxLaw (ν : MassGap.DLRLimit.State (Cfg 2)) (χ : C(Cfg 2, Cfg 2)) (β : ℝ) (Fp : LocalPotFam 2)
    (𝒰 : Filter ℕ) (α : ℝ) : Prop :=
  0 ≤ β ∧ (∀ M : ℕ, 1 ≤ M → ∀ l, ∑ l', boxInfl β (Fp.P M) l l' ≤ α) ∧ 𝒰.NeBot ∧
    ∀ G : C(Cfg 2, ℝ), Tendsto (fun j => wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) G) 𝒰
      (𝓝 (ν (G.comp χ)))

/-- **`CoarseLawAt` is the box law of the step-`k` state**, with the coupling and norm windows of
`ObserverEnergyV.InBox` replaced by the row-sum class (forward direction at Lean `β ≤ 1/40`).

DERIVED: `1/40`, `1/16`, `39/40` as in `BoxDobrushinCoupling.rowSum_box`; `0` the sign of `β`; `1`
the least extent. -/
theorem boxLaw_of_coarseLawAt {k : ℕ} {β : ℝ} {Fp : LocalPotFam 2} {𝒰 : Filter ℕ}
    {χ : C(Cfg 2, Cfg 2)} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) (hn : ∀ M l, (Fp.P M).norm l ≤ 1 / 16)
    (hU : 𝒰.NeBot) (hL : CoarseLawAt k β Fp 𝒰 χ) :
    BoxLaw (stateK two_ne k) χ β Fp 𝒰 (39 / 40) :=
  ⟨hβ0, fun M hM l => rowSum_box hβ0 hβ hM (Fp.P M) l (hn M l), hU, hL⟩

#print axioms boxLaw_of_coarseLawAt

/-- **Covariance decay of a box law.** If `ν` has a box law of class `α` through `χ`, `α < θ ≤ 1`,
`G_P`, `G_Q` are local on `S_P`, `S_Q` with `|S_P| ≤ a` and `|G_P|, |G_Q| ≤ B`, and eventually along
the filter every torus link of `S_P` lies outside the `d`-step influence neighbourhood of the torus
image of `S_Q`, then `|ν(G_P G_Q ∘ χ) − ν(G_P ∘ χ) ν(G_Q ∘ χ)| ≤ 2B θ/(θ − α) · θ^{d+1} · a · 2B`
(`BoxDobrushinSpatial.cov_spatial` on each box, passed to the limit).

DERIVED: `2` the oscillation `2B` and the rank; `299999` the extent offset; `1` the cap beyond `d`,
the least extent and the bound on `θ`; `0` the signs. -/
theorem boxLaw_cov {ν : MassGap.DLRLimit.State (Cfg 2)} {χ : C(Cfg 2, Cfg 2)} {β : ℝ}
    {Fp : LocalPotFam 2} {𝒰 : Filter ℕ} {α : ℝ} (hv : BoxLaw ν χ β Fp 𝒰 α) {θ : ℝ}
    (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) {GP GQ : C(Cfg 2, ℝ)} {SP SQ : Finset ILink}
    (hlP : IsLocalOn SP ⇑GP) (hlQ : IsLocalOn SQ ⇑GQ) {a : ℕ} (hcP : SP.card ≤ a) {B : ℝ}
    (hB0 : 0 ≤ B) (hbP : ∀ U, |GP U| ≤ B) (hbQ : ∀ U, |GQ U| ≤ B) (d : ℕ)
    (hfar : ∀ᶠ j in 𝒰, ∀ l ∈ SP.image (linkMod (2 * (j + 299999) + 1)),
      l ∉ reach (boxInfl β (Fp.P (2 * (j + 299999) + 1)))
        (SQ.image (linkMod (2 * (j + 299999) + 1))) d) :
    |ν ((GP * GQ).comp χ) - ν (GP.comp χ) * ν (GQ.comp χ)|
      ≤ 2 * B * θ / (θ - α) * (θ ^ (d + 1) * (a * (2 * B))) := by
  obtain ⟨hβ0, hrow, hU, hL⟩ := hv
  haveI := hU
  have hθ0 : 0 ≤ θ := by linarith
  refine le_of_tendsto (((hL (GP * GQ)).sub ((hL GP).mul (hL GQ))).abs) ?_
  filter_upwards [hfar] with j hj
  have hM1 : 1 ≤ 2 * (j + 299999) + 1 := by omega
  have e1 : wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) (GP * GQ)
      = wExpect (wtV β (Fp.P (2 * (j + 299999) + 1)))
          (fun W => tObs (2 * (j + 299999) + 1) GP W * tObs (2 * (j + 299999) + 1) GQ W) := rfl
  have e2 : wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) GP
      = wExpect (wtV β (Fp.P (2 * (j + 299999) + 1))) (tObs (2 * (j + 299999) + 1) GP) := rfl
  have e3 : wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) GQ
      = wExpect (wtV β (Fp.P (2 * (j + 299999) + 1))) (tObs (2 * (j + 299999) + 1) GQ) := rfl
  show |wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) (GP * GQ)
      - wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) GP
        * wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) GQ| ≤ _
  rw [e1, e2, e3]
  have hvP := oscLe_tObs hlP hbP (j + 299999)
  have hvQ := oscLe_tObs hlQ hbQ (j + 299999)
  have hc := cov_spatial (wtV_pos β (Fp.P (2 * (j + 299999) + 1)))
    (continuous_wtV β (Fp.P (2 * (j + 299999) + 1)))
    (infl_wtV two_ne hβ0 (Fp.P (2 * (j + 299999) + 1)))
    (boxInfl_nonneg hβ0 (Fp.P (2 * (j + 299999) + 1))) (hrow _ hM1) hα0 hαθ hθ1 hvP hvQ
    (SQ.image (linkMod (2 * (j + 299999) + 1))) (by linarith : (0 : ℝ) ≤ 2 * B)
    (fun l hl => if_neg hl) (fun l => by split_ifs <;> linarith) d
    (fun l hl => hj l (by
      by_contra h
      exact hl (if_neg h)))
  refine hc.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 _))
    (div_nonneg (by nlinarith) (by linarith)))
  exact sum_indicator_le _ (by linarith) (Finset.card_image_le.trans hcP)

#print axioms boxLaw_cov

end BoxLaw

/-! ## 3. The identification that remains, and the chain to M -/

section Chain

/-- **The observer's coarse view lies in a Dobrushin box, on the pairs of `S`.** There are couplings
`βₖ`, potentials `Fpₖ`, filters `𝒰ₖ` of extents and coarse maps `χₖ` with:

* eventually in the fine step `k`, the step-`k` state read through `χₖ` has a box law of class `α`
  (`BoxLaw (stateK k) χₖ βₖ Fpₖ 𝒰ₖ α`);
* for every pair `P, Q ∈ S` a support bound `a` and a sup bound `Mb` such that at every time separation
  `n`, eventually in `k`, the reflected smeared product of `P` and the smeared product of `Q` shifted by
  `aₘ₀ n` are `G_P ∘ χₖ`, `G_Q ∘ χₖ` for readers local on `S_P`, `S_Q` (`|S_P| ≤ a`) with
  `|G_P|, |G_Q| ≤ Mb`, and eventually along `𝒰ₖ` the torus image of `S_P` lies outside the
  `lv · n`-step influence neighbourhood of the torus image of `S_Q`.

This is `ObserverEnergyGap.ObserverVOn` with the coupling window `InBox` (`β ≤ 1/20`, norm `≤ 1/16`)
replaced by the row-sum class `α`, the second-moment bounds by sup bounds, gauge invariance dropped, and
the `obsNb` level `⌊n/q⌋` replaced by `lv · n` influence steps.

DERIVED: `2` is the rank; `299999` the extent offset; `0` the reflection plane; `4` in `Fin 4` is the
spacetime dimension; `1` the successor writing the extent. -/
def CoarseViewInBox (Φ : Flow 2) (τ : Fin 4) (r : ℝ) (m0 lv : ℕ) (α : ℝ)
    (S : Set (MarginMono 2 τ r)) : Prop :=
  ∃ (β : ℕ → ℝ) (Fp : ℕ → LocalPotFam 2) (𝒰 : ℕ → Filter ℕ) (χ : ℕ → C(Cfg 2, Cfg 2)),
    (∀ᶠ k in atTop, BoxLaw (stateK two_ne k) (χ k) (β k) (Fp k) (𝒰 k) α) ∧
    ∀ P ∈ S, ∀ Q ∈ S, ∃ (a : ℕ) (Mb : ℝ), ∀ n : ℕ, ∀ᶠ k in atTop,
      ∃ (GP GQ : C(Cfg 2, ℝ)) (SP SQ : Finset ILink),
        IsLocalOn SP ⇑GP ∧ IsLocalOn SQ ⇑GQ ∧ SP.card ≤ a ∧
        (∀ U, |GP U| ≤ Mb) ∧ (∀ U, |GQ U| ≤ Mb) ∧
        LatticeReflection.ireflObs τ 0 (prodSmear (dySpacing 2 k) (Φ.mono k P.1)) = GP.comp (χ k) ∧
        prodSmear (dySpacing 2 k) (Φ.mono k (Mono.shift (timeVec 2 m0 τ n) Q.1)) = GQ.comp (χ k) ∧
        ∀ᶠ j in 𝒰 k, ∀ l ∈ SP.image (linkMod (2 * (j + 299999) + 1)),
          l ∉ reach (boxInfl (β k) ((Fp k).P (2 * (j + 299999) + 1)))
            (SQ.image (linkMod (2 * (j + 299999) + 1))) (lv * n)

/-- **The coarse view in a Dobrushin box gives lattice clustering at `θ^{lv}`** for every
`θ ∈ (α, 1]`, with constant `2B θ/(θ − α) · θ · a · 2B`, `B = max(Mb, 0)` (`boxLaw_cov` at
`d = lv · n`; `latSF_pair_eq`, `prodSmear_empty`, `FlowCapstone.mono_empty`).

DERIVED: `2` the rank and the oscillation `2B`; `0` the reflection plane and the signs; `1` the unit
observable and the cap beyond `d`. -/
theorem latClusterRateOn_of_coarseViewInBox {Φ : Flow 2} {τ : Fin 4} {r : ℝ} {m0 lv : ℕ} {α : ℝ}
    {S : Set (MarginMono 2 τ r)} (hV : CoarseViewInBox Φ τ r m0 lv α S) {θ : ℝ} (hα0 : 0 ≤ α)
    (hαθ : α < θ) (hθ1 : θ ≤ 1) :
    LatClusterRateOn two_ne Φ τ r m0 (θ ^ lv) S := by
  obtain ⟨β, Fp, 𝒰, χ, hlaw, hread⟩ := hV
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
  have hb := boxLaw_cov hk hα0 hαθ hθ1 hlP hlQ hcP (le_max_right Mb 0)
    (fun U => (hbP U).trans (le_max_left _ _)) (fun U => (hbQ U).trans (le_max_left _ _))
    (lv * n) hfar
  refine hb.trans (le_of_eq ?_)
  rw [pow_succ, pow_mul]
  ring

#print axioms latClusterRateOn_of_coarseViewInBox

/-- **M for the energy density from the coarse view in a Dobrushin box.** `CoarseViewInBox` of class
`α` on a set `S ∋ ∅` with `lv ≥ 1` influence steps per time step, any `θ ∈ (α, 1)`, and the leakage
inputs on `coarseSpan S` at time `k ≥ 1` with `ρr² < 1` and `η² < (1 − θ^{2 lv k})(1 − ρr²)` give
`FlowClusterAbs` (`latClusterRateOn_of_coarseViewInBox`, `energy_M_of_rate_leak`).

DERIVED: `2` is the rank and the form's degree; `1/6` the dominance bound; `0` and `1` bracket `θ`,
`lv`, `k`, `L` and the rates. -/
theorem energy_M_of_coarseViewInBox {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv) {α θ : ℝ}
    (hV : CoarseViewInBox (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv α S)
    (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ < 1)
    {k : ℕ} (hk : 0 < k) {ρr η : ℝ} (hρr : ρr ^ 2 < 1)
    (hη : η ^ 2 < (1 - ((θ ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2))
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr η)
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L := by
  have hθ0 : 0 ≤ θ := by linarith
  exact energy_M_of_rate_leak hc0 hc n R D hD s hs hB τ hphys m0 S hS (pow_nonneg hθ0 lv)
    (pow_lt_one₀ hθ0 hθ1 hlv.ne') (latClusterRateOn_of_coarseViewInBox hV hα0 hαθ hθ1.le) hk hρr
    hη hL hLw

#print axioms energy_M_of_coarseViewInBox

/-- **The η margin at the proved rate.** At `θ = 79/80` and `lv · k ≥ 1`, the measured leakage
`η = 0.093` satisfies `η² < (1 − θ^{2 lv k})(1 − ρr²)` whenever `ρr² ≤ 13/20`: the left side is
`0.008649`, the right side is at least `(159/6400)(7/20) = 0.0086953`.

DERIVED: `79/80` the rate of `BoxDobrushinSpatial.box_cov_spatial_79`; `93/1000` the leakage
`η = 0.093` measured at one coarse step in the two-operator basis; `13/20` the largest `ρr²` kept, `7/20 = 1 − 13/20`;
`159/6400 = 1 − (79/80)²`; `1` the least `lv · k`; `2` the form's degree. -/
theorem eta_margin_79 {lv k : ℕ} (hlk : 1 ≤ lv * k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20) :
    (93 / 1000 : ℝ) ^ 2 < (1 - (((79 / 80 : ℝ) ^ lv) ^ k) ^ 2) * (1 - ρr ^ 2) := by
  have h1 : ((79 / 80 : ℝ) ^ lv) ^ k ≤ 79 / 80 := by
    rw [← pow_mul]
    calc (79 / 80 : ℝ) ^ (lv * k) ≤ (79 / 80) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hlk
      _ = 79 / 80 := pow_one _
  have h0 : 0 ≤ ((79 / 80 : ℝ) ^ lv) ^ k := by positivity
  have h2 : (((79 / 80 : ℝ) ^ lv) ^ k) ^ 2 ≤ (79 / 80) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hρr), sq_nonneg ρr]

#print axioms eta_margin_79

/-- **M from the coarse view in the proved Dobrushin box, at the measured leakage.** If the coarse
view lies in the box of Lean `β ≤ 1/40` and local norm `≤ 1/16` (row sums `≤ 39/40`,
`BoxDobrushinCoupling.rowSum_box`) with `lv ≥ 1`, and the leakage inputs hold at time `k ≥ 1` with
`η = 0.093` and `ρr² ≤ 13/20`, then `FlowClusterAbs` holds (`energy_M_of_coarseViewInBox` at
`θ = 79/80`, `eta_margin_79`).

DERIVED: `39/40`, `79/80`, `93/1000`, `13/20` as in `eta_margin_79` and `rowSum_box`; `2` the rank;
`1/6` the dominance bound; `0` and `1` bracket `lv`, `k`, `L`. -/
theorem energy_M_of_coarseViewInBox_79 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    (D : Set (LField (MassGap.SUN.SU 2)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU 2) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), s k (O.refl τ) = s k O)
    (hB : UniformBoundF two_ne (obsEnergyOn c hc0 hc n R D hD s hs)) (τ : Fin 4) {r : ℝ}
    (hphys : (obsEnergyOn c hc0 hc n R D hD s hs).PhysRange r) (m0 : ℕ)
    (S : Set (MarginMono 2 τ r)) (hS : emptyMargin 2 τ r ∈ S) {lv : ℕ} (hlv : 0 < lv)
    (hV : CoarseViewInBox (obsEnergyOn c hc0 hc n R D hD s hs) τ r m0 lv (39 / 40) S)
    {k : ℕ} (hk : 0 < k) {ρr : ℝ} (hρr : ρr ^ 2 ≤ 13 / 20)
    (hL : LeakInputs (energyTransfer hc0 hc n R D hD s hs hB τ hphys m0) (coarseSpan S) k ρr
      (93 / 1000))
    {L : ℝ} (hLw : 0 < L) :
    FlowClusterAbs two_ne (obsEnergyOn c hc0 hc n R D hD s hs) τ r L :=
  energy_M_of_coarseViewInBox hc0 hc n R D hD s hs hB τ hphys m0 S hS hlv hV (by norm_num)
    (by norm_num : (39 / 40 : ℝ) < 79 / 80) (by norm_num) hk (by linarith)
    (eta_margin_79 (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hlv.ne' hk.ne')) hρr) hL hLw

#print axioms energy_M_of_coarseViewInBox_79

end Chain

/-! ## 4. Non-vacuity of the box law -/

section NonVacuity

/-- **The zero potential at extent `M`**: no terms.

DERIVED: `2` is the rank. -/
def zeroPot (M : ℕ) : LocalPot 2 M where
  ι := Empty
  supp X := X.elim
  V X := X.elim
  v X := X.elim
  cont X := X.elim
  reads X := X.elim
  bound X := X.elim

/-- **The zero potential family.**

DERIVED: `2` is the rank. -/
def zeroFam : LocalPotFam 2 where
  P M := zeroPot M
  gauge _ X := X.elim

/-- The zero family has local norm `0 ≤ 1/16`.

DERIVED: `1/16` the norm bound of `rowSum_box`. -/
theorem zeroFam_norm (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    (zeroFam.P M).norm l ≤ 1 / 16 := by
  haveI : IsEmpty (zeroFam.P M).ι := inferInstanceAs (IsEmpty Empty)
  have h : (zeroFam.P M).norm l = 0 := by
    unfold LocalPot.norm
    rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
  rw [h]
  norm_num

#print axioms zeroFam_norm

/-- **The box law is not vacuous.** The periodic box Gibbs state of `Wilson(β) × e^{Fp}` at the
extent of index `j₀`, read through the identity, has a box law of class `39/40` along the principal
filter at `j₀`, for every `0 ≤ β ≤ 1/40` and every `Fp` of local norm `≤ 1/16`: the fine measure is
itself in the box class and the observer step is the identity.

DERIVED: `1/40`, `1/16`, `39/40` as in `rowSum_box`; `2` the rank; `299999` the extent offset; `1`
the successor writing the extent. -/
theorem boxLaw_self {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 40) {Fp : LocalPotFam 2}
    (hn : ∀ M l, (Fp.P M).norm l ≤ 1 / 16) (j0 : ℕ) :
    BoxLaw (wTorusState (potWeight β Fp) (2 * (j0 + 299999) + 1)) (ContinuousMap.id _) β Fp
      (pure j0) (39 / 40) := by
  refine ⟨hβ0, fun M hM l => rowSum_box hβ0 hβ hM (Fp.P M) l (hn M l), inferInstance,
    fun G => ?_⟩
  rw [ContinuousMap.comp_id]
  exact tendsto_pure_nhds (fun j => wTorusState (potWeight β Fp) (2 * (j + 299999) + 1) G) j0

#print axioms boxLaw_self

/-- **A witness**: the pure Wilson box state at Lean `β = 1/40` has a box law of class `39/40`.

DERIVED: `1/40` the coupling; `39/40`, `299999`, `2`, `1` as in `boxLaw_self`; `0` the index. -/
theorem boxLaw_witness :
    BoxLaw (wTorusState (potWeight (1 / 40) zeroFam) (2 * (0 + 299999) + 1))
      (ContinuousMap.id _) (1 / 40) zeroFam (pure 0) (39 / 40) :=
  boxLaw_self (by norm_num) le_rfl zeroFam_norm 0

#print axioms boxLaw_witness

end NonVacuity

end MassGap.ObserverEnergyMClose
