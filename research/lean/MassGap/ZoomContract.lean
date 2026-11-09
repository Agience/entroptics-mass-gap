import Mathlib
import MassGap.WindowFreq
import MassGap.RectWilson
import MassGap.WilsonReal

/-!
# MassGap.ZoomContract — the zoom-out read: monotone per site, contracting under a per-step gap

The author's mechanism: as the aperture zooms out, entropy decreases, because the average frequency rises and the
information clumps (motivation, not formalised); zoomed out far enough, the information goes to zero at the vanishing point. This module
formalises what of that is exactly true for the doubling defect
`D(β, w) = CouplingTower.windowCoupling N β w = 16 log ZR(side n) − log ZR(side 2n)`, `n = 2^w`.

* §1 The monotone read. The free energy per site `freeSite N β w = log ZR(2^w) / 16^w` is antitone in `w`
  for `w ≥ 1` (`freeSite_succ_le`: this is exactly `D ≥ 0`), lies in `[−32β, 0]` (`freeSite_bounds`), and so
  converges at every `β ≥ 0` (`tendsto_freeSite`, limit `zoomLimit N β`). The exact relation to `D` is
  `D(β, w) = 16^{w+1} (freeSite w − freeSite (w+1))` (`windowCoupling_eq`): `D` is the per-site entropy drop
  multiplied by the doubled volume. The per-volume read `D / 16^{w+1}` is summable with sum at most `32β`
  (`summable_perVolume`), so it tends to `0` at every `β ≥ 0` (`tendsto_perVolume`). Plainly, that is not
  `Vanishes N β`: `D` itself is the per-volume read times `16^{w+1}`, and its monotonicity in `w` does not follow
  from the definitions.
* §2 The contraction template (Dobrushin / strong data processing shape). If `d ≥ 0` and
  `d(w+1) ≤ η_w d(w)` from `w₀` on, with `η_w ≥ 0`, and `Σ (1 − η_w) = ∞`, then `d → 0`
  (`tendsto_zero_of_contraction`, through `η ≤ e^{η−1}`). A per-step gap `η_w ≤ 1 − δ` gives the divergence
  (`divergence_of_gap`). Convergent `Σ (1 − η)` alone forces nothing (`contraction_without_divergence`,
  counterexample).
* §3 The tree's contraction. In the basin the proved squaring `D(w+1) ≤ 250 D(w)²` is a contraction with
  `η(β, w) = 250 D(β, w)`; once one window `c ≥ 1` reads at most `1/1000`, every later `η ≤ 1/4`, the per-step
  gap is `3/4`, and the template gives `Vanishes N β` (`vanishes_of_basin_contraction`). This reproduces the
  strong anchor's mechanism (`StrongAnchor.vanishes_iff_seed`), and the remaining condition at general `β`
  is exactly that seed inequality.
* §4 Hypothetical block floor. `ReadPos.kernel_floor` gives only an existential κ > 0. The step from it to a
  contraction coefficient 1−κ with κ = e^{−2βB} is not in the tree; the form of κ and B_w ≥ w are assumed
  here. Under that assumption Σκ_w < ∞ (`floor_summable`), so the template's divergence fails
  (`floor_divergence_fails`). This shows the template does not apply; it does not show Vanishes fails.
* §5 Load tests. Free massive chain: from the window where `e^{−2^w θ} ≤ 1/3`, one doubling halves the read,
  and the template gives the read `→ 0` (`freeMassive_vanishes_by_contraction`). Free massless chain: the
  read is `log 2 − w log 2` (`freeWindow_massless`), its size grows at every step `w ≥ 1`, and no `η ≤ 1`
  contracts it (`freeMassless_no_contraction`). The link between this free-chain frequency and `FreqRead`
  is not formalised here.

DERIVED (module-wide): `16 = 2⁴` the copies and `2` the doubling; `32 = 2 · 16`, the action bound `2` of
`WilsonAction.wilsonDensity_le_two` times the `16 = 4 · 4` ordered direction pairs per site; `1` the least
window index and the step; `0` the signs and the limit. Inherited: `1/1000`, `250` the sharp seed and squaring
constant of `DoublingSharp` (through `CouplingTower.windowCoupling_succ_le`); `1/4 = 250 · 1/1000`; `3/4 = 1 − 1/4`.
Counterexample choices are labelled where they occur.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.ZoomContract

open Filter Topology Finset MeasureTheory
open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction MassGap.WilsonReal
  MassGap.RectWilson MassGap.CouplingTower MassGap.ZoomSelfScale MassGap.CompactGauge

variable {N : ℕ}

/-! ## 1. The monotone read: free energy per site -/

/-- The Wilson partition function is at most `1` at `β ≥ 0` (Haar probability, nonnegative action).
DERIVED: `1` the total mass; `0` the sign. -/
theorem partition_le_one (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β) :
    (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (MassGap.SUN.SU N)) β ≤ 1 := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  have hle : ∀ U : (wilsonSystem bd (wilsonDensity (N := N))).Config,
      (wilsonSystem bd (wilsonDensity (N := N))).boltz β U ≤ 1 := by
    intro U
    unfold System.boltz
    rw [Real.exp_le_one_iff]
    have := wilsonSystem_action_nonneg hN bd U
    nlinarith
  have hint : Integrable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    (integrable_const (1 : ℝ)).mono' (measurable_wilsonSystem_boltz bd β).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_of_nonneg (wilsonSystem_boltz_pos bd β U).le]; exact hle U)
  unfold System.partition
  calc ∫ U, (wilsonSystem bd (wilsonDensity (N := N))).boltz β U
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N)))
      ≤ ∫ _U, (1 : ℝ)
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
        integral_mono hint (integrable_const _) hle
    _ = 1 := by simp

/-- The Wilson partition function is at least `e^{−2β |plaquettes|}` at `β ≥ 0`.
DERIVED: `2` the action bound of `wilsonDensity_le_two`; `0` the sign. -/
theorem exp_le_partition (hN : N ≠ 0) {Lk Pq : Type} [Fintype Lk] [Fintype Pq]
    (bd : Pq → List (Lk × Bool)) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-(β * (2 * (Fintype.card Pq : ℝ))))
      ≤ (wilsonSystem bd (wilsonDensity (N := N))).partition (probHaar (MassGap.SUN.SU N)) β := by
  haveI : IsProbabilityMeasure ((wilsonSystem bd (wilsonDensity (N := N))).vol
      (probHaar (MassGap.SUN.SU N))) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Lk => probHaar (MassGap.SUN.SU N))))
  have hle : ∀ U : (wilsonSystem bd (wilsonDensity (N := N))).Config,
      (wilsonSystem bd (wilsonDensity (N := N))).boltz β U ≤ 1 := by
    intro U
    unfold System.boltz
    rw [Real.exp_le_one_iff]
    have := wilsonSystem_action_nonneg hN bd U
    nlinarith
  have hint : Integrable ((wilsonSystem bd (wilsonDensity (N := N))).boltz β)
      ((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) :=
    (integrable_const (1 : ℝ)).mono' (measurable_wilsonSystem_boltz bd β).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_of_nonneg (wilsonSystem_boltz_pos bd β U).le]; exact hle U)
  have hge : ∀ U : (wilsonSystem bd (wilsonDensity (N := N))).Config,
      Real.exp (-(β * (2 * (Fintype.card Pq : ℝ))))
        ≤ (wilsonSystem bd (wilsonDensity (N := N))).boltz β U := by
    intro U
    unfold System.boltz
    rw [Real.exp_le_exp]
    have := wilsonSystem_action_le hN bd U
    nlinarith
  unfold System.partition
  calc Real.exp (-(β * (2 * (Fintype.card Pq : ℝ))))
      = ∫ _U, Real.exp (-(β * (2 * (Fintype.card Pq : ℝ))))
        ∂((wilsonSystem bd (wilsonDensity (N := N))).vol (probHaar (MassGap.SUN.SU N))) := by simp
    _ ≤ _ := integral_mono (integrable_const _) hint hge

/-- The plaquette count of the side-`n` torus: `16 n⁴` ordered direction pairs and sites.
DERIVED: `16 = 4 · 4`, `4` the dimension. -/
theorem card_plaq (n : ℕ) : Fintype.card (RPlaq (fun _ : Fin 4 => n)) = 16 * n ^ 4 := by
  simp [RPlaq, RSite, Fintype.card_prod, Fintype.card_pi]

/-- **The free energy per site** at the window `w`: `log ZR(2^w) / 16^w`. DERIVED: `16 = 2⁴`, `2` the doubling. -/
def freeSite (N : ℕ) (β : ℝ) (w : ℕ) : ℝ := Real.log (ZR (fun _ => 2 ^ w) N β) / 16 ^ w

/-- **The doubling defect is the per-site entropy drop times the doubled volume**:
`D(β, w) = 16^{w+1} (freeSite w − freeSite (w+1))`. DERIVED: `16 = 2⁴`, `2` the doubling, `1` the step. -/
theorem windowCoupling_eq (N : ℕ) (β : ℝ) (w : ℕ) :
    windowCoupling N β w = 16 ^ (w + 1) * (freeSite N β w - freeSite N β (w + 1)) := by
  unfold windowCoupling defectW freeSite
  have e : (2 : ℕ) ^ (w + 1) = 2 * 2 ^ w := by ring
  rw [e]
  have h16 : (0 : ℝ) < 16 ^ w := by positivity
  field_simp
  ring

/-- **The per-site read lies in `[−32β, 0]`** at `β ≥ 0`. DERIVED: `32 = 2 · 16`; `0` the sign. -/
theorem freeSite_bounds (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) :
    -(32 * β) ≤ freeSite N β w ∧ freeSite N β w ≤ 0 := by
  have hZ := DeltaLengthTower.ZR_pos hN (fun _ : Fin 4 => 2 ^ w) β
  have h1 : ZR (fun _ => 2 ^ w) N β ≤ 1 := partition_le_one hN _ hβ
  have h0 := exp_le_partition (N := N) hN (rbd (fun _ : Fin 4 => 2 ^ w)) hβ
  rw [card_plaq] at h0
  change Real.exp _ ≤ ZR (fun _ => 2 ^ w) N β at h0
  have hlog : -(β * (2 * ((16 * (2 ^ w) ^ 4 : ℕ) : ℝ))) ≤ Real.log (ZR (fun _ => 2 ^ w) N β) := by
    have := Real.log_le_log (Real.exp_pos _) h0
    rwa [Real.log_exp] at this
  have e : ((16 * (2 ^ w) ^ 4 : ℕ) : ℝ) = 16 * 16 ^ w := by
    push_cast
    rw [← pow_mul, mul_comm w 4, pow_mul]
    norm_num
  rw [e] at hlog
  have h16 : (0 : ℝ) < 16 ^ w := by positivity
  unfold freeSite
  refine ⟨?_, div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hZ.le h1) h16.le⟩
  rw [le_div_iff₀ h16]
  linarith

/-- **Zoom-out lowers the entropy per site** (`w ≥ 1`): exactly `D ≥ 0`. DERIVED: `1` the least window and
the step; `0` the sign. -/
theorem freeSite_succ_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    freeSite N β (w + 1) ≤ freeSite N β w := by
  have hD := windowCoupling_nonneg hN hβ hw
  rw [windowCoupling_eq] at hD
  have h16 : (0 : ℝ) < 16 ^ (w + 1) := by positivity
  have : 0 ≤ freeSite N β w - freeSite N β (w + 1) := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  linarith

/-- **The zoom-out limit** `L(β)`: the infimum of the per-site read along `w ≥ 1`. DERIVED: `1` the least window. -/
def zoomLimit (N : ℕ) (β : ℝ) : ℝ := ⨅ k : ℕ, freeSite N β (k + 1)

/-- **The per-site read converges at every `β ≥ 0`** (monotone and bounded). DERIVED: `1` the least window. -/
theorem tendsto_freeSite (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (freeSite N β) atTop (𝓝 (zoomLimit N β)) := by
  have hanti : Antitone fun k : ℕ => freeSite N β (k + 1) :=
    antitone_nat_of_succ_le fun k => freeSite_succ_le hN hβ (by omega)
  have hbdd : BddBelow (Set.range fun k : ℕ => freeSite N β (k + 1)) :=
    ⟨-(32 * β), by rintro _ ⟨k, rfl⟩; exact (freeSite_bounds hN hβ _).1⟩
  exact (tendsto_add_atTop_iff_nat 1).mp (tendsto_atTop_ciInf hanti hbdd)

/-- **The per-volume read is summable**, with sum at most `32β`: `Σ_{w ≥ 1} D(β,w)/16^{w+1} ≤ 32β`.
DERIVED: `32 = 2 · 16`; `1`, `2` the shifts to `w ≥ 1`. -/
theorem summable_perVolume (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Summable (fun k : ℕ => windowCoupling N β (k + 1) / 16 ^ (k + 2)) ∧
      ∀ K, ∑ k ∈ range K, windowCoupling N β (k + 1) / 16 ^ (k + 2) ≤ 32 * β := by
  have e : ∀ k : ℕ, windowCoupling N β (k + 1) / 16 ^ (k + 2)
      = freeSite N β (k + 1) - freeSite N β (k + 1 + 1) := by
    intro k
    rw [windowCoupling_eq]
    have h16 : (0 : ℝ) < 16 ^ (k + 1 + 1) := by positivity
    rw [show k + 2 = k + 1 + 1 by ring]
    field_simp
  have hK : ∀ K, ∑ k ∈ range K, windowCoupling N β (k + 1) / 16 ^ (k + 2) ≤ 32 * β := by
    intro K
    simp_rw [e]
    rw [Finset.sum_range_sub' (fun k => freeSite N β (k + 1)) K]
    linarith [(freeSite_bounds hN hβ 1).2, (freeSite_bounds hN hβ (K + 1)).1]
  refine ⟨summable_of_sum_range_le (fun k => ?_) hK, hK⟩
  exact div_nonneg (windowCoupling_nonneg hN hβ (by omega)) (by positivity)

/-- **The per-volume read tends to `0` at every `β ≥ 0`.** Plainly, this is not `StrongAnchor.Vanishes`:
`D` is this read times `16^{w+2}`. DERIVED: `0` the limit; `1`, `2` the shifts; `16 = 2⁴` the copies of
the side-`n` torus in the side-`2n` torus. -/
theorem tendsto_perVolume (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun k : ℕ => windowCoupling N β (k + 1) / 16 ^ (k + 2)) atTop (𝓝 0) :=
  (summable_perVolume hN hβ).1.tendsto_atTop_zero

/-! ## 2. The contraction template -/

/-- **Contraction with divergent `Σ(1 − η)` drives the read to `0`** (strong data processing shape):
`d(w+1) ≤ η_w d(w)` from `w₀`, `d, η ≥ 0` from `w₀`, and `Σ_{i<K} (1 − η_{i+w₀}) → ∞`. The bound is
`d(K + w₀) ≤ d(w₀) e^{−Σ_{i<K}(1 − η_{i+w₀})}`, from `η ≤ e^{η − 1}`. DERIVED: `1` the step and the
exponent shift; `0` the signs and the limit. -/
theorem tendsto_zero_of_contraction {d η : ℕ → ℝ} (w₀ : ℕ) (hd : ∀ w, w₀ ≤ w → 0 ≤ d w)
    (hη : ∀ w, w₀ ≤ w → 0 ≤ η w) (hstep : ∀ w, w₀ ≤ w → d (w + 1) ≤ η w * d w)
    (hdiv : Tendsto (fun K => ∑ i ∈ range K, (1 - η (i + w₀))) atTop atTop) :
    Tendsto d atTop (𝓝 0) := by
  have hd0 := hd w₀ le_rfl
  have claim : ∀ K : ℕ, d (K + w₀) ≤ d w₀ * Real.exp (-∑ i ∈ range K, (1 - η (i + w₀))) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hηe : η (K + w₀) ≤ Real.exp (η (K + w₀) - 1) := by
        have := Real.add_one_le_exp (η (K + w₀) - 1); linarith
      have hpos : 0 ≤ d w₀ * Real.exp (-∑ i ∈ range K, (1 - η (i + w₀))) :=
        mul_nonneg hd0 (Real.exp_pos _).le
      rw [show K + 1 + w₀ = (K + w₀) + 1 by omega]
      calc d ((K + w₀) + 1) ≤ η (K + w₀) * d (K + w₀) := hstep _ (by omega)
        _ ≤ η (K + w₀) * (d w₀ * Real.exp (-∑ i ∈ range K, (1 - η (i + w₀)))) :=
            mul_le_mul_of_nonneg_left ih (hη _ (by omega))
        _ ≤ Real.exp (η (K + w₀) - 1) * (d w₀ * Real.exp (-∑ i ∈ range K, (1 - η (i + w₀)))) :=
            mul_le_mul_of_nonneg_right hηe hpos
        _ = d w₀ * Real.exp (-∑ i ∈ range (K + 1), (1 - η (i + w₀))) := by
            rw [Finset.sum_range_succ,
              show -(∑ i ∈ range K, (1 - η (i + w₀)) + (1 - η (K + w₀)))
                = -∑ i ∈ range K, (1 - η (i + w₀)) + (η (K + w₀) - 1) by ring, Real.exp_add]
            ring
  have hexp : Tendsto (fun K => d w₀ * Real.exp (-∑ i ∈ range K, (1 - η (i + w₀)))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv))
    simpa using (tendsto_const_nhds (x := d w₀)).mul this
  refine (tendsto_add_atTop_iff_nat w₀).mp ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
    (fun K => hd _ (by omega)) claim

/-- **A per-step gap gives the divergence**: `η_w ≤ 1 − δ` from `w₀`, `δ > 0`. DERIVED: `1` the unit; `0` the sign. -/
theorem divergence_of_gap {η : ℕ → ℝ} (w₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) (h : ∀ w, w₀ ≤ w → η w ≤ 1 - δ) :
    Tendsto (fun K => ∑ i ∈ range K, (1 - η (i + w₀))) atTop atTop := by
  refine tendsto_atTop_mono (fun K => ?_) (tendsto_natCast_atTop_atTop.atTop_mul_const hδ)
  calc (K : ℝ) * δ = ∑ _i ∈ range K, δ := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => by linarith [h (i + w₀) (by omega)]

/-- **Contraction without divergence forces nothing.** Counterexample choice: `d ≡ 1`, `η ≡ 1`. -/
theorem contraction_without_divergence :
    (∀ _w : ℕ, (1 : ℝ) ≤ 1 * 1) ∧ ¬ Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
  refine ⟨fun _ => by norm_num, fun h => ?_⟩
  have := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at this

/-! ## 3. The tree's contraction: the basin -/

/-- **The basin is a contraction with `η(β, w) = 250 D(β, w)` and per-step gap `3/4`**: one window `c ≥ 1`
at most `1/1000` gives `Vanishes N β` through the template. Inherited: `1/1000`, `250` of `DoublingSharp`;
`3/4 = 1 − 250/1000`. DERIVED: `1` the least window. Inherited: `1/1000` the sharp seed of
`DoublingSharp` (through `CouplingTower.windowCoupling_succ_le`). -/
theorem vanishes_of_basin_contraction (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {c : ℕ} (hc : 1 ≤ c)
    (h : windowCoupling N β c ≤ 1 / 1000) : StrongAnchor.Vanishes N β := by
  have hbasin : ∀ w, c ≤ w → windowCoupling N β w ≤ 1 / 1000 := by
    intro w hw
    induction w, hw using Nat.le_induction with
    | base => exact h
    | succ w hcw ih =>
      have := basin_contracts hN hβ (hc.trans hcw) ih
      have := windowCoupling_nonneg hN hβ (hc.trans hcw)
      linarith
  have hnn : ∀ w, c ≤ w → 0 ≤ windowCoupling N β w := fun w hw => windowCoupling_nonneg hN hβ (hc.trans hw)
  set η : ℕ → ℝ := fun w => 250 * windowCoupling N β w with hηdef
  have hη : ∀ w, c ≤ w → 0 ≤ η w := fun w hw => by
    have := hnn w hw
    simp only [hηdef]
    linarith
  have hstep : ∀ w, c ≤ w → windowCoupling N β (w + 1) ≤ η w * windowCoupling N β w := by
    intro w hw
    have := windowCoupling_succ_le hN hβ (hc.trans hw) (hbasin w hw)
    simp only [hηdef]
    nlinarith
  have hgap : ∀ w, c ≤ w → η w ≤ 1 - 3 / 4 := fun w hw => by
    have := hbasin w hw
    simp only [hηdef]
    linarith
  have hdiv := divergence_of_gap (η := η) c (by norm_num : (0 : ℝ) < 3 / 4) hgap
  exact tendsto_zero_of_contraction (d := windowCoupling N β) (η := η) c hnn hη hstep hdiv

/-- **The anchor through the contraction**: Restates the strong anchor: its seed comes from `strongAnchor` / `vanishes_iff_seed`, and the contraction template then reproves `Vanishes` from that seed; no new range of β is obtained.
DERIVED: `0` the lower end; `1` the least window. -/
theorem anchor_by_contraction (hN : N ≠ 0) :
    ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ → StrongAnchor.Vanishes N β := by
  obtain ⟨β₀, hβ₀, h⟩ := StrongAnchor.strongAnchor hN
  refine ⟨β₀, hβ₀, fun β h0 hlt => ?_⟩
  obtain ⟨c, hc, hlt'⟩ := (StrongAnchor.vanishes_iff_seed hN h0).mp (h β h0 hlt)
  exact vanishes_of_basin_contraction hN h0 hc hlt'.le

/-! ## 4. The block floor -/

/-- **The block floors are summable**: `Σ_w e^{−2β B_w} < ∞` at `β > 0` whenever `B_w ≥ w`.
DERIVED: `2` the action bound; `0` the sign. -/
theorem floor_summable {β : ℝ} (hβ : 0 < β) {B : ℕ → ℝ} (hB : ∀ w : ℕ, (w : ℝ) ≤ B w) :
    Summable (fun w => Real.exp (-(2 * β * B w))) := by
  refine Summable.of_nonneg_of_le (fun w => (Real.exp_pos _).le) (fun w => ?_)
    (summable_geometric_of_lt_one (Real.exp_pos (-(2 * β))).le
      (Real.exp_lt_one_iff.mpr (by linarith)))
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  nlinarith [hB w]

/-- **The floor contraction does not diverge**: with `η_w = 1 − e^{−2β B_w}`, `Σ (1 − η) < ∞`, so the
template does not apply. DERIVED: `2` the action bound; `0` the sign. -/
theorem floor_divergence_fails {β : ℝ} (hβ : 0 < β) {B : ℕ → ℝ} (hB : ∀ w : ℕ, (w : ℝ) ≤ B w) (w₀ : ℕ) :
    ¬ Tendsto (fun K => ∑ i ∈ range K, (1 - (1 - Real.exp (-(2 * β * B (i + w₀)))))) atTop atTop := by
  have hs := floor_summable hβ (B := fun i => B (i + w₀)) (fun i => by
    have := hB (i + w₀); push_cast at this; linarith)
  intro ht
  simp only [sub_sub_cancel] at ht
  exact not_tendsto_nhds_of_tendsto_atTop ht _ hs.hasSum.tendsto_sum_nat

/-! ## 5. Load tests: the free chain -/

/-- **Free massive chain: one doubling halves the read** once `e^{−2^w θ} ≤ 1/3`.
DERIVED: `1/2`, `1/3` from `2q²/(1−q²) ≤ q/(1+q) ⇔ 3q ≤ 1`; `2` the doubling. -/
theorem freeMassive_step {m : ℝ} (hm : 0 < m) {w : ℕ}
    (hq : Real.exp (-(((2 ^ w : ℕ) : ℝ) * WindowFreq.rate m)) ≤ 1 / 3) :
    WindowFreq.freeWindow m (w + 1) ≤ 1 / 2 * WindowFreq.freeWindow m w := by
  have hθ := WindowFreq.rate_pos_iff.mpr hm
  set x : ℝ := ((2 ^ w : ℕ) : ℝ) * WindowFreq.rate m with hx
  have hx0 : 0 < x := mul_pos (by positivity) hθ
  unfold WindowFreq.freeWindow
  rw [WindowFreq.defect_massive hm (by positivity), WindowFreq.defect_massive hm (by positivity)]
  have e : ((2 ^ (w + 1) : ℕ) : ℝ) * WindowFreq.rate m = 2 * x := by
    rw [hx]; push_cast; ring
  rw [e, ← hx]
  have hup := WindowFreq.casimirLaw_le (by linarith : 0 < 2 * x)
  have hlo := WindowFreq.le_casimirLaw hx0
  rw [WindowFreq.exp_two_mul_neg] at hup
  set q := Real.exp (-x)
  have hq0 : 0 < q := Real.exp_pos _
  have key : 2 * q ^ 2 / (1 - q ^ 2) ≤ 1 / 2 * (2 * q / (1 + q)) := by
    rw [div_le_iff₀ (by nlinarith), mul_comm]
    rw [show 1 / 2 * (2 * q / (1 + q)) * (1 - q ^ 2) = q * (1 - q) by field_simp; ring]
    nlinarith
  linarith

/-- **Free massive chain: the template drives the read to `0`** (per-step gap `1/2`).
DERIVED: `1/2`, `1/3` as in `freeMassive_step`; `0` the limit; `2` the doubling. -/
theorem freeMassive_vanishes_by_contraction {m : ℝ} (hm : 0 < m) :
    Tendsto (WindowFreq.freeWindow m) atTop (𝓝 0) := by
  have hθ := WindowFreq.rate_pos_iff.mpr hm
  have h2 : Tendsto (fun w : ℕ => ((2 ^ w : ℕ) : ℝ)) atTop atTop := by
    simpa using tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
  have hx : Tendsto (fun w : ℕ => ((2 ^ w : ℕ) : ℝ) * WindowFreq.rate m) atTop atTop :=
    h2.atTop_mul_const hθ
  have hq := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hx).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp hq
  have hnn : ∀ w, w₀ ≤ w → 0 ≤ WindowFreq.freeWindow m w := fun w _ => by
    unfold WindowFreq.freeWindow
    rw [WindowFreq.defect_massive hm (by positivity)]
    exact (WindowFreq.casimirLaw_pos (mul_pos (by positivity) hθ)).le
  have hdiv := divergence_of_gap (η := fun _ => (1 / 2 : ℝ)) w₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (fun _ _ => by norm_num)
  exact tendsto_zero_of_contraction (d := WindowFreq.freeWindow m) (η := fun _ => (1 / 2 : ℝ)) w₀ hnn
    (fun _ _ => by norm_num) (fun w hw => freeMassive_step hm (hw₀ w hw)) hdiv

/-- **Free massless chain in closed form along the windows**: `freeWindow 0 w = log 2 − w log 2`.
DERIVED: `0` the mass; `1` the shift; `2` the doubling. -/
theorem freeWindow_massless (w : ℕ) :
    WindowFreq.freeWindow 0 w = Real.log 2 - w * Real.log 2 := by
  have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  have h := WindowFreq.defect_massless (2 ^ w - 1)
  rw [Nat.sub_add_cancel h1] at h
  unfold WindowFreq.freeWindow
  rw [h, Nat.cast_sub h1]
  push_cast
  rw [sub_add_cancel, Real.log_pow]

/-- **Free massless chain: no contraction.** At every `w ≥ 1` the size of the read grows by `log 2`, so no
`η ≤ 1` gives `|D(w+1)| ≤ η |D(w)|`. DERIVED: `0` the mass; `1` the least window and the bound on `η`. -/
theorem freeMassless_no_contraction {w : ℕ} (hw : 1 ≤ w) {η : ℝ} (hη : η ≤ 1) :
    ¬ |WindowFreq.freeWindow 0 (w + 1)| ≤ η * |WindowFreq.freeWindow 0 w| := by
  rw [freeWindow_massless, freeWindow_massless]
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  rw [abs_of_nonpos (by push_cast; nlinarith), abs_of_nonpos (by nlinarith)]
  push_cast
  intro h
  have h0 : 0 ≤ -(Real.log 2 - w * Real.log 2) := by nlinarith
  nlinarith

end MassGap.ZoomContract

#print axioms MassGap.ZoomContract.partition_le_one
#print axioms MassGap.ZoomContract.exp_le_partition
#print axioms MassGap.ZoomContract.card_plaq
#print axioms MassGap.ZoomContract.windowCoupling_eq
#print axioms MassGap.ZoomContract.freeSite_bounds
#print axioms MassGap.ZoomContract.freeSite_succ_le
#print axioms MassGap.ZoomContract.tendsto_freeSite
#print axioms MassGap.ZoomContract.summable_perVolume
#print axioms MassGap.ZoomContract.tendsto_perVolume
#print axioms MassGap.ZoomContract.tendsto_zero_of_contraction
#print axioms MassGap.ZoomContract.divergence_of_gap
#print axioms MassGap.ZoomContract.contraction_without_divergence
#print axioms MassGap.ZoomContract.vanishes_of_basin_contraction
#print axioms MassGap.ZoomContract.anchor_by_contraction
#print axioms MassGap.ZoomContract.floor_summable
#print axioms MassGap.ZoomContract.floor_divergence_fails
#print axioms MassGap.ZoomContract.freeMassive_step
#print axioms MassGap.ZoomContract.freeMassive_vanishes_by_contraction
#print axioms MassGap.ZoomContract.freeWindow_massless
#print axioms MassGap.ZoomContract.freeMassless_no_contraction
