import Mathlib
import MassGap.FlowClusterG
import MassGap.DoublingWilsonG
import MassGap.CentreSectorSeedN
import MassGap.ApertureGap
import MassGap.ApertureOne
import MassGap.ApertureBridge
import MassGap.RelativeGap

/-!
# MassGap.ObserverTheory — the author's chain, from the cost of a flux edge to the run seed of every `G`

The chain in the author's words: the substrate is the lattice Wilson measure, refining with the zoom; the aperture is a
fixed physical length, fixed relative to the observer; the observer reads it. A flux edge that spans the aperture
costs `σ` per unit of physical length, at every zoom; so what the aperture holds about anything beyond it is
suppressed like `e^{−σ · length}`; so the reading forgets geometrically; so there is a gap. This module states the
binding step on the real objects (the Wilson torus of `G`), proves every implication from it to `WindowG.RunSeedG G`
and the observer's gap, proves that the binding step in its weakest consumed form is equivalent to the run seed,
tests it, and splits it at `SU(N)` into the two statements on which the proof stops.

## 1. The binding statement (defined)

`a = aRunG G β` is the spacing; the torus of side `n` has physical side `n a`. `defectWG G 4 (wilsonDensityG G) β n
= 16 log Z(n) − log Z(2n)` is what the side-`2n` torus holds beyond sixteen independent side-`n` tori: the
excitations that span the side-`n` torus.

* `EdgeCostG G σ A ℓ₀`: `σ > 0` and, eventually in `β`, at every power-of-two side `n ≥ 2` of physical length
  `n a ≥ ℓ₀`, `defectWG ≤ A e^{−σ n a}`. Every spanning edge longer than the cutoff `ℓ₀` costs `σ` per physical
  length, uniformly in the zoom. The cutoff is needed: on boxes far below the correlation length the finite-size
  part is Coulomb-like and the defect grows like `κ log β` (`EnergySeed.defectW_log_growth`), so the bound at every
  side, without a cutoff, is expected false (`not_edgeCostG_of_coulomb` is the conditional form).
* `BindingG G σ A`: the same bound, asked only at sides of physical length in `[2ℓ, 5ℓ]` and only for arbitrarily
  large `ℓ` (frequently in `ℓ`). `bindingG_of_edgeCostG` (at `ℓ ≥ ℓ₀/2`).

## 2. The chain (proved)

* `runSeedG_of_bindingG`: `BindingG G σ A ⇒ RunSeedG G` (the side `nPG G ℓ β` lies in the window,
  `DoublingClay2.nP_bounds`; `ℓ` is taken with `max A 0 · e^{−2σℓ} ≤ 1/1000`).
* `defectWG_edge`, `edgeCostG_of_runSeedG`: the converse, `RunSeedG G ⇒ EdgeCostG G (log 4 / C) (1/250) C` for the
  seed's own `C` (`DoublingSharp.iterate_sharp` at the Wilson facts `DoublingWilsonG.factRepG`: from a seed at side
  `n₀`, the side `2ᵏ n₀` has defect at most `(1/4)^{2ᵏ}/250`, and `2ᵏ ≥ n a / C`); `bindingG_of_runSeedG`.
* `runSeedG_iff_edgeCost`: `RunSeedG G ↔ ∃ σ A ℓ₀, 0 < ℓ₀ ∧ EdgeCostG G σ A ℓ₀`; `runSeedG_iff_binding`:
  `RunSeedG G ↔ ∃ σ A, BindingG G σ A`. So both forms are exactly as weak as the downstream needs: they are the run
  seed read as an edge cost. Neither is more basic than the run seed.
* `observerGapG_of_bindingG`, `observerGapG_of_edgeCostG`: the observer's gap input of
  `ClayGFinal.clayStatementAtG_GS_noNT` (`FlowClusterG.observerGapG_of_runSeedG`).

## 3. The hypothesis on the hidden modes: the `SU(N)` split (defined; both directions proved)

`CentreSectorSeedN` splits each corner step of the `SU(N)` defect over the `N³` centre sectors of the slice.

* `FluxCostAt N σ A ℓ` (the flux edges): at every side in the window, every step's flux share `fluxShareN`, the
  share of the trace carried by non-zero electric flux (a flux edge winding the torus), is at most `A e^{−σ n a}`.
* `HiddenCostAt N σ A ℓ` (the hidden modes): at every side in the window, every step's zero-flux doubling defect
  `trivialDefectN` is at most `A e^{−σ n a}`. The zero-flux sector carries no centre charge: no centre twist reads
  it. (Read as the closed loops; that reading is not a declaration.)
* `BindingSU N σ A`: `σ > 0` and, frequently in `ℓ`, both.
* `runSeed_of_bindingSU`: `BindingSU N σ A ⇒ WDeltaRun.RunSeed N` (`CentreSectorSeedN.defectW_le_of_sectorsN`);
  `runSeedG_of_bindingSU`: hence `RunSeedG (SU N)` (`WindowG.runSeedG_SU`), `N ≥ 2`.
* `defectW_edge`, `bindingSU_of_runSeed`: the converse, `RunSeed N ⇒ BindingSU N (log 4 / C) (max(N³/2, 2)/250)`
  (`CentreSectorSeedN.sectors_of_defectWN` at `δ = e^{−σ n a}/250`, at the `ℓ` with `(4 + N⁶) δ ≤ 2`);
  `runSeed_iff_bindingSU`: `RunSeed N ↔ ∃ σ A, BindingSU N σ A`.

## 4. Tests (proved)

* On the real `SU(2)` objects, conditionally: `not_bindingG_of_coulomb`, `not_edgeCostG_of_coulomb`. A Coulomb
  finite-size part `κ/x ≤ finiteSize 2 n x` (the Gaussian count of a massless spectrum, `ApertureOne`) excludes
  `BindingG (SU 2) σ A` and `EdgeCostG (SU 2) σ A ℓ₀` at every `σ, A, ℓ₀` (`ApertureOne.not_physDefect_of_coulomb`).
* `EdgeCostModel D σ A`, the model form of the binding statement: `σ > 0` and, frequently in the physical length
  `L`, eventually in the zoom `K`, `D L K ≤ A e^{−σL}`.
* `gaussD_lower_zoom`: the 4D Gaussian box defect of `ApertureGap` is at least `e^{−2π} e^{−ML}` at every `L ≥ 1` and
  every zoom `K ≥ 1` (`ApertureGap.gaussD_lower` is the case `K = 1`).
* `photon_not_edgeCost` (the 4D massless Gaussian: a free-field stand-in for the weak-coupling photon; one-direction
  cycle doubling, Dirichlet modes): `¬ EdgeCostModel (gaussD 0) σ A` for every `σ`, `A`. `massive_not_edgeCost_above`: the massive field fails at every `σ > M`; `massive_edgeCost`: it satisfies the
  model form at `σ = λM`, `λ ∈ (0, 1)`; `ym2_edgeCost`: 2D `SU(2)` by characters satisfies it at every `σ > 0`.
  The hypothesis separates the massless and the confining unit models.

## 5. The forgetting margin (Entroptics) and the open link (proved; finite form)

The observer's transfer at the aperture is the propagator of Entroptics §9; its forgetting margin on mean-zero
readings is the rate `ρ` of `TransferGap.GapAt`. "Margin `< 1` ⇒ the reading forgets" is the closed link
`GapAt ⇒ clustering` (`FlowClusterG.lattice_clusterG`, `WindowG.gapAt_physical_of_fixedWindowDecayG`). In lattice
units the per-step margin is `e^{−m a} → 1` as `a → 0` (`stepMargin_tendsto_one`), so what must hold is the rate per
physical length, `−log(margin)/a ≥ m > 0`, across zooms, for the full transfer including the hidden modes.

The Weyl step of `Entroptics.weyl_top_of_rayleigh` / `attenuation_weyl_certified` (Entroptics library) has this
analogue in the bilinear `L²(π)` form of `GapL2` (restated, not imported: `MassGap`'s lakefile does not require the
Entroptics library):

* `PertBound π E ε`: `|⟨f, E g⟩_π| ≤ ε ‖f‖ ‖g‖` for mean-zero `f, g` (the perturbation is `ε`-close in the
  bilinear form on mean-zero readings).
* `corr_add`: `Corr π K₀ r₀` and `PertBound π E ε` give `Corr π (K₀ + E) (r₀ + ε)`: the margin moves by at most the
  perturbation. `maxCorr_add_le`: `maxCorr π (K₀ + E) ≤ r₀ + ε`.
* `rate_of_pert`: at a slab of physical thickness `τ > 0`, `r₀ + ε ≤ e^{−mτ}` gives the rate
  `m ≤ −log(maxCorr)/τ`.
* `pert_ge_one_of_kH`: for the hidden-mode kernel `kH` of `RelativeGap`, no split `kH = K₀ + E` with `Corr K₀ r₀`
  and `PertBound E ε` certifies a margin below `1`: `1 ≤ r₀ + ε`. With `RelativeGap.hidden_coarse` (correlation `0`
  on the aperture's readings), the aperture's margin does not bound the full transfer.

So the Weyl reduction carries a margin from the finite aperture operator `K₀` (the transfer restricted to the
aperture's readings) to the full slab transfer exactly when the hidden part is `ε`-close with
`r₀ + ε ≤ e^{−mτ} < 1`, at the slab of fixed physical thickness `τ` and with the same `ε` at every zoom. At `SU(N)` that
`ε`-closeness is the content of `HiddenCostAt` (the zero-flux sector, which the centre readings do not see).

## Where the proof stops

`HiddenCostAt` and `FluxCostAt` are not proved for the Wilson measure of any `N`, at any `σ > 0`, by any declaration
in this tree. `BindingSU` is the named statement, and `runSeed_iff_bindingSU` shows `BindingSU ⇔ RunSeed N`: the
split restates the run seed sector by sector; it does not reduce it to something weaker. `EdgeCostG` without a cutoff
(at every side down to the lattice scale) is expected false at small sides, where the finite-size part is
Coulomb-like (`EnergySeed.defectW_log_growth`, `not_edgeCostG_of_coulomb`); the cutoff `ℓ₀` is part of the statement.
Of the author's arguments:

* finite centre (`NonAbelianForget.center_SU_finite`; `U(1)`: `center_U1_infinite`) supplies the split itself —
  `N³` sectors, a finite sum — and no bound on either part;
* non-abelian binding (`σ > 0`) is `FluxCostAt` read in 't Hooft's electric-flux form; the tree's area-law statement
  `EdgeCost.StringScalingAt` is on Wilson loops, and no declaration links it to `fluxShareN`;
* finite information and the aperture fixed relative to the observer give the observer side only
  (`RelativeGap.CorrOn.anti`: the coarse correlation is at most the fine one), the converse fails
  (`RelativeGap.hidden_maxCorr`, `pert_ge_one_of_kH`), so they do not supply `HiddenCostAt`;
* the fixed diffraction length (`ApertureGap.FixedDiffraction`) is a strengthening of `BindingG` at `SU(2)`, not a
  supply of it.

DERIVED (module-wide): `4` the dimension; `16 = 2⁴`; `2` and `5` the window `[2ℓ, 5ℓ]` of `nPG`
(`DoublingClay2.nP_bounds`: `nP a ≤ 4ℓ + 2a ≤ 5ℓ` at `a ≤ ℓ/2`; `nP a ≥ 2ℓ` from the ceiling); `1/1000` the seed
threshold of `RunSeedG`; `250`, `1/4` from `DoublingSharp.iterate_sharp`, so `log 4` the rate per seed length;
`1/80000` the sector thresholds of `CentreSectorSeedN.defectW_le_of_sectorsN`; `N³/2`, `2`, `4 + N⁶` from
`CentreSectorSeedN.sectors_of_defectWN`, and `500 = 2 · 250`; `2π` from `ApertureGap.freq_low_le`;
`1/2`, `1/4` the kernel and the state of `RelativeGap.kH`.
-/

noncomputable section

namespace MassGap.ObserverTheory

open Filter MassGap MassGap.ClayTreeG MassGap.PeriodicReduceG MassGap.GaugeGroup MassGap.WindowG

/-! ## 1–2. The binding statement and the chain, for every `G` -/

section Chain

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]

/-- **Every spanning edge longer than the cutoff `ℓ₀` costs `σ` per physical length, uniformly in the zoom.** -/
def EdgeCostG (σ A ℓ₀ : ℝ) : Prop :=
  0 < σ ∧ ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    ℓ₀ ≤ (n : ℝ) * GaugeRunning.aRunG G β →
    TorusDoubling.defectWG G 4 (wilsonDensityG G) β n
      ≤ A * Real.exp (-(σ * ((n : ℝ) * GaugeRunning.aRunG G β)))

/-- **The binding statement**: the edge-cost bound at the sides of physical length in `[2ℓ, 5ℓ]`, for arbitrarily
large `ℓ`.

DERIVED: `2` and `5` the window `[2ℓ, 5ℓ]` of `nPG` (`DoublingClay2.nP_bounds`: `nP a ≤ 4ℓ + 2a ≤ 5ℓ` at
`a ≤ ℓ/2`); `4` the dimension. -/
def BindingG (σ A : ℝ) : Prop :=
  0 < σ ∧ ∃ᶠ ℓ in atTop, ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * GaugeRunning.aRunG G β → (n : ℝ) * GaugeRunning.aRunG G β ≤ 5 * ℓ →
    TorusDoubling.defectWG G 4 (wilsonDensityG G) β n
      ≤ A * Real.exp (-(σ * ((n : ℝ) * GaugeRunning.aRunG G β)))

theorem bindingG_of_edgeCostG {σ A ℓ₀ : ℝ} (h : EdgeCostG G σ A ℓ₀) : BindingG G σ A := by
  refine ⟨h.1, Eventually.frequently ?_⟩
  filter_upwards [eventually_ge_atTop (ℓ₀ / 2)] with ℓ hℓ
  exact h.2.mono fun _ hβ n hp h2 hlo _ => hβ n hp h2 (by linarith)

/-- Eventually in `ℓ`, `ℓ > 0` and `c e^{−σ' ℓ} ≤ ε`. -/
theorem eventually_small {σ' c ε : ℝ} (hσ : 0 < σ') (hε : 0 < ε) :
    ∀ᶠ ℓ : ℝ in atTop, 0 < ℓ ∧ c * Real.exp (-(σ' * ℓ)) ≤ ε := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), ApertureGap.eventually_poly_exp_le hσ c 0 hε] with ℓ h0 h
  exact ⟨h0, by simpa using h⟩

/-- `A e^{−σx} ≤ max A 0 · e^{−σy}` for `y ≤ x`, `σ ≥ 0`. -/
theorem edge_le {A σ x y : ℝ} (hσ : 0 ≤ σ) (hxy : y ≤ x) :
    A * Real.exp (-(σ * x)) ≤ max A 0 * Real.exp (-(σ * y)) := by
  have h1 : A * Real.exp (-(σ * x)) ≤ max A 0 * Real.exp (-(σ * x)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have h2 : Real.exp (-(σ * x)) ≤ Real.exp (-(σ * y)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hxy hσ])
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (le_max_right _ _))

/-- The power-of-two side `nPG G ℓ β` has physical length at least `2ℓ`. -/
theorem nPG_lower {ℓ β : ℝ} (hβ : 0 < β) :
    2 * ℓ ≤ (nPG G ℓ β : ℝ) * GaugeRunning.aRunG G β := by
  have ha : 0 < GaugeRunning.aRunG G β := aRunG_pos G hβ
  have h1 : ⌈2 * ℓ / GaugeRunning.aRunG G β⌉₊ ≤ nPG G ℓ β := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 * ℓ / GaugeRunning.aRunG G β ≤ (nPG G ℓ β : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast h1)
  rwa [div_le_iff₀ ha] at h2

/-- **The binding statement gives the run seed of `G`.** -/
theorem runSeedG_of_bindingG {σ A : ℝ} (h : BindingG G σ A) : RunSeedG G := by
  obtain ⟨hσ, hfr⟩ := h
  have hσ2 : 0 < 2 * σ := by linarith
  obtain ⟨ℓ, hβev, hℓ, hsmall⟩ :=
    (hfr.and_eventually (eventually_small (c := max A 0) hσ2 (by norm_num : (0 : ℝ) < 1 / 1000))).exists
  refine ⟨5 * ℓ, by positivity, ?_⟩
  filter_upwards [hβev, eventually_gt_atTop (0 : ℝ), eventually_aRunG_le G (b := ℓ / 2) (by positivity)]
    with β hb hβ0 hale
  have ha : 0 < GaugeRunning.aRunG G β := aRunG_pos G hβ0
  obtain ⟨h2, hna⟩ := DoublingClay2.nP_bounds hℓ ha hale
  have hnP : nPG G ℓ β = 2 ^ Nat.clog 2 ⌈2 * ℓ / GaugeRunning.aRunG G β⌉₊ := rfl
  rw [← hnP] at h2 hna
  have hlow := nPG_lower G (ℓ := ℓ) hβ0
  have hup : (nPG G ℓ β : ℝ) * GaugeRunning.aRunG G β ≤ 5 * ℓ := by linarith
  refine ⟨nPG G ℓ β, ⟨_, hnP⟩, h2, hup, ?_⟩
  have hd := hb _ ⟨_, hnP⟩ h2 hlow hup
  have he := edge_le (A := A) hσ.le hlow
  have e : σ * (2 * ℓ) = 2 * σ * ℓ := by ring
  rw [e] at he
  linarith

/-- `(1/4)^m = e^{−log 4 · m}`. -/
theorem quarter_pow (m : ℕ) : ((1 : ℝ) / 4) ^ m = Real.exp (-(Real.log 4 * m)) := by
  rw [show -(Real.log 4 * m) = (m : ℝ) * Real.log (1 / 4) by
    rw [one_div, Real.log_inv]; ring, Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- **A sharp bound as an edge cost**: `250 D ≤ (1/4)^{2ᵏ}` and `n₀ a ≤ C` give
`D ≤ (1/250) e^{−(log 4 / C)(2ᵏ n₀ a)}`. -/
theorem sharp_edge {D C a n₀ : ℝ} {k : ℕ} (hC : 0 < C) (hn0 : 0 ≤ n₀) (hna : n₀ * a ≤ C)
    (hi : 250 * D ≤ ((1 : ℝ) / 4) ^ (2 ^ k)) :
    D ≤ 1 / 250 * Real.exp (-(Real.log 4 / C * ((2 ^ k * n₀) * a))) := by
  have hx2 : (2 ^ k * n₀) * a ≤ 2 ^ k * C := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hna (by positivity)
  have hexp : Real.log 4 / C * ((2 ^ k * n₀) * a) ≤ Real.log 4 * ((2 ^ k : ℕ) : ℝ) := by
    have hl : 0 ≤ Real.log 4 / C := (div_pos (Real.log_pos (by norm_num)) hC).le
    calc Real.log 4 / C * ((2 ^ k * n₀) * a) ≤ Real.log 4 / C * (2 ^ k * C) :=
          mul_le_mul_of_nonneg_left hx2 hl
      _ = Real.log 4 * ((2 ^ k : ℕ) : ℝ) := by push_cast; field_simp
  have hq : ((1 : ℝ) / 4) ^ (2 ^ k) ≤ Real.exp (-(Real.log 4 / C * ((2 ^ k * n₀) * a))) := by
    rw [quarter_pow]; exact Real.exp_le_exp.mpr (by linarith)
  linarith

/-- A power of two above a power of two `n₀ ≥ 2` is `2ᵏ n₀`, and `n₀` is even. -/
theorem pow2_factor {n₀ n : ℕ} (h0 : PeriodicState.IsPow2 n₀) (hn2 : 2 ≤ n₀) (h : PeriodicState.IsPow2 n)
    (hle : n₀ ≤ n) : Even n₀ ∧ ∃ k : ℕ, n = 2 ^ k * n₀ := by
  obtain ⟨b₀, hb₀⟩ := h0
  obtain ⟨b, hb⟩ := h
  have hbb : b₀ ≤ b := by
    have h1 : 2 ^ b₀ ≤ 2 ^ b := by rw [← hb₀, ← hb]; exact hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hb0 : 1 ≤ b₀ := by
    rcases Nat.eq_zero_or_pos b₀ with h0 | h0
    · rw [h0] at hb₀; omega
    · exact h0
  refine ⟨by rw [hb₀]; exact DeltaLengthTower.even_two_pow hb0, b - b₀, ?_⟩
  rw [hb, hb₀, ← pow_add, Nat.sub_add_cancel hbb]

/-- `n₀ a ≤ C ≤ n a`, `a > 0` give `n₀ ≤ n`. -/
theorem le_of_window {n₀ n : ℕ} {a C : ℝ} (ha : 0 < a) (h0 : (n₀ : ℝ) * a ≤ C) (h1 : C ≤ (n : ℝ) * a) :
    n₀ ≤ n := by
  have : (n₀ : ℝ) ≤ n := le_of_mul_le_mul_right (h0.trans h1) ha
  exact_mod_cast this

/-- **The sharp squarings of a seed of `G`, as an edge cost**: at `β > 0`, a seed at the power of two `n₀ ≥ 2`
with `n₀ a ≤ C` bounds the defect at every power of two `n` with `C ≤ n a` by `(1/250) e^{−(log 4/C) n a}`. -/
theorem defectWG_edge {β C : ℝ} (hβ : 0 < β) (hC : 0 < C) {n₀ n : ℕ} (h0 : PeriodicState.IsPow2 n₀)
    (hn2 : 2 ≤ n₀) (hna : (n₀ : ℝ) * GaugeRunning.aRunG G β ≤ C)
    (hd : TorusDoubling.defectWG G 4 (wilsonDensityG G) β n₀ ≤ 1 / 1000)
    (h : PeriodicState.IsPow2 n) (hlo : C ≤ (n : ℝ) * GaugeRunning.aRunG G β) :
    TorusDoubling.defectWG G 4 (wilsonDensityG G) β n
      ≤ 1 / 250 * Real.exp (-(Real.log 4 / C * ((n : ℝ) * GaugeRunning.aRunG G β))) := by
  have ha : 0 < GaugeRunning.aRunG G β := aRunG_pos G hβ
  obtain ⟨he, k, hn⟩ := pow2_factor h0 hn2 h (le_of_window ha hna hlo)
  have hfr := DoublingWilsonG.factRepG (G := G) hβ.le hn2 he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : DoublingRecursion.Δ (DoublingWilsonG.xWG G n₀ β) (DoublingRecursion.corner 0) ≤ 1 / 1000 := by
    rw [DoublingWilsonG.Δ_corner0G]; exact hd
  have hi := DoublingSharp.iterate_sharp hx hp (by linarith) k
  rw [DoublingWilsonG.Δ_cornerG, ← hn] at hi
  have hnR : (n : ℝ) = 2 ^ k * n₀ := by rw [hn]; push_cast; ring
  rw [hnR]
  exact sharp_edge hC (Nat.cast_nonneg _) hna hi

/-- **The run seed of `G` gives the edge cost** at `σ = log 4 / C`, `A = 1/250`, cutoff `ℓ₀ = C`. -/
theorem edgeCostG_of_runSeedG (h : RunSeedG G) :
    ∃ σ A ℓ₀ : ℝ, 0 < ℓ₀ ∧ EdgeCostG G σ A ℓ₀ := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨Real.log 4 / C, 1 / 250, C, hC, div_pos (Real.log_pos (by norm_num)) hC, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β ⟨n₀, h0, hn2, hna, hd⟩ hβ
  intro n hn _ hlo
  exact defectWG_edge G hβ hC h0 hn2 hna hd hn hlo

/-- **The run seed of `G` gives the binding statement** at `σ = log 4 / C`, `A = 1/250`. -/
theorem bindingG_of_runSeedG (h : RunSeedG G) :
    ∃ σ A : ℝ, BindingG G σ A := by
  obtain ⟨σ, A, ℓ₀, _, h⟩ := edgeCostG_of_runSeedG G h
  exact ⟨σ, A, bindingG_of_edgeCostG G h⟩

/-- **`BindingG` is the run seed read as an edge cost.** -/
theorem runSeedG_iff_binding : RunSeedG G ↔ ∃ σ A : ℝ, BindingG G σ A :=
  ⟨bindingG_of_runSeedG G, fun ⟨_, _, h⟩ => runSeedG_of_bindingG G h⟩

theorem runSeedG_of_edgeCostG {σ A ℓ₀ : ℝ} (h : EdgeCostG G σ A ℓ₀) : RunSeedG G :=
  runSeedG_of_bindingG G (bindingG_of_edgeCostG G h)

/-- **The edge cost above a physical cutoff is the run seed.** -/
theorem runSeedG_iff_edgeCost : RunSeedG G ↔ ∃ σ A ℓ₀ : ℝ, 0 < ℓ₀ ∧ EdgeCostG G σ A ℓ₀ :=
  ⟨edgeCostG_of_runSeedG G, fun ⟨_, _, _, _, h⟩ => runSeedG_of_edgeCostG G h⟩

end Chain

section Capstone

open MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.FlowG
  MassGap.TimeGroupG MassGap.ContinuumCluster MassGap.ObserverLinkedG MassGap.SymPlaqG MassGap.FlowClusterG

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]

/-- **The observer's gap from the binding statement**: the input `hρ0`, `hρ1`, `hg` of
`ClayGFinal.clayStatementAtG_GS_noNT`. -/
theorem observerGapG_of_bindingG {σ A : ℝ} (h : BindingG G σ A) (W : ConfFlowG G) {t C₀ : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
      TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
        (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
        (ClayGFinal.preBG W hU) 0 hphys 0) ρ₀ :=
  observerGapG_of_runSeedG (runSeedG_of_bindingG G h) W hU hphys

theorem observerGapG_of_edgeCostG {σ A ℓ₀ : ℝ} (h : EdgeCostG G σ A ℓ₀) (W : ConfFlowG G) {t C₀ : ℝ}
    (hU : ClassMomentsG (canonSched G) W (SymPlaqClassG G) t C₀) {r : ℝ}
    (hphys : (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G)).PhysRange
      (canonSched G) r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
      TransferGap.GapAt (transferNG (canonSched G) schedOS_canonSched
        (energy0G (canonSched G) W (SymPlaqClassG G) (symPlaqG_refl G))
        (ClayGFinal.preBG W hU) 0 hphys 0) ρ₀ :=
  observerGapG_of_bindingG (bindingG_of_edgeCostG G h) W hU hphys

end Capstone

/-! ## 3. The `SU(N)` split: flux edges and hidden modes -/

section SU

open MassGap.CentreSectorSeedN

variable (N : ℕ) [NeZero N]

/-- **The flux edges cost `σ` per length** at the window `[2ℓ, 5ℓ]`: every step's non-zero electric-flux share.

DERIVED: `2` and `5` the window `[2ℓ, 5ℓ]` of `nP` (`DoublingClay2.nP_bounds`). -/
def FluxCostAt (σ A ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun N β → (n : ℝ) * AsymptoticScaling.aRun N β ≤ 5 * ℓ →
    ∀ i : Fin 4, fluxShareN N β n i ≤ A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun N β)))

/-- **The hidden modes cost `σ` per length** at the window `[2ℓ, 5ℓ]`: every step's zero-flux doubling defect.

DERIVED: `2` and `5` the window `[2ℓ, 5ℓ]` of `nP` (`DoublingClay2.nP_bounds`). -/
def HiddenCostAt (σ A ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun N β → (n : ℝ) * AsymptoticScaling.aRun N β ≤ 5 * ℓ →
    ∀ i : Fin 4, trivialDefectN N β n i ≤ A * Real.exp (-(σ * ((n : ℝ) * AsymptoticScaling.aRun N β)))

/-- **The binding statement at `SU(N)`, split over the centre sectors.** -/
def BindingSU (σ A : ℝ) : Prop :=
  0 < σ ∧ ∃ᶠ ℓ in atTop, FluxCostAt N σ A ℓ ∧ HiddenCostAt N σ A ℓ

/-- **The split binding statement gives the run seed of `SU(N)`.** -/
theorem runSeed_of_bindingSU {σ A : ℝ} (h : BindingSU N σ A) : WDeltaRun.RunSeed N := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨hσ, hfr⟩ := h
  have hσ2 : 0 < 2 * σ := by linarith
  obtain ⟨ℓ, ⟨hF, hH⟩, hℓ, hsmall⟩ :=
    (hfr.and_eventually (eventually_small (c := max A 0) hσ2 (by norm_num : (0 : ℝ) < 1 / 80000))).exists
  refine ⟨5 * ℓ, by positivity, ?_⟩
  filter_upwards [hF, hH, eventually_gt_atTop (0 : ℝ),
    WeakCouplingWindow.eventually_aRun_le hN (b := ℓ / 2) (by positivity)] with β hFβ hHβ hβ0 hale
  set a := AsymptoticScaling.aRun N β with ha_def
  have ha : 0 < a := AsymptoticScaling.aRun_pos hN hβ0
  obtain ⟨h2, hna⟩ := DoublingClay2.nP_bounds hℓ ha hale
  set c := Nat.clog 2 ⌈2 * ℓ / a⌉₊ with hc
  have hlow : 2 * ℓ ≤ ((2 ^ c : ℕ) : ℝ) * a := by
    have h1 : ⌈2 * ℓ / a⌉₊ ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
    have h3 : 2 * ℓ / a ≤ ((2 ^ c : ℕ) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rwa [div_le_iff₀ ha] at h3
  have hup : ((2 ^ c : ℕ) : ℝ) * a ≤ 5 * ℓ := by linarith
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at h2; norm_num at h2
    · exact h0
  refine ⟨2 ^ c, ⟨c, rfl⟩, h2, hup, ?_⟩
  have he := edge_le (A := A) hσ.le hlow
  have e : σ * (2 * ℓ) = 2 * σ * ℓ := by ring
  rw [e] at he
  refine defectW_le_of_sectorsN hβ0.le h2 (DeltaLengthTower.even_two_pow hc1) (fun i => ⟨?_, ?_⟩)
  · have := hFβ (2 ^ c) ⟨c, rfl⟩ h2 hlow hup i; linarith
  · have := hHβ (2 ^ c) ⟨c, rfl⟩ h2 hlow hup i; linarith

/-- **The split binding statement gives `RunSeedG (SU N)`**, hence the observer's gap over `SU(N)`. -/
theorem runSeedG_of_bindingSU [Fact (2 ≤ N)] {σ A : ℝ} (h : BindingSU N σ A) :
    RunSeedG (SUN.SU N) :=
  (runSeedG_SU N).mpr (runSeed_of_bindingSU N h)

/-- **The sharp squarings of an `SU(N)` seed, as an edge cost**: at `β > 0`, a seed at the power of two `n₀ ≥ 2`
with `n₀ a ≤ C` bounds the defect at every power of two `n` with `C ≤ n a` by `(1/250) e^{−(log 4/C) n a}`. -/
theorem defectW_edge {β C : ℝ} (hβ : 0 < β) (hC : 0 < C) {n₀ n : ℕ} (h0 : PeriodicState.IsPow2 n₀)
    (hn2 : 2 ≤ n₀) (hna : (n₀ : ℝ) * AsymptoticScaling.aRun N β ≤ C)
    (hd : ZoomSelfScale.defectW N β n₀ ≤ 1 / 1000)
    (h : PeriodicState.IsPow2 n) (hlo : C ≤ (n : ℝ) * AsymptoticScaling.aRun N β) :
    ZoomSelfScale.defectW N β n
      ≤ 1 / 250 * Real.exp (-(Real.log 4 / C * ((n : ℝ) * AsymptoticScaling.aRun N β))) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ha : 0 < AsymptoticScaling.aRun N β := AsymptoticScaling.aRun_pos hN hβ
  obtain ⟨he, k, hn⟩ := pow2_factor h0 hn2 h (le_of_window ha hna hlo)
  have hfr := DoublingWilson.factRep (N := N) (NeZero.ne N) hβ.le hn2 he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : DoublingRecursion.Δ (DoublingWilson.xW N n₀ β) (DoublingRecursion.corner 0) ≤ 1 / 1000 := by
    rw [DoublingWilson.Δ_corner0]; exact hd
  have hi := DoublingSharp.iterate_sharp hx hp (by linarith) k
  rw [WDeltaRun.Δ_corner, ← hn] at hi
  have hnR : (n : ℝ) = 2 ^ k * n₀ := by rw [hn]; push_cast; ring
  rw [hnR]
  exact sharp_edge hC (Nat.cast_nonneg _) hna hi

/-- **The run seed of `SU(N)` gives the split binding statement** at `σ = log 4 / C`,
`A = max(N³/2, 2)/250` (`CentreSectorSeedN.sectors_of_defectWN` at `δ = e^{−σ n a}/250`, once
`(4 + N⁶) δ ≤ 2`). -/
theorem bindingSU_of_runSeed (h : WDeltaRun.RunSeed N) : ∃ σ A : ℝ, BindingSU N σ A := by
  obtain ⟨C, hC, hev⟩ := h
  have hσ : 0 < Real.log 4 / C := div_pos (Real.log_pos (by norm_num)) hC
  refine ⟨Real.log 4 / C, max ((N : ℝ) ^ 3 / 2) 2 / 250, hσ, Eventually.frequently ?_⟩
  have hsm := ApertureGap.eventually_poly_exp_le (m := 2 * (Real.log 4 / C)) (by linarith)
    (4 + (N : ℝ) ^ 6) 0 (by norm_num : (0 : ℝ) < 500)
  filter_upwards [eventually_ge_atTop (C / 2), hsm] with ℓ hℓ hs
  simp only [pow_zero, mul_one] at hs
  have key : ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
      2 * ℓ ≤ (n : ℝ) * AsymptoticScaling.aRun N β → ∀ i : Fin 4,
      fluxShareN N β n i ≤ max ((N : ℝ) ^ 3 / 2) 2 / 250
          * Real.exp (-(Real.log 4 / C * ((n : ℝ) * AsymptoticScaling.aRun N β)))
        ∧ trivialDefectN N β n i ≤ max ((N : ℝ) ^ 3 / 2) 2 / 250
          * Real.exp (-(Real.log 4 / C * ((n : ℝ) * AsymptoticScaling.aRun N β))) := by
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with β ⟨n₀, h0, hn2, hna, hd⟩ hβ
    intro n hn h2 hlo i
    set x := (n : ℝ) * AsymptoticScaling.aRun N β with hx
    set e := Real.exp (-(Real.log 4 / C * x)) with he_def
    have hd' := defectW_edge N hβ hC h0 hn2 hna hd hn (by linarith)
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have hee : e ≤ Real.exp (-(2 * (Real.log 4 / C) * ℓ)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hlo hσ.le])
    have hN6 : 0 ≤ 4 + (N : ℝ) ^ 6 := by positivity
    have hδ : (4 + (N : ℝ) ^ 6) * (1 / 250 * e) ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hee hN6
      linarith
    have heven : Even n := (pow2_factor hn h2 hn le_rfl).1
    obtain ⟨hf, ht⟩ := sectors_of_defectWN (δ := 1 / 250 * e) hβ.le h2 heven (by positivity) hδ hd' i
    have hm1 := mul_le_mul_of_nonneg_right (le_max_left ((N : ℝ) ^ 3 / 2) 2) he0
    have hm2 := mul_le_mul_of_nonneg_right (le_max_right ((N : ℝ) ^ 3 / 2) 2) he0
    exact ⟨by linarith, by linarith⟩
  exact ⟨key.mono fun β hβ n hn h2 hlo _ i => (hβ n hn h2 hlo i).1,
    key.mono fun β hβ n hn h2 hlo _ i => (hβ n hn h2 hlo i).2⟩

/-- **The split binding statement is the run seed of `SU(N)`.** -/
theorem runSeed_iff_bindingSU : WDeltaRun.RunSeed N ↔ ∃ σ A : ℝ, BindingSU N σ A :=
  ⟨bindingSU_of_runSeed N, fun ⟨_, _, h⟩ => runSeed_of_bindingSU N h⟩

end SU

/-! ## 4. Tests -/

section Tests

open MassGap.ApertureGap

/-- `2 ≤ 2`, for the `SU(2)` instances. -/
local instance fact_two_le_two : Fact (2 ≤ 2) := ⟨le_rfl⟩

/-- **A Coulomb finite-size part excludes the binding statement at `SU(2)`**, at every `σ`, `A`. -/
theorem not_bindingG_of_coulomb {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hcoul : ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, a ≤ x → κ * x⁻¹ ≤ EnergySeed.finiteSize 2 n x) (σ A : ℝ) :
    ¬ BindingG (SUN.SU 2) σ A := by
  intro h
  have hr := (runSeedG_SU 2).mp (runSeedG_of_bindingG (SUN.SU 2) h)
  obtain ⟨L, _, hP⟩ := ApertureBridge.physDefect_of_runSeed hr
  exact ApertureOne.not_physDefect_of_coulomb (L := L) (δ := 1 / 1000) hκ ha hcoul hP

/-- **A Coulomb finite-size part excludes the edge cost at `SU(2)`**, at every `σ`, `A`, `ℓ₀`. -/
theorem not_edgeCostG_of_coulomb {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hcoul : ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, a ≤ x → κ * x⁻¹ ≤ EnergySeed.finiteSize 2 n x) (σ A ℓ₀ : ℝ) :
    ¬ EdgeCostG (SUN.SU 2) σ A ℓ₀ :=
  fun h => not_bindingG_of_coulomb hκ ha hcoul σ A (bindingG_of_edgeCostG (SUN.SU 2) h)

/-- **The model form of the binding statement**: frequently in the physical length `L`, eventually in the zoom
`K`. -/
def EdgeCostModel (D : ℝ → ℕ → ℝ) (σ A : ℝ) : Prop :=
  0 < σ ∧ ∃ᶠ L in atTop, ∀ᶠ K in atTop, D L K ≤ A * Real.exp (-(σ * L))

/-- **The Gaussian box defect at every zoom**: at least `e^{−2π} e^{−ML}` for `L ≥ 1`, `K ≥ 1`. -/
theorem gaussD_lower_zoom {M L : ℝ} (hM : 0 ≤ M) (hL : 1 ≤ L) {K : ℕ} (hK : 1 ≤ K) :
    Real.exp (-(2 * Real.pi)) * Real.exp (-(M * L)) ≤ gaussD M L K := by
  have hL0 : 0 < L := by linarith
  have hmem : (fun _ => 1 : Fin 3 → ℕ) ∈ box K := by
    simp [box, Fintype.mem_piFinset]
    exact hK
  have hq : ∀ k, 0 ≤ oscD (Real.exp (-(freq M L K k * L))) := by
    intro k
    obtain ⟨h0, h1⟩ := gauss_q (M := M) hL0 (K := K) k
    rcases h1.lt_or_eq with h1 | h1
    · exact oscD_nonneg h0 h1
    · rw [h1]; simp [oscD]
  have hone := Finset.single_le_sum (fun k _ => hq k) hmem
  have hfl := freq_low_le hM hL0 hK
  have hqlow : Real.exp (-(2 * Real.pi)) * Real.exp (-(M * L))
      ≤ Real.exp (-(freq M L K (fun _ => 1) * L)) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  have hlt : Real.exp (-(freq M L K (fun _ => 1) * L)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hf : 0 < freq M L K (fun _ => 1) := by
      show 0 < Real.sqrt (M ^ 2 + (phat L K 1 ^ 2 + phat L K 1 ^ 2 + phat L K 1 ^ 2))
      apply Real.sqrt_pos.2
      have h1 := phat_ge hL0 (K := K) (j := 1) hK
      have h2 : 0 < 2 * ((1 : ℕ) : ℝ) / L := div_pos (by norm_num) hL0
      nlinarith [sq_nonneg M, pow_pos (h2.trans_le h1) 2]
    have := mul_pos hf hL0
    linarith
  exact hqlow.trans ((oscD_ge (Real.exp_pos _).le hlt).trans hone)

/-- **The massive Gaussian fails the model form of the binding statement at every rate above its mass**, at every
zoom. -/
theorem massive_not_edgeCost_above {M σ : ℝ} (hM : 0 ≤ M) (hσM : M < σ) (A : ℝ) :
    ¬ EdgeCostModel (gaussD M) σ A := by
  rintro ⟨_, hfr⟩
  have hδ : (0 : ℝ) < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
  obtain ⟨L, hK, hsmall, hL1⟩ := (hfr.and_eventually
    ((eventually_poly_exp_le (sub_pos.2 hσM) A 0 (half_pos hδ)).and (eventually_ge_atTop (1 : ℝ)))).exists
  obtain ⟨K, hD, hK1⟩ := (hK.and (eventually_ge_atTop 1)).exists
  have h1 := (gaussD_lower_zoom hM hL1 hK1).trans hD
  have e : A * Real.exp (-(σ * L)) = A * L ^ 0 * Real.exp (-((σ - M) * L)) * Real.exp (-(M * L)) := by
    rw [pow_zero, mul_one, mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [e] at h1
  have h2 := le_of_mul_le_mul_right h1 (Real.exp_pos _)
  linarith

/-- **The 4D massless Gaussian fails the model form of the binding statement at every `σ`, `A`** (a free-field
stand-in for the weak-coupling photon; one-direction cycle doubling, Dirichlet modes). -/
theorem photon_not_edgeCost (σ A : ℝ) : ¬ EdgeCostModel (gaussD 0) σ A := by
  rintro ⟨hσ, hfr⟩
  exact massive_not_edgeCost_above le_rfl hσ A ⟨hσ, hfr⟩

/-- `ModelFD` at polynomial degree `0` gives the model form of the binding statement. -/
theorem edgeCost_of_modelFD {D : ℝ → ℕ → ℝ} {m C : ℝ} (hm : 0 < m) (h : ModelFD D m C 0) :
    EdgeCostModel D m C := by
  refine ⟨hm, Eventually.frequently ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact Eventually.of_forall fun K => by simpa using h L hL K

/-- **The massive Gaussian satisfies the model form of the binding statement at `σ = λM`.** -/
theorem massive_edgeCost {M lam : ℝ} (hM : 0 < M) (hl0 : 0 < lam) (hl1 : lam < 1) :
    ∃ A : ℝ, EdgeCostModel (gaussD M) (lam * M) A :=
  ⟨_, edgeCost_of_modelFD (mul_pos hl0 hM) (massive_modelFD hM hl0 hl1)⟩

/-- **2D `SU(2)` by characters satisfies the model form of the binding statement at every `σ > 0`.** -/
theorem ym2_edgeCost {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) : ∃ A : ℝ, EdgeCostModel (ymD κ) σ A :=
  ⟨_, edgeCost_of_modelFD hσ (ym_modelFD hκ σ)⟩

end Tests

/-! ## 5. The forgetting margin and the Weyl step -/

section Margin

open GapL2 Matrix

variable {α : Type*} [Fintype α]

/-- **The perturbation is `ε`-close in the bilinear `L²(π)` form on mean-zero readings**: the analogue of the
Rayleigh closeness of `Entroptics.weyl_top_of_rayleigh` (restated, not imported). -/
def PertBound (π : α → ℝ) (E : Matrix α α ℝ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ f g : α → ℝ, mean π f = 0 → mean π g = 0 →
    |ip π f (E *ᵥ g)| ≤ ε * Real.sqrt (nsq π f) * Real.sqrt (nsq π g)

theorem ip_add (π f u v : α → ℝ) : ip π f (u + v) = ip π f u + ip π f v := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring

/-- The square form of `Corr` in absolute-value form. -/
theorem abs_ip_le_of_corr {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) {K : Matrix α α ℝ} {r : ℝ} (h : Corr π K r)
    {f g : α → ℝ} (hf : mean π f = 0) (hg : mean π g = 0) :
    |ip π f (K *ᵥ g)| ≤ r * Real.sqrt (nsq π f) * Real.sqrt (nsq π g) := by
  have h2 := h.2 f g hf hg
  have hnf := nsq_nonneg hπ f
  have hng := nsq_nonneg hπ g
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt (ip π f (K *ᵥ g) ^ 2) ≤ Real.sqrt (r ^ 2 * nsq π f * nsq π g) := Real.sqrt_le_sqrt h2
    _ = r * Real.sqrt (nsq π f) * Real.sqrt (nsq π g) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq h.1]

/-- **Weyl step**: the margin of `K₀ + E` is at most the margin of `K₀` plus the perturbation. -/
theorem corr_add {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) {K₀ E : Matrix α α ℝ} {r₀ ε : ℝ} (h0 : Corr π K₀ r₀)
    (hE : PertBound π E ε) : Corr π (K₀ + E) (r₀ + ε) := by
  refine ⟨add_nonneg h0.1 hE.1, fun f g hf hg => ?_⟩
  have h1 := abs_ip_le_of_corr hπ h0 hf hg
  have h2 := hE.2 f g hf hg
  have hs : ip π f ((K₀ + E) *ᵥ g) = ip π f (K₀ *ᵥ g) + ip π f (E *ᵥ g) := by
    rw [Matrix.add_mulVec, ip_add]
  have habs : |ip π f ((K₀ + E) *ᵥ g)| ≤ (r₀ + ε) * Real.sqrt (nsq π f) * Real.sqrt (nsq π g) := by
    rw [hs]
    calc |ip π f (K₀ *ᵥ g) + ip π f (E *ᵥ g)| ≤ |ip π f (K₀ *ᵥ g)| + |ip π f (E *ᵥ g)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hsq := sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
  have e : ((r₀ + ε) * Real.sqrt (nsq π f) * Real.sqrt (nsq π g)) ^ 2
      = (r₀ + ε) ^ 2 * nsq π f * nsq π g := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (nsq_nonneg hπ f), Real.sq_sqrt (nsq_nonneg hπ g)]
  linarith

theorem maxCorr_add_le {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) {K₀ E : Matrix α α ℝ} {r₀ ε : ℝ}
    (h0 : Corr π K₀ r₀) (hE : PertBound π E ε) : maxCorr π (K₀ + E) ≤ r₀ + ε :=
  maxCorr_le (corr_add hπ h0 hE)

/-- **The rate per physical length from the Weyl step** at a slab of thickness `τ`. -/
theorem rate_of_pert {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) {K₀ E : Matrix α α ℝ} {r₀ ε m τ : ℝ} (hτ : 0 < τ)
    (h0 : Corr π K₀ r₀) (hE : PertBound π E ε) (hpos : 0 < maxCorr π (K₀ + E))
    (hm : r₀ + ε ≤ Real.exp (-(m * τ))) : m ≤ -Real.log (maxCorr π (K₀ + E)) / τ := by
  have h1 := (maxCorr_add_le hπ h0 hE).trans hm
  have h2 : Real.log (maxCorr π (K₀ + E)) ≤ -(m * τ) := by
    rw [← Real.log_exp (-(m * τ))]; exact Real.log_le_log hpos h1
  rw [le_div_iff₀ hτ]; linarith

/-- **The per-step margin tends to `1` with the spacing.** -/
theorem stepMargin_tendsto_one (m : ℝ) :
    Tendsto (fun a : ℝ => Real.exp (-(m * a))) (nhds 0) (nhds 1) := by
  have h : Continuous (fun a : ℝ => Real.exp (-(m * a))) := by fun_prop
  simpa using h.tendsto 0

open MassGap.RelativeGap

/-- `kH` has no maximal-correlation bound below `1`. -/
theorem not_corr_kH {r : ℝ} (hr : r < 1) : ¬ Corr piH kH r := by
  intro h
  have h2 := h.2 gH gH mean_gH mean_gH
  rw [kH_gH, ← nsq_eq_ip, nsq_gH] at h2
  have := h.1
  nlinarith

/-- **For `kH` no split certifies a margin below `1`**: every split `kH = K₀ + E` with `Corr K₀ r₀` and
`PertBound E ε` has `1 ≤ r₀ + ε`. With `RelativeGap.hidden_coarse` (correlation `0` on the aperture's readings), the
aperture's margin does not bound the full transfer. -/
theorem pert_ge_one_of_kH {K₀ E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ} {r₀ ε : ℝ}
    (h0 : Corr piH K₀ r₀) (hE : PertBound piH E ε) (hs : K₀ + E = kH) : 1 ≤ r₀ + ε := by
  by_contra hlt
  have hc := corr_add markov_kH.pi_nonneg h0 hE
  rw [hs] at hc
  exact not_corr_kH (not_le.mp hlt) hc

end Margin

end MassGap.ObserverTheory

end

#print axioms MassGap.ObserverTheory.runSeedG_of_bindingG
#print axioms MassGap.ObserverTheory.bindingG_of_runSeedG
#print axioms MassGap.ObserverTheory.runSeedG_iff_binding
#print axioms MassGap.ObserverTheory.runSeedG_of_edgeCostG
#print axioms MassGap.ObserverTheory.edgeCostG_of_runSeedG
#print axioms MassGap.ObserverTheory.runSeedG_iff_edgeCost
#print axioms MassGap.ObserverTheory.bindingSU_of_runSeed
#print axioms MassGap.ObserverTheory.runSeed_iff_bindingSU
#print axioms MassGap.ObserverTheory.not_edgeCostG_of_coulomb
#print axioms MassGap.ObserverTheory.observerGapG_of_bindingG
#print axioms MassGap.ObserverTheory.observerGapG_of_edgeCostG
#print axioms MassGap.ObserverTheory.runSeed_of_bindingSU
#print axioms MassGap.ObserverTheory.runSeedG_of_bindingSU
#print axioms MassGap.ObserverTheory.not_bindingG_of_coulomb
#print axioms MassGap.ObserverTheory.gaussD_lower_zoom
#print axioms MassGap.ObserverTheory.massive_not_edgeCost_above
#print axioms MassGap.ObserverTheory.photon_not_edgeCost
#print axioms MassGap.ObserverTheory.massive_edgeCost
#print axioms MassGap.ObserverTheory.ym2_edgeCost
#print axioms MassGap.ObserverTheory.corr_add
#print axioms MassGap.ObserverTheory.rate_of_pert
#print axioms MassGap.ObserverTheory.stepMargin_tendsto_one
#print axioms MassGap.ObserverTheory.pert_ge_one_of_kH
