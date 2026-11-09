import Mathlib
import MassGap.FixedAperture
import MassGap.GapL2

/-!
# MassGap.RelativeGap — the box gap at fixed aperture, read relative to the state

`FixedAperture` splits the fine end into (A) a floor on the box gap at fixed physical aperture `L` as
the zoom refines, (B) uniformity in `L`, and a volume link. Its section 4 shows that every bound built
from a supremum over fine configurations (Birkhoff cross ratio, projective diameter, `apTheta`) fails
to give (A) in 4D. This module states (A) in the relative form: the decay of the slab transfer measured
in the `L²` norm of the box state (`GapL2.Contr`, `GapL2.maxCorr`), the norm the readings themselves
are measured in, not a supremum over configurations.

Everything is finite-dimensional, as in `GapL2`: a slab is a finite Markov pair `(π, K)`.

## 1. The relative floor and (A)

* `Slab`: one time slab of the box — a finite state space, its state `π`, its kernel `K`, `Markov π K`.
  `Slab.rho S = maxCorr S.π S.K`, the maximal correlation across the slab.
Apertures are indexed as in `FixedAperture`: `m : ℕ`, side `L_m = m a₀`; `S m k` is the slab of the box
of side `L_m` at spacing `a_k`.

* `RelFloor S ρ K` (the statement (A_L²)): at every `m > 0`, `0 < ρ m < 1` and from zoom `K m` on the
  slab of the box of side `L_m` has maximal correlation at most `ρ m`.
* `ReadsSlab gL S τ`: the slab has physical thickness `τ m > 0`, and every `L²(π)` contraction rate
  `r > 0` of the slab on mean-zero functions bounds the box gap below: `−log r / τ m ≤ gL m k`. This is
  the link between the number `gL` and the slab (for a reversible transfer whose slab kernel has
  largest excited eigenvalue in absolute value `e^{−g τ}` it is the statement that `g` is the gap); `readsSlab_relGap` proves it
  for the gap defined as `relGap = −log ρ / τ` when `ρ > 0`.
* `fixedApertureFloor_of_relFloor`: `RelFloor ∧ ReadsSlab ∧ (0 < rLat ≤ R)` ⇒
  `FixedAperture.FixedApertureFloor gL rLat c K` with `c m = −log(ρ m) / τ m / R`.
* `uniformInAperture_of_relFloor`: if eventually in `m` the bounds `ρ m ≤ ρ₀ < 1`, `τ m ≤ T` and
  `K m ≤ K₀` hold, (B) holds. `noFade_of_relFloor`: with the volume link, `NoFadeAtFineEnd gLat rLat`.
* `contr_slab_of_step`: a per-step rate `e^{−m a}` gives the slab of `n` steps the rate
  `e^{−m (n a)}`. In `L²` the stacking keeps the rate per unit physical time; the per-step factor tends
  to `1` as `a → 0` while the slab factor does not. The Birkhoff composition (`ApertureGap.crossRatio_iter`)
  does not keep it (`FixedAperture.apTheta_slab_tendsto_one`).

## 2. Which way coarse-graining goes

* `CorrOn π K V r`: the maximal-correlation bound restricted to a set `V` of readings.
  `readings c` is the set of functions of the coarse variable `c`; `readings_comp`: a coarser reading's
  functions are among the finer one's. `corrOn_of_maxCorr`: every set of readings obeys the fine bound,
  `CorrOn π K V (maxCorr π K)`; `CorrOn.anti`: a smaller set obeys every bound of a larger one.
  So the observer's coarse correlation is at most the fine one: the observer's gap is at least the box
  gap. A floor on the fine `ρ` gives one on the observer's; the converse fails.
* `hidden_coarse`, `hidden_maxCorr`: on `Fin 2 × Fin 2`, the kernel `kH` that redraws the first
  coordinate and keeps the second has correlation `0` on every reading of the first coordinate and
  maximal correlation `1`. A coarse reading with a gap does not give a fine gap: a mode hidden from the
  reading can carry correlation `1`.
* `maxCorr_le_of_embed`: if the zoom-`k` slab embeds into the zoom-`(k+1)` slab exactly (a map `e` on
  functions preserving the mean and the `L²` norm and intertwining the kernels, `K' (e u) = e (K u)`: the
  coarse variables of the finer slab evolve as the coarser slab), then `ρ_k ≤ ρ_{k+1}`. Along an exact
  refinement the fine correlation does not decrease: the box gap at fixed aperture does not increase
  with the zoom. Data processing gives no floor; it gives the observer side for free and the fine side as the
  hard side.

## 3. Refinement composes by `max`

* `contr_of_split`: if every mean-zero `g` splits as `v + w`, orthogonal in `L²(π)` and with `K v`,
  `K w` orthogonal, with `‖K v‖ ≤ r₁ ‖v‖` and `‖K w‖ ≤ r₂ ‖w‖`, then `Contr π K (max r₁ r₂)`. The
  readings and the modes hidden from them combine by `max` (the abstract form of `GapL2.Contr.kron`).
* `refine_step`: under an exact embedding `e` of the zoom-`k` slab and a split of the mean-zero functions
  of the zoom-`(k+1)` slab into `e`-images and a hidden layer `W` of rate `r_W`,
  `ρ_{k+1} ≤ max(ρ_k, r_W)`.
* `floor_of_layers`, `relFloor_of_layers`: `ρ_K ≤ ρb` and every layer rate `≤ ρb` give `ρ_k ≤ ρb` at
  every `k ≥ K`. No budget is summed: under the exact split the layers enter by `max`, unlike
  `FineEnd.StepLoss`, whose losses multiply.
* `relFloor_of_contr`: a contraction rate `ρ m` at every zoom from `K m` on (for example from
  `GapL2.contr_of_cellInput`, which holds at every number of cells) gives `RelFloor`.

## 4. Numerics

`research/code/relative_gap_checks.py` (under 3 s), slab `τ = L`, zooms `N = L/a = 4 … 64`.

* 4D free photon (Gaussian, periodic box, spatial zero mode removed; the Gaussian maximal correlation is
  the largest canonical correlation, Lancaster, cited): slab `ρ = 0.00516, 0.00252, 0.00202, 0.00191,
  0.00188 → e^{−2π}`, gap·L `= 5.27 … 6.28 → 2π`, while the log cross ratio of the same slab
  (`fixed_aperture_checks.py` section 3) is `5.6, 10, 32, 121, 477` (`∝ N²`). The one-step `ρ₁` tends to
  `1` (`0.27 … 0.91`) and `ρ₁ⁿ` is the slab `ρ` exactly. A direct matrix computation of the canonical
  correlations at `N = 3, 4` agrees with the mode formula to `10⁻¹⁰`. On `N → 2N` the modes new at
  `2N` have slab correlation `2.7·10⁻⁵ … 2.5·10⁻³⁷`, far below the old modes', so `ρ(2N) = ρ_old`; the
  old modes' `log ρ` moves by `0.72, 0.22, 0.059, 0.015` (lattice dispersion; the refinement is not an
  exact embedding, and `ρ` falls with `N` on this line), a geometric sequence with total `≈ 1.0`.
* 2D `U(1)`/`SU(2)` heat kernel, gauge-projected: the discretised slab kernel in `L²` of the Haar class
  measure has `ρ = e^{−κL²}`, `e^{−3κL²}` to `10⁻⁶`, and the `N`-th power of the one-step kernel has the
  same `ρ` at every `N`, while the one-step-composed sup bound `tanh(D₁/2)^N` is `≥ 0.99997`.
* Aperture growth at fixed `τ = 1`: the photon's `ρ = e^{−2π/L}` tends to `1` (`0.0019 … 0.68` for
  `L = 1 … 16`), the 2D `SU(2)` `ρ = e^{−3κL}` tends to `0`.

So in both models the `L²` gap of the fixed physical slab stays bounded across zooms where the sup-based
constants lose it.

## 5. What remains

`RelFloor` for the 4D `SU(N)` Wilson slab at fixed aperture is not proved here, and no declaration ties
`Slab`, `gL` or `rLat` to the Wilson measure. In the form of section 3 it asks: (i) an embedding of
the coarser slab into the finer one that intertwines the kernels — exact block-spin compatibility, which
the Wilson action does not have; with an approximate intertwining each step adds an error that must be
summed, and the step budget of `FineEnd` returns; (ii) a rate `≤ ρb < 1` for each hidden layer, uniform
in the zoom; (iii) `ReadsSlab`, the lower bound of the box gap by the `L²` rate of the slab of the
Wilson transfer in the state's GNS space. (B) for the photon fails at fixed slab thickness: its `ρ` at
thickness `τ` is `≈ e^{−2πτ/L}`, which tends to `1` as `L` grows.

DERIVED (module-wide): `0` the mean that selects the readings orthogonal to the vacuum and the sign of
every bound; `1` the bound `maxCorr ≤ 1` and the hidden mode's correlation; `1/4` the uniform state on
`Fin 2 × Fin 2`; `1/2` the redraw probability of each value of the first coordinate; `2` the degree of
the norm (`r²`) and the size of each coordinate.
-/

noncomputable section

namespace MassGap.RelativeGap

open Filter Topology Matrix GapL2
open MassGap.NoTransition MassGap.FixedAperture

/-! ## 1. The relative floor and (A) -/

/-- **One time slab of the box**: a finite state space, the box state `π` on it, the slab kernel `K`,
and `Markov π K`. -/
structure Slab where
  Ω : Type
  [fin : Fintype Ω]
  π : Ω → ℝ
  K : Matrix Ω Ω ℝ
  markov : Markov π K

attribute [instance] Slab.fin

/-- The maximal correlation across the slab, in `L²` of the state. -/
def Slab.rho (S : Slab) : ℝ := maxCorr S.π S.K

/-- **(A_L²)**: at every aperture `m > 0` (side `L_m = m a₀`, the convention of `FixedAperture`),
`0 < ρ m < 1`, and from zoom `K m` on the slab of the box of side `L_m` has maximal correlation at
most `ρ m`. -/
def RelFloor (S : ℕ → ℕ → Slab) (ρ : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ m, 0 < m → 0 < ρ m ∧ ρ m < 1 ∧ ∀ k, K m ≤ k → (S m k).rho ≤ ρ m

/-- **The box gap reads the slab**: the slab has physical thickness `τ m > 0`, and every `L²(π)`
contraction rate `r > 0` of the slab on mean-zero functions bounds the box gap below by `−log r / τ m`. -/
def ReadsSlab (gL : ℕ → ℕ → ℝ) (S : ℕ → ℕ → Slab) (τ : ℕ → ℝ) : Prop :=
  ∀ m, 0 < m → 0 < τ m ∧
    ∀ k r, 0 < r → Contr (S m k).π (S m k).K r → -Real.log r / τ m ≤ gL m k

/-- The gap per unit physical time read from the maximal correlation of the slab. -/
def relGap (S : ℕ → ℕ → Slab) (τ : ℕ → ℝ) (m k : ℕ) : ℝ := -Real.log (S m k).rho / τ m

/-- **The gap `−log ρ / τ` reads the slab** when every maximal correlation is positive. -/
theorem readsSlab_relGap {S : ℕ → ℕ → Slab} {τ : ℕ → ℝ} (hτ : ∀ m, 0 < m → 0 < τ m)
    (hρ : ∀ m k, 0 < m → 0 < (S m k).rho) : ReadsSlab (relGap S τ) S τ := by
  intro m hm
  refine ⟨hτ m hm, fun k r _ hc => ?_⟩
  have hle : (S m k).rho ≤ r := maxCorr_le_of_contr (S m k).markov hc
  have hlog : Real.log (S m k).rho ≤ Real.log r := Real.log_le_log (hρ m k hm) hle
  exact div_le_div_of_nonneg_right (by linarith) (hτ m hm).le

/-- The floor value `−log(ρ m) / τ m / R`. -/
def relValue (ρ τ : ℕ → ℝ) (R : ℝ) (m : ℕ) : ℝ := -Real.log (ρ m) / τ m / R

/-- **(A_L²) gives (A)**: with the box gap reading the slab and the observer reading in `(0, R]`, the
box gap in observer units has the floor `−log(ρ m) / τ m / R > 0` from zoom `K m` on, at every
aperture `m > 0`. -/
theorem fixedApertureFloor_of_relFloor {gL : ℕ → ℕ → ℝ} {rLat : ℕ → ℝ} {S : ℕ → ℕ → Slab}
    {τ ρ : ℕ → ℝ} {K : ℕ → ℕ} {R : ℝ} (hS : ReadsSlab gL S τ) (hA : RelFloor S ρ K)
    (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R) :
    FixedApertureFloor gL rLat (relValue ρ τ R) K := by
  intro m hm0
  obtain ⟨hρ0, hρ1, hk⟩ := hA m hm0
  obtain ⟨hτ, hg⟩ := hS m hm0
  have hlog : 0 < -Real.log (ρ m) := neg_pos.2 (Real.log_neg hρ0 hρ1)
  have hm : 0 < -Real.log (ρ m) / τ m := div_pos hlog hτ
  refine ⟨div_pos hm hR, fun k hkK => ?_⟩
  have hc : Contr (S m k).π (S m k).K (ρ m) :=
    (contr_maxCorr (S m k).markov).mono (hk k hkK) (S m k).markov.pi_nonneg
  have hgk : -Real.log (ρ m) / τ m ≤ gL m k := hg k (ρ m) hρ0 hc
  obtain ⟨hr0, hrR⟩ := hr k
  show -Real.log (ρ m) / τ m / R ≤ gL m k / rLat k
  calc -Real.log (ρ m) / τ m / R ≤ -Real.log (ρ m) / τ m / rLat k :=
        div_le_div_of_nonneg_left hm.le hr0 hrR
    _ ≤ gL m k / rLat k := div_le_div_of_nonneg_right hgk hr0.le

/-- **(B) from bounds uniform in the aperture**: eventually in `m`, `0 < ρ m ≤ ρ₀ < 1`,
`0 < τ m ≤ T` and `K m ≤ K₀`. -/
theorem uniformInAperture_of_relFloor {ρ τ : ℕ → ℝ} {K : ℕ → ℕ} {R ρ₀ T : ℝ} (K₀ : ℕ)
    (hR : 0 < R) (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1) (hT : 0 < T)
    (hev : ∀ᶠ m in atTop, 0 < ρ m ∧ ρ m ≤ ρ₀ ∧ 0 < τ m ∧ τ m ≤ T ∧ K m ≤ K₀) :
    UniformInAperture (relValue ρ τ R) K := by
  have hl0 : 0 < -Real.log ρ₀ := neg_pos.2 (Real.log_neg hρ₀ hρ₀1)
  refine ⟨-Real.log ρ₀ / T / R, div_pos (div_pos hl0 hT) hR, K₀, ?_⟩
  filter_upwards [hev] with m ⟨h0, h1, h2, h3, h4⟩
  refine ⟨?_, h4⟩
  have hlog : -Real.log ρ₀ ≤ -Real.log (ρ m) := neg_le_neg (Real.log_le_log h0 h1)
  show -Real.log ρ₀ / T / R ≤ -Real.log (ρ m) / τ m / R
  refine div_le_div_of_nonneg_right ?_ hR.le
  calc -Real.log ρ₀ / T ≤ -Real.log ρ₀ / τ m := div_le_div_of_nonneg_left hl0.le h2 h3
    _ ≤ -Real.log (ρ m) / τ m := div_le_div_of_nonneg_right hlog h2.le

/-- **The relative route to the fine end**: (A_L²), the reading of the slab, an observer reading in
`(0, R]`, bounds uniform in the aperture and the volume link give `NoFadeAtFineEnd gLat rLat`. -/
theorem noFade_of_relFloor {gL : ℕ → ℕ → ℝ} {gLat rLat : ℕ → ℝ} {S : ℕ → ℕ → Slab}
    {τ ρ : ℕ → ℝ} {K : ℕ → ℕ} {R ρ₀ T : ℝ} (K₀ : ℕ) (hS : ReadsSlab gL S τ)
    (hA : RelFloor S ρ K) (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R)
    (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1) (hT : 0 < T)
    (hev : ∀ᶠ m in atTop, 0 < ρ m ∧ ρ m ≤ ρ₀ ∧ 0 < τ m ∧ τ m ≤ T ∧ K m ≤ K₀)
    (hV : VolumeLink gL gLat rLat) : NoFadeAtFineEnd gLat rLat :=
  noFade_of_split (fixedApertureFloor_of_relFloor hS hA hR hr)
    (uniformInAperture_of_relFloor K₀ hR hρ₀ hρ₀1 hT hev) hV

/-- **Stacking keeps the rate per unit time**: a per-step rate `e^{−m a}` gives the slab of `n` steps
the rate `e^{−m (n a)}`. -/
theorem contr_slab_of_step {α : Type*} [Fintype α] [DecidableEq α] {π : α → ℝ} {K : Matrix α α ℝ}
    (hs : Stat π K) {m a : ℝ} (h : Contr π K (Real.exp (-(m * a)))) (n : ℕ) :
    Contr π (K ^ n) (Real.exp (-(m * (n * a)))) := by
  have e : Real.exp (-(m * (n * a))) = Real.exp (-(m * a)) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [e]; exact Contr.pow hs h n

/-! ## 2. Which way coarse-graining goes -/

section Coarse

variable {α : Type*} [Fintype α]

/-- **The maximal-correlation bound on a set `V` of readings.** -/
def CorrOn (π : α → ℝ) (K : Matrix α α ℝ) (V : Set (α → ℝ)) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ f ∈ V, ∀ g ∈ V, mean π f = 0 → mean π g = 0 →
    ip π f (K *ᵥ g) ^ 2 ≤ r ^ 2 * nsq π f * nsq π g

/-- The readings of a coarse variable `c`: the functions of `c`. -/
def readings {β : Type*} (c : α → β) : Set (α → ℝ) := Set.range fun u : β → ℝ => u ∘ c

omit [Fintype α] in
/-- **A coarser reading's functions are among the finer one's.** -/
theorem readings_comp {β γ : Type*} (c : α → γ) (h : γ → β) : readings (h ∘ c) ⊆ readings c := by
  rintro _ ⟨u, rfl⟩
  exact ⟨u ∘ h, rfl⟩

/-- **A smaller set of readings obeys every bound of a larger one.** -/
theorem CorrOn.anti {π : α → ℝ} {K : Matrix α α ℝ} {V W : Set (α → ℝ)} {r : ℝ}
    (h : CorrOn π K W r) (hVW : V ⊆ W) : CorrOn π K V r :=
  ⟨h.1, fun f hf g hg => h.2 f (hVW hf) g (hVW hg)⟩

/-- **Every set of readings obeys the fine bound**: the observer's correlation is at most `maxCorr`. -/
theorem corrOn_of_maxCorr {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (V : Set (α → ℝ)) :
    CorrOn π K V (maxCorr π K) :=
  ⟨maxCorr_nonneg M, fun f _ g _ hf hg => (corr_maxCorr M).2 f g hf hg⟩

/-- **An exact refinement does not decrease the maximal correlation**: if `e` preserves the mean and
the `L²` norm and intertwines the kernels, `ρ(K) ≤ ρ(K')`. -/
theorem maxCorr_le_of_embed {β : Type*} [Fintype β] {π : α → ℝ} {K : Matrix α α ℝ}
    {π' : β → ℝ} {K' : Matrix β β ℝ} (M : Markov π K) (M' : Markov π' K')
    (e : (α → ℝ) → (β → ℝ)) (he_mean : ∀ u, mean π' (e u) = mean π u)
    (he_nsq : ∀ u, nsq π' (e u) = nsq π u) (he_int : ∀ u, K' *ᵥ e u = e (K *ᵥ u)) :
    maxCorr π K ≤ maxCorr π' K' := by
  refine maxCorr_le_of_contr M ⟨maxCorr_nonneg M', fun u hu => ?_⟩
  have h := (contr_maxCorr M').2 (e u) (by rw [he_mean, hu])
  rw [he_int, he_nsq, he_nsq] at h
  exact h

end Coarse

/-! ### A hidden mode: a coarse gap without a fine one -/

/-- The uniform state on `Fin 2 × Fin 2`. -/
def piH : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4

/-- Redraw the first coordinate uniformly, keep the second. -/
def kH : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := fun p q => if p.2 = q.2 then 1 / 2 else 0

theorem markov_kH : Markov piH kH where
  pi_nonneg _ := by norm_num [piH]
  pi_sum := by norm_num [piH]
  nonneg p q := by unfold kH; split_ifs <;> norm_num
  row p := by
    rcases p with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> norm_num [kH, Fintype.sum_prod_type, Fin.sum_univ_two]
  stat q := by
    rcases q with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> norm_num [piH, kH, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **The reading of the first coordinate sees correlation `0`.** -/
theorem hidden_coarse : CorrOn piH kH (readings (Prod.fst : Fin 2 × Fin 2 → Fin 2)) 0 := by
  refine ⟨le_rfl, ?_⟩
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ _ hv
  beta_reduce at hv ⊢
  have hv' : v 0 + v 1 = 0 := by
    simp only [mean, piH, Fintype.sum_prod_type, Fin.sum_univ_two, Function.comp_apply] at hv
    linarith
  have kHv : kH *ᵥ (v ∘ Prod.fst) = 0 := by
    funext p
    rcases p with ⟨a, b⟩
    rw [mulVec_apply']
    fin_cases b <;> simp [kH, Fintype.sum_prod_type, Fin.sum_univ_two] <;> linarith
  rw [kHv]
  simp [ip]

/-- The hidden mode: the sign of the second coordinate. -/
def gH : Fin 2 × Fin 2 → ℝ := fun p => if p.2 = 0 then 1 else -1

theorem mean_gH : mean piH gH = 0 := by
  norm_num [mean, piH, gH, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem kH_gH : kH *ᵥ gH = gH := by
  funext p
  rcases p with ⟨a, b⟩
  rw [mulVec_apply']
  fin_cases a <;> fin_cases b <;> norm_num [kH, gH, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem nsq_gH : nsq piH gH = 1 := by
  norm_num [nsq, piH, gH, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **No contraction below `1` on the fine functions.** -/
theorem hidden_not_contr {r : ℝ} (hr : r < 1) : ¬ Contr piH kH r := by
  rintro ⟨h0, h⟩
  have h1 := h gH mean_gH
  rw [kH_gH, nsq_gH] at h1
  nlinarith

/-- **The hidden mode carries maximal correlation `1`.** -/
theorem hidden_maxCorr : maxCorr piH kH = 1 :=
  le_antisymm (maxCorr_le_one markov_kH)
    (not_lt.1 fun h => hidden_not_contr h (contr_maxCorr markov_kH))

/-! ## 3. Refinement composes by `max` -/

section Split

variable {α : Type*} [Fintype α]

/-- **Readings and hidden modes combine by `max`.** -/
theorem contr_of_split {π : α → ℝ} {K : Matrix α α ℝ} (piH0 : ∀ x, 0 ≤ π x) {r₁ r₂ : ℝ}
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂)
    (hdec : ∀ g, mean π g = 0 → ∃ v w : α → ℝ, g = v + w ∧ ip π v w = 0 ∧
      ip π (K *ᵥ v) (K *ᵥ w) = 0 ∧ nsq π (K *ᵥ v) ≤ r₁ ^ 2 * nsq π v ∧
      nsq π (K *ᵥ w) ≤ r₂ ^ 2 * nsq π w) :
    Contr π K (max r₁ r₂) := by
  refine ⟨le_max_of_le_left h₁, fun g hg => ?_⟩
  obtain ⟨v, w, rfl, hvw, kHvw, hv, hw⟩ := hdec g hg
  rw [Matrix.mulVec_add, nsq_add, nsq_add, hvw, kHvw]
  have hm1 : r₁ ^ 2 ≤ (max r₁ r₂) ^ 2 := pow_le_pow_left₀ h₁ (le_max_left _ _) 2
  have hm2 : r₂ ^ 2 ≤ (max r₁ r₂) ^ 2 := pow_le_pow_left₀ h₂ (le_max_right _ _) 2
  nlinarith [mul_le_mul_of_nonneg_right hm1 (nsq_nonneg piH0 v),
    mul_le_mul_of_nonneg_right hm2 (nsq_nonneg piH0 w)]

/-- **One refinement step**: under an exact embedding `e` of the coarser slab and a split of the
finer slab's mean-zero functions into `e`-images and a hidden layer `W` of rate `r_W`,
`ρ(K') ≤ max(ρ(K), r_W)`. -/
theorem refine_step {β : Type*} [Fintype β] {π : α → ℝ} {K : Matrix α α ℝ}
    {π' : β → ℝ} {K' : Matrix β β ℝ} (M : Markov π K) (M' : Markov π' K')
    (e : (α → ℝ) → (β → ℝ)) (he_nsq : ∀ u, nsq π' (e u) = nsq π u)
    (he_int : ∀ u, K' *ᵥ e u = e (K *ᵥ u)) {W : Set (β → ℝ)} {rW : ℝ} (hrW : 0 ≤ rW)
    (hW : ∀ w ∈ W, nsq π' (K' *ᵥ w) ≤ rW ^ 2 * nsq π' w)
    (hdec : ∀ g, mean π' g = 0 → ∃ u, mean π u = 0 ∧ ∃ w ∈ W, g = e u + w ∧
      ip π' (e u) w = 0 ∧ ip π' (K' *ᵥ e u) (K' *ᵥ w) = 0) :
    maxCorr π' K' ≤ max (maxCorr π K) rW := by
  have hc := contr_maxCorr M
  refine maxCorr_le_of_contr M' (contr_of_split M'.pi_nonneg (maxCorr_nonneg M) hrW fun g hg => ?_)
  obtain ⟨u, hu, w, hwW, hg', h1, h2⟩ := hdec g hg
  refine ⟨e u, w, hg', h1, h2, ?_, hW w hwW⟩
  rw [he_int, he_nsq, he_nsq]
  exact hc.2 u hu

end Split

/-- **Layers bounded by `ρb` keep the floor**: `ρ_K ≤ ρb` and `ρ_{k+1} ≤ max(ρ_k, h_k)` with
`h_k ≤ ρb` give `ρ_k ≤ ρb` at every `k ≥ K`. -/
theorem floor_of_layers {ρk h : ℕ → ℝ} {K : ℕ} {ρb : ℝ} (h0 : ρk K ≤ ρb)
    (hstep : ∀ k, K ≤ k → ρk (k + 1) ≤ max (ρk k) (h k)) (hh : ∀ k, K ≤ k → h k ≤ ρb) :
    ∀ k, K ≤ k → ρk k ≤ ρb := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h0
  | succ n hn ih => exact (hstep n hn).trans (max_le ih (hh n hn))

/-- **(A_L²) from the layers**: at every aperture `m > 0`, a start `ρ_{K m} ≤ ρ m < 1`, refinement
steps `ρ_{k+1} ≤ max(ρ_k, h m k)` and layer rates `h m k ≤ ρ m`. -/
theorem relFloor_of_layers {S : ℕ → ℕ → Slab} {ρ : ℕ → ℝ} {K : ℕ → ℕ} {h : ℕ → ℕ → ℝ}
    (hρ : ∀ m, 0 < m → 0 < ρ m ∧ ρ m < 1) (h0 : ∀ m, 0 < m → (S m (K m)).rho ≤ ρ m)
    (hstep : ∀ m, 0 < m → ∀ k, K m ≤ k → (S m (k + 1)).rho ≤ max (S m k).rho (h m k))
    (hh : ∀ m, 0 < m → ∀ k, K m ≤ k → h m k ≤ ρ m) : RelFloor S ρ K := fun m hm =>
  ⟨(hρ m hm).1, (hρ m hm).2,
    floor_of_layers (ρk := fun k => (S m k).rho) (h0 m hm) (hstep m hm) (hh m hm)⟩

/-- **(A_L²) from a contraction rate at every zoom.** -/
theorem relFloor_of_contr {S : ℕ → ℕ → Slab} {ρ : ℕ → ℝ} {K : ℕ → ℕ}
    (hρ : ∀ m, 0 < m → 0 < ρ m ∧ ρ m < 1)
    (hc : ∀ m, 0 < m → ∀ k, K m ≤ k → Contr (S m k).π (S m k).K (ρ m)) : RelFloor S ρ K :=
  fun m hm => ⟨(hρ m hm).1, (hρ m hm).2, fun k hk => maxCorr_le_of_contr (S m k).markov (hc m hm k hk)⟩

#print axioms readsSlab_relGap
#print axioms fixedApertureFloor_of_relFloor
#print axioms uniformInAperture_of_relFloor
#print axioms noFade_of_relFloor
#print axioms contr_slab_of_step
#print axioms readings_comp
#print axioms CorrOn.anti
#print axioms corrOn_of_maxCorr
#print axioms maxCorr_le_of_embed
#print axioms markov_kH
#print axioms hidden_coarse
#print axioms hidden_not_contr
#print axioms hidden_maxCorr
#print axioms contr_of_split
#print axioms refine_step
#print axioms floor_of_layers
#print axioms relFloor_of_layers
#print axioms relFloor_of_contr

end MassGap.RelativeGap
