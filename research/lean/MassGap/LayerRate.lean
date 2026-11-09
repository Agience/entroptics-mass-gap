import Mathlib
import MassGap.RelativeGap

/-!
# MassGap.LayerRate — the approximate layer split, and the rate of the new modes across a fixed slab

`RelativeGap` section 3 proves that refinement combines by `max` when the new ("hidden") layer is
exactly orthogonal to the old readings before and after the slab kernel (`contr_of_split`,
`refine_step`). This module drops the exactness: the cross term between the old readings and the new
layer after the kernel, and the defect of the embedding of the coarser slab, each enter the step as an
additive error on `ρ²`. Under a summable error the floor of `RelativeGap.RelFloor` follows. The second
half bounds the rate of the new layer by the length of the slab in lattice steps.

Everything is finite-dimensional, as in `GapL2`.

## 1. The approximate split

* `nsq_add_le_sq`: `‖a‖ ≤ A √N`, `‖b‖ ≤ B √N` (squared form) give `‖a + b‖ ≤ (A + B) √N`.
* `contr_of_approxSplit`: if every mean-zero `g` splits as `v + w` with `⟨v, w⟩ = 0`,
  `‖K v‖ ≤ r₁ ‖v‖`, `‖K w‖ ≤ r₂ ‖w‖` and the **relative cross term** bounded,
  `⟨K v, K w⟩² ≤ δ² ‖v‖² ‖w‖²` (norms and inner products in `L²(π)`), then
  `‖K g‖² ≤ (max(r₁, r₂)² + δ) ‖g‖²`. `RelativeGap.contr_of_split` is the case `δ = 0`.
* `refine_step_approx`: zoom-`k` slab `(π, K)`, zoom-`(k+1)` slab `(π', K')`, a norm-preserving map `e`
  of the coarse functions into the fine ones, a set `W` (the new layer) with rate `r_W`, and:
  - the **intertwining defect** `η`: `‖K' (e u) − e (K u)‖² ≤ η² ‖u‖²` for mean-zero `u`;
  - the **cross term** `δ`: `⟨K' (e u), K' w⟩² ≤ δ² ‖e u‖² ‖w‖²` for the pieces of the split;
  - every mean-zero `g` is `e u + w` with `u` mean-zero, `w ∈ W`, `⟨e u, w⟩ = 0`.
  Then `ρ_{k+1}² ≤ max((ρ_k + η)², r_W²) + δ`.
* `refine_step_sq`: the same as `ρ_{k+1}² ≤ max(ρ_k², r_W²) + (η (2 + η) + δ)`, using `ρ_k ≤ 1`.

**Which object `δ_k` is.** The theorems accept any `δ` satisfying the bound; the smallest admissible
`δ_k` is the operator norm of the off-diagonal block of the form
`(f, g) ↦ ⟨K' f, K' g⟩` between the old readings `e(·)` and the new layer `W`, each measured in the
`L²` norm of the zoom-`(k+1)` state before the kernel. For a reversible slab
`⟨K' f, K' g⟩ = ⟨f, K'² g⟩`: `δ_k` is the correlation between an old reading and a new mode across the
doubled slab, relative to their own `L²` norms. It is not a supremum over configurations. When `W` is
taken as the `L²(π')` orthogonal complement of the old readings, the condition `⟨e u, w⟩ = 0` holds by
construction and `δ_k` is the only cross term.

## 2. The floor from a summable error

* `floor_of_layers_approx`: `s_K ≤ s_b`, `s_{k+1} ≤ max(s_k, h_k) + e_k`, `h_k ≤ s_b`, `e_k ≥ 0` give
  `s_k ≤ s_b + Σ_{K ≤ j < k} e_j`. The layers still enter by `max`; only the errors are summed.
* `Ico_sum_le_tail`, `exists_tail_le`: for a non-negative summable `e`, the partial sums from `K` are at
  most the tail `Σ' e_{j+K}`, and the tail is below any `ε > 0` from some `K₀` on.
* `relFloor_of_layers_approx`, `relFloor_of_summable`: at every aperture `m > 0`, the squared steps of
  `refine_step_sq` from a start `ρ_{K m}² ≤ ρb_m²`, layer rates `h ≤ ρb_m²`, and errors whose partial
  sums are at most `E_m` with `ρb_m² + E_m < 1` give `RelFloor S (√(ρb² + E)) K`.

So the summable budget returns, on the cross term `δ_k` and the intertwining defect `η_k`, both
measured relative to the state, and not on the gap: `FineEnd.StepLoss` multiplies the gap by
`1 − ε_k` at every step, while here the layer rates enter by `max` and need no budget.

## 3. The rate of the new layer across a fixed physical slab

* `layer_contr_pow`: if the per-step kernel `Q` maps `W` into itself and contracts it by `e^{−c}` in
  `L²(π)`, then `Qⁿ` contracts `W` by `e^{−c n}`.
* `layer_rate_slab`: with spacing `a > 0` and `n a ≥ τ` (the slab of physical thickness `τ` has
  `n ≥ τ / a` steps), `Qⁿ` contracts `W` by `e^{−c τ / a}`. A per-step rate `e^{−c}` is an `L²` gap
  `c / a` per unit physical time: new modes that are massive in lattice units are almost uncorrelated
  across a slab of fixed physical thickness.
* `maxCorr_slab_le_of_stepGap`: the Markov form, `ρ(Qⁿ) ≤ e^{−c τ / a}` from `Contr π Q (e^{−c})`.
* `layerRate a₀ c τ k = e^{−c τ / a_k}`, `a_k = a₀ / 2^k` (`FixedAperture.aZ`):
  `layerRate_le_geom` (`≤ (e^{−c τ / a₀})^{k+1}`, at `c τ / a₀ ≥ 0`), and at `c τ / a₀ > 0`
  `layerRate_summable`, `layerRate_tendsto_zero`, `layerRate_eventually_le`. Along the zoom the layer rate tends to `0` and is summable; it is below
  every `ρb > 0` from some zoom on.

## 4. Numerics

`research/code/layer_rate_checks.py` (under 5 s, no Monte Carlo). Old readings: the linear functionals
of the averages over `2³` spatial blocks; `W` their `L²` complement; linear functionals only (the
Gaussian maximal correlation is the largest canonical correlation, Lancaster, cited; for `δ`, `η`,
`r_W` on the higher Wiener chaoses of the complement the script sketches a bound and does not prove it).

* 4D free photon, each transverse polarisation treated as a massless scalar (the `k`-dependent
  transverse projector is not included), spatial zero mode removed, `τ = L`, `N → 2N` for `N = 4 … 64`:
  `δ_k = 1.4·10⁻⁶, 3.1·10⁻⁷, 9.5·10⁻⁸, 3.2·10⁻⁸, 1.1·10⁻⁸`, ratios `0.22, 0.31, 0.34, 0.35` beside
  `2^{−3/2} = 0.354`; `η_k = 2.8·10⁻³ … 9.3·10⁻⁶`; `Σ (η (2 + η) + δ) = 7.1·10⁻³` over the line.
  `r_W` of the block layer `5.8·10⁻⁴ … 6.0·10⁻⁶` (ratios toward `2^{−3/2}`: the block average leaks into
  the aliases of a coarse momentum); `r_W` of the Fourier layer (momenta above the coarse Nyquist
  index) `= e^{−c_k τ / a}` with per-step `c_k = 1.653, 1.514, 1.423, 1.372, 1.345`, falling toward
  `arccosh 2 = 1.317` and above it, `1.8·10⁻⁶ … 1.7·10⁻⁷⁵`. Both
  `ρ_{k+1}² ≤ max(r_old², r_W²) + δ` and `ρ_{k+1}² ≤ max(ρ_k², r_W²) + η (2 + η) + δ` hold on the
  computed numbers at every step.
* Free massive scalar, `m L = 1`, `τ = L`: the same orders (`δ_k = 1.2·10⁻⁶ … 9.7·10⁻⁹`), `ρ → e^{−1}`.
* 2D: `Z_12` (discretised `U(1)`) on two fine links against one coarse link, gauge-projected:
  `δ = η = r_W = 0` to `10⁻¹⁵` (the complement of the holonomy readings is gauge-variant and the
  projected kernel kills it). `SU(2)` class functions: `‖K_{t/2}² − K_t‖ = 10⁻¹⁶`.
* 4D `U(1)` (Gaussian, Coulomb phase), `τ = 1`, `L = 1, 2, 4, 8`: at each `L`, `δ_k`, `η_k`, `r_W`
  fall along the zoom; at fine spacing `a = 1/8`, `δ = 1.4·10⁻⁶, 1.5·10⁻⁴, 1.1·10⁻³, 1.9·10⁻³`; the slab
  `ρ` at the finest zoom read for each `L` (`a = 1/32, 1/16, 1/8, 1/8`) is `0.0019, 0.044, 0.21, 0.46`,
  beside `e^{−2πτ/L}`, and tends to `1`. What fails is (B), uniformity in the
  aperture, not the approximate split or the layer rate.

## 5. What remains for 4D `SU(N)`

Neither input below is proved here, and no declaration here ties `Q`, `W`, `e`, `δ` or `η` to the
Wilson measure.

(i) **The conditional UV gap.** For the fine Wilson measure at zoom `k+1` conditioned on the coarse
(block) field, the per-step transfer of the new modes on one fixed physical cell contracts them in
`L²` of the conditional measure by `e^{−c}`, `c > 0` uniform in `k` (gap `≥ c / a_k`), at the bare
couplings of the asymptotically free regime. `layer_rate_slab` turns a per-step contraction of an
INVARIANT layer into `r_W ≤ e^{−c τ / a_k}`; for a reversible slab an invariant complement of the
old readings has cross term `δ = 0`, so for a split with `δ > 0` the bound on the slab restricted to
`W` (the `hW` of `refine_step_*`) from the conditional kernel is a further link, part of this input.
(ii) **The summable relative cross term.** `Σ_k (η_k (2 + η_k) + δ_k) < ∞`, with `δ_k`, `η_k` the
objects of section 1 for the Wilson slab and a gauge-covariant block map `e`.
`ReadsSlab` is the third input (`RelativeGap` section 5).

Near them in the tree, none stating either: `BlockSU2.blockLink` / `BlockLattice.blockConf` are a
continuous gauge-covariant block map of `SU(2)` configurations (a candidate for the coarse variable of
`e`; no `L²` isometry or intertwining is stated for it); `FlowUV.SiteExp` is a one-site exponential
moment of the flowed density; `GaugeRunning` and `ShortDistanceRunning.UVControl` are the running
coupling and the running of two-point readings; `StrongCoupling` is the cluster expansion at small `β`,
the regime opposite to (i).

DERIVED (module-wide): `0` the mean that selects the readings orthogonal to the vacuum and the sign of
every bound; `1` the bound `maxCorr ≤ 1` and the bound `RelFloor` asks below; `2` the degree of the
norm (`r²`), the cross term counted twice in `‖v + w‖²`, the factor of `η (2 + η)` from
`(ρ + η)² ≤ ρ² + η (2 + η)` at `ρ ≤ 1`, and the doubling `a_k = a₀ / 2^k`.
-/

noncomputable section

namespace MassGap.LayerRate

open Filter Topology Matrix GapL2
open MassGap.RelativeGap MassGap.FixedAperture

/-! ## 1. The approximate split -/

section Approx

variable {α : Type*} [Fintype α]

/-- **The triangle inequality, squared form**: `‖a‖² ≤ A² N`, `‖b‖² ≤ B² N` give
`‖a + b‖² ≤ (A + B)² N`. -/
theorem nsq_add_le_sq {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) {a b : α → ℝ} {A B N : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N) (ha : nsq π a ≤ A ^ 2 * N)
    (hb : nsq π b ≤ B ^ 2 * N) : nsq π (a + b) ≤ (A + B) ^ 2 * N := by
  rw [nsq_add]
  have hcs := ip_sq_le hπ a b
  have hAB : nsq π a * nsq π b ≤ (A * B * N) ^ 2 := by
    calc nsq π a * nsq π b ≤ (A ^ 2 * N) * (B ^ 2 * N) :=
          mul_le_mul ha hb (nsq_nonneg hπ _) (mul_nonneg (sq_nonneg A) hN)
      _ = (A * B * N) ^ 2 := by ring
  have hip : ip π a b ≤ A * B * N :=
    (abs_le_of_sq_le_sq' (hcs.trans hAB) (mul_nonneg (mul_nonneg hA hB) hN)).2
  have e : (A + B) ^ 2 * N = A ^ 2 * N + 2 * (A * B * N) + B ^ 2 * N := by ring
  rw [e]
  linarith

/-- **The approximate split**: if every mean-zero `g` splits as `v + w` with `⟨v, w⟩ = 0`, rates
`r₁`, `r₂` on the two pieces, and relative cross term `⟨K v, K w⟩² ≤ δ² ‖v‖² ‖w‖²`, then
`‖K g‖² ≤ (max(r₁, r₂)² + δ) ‖g‖²`. -/
theorem contr_of_approxSplit {π : α → ℝ} {K : Matrix α α ℝ} (hπ : ∀ x, 0 ≤ π x) {r₁ r₂ δ : ℝ}
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (hδ : 0 ≤ δ)
    (hdec : ∀ g, mean π g = 0 → ∃ v w : α → ℝ, g = v + w ∧ ip π v w = 0 ∧
      ip π (K *ᵥ v) (K *ᵥ w) ^ 2 ≤ δ ^ 2 * nsq π v * nsq π w ∧
      nsq π (K *ᵥ v) ≤ r₁ ^ 2 * nsq π v ∧ nsq π (K *ᵥ w) ≤ r₂ ^ 2 * nsq π w) :
    ∀ g, mean π g = 0 → nsq π (K *ᵥ g) ≤ (max r₁ r₂ ^ 2 + δ) * nsq π g := by
  intro g hg
  obtain ⟨v, w, rfl, hvw, hx, hv, hw⟩ := hdec g hg
  rw [Matrix.mulVec_add, nsq_add, nsq_add, hvw]
  have ha := nsq_nonneg hπ v
  have hb := nsq_nonneg hπ w
  have h2x : 2 * ip π (K *ᵥ v) (K *ᵥ w) ≤ δ * (nsq π v + nsq π w) := by
    have hsq : (2 * ip π (K *ᵥ v) (K *ᵥ w)) ^ 2 ≤ (δ * (nsq π v + nsq π w)) ^ 2 := by
      calc (2 * ip π (K *ᵥ v) (K *ᵥ w)) ^ 2 = 4 * ip π (K *ᵥ v) (K *ᵥ w) ^ 2 := by ring
        _ ≤ 4 * (δ ^ 2 * nsq π v * nsq π w) := by linarith
        _ ≤ (δ * (nsq π v + nsq π w)) ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg (nsq π v - nsq π w))]
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg hδ (add_nonneg ha hb))).2
  have hm1 : r₁ ^ 2 ≤ max r₁ r₂ ^ 2 := pow_le_pow_left₀ h₁ (le_max_left _ _) 2
  have hm2 : r₂ ^ 2 ≤ max r₁ r₂ ^ 2 := pow_le_pow_left₀ h₂ (le_max_right _ _) 2
  nlinarith [mul_le_mul_of_nonneg_right hm1 ha, mul_le_mul_of_nonneg_right hm2 hb]

/-- **The approximate split as a contraction rate** `√(max(r₁, r₂)² + δ)`. -/
theorem contr_sqrt_of_approxSplit {π : α → ℝ} {K : Matrix α α ℝ} (hπ : ∀ x, 0 ≤ π x)
    {r₁ r₂ δ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (hδ : 0 ≤ δ)
    (hdec : ∀ g, mean π g = 0 → ∃ v w : α → ℝ, g = v + w ∧ ip π v w = 0 ∧
      ip π (K *ᵥ v) (K *ᵥ w) ^ 2 ≤ δ ^ 2 * nsq π v * nsq π w ∧
      nsq π (K *ᵥ v) ≤ r₁ ^ 2 * nsq π v ∧ nsq π (K *ᵥ w) ≤ r₂ ^ 2 * nsq π w) :
    Contr π K (Real.sqrt (max r₁ r₂ ^ 2 + δ)) := by
  refine ⟨Real.sqrt_nonneg _, fun g hg => ?_⟩
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) hδ)]
  exact contr_of_approxSplit hπ h₁ h₂ hδ hdec g hg

/-- **One approximate refinement step**: with intertwining defect `η`, a new layer `W` of rate `r_W`
and relative cross term `δ`, `ρ_{k+1}² ≤ max((ρ_k + η)², r_W²) + δ`. -/
theorem refine_step_approx {β : Type*} [Fintype β] {π : α → ℝ} {K : Matrix α α ℝ}
    {π' : β → ℝ} {K' : Matrix β β ℝ} (M : Markov π K) (M' : Markov π' K')
    (e : (α → ℝ) → (β → ℝ)) (he_nsq : ∀ u, nsq π' (e u) = nsq π u) {η : ℝ} (hη : 0 ≤ η)
    (he_int : ∀ u, mean π u = 0 → nsq π' (K' *ᵥ e u - e (K *ᵥ u)) ≤ η ^ 2 * nsq π u)
    {W : Set (β → ℝ)} {rW δ : ℝ} (hrW : 0 ≤ rW) (hδ : 0 ≤ δ)
    (hW : ∀ w ∈ W, nsq π' (K' *ᵥ w) ≤ rW ^ 2 * nsq π' w)
    (hdec : ∀ g, mean π' g = 0 → ∃ u, mean π u = 0 ∧ ∃ w ∈ W, g = e u + w ∧
      ip π' (e u) w = 0 ∧ ip π' (K' *ᵥ e u) (K' *ᵥ w) ^ 2 ≤ δ ^ 2 * nsq π' (e u) * nsq π' w) :
    maxCorr π' K' ^ 2 ≤ max ((maxCorr π K + η) ^ 2) (rW ^ 2) + δ := by
  have hρ0 := maxCorr_nonneg M
  have hc := contr_maxCorr M
  have hr1 : 0 ≤ maxCorr π K + η := add_nonneg hρ0 hη
  -- the old readings contract by `ρ + η` in the fine slab
  have hold : ∀ u, mean π u = 0 →
      nsq π' (K' *ᵥ e u) ≤ (maxCorr π K + η) ^ 2 * nsq π' (e u) := by
    intro u hu
    have hsplit : K' *ᵥ e u = e (K *ᵥ u) + (K' *ᵥ e u - e (K *ᵥ u)) := by abel
    rw [hsplit, he_nsq u]
    refine nsq_add_le_sq M'.pi_nonneg hρ0 hη (nsq_nonneg M.pi_nonneg u) ?_ (he_int u hu)
    rw [he_nsq]
    exact hc.2 u hu
  have hcon := contr_sqrt_of_approxSplit M'.pi_nonneg hr1 hrW hδ (fun g hg => by
    obtain ⟨u, hu, w, hwW, hg', h1, h2⟩ := hdec g hg
    exact ⟨e u, w, hg', h1, h2, hold u hu, hW w hwW⟩)
  have hle : maxCorr π' K' ≤ Real.sqrt (max (maxCorr π K + η) rW ^ 2 + δ) :=
    maxCorr_le_of_contr M' hcon
  have hsq : maxCorr π' K' ^ 2 ≤ max (maxCorr π K + η) rW ^ 2 + δ := by
    have := pow_le_pow_left₀ (maxCorr_nonneg M') hle 2
    rwa [Real.sq_sqrt (add_nonneg (sq_nonneg _) hδ)] at this
  have hmx : max (maxCorr π K + η) rW ^ 2 ≤ max ((maxCorr π K + η) ^ 2) (rW ^ 2) := by
    rcases le_total (maxCorr π K + η) rW with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_max_left _ _
  linarith

/-- `(ρ + η)² ≤ ρ² + η (2 + η)` at `ρ ≤ 1`, `η ≥ 0`, inside a `max`. -/
theorem max_sq_add_le {ρ η rW δ : ℝ} (hρ1 : ρ ≤ 1) (hη : 0 ≤ η) :
    max ((ρ + η) ^ 2) (rW ^ 2) + δ ≤ max (ρ ^ 2) (rW ^ 2) + (η * (2 + η) + δ) := by
  have hc : 0 ≤ η * (2 + η) := mul_nonneg hη (by linarith)
  have h1 := le_max_left (ρ ^ 2) (rW ^ 2)
  have h2 := le_max_right (ρ ^ 2) (rW ^ 2)
  have hmax : max ((ρ + η) ^ 2) (rW ^ 2) ≤ max (ρ ^ 2) (rW ^ 2) + η * (2 + η) :=
    max_le (by nlinarith [mul_le_mul_of_nonneg_left hρ1 hη]) (by linarith)
  linarith

/-- **One approximate refinement step, squared form**:
`ρ_{k+1}² ≤ max(ρ_k², r_W²) + (η (2 + η) + δ)`. -/
theorem refine_step_sq {β : Type*} [Fintype β] {π : α → ℝ} {K : Matrix α α ℝ}
    {π' : β → ℝ} {K' : Matrix β β ℝ} (M : Markov π K) (M' : Markov π' K')
    (e : (α → ℝ) → (β → ℝ)) (he_nsq : ∀ u, nsq π' (e u) = nsq π u) {η : ℝ} (hη : 0 ≤ η)
    (he_int : ∀ u, mean π u = 0 → nsq π' (K' *ᵥ e u - e (K *ᵥ u)) ≤ η ^ 2 * nsq π u)
    {W : Set (β → ℝ)} {rW δ : ℝ} (hrW : 0 ≤ rW) (hδ : 0 ≤ δ)
    (hW : ∀ w ∈ W, nsq π' (K' *ᵥ w) ≤ rW ^ 2 * nsq π' w)
    (hdec : ∀ g, mean π' g = 0 → ∃ u, mean π u = 0 ∧ ∃ w ∈ W, g = e u + w ∧
      ip π' (e u) w = 0 ∧ ip π' (K' *ᵥ e u) (K' *ᵥ w) ^ 2 ≤ δ ^ 2 * nsq π' (e u) * nsq π' w) :
    maxCorr π' K' ^ 2 ≤ max (maxCorr π K ^ 2) (rW ^ 2) + (η * (2 + η) + δ) :=
  (refine_step_approx M M' e he_nsq hη he_int hrW hδ hW hdec).trans
    (max_sq_add_le (maxCorr_le_one M) hη)

end Approx

/-! ## 2. The floor from a summable error -/

/-- **Layers by `max`, errors by sum**: `s_K ≤ s_b`, `s_{k+1} ≤ max(s_k, h_k) + e_k`, `h_k ≤ s_b`,
`e ≥ 0` give `s_k ≤ s_b + Σ_{K ≤ j < k} e_j` at every `k ≥ K`. -/
theorem floor_of_layers_approx {s h e : ℕ → ℝ} {K : ℕ} {sb : ℝ} (h0 : s K ≤ sb)
    (hstep : ∀ k, K ≤ k → s (k + 1) ≤ max (s k) (h k) + e k) (hh : ∀ k, K ≤ k → h k ≤ sb)
    (he : ∀ k, 0 ≤ e k) : ∀ k, K ≤ k → s k ≤ sb + ∑ j ∈ Finset.Ico K k, e j := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using h0
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have hS : 0 ≤ ∑ j ∈ Finset.Ico K n, e j := Finset.sum_nonneg fun j _ => he j
    have hmax : max (s n) (h n) ≤ sb + ∑ j ∈ Finset.Ico K n, e j :=
      max_le ih (by linarith [hh n hn])
    linarith [hstep n hn]

/-- **Partial sums from `K` are at most the tail** of a non-negative summable sequence. -/
theorem Ico_sum_le_tail {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (hs : Summable e) (K k : ℕ) :
    ∑ j ∈ Finset.Ico K k, e j ≤ ∑' j, e (j + K) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hs' : Summable fun j => e (j + K) := (summable_nat_add_iff K).2 hs
  calc ∑ j ∈ Finset.range (k - K), e (K + j) = ∑ j ∈ Finset.range (k - K), e (j + K) :=
        Finset.sum_congr rfl fun j _ => by rw [add_comm]
    _ ≤ ∑' j, e (j + K) := Summable.sum_le_tsum _ (fun j _ => he _) hs'

/-- **The tail is small from some start on**: for a non-negative summable `e` and `ε > 0` there is
`K₀` such that every partial sum from `K ≥ K₀` is at most `ε`. -/
theorem exists_tail_le {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (hs : Summable e) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ k, ∑ j ∈ Finset.Ico K k, e j ≤ ε := by
  have hev := (tendsto_sum_nat_add e).eventually_lt_const hε
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
  exact ⟨K₀, fun K hK k => (Ico_sum_le_tail he hs K k).trans (hK₀ K hK).le⟩

/-- **(A_L²) from approximate layers**: at every aperture `m > 0`, a start
`ρ_{K m}² ≤ ρb_m²`, squared steps `ρ_{k+1}² ≤ max(ρ_k², h) + e`, layer rates `h ≤ ρb_m²`, errors
`e ≥ 0` with partial sums at most `E_m`, and `ρb_m² + E_m < 1` give `RelFloor S (√(ρb² + E)) K`. -/
theorem relFloor_of_layers_approx {S : ℕ → ℕ → Slab} {ρb E : ℕ → ℝ} {K : ℕ → ℕ}
    {h e : ℕ → ℕ → ℝ} (hb : ∀ m, 0 < m → 0 < ρb m ∧ ρb m ^ 2 + E m < 1)
    (h0 : ∀ m, 0 < m → (S m (K m)).rho ^ 2 ≤ ρb m ^ 2)
    (hstep : ∀ m, 0 < m → ∀ k, K m ≤ k →
      (S m (k + 1)).rho ^ 2 ≤ max ((S m k).rho ^ 2) (h m k) + e m k)
    (hh : ∀ m, 0 < m → ∀ k, K m ≤ k → h m k ≤ ρb m ^ 2) (he : ∀ m k, 0 ≤ e m k)
    (hE : ∀ m, 0 < m → ∀ k, ∑ j ∈ Finset.Ico (K m) k, e m j ≤ E m) :
    RelFloor S (fun m => Real.sqrt (ρb m ^ 2 + E m)) K := by
  intro m hm
  obtain ⟨hb0, hb1⟩ := hb m hm
  have hE0 : 0 ≤ E m := by simpa using hE m hm (K m)
  have hpos : 0 < ρb m ^ 2 + E m := by positivity
  refine ⟨Real.sqrt_pos.2 hpos, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hb1),
    fun k hk => ?_⟩
  have hf := floor_of_layers_approx (s := fun k => (S m k).rho ^ 2) (h0 m hm) (hstep m hm)
    (hh m hm) (he m) k hk
  have hsq : (S m k).rho ^ 2 ≤ ρb m ^ 2 + E m := hf.trans (by linarith [hE m hm k])
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

/-- **(A_L²) from a summable error**: as `relFloor_of_layers_approx`, with `E_m` the tail
`Σ' e_m(j + K m)` of a summable error. -/
theorem relFloor_of_summable {S : ℕ → ℕ → Slab} {ρb : ℕ → ℝ} {K : ℕ → ℕ} {h e : ℕ → ℕ → ℝ}
    (hs : ∀ m, 0 < m → Summable (e m))
    (hb : ∀ m, 0 < m → 0 < ρb m ∧ ρb m ^ 2 + ∑' j, e m (j + K m) < 1)
    (h0 : ∀ m, 0 < m → (S m (K m)).rho ^ 2 ≤ ρb m ^ 2)
    (hstep : ∀ m, 0 < m → ∀ k, K m ≤ k →
      (S m (k + 1)).rho ^ 2 ≤ max ((S m k).rho ^ 2) (h m k) + e m k)
    (hh : ∀ m, 0 < m → ∀ k, K m ≤ k → h m k ≤ ρb m ^ 2) (he : ∀ m k, 0 ≤ e m k) :
    RelFloor S (fun m => Real.sqrt (ρb m ^ 2 + ∑' j, e m (j + K m))) K :=
  relFloor_of_layers_approx hb h0 hstep hh he fun m hm k => Ico_sum_le_tail (he m) (hs m hm) (K m) k

/-! ## 3. The rate of the new layer across a fixed physical slab -/

section Layer

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **A per-step rate on an invariant layer stacks**: if `Q` maps `W` into itself and contracts it by
`e^{−c}`, then `Qⁿ` contracts `W` by `e^{−c n}`. -/
theorem layer_contr_pow {π : α → ℝ} {Q : Matrix α α ℝ} {W : Set (α → ℝ)} {c : ℝ}
    (hinv : ∀ w ∈ W, Q *ᵥ w ∈ W)
    (hstep : ∀ w ∈ W, nsq π (Q *ᵥ w) ≤ Real.exp (-c) ^ 2 * nsq π w) :
    ∀ n : ℕ, ∀ w ∈ W, nsq π ((Q ^ n) *ᵥ w) ≤ Real.exp (-(c * n)) ^ 2 * nsq π w := by
  intro n
  induction n with
  | zero => intro w _; simp
  | succ n ih =>
    intro w hw
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    have e : Real.exp (-(c * ((n + 1 : ℕ) : ℝ))) = Real.exp (-(c * n)) * Real.exp (-c) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [e]
    calc nsq π ((Q ^ n) *ᵥ (Q *ᵥ w)) ≤ Real.exp (-(c * n)) ^ 2 * nsq π (Q *ᵥ w) :=
          ih _ (hinv w hw)
      _ ≤ Real.exp (-(c * n)) ^ 2 * (Real.exp (-c) ^ 2 * nsq π w) :=
          mul_le_mul_of_nonneg_left (hstep w hw) (sq_nonneg _)
      _ = (Real.exp (-(c * n)) * Real.exp (-c)) ^ 2 * nsq π w := by ring

/-- `e^{−c n} ≤ e^{−c τ / a}` when the `n` steps of spacing `a > 0` cover the thickness `τ`, `c ≥ 0`. -/
theorem exp_neg_mul_le_of_slab {a c τ : ℝ} {n : ℕ} (ha : 0 < a) (hc : 0 ≤ c)
    (hn : τ ≤ n * a) : Real.exp (-(c * n)) ≤ Real.exp (-(c * τ / a)) := by
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h1 : τ / a ≤ n := (div_le_iff₀ ha).2 hn
  calc c * τ / a = c * (τ / a) := by ring
    _ ≤ c * n := mul_le_mul_of_nonneg_left h1 hc

/-- **The new layer across a slab of physical thickness `τ`**: per-step rate `e^{−c}` on an invariant
layer, spacing `a > 0`, `n a ≥ τ` give the slab rate `e^{−c τ / a}`. -/
theorem layer_rate_slab {π : α → ℝ} (hπ : ∀ x, 0 ≤ π x) {Q : Matrix α α ℝ} {W : Set (α → ℝ)}
    {c a τ : ℝ} {n : ℕ} (ha : 0 < a) (hc : 0 ≤ c) (hn : τ ≤ n * a)
    (hinv : ∀ w ∈ W, Q *ᵥ w ∈ W)
    (hstep : ∀ w ∈ W, nsq π (Q *ᵥ w) ≤ Real.exp (-c) ^ 2 * nsq π w) :
    ∀ w ∈ W, nsq π ((Q ^ n) *ᵥ w) ≤ Real.exp (-(c * τ / a)) ^ 2 * nsq π w := by
  intro w hw
  refine (layer_contr_pow hinv hstep n w hw).trans (mul_le_mul_of_nonneg_right ?_ (nsq_nonneg hπ w))
  exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_mul_le_of_slab ha hc hn) 2

/-- **The Markov form**: `Contr π Q (e^{−c})`, `a > 0`, `n a ≥ τ` give `ρ(Qⁿ) ≤ e^{−c τ / a}`. -/
theorem maxCorr_slab_le_of_stepGap {π : α → ℝ} {Q : Matrix α α ℝ} (M : Markov π Q) {c a τ : ℝ}
    {n : ℕ} (ha : 0 < a) (hc : 0 ≤ c) (hn : τ ≤ n * a) (h : Contr π Q (Real.exp (-c))) :
    maxCorr π (Q ^ n) ≤ Real.exp (-(c * τ / a)) := by
  have h1 : maxCorr π (Q ^ n) ≤ Real.exp (-c) ^ n :=
    maxCorr_le_of_contr (M.pow n) (Contr.pow M.stat h n)
  have h2 : Real.exp (-c) ^ n = Real.exp (-(c * n)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h2] at h1
  exact h1.trans (exp_neg_mul_le_of_slab ha hc hn)

end Layer

/-- The layer rate along the zoom: `e^{−c τ / a_k}`, `a_k = a₀ / 2^k`. -/
def layerRate (a₀ c τ : ℝ) (k : ℕ) : ℝ := Real.exp (-(c * τ / aZ a₀ k))

theorem succ_le_two_pow (k : ℕ) : (k : ℝ) + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith

theorem layerRate_nonneg (a₀ c τ : ℝ) (k : ℕ) : 0 ≤ layerRate a₀ c τ k := (Real.exp_pos _).le

/-- **The layer rate is below a geometric sequence**: `e^{−c τ / a_k} ≤ (e^{−c τ / a₀})^{k+1}`. -/
theorem layerRate_le_geom {a₀ c τ : ℝ} (hc : 0 ≤ c * τ / a₀) (k : ℕ) :
    layerRate a₀ c τ k ≤ Real.exp (-(c * τ / a₀)) ^ (k + 1) := by
  unfold layerRate aZ
  rw [div_div_eq_mul_div, ← Real.exp_nat_mul]
  refine Real.exp_le_exp.2 ?_
  have h2 := succ_le_two_pow k
  have e1 : c * τ * 2 ^ k / a₀ = (c * τ / a₀) * 2 ^ k := by ring
  rw [e1]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h2 hc]

/-- **The layer rates are summable along the zoom.** -/
theorem layerRate_summable {a₀ c τ : ℝ} (hc : 0 < c * τ / a₀) :
    Summable (layerRate a₀ c τ) := by
  have hr0 : 0 ≤ Real.exp (-(c * τ / a₀)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(c * τ / a₀)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hg : Summable fun k : ℕ => Real.exp (-(c * τ / a₀)) ^ (k + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hr0 hr1)
  exact Summable.of_nonneg_of_le (layerRate_nonneg a₀ c τ) (layerRate_le_geom hc.le) hg

/-- **The layer rate tends to `0` along the zoom.** -/
theorem layerRate_tendsto_zero {a₀ c τ : ℝ} (hc : 0 < c * τ / a₀) :
    Tendsto (layerRate a₀ c τ) atTop (𝓝 0) :=
  (layerRate_summable hc).tendsto_atTop_zero

/-- **Below every `ρb > 0` from some zoom on.** -/
theorem layerRate_eventually_le {a₀ c τ ρb : ℝ} (hc : 0 < c * τ / a₀) (hρb : 0 < ρb) :
    ∃ K₀, ∀ k, K₀ ≤ k → layerRate a₀ c τ k ≤ ρb := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 ((layerRate_tendsto_zero hc).eventually_lt_const hρb)
  exact ⟨K₀, fun k hk => (hK₀ k hk).le⟩

#print axioms nsq_add_le_sq
#print axioms contr_of_approxSplit
#print axioms contr_sqrt_of_approxSplit
#print axioms refine_step_approx
#print axioms max_sq_add_le
#print axioms refine_step_sq
#print axioms floor_of_layers_approx
#print axioms Ico_sum_le_tail
#print axioms exists_tail_le
#print axioms relFloor_of_layers_approx
#print axioms relFloor_of_summable
#print axioms layer_contr_pow
#print axioms exp_neg_mul_le_of_slab
#print axioms layer_rate_slab
#print axioms maxCorr_slab_le_of_stepGap
#print axioms succ_le_two_pow
#print axioms layerRate_le_geom
#print axioms layerRate_summable
#print axioms layerRate_tendsto_zero
#print axioms layerRate_eventually_le

end MassGap.LayerRate
