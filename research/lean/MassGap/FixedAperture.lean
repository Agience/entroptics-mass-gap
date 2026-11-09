import Mathlib
import MassGap.FineEnd
import MassGap.ApertureGap

/-!
# MassGap.FixedAperture — the fine end inside a fixed physical aperture, then the aperture grows

The aperture is a box of fixed physical side `L`. The owner's step: zooming finer does not change the
aperture. So the fine end is split in two. First hold `L` fixed and refine the spacing inside it;
then let `L` grow.

**Convention.** Zoom `k` is the physical spacing `a_k = a₀/2ᵏ` (`aZ a₀ k`), the same at every
aperture. Apertures are indexed by `m : ℕ`, the physical side `L_m = m a₀` (`LA a₀ m`), so at zoom `k`
the box has `m·2ᵏ` cells per side, an integer, and no non-integer side arises. `gL m k` is the gap
read in the box of side `L_m` at spacing `a_k`, `rLat k` the observer's reading at spacing `a_k`,
`ratio (gL m) rLat k` the box gap in observer units. `k → ∞` at fixed `m` is the continuum limit in a
fixed box; `m → ∞` at fixed `k` is infinite volume at a fixed spacing.

**Sector.** `gL m k` is read as the full transfer-matrix gap of the periodic box, every flux
(torelon) sector included. In a confining theory it is then `min(glueball mass, flux energy ∝ σ L)`
and tends to the glueball mass as `L` grows, which is what lets `VolumeLink` hold. (A) and (B) are
blind to which sector carries the gap: a flux energy growing with `L` satisfies both
(`su2_control`); only `VolumeLink` rules it out as an infinite-volume gap (`su2_not_volumeLink`).

## 1. A floor that depends only on the budget (`uniform_floor`)

`FineEnd.noFade_of_stepLoss` gives a floor whose value depends on the reading. Here the floor depends
only on the budget `ε`, the zoom `K` and a lower bound `c₀` on the reading at `K`: the quantifier
over the reading comes after the floor. The per-step factor is `1 − ε ≥ e^{−ε/(1−ε)}`
(`one_sub_ge_exp`, valid on all of `[0, 1)`), and `ε/(1−ε)` is summable with `ε`
(`adj_summable`), so the floor is `c₀ e^{−Σ_{i} ε(i+K)/(1−ε(i+K))}`.

## 2. The split

* (A) `FixedApertureFloor gL rLat c K`: at every aperture `m > 0`, the box gap in observer units has
  the floor `c m > 0` from zoom `K m` on: the continuum limit inside a fixed box keeps a positive
  gap. `fixedApertureFloor_of_fineEndStep`: `FineEndStep (gL m) rLat` at every `m > 0` gives such
  witnesses (the step statement of `FineEnd`, read at fixed `L`).
* (B) `UniformInAperture c K`: eventually in `m`, the floors stay above one `c₀ > 0` and the zooms
  where they start stay below one `K₀`. `UniformFloorsOnly c` is (B) without the zoom bound.
* `VolumeLink gL gLat rLat`: at every spacing, a lower bound on the box ratio eventually in `m` is a
  lower bound on the ratio of `gLat`. `volumeLink_of_tendsto`: it holds when the box gaps converge to
  `gLat k` as `m → ∞` at every spacing.

`noFade_of_split`: (A) ∧ (B) ∧ `VolumeLink` ⇒ `NoFadeAtFineEnd gLat rLat`. With link 3
(`OneScale`), `ratioInvariant_of_split` gives `RatioInvariant`.

`UniformStep gL rLat`: one budget `ε`, one zoom `K` and one `c₀ > 0` serve every aperture
(`c₀ ≤ ratio (gL m) rLat K` and the step loss within `ε` from `K` on, at every `m > 0`).
`fineEndStep_of_uniformStep`: it gives (A) in the step form at every `m`; `split_of_uniformStep`:
it gives (A) and (B) with constant witnesses (`uniform_floor`); `noFade_of_uniformStep`: with
`VolumeLink`, `NoFadeAtFineEnd gLat rLat`.

## 3. Controls

* `threshold_needed`: the bound `K m ≤ K₀` in (B) cannot be dropped. The reading `1` from zoom `m`
  on and `fade k` before has (A) with floor `1` at every `m`, satisfies `UniformFloorsOnly`, has the
  volume link to `fade`, and `fade` has no floor. The two limits do not commute without it.
* `u1_control` (4D `U(1)`; must fail (B)). `gU1 a₀ m k = (2/a_k) sin(π a_k / L_m)`: a one-mode model
  of the photon box gap, the lowest periodic lattice momentum `|p̂| = (2/a) sin(p a/2)` at
  `p = 2π/L`, with the massless Hamiltonian dispersion `ω = |p̂|` (the Euclidean transfer energy
  `(2/a) asinh(a|p̂|/2)` of the Python check agrees with it to relative order `a²/L²`), `rLat ≡ 1`.
  `4/L ≤ gU1 ≤ 2π/L` (`gU1_ge`, `gU1_le`). (A) holds at every `m` (floor `4/L_m` from zoom `1`), every
  family of (A) witnesses fails (B), the volume link holds with `gLat ≡ 0` (at fixed spacing the box
  gap tends to `0` as `L → ∞`), and `NoFadeAtFineEnd 0 1` fails. (B) is where the photon is excluded.
* `su2_control` (2D `SU(2)` heat kernel, rLat ≡ 1). The box gap is `3κL` at every spacing: the first
  excited level of `ApertureGap.ymZ`, the energy `κ L (n² − 1)` at `n = 2` of one unit of flux around
  the periodic box (a torelon energy, not a glueball). (A) holds with no loss (`FineEndStep` with
  `ε ≡ 0`) and (B) holds. `su2_not_volumeLink`: the flux energy grows without bound in `L`, so no
  real `gLat` satisfies `VolumeLink`; the link is what separates a flux energy from an infinite-volume
  gap (2D has no propagating state).

## 4. What the existing aperture tools give toward (A)

`ApertureGap.aperture_gap` bounds the slice kernel `kT` by its cross ratio `apTheta = (1 − m²)/(1 + m²)`,
`m = RectTransfer.kTmin = e^{−β(spMax + 2 tpMax)}`, and composes it over `n` steps as `apThetaⁿ`
(`crossRatio_iter`). At fixed physical `L` the physical slab of thickness `τ` has `n = τ/a` steps.

* `one_sub_apTheta_le`: `1 − apTheta ≤ 2 m²`.
* `one_sub_mul_le_pow`: `1 − n(1 − θ) ≤ θⁿ` at `θ ≥ 0` (Bernoulli).
* `apTheta_slab_tendsto_one`: along any zoom line with `n_k m_k² → 0`, `apTheta_kⁿᵏ → 1`.

The rest of this section is prose and numerics, not Lean. With `θⁿ → 1` the bound
`(1 − θⁿ) cyc(n)² ≤ (1 + θⁿ) cyc(2n)` of `aperture_gap` tends to the trivial `0 ≤ 2 cyc(2n)`.
`spMax + 2 tpMax` is `30` times the number of cross-section sites, `(L/a)³` at fixed `L`, so
`log(1/m) = 30 β (L/a)³` and `n m² → 0` faster than any power of `a` (numerics:
`research/code/fixed_aperture_checks.py`, section 2). The loss is not only in the crude constant
`kTmin`. The least cross-ratio constant of the one-step kernel is `tanh(D₁/2)`, `D₁` its Hilbert
projective diameter; in the exact 2D heat-kernel models (section 1) `D₁` grows linearly in `L/a`,
and the composed bound `tanh(D₁/2)^{L/a}` tends to `1`, while the kernel over the fixed physical slab
has the same diameter at every zoom. A zoom-uniform bound must be stated on the slab kernel, not
composed from one step. For the slab kernel the diameter is a supremum over all fine
configurations: in the 4D free-photon model (section 3) the slab cross ratio on the lowest box mode
grows like `(L/a)²` at fixed physical slab thickness. So, numerically (Python sections 1 and 3; not
proved here), no zoom-uniform cross-ratio bound on the fixed-`L` slab kernel holds in 4D, even for a
free field with a periodic box gap `≈ 2π/L` at every zoom.
The quantitative tools (`kTmin`, cross ratio, Birkhoff composition) are suprema over fine
configurations and do not reach (A). Definiteness and injectivity (`SliceKernelDefinite`,
`KernelInjective`) are statements on the weighted (L²) form of the kernel, the form in which (A) would
have to be read, but they carry no rate: they give a positive gap at each zoom, not a floor on it.

No declaration here proves (A) or (B) for the 4D `SU(N)` Wilson measure or ties `gL`, `rLat`,
`gLat` to it.

DERIVED (module-wide): `1` the reading of `rLat` in the controls and the floor of
`threshold_needed`; `2` in `a₀/2ᵏ` the block factor of one zoom step, in `2/a` the lattice momentum
and in `2 m²` from `(1 + m²) − (1 − m²)`; `4` in `4/L` from Jordan's `sin x ≥ 2x/π`; `2π` the
lowest periodic momentum; `3` in
`3κL` the Casimir difference `n² − 1` at `n = 2`; `1/2` the threshold for `ε/(1−ε) ≤ 2ε`; `0` the
first zoom and the sign of every bound.
-/

noncomputable section

namespace MassGap.FixedAperture

open Filter Topology
open MassGap.ApertureInvariance MassGap.EdgeCost MassGap.NoTransition MassGap.FineEnd

/-! ## 1. A floor that depends only on the budget -/

/-- `1 − x ≥ e^{−x/(1−x)}` on `[0, 1)`. -/
theorem one_sub_ge_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : Real.exp (-(x / (1 - x))) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  have hmul : (x / (1 - x) + 1) * (1 - x) = 1 := by
    rw [add_mul, div_mul_cancel₀ x hpos.ne']; ring
  have hy : 0 < x / (1 - x) + 1 := by
    have : 0 ≤ x / (1 - x) := div_nonneg h0 hpos.le
    linarith
  have he := Real.add_one_le_exp (x / (1 - x))
  rw [Real.exp_neg]
  calc (Real.exp (x / (1 - x)))⁻¹ ≤ (x / (1 - x) + 1)⁻¹ := inv_anti₀ hy he
    _ = 1 - x := inv_eq_of_mul_eq_one_right hmul

/-- The loss in the exponent: `ε/(1 − ε)`. -/
def adj (ε : ℕ → ℝ) (k : ℕ) : ℝ := ε k / (1 - ε k)

theorem adj_nonneg {ε : ℕ → ℝ} (hb : StepBudget ε) (k : ℕ) : 0 ≤ adj ε k :=
  div_nonneg (hb.1 k).1 (by linarith [(hb.1 k).2])

/-- `ε/(1 − ε)` is summable with `ε`.

DERIVED: `1/2` the threshold for `ε/(1−ε) ≤ 2ε`. -/
theorem adj_summable {ε : ℕ → ℝ} (hb : StepBudget ε) : Summable (adj ε) := by
  refine Summable.of_norm_bounded_eventually_nat (hb.2.mul_left 2) ?_
  filter_upwards [hb.2.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (adj_nonneg hb k)]
  unfold adj
  have h0 := (hb.1 k).1
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The reading after `n` steps is at least `f K · e^{−Σ ε/(1−ε)}`**, at every loss below `1`. -/
theorem stepLoss_lower {f ε : ℕ → ℝ} {K : ℕ} (hb : StepBudget ε) (hpos : 0 ≤ f K)
    (hstep : StepLoss f ε K) (n : ℕ) :
    f K * Real.exp (-(∑ i ∈ Finset.range n, adj ε (i + K))) ≤ f (n + K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := hstep (n + K) (by omega)
    have h0 := (hb.1 (n + K)).1
    have h1 := (hb.1 (n + K)).2
    have hX : 0 ≤ f K * Real.exp (-(∑ i ∈ Finset.range n, adj ε (i + K))) :=
      mul_nonneg hpos (Real.exp_pos _).le
    rw [show n + 1 + K = n + K + 1 by omega]
    calc f K * Real.exp (-(∑ i ∈ Finset.range (n + 1), adj ε (i + K)))
        = Real.exp (-(adj ε (n + K))) * (f K * Real.exp (-(∑ i ∈ Finset.range n, adj ε (i + K)))) := by
          rw [Finset.sum_range_succ, neg_add, Real.exp_add]; ring
      _ ≤ (1 - ε (n + K)) * (f K * Real.exp (-(∑ i ∈ Finset.range n, adj ε (i + K)))) :=
          mul_le_mul_of_nonneg_right (one_sub_ge_exp h0 h1) hX
      _ ≤ (1 - ε (n + K)) * f (n + K) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ f (n + K + 1) := hs

/-- **A floor that depends only on the budget, the zoom and the starting bound**: one `c > 0` serves
every reading `f` with `c₀ ≤ f K` and step losses within `ε` from `K` on. -/
theorem uniform_floor {ε : ℕ → ℝ} {K : ℕ} {c₀ : ℝ} (hb : StepBudget ε) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℕ → ℝ, c₀ ≤ f K → StepLoss f ε K → ∀ k, K ≤ k → c ≤ f k := by
  refine ⟨c₀ * Real.exp (-(∑' i, adj ε (i + K))), mul_pos hc₀ (Real.exp_pos _),
    fun f hf hs k hk => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + K := ⟨k - K, by omega⟩
  have hs' : Summable (fun i => adj ε (i + K)) := (summable_nat_add_iff K).mpr (adj_summable hb)
  have hle : ∑ i ∈ Finset.range n, adj ε (i + K) ≤ ∑' i, adj ε (i + K) :=
    hs'.sum_le_tsum _ (fun i _ => adj_nonneg hb _)
  calc c₀ * Real.exp (-(∑' i, adj ε (i + K)))
      ≤ f K * Real.exp (-(∑ i ∈ Finset.range n, adj ε (i + K))) :=
        mul_le_mul hf (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (hc₀.le.trans hf)
    _ ≤ f (n + K) := stepLoss_lower hb (hc₀.le.trans hf) hs n

/-! ## 2. The split -/

/-- A floor `c` on `f` from zoom `K` on. -/
def FloorFrom (f : ℕ → ℝ) (c : ℝ) (K : ℕ) : Prop := ∀ k, K ≤ k → c ≤ f k

/-- The physical spacing at zoom `k`: `a_k = a₀/2ᵏ`, the same at every aperture.

DERIVED: `2` the block factor of one zoom step. -/
def aZ (a₀ : ℝ) (k : ℕ) : ℝ := a₀ / 2 ^ k

/-- The physical side of aperture `m`: `L_m = m a₀`, so the box at zoom `k` has `m·2ᵏ` cells. -/
def LA (a₀ : ℝ) (m : ℕ) : ℝ := m * a₀

/-- **(A) at every fixed aperture**: at every `m > 0`, the box gap of side `L_m` in observer units has
the floor `c m > 0` from zoom `K m` on. `gL m k` is the box gap at side `L_m` and spacing `a_k`
(convention of the module header): the full transfer-matrix gap of the periodic box, every flux
sector included. -/
def FixedApertureFloor (gL : ℕ → ℕ → ℝ) (rLat : ℕ → ℝ) (c : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ m, 0 < m → 0 < c m ∧ FloorFrom (ratio (gL m) rLat) (c m) (K m)

/-- **(B) uniformity in the aperture**: eventually in `m`, the floors stay above one `c₀ > 0` and the
zooms where they start stay below one `K₀`. -/
def UniformInAperture (c : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K₀ : ℕ, ∀ᶠ m in atTop, c₀ ≤ c m ∧ K m ≤ K₀

/-- **(B) without the zoom bound**: eventually in `m`, the floors stay above one `c₀ > 0`. -/
def UniformFloorsOnly (c : ℕ → ℝ) : Prop := ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ m in atTop, c₀ ≤ c m

/-- **The volume link**: at every spacing `a_k`, a lower bound on the box ratio eventually in `m` is a
lower bound on the ratio of `gLat`. -/
def VolumeLink (gL : ℕ → ℕ → ℝ) (gLat rLat : ℕ → ℝ) : Prop :=
  ∀ k c, (∀ᶠ m in atTop, c ≤ ratio (gL m) rLat k) → c ≤ ratio gLat rLat k

/-- **The volume link holds when the box gaps converge** to `gLat k` as `m → ∞` at every spacing. -/
theorem volumeLink_of_tendsto {gL : ℕ → ℕ → ℝ} {gLat rLat : ℕ → ℝ}
    (h : ∀ k, Tendsto (fun m => gL m k) atTop (𝓝 (gLat k))) : VolumeLink gL gLat rLat := by
  intro k c hc
  have ht : Tendsto (fun m => ratio (gL m) rLat k) atTop (𝓝 (ratio gLat rLat k)) :=
    (h k).div_const (rLat k)
  exact ge_of_tendsto ht hc

/-- **The step statement at every fixed aperture gives (A).** -/
theorem fixedApertureFloor_of_fineEndStep {gL : ℕ → ℕ → ℝ} {rLat : ℕ → ℝ}
    (h : ∀ m, 0 < m → FineEndStep (gL m) rLat) : ∃ c K, FixedApertureFloor gL rLat c K := by
  have hw : ∀ m : ℕ, ∃ (c : ℝ) (K : ℕ), 0 < m → 0 < c ∧ FloorFrom (ratio (gL m) rLat) c K := by
    intro m
    by_cases hm : 0 < m
    · obtain ⟨c, hc, ht⟩ := noFadeAtFineEnd_of_fineEndStep (h m hm)
      obtain ⟨K, hK⟩ := eventually_atTop.1 ht
      exact ⟨c, K, fun _ => ⟨hc, fun k hk => hK k hk⟩⟩
    · exact ⟨1, 0, fun h' => absurd h' hm⟩
  choose c K hcK using hw
  exact ⟨c, K, fun m hm => hcK m hm⟩

/-- **(A) ∧ (B) ∧ the volume link ⇒ `NoFadeAtFineEnd`.** -/
theorem noFade_of_split {gL : ℕ → ℕ → ℝ} {gLat rLat : ℕ → ℝ} {c : ℕ → ℝ} {K : ℕ → ℕ}
    (hA : FixedApertureFloor gL rLat c K) (hB : UniformInAperture c K)
    (hV : VolumeLink gL gLat rLat) : NoFadeAtFineEnd gLat rLat := by
  obtain ⟨c₀, hc₀, K₀, hev⟩ := hB
  refine ⟨c₀, hc₀, eventually_atTop.2 ⟨K₀, fun k hk => hV k c₀ ?_⟩⟩
  filter_upwards [hev, eventually_gt_atTop 0] with m hm hm0
  exact hm.1.trans ((hA m hm0).2 k (hm.2.trans hk))

/-- **With link 3, the split gives `RatioInvariant`.** -/
theorem ratioInvariant_of_split {gL : ℕ → ℕ → ℝ} {gLat rLat : ℕ → ℝ} {c : ℕ → ℝ} {K : ℕ → ℕ}
    (h3 : OneScale gLat rLat) (hA : FixedApertureFloor gL rLat c K) (hB : UniformInAperture c K)
    (hV : VolumeLink gL gLat rLat) : ∃ q C : ℝ, 0 < q ∧ RatioInvariant gLat rLat q C :=
  (ratioInvariant_iff_links h3).2 (noFade_of_split hA hB hV)

/-- **One budget, one zoom and one starting floor for every aperture.** -/
def UniformStep (gL : ℕ → ℕ → ℝ) (rLat : ℕ → ℝ) : Prop :=
  ∃ (ε : ℕ → ℝ) (K : ℕ) (c₀ : ℝ), StepBudget ε ∧ 0 < c₀ ∧
    ∀ m, 0 < m → c₀ ≤ ratio (gL m) rLat K ∧ StepLoss (ratio (gL m) rLat) ε K

/-- **The uniform step statement gives the step statement at every fixed aperture.** -/
theorem fineEndStep_of_uniformStep {gL : ℕ → ℕ → ℝ} {rLat : ℕ → ℝ} (h : UniformStep gL rLat)
    {m : ℕ} (hm : 0 < m) : FineEndStep (gL m) rLat := by
  obtain ⟨ε, K, c₀, hb, hc₀, hs⟩ := h
  exact ⟨ε, K, hb, hc₀.trans_le (hs m hm).1, (hs m hm).2⟩

/-- **The uniform step statement gives (A) and (B)**, with constant witnesses. -/
theorem split_of_uniformStep {gL : ℕ → ℕ → ℝ} {rLat : ℕ → ℝ} (h : UniformStep gL rLat) :
    ∃ c K, FixedApertureFloor gL rLat c K ∧ UniformInAperture c K := by
  obtain ⟨ε, K, c₀, hb, hc₀, hs⟩ := h
  obtain ⟨c, hc, hfl⟩ := uniform_floor (K := K) hb hc₀
  exact ⟨fun _ => c, fun _ => K, fun m hm => ⟨hc, hfl _ (hs m hm).1 (hs m hm).2⟩,
    ⟨c, hc, K, Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩⟩⟩

/-- **The uniform step statement and the volume link give `NoFadeAtFineEnd`.** -/
theorem noFade_of_uniformStep {gL : ℕ → ℕ → ℝ} {gLat rLat : ℕ → ℝ} (h : UniformStep gL rLat)
    (hV : VolumeLink gL gLat rLat) : NoFadeAtFineEnd gLat rLat := by
  obtain ⟨c, K, hA, hB⟩ := split_of_uniformStep h
  exact noFade_of_split hA hB hV

/-! ## 3. Controls -/

/-- The reading `1` from zoom `m` on and `fade k` before. -/
def gThr (m k : ℕ) : ℝ := if m ≤ k then 1 else fade k

/-- **The threshold bound in (B) cannot be dropped.** `gThr` has (A) with floor `1` from zoom `m` at
every aperture `m`, the floors satisfy `UniformFloorsOnly` ((B) without the zoom bound), the volume
link to `fade` holds, and `fade` has no floor.

DERIVED: `1` the floor. -/
theorem threshold_needed :
    FixedApertureFloor gThr (fun _ => 1) (fun _ => 1) (fun m => m) ∧
      UniformFloorsOnly (fun _ => 1) ∧
      VolumeLink gThr fade (fun _ => 1) ∧ ¬ NoFadeAtFineEnd fade (fun _ => 1) := by
  refine ⟨fun m _ => ⟨one_pos, fun k hk => ?_⟩, ⟨1, one_pos, Eventually.of_forall fun _ => le_rfl⟩,
    fun k c hc => ?_, links_not_sufficient.2.2⟩
  · have hmk : m ≤ k := hk
    simp [ratio, gThr, hmk]
  · obtain ⟨m, hm1, hm2⟩ := (hc.and (eventually_gt_atTop k)).exists
    have hn : ¬ m ≤ k := not_le.2 hm2
    simpa [ratio, gThr, hn] using hm1

theorem aZ_pos {a₀ : ℝ} (ha : 0 < a₀) (k : ℕ) : 0 < aZ a₀ k := div_pos ha (pow_pos two_pos k)

theorem LA_pos {a₀ : ℝ} (ha : 0 < a₀) {m : ℕ} (hm : 0 < m) : 0 < LA a₀ m :=
  mul_pos (Nat.cast_pos.2 hm) ha

/-- A one-mode model of the 4D photon's periodic box gap at aperture `m` and spacing `a_k`: the lowest
periodic lattice momentum `(2/a) sin(π a/L)` (`p = 2π/L`), with the massless Hamiltonian dispersion
`ω = |p̂|`.

DERIVED: `2` in `2/a` and `π` in `π a/L` from `|p̂| = (2/a) sin(p a/2)` at `p = 2π/L`. -/
def gU1 (a₀ : ℝ) (m k : ℕ) : ℝ := 2 / aZ a₀ k * Real.sin (Real.pi * aZ a₀ k / LA a₀ m)

/-- `gU1 ≤ 2π/L` at every spacing.

DERIVED: `2π` the lowest periodic momentum. -/
theorem gU1_le {a₀ : ℝ} (ha : 0 < a₀) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    gU1 a₀ m k ≤ 2 * Real.pi / LA a₀ m := by
  have hA := aZ_pos ha k
  have hL := LA_pos ha hm
  have hA' := hA.ne'
  have hx : 0 ≤ Real.pi * aZ a₀ k / LA a₀ m := div_nonneg (mul_nonneg Real.pi_pos.le hA.le) hL.le
  unfold gU1
  calc 2 / aZ a₀ k * Real.sin (Real.pi * aZ a₀ k / LA a₀ m)
      ≤ 2 / aZ a₀ k * (Real.pi * aZ a₀ k / LA a₀ m) :=
        mul_le_mul_of_nonneg_left (Real.sin_le hx) (div_nonneg two_pos.le hA.le)
    _ = 2 * Real.pi / LA a₀ m := by
        rw [div_mul_div_comm, show 2 * (Real.pi * aZ a₀ k) = aZ a₀ k * (2 * Real.pi) by ring,
          mul_div_mul_left _ _ hA']

/-- `gU1 ≥ 4/L` from zoom `1` on (the box has at least two cells per side).

DERIVED: `4` from Jordan's `sin x ≥ 2x/π` on `[0, π/2]`; `1` the first zoom with `m·2ᵏ ≥ 2` for every `m ≥ 1`. -/
theorem gU1_ge {a₀ : ℝ} (ha : 0 < a₀) {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : 1 ≤ k) :
    4 / LA a₀ m ≤ gU1 a₀ m k := by
  have hA := aZ_pos ha k
  have hL := LA_pos ha hm
  have hA' := hA.ne'
  have hL' := hL.ne'
  have hπ := Real.pi_pos
  have hπ' := hπ.ne'
  have hx : 0 ≤ Real.pi * aZ a₀ k / LA a₀ m := div_nonneg (mul_nonneg hπ.le hA.le) hL.le
  have h2k : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
  have h2a : 2 * aZ a₀ k ≤ LA a₀ m := by
    unfold aZ LA
    calc 2 * (a₀ / 2 ^ k) ≤ a₀ := by
          rw [mul_div_assoc', div_le_iff₀ (pow_pos two_pos k)]; nlinarith
      _ ≤ m * a₀ := le_mul_of_one_le_left ha.le hm1
  have hx2 : Real.pi * aZ a₀ k / LA a₀ m ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hL]; nlinarith
  unfold gU1
  calc 4 / LA a₀ m = 2 / aZ a₀ k * (2 / Real.pi * (Real.pi * aZ a₀ k / LA a₀ m)) := by
        first | (field_simp; done) | (field_simp; ring)
    _ ≤ 2 / aZ a₀ k * Real.sin (Real.pi * aZ a₀ k / LA a₀ m) :=
        mul_le_mul_of_nonneg_left (Real.mul_le_sin hx hx2) (div_nonneg two_pos.le hA.le)

/-- `2π/L_m → 0` as the aperture grows. -/
theorem tendsto_two_pi_div_LA {a₀ : ℝ} :
    Tendsto (fun m : ℕ => 2 * Real.pi / LA a₀ m) atTop (𝓝 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi / a₀)).congr fun m => by
    unfold LA; rw [div_div, mul_comm a₀]

/-- **The 4D `U(1)` control** (one-mode periodic model, `rLat ≡ 1`). (A) holds with floor `4/L_m`
from zoom `1`; every family of (A) witnesses fails (B); the volume link holds with `gLat ≡ 0` (at a
fixed spacing the box gap tends to `0` as the box grows); `NoFadeAtFineEnd 0 1` fails. -/
theorem u1_control {a₀ : ℝ} (ha : 0 < a₀) :
    FixedApertureFloor (gU1 a₀) (fun _ => 1) (fun m => 4 / LA a₀ m) (fun _ => 1) ∧
      (∀ c K, FixedApertureFloor (gU1 a₀) (fun _ => 1) c K → ¬ UniformInAperture c K) ∧
      VolumeLink (gU1 a₀) (fun _ => 0) (fun _ => 1) ∧
      ¬ NoFadeAtFineEnd (fun _ => 0) (fun _ => 1) := by
  have ht := tendsto_two_pi_div_LA (a₀ := a₀)
  refine ⟨fun m hm => ⟨div_pos (by norm_num) (LA_pos ha hm), fun k hk => ?_⟩,
    fun c K hA hB => ?_, fun k c hc => ?_, ?_⟩
  · simp only [ratio, div_one]
    exact gU1_ge ha hm hk
  · obtain ⟨c₀, hc₀, K₀, hev⟩ := hB
    have hsmall : ∀ᶠ m : ℕ in atTop, 2 * Real.pi / LA a₀ m < c₀ := ht.eventually (gt_mem_nhds hc₀)
    obtain ⟨m, ⟨⟨hm1, -⟩, hm2⟩, hm0⟩ := ((hev.and hsmall).and (eventually_gt_atTop 0)).exists
    have hfl := (hA m hm0).2 (max (K m) 1) (le_max_left _ _)
    have hle := gU1_le ha hm0 (max (K m) 1)
    simp only [ratio, div_one] at hfl
    linarith
  · have hev : ∀ᶠ m : ℕ in atTop, c ≤ 2 * Real.pi / LA a₀ m := by
      filter_upwards [hc, eventually_gt_atTop 0] with m hm hm0
      simp only [ratio, div_one] at hm
      exact hm.trans (gU1_le ha hm0 k)
    simp only [ratio, div_one]
    exact ge_of_tendsto ht hev
  · rintro ⟨c, hc, ht⟩
    obtain ⟨k, hk⟩ := ht.exists
    simp only [ratio, div_one] at hk
    linarith

/-- The 2D `SU(2)` heat-kernel box gap at aperture `m`: `3κL_m` at every spacing, the energy of one
unit of flux around the periodic box (a torelon energy, not a glueball).

DERIVED: `3` the Casimir difference `n² − 1` at `n = 2`. -/
def gSU2 (κ a₀ : ℝ) (m _k : ℕ) : ℝ := 3 * κ * LA a₀ m

/-- **The 2D `SU(2)` control.** At every `m > 0`, the step statement holds with no loss; (A) holds
with floor `3κL_m` from zoom `0`; (B) holds with `c₀ = 3κa₀`. (A) and (B) do not tell this flux energy
from a glueball gap; `su2_not_volumeLink` does. -/
theorem su2_control {κ a₀ : ℝ} (hκ : 0 < κ) (ha : 0 < a₀) :
    (∀ m, 0 < m → FineEndStep (gSU2 κ a₀ m) (fun _ => 1)) ∧
      FixedApertureFloor (gSU2 κ a₀) (fun _ => 1) (fun m => 3 * κ * LA a₀ m) (fun _ => 0) ∧
      UniformInAperture (fun m => 3 * κ * LA a₀ m) (fun _ => 0) := by
  have h3 : 0 < 3 * κ := mul_pos (by norm_num) hκ
  refine ⟨fun m hm => ⟨fun _ => 0, 0, ⟨fun _ => ⟨le_rfl, one_pos⟩, summable_zero⟩, ?_, ?_⟩,
    fun m hm => ⟨mul_pos h3 (LA_pos ha hm), fun k _ => ?_⟩, ⟨3 * κ * a₀, mul_pos h3 ha, 0, ?_⟩⟩
  · simp only [ratio, div_one, gSU2]; exact mul_pos h3 (LA_pos ha hm)
  · intro k _; simp [ratio, gSU2]
  · simp [ratio, gSU2]
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hLa : a₀ ≤ LA a₀ m := by
      unfold LA; exact le_mul_of_one_le_left ha.le (Nat.one_le_cast.mpr hm)
    exact ⟨show 3 * κ * a₀ ≤ 3 * κ * LA a₀ m from mul_le_mul_of_nonneg_left hLa h3.le, le_rfl⟩

/-- **No real `gLat` satisfies the volume link for the 2D `SU(2)` box gaps**: the flux energy grows
without bound in `L`. -/
theorem su2_not_volumeLink {κ a₀ : ℝ} (hκ : 0 < κ) (ha : 0 < a₀) (gLat : ℕ → ℝ) :
    ¬ VolumeLink (gSU2 κ a₀) gLat (fun _ => 1) := by
  intro hV
  have h := hV 0 (ratio gLat (fun _ => 1) 0 + 1) ?_
  · linarith
  · have ht : Tendsto (fun m : ℕ => 3 * κ * LA a₀ m) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const ha).const_mul_atTop (mul_pos (by norm_num) hκ)
    filter_upwards [ht.eventually_ge_atTop (ratio gLat (fun _ => 1) 0 + 1)] with m hm
    simpa [ratio, gSU2] using hm

/-! ## 4. What the existing aperture tools give toward (A) -/

/-- **`1 − apTheta ≤ 2 kTmin²`.**

DERIVED: `2` from `(1 + m²) − (1 − m²)`. -/
theorem one_sub_apTheta_le (s : Fin 4) (T : {j : Fin 4 // j ≠ s} → ℕ) (β : ℝ) :
    1 - ApertureGap.apTheta s T β ≤ 2 * RectTransfer.kTmin s T β ^ 2 := by
  unfold ApertureGap.apTheta
  have hm := RectTransfer.kTmin_pos (μ := s) (T := T) β
  have hD : 0 < 1 + RectTransfer.kTmin s T β ^ 2 := by positivity
  rw [one_sub_div hD.ne', div_le_iff₀ hD]
  nlinarith [pow_pos hm 2, sq_nonneg (RectTransfer.kTmin s T β ^ 2)]

/-- **Bernoulli**: `1 − n(1 − θ) ≤ θⁿ` for `θ ≥ 0`. -/
theorem one_sub_mul_le_pow {θ : ℝ} (h0 : 0 ≤ θ) (n : ℕ) :
    1 - n * (1 - θ) ≤ θ ^ n := by
  have h := one_add_mul_le_pow (a := θ - 1) (by linarith) n
  rw [show 1 + (θ - 1) = θ by ring] at h
  calc 1 - n * (1 - θ) = 1 + n * (θ - 1) := by ring
    _ ≤ θ ^ n := h

/-- **The composed slab bound is trivial on a fine line**: along a zoom line of cross-sections
`T k`, couplings `β k ≥ 0` and step counts `n k` with `n k · kTmin_k² → 0`, `apTheta_k^{n k} → 1`. -/
theorem apTheta_slab_tendsto_one (s : Fin 4) (T : ℕ → {j : Fin 4 // j ≠ s} → ℕ)
    (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) (n : ℕ → ℕ)
    (h : Tendsto (fun k => (n k : ℝ) * RectTransfer.kTmin s (T k) (b k) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ApertureGap.apTheta s (T k) (b k) ^ n k) atTop (𝓝 1) := by
  have hlow : Tendsto (fun k => 1 - 2 * ((n k : ℝ) * RectTransfer.kTmin s (T k) (b k) ^ 2))
      atTop (𝓝 1) := by
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub (h.const_mul 2)
    rwa [mul_zero, sub_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun k => ?_) (fun k => ?_)
  · have h0 := ApertureGap.apTheta_nonneg s (T k) (hb k)
    have hB := one_sub_mul_le_pow h0 (n k)
    have hc := one_sub_apTheta_le s (T k) (b k)
    have hn : (0 : ℝ) ≤ n k := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hc hn
    have e : (n k : ℝ) * (2 * RectTransfer.kTmin s (T k) (b k) ^ 2)
        = 2 * ((n k : ℝ) * RectTransfer.kTmin s (T k) (b k) ^ 2) := by ring
    linarith
  · exact pow_le_one₀ (ApertureGap.apTheta_nonneg s (T k) (hb k))
      (ApertureGap.apTheta_lt_one s (T k) (b k)).le

#print axioms one_sub_ge_exp
#print axioms adj_summable
#print axioms stepLoss_lower
#print axioms uniform_floor
#print axioms volumeLink_of_tendsto
#print axioms fixedApertureFloor_of_fineEndStep
#print axioms noFade_of_split
#print axioms ratioInvariant_of_split
#print axioms fineEndStep_of_uniformStep
#print axioms split_of_uniformStep
#print axioms noFade_of_uniformStep
#print axioms threshold_needed
#print axioms aZ_pos
#print axioms LA_pos
#print axioms gU1_le
#print axioms gU1_ge
#print axioms tendsto_two_pi_div_LA
#print axioms u1_control
#print axioms su2_control
#print axioms su2_not_volumeLink
#print axioms one_sub_apTheta_le
#print axioms one_sub_mul_le_pow
#print axioms apTheta_slab_tendsto_one

end MassGap.FixedAperture
