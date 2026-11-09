import Mathlib
import MassGap.GlueballArea

/-!
# MassGap.NestedAperture — the zero-flux count as a nesting statement: finer apertures inside a fixed one

The open piece (T) is `ObserverTheory.HiddenCostAt N σ A ℓ`. `GlueballArea.hiddenCostAt_of_uniformGlueball`
reduces it, at the spectral levels of the real zero-flux kernel `trivKN` (`GlueballArea.ZeroFluxLevels`), to a gap
clause (`ZeroFluxGap g₀ E m`) and a count clause (`ZeroFluxCount g₀ E t₀ C`), uniform in the zoom.
`GlueballArea.not_eventually_area_beats_entropy` shows that counting the excited levels by configurations on the
lattice cannot be uniform: the cost per plaquette `σ a t₀` goes to `0` with `a = aRun N β`. This module states the
count clause at a fixed physical resolution `b`, the resolution of the aperture, and splits the excited levels
into those the aperture resolves and those it does not.

The intended reading, in the author's terms (argued, not a theorem): nesting finer apertures inside a fixed one adds no
low-lying no-flux states it cannot count. The aperture is a block lattice of physical cell side `b`; its
configurations (decorated block animals) count `V Kˢ` per size `s` and cost `σ b` of energy per block; whatever
the finer apertures add beyond what the fixed one carries contributes at most `ε` to the excited weight at the
physical time `t₀`. Formally the split is equivalent in strength to `GlueballArea.UniformGlueball`
(`uniformGlueball_of_uniformNest` and `uniformNest_of_uniformGlueball`), and by `resolved_ge` every excited
level below `σ b`, in particular a low-lying glueball, sits in the fine part `NestFine`, not in the counted part.

## 1. The split (defined)

On a family of levels `E : ι → ℝ` with ground `g₀`, a predicate `coarse` (existentially chosen in
`UniformNest`; any partition qualifies) picks the excited levels the aperture resolves; `p : ι → P` assigns them aperture configurations of size `size : P → ℕ`.

* `NestCount g₀ E σ b size coarse p` (the aperture-scale part):
  - `inj`: distinct resolved excited levels have distinct configurations;
  - `gap`: a resolved excited level carried by a configuration of `s` blocks lies at least `σ (b s)` above the
    ground (the aperture-scale gap: `σ b` per block).
* `fineW g₀ E coarse t₀ j`: the heat weight `e^{−(E_j − E_{g₀}) t₀}` of an excited level the aperture does not
  resolve, `0` otherwise.
* `NestFine g₀ E coarse t₀ ε` (finer apertures add nothing the coarse one cannot count): the sub-resolution excited
  weight `Σ_j fineW j` is summable and at most `ε` (the reading; formally the weight of the excited levels outside
  `coarse`, which includes every level below `σ b`: `resolved_ge`).
* `resolved_ge` (proved): with sizes `≥ 1` and `σ b ≥ 0`, every resolved excited level lies at least `σ b` above
  the ground.

## 2. The reduction (proved)

* **`count_of_nest`**: `NestCount`, `NestFine ε`, `t₀ ≥ 0`, sizes `≥ 1`, `GlueballArea.LoopEntropy size V K`
  (`V, K ≥ 0`) and `q = K e^{−σ b t₀} < 1` give `ZeroFluxCount g₀ E t₀ (V q/(1 − q) + ε)`.
* `count_of_nest_log`: the same with `log K < σ b t₀` (`K > 0`) in place of `q < 1`.
* `UniformNest N size m t₀ σ b ε ℓ`: eventually in `β`, at every power-of-two side `n ≥ 2` with
  `n a ∈ [2ℓ, 5ℓ]` and every step `i`, the real `trivKN N β n i` has spectral levels (`ZeroFluxLevels`) with gap
  `m`, a split satisfying `NestCount` (into the fixed configuration type `P`, at the fixed `σ`, `b`) and
  `NestFine` at the fixed `t₀`, `ε`. `P`, `size`, `m`, `t₀`, `σ`, `b`, `ε` are chosen before `β`.
* `uniformGlueball_of_uniformNest`: `UniformNest` with an entropy bound and `log K < σ b t₀` gives
  `GlueballArea.UniformGlueball N m t₀ (V q/(1 − q) + ε) ℓ`.
* **`hiddenCostAt_of_uniformNest`**: with `0 ≤ t₀ ≤ 2ℓ`, it gives
  `ObserverTheory.HiddenCostAt N m (2 (V q/(1 − q) + ε) e^{m t₀}) ℓ`. Every constant (`m`, `V`, `K`, `σ b t₀`, `ε`,
  `t₀`) is fixed before `β`, so none depends on `a`.

## 3. The aperture's configurations (proved)

* `cells ℓ b = ⌈5ℓ/b⌉₊`, `window_covered`: a block lattice of `cells ℓ b` cells of side `b` per direction covers
  every box of the window (`n a ≤ 5ℓ ≤ cells ℓ b · b`). `cells` depends on `ℓ/b` only (`cells_rescale`).
  In the theorems below `nB` is a free parameter, not tied to `cells ℓ b`. The intended choice `nB = cells ℓ b`
  makes `V = dim² nB^dim` grow like `(ℓ/b)^dim`; `HiddenCostAt` is stated per `ℓ`, so the uniformity in `ℓ` that
  `ObserverTheory.BindingSU` needs is not supplied here.
* `hiddenCostAt_of_uniformNest_block`: undecorated block animals (`GlueballArea.LoopConf dim nB`, touch-connected
  plaquette sets of the block lattice) as the aperture's configurations: `V = dim² nB^dim`, `K = (16 dim + 1)²`
  (`GlueballArea.loopEntropy_hypercubic`), so (T) holds with
  `A = 2 (dim² nB^dim q/(1 − q) + ε) e^{m t₀}`, `q = (16 dim + 1)² e^{−σ b t₀}`, given
  `log (16 dim + 1)² < σ b t₀`.
* `loopEntropy_decorated`: decorations. Configurations `Q` over base configurations `P` (`π : Q → P`,
  `size_P(π d) ≤ size_Q d`) with at most `Kd^s` decorations of total size `s` over each base configuration satisfy
  `LoopEntropy size_Q V (2 K Kd)` when the base satisfies `LoopEntropy size_P V K`, `K ≥ 1`.
* `hiddenCostAt_of_uniformNest_decorated`: decorated block animals over `LoopConf dim nB` with the fibre bound
  give (T) with `V = dim² nB^dim`, `K = 2 (16 dim + 1)² Kd`, given `log K < σ b t₀`.

## 4. The split alone carries no content (proved)

* `nestCount_none`, `nestFine_of_count`: with `coarse = ∅`, `NestCount` holds vacuously and `NestFine C` is
  `ZeroFluxCount C` (both directions proved: `nestFine_of_count`, `count_of_nestFine_none`).
* `nestFine_all`: with every level resolved, `NestFine 0` holds and the whole content is in `NestCount`.
* `uniformNest_of_uniformGlueball`: `UniformGlueball N m t₀ C ℓ` gives `UniformNest N size m t₀ σ b C ℓ` for any
  nonempty `P`, `size`, `σ`, `b`. With `uniformGlueball_of_uniformNest` the two uniform statements are equivalent
  up to constants.

So the reduction moves the count clause into the carrier: the content of `NestCount ∧ NestFine` is the claim that
the resolved excited levels are carried injectively by aperture configurations at `σ b` per block while the rest
weigh at most `ε` at `t₀`, with every constant fixed in the zoom.

## 5. Ratio only (the clause lemmas proved; the statement for `UniformNest` argued)

Under a change of the observer's unit by `r > 0` (lengths and times `× r`, energies `× 1/r`, tension `× 1/r²`):
`heatW_rescale`, `zeroFluxGap_rescale`, `zeroFluxCount_rescale`, `nestCount_rescale`, `nestFine_rescale` (each an
`↔`), `cost_rescale` (`(σ/r²)(r b)(r t₀) = σ b t₀`), `rate_rescale` (`(m/r)(r t₀) = m t₀`) and `cells_rescale`.
Every hypothesis of `count_of_nest` and every constant of its conclusion is unchanged. Argued, not proved (no
theorem rescales `UniformNest`; `aRun` has a fixed normalisation; `nB` is not tied to `ℓ/b`): in `UniformNest` the lattice
spacing `aRun N β` enters only through the physical extent `n a` (the window and `ZeroFluxLevels`, where
`μ_j² = e^{−E_j (n a)}`); `b`, `t₀`, `ℓ` are physical lengths measured by the observer's ruler. So the statement is
ratio-only: it reads `σ b t₀`, `m t₀`, `ℓ/b`, `t₀/ℓ`, never a length or energy alone.

## What remains (argued, not proved)

The three inputs of `hiddenCostAt_of_uniformNest` at the real `trivKN`, uniform in the zoom:
(a) the decorated block count (the fibre bound of `loopEntropy_decorated`, for whatever decoration labels the
levels: with labels in `ℕ` of total size `s` over `k ≤ s` blocks there are `C(s−1, k−1) ≤ 2ˢ` (argued), so
`Kd = 2`); (b) the aperture-scale gap (`NestCount.gap`: each resolved excited level costs `σ b` per block of its
carrier) together with the injective carrier; (c) `NestFine`. By section 4 none of them is weaker than the count
clause they replace, taken together. No declaration of the tree supplies any of them. `CondGap.WilsonCondUVGap`
(the conditional UV gap) is a per-step correlation bound on fibre Gibbs measures, `FineLinks.NearFree` a pointwise
closeness of transition weights to a free reference, `BalabanUV.BalabanShape` a renormalisation-step shape
hypothesis, `PolymerCount.ChunkDecay` a decay bound on polymer activities on coarse plaquettes; each is about a
measure or an activity, not about the levels of `trivKN`, and no theorem derives `NestFine` or `NestCount` from
any of them. `ChunkDecay` has the same shape as (a)+(b) (touch-connected coarse polymers, a cost per chunk, fixed
in the zoom) but is stated for activities `w`, not for the levels.

DERIVED (module-wide): `5ℓ` is the upper end of `HiddenCostAt`'s window; `2` in `2 K Kd` bounds `s + 1 ≤ 2ˢ`
(the number of base sizes `0, …, s`); `2` in `2 (…) e^{m t₀}` and `[2ℓ, 5ℓ]` are `GlueballArea`'s;
`16 dim + 1` and the square are `StrongCoupling.card_connSets_le_hypercubic`'s.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.NestedAperture

open Filter Finset MassGap.GlueballArea MassGap.CentreSectorSeedN
open MassGap.AsymptoticScaling (aRun aRun_pos)

/-! ## 1. The split -/

section Split

variable {ι P : Type*}

/-- **The aperture-scale part of the split**: the excited levels in `coarse` are carried injectively by aperture
configurations `p j`, and a level carried by `s` blocks lies at least `σ (b s)` above the ground (`σ b` per
block). -/
structure NestCount (g₀ : ι) (E : ι → ℝ) (σ b : ℝ) (size : P → ℕ) (coarse : ι → Prop) (p : ι → P) :
    Prop where
  inj : ∀ j k, j ≠ g₀ → k ≠ g₀ → coarse j → coarse k → p j = p k → j = k
  gap : ∀ j, j ≠ g₀ → coarse j → σ * (b * size (p j)) ≤ E j - E g₀

open Classical in
/-- **The sub-resolution weight of level `j`**: its heat weight at `t₀` if it is excited and not resolved by the
aperture, `0` otherwise. -/
def fineW (g₀ : ι) (E : ι → ℝ) (coarse : ι → Prop) (t₀ : ℝ) (j : ι) : ℝ :=
  if j ≠ g₀ ∧ ¬ coarse j then heatW g₀ E t₀ j else 0

/-- **The sub-resolution weight is at most `ε`**: the weight at `t₀` of the excited levels outside `coarse` is
summable and at most `ε`. Intended reading (argued): finer apertures add nothing the coarse one cannot count.
Formally it includes every excited level below `σ b` (`resolved_ge`). -/
def NestFine (g₀ : ι) (E : ι → ℝ) (coarse : ι → Prop) (t₀ ε : ℝ) : Prop :=
  Summable (fineW g₀ E coarse t₀) ∧ ∑' j, fineW g₀ E coarse t₀ j ≤ ε

theorem fineW_nonneg (g₀ : ι) (E : ι → ℝ) (coarse : ι → Prop) (t₀ : ℝ) (j : ι) :
    0 ≤ fineW g₀ E coarse t₀ j := by
  unfold fineW
  split_ifs
  · exact (heatW_pos g₀ E t₀ j).le
  · exact le_rfl

/-! ## 2. The reduction -/

/-- **The count clause from the nesting**: the aperture-scale part with an entropy bound `LoopEntropy size V K`
and `q = K e^{−σ b t₀} < 1`, plus the sub-resolution part `ε`, give
`ZeroFluxCount g₀ E t₀ (V q/(1 − q) + ε)`. -/
theorem count_of_nest {g₀ : ι} {E : ι → ℝ} {σ b t₀ V K ε : ℝ} {size : P → ℕ} {coarse : ι → Prop}
    {p : ι → P} (hN : NestCount g₀ E σ b size coarse p) (hF : NestFine g₀ E coarse t₀ ε)
    (ht₀ : 0 ≤ t₀) (hsize : ∀ γ, 1 ≤ size γ) (hent : LoopEntropy size V K) (hV : 0 ≤ V)
    (hK : 0 ≤ K) (hq : K * Real.exp (-(σ * b * t₀)) < 1) :
    ZeroFluxCount g₀ E t₀
      (V * (K * Real.exp (-(σ * b * t₀)) / (1 - K * Real.exp (-(σ * b * t₀)))) + ε) := by
  classical
  set c := σ * b * t₀ with hc
  set B := V * (K * Real.exp (-c) / (1 - K * Real.exp (-c))) with hB
  obtain ⟨hFs, hFle⟩ := hF
  have hfin : ∀ u : Finset ι, ∑ j ∈ u, heatW g₀ E t₀ j ≤ 1 + (B + ε) := by
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not u (fun j => j = g₀)]
    have hA : ∑ j ∈ u.filter (fun j => j = g₀), heatW g₀ E t₀ j ≤ 1 := by
      have hsub : u.filter (fun j => j = g₀) ⊆ {g₀} := by
        intro j hj; rw [Finset.mem_singleton]; exact (Finset.mem_filter.1 hj).2
      calc ∑ j ∈ u.filter (fun j => j = g₀), heatW g₀ E t₀ j
          ≤ ∑ j ∈ ({g₀} : Finset ι), heatW g₀ E t₀ j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (heatW_pos g₀ E t₀ j).le)
        _ = 1 := by rw [Finset.sum_singleton, heatW_ground]
    set u' := u.filter (fun j => ¬ j = g₀) with hu'
    rw [← Finset.sum_filter_add_sum_filter_not u' coarse]
    have hC : ∑ j ∈ u'.filter coarse, heatW g₀ E t₀ j ≤ B := by
      set w := u'.filter coarse with hw
      have hmem : ∀ j ∈ w, j ≠ g₀ ∧ coarse j := fun j hj => by
        rw [hw, Finset.mem_filter, hu', Finset.mem_filter] at hj
        exact ⟨hj.1.2, hj.2⟩
      have hinj : Set.InjOn p w := fun j hj k hk hjk =>
        hN.inj j k (hmem j hj).1 (hmem k hk).1 (hmem j hj).2 (hmem k hk).2 hjk
      calc ∑ j ∈ w, heatW g₀ E t₀ j ≤ ∑ j ∈ w, Real.exp (-(c * size (p j))) := by
            refine Finset.sum_le_sum fun j hj => ?_
            unfold heatW
            refine Real.exp_le_exp.2 (neg_le_neg ?_)
            have h1 := mul_le_mul_of_nonneg_right (hN.gap j (hmem j hj).1 (hmem j hj).2) ht₀
            calc c * (size (p j) : ℝ) = σ * (b * size (p j)) * t₀ := by rw [hc]; ring
              _ ≤ (E j - E g₀) * t₀ := h1
        _ = ∑ γ ∈ w.image p, Real.exp (-(c * size γ)) :=
            (Finset.sum_image (f := fun γ => Real.exp (-(c * size γ))) hinj).symm
        _ ≤ B := loopGas_finset_le hsize hent hV hK hq _
    have hR : ∑ j ∈ u'.filter (fun j => ¬ coarse j), heatW g₀ E t₀ j ≤ ε := by
      calc ∑ j ∈ u'.filter (fun j => ¬ coarse j), heatW g₀ E t₀ j
          = ∑ j ∈ u'.filter (fun j => ¬ coarse j), fineW g₀ E coarse t₀ j := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Finset.mem_filter, hu', Finset.mem_filter] at hj
            unfold fineW
            rw [if_pos ⟨hj.1.2, hj.2⟩]
        _ ≤ ∑' j, fineW g₀ E coarse t₀ j :=
            hFs.sum_le_tsum _ (fun j _ => fineW_nonneg g₀ E coarse t₀ j)
        _ ≤ ε := hFle
    linarith
  have hnn : 0 ≤ heatW g₀ E t₀ := fun j => (heatW_pos g₀ E t₀ j).le
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

/-- **The count clause from the nesting, entropy against cost**: as `count_of_nest`, with
`log K < σ b t₀` (`K > 0`) in place of `q < 1`. -/
theorem count_of_nest_log {g₀ : ι} {E : ι → ℝ} {σ b t₀ V K ε : ℝ} {size : P → ℕ}
    {coarse : ι → Prop} {p : ι → P} (hN : NestCount g₀ E σ b size coarse p)
    (hF : NestFine g₀ E coarse t₀ ε) (ht₀ : 0 ≤ t₀) (hsize : ∀ γ, 1 ≤ size γ)
    (hent : LoopEntropy size V K) (hV : 0 ≤ V) (hK : 0 < K) (hcost : Real.log K < σ * b * t₀) :
    ZeroFluxCount g₀ E t₀
      (V * (K * Real.exp (-(σ * b * t₀)) / (1 - K * Real.exp (-(σ * b * t₀)))) + ε) :=
  count_of_nest hN hF ht₀ hsize hent hV hK.le ((q_lt_one_iff hK).2 hcost)

/-! ## 4. The split alone carries no content -/

/-- With no level resolved, `NestCount` holds vacuously. -/
theorem nestCount_none (g₀ : ι) (E : ι → ℝ) (σ b : ℝ) (size : P → ℕ) (p : ι → P) :
    NestCount g₀ E σ b size (fun _ => False) p :=
  ⟨fun _ _ _ _ h => h.elim, fun _ _ h => h.elim⟩

/-- **With no level resolved, `NestFine` is the count clause**: `ZeroFluxCount g₀ E t₀ C` gives
`NestFine g₀ E ∅ t₀ C`. -/
theorem nestFine_of_count {g₀ : ι} {E : ι → ℝ} {t₀ C : ℝ} (h : ZeroFluxCount g₀ E t₀ C) :
    NestFine g₀ E (fun _ => False) t₀ C := by
  classical
  obtain ⟨hs, hle⟩ := h
  have hf : fineW g₀ E (fun _ => False) t₀ = fun j => if j = g₀ then 0 else heatW g₀ E t₀ j := by
    funext j
    unfold fineW
    by_cases hj : j = g₀
    · simp [hj]
    · simp [hj]
  unfold NestFine
  rw [hf]
  have hsum : ∑' j, heatW g₀ E t₀ j = 1 + ∑' j, (if j = g₀ then 0 else heatW g₀ E t₀ j) := by
    have := hs.tsum_eq_add_tsum_ite g₀
    rw [heatW_ground] at this
    exact this
  refine ⟨?_, by linarith⟩
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hs
  · split_ifs
    · exact le_rfl
    · exact (heatW_pos g₀ E t₀ j).le
  · split_ifs
    · exact (heatW_pos g₀ E t₀ j).le
    · exact le_rfl

/-- **The converse of `nestFine_of_count`**: `NestFine g₀ E ∅ t₀ C` gives `ZeroFluxCount g₀ E t₀ C`. -/
theorem count_of_nestFine_none {g₀ : ι} {E : ι → ℝ} {t₀ C : ℝ}
    (h : NestFine g₀ E (fun _ => False) t₀ C) : ZeroFluxCount g₀ E t₀ C := by
  classical
  obtain ⟨hs, hle⟩ := h
  have hf : fineW g₀ E (fun _ => False) t₀ = fun j => if j = g₀ then 0 else heatW g₀ E t₀ j := by
    funext j; unfold fineW; by_cases hj : j = g₀ <;> simp [hj]
  rw [hf] at hs hle
  have hW : Summable (heatW g₀ E t₀) := by
    have h1 : Summable (fun j => if j = g₀ then heatW g₀ E t₀ j else 0) :=
      (hasSum_ite_eq g₀ (heatW g₀ E t₀ g₀)).summable.congr (fun j => by
        by_cases hj : j = g₀ <;> simp [hj])
    refine (h1.add hs).congr (fun j => ?_)
    by_cases hj : j = g₀ <;> simp [hj]
  refine ⟨hW, ?_⟩
  have := hW.tsum_eq_add_tsum_ite g₀
  rw [heatW_ground] at this
  linarith

/-- **Resolved levels lie at least `σ b` above the ground** (sizes `≥ 1`, `σ b ≥ 0`): so every excited level
below `σ b` is outside `coarse`, in the fine part. -/
theorem resolved_ge {g₀ : ι} {E : ι → ℝ} {σ b : ℝ} {size : P → ℕ} {coarse : ι → Prop} {p : ι → P}
    (hN : NestCount g₀ E σ b size coarse p) (hsize : ∀ γ, 1 ≤ size γ) (hσb : 0 ≤ σ * b)
    (j : ι) (hj : j ≠ g₀) (hc : coarse j) : σ * b ≤ E j - E g₀ := by
  have := hN.gap j hj hc
  have h1 : (1 : ℝ) ≤ size (p j) := by exact_mod_cast hsize (p j)
  nlinarith

/-- **With every level resolved, `NestFine 0` holds**: the whole content is then in `NestCount`. -/
theorem nestFine_all (g₀ : ι) (E : ι → ℝ) (t₀ : ℝ) : NestFine g₀ E (fun _ => True) t₀ 0 := by
  have h0 : fineW g₀ E (fun _ => True) t₀ = 0 := by
    funext j
    simp [fineW]
  unfold NestFine
  rw [h0]
  exact ⟨summable_zero, by simp⟩

/-! ## 5. Ratio only -/

/-- **Heat weights read only `E t`**: energies `× 1/r` and time `× r` leave every heat weight unchanged. -/
theorem heatW_rescale (g₀ : ι) (E : ι → ℝ) (t : ℝ) {r : ℝ} (hr : r ≠ 0) (j : ι) :
    heatW g₀ (fun k => E k / r) (r * t) j = heatW g₀ E t j := by
  simp only [heatW]
  congr 2
  rw [div_sub_div_same, div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ hr]

theorem zeroFluxGap_rescale (g₀ : ι) (E : ι → ℝ) (m : ℝ) {r : ℝ} (hr : 0 < r) :
    ZeroFluxGap g₀ (fun k => E k / r) (m / r) ↔ ZeroFluxGap g₀ E m := by
  simp only [ZeroFluxGap]
  refine forall_congr' fun j => imp_congr_right fun _ => ?_
  rw [← add_div, div_le_div_iff_of_pos_right hr]

theorem zeroFluxCount_rescale (g₀ : ι) (E : ι → ℝ) (t₀ C : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ZeroFluxCount g₀ (fun k => E k / r) (r * t₀) C ↔ ZeroFluxCount g₀ E t₀ C := by
  have h : heatW g₀ (fun k => E k / r) (r * t₀) = heatW g₀ E t₀ := funext (heatW_rescale g₀ E t₀ hr)
  unfold ZeroFluxCount
  rw [h]

theorem nestCount_rescale (g₀ : ι) (E : ι → ℝ) (σ b : ℝ) (size : P → ℕ) (coarse : ι → Prop)
    (p : ι → P) {r : ℝ} (hr : 0 < r) :
    NestCount g₀ (fun k => E k / r) (σ / r ^ 2) (r * b) size coarse p
      ↔ NestCount g₀ E σ b size coarse p := by
  have key : ∀ j, (σ / r ^ 2 * (r * b * size (p j)) ≤ E j / r - E g₀ / r
      ↔ σ * (b * size (p j)) ≤ E j - E g₀) := by
    intro j
    have hl : σ / r ^ 2 * (r * b * size (p j)) = σ * (b * size (p j)) / r := by
      field_simp
    rw [hl, div_sub_div_same, div_le_div_iff_of_pos_right hr]
  constructor
  · intro h
    exact ⟨h.inj, fun j hj hc => (key j).1 (h.gap j hj hc)⟩
  · intro h
    exact ⟨h.inj, fun j hj hc => (key j).2 (h.gap j hj hc)⟩

theorem nestFine_rescale (g₀ : ι) (E : ι → ℝ) (coarse : ι → Prop) (t₀ ε : ℝ) {r : ℝ} (hr : r ≠ 0) :
    NestFine g₀ (fun k => E k / r) coarse (r * t₀) ε ↔ NestFine g₀ E coarse t₀ ε := by
  have h : fineW g₀ (fun k => E k / r) coarse (r * t₀) = fineW g₀ E coarse t₀ := by
    funext j
    unfold fineW
    rw [heatW_rescale g₀ E t₀ hr j]
  unfold NestFine
  rw [h]

/-- **The cost per block in units of the entropy is a ratio**: `(σ/r²)(r b)(r t₀) = σ b t₀`. -/
theorem cost_rescale (σ b t₀ : ℝ) {r : ℝ} (hr : r ≠ 0) : σ / r ^ 2 * (r * b) * (r * t₀) = σ * b * t₀ := by
  field_simp

/-- **The rate in units of `t₀` is a ratio**: `(m/r)(r t₀) = m t₀`. -/
theorem rate_rescale (m t₀ : ℝ) {r : ℝ} (hr : r ≠ 0) : m / r * (r * t₀) = m * t₀ := by
  field_simp

end Split

/-! ## 3. The aperture's cells -/

/-- **The aperture's cells per direction**: `⌈5ℓ/b⌉₊` cells of side `b`.

DERIVED: Inherited: `5` from `5ℓ`, the upper end of `HiddenCostAt`'s window `[2ℓ, 5ℓ]`. -/
def cells (ℓ b : ℝ) : ℕ := ⌈5 * ℓ / b⌉₊

/-- **The aperture covers the window**: a box of physical side `L ≤ 5ℓ` fits in `cells ℓ b` cells of side `b`. -/
theorem window_covered {L ℓ b : ℝ} (hb : 0 < b) (hL : L ≤ 5 * ℓ) : L ≤ (cells ℓ b : ℝ) * b := by
  have h := Nat.le_ceil (5 * ℓ / b)
  calc L ≤ 5 * ℓ := hL
    _ = 5 * ℓ / b * b := (div_mul_cancel₀ _ hb.ne').symm
    _ ≤ (cells ℓ b : ℝ) * b := mul_le_mul_of_nonneg_right h hb.le

/-- **The cell count reads only `ℓ/b`.** -/
theorem cells_rescale (ℓ b : ℝ) {r : ℝ} (hr : r ≠ 0) : cells (r * ℓ) (r * b) = cells ℓ b := by
  unfold cells
  rw [mul_left_comm, mul_div_mul_left _ _ hr]

/-! ### Decorations -/

section Decorated

variable {Q P : Type*}

/-- **Decorated entropy from a fibre bound**: configurations `Q` over base configurations `P`
(`size_P(π d) ≤ size_Q d`), with at most `Kd^s` members of total size `s` over each base configuration, satisfy
`LoopEntropy size_Q V (2 K Kd)` when the base satisfies `LoopEntropy size_P V K` with `K ≥ 1`. -/
theorem loopEntropy_decorated {sizeB : P → ℕ} {size : Q → ℕ} {π : Q → P} {V K Kd : ℝ}
    (hent : LoopEntropy sizeB V K) (hV : 0 ≤ V) (hK : 1 ≤ K) (hKd : 0 ≤ Kd)
    (hmono : ∀ d, sizeB (π d) ≤ size d)
    (hfib : ∀ (γ : P) (s : ℕ) (F : Finset Q), (∀ d ∈ F, π d = γ ∧ size d = s) →
      (F.card : ℝ) ≤ Kd ^ s) :
    LoopEntropy size V (2 * K * Kd) := by
  classical
  intro s F hF
  set Bs := F.image π with hBs
  have h1 : (F.card : ℝ) ≤ Bs.card * Kd ^ s := by
    rw [Finset.card_eq_sum_card_image π F]
    push_cast
    calc ∑ γ ∈ F.image π, ((F.filter (fun d => π d = γ)).card : ℝ) ≤ ∑ γ ∈ F.image π, Kd ^ s :=
          Finset.sum_le_sum fun γ _ => hfib γ s _ (fun d hd =>
            ⟨(Finset.mem_filter.1 hd).2, hF d (Finset.mem_filter.1 hd).1⟩)
      _ = Bs.card * Kd ^ s := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : (Bs.card : ℝ) ≤ ((s : ℝ) + 1) * (V * K ^ s) := by
    have hmaps : (Bs : Set P).MapsTo sizeB (Finset.range (s + 1)) := by
      intro γ hγ
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hγ)
      exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le ((hmono d).trans (hF d hd).le)))
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    calc ∑ k ∈ Finset.range (s + 1), ((Bs.filter (fun γ => sizeB γ = k)).card : ℝ)
        ≤ ∑ _k ∈ Finset.range (s + 1), V * K ^ s := Finset.sum_le_sum fun k hk => by
          refine (hent k _ (fun γ hγ => (Finset.mem_filter.1 hγ).2)).trans ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hK (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))) hV
      _ = ((s : ℝ) + 1) * (V * K ^ s) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have h3 : ((s : ℝ) + 1) ≤ 2 ^ s := by
    have : s + 1 ≤ 2 ^ s := (Nat.lt_two_pow_self : s < 2 ^ s)
    exact_mod_cast this
  have hVK : 0 ≤ V * K ^ s := mul_nonneg hV (pow_nonneg (by linarith) s)
  calc (F.card : ℝ) ≤ Bs.card * Kd ^ s := h1
    _ ≤ (((s : ℝ) + 1) * (V * K ^ s)) * Kd ^ s := mul_le_mul_of_nonneg_right h2 (pow_nonneg hKd s)
    _ ≤ (2 ^ s * (V * K ^ s)) * Kd ^ s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hVK) (pow_nonneg hKd s)
    _ = V * (2 * K * Kd) ^ s := by rw [mul_pow, mul_pow]; ring

end Decorated

/-! ## 2. The reduction at the real zero-flux kernel, uniform in the zoom -/

section Kernel

variable {N : ℕ} [NeZero N]

/-- **The nesting statement at the window `[2ℓ, 5ℓ]`**: eventually in `β`, at every power-of-two side `n ≥ 2`
with `n a ∈ [2ℓ, 5ℓ]` and every step, the real zero-flux kernel `trivKN N β n i` has spectral levels with gap `m`
and a split into an aperture-scale part (`NestCount`, configurations in the fixed type `P` at `σ b` per block) and
a sub-resolution part of weight at most `ε` at `t₀` (`NestFine`). `P`, `size`, `m`, `t₀`, `σ`, `b`, `ε`, `ℓ` are
the same at every `β`.

DERIVED: Inherited: `2`, `5` the ends of `HiddenCostAt`'s window `[2ℓ, 5ℓ]` (`GlueballArea`'s). -/
def UniformNest (N : ℕ) [NeZero N] {P : Type*} (size : P → ℕ) (m t₀ σ b ε ℓ : ℝ) : Prop :=
  ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun N β → (n : ℝ) * aRun N β ≤ 5 * ℓ → ∀ i : Fin 4,
      ∃ (ι : Type) (g₀ : ι) (E : ι → ℝ) (coarse : ι → Prop) (p : ι → P),
        ZeroFluxLevels N β n i g₀ E ∧ ZeroFluxGap g₀ E m ∧
        NestCount g₀ E σ b size coarse p ∧ NestFine g₀ E coarse t₀ ε

/-- **The uniform glueball statement from the nesting.** -/
theorem uniformGlueball_of_uniformNest {P : Type*} {size : P → ℕ} {m t₀ σ b ε ℓ V K : ℝ}
    (ht₀ : 0 ≤ t₀) (hsize : ∀ γ, 1 ≤ size γ) (hent : LoopEntropy size V K) (hV : 0 ≤ V)
    (hK : 0 < K) (hcost : Real.log K < σ * b * t₀) (h : UniformNest N size m t₀ σ b ε ℓ) :
    UniformGlueball N m t₀
      (V * (K * Real.exp (-(σ * b * t₀)) / (1 - K * Real.exp (-(σ * b * t₀)))) + ε) ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hhi i
  obtain ⟨ι, g₀, E, coarse, p, hL, hg, hNC, hNF⟩ := hβ n hn h2 hlo hhi i
  exact ⟨ι, g₀, E, hL, hg, count_of_nest_log hNC hNF ht₀ hsize hent hV hK hcost⟩

/-- **The split adds no content at the uniform level**: `UniformGlueball N m t₀ C ℓ` gives
`UniformNest N size m t₀ σ b C ℓ` for any nonempty `P`, `size`, `σ`, `b` (no level resolved). -/
theorem uniformNest_of_uniformGlueball {P : Type*} [Nonempty P] (size : P → ℕ) {m t₀ σ b C ℓ : ℝ}
    (h : UniformGlueball N m t₀ C ℓ) : UniformNest N size m t₀ σ b C ℓ := by
  filter_upwards [h] with β hβ n hn h2 hlo hhi i
  obtain ⟨ι, g₀, E, hL, hg, hc⟩ := hβ n hn h2 hlo hhi i
  exact ⟨ι, g₀, E, fun _ => False, fun _ => Classical.arbitrary P, hL, hg,
    nestCount_none g₀ E σ b size _, nestFine_of_count hc⟩

/-- **(T) from the nesting.** Intended reading (argued): nesting finer apertures inside a fixed one adds no
low-lying no-flux states it cannot count. Formally `UniformNest` is equivalent in strength to `UniformGlueball`
(`uniformNest_of_uniformGlueball`), and by `resolved_ge` the levels below `σ b` sit in the fine part. With a gap `m`, an aperture-scale count (`LoopEntropy size V K`, `log K < σ b t₀`, `σ b` per
block) and a sub-resolution weight `ε`, all fixed in the zoom, and `0 ≤ t₀ ≤ 2ℓ`:
`HiddenCostAt N m (2 (V q/(1 − q) + ε) e^{m t₀}) ℓ`, `q = K e^{−σ b t₀}`. -/
theorem hiddenCostAt_of_uniformNest {P : Type*} {size : P → ℕ} {m t₀ σ b ε ℓ V K : ℝ}
    (ht₀ : 0 ≤ t₀) (hℓ : t₀ ≤ 2 * ℓ) (hsize : ∀ γ, 1 ≤ size γ) (hent : LoopEntropy size V K)
    (hV : 0 ≤ V) (hK : 0 < K) (hcost : Real.log K < σ * b * t₀)
    (h : UniformNest N size m t₀ σ b ε ℓ) :
    ObserverTheory.HiddenCostAt N m
      (2 * (V * (K * Real.exp (-(σ * b * t₀)) / (1 - K * Real.exp (-(σ * b * t₀)))) + ε)
        * Real.exp (m * t₀)) ℓ :=
  hiddenCostAt_of_uniformGlueball ht₀ hℓ
    (uniformGlueball_of_uniformNest ht₀ hsize hent hV hK hcost h)

/-- **(T) from the nesting, undecorated block animals**: the aperture's configurations are the touch-connected
plaquette sets of the periodic block lattice of extent `nB` (`V = dim² nB^dim`, `K = (16 dim + 1)²`). -/
theorem hiddenCostAt_of_uniformNest_block (dim nB : ℕ) [NeZero nB] {m t₀ σ b ε ℓ : ℝ}
    (ht₀ : 0 ≤ t₀) (hℓ : t₀ ≤ 2 * ℓ)
    (hcost : Real.log (((16 * dim + 1) ^ 2 : ℕ) : ℝ) < σ * b * t₀)
    (h : UniformNest N (loopSize dim nB) m t₀ σ b ε ℓ) :
    ObserverTheory.HiddenCostAt N m
      (2 * ((dim : ℝ) ^ 2 * (nB : ℝ) ^ dim
          * ((((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Real.exp (-(σ * b * t₀))
            / (1 - (((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Real.exp (-(σ * b * t₀)))) + ε)
        * Real.exp (m * t₀)) ℓ := by
  have hK : (0 : ℝ) < (((16 * dim + 1) ^ 2 : ℕ) : ℝ) := by positivity
  have := hiddenCostAt_of_uniformNest ht₀ hℓ (one_le_loopSize dim nB) (loopEntropy_hypercubic dim nB)
    (Nat.cast_nonneg _) hK hcost h
  rwa [card_plaq dim nB] at this

/-- **(T) from the nesting, decorated block animals**: configurations `Q` over the block animals
`LoopConf dim nB` with at most `Kd^s` decorations of total size `s` over each animal give (T) with
`V = dim² nB^dim`, `K = 2 (16 dim + 1)² Kd`. -/
theorem hiddenCostAt_of_uniformNest_decorated (dim nB : ℕ) [NeZero nB] {Q : Type*} {size : Q → ℕ}
    {π : Q → LoopConf dim nB} {Kd m t₀ σ b ε ℓ : ℝ} (hKd : 0 < Kd)
    (hmono : ∀ d, loopSize dim nB (π d) ≤ size d)
    (hfib : ∀ (γ : LoopConf dim nB) (s : ℕ) (F : Finset Q), (∀ d ∈ F, π d = γ ∧ size d = s) →
      (F.card : ℝ) ≤ Kd ^ s)
    (ht₀ : 0 ≤ t₀) (hℓ : t₀ ≤ 2 * ℓ)
    (hcost : Real.log (2 * (((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Kd) < σ * b * t₀)
    (h : UniformNest N size m t₀ σ b ε ℓ) :
    ObserverTheory.HiddenCostAt N m
      (2 * ((dim : ℝ) ^ 2 * (nB : ℝ) ^ dim
          * (2 * (((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Kd * Real.exp (-(σ * b * t₀))
            / (1 - 2 * (((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Kd * Real.exp (-(σ * b * t₀)))) + ε)
        * Real.exp (m * t₀)) ℓ := by
  have hK1 : (1 : ℝ) ≤ (((16 * dim + 1) ^ 2 : ℕ) : ℝ) := by
    have : 1 ≤ (16 * dim + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    exact_mod_cast this
  have hent := loopEntropy_decorated (loopEntropy_hypercubic dim nB) (Nat.cast_nonneg _) hK1
    hKd.le hmono hfib
  have hsize : ∀ d, 1 ≤ size d := fun d => (one_le_loopSize dim nB (π d)).trans (hmono d)
  have hK : (0 : ℝ) < 2 * (((16 * dim + 1) ^ 2 : ℕ) : ℝ) * Kd := by positivity
  have := hiddenCostAt_of_uniformNest ht₀ hℓ hsize hent (Nat.cast_nonneg _) hK hcost h
  rwa [card_plaq dim nB] at this

end Kernel

end MassGap.NestedAperture

#print axioms MassGap.NestedAperture.fineW_nonneg
#print axioms MassGap.NestedAperture.count_of_nest
#print axioms MassGap.NestedAperture.count_of_nest_log
#print axioms MassGap.NestedAperture.nestCount_none
#print axioms MassGap.NestedAperture.nestFine_of_count
#print axioms MassGap.NestedAperture.nestFine_all
#print axioms MassGap.NestedAperture.count_of_nestFine_none
#print axioms MassGap.NestedAperture.resolved_ge
#print axioms MassGap.NestedAperture.uniformNest_of_uniformGlueball
#print axioms MassGap.NestedAperture.heatW_rescale
#print axioms MassGap.NestedAperture.zeroFluxGap_rescale
#print axioms MassGap.NestedAperture.zeroFluxCount_rescale
#print axioms MassGap.NestedAperture.nestCount_rescale
#print axioms MassGap.NestedAperture.nestFine_rescale
#print axioms MassGap.NestedAperture.cost_rescale
#print axioms MassGap.NestedAperture.rate_rescale
#print axioms MassGap.NestedAperture.window_covered
#print axioms MassGap.NestedAperture.cells_rescale
#print axioms MassGap.NestedAperture.loopEntropy_decorated
#print axioms MassGap.NestedAperture.uniformGlueball_of_uniformNest
#print axioms MassGap.NestedAperture.hiddenCostAt_of_uniformNest
#print axioms MassGap.NestedAperture.hiddenCostAt_of_uniformNest_block
#print axioms MassGap.NestedAperture.hiddenCostAt_of_uniformNest_decorated
