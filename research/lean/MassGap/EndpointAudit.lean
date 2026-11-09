import Mathlib
import MassGap.RunSeedN

/-!
# MassGap.EndpointAudit — which fields of `RunSeedN.EndpointN` a cluster input can carry

`ClusterRoute.NarrowInputsAtCL` carries, per `N`, the gap input `RunSeedN.EndpointN N` and the
clustering input `ClusterRoute.ClusterPM Wf cf` (with `ClusterPassage.PointCluster`, `TreeCount.TreeGap` and the
rated forms `ClusterGap`, `PointGap` behind it). This module sorts the fields of `EndpointN` by what could supply
them, proves the reductions and no-go statements that can be stated on the fields themselves, and states a single-window
form of the endpoint, `EndpointS N`, that `EndpointN N` implies (`endpointS_of_endpointN`) and that still gives
`WDeltaRun.RunSeed N` (`runSeed_of_endpointS`), and proves the conditional no-go `not_endpointN_of_levels_unbounded`
for the fixed-`t₀` count. `ClayRunSeed` states the cluster capstone with `RunSeed N` in the gap slot. Declarations
are in the namespace `MassGap.EndpointAudit`.

## 1. The two inputs read different objects

`ClusterPM` bounds the cumulants of smeared flowed composites in the infinite-volume state `stateK k` at the
observer's steps `k` (`ClusterRoute.clX`). Every field of `EndpointN` is a statement on a finite slice: the
zero-flux transfer `trivKN N β n i` and the charged sector kernels of `halfKN N β n i`, at every large `β`, at power-of-two
sides with `n a ∈ [2ℓ, 5ℓ]`. No declaration in the tree passes from the first to the second (search; as
`ObserverReads` §4 records for `cluster → endpoint`). So no field of `EndpointN` follows from `ClusterPM`, `ClusterGap`,
`PointCluster`, `PointGap` or `TreeGap` as they stand (search): verdict (a) is empty for the cluster inputs, and every
(a) below is bookkeeping or an existing theorem.

## 2. The circular form, at the level of the slice

**`zeroFluxGap_iff_heatW`**: on any levels, `ZeroFluxGap g₀ E m` is exactly `e^{−(E_j − E_{g₀}) t} ≤ e^{−m t}` for
every excited `j` at one `t > 0`. A cluster bound on the slice's level vectors at rate `m` (the time correlation of
`φ_j` over `t`) is therefore the zero-flux gap itself, the slice form of `ObserverReads.cluster_of_clayStatementAt`.
`RunSeedN.zeroFluxGap_of_levelBoundN` is the same statement read on the kernel. On the charged side,
**`level_gap_of_trace`**: a bound `∑_j e^{−F_j t} ≤ e^{−E₀ t} A e^{−σ t}` on a sector trace puts every level at
`F_j ≥ E₀ + σ − log A / t`. With `RunSeedN.one_sub_twistRatioN_le_of_fluxLevels` (levels with gap and count bound
the trace) this makes `FluxLevels.gap` the (V) half of the run seed read level by level: a decay bound on the charged
trace (the twist deficit, `FluxCost.PlaneCostAt`) gives it, and it gives that bound only together with
`FluxLevels.count`.

## 3. Bookkeeping fields (proved here)

* **`exists_pair_bound`**: every finite family has a pair bound (`η k` the sum of the absolute pair entries), so
  `SliceEndN.pair` alone holds for every choice of spanning family; its content sits in `rate`.
* **`exists_radii`**: for `δ > 0` the radii `R k = (k + 1) δ` meet `R_mono`, `R_reach`, `R_pos`, `R_step`.
* **`SliceEndS`** replaces the eight fields `κ, v, span, lam, gram, η, pair, rate` of `SliceEndN` by one, `diag`:
  `‖K x‖² ≤ μ_{g₀}² e^{−(cσR_k + c'/R_k) n a} ‖x‖²` on the `k`-th loop shell. **`SliceEndS.ofN`**: every `SliceEndN`
  record gives one (`FocusFeed.norm_sq_le_on_span`); **`SliceEndS.gap`**: `diag` gives the zero-flux gap at
  `diagRate` (`RunSeedN.zeroFluxGap_of_electricDiagN`), which is the only use of the eight fields.

## 4. The count clauses

`SliceEndN.count` and `FluxLevels.count` bound heat traces at the time `t₀`, with `t₀`, `Cc`, `Co` fixed for every
window `ℓ` that `EndpointN` visits.

* **`card_mul_exp_le_of_count`**: `ZeroFluxCount g₀ E t₀ C` bounds the number of levels within `D` of the ground
  by `(1 + C) e^{D t₀}`, with no dependence on the slice volume.
* **`exists_not_count_of_gap_count`** (no-go): for `0 < t₀ < T`, a gap at any rate and a count at the later time
  `T` do not give a count at `t₀`. So the count at `t₀` is not carried by the slice's own trace `hs(trivKN)` at
  `t = n a ≥ 2ℓ ≥ t₀` (which is the count at `n a`) nor by any gap statement.
* Argued, not proved: `∑_j e^{−(E_j − E_{g₀}) t₀}` is `Z₀(L³ × t₀) e^{E_{g₀} t₀}`, the zero-flux part of the box
  partition function at temperature `1/t₀` against its ground, where `L` is the transverse side of the slice, `n a`
  or `2n a` (`ext n (pathV i)`), so `L ≥ n a ≥ 2ℓ`. Its logarithm is extensive in the spatial volume `L³`: the
  one-glueball momentum states alone number `∼ (L·p_D)³`, `p_D = √(D(2m_G + D))`, within `D > m_G` of the ground
  (weighted at `t₀`: `∼ L³·t₀^{−3}·e^{−m_G·t₀}`). `card_mul_exp_le_of_count` bounds that number by the fixed
  `(1 + Cc) e^{D t₀}`, so with `t₀` and `Cc` fixed `count` cannot hold frequently in `ℓ` for a theory with that
  spectrum. The same holds for the charged count. The proved form is the conditional no-go
  **`not_endpointN_of_levels_unbounded`**: if, eventually in `ℓ`, the level count within `D` of the ground on some
  window slice exceeds every bound, then `¬ EndpointN N`. The same uniform-count clause sits in the other carriers of
  the fixed-`t₀` endpoint: `MultiScale.Endpoint` (`SU(2)`), `ScaleControlRun` (its endpoint record), likely
  `TensionFloor` (its count clause, argued), and the five roots that take `EndpointN` as a hypothesis,
  `ClayNarrow`, `ClayNarrowMG`, `ClusterRoute`, `GenerationCyclic` and `GenerationN`. `EndpointN`'s `∃ᶠ ℓ` is the
  source of that uniformity, and `RunSeed` does not need it: `ObserverTheory.runSeed_of_bindingSU` uses one window
  `ℓ` at which `A e^{−2σℓ} ≤ 1/80000`.

## 5. The single-window endpoint (proved)

`EndpointSAt N c c' σ δ t₀ Cc m Co ℓ` is `RunSeedN.EndpointNAt` with `SliceEndS` in place of `SliceEndN`.
`EndpointS N`: constants and ONE window `ℓ > 0` with `D = diagRate c c' σ δ (2ℓ) > 0`, `m > 0`, the two smallness
conditions `2 Cc e^{D t₀} e^{−2Dℓ} ≤ 1/80000` and `9 ⌊N/2⌋² · 2 Co e^{m t₀} e^{−2mℓ} ≤ 1/80000`, and
`EndpointSAt` at that `ℓ`. The counts are asked at one box size, so their constants may be the box's own. The
smallness conditions then force `t₀` to grow with `ℓ`: at fixed `t₀` the box's own `Cc` is `∼ exp(c ℓ³)` (§4), which
`e^{−2Dℓ}` does not beat, while at `t₀ = 2ℓ` the factor `e^{D t₀}` cancels the decay `e^{−2Dℓ}`. So `EndpointS` is
satisfiable in principle only at `t₀ ≈ ℓ` (argued, not proved).

* **`runSeed_of_endpointS`**: `EndpointS N → WDeltaRun.RunSeed N`, with the seed at `C = 5ℓ`
  (`CentreSectorSeedN.defectW_le_of_sectorsN`).
* **`endpointS_of_endpointN`**: `EndpointN N → EndpointS N` (`SliceEndS.ofN`; the window is any `ℓ ≥ ℓ₀` visited
  by `EndpointN` at which `2 Cc e^{M t₀} e^{−2 D₀ ℓ}` and the flux term are below `1/80000`, `D₀ = diagRate(2ℓ₀)`,
  `M = √(c c' σ) + cσδ/2`).

So `EndpointS` asks less than `EndpointN` and gives the same `RunSeed`.

## 6. The audit table

Verdicts: (a) derivable from an existing input or bookkeeping; (b) derivable from a strengthened cluster input that
is not the conclusion; (c) independent of every cluster input. "Restates" marks a field that a cluster input could
give only in the large-distance form that the gap conclusion already is.

| field | verdict | reason |
|---|---|---|
| `SliceEndN.levels`, `meas` | (a), bookkeeping | Hilbert–Schmidt spectral theorem for `trivKN`; not proved in the tree |
| `fam`, `gen` | (a), proved | `ProcesiSeparation.excited_mem_closure_words_all` on `words` |
| `C`, `kmeas`, `C0`, `kbd` | (a), bookkeeping | a bounded measurable kernel |
| `R`, `R_mono`, `R_reach`, `R_pos`, `R_step` | (a), proved | `exists_radii` |
| `κ`, `v`, `span`, `lam`, `gram`, `η` | (a), bookkeeping | removed in `SliceEndS` |
| `pair` | (a), proved | `exists_pair_bound`; empty without `rate` |
| `rate` (`diag` in `SliceEndS`) | (c) | loop-size-dependent decay `cσR + c'/R` on the shells at one time `n a`; it gives the zero-flux gap (`SliceEndS.gap`) and is stronger than it (the `R`-growth is what sums the shells). A tree-graph bound with a size-independent rate (`ClusterGap`, `TreeGap`) does not give it; one with edge weight `e^{−(cσR + c'/R) t}` on loops of size `R` is `diag` restated. The open content is the cost of large contractible loops |
| `count` (zero flux) | (c) | a short-time heat trace of the box (`exists_not_count_of_gap_count`: not from gap or later counts); fixed `t₀`, `Cc` over `∃ᶠ ℓ` conflicts with extensivity (argued, §4; proved conditionally, `not_endpointN_of_levels_unbounded`); `EndpointS` asks it at one box, satisfiable in principle only at `t₀ ≈ ℓ` |
| `FluxLevels` `κ … energy`, `trace`, `charged` | (a), bookkeeping | spectral theorem for the sector kernels |
| `FluxLevels.gap` | restates (V) | `level_gap_of_trace` with `one_sub_twistRatioN_le_of_fluxLevels`; local cluster inputs (centre-invariant composites) have no matrix elements into charged sectors (argued), a winding (Polyakov) cluster bound at rate `m` is the twist deficit itself |
| `FluxLevels.count` | (c) | as the zero-flux count |
| constants uniform, `∃ᶠ ℓ`, eventually `β` | (a), proved weaker | `EndpointS` needs one window (`endpointS_of_endpointN`, `runSeed_of_endpointS`) |

No field is (b). The cluster-type statement that is not the conclusion and does carry the gap slot is the run
seed itself: `RunSeed N` asks, at one physical scale `C` and eventually in `β`, that the doubling defect
`16 log Z(n) − log Z(2n)` (a connected free energy across the doubling, `ZoomSelfScale.defectW`) be at most
`1/1000`. It has no rate and no large distance; the decay follows by the proved squaring (`DoublingSharp`).
`EndpointS` is one sufficient condition for it at one window.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `1/80000` the sector smallness of `CentreSectorSeedN.defectW_le_of_sectorsN`; `9 ⌊N/2⌋²`
the plane-to-flux factor of `FluxCost.fluxCostAt_of_planeCostAt`; `2` and `5` the window of `FluxCost.PlaneCostAt`
and the `2` of the twist bound; `1` the ground weight and the count offset; `0` the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.EndpointAudit

open MeasureTheory Filter
open MassGap.ElectricLoops
open MassGap.RunSeedN
open MassGap.CentreSectorSeedN (trivKN hSN halfKN twistRatioN)
open MassGap.AsymptoticScaling (aRun aRun_pos)
open MassGap.GlueballArea (ZeroFluxGap ZeroFluxCount UniformGlueball heatW)
open MassGap.SlabKernelOperator (kernelCLM)
open MassGap.LoopZoom (diagRate)

/-! ## 1. Levels: the gap as level decay, the count as a level count -/

section Levels

variable {ι : Type*}

/-- **A level-decay bound at rate `m` is the gap clause**: at one `t > 0`, `ZeroFluxGap g₀ E m` holds iff every
excited level has ground-normalised weight at most `e^{−m t}`. DERIVED: no numeral. -/
theorem zeroFluxGap_iff_heatW {g₀ : ι} {E : ι → ℝ} {m t : ℝ} (ht : 0 < t) :
    ZeroFluxGap g₀ E m ↔ ∀ j, j ≠ g₀ → heatW g₀ E t j ≤ Real.exp (-(m * t)) := by
  constructor
  · intro h j hj
    unfold heatW
    have hm : m ≤ E j - E g₀ := by linarith [h j hj]
    exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hm ht.le))
  · intro h j hj
    have h1 := Real.exp_le_exp.1 (h j hj)
    have h2 : m * t ≤ (E j - E g₀) * t := by linarith
    have h3 := le_of_mul_le_mul_right h2 ht
    linarith

/-- **The count bounds the number of low levels, uniformly in the volume**: `ZeroFluxCount g₀ E t₀ C` and a set
`S` of levels within `D` of the ground give `|S| e^{−D t₀} ≤ 1 + C`. DERIVED: `1` the ground weight. -/
theorem card_mul_exp_le_of_count {g₀ : ι} {E : ι → ℝ} {t₀ C D : ℝ} (ht₀ : 0 ≤ t₀)
    (h : ZeroFluxCount g₀ E t₀ C) (S : Finset ι) (hS : ∀ j ∈ S, E j - E g₀ ≤ D) :
    (S.card : ℝ) * Real.exp (-(D * t₀)) ≤ 1 + C := by
  obtain ⟨hs, hc⟩ := h
  calc (S.card : ℝ) * Real.exp (-(D * t₀)) = ∑ _j ∈ S, Real.exp (-(D * t₀)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ S, heatW g₀ E t₀ j := Finset.sum_le_sum fun j hj => by
        unfold heatW
        exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (hS j hj) ht₀))
    _ ≤ ∑' j, heatW g₀ E t₀ j := hs.sum_le_tsum S (fun j _ => (Real.exp_pos _).le)
    _ ≤ 1 + C := hc

/-- The ground-normalised heat trace of `M` levels at `L` above a ground at `0`. DERIVED: `1` the ground weight. -/
theorem tsum_heatW_two_levels (M : ℕ) (L t : ℝ) :
    ∑' j : Fin (M + 1), heatW (0 : Fin (M + 1)) (fun j => if j = 0 then 0 else L) t j
      = 1 + (M : ℝ) * Real.exp (-(L * t)) := by
  rw [tsum_fintype, Fin.sum_univ_succ]
  have h0 : heatW (0 : Fin (M + 1)) (fun j => if j = 0 then 0 else L) t 0 = 1 := by
    simp [heatW]
  have hs : ∀ k : Fin M,
      heatW (0 : Fin (M + 1)) (fun j => if j = 0 then 0 else L) t k.succ = Real.exp (-(L * t)) := by
    intro k
    simp [heatW, Fin.succ_ne_zero]
  rw [h0, Finset.sum_congr rfl fun k _ => hs k, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- **No-go: a gap and a later count do not give an earlier count.** For `0 < t₀ < T`, every rate `m` and every
`C`, there are levels with ground `0`, the gap `m`, the count `(T, 1)`, and no count `(t₀, C)`: `M = ⌊e^{L T}⌋`
excited levels at `L ≥ max(m, 0, (|C| + 1)/(T − t₀))`. DERIVED: `1` the count constant at `T` and the margin
over `|C|`; `0` the ground. -/
theorem exists_not_count_of_gap_count {m C t₀ T : ℝ} (ht₀ : 0 < t₀) (hT : t₀ < T) :
    ∃ (M : ℕ) (E : Fin (M + 1) → ℝ), (∀ j, E 0 ≤ E j) ∧ ZeroFluxGap 0 E m ∧
      ZeroFluxCount 0 E T 1 ∧ ¬ ZeroFluxCount 0 E t₀ C := by
  have hTt : 0 < T - t₀ := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = max (max m 0) ((|C| + 1) / (T - t₀)) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hLdef ▸ (le_max_right m 0).trans (le_max_left _ _)
  have hLm : m ≤ L := hLdef ▸ (le_max_left m 0).trans (le_max_left _ _)
  have hLC : |C| + 1 ≤ L * (T - t₀) := by
    have h := hLdef ▸ le_max_right (max m 0) ((|C| + 1) / (T - t₀))
    rwa [div_le_iff₀ hTt] at h
  refine ⟨⌊Real.exp (L * T)⌋₊, fun j => if j = 0 then 0 else L, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0 <;> simp [hj, hL0]
  · intro j hj
    simp only [if_neg hj, if_true]
    linarith
  · refine ⟨(hasSum_fintype _).summable, ?_⟩
    rw [tsum_heatW_two_levels]
    have hfl : (⌊Real.exp (L * T)⌋₊ : ℝ) ≤ Real.exp (L * T) := Nat.floor_le (Real.exp_pos _).le
    have he : Real.exp (L * T) * Real.exp (-(L * T)) = 1 := by
      rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right hfl (Real.exp_pos (-(L * T))).le
    linarith
  · rintro ⟨-, hc⟩
    rw [tsum_heatW_two_levels] at hc
    have hfl : Real.exp (L * T) - 1 < (⌊Real.exp (L * T)⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (Real.exp (L * T)); linarith
    have hE0 : 0 < Real.exp (-(L * t₀)) := Real.exp_pos _
    have hE1 : Real.exp (-(L * t₀)) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith)
    have hsplit : Real.exp (L * T) * Real.exp (-(L * t₀)) = Real.exp (L * (T - t₀)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hx : L * (T - t₀) + 1 ≤ Real.exp (L * (T - t₀)) := Real.add_one_le_exp _
    have hlow : (Real.exp (L * T) - 1) * Real.exp (-(L * t₀))
        < (⌊Real.exp (L * T)⌋₊ : ℝ) * Real.exp (-(L * t₀)) :=
      mul_lt_mul_of_pos_right hfl hE0
    have hC : C ≤ |C| := le_abs_self C
    nlinarith

/-- **A trace bound places every level**: `∑_j e^{−F_j t} ≤ e^{−E₀ t} A e^{−σ t}` with `A, t > 0` gives
`F_j ≥ E₀ + σ − log A / t` for every `j`. DERIVED: no numeral. -/
theorem level_gap_of_trace {κ : Type*} {F : κ → ℝ} {E₀ σ A t : ℝ} (ht : 0 < t) (hA : 0 < A)
    (hs : Summable fun j => Real.exp (-(F j * t)))
    (h : ∑' j, Real.exp (-(F j * t)) ≤ Real.exp (-(E₀ * t)) * (A * Real.exp (-(σ * t)))) (j : κ) :
    E₀ + (σ - Real.log A / t) ≤ F j := by
  have h1 : Real.exp (-(F j * t)) ≤ Real.exp (-(E₀ * t)) * (A * Real.exp (-(σ * t))) :=
    (hs.le_tsum j (fun k _ => (Real.exp_pos _).le)).trans h
  have h2 : Real.exp (-(E₀ * t)) * (A * Real.exp (-(σ * t)))
      = Real.exp (-(E₀ * t) + Real.log A + -(σ * t)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hA]
    ring
  rw [h2, Real.exp_le_exp] at h1
  have h3 : (E₀ + (σ - Real.log A / t)) * t = E₀ * t + σ * t - Real.log A := by
    rw [add_mul, sub_mul, div_mul_cancel₀ _ ht.ne']; ring
  exact le_of_mul_le_mul_right (by rw [h3]; linarith) ht

end Levels

/-! ## 2. Bookkeeping fields -/

section Bookkeeping

/-- **Every finite family has a pair bound**: `η k = ∑_{j,l} |⟨T v_j, T v_l⟩|`. So `SliceEndN.pair` holds for every
spanning family, and the content of the pair data is `SliceEndN.rate`. DERIVED: no numeral. -/
theorem exists_pair_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (κ : ℕ → Type*) [∀ k, Fintype (κ k)] (v : ∀ k, κ k → E) :
    ∃ η : ℕ → ℝ, ∀ k j l, |inner ℝ (T (v k j)) (T (v k l))| ≤ η k := by
  classical
  refine ⟨fun k => ∑ p : κ k × κ k, |inner ℝ (T (v k p.1)) (T (v k p.2))|, fun k j l => ?_⟩
  exact Finset.single_le_sum (f := fun p : κ k × κ k => |inner ℝ (T (v k p.1)) (T (v k p.2))|)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (j, l))

/-- **The shell radii are bookkeeping**: for `δ > 0`, `R k = (k + 1) δ` is monotone, positive, reaches every size
at spacing `a ≥ 0`, and meets the step `(k + 1) δ ≤ R k`. DERIVED: `1` the index offset. -/
theorem exists_radii {a δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ → ℝ, Monotone R ∧ (∀ L : ℕ, ∃ k, a * (L : ℝ) ≤ R k) ∧ (∀ k, 0 < R k) ∧
      ∀ k : ℕ, ((k : ℝ) + 1) * δ ≤ R k := by
  refine ⟨fun k => ((k : ℝ) + 1) * δ, ?_, ?_, ?_, fun k => le_rfl⟩
  · intro k l hkl
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
  · intro L
    refine ⟨⌈a * L / δ⌉₊, ?_⟩
    have h1 : a * L / δ ≤ (⌈a * L / δ⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hδ] at h1
    show a * (L : ℝ) ≤ ((⌈a * L / δ⌉₊ : ℕ) + 1) * δ
    linarith
  · intro k
    exact mul_pos (by positivity) hδ

end Bookkeeping

/-! ## 3. The slice record with one shell field -/

section Slim

variable (N : ℕ) [NeZero N]

/-- **One zero-flux slice with the shell data in one field**: `RunSeedN.SliceEndN` with `κ, v, span, lam, gram, η,
pair, rate` replaced by `diag`, the bound of the zero-flux transfer on each loop shell. -/
structure SliceEndS (c c' σ δ t₀ Cc : ℝ) (β : ℝ) (n : ℕ) (i : Fin 4) : Type 1 where
  /-- Index type of the levels. -/
  ι : Type
  /-- The ground level. -/
  g₀ : ι
  /-- The level energies. -/
  E : ι → ℝ
  /-- The eigenfunctions. -/
  φ : ι → SliceN N n i → ℝ
  /-- The eigenvalues. -/
  μ : ι → ℝ
  /-- Bookkeeping: orthonormal eigenfunctions exhausting both traces. -/
  levels : EigenLevelsN N β n i g₀ E φ μ
  /-- Bookkeeping: each eigenfunction is measurable. -/
  meas : ∀ j, Measurable (φ j)
  /-- The loop family the shells are built on. -/
  fam : LoopFam
  /-- Every excited level lies in the closed span of the loop states of `fam` (proved on `words`,
  `ProcesiSeparation.excited_mem_closure_words_all`). -/
  gen : ∀ j, j ≠ g₀ → vecOf (meas j) (levels.norm j)
    ∈ closure (Submodule.span ℝ (allLoopsN (hSN N n i) (φ g₀) fam) : Set (Lp ℝ 2 (hSN N n i)))
  /-- Bookkeeping: a bound of the kernel. -/
  C : ℝ
  kmeas : Measurable (Function.uncurry (trivKN N β n i))
  C0 : 0 ≤ C
  kbd : ∀ x y, |trivKN N β n i x y| ≤ C
  /-- Bookkeeping: the shell radii (`exists_radii`). -/
  R : ℕ → ℝ
  R_mono : Monotone R
  R_reach : ∀ L : ℕ, ∃ k, aRun N β * (L : ℝ) ≤ R k
  R_pos : ∀ k, 0 < R k
  R_step : ∀ k : ℕ, ((k : ℝ) + 1) * δ ≤ R k
  /-- Physics, open: the zero-flux transfer on the `k`-th loop shell. -/
  diag : ∀ k, ∀ x ∈ shellN (hSN N n i) (φ g₀) fam (aRun N β) R k,
    ‖kernelCLM (trivKN N β n i) C kmeas C0 kbd (hSN N n i) (hSN N n i) x‖ ^ 2
      ≤ μ g₀ ^ 2 * Real.exp (-((c * σ * R k + c' / R k) * ((n : ℝ) * aRun N β))) * ‖x‖ ^ 2
  /-- Physics, open: the count clause at the time `t₀`. -/
  count : ZeroFluxCount g₀ E t₀ Cc

variable {N}

/-- **A `SliceEndN` record gives a `SliceEndS` record**: `pair`, `rate`, `span` and `gram` give `diag`
(`FocusFeed.norm_sq_le_on_span`). DERIVED: no numeral. -/
def SliceEndS.ofN {c c' σ δ t₀ Cc β : ℝ} {n : ℕ} {i : Fin 4} (S : SliceEndN N c c' σ δ t₀ Cc β n i) :
    SliceEndS N c c' σ δ t₀ Cc β n i where
  ι := S.ι
  g₀ := S.g₀
  E := S.E
  φ := S.φ
  μ := S.μ
  levels := S.levels
  meas := S.meas
  fam := S.fam
  gen := S.gen
  C := S.C
  kmeas := S.kmeas
  C0 := S.C0
  kbd := S.kbd
  R := S.R
  R_mono := S.R_mono
  R_reach := S.R_reach
  R_pos := S.R_pos
  R_step := S.R_step
  diag k x hx := by
    letI := S.κfin
    have h := FocusFeed.norm_sq_le_on_span _ (S.v k) (S.pair k) (S.lam_pos k) (S.gram k) x (S.span k hx)
    have hq : (Fintype.card (S.κ k) : ℝ) * S.η k / S.lam k
        ≤ S.μ S.g₀ ^ 2 * Real.exp (-((c * σ * S.R k + c' / S.R k) * ((n : ℝ) * aRun N β))) := by
      rw [div_le_iff₀ (S.lam_pos k), mul_comm _ (S.lam k)]
      exact S.rate k
    exact h.trans (mul_le_mul_of_nonneg_right hq (sq_nonneg _))
  count := S.count

/-- **`diag` gives the zero-flux gap** at `diagRate c c' σ δ (n a)` (`RunSeedN.zeroFluxGap_of_electricDiagN`).
DERIVED: no numeral. -/
theorem SliceEndS.gap {c c' σ δ t₀ Cc β : ℝ} {n : ℕ} {i : Fin 4} (S : SliceEndS N c c' σ δ t₀ Cc β n i)
    (hβ : 0 < β) (hn : 0 < n) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hσ : 0 ≤ σ) (hδ : 0 < c * σ * δ) :
    ZeroFluxGap S.g₀ S.E (diagRate c c' σ δ ((n : ℝ) * aRun N β)) :=
  zeroFluxGap_of_electricDiagN hβ hn S.levels S.meas S.kmeas S.C0 S.kbd S.fam S.R_mono S.R_reach S.gen
    hc hc' hσ hδ S.R_pos S.R_step S.diag

variable (N)

/-- **One slice of the single-window endpoint**: a `SliceEndS` record and the charged levels of every transverse
`ν` on its zero-flux levels. -/
structure EndRunS (c c' σ δ t₀ Cc m Co : ℝ) (β : ℝ) (n : ℕ) (i : Fin 4) : Type 1 where
  core : SliceEndS N c c' σ δ t₀ Cc β n i
  flux : ∀ ν : Dir i, FluxLevels N β n i ν core.g₀ core.E m t₀ Co

/-- **The endpoint at one window `[2ℓ, 5ℓ]`**: `RunSeedN.EndpointNAt` with `SliceEndS` records.
DERIVED: `2` and `5` the window. -/
structure EndpointSAt (c c' σ δ t₀ Cc m Co ℓ : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  c'_nonneg : 0 ≤ c'
  σ_nonneg : 0 ≤ σ
  step_pos : 0 < c * σ * δ
  t₀_nonneg : 0 ≤ t₀
  t₀_le : t₀ ≤ 2 * ℓ
  slices : ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    2 * ℓ ≤ (n : ℝ) * aRun N β → (n : ℝ) * aRun N β ≤ 5 * ℓ → ∀ i : Fin 4,
      Nonempty (EndRunS N c c' σ δ t₀ Cc m Co β n i)

/-- **The single-window endpoint**: constants and one window `ℓ > 0` with `D = diagRate c c' σ δ (2ℓ) > 0`,
`m > 0`, the excited weights at the window below the sector smallness `1/80000`, and `EndpointSAt` there.
DERIVED: `1/80000` the sector smallness of `CentreSectorSeedN.defectW_le_of_sectorsN`; `9 ⌊N/2⌋²` the factor of
`FluxCost.fluxCostAt_of_planeCostAt`; `2` the window's lower end and the twist bound. -/
def EndpointS : Prop :=
  ∃ c c' σ δ t₀ Cc m Co ℓ : ℝ, 0 < ℓ ∧ 0 < diagRate c c' σ δ (2 * ℓ) ∧ 0 < m ∧ 0 ≤ Cc ∧ 0 ≤ Co ∧
    2 * Cc * Real.exp (diagRate c c' σ δ (2 * ℓ) * t₀)
      * Real.exp (-(diagRate c c' σ δ (2 * ℓ) * (2 * ℓ))) ≤ 1 / 80000 ∧
    9 * ((N / 2 : ℕ) : ℝ) ^ 2 * (2 * Co * Real.exp (m * t₀)) * Real.exp (-(m * (2 * ℓ))) ≤ 1 / 80000 ∧
    EndpointSAt N c c' σ δ t₀ Cc m Co ℓ

variable {N}

/-- **The zero-flux half at the window**: `UniformGlueball N (diagRate c c' σ δ (2ℓ)) t₀ Cc ℓ` (`ℓ > 0`).
DERIVED: `2` the window's lower end. -/
theorem uniformGlueball_of_endpointSAt {c c' σ δ t₀ Cc m Co ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : EndpointSAt N c c' σ δ t₀ Cc m Co ℓ) :
    UniformGlueball N (diagRate c c' σ δ (2 * ℓ)) t₀ Cc ℓ := by
  filter_upwards [h.slices, eventually_gt_atTop (0 : ℝ)] with β hS hβ n hn h2 hlo hhi i
  obtain ⟨S⟩ := hS n hn h2 hlo hhi i
  have hn0 : 0 < n := by omega
  have h2ℓ : 0 < 2 * ℓ := by linarith
  have hg := S.core.gap hβ hn0 h.c_nonneg h.c'_nonneg h.σ_nonneg h.step_pos
  exact ⟨S.core.ι, S.core.g₀, S.core.E, S.core.levels.zeroFluxLevels,
    ScaleControl.zeroFluxGap_mono hg (ScaleControl.diagRate_mono h.step_pos h2ℓ hlo), S.core.count⟩

/-- **(T) at the window**: `HiddenCostAt N D (2 Cc e^{D t₀}) ℓ`, `D = diagRate c c' σ δ (2ℓ)` (`ℓ > 0`).
DERIVED: `2` the factor of `GlueballArea.hiddenCostAt_of_uniformGlueball`. -/
theorem hiddenCostAt_of_endpointSAt {c c' σ δ t₀ Cc m Co ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : EndpointSAt N c c' σ δ t₀ Cc m Co ℓ) :
    ObserverTheory.HiddenCostAt N (diagRate c c' σ δ (2 * ℓ))
      (2 * Cc * Real.exp (diagRate c c' σ δ (2 * ℓ) * t₀)) ℓ :=
  GlueballArea.hiddenCostAt_of_uniformGlueball h.t₀_nonneg h.t₀_le (uniformGlueball_of_endpointSAt hℓ h)

/-- **(V) at the window**: `PlaneCostAt N m (2 Co e^{m t₀}) ℓ`. DERIVED: `2` the twist bound. -/
theorem planeCostAt_of_endpointSAt {c c' σ δ t₀ Cc m Co ℓ : ℝ}
    (h : EndpointSAt N c c' σ δ t₀ Cc m Co ℓ) :
    FluxCost.PlaneCostAt N m (2 * Co * Real.exp (m * t₀)) ℓ := by
  filter_upwards [h.slices, eventually_ge_atTop (0 : ℝ)] with β hS hβ0 n hn h2 hlo hhi i ν
  obtain ⟨R⟩ := hS n hn h2 hlo hhi i
  exact one_sub_twistRatioN_le_of_fluxLevels hβ0 ν R.core.levels (R.flux ν) (h.t₀_le.trans hlo)

/-- **The run seed from one window**: `EndpointS N → WDeltaRun.RunSeed N`, with the seed at the power of two
`2^⌈log₂ ⌈2ℓ/a⌉⌉ ∈ [2ℓ, 5ℓ]` and `C = 5ℓ`. DERIVED: `5` the window's upper end; `1/80000` the sector smallness;
`2` the least side. -/
theorem runSeed_of_endpointS (h : EndpointS N) : WDeltaRun.RunSeed N := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  obtain ⟨c, c', σ, δ, t₀, Cc, m, Co, ℓ, hℓ, hD, hm, hCc, hCo, hsT, hsV, hE⟩ := h
  have hH := hiddenCostAt_of_endpointSAt hℓ hE
  have hF := FluxCost.fluxCostAt_of_planeCostAt (planeCostAt_of_endpointSAt hE)
  refine ⟨5 * ℓ, by positivity, ?_⟩
  filter_upwards [hF, hH, eventually_gt_atTop (0 : ℝ),
    WeakCouplingWindow.eventually_aRun_le hN (b := ℓ / 2) (by positivity)] with β hFβ hHβ hβ0 hale
  set a := aRun N β with ha_def
  have ha : 0 < a := aRun_pos hN hβ0
  obtain ⟨h2, hna⟩ := DoublingClay2.nP_bounds hℓ ha hale
  set k := Nat.clog 2 ⌈2 * ℓ / a⌉₊ with hk
  have hlow : 2 * ℓ ≤ ((2 ^ k : ℕ) : ℝ) * a := by
    have h1 : ⌈2 * ℓ / a⌉₊ ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) _
    have h3 : 2 * ℓ / a ≤ ((2 ^ k : ℕ) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rwa [div_le_iff₀ ha] at h3
  have hup : ((2 ^ k : ℕ) : ℝ) * a ≤ 5 * ℓ := by linarith
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at h2; norm_num at h2
    · exact h0
  refine ⟨2 ^ k, ⟨k, rfl⟩, h2, hup, ?_⟩
  refine CentreSectorSeedN.defectW_le_of_sectorsN hβ0.le h2 (DeltaLengthTower.even_two_pow hk1)
    (fun i => ⟨?_, ?_⟩)
  · have h1 := hFβ (2 ^ k) ⟨k, rfl⟩ h2 hlow hup i
    have he : Real.exp (-(m * (((2 ^ k : ℕ) : ℝ) * a))) ≤ Real.exp (-(m * (2 * ℓ))) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hlow hm.le))
    have hA : 0 ≤ 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * (2 * Co * Real.exp (m * t₀)) := by positivity
    exact h1.trans ((mul_le_mul_of_nonneg_left he hA).trans hsV)
  · have h1 := hHβ (2 ^ k) ⟨k, rfl⟩ h2 hlow hup i
    have he : Real.exp (-(diagRate c c' σ δ (2 * ℓ) * (((2 ^ k : ℕ) : ℝ) * a)))
        ≤ Real.exp (-(diagRate c c' σ δ (2 * ℓ) * (2 * ℓ))) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hlow hD.le))
    have hA : 0 ≤ 2 * Cc * Real.exp (diagRate c c' σ δ (2 * ℓ) * t₀) := by positivity
    exact h1.trans ((mul_le_mul_of_nonneg_left he hA).trans hsT)

/-- **`EndpointN` gives the single-window endpoint**: `EndpointN N → EndpointS N`, at a window `ℓ ≥ ℓ₀` visited by
`EndpointN` where `2 Cc e^{M t₀} e^{−2 D₀ ℓ}` and `9 ⌊N/2⌋² 2 Co e^{m t₀} e^{−2mℓ}` are at most `1/80000`
(`D₀ = diagRate(2ℓ₀)`, `M = √(c c' σ) + cσδ/2`). DERIVED: `1/80000` the sector smallness; `2` the window's lower
end. -/
theorem endpointS_of_endpointN (h : EndpointN N) : EndpointS N := by
  obtain ⟨c, c', σ, δ, t₀, Cc, m, Co, ℓ₀, hℓ₀, hpos, hm, hCc, hCo, hfr⟩ := h
  have hs1 := ObserverTheory.eventually_small
    (c := 2 * Cc * Real.exp ((Real.sqrt (c * c' * σ) + c * σ * δ / 2) * t₀))
    (σ' := 2 * diagRate c c' σ δ (2 * ℓ₀)) (by linarith) (by norm_num : (0 : ℝ) < 1 / 80000)
  have hs2 := ObserverTheory.eventually_small
    (c := 9 * ((N / 2 : ℕ) : ℝ) ^ 2 * (2 * Co * Real.exp (m * t₀)))
    (σ' := 2 * m) (by linarith) (by norm_num : (0 : ℝ) < 1 / 80000)
  obtain ⟨ℓ, hR, hℓ, ⟨hℓ0, h1⟩, -, h2⟩ :=
    (hfr.and_eventually ((eventually_ge_atTop ℓ₀).and (hs1.and hs2))).exists
  have h2ℓ₀ : 0 < 2 * ℓ₀ := by linarith
  have h2ℓ : 0 < 2 * ℓ := by linarith
  have hmono := ScaleControl.diagRate_mono (c' := c') hR.step_pos h2ℓ₀ (by linarith : 2 * ℓ₀ ≤ 2 * ℓ)
  have hsup := ScaleControlRun.diagRate_le_sup (c' := c') h2ℓ hR.step_pos
  refine ⟨c, c', σ, δ, t₀, Cc, m, Co, ℓ, hℓ0, hpos.trans_le hmono, hm, hCc, hCo, ?_, ?_, ?_⟩
  · have ea : Real.exp (diagRate c c' σ δ (2 * ℓ) * t₀)
        ≤ Real.exp ((Real.sqrt (c * c' * σ) + c * σ * δ / 2) * t₀) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hsup hR.t₀_nonneg)
    have eb : Real.exp (-(diagRate c c' σ δ (2 * ℓ) * (2 * ℓ)))
        ≤ Real.exp (-(2 * diagRate c c' σ δ (2 * ℓ₀) * ℓ)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [mul_le_mul_of_nonneg_right hmono hℓ0.le]
    calc 2 * Cc * Real.exp (diagRate c c' σ δ (2 * ℓ) * t₀)
          * Real.exp (-(diagRate c c' σ δ (2 * ℓ) * (2 * ℓ)))
        ≤ 2 * Cc * Real.exp ((Real.sqrt (c * c' * σ) + c * σ * δ / 2) * t₀)
          * Real.exp (-(2 * diagRate c c' σ δ (2 * ℓ₀) * ℓ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left ea (by positivity)) eb (Real.exp_pos _).le
            (by positivity)
      _ ≤ 1 / 80000 := h1
  · have e : m * (2 * ℓ) = 2 * m * ℓ := by ring
    rw [e]
    exact h2
  · exact
      { c_nonneg := hR.c_nonneg
        c'_nonneg := hR.c'_nonneg
        σ_nonneg := hR.σ_nonneg
        step_pos := hR.step_pos
        t₀_nonneg := hR.t₀_nonneg
        t₀_le := hR.t₀_le
        slices := by
          filter_upwards [hR.slices] with β hS n hn h2' hlo hhi i
          obtain ⟨R⟩ := hS n hn h2' hlo hhi i
          exact ⟨⟨SliceEndS.ofN R.core, R.flux⟩⟩ }

end Slim

/-! ## 4. The fixed-`t₀` count: a conditional no-go -/

section NoGo

variable (N : ℕ) [NeZero N]

/-- **The low-level count of the window slices exceeds every bound**: for every `K`, eventually in `ℓ` and
frequently in `β`, some power-of-two side `n ≥ 2` with `n a ∈ [2ℓ, 5ℓ]` and some step `i` have, on every
spectral resolution of the zero-flux transfer (`EigenLevelsN`), more than `K` levels within `D` of the ground.
Argued (§4 of the module docstring), not proved: the one-glueball momentum states give `∼ (L·p_D)³` such levels
with `L ≥ 2ℓ`. DERIVED: `2` the least side and the window's lower end; `5` the window's upper end. -/
def LevelsUnbounded (D : ℝ) : Prop :=
  ∀ K : ℝ, ∀ᶠ ℓ in atTop, ∃ᶠ β in atTop, ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
    2 * ℓ ≤ (n : ℝ) * aRun N β ∧ (n : ℝ) * aRun N β ≤ 5 * ℓ ∧ ∃ i : Fin 4,
      ∀ (ι : Type) (g₀ : ι) (E : ι → ℝ) (φ : ι → SliceN N n i → ℝ) (μ : ι → ℝ),
        EigenLevelsN N β n i g₀ E φ μ →
          ∃ S : Finset ι, (∀ j ∈ S, E j - E g₀ ≤ D) ∧ K < (S.card : ℝ)

variable {N}

/-- **No-go for the fixed-`t₀` endpoint**: unbounded low-level counts on the window slices rule out `EndpointN N`.
`EndpointN` fixes `t₀` and `Cc` for every window it visits, and `card_mul_exp_le_of_count` bounds the number of
levels within `D` of the ground on each of its slices by `(1 + Cc) e^{D t₀}`. DERIVED: `1` the ground weight. -/
theorem not_endpointN_of_levels_unbounded {D : ℝ} (h : LevelsUnbounded N D) : ¬ EndpointN N := by
  rintro ⟨c, c', σ, δ, t₀, Cc, m, Co, ℓ₀, -, -, -, -, -, hfr⟩
  obtain ⟨ℓ, hE, hL⟩ := (hfr.and_eventually (h ((1 + Cc) * Real.exp (D * t₀)))).exists
  obtain ⟨β, ⟨n, hn, h2, hlo, hhi, i, hlev⟩, hS⟩ := (hL.and_eventually hE.slices).exists
  obtain ⟨R⟩ := hS n hn h2 hlo hhi i
  obtain ⟨S, hSD, hK⟩ := hlev _ _ _ _ _ R.core.levels
  have hc := card_mul_exp_le_of_count hE.t₀_nonneg R.core.count S hSD
  have h1 := mul_lt_mul_of_pos_right hK (Real.exp_pos (-(D * t₀)))
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h1
  linarith

end NoGo

end MassGap.EndpointAudit

end

#print axioms MassGap.EndpointAudit.zeroFluxGap_iff_heatW
#print axioms MassGap.EndpointAudit.card_mul_exp_le_of_count
#print axioms MassGap.EndpointAudit.tsum_heatW_two_levels
#print axioms MassGap.EndpointAudit.exists_not_count_of_gap_count
#print axioms MassGap.EndpointAudit.level_gap_of_trace
#print axioms MassGap.EndpointAudit.exists_pair_bound
#print axioms MassGap.EndpointAudit.exists_radii
#print axioms MassGap.EndpointAudit.SliceEndS.ofN
#print axioms MassGap.EndpointAudit.SliceEndS.gap
#print axioms MassGap.EndpointAudit.uniformGlueball_of_endpointSAt
#print axioms MassGap.EndpointAudit.hiddenCostAt_of_endpointSAt
#print axioms MassGap.EndpointAudit.planeCostAt_of_endpointSAt
#print axioms MassGap.EndpointAudit.runSeed_of_endpointS
#print axioms MassGap.EndpointAudit.endpointS_of_endpointN
#print axioms MassGap.EndpointAudit.not_endpointN_of_levels_unbounded
