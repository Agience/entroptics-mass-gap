import Mathlib
import MassGap.OpenAIBridgeUniform
import MassGap.DoublingWilsonG
import MassGap.TorusChainG
import MassGap.OpenAIConfig

/-!
# MassGap.OpenAIBridgeGroups — the torus gap and clustering over every compact gauge group

`DoublingSharp.wilson_gap_sharp`, `OpenAIBridgeSides.gap_even_side` and
`OpenAIBridgeUniform.wilson_conn_even_side` are stated for `SU(N)`. None of their proofs uses a fact
about `SU(N)` as a group: every use is through the transfer kernel of one slice — symmetric,
continuous, with values in `[kTmin, 1]` at `β ≥ 0` — and the identity of the partition function with
its cyclic trace. `RectTransferG` proves those for every `GaugeGroup G` (`kTG_symm`,
`continuous_kTG`, `kTG_lower`, `abs_kTG_le`, `ZRG_eq_traceSeq`, `ZRG_eq_cyc`), `DoublingWilsonG`
the four trace facts (`factRepG`), and `TorusChainG` the chain form of the Wilson torus over `G`
(`corrNum_eqG`). This module reads the three proofs on those objects.

## 1. The dyadic tori

* `Δ_corner0_ZRG` — the corner function at `0` is `16 log ZRG(n) − log ZRG(2n)`;
* `wilson_gap_sharpG` — `wilson_gap_sharp` over `G`: from the seed `16 log ZRG(n⁴) − log ZRG((2n)⁴)
  ≤ 1/1000` at `β ≥ 0`, the slice transfer of the torus of side `2^k n` has a unit top eigenvector
  and `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` off it.

## 2. Every even side `L ≥ 2n`

* `seqFactsG`, `yWG`, `yWG_at`, `yWG_next`, `climb_yWG` — the mixed-ratio climb of
  `OpenAIBridgeSides` on the corner function of `G` (`climb`, `stepC`, `raised_nonneg`, `raised_sq`,
  `sides_base`, `exists_window` are group-free and reused);
* `gap_side_excitedG` — the gap on the slice of side `L`, `2^(a+1) n ≤ L ≤ 2^(a+3) n`, with the excited
  weight the climb bounds;
* `gap_even_sideG` — the gap at every even `L ≥ 2n`; `cluster_even_sideG` — the clustering of the
  transfer state there (Theorem 4.47 in state form);
* `connTorus_even_side_uniformG` — `|connTorus| ≤ 6 A B ((1/2)^⌊t/n⌋ + (1/2)^⌊(L−t)/n⌋)`.

## 3. The trace identity with insertions

* `Zc_trPairG`, `spSliceG`, `spSliceG_joinWG`, `corrNum_slabG`, `ZRG_eq_trPowG`,
  `connTorus_eq_expectG` — the connected trace ratio is the connected Wilson correlation of the cubic
  torus of `G`;
* `wilson_conn_even_sideG` — `|⟨a_0 b_{p+1}⟩ − ⟨a_0⟩⟨b_{p+1}⟩| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ +
  (1/2)^⌊(q+1)/n⌋)` on the cubic Wilson torus of `G` of every even side `L ≥ 2n`, from the seed.

## 4. On the OpenAI laws of every closed matrix group

Their gauge group is any closed subgroup `g.image ≤ U(n+1)` (`OpenAIConfig.GaugeGroup`), which
`OpenAIConfig.instGaugeGroupImage` makes one of ours, with our density their summand
(`OpenAIConfig.wilsonDensityG_image`). No group isomorphism is needed.

* `eq_probHaar_image` — their probability Haar measure is our `probHaar g.image`;
* `expect_eq_openAILawG` — our expectation on the cubic torus of side `L` at `β` of `O ∘ configEquiv`
  is the integral of `O` against their law at `2β`;
* `familyGap_on_openAI_lawsG` — Theorem 4.46 on their laws: for all large `m`, every torus of the
  family of even side at least twice the seed side carries their law at `β m p` as our law at
  `β m p / 2`, and its transfer operator has the gap;
* `familyConn_on_openAI_lawsG` — Theorem 4.47 on their laws: the connected correlation of two
  slice observables under their law, uniform in the spacing, the torus and the observables.

The simplicity of their Lie algebra is not used: the statements hold for every closed subgroup of
`U(n+1)`. The seed hypothesis is the open input, as at `SU(N)`.
-/

namespace MassGap.OpenAIBridgeGroups

open MeasureTheory Real MassGap MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG
  MassGap.KernelPower MassGap.DoublingRecursion MassGap.SlabKernelOperator MassGap.DoublingWilson
  MassGap.DoublingWilsonG MassGap.GaugeGroup MassGap.CompactGauge MassGap.OpenAIBridgeSides
  MassGap.OpenAIBridgeCluster MassGap.OpenAIBridgeUniform

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-! ## 1. The dyadic tori -/

section Wilson

variable (G) in
/-- **The corner function of `G` at `0`** is the seed of `wilson_gap_sharp`:
`Δ (xWG G n β) 0 = 16 log ZRG(n⁴) − log ZRG((2n)⁴)`. It is `DoublingWilson.Δ_corner0` over `G`.

DERIVED: `16 = 2⁴` the number of side-`n` tori in the side-`2n` torus; `2` the doubled side; `0` the
base corner. -/
theorem Δ_corner0_ZRG (n : ℕ) (β : ℝ) :
    Δ (xWG G n β) (corner 0)
      = 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) := by
  unfold Δ xWG; rw [corner0, corner1]

variable {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)

include hβ hn he in
/-- **The gap of the seed on the dyadic tori of `G`** (`DoublingSharp.wilson_gap_sharp` over a
`GaugeGroup G`). If one torus of even side `n ≥ 2` has `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at
`β ≥ 0`, then for every `k` the transfer operator `K` in direction `0` of the torus of side `2^k n` has
a unit eigenvector `ψ` with eigenvalue of modulus `‖K‖`, and `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` for every
`f ⊥ ψ`. The proof is that of `wilson_gap_sharp` on `DoublingWilsonG.factRepG`, `RectTransferG.kTG`
and `DoublingWilsonG.K_posG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the doubled side, the least seed
side, the `L²` exponent and the contraction `1/2`; `0` the time direction of the slice and the sign
of the coupling; `1` the unit norm and the kernel bound. -/
theorem wilson_gap_sharpG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (k : ℕ) :
    ∃ ψ : Lp ℝ 2 (hSG G 0 (tr (ext n (corner k)) 0)), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kTG G 0 (tr (ext n (corner k)) 0) β) 1
          (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
          (hSG G 0 (tr (ext n (corner k)) 0)) (hSG G 0 (tr (ext n (corner k)) 0))‖ ∧
      kernelCLM (kTG G 0 (tr (ext n (corner k)) 0) β) 1 (continuous_kTG β).measurable zero_le_one
          (abs_kTG_le hβ) (hSG G 0 (tr (ext n (corner k)) 0))
          (hSG G 0 (tr (ext n (corner k)) 0)) ψ = c • ψ ∧
      ∀ f : Lp ℝ 2 (hSG G 0 (tr (ext n (corner k)) 0)), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kTG G 0 (tr (ext n (corner k)) 0) β) 1 (continuous_kTG β).measurable
          zero_le_one (abs_kTG_le hβ) (hSG G 0 (tr (ext n (corner k)) 0))
          (hSG G 0 (tr (ext n (corner k)) 0))) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kTG G 0 (tr (ext n (corner k)) 0) β) 1
            (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
            (hSG G 0 (tr (ext n (corner k)) 0)) (hSG G 0 (tr (ext n (corner k)) 0))‖ ^ n
            * ‖f‖ := by
  set T := tr (ext n (corner k)) 0
  have hfr := factRepG (G := G) hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hx := DoublingSharp.positiveS_of_facts hfr
  have hΔ : Δ (xWG G n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0_ZRG]; exact h0
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hSG G 0 T) (continuous_kTG β) zero_le_one (abs_kTG_le hβ)
      (kTG_symm β) (K_posG hβ 0 T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_posG (G := G) hβ 0 T]
  obtain ⟨n', hn'⟩ := he
  set j := 2 ^ k * n' with hjdef
  have hj : 1 ≤ j := by
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by omega
    rw [hjdef]; exact Nat.mul_le_mul h1 h2
  have hpf := powerFacts (μ := hSG G 0 T) (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ) (kTG_symm β) hφm hφb hφ1 heig hc hc0 j hj
  have hm : ext n (corner k) 0 = 2 * j := by simp only [ext, corner, hjdef, hn']; ring
  have h1 : xWG G n β (corner k) = Real.log (FG G β 0 T (2 * j)) := by
    rw [xWG_eq hβ hn ⟨n', hn'⟩ (corner k) 0, hm]
  have h2 : xWG G n β (corner k + E 0) = Real.log (FG G β 0 T (2 * (2 * j))) := by
    rw [xWG_eq hβ hn ⟨n', hn'⟩ (corner k + E 0) 0, tr_ext_add, ext_add_self, hm]
  have hexc := DoublingSharp.excited_le_corner_sharp hx hp hΔ k hpf h1 h2
  have hidx : 2 ^ k * n / 2 = j := by
    rw [hn', hjdef, show 2 ^ k * (n' + n') = 2 * (2 ^ k * n') by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  refine ⟨KernelGap.vac (μ := hSG G 0 T) hφm hφb, KernelGap.norm_vac hφm hφb hφ1, c, hc,
    KernelGap.K_vac _ _ _ hφm hφb heig, fun f hf => ?_⟩
  exact KernelGap.gap_of_excited (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (kTG_symm β) hφm hφb hφ1 heig hc hc0 k n (by omega) ⟨n', hn'⟩ (by rw [hidx]; exact hexc) f hf

/-! ## 2. The gap on every even side -/

include hβ in
/-- **The trace facts on one slice of `G`, at the times `2j`, `4j` and `L`**
(`OpenAIBridgeSides.seqFacts` over `G`). For the transfer kernel `kTG` of the slice `T`, `j ≥ 1` and
an even `L ≥ 4j`: the four trace facts at `2j` with `λ = ‖K‖`, and `F L ≤ λ^{L − 4j} F(4j)`
(`hs_iter_le`), `λ^L ≤ F L` (`hs_iter_decomp`).

DERIVED: no numeral beyond the structural ones; `2` is the even time and its doubling, and the
`L²` exponent of `hs`. -/
theorem seqFactsG (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) (j : ℕ) (hj : 1 ≤ j) (L : ℕ)
    (hLe : Even L) (hL : 2 * (2 * j) ≤ L) :
    ∃ lam s : ℝ, DoublingPower.PowerFacts (FG G β μ T) lam s (2 * j) ∧
      FG G β μ T L ≤ lam ^ (L - 2 * (2 * j)) * FG G β μ T (2 * (2 * j)) ∧
      lam ^ L ≤ FG G β μ T L := by
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hSG G μ T) (continuous_kTG β) zero_le_one (abs_kTG_le hβ)
      (kTG_symm β) (K_posG hβ μ T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_posG (G := G) hβ μ T]
  have hpf := powerFacts (μ := hSG G μ T) (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ) (kTG_symm β) hφm hφb hφ1 heig hc hc0 j hj
  refine ⟨|c|, _, hpf, ?_, ?_⟩
  · obtain ⟨L', rfl⟩ := hLe
    unfold FG traceSeq
    have e1 : (L' + L') / 2 - 1 = (2 * j - 1) + (L' - 2 * j) := by omega
    have e2 : 2 * (2 * j) / 2 - 1 = 2 * j - 1 := by omega
    have e3 : L' + L' - 2 * (2 * j) = 2 * (L' - 2 * j) := by omega
    rw [e1, e2, e3, hc]
    exact hs_iter_le (μ := hSG G μ T) (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
      (2 * j - 1) (L' - 2 * j)
  · obtain ⟨L', rfl⟩ := hLe
    unfold FG traceSeq
    rw [hs_iter_decomp (μ := hSG G μ T) (bdd_kTG hβ) (kTG_symm β) hφm hφb hφ1 heig
      ((L' + L') / 2 - 1)]
    have e : (L' + L') / 2 - 1 + 1 = L' := by omega
    rw [e]
    have hpow : c ^ (2 * L') = |c| ^ (L' + L') := by
      rw [pow_mul, ← sq_abs, ← pow_mul]; ring_nf
    rw [hpow]
    linarith [hs_nonneg (μ := hSG G μ T)
      (iter (hSG G μ T) (rem (kTG G μ T β) c φ) ((L' + L') / 2 - 1))]

variable (G) in
/-- The corner function of `G` on the levels `m0, 2 m0, L`: `log ZRG` of the Wilson torus of `G` at
corner `v` (`OpenAIBridgeSides.yW` over `G`).

DERIVED: no numeral. -/
noncomputable def yWG (m0 L : ℕ) (β : ℝ) (v : Pt) : ℝ := Real.log (ZRG G (sides m0 L v) β)

include hβ in
/-- At every corner and in every direction `μ`, `yWG` is the logarithm of the trace sequence of the
slice transverse to `μ` at the level of `μ`, when the three levels are even and positive
(`OpenAIBridgeSides.yW_at` over `G`).

DERIVED: no numeral beyond the structural ones; `2` is the even side. -/
theorem yWG_at {j0 L : ℕ} (hj0 : 1 ≤ j0) (hLe : Even L) (hL2 : 2 ≤ L) (v : Pt) (μ : Fin 4) :
    yWG G (2 * j0) L β v
      = Real.log (FG G β μ (tr (sides (2 * j0) L v) μ) (lev (2 * j0) L (v μ))) := by
  have hev : ∃ i, 1 ≤ i ∧ sides (2 * j0) L v μ = 2 * i := by
    show ∃ i, 1 ≤ i ∧ lev (2 * j0) L (v μ) = 2 * i
    unfold lev
    split_ifs
    · exact ⟨j0, hj0, rfl⟩
    · exact ⟨2 * j0, by omega, rfl⟩
    · obtain ⟨L', hL'⟩ := hLe; exact ⟨L', by omega, by omega⟩
  obtain ⟨i, hi, hiL⟩ := hev
  unfold yWG FG
  rw [ZRG_eq_traceSeq (μ := μ) hβ i hi hiL]
  rfl

include hβ in
/-- One step in direction `μ` from `v`: the same slice of `G` at the next level
(`OpenAIBridgeSides.yW_next` over `G`).

DERIVED: `2` is the even side; `1` the step. -/
theorem yWG_next {j0 L : ℕ} (hj0 : 1 ≤ j0) (hLe : Even L) (hL2 : 2 ≤ L) (v : Pt) (μ : Fin 4) :
    yWG G (2 * j0) L β (v + E μ)
      = Real.log (FG G β μ (tr (sides (2 * j0) L v) μ) (lev (2 * j0) L (v μ + 1))) := by
  rw [yWG_at (G := G) hβ hj0 hLe hL2 (v + E μ) μ, tr_sides_add, add_E_self]

include hβ in
/-- **`Climb` for the Wilson corner function of `G`** (`OpenAIBridgeSides.climb_yW` over `G`). With
levels `2j0`, `4j0`, `L` (`j0 ≥ 1`, `L` even, `L ≥ 4j0`) and the ratio `ρ = L / 4j0 ∈ [1, 4]`,
`yWG G (2j0) L β` satisfies the three facts of `Climb`, each on the trace sequence of the slice of
`seqFactsG`.

DERIVED: no numeral beyond the structural ones; `2` is the doubled side and `4` the largest
ratio. -/
theorem climb_yWG {ρ : ℝ} {j0 L : ℕ} (hj0 : 1 ≤ j0) (hLe : Even L) (hL4 : 2 * (2 * j0) ≤ L)
    (hρ : ρ * (2 * ((2 * j0 : ℕ) : ℝ)) = L) (hρ1 : 1 ≤ ρ) (hρ4 : ρ ≤ 4) :
    Climb (yWG G (2 * j0) L β) ρ := by
  have hL2 : 2 ≤ L := by omega
  have l0 : lev (2 * j0) L 0 = 2 * j0 := by simp [lev]
  have l1 : lev (2 * j0) L (0 + 1) = 2 * (2 * j0) := by simp [lev]
  have l1' : lev (2 * j0) L 1 = 2 * (2 * j0) := by simp [lev]
  have l2 : lev (2 * j0) L (1 + 1) = L := by simp [lev]
  refine ⟨fun μ v _ h0 => ?_, fun μ v _ h1 => ?_, fun μ v _ h0 hd => ?_⟩
  · obtain ⟨lam, s, hpf, -, -⟩ :=
      seqFactsG (G := G) hβ μ (tr (sides (2 * j0) L v) μ) j0 hj0 L hLe hL4
    have := DoublingPower.defect_nonneg hpf
    rw [p, yWG_at (G := G) hβ hj0 hLe hL2 v μ, yWG_next (G := G) hβ hj0 hLe hL2 v μ, h0, l0, l1]
    exact this
  · obtain ⟨lam, s, hpf, hup, hlow⟩ :=
      seqFactsG (G := G) hβ μ (tr (sides (2 * j0) L v) μ) j0 hj0 L hLe hL4
    rw [pr, yWG_at (G := G) hβ hj0 hLe hL2 v μ, yWG_next (G := G) hβ hj0 hLe hL2 v μ, h1, l1', l2]
    exact raised_nonneg hpf hL4 hup hlow hρ hρ1
  · obtain ⟨lam, s, hpf, -, hlow⟩ :=
      seqFactsG (G := G) hβ μ (tr (sides (2 * j0) L v) μ) j0 hj0 L hLe hL4
    have hpd : p (yWG G (2 * j0) L β) μ v
        = DoublingPower.defect (FG G β μ (tr (sides (2 * j0) L v) μ)) (2 * j0) := by
      rw [p, yWG_at (G := G) hβ hj0 hLe hL2 v μ, yWG_next (G := G) hβ hj0 hLe hL2 v μ, h0, l0, l1]
      rfl
    rw [hpd] at hd ⊢
    have hv1 : (v + E μ) μ = 1 := by rw [add_E_self, h0]
    rw [pr, yWG_at (G := G) hβ hj0 hLe hL2 (v + E μ) μ, yWG_next (G := G) hβ hj0 hLe hL2 (v + E μ) μ,
      tr_sides_add, hv1, l1', l2]
    exact raised_sq hpf hlow hρ (by linarith) hρ4 hd

include hβ hn he in
/-- **The gap of the seed on the slice of `G` of side `L`, `2^(a+1) n ≤ L ≤ 2^(a+3) n`, with its
excited weight** (`OpenAIBridgeUniform.gap_side_excited` over `G`). If one torus of even side `n ≥ 2`
has `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then the slice kernel `kTG` of the cubic
torus of side `L` has a normalized bounded eigenfunction `φ` with eigenvalue `c ≠ 0`, `|c| = ‖K‖`,
the gap `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` off `φ`, and a level `j0 ≥ 1` with `4 j0 ≤ L` at which the excited
weight is at most `(1/2)^{2^a}`. `DoublingSharp.iterate_sharp` climbs the dyadic corners to `a`,
`climb` takes one step of ratio `L / 2^(a+1) n ∈ [1, 4]`, and `KernelGap.gap_of_excited` gives the
gap.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `3` is the exponent of the largest
ratio `4 = 2^(3−1)` above the level `2^(a+1) n`; `2` the doubled side, the least seed side, the `L²`
exponent, the contraction `1/2` and the two doublings in `2 (2 j0) ≤ L`; `0` the time direction of
the slice, the sign of the coupling and the excluded eigenvalue; `1` the unit norm, the kernel
bound, the first level and the least `j0`. -/
theorem gap_side_excitedG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (a L : ℕ) (hLe : Even L) (hlo : 2 ^ (a + 1) * n ≤ L) (hhi : L ≤ 2 ^ (a + 3) * n) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → G) → ℝ, ∃ hφm : Measurable φ, ∃ Bφ : ℝ,
      ∃ hφb : ∀ x, |φ x| ≤ Bφ, ∫ x, φ x ^ 2 ∂(hSG G 0 (tr (fun _ : Fin 4 => L) 0)) = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧
      (∀ z, ∫ y, kTG G 0 (tr (fun _ : Fin 4 => L) 0) β z y * φ y
        ∂(hSG G 0 (tr (fun _ : Fin 4 => L) 0)) = c * φ z) ∧
      |c| = ‖kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1
          (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))‖ ∧
      (∀ f : Lp ℝ 2 (hSG G 0 (tr (fun _ : Fin 4 => L) 0)),
        inner ℝ f (KernelGap.vac (μ := hSG G 0 (tr (fun _ : Fin 4 => L) 0)) hφm hφb) = 0 →
        ‖((kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1 (continuous_kTG β).measurable
          zero_le_one (abs_kTG_le hβ) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0))) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1
            (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
            (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))‖ ^ n
            * ‖f‖) ∧
      ∃ j0 : ℕ, 1 ≤ j0 ∧ 2 * (2 * j0) ≤ L ∧
        excited (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β)
          c φ j0 ≤ (1 / 2) ^ (2 ^ a) := by
  set T := tr (fun _ : Fin 4 => L) 0 with hTdef
  -- the dyadic climb to corner `a`
  have hfr := factRepG (G := G) hβ hn he
  have hp := DoublingPower.positive_of_facts hfr
  have hxs := DoublingSharp.positiveS_of_facts hfr
  have hΔ0 : Δ (xWG G n β) (corner 0) ≤ 1 / 1000 := by rw [Δ_corner0_ZRG]; exact h0
  have hit := DoublingSharp.iterate_sharp hxs hp (by linarith) a
  have hq1 : ((1 : ℝ) / 4) ^ (2 ^ a) ≤ 1 / 4 := by
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 4) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := a))
    simpa using this
  have hq0 : 0 ≤ ((1 : ℝ) / 4) ^ (2 ^ a) := by positivity
  -- the levels
  obtain ⟨n', hn'⟩ := he
  set j0 := 2 ^ a * n' with hj0def
  have hj0 : 1 ≤ j0 := by
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have h2 : 1 ≤ n' := by omega
    rw [hj0def]; exact Nat.mul_le_mul h1 h2
  have hm0 : 2 * j0 = 2 ^ a * n := by rw [hj0def, hn']; ring
  have hL4 : 2 * (2 * j0) ≤ L := by
    have : 2 * (2 * j0) = 2 ^ (a + 1) * n := by rw [hm0, pow_succ]; ring
    omega
  have hL8 : L ≤ 4 * (2 * (2 * j0)) := by
    have : 4 * (2 * (2 * j0)) = 2 ^ (a + 3) * n := by rw [hm0, pow_add]; ring
    omega
  have hM : (0 : ℝ) < 2 * ((2 * j0 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((2 * j0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * j0)
    linarith
  set ρ : ℝ := (L : ℝ) / (2 * ((2 * j0 : ℕ) : ℝ)) with hρdef
  have hρ : ρ * (2 * ((2 * j0 : ℕ) : ℝ)) = L := by rw [hρdef]; field_simp
  have hρ1 : 1 ≤ ρ := by
    rw [hρdef, le_div_iff₀ hM, one_mul]
    exact_mod_cast hL4
  have hρ4 : ρ ≤ 4 := by
    rw [hρdef, div_le_iff₀ hM]
    exact_mod_cast hL8
  have hx := climb_yWG (G := G) hβ hj0 hLe hL4 hρ hρ1 hρ4
  -- the base of the mixed lattice is the dyadic corner `a`
  have hbase : Δ (yWG G (2 * j0) L β) ![0, 0, 0, 0] = Δ (xWG G n β) (corner a) := by
    obtain ⟨s0, s1⟩ := sides_base n a L hm0
    unfold Δ yWG xWG
    rw [s0, s1]
  have hD : Δ (yWG G (2 * j0) L β) ![0, 0, 0, 0] ≤ 1 / 1000 := by rw [hbase]; linarith
  have hcl := climb hx hρ4 hD
  rw [hbase] at hcl
  -- the eigenvector on the slice of side `L`
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hSG G 0 T) (continuous_kTG β) zero_le_one (abs_kTG_le hβ)
      (kTG_symm β) (K_posG hβ 0 T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_posG (G := G) hβ 0 T]
  have hpf : DoublingPower.PowerFacts (FG G β 0 T) |c|
      (excited (hSG G 0 T) (kTG G 0 T β) c φ j0) (2 * j0) :=
    powerFacts (μ := hSG G 0 T) (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
      (kTG_symm β) hφm hφb hφ1 heig hc hc0 j0 hj0
  have hL2 : 2 ≤ L := by omega
  have hpd : p (yWG G (2 * j0) L β) 0 ![0, 2, 2, 2]
      = DoublingPower.defect (FG G β 0 T) (2 * j0) := by
    have hv : (![0, 2, 2, 2] : Pt) 0 = 0 := rfl
    have l0 : lev (2 * j0) L 0 = 2 * j0 := by simp [lev]
    have l1 : lev (2 * j0) L (0 + 1) = 2 * (2 * j0) := by simp [lev]
    rw [p, yWG_at (G := G) hβ hj0 hLe hL2 ![0, 2, 2, 2] 0,
      yWG_next (G := G) hβ hj0 hLe hL2 ![0, 2, 2, 2] 0, tr_sides_top, hv, l0, l1]
    rfl
  rw [hpd] at hcl
  have hd14 : DoublingPower.defect (FG G β 0 T) (2 * j0) ≤ 1 / 4 := by nlinarith
  have hexc0 := DoublingPower.excited_le_two_defect hpf hd14
  have hhalf : ((1 : ℝ) / 4) ^ (2 ^ a) ≤ (1 / 2) ^ (2 ^ a) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hexc : excited (hSG G 0 T) (kTG G 0 T β) c φ j0 ≤ (1 / 2) ^ (2 ^ a) := by nlinarith
  have hidx : 2 ^ a * n / 2 = j0 := by rw [← hm0]; omega
  refine ⟨φ, hφm, B, hφb, hφ1, c, hc0, heig, hc, fun f hf => ?_, j0, hj0, hL4, hexc⟩
  exact KernelGap.gap_of_excited (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (kTG_symm β) hφm hφb hφ1 heig hc hc0 a n (by omega) ⟨n', hn'⟩ (by rw [hidx]; exact hexc) f hf

include hβ hn he in
/-- **The gap of the seed on the cubic torus of `G` of every even side `L ≥ 2n`**
(`OpenAIBridgeSides.gap_even_side` over a `GaugeGroup G`). If one torus of even side `n ≥ 2` has
`16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then for every even `L ≥ 2n` the transfer
operator `K` in direction `0` of the cubic torus of side `L` has a unit eigenvector `ψ` with
eigenvalue of modulus `‖K‖`, and `‖K^n f‖ ≤ ½ ‖K‖^n ‖f‖` for every `f ⊥ ψ`. It is
`gap_side_excitedG` at the window of `exists_window`, with `ψ` the vacuum of its eigenfunction.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the doubled side, the least seed
side, the least ratio `L / n`, the `L²` exponent and the contraction `1/2`; `0` the time direction
of the slice and the sign of the coupling; `1` the unit norm and the kernel bound. -/
theorem gap_even_sideG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ ψ : Lp ℝ 2 (hSG G 0 (tr (fun _ : Fin 4 => L) 0)), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, |c| = ‖kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1
          (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))‖ ∧
      kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1 (continuous_kTG β).measurable
          zero_le_one (abs_kTG_le hβ) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) ψ = c • ψ ∧
      ∀ f : Lp ℝ 2 (hSG G 0 (tr (fun _ : Fin 4 => L) 0)), inner ℝ f ψ = 0 →
        ‖((kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1 (continuous_kTG β).measurable
          zero_le_one (abs_kTG_le hβ) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0))) ^ n) f‖
          ≤ 1 / 2 * ‖kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1
            (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
            (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))‖ ^ n
            * ‖f‖ := by
  obtain ⟨a, hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, -, heig, hc, hgap, -⟩ :=
    gap_side_excitedG hβ hn he h0 a L hLe hlo hhi
  exact ⟨KernelGap.vac (μ := hSG G 0 (tr (fun _ : Fin 4 => L) 0)) hφm hφb,
    KernelGap.norm_vac hφm hφb hφ1, c, hc, KernelGap.K_vac _ _ _ hφm hφb heig, hgap⟩

include hβ hn he in
/-- **Uniform exponential clustering of the transfer state of `G` on the cubic torus of every even
side `L ≥ 2n`, from the seed** (`OpenAIBridgeSides.cluster_even_side` over `G`). The slice transfer
`K` of the torus of side `L` has a unit eigenvector `ψ` with eigenvalue `c ≠ 0`, `|c| = ‖K‖`, and for
every `t` and all `u`, `w`, `|⟨u, K^t w⟩/c^t − ⟨u,ψ⟩⟨w,ψ⟩| ≤ 2 e^{−(log 2/n) t} ‖u‖ ‖w‖`. It is
`OpenAIBridgeCluster.inner_pow_div_sub_le` and `half_pow_div_le_exp` at the gap of
`gap_even_sideG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `2` the inverse of the contraction
`1/2` (the logarithm of which is the rate), the doubled side, the least seed side, the least ratio
`L / n` and the `L²` exponent; `0` the time direction of the slice, the sign of the coupling and the
excluded eigenvalue; `1` the kernel bound and the unit norm. -/
theorem cluster_even_sideG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ ψ : Lp ℝ 2 (hSG G 0 (tr (fun _ : Fin 4 => L) 0)), ‖ψ‖ = 1 ∧
      ∃ c : ℝ, c ≠ 0 ∧ |c| = ‖kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1
          (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))‖ ∧
      kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1 (continuous_kTG β).measurable
          zero_le_one (abs_kTG_le hβ) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) ψ = c • ψ ∧
      ∀ (t : ℕ) (u w : Lp ℝ 2 (hSG G 0 (tr (fun _ : Fin 4 => L) 0))),
        |inner ℝ u (((kernelCLM (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1
          (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
          (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (hSG G 0 (tr (fun _ : Fin 4 => L) 0))) ^ t) w)
            / c ^ t - inner ℝ u ψ * inner ℝ w ψ|
          ≤ 2 * Real.exp (-(Real.log 2 / n) * t) * ‖u‖ * ‖w‖ := by
  obtain ⟨ψ, hψ1, c, hc, hKψ, hgap⟩ := gap_even_sideG hβ hn he h0 L hLe hL
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc
    linarith [K_posG (G := G) hβ 0 (tr (fun _ : Fin 4 => L) 0)]
  have hTs := fun u w => (MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm
    (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) 1 (continuous_kTG β).measurable zero_le_one
    (abs_kTG_le hβ) (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (kTG_symm β)).isSymmetric u w
  refine ⟨ψ, hψ1, c, hc0, hc, hKψ, fun t u w => ?_⟩
  have h1 := inner_pow_div_sub_le hTs hKψ hgap hψ1 hc hc0 t u w
  have h2 := half_pow_div_le_exp (n := n) (by omega) t
  calc _ ≤ _ := h1
    _ ≤ 2 * Real.exp (-(Real.log 2 / n) * t) * ‖u‖ * ‖w‖ := by
        gcongr

include hβ hn he in
/-- **The connected periodic trace ratio of `G` on the cubic torus of every even side `L ≥ 2n`, with
a constant uniform in the torus** (`OpenAIBridgeUniform.connTorus_even_side_uniform` over `G`). There
are a normalized bounded eigenfunction `φ` of the slice kernel `kTG` of the torus of side `L` and its
eigenvalue `c ≠ 0` such that for all bounded measurable `a`, `b` of the slice (`|a| ≤ A`, `|b| ≤ B`)
and all `p + q + 2 = L`,

    |connTorus a b p q| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋).

`gap_side_excitedG` gives `σ_{j0} ≤ 1/2` at a level `4 j0 ≤ L`; `excited_add_le` moves it to half the
torus; `connTorus_uniform` closes.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of
`connTorus_uniform`; `1/2` the contraction; `2` the doubled side, the least seed side, the least
ratio `L / n` and the offset of `iter` on the torus of `p + q + 2` steps; `0` the time direction of
the slice, the sign of the coupling and the excluded eigenvalue; `1` the offset of `iter` and the
unit norm. -/
theorem connTorus_even_side_uniformG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L) :
    ∃ φ : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → G) → ℝ, ∃ c : ℝ, c ≠ 0 ∧
      ∫ x, φ x ^ 2 ∂(hSG G 0 (tr (fun _ : Fin 4 => L) 0)) = 1 ∧
      (∀ z, ∫ y, kTG G 0 (tr (fun _ : Fin 4 => L) 0) β z y * φ y
        ∂(hSG G 0 (tr (fun _ : Fin 4 => L) 0)) = c * φ z) ∧
      ∀ (a b : (SpT 0 (tr (fun _ : Fin 4 => L) 0) → G) → ℝ), Measurable a → Measurable b →
      ∀ A B : ℝ, (∀ x, |a x| ≤ A) → (∀ x, |b x| ≤ B) →
      ∀ p q : ℕ, p + q + 2 = L →
        |connTorus (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β)
            a b p q|
          ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨a', hlo, hhi⟩ := exists_window (by omega : 1 ≤ n) hL
  obtain ⟨φ, hφm, Bφ, hφb, hφ1, c, hc0, heig, hc, hgap, j0, hj0, hL4, hexc⟩ :=
    gap_side_excitedG hβ hn he h0 a' L hLe hlo hhi
  refine ⟨φ, c, hc0, hφ1, heig, fun a b ham hbm A B hab hbb p q hpq => ?_⟩
  have hev : Even (p + q) := by
    obtain ⟨L', hL'⟩ := hLe
    exact ⟨L' - 1, by omega⟩
  have hn0 : 0 < n := by omega
  have hl : 1 ≤ (p + q) / 2 + 1 - j0 := by omega
  have hadd := excited_add_le (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (kTG_symm β) hφm hφb hφ1 heig hc hgap hc0 j0 ((p + q) / 2 + 1 - j0) hj0 hl
  rw [show j0 + ((p + q) / 2 + 1 - j0) = (p + q) / 2 + 1 by omega] at hadd
  have hexc' : excited (hSG G 0 (tr (fun _ : Fin 4 => L) 0))
      (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) c φ j0 ≤ 1 / 2 := by
    refine hexc.trans ?_
    have := pow_le_pow_of_le_one (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
      (Nat.one_le_two_pow (n := a'))
    simpa using this
  have hfl : ((p + q) / 2 + 1) / n ≤ 2 * (((p + q) / 2 + 1 - j0) / n) + 1 := by
    have h1 : (p + q) / 2 + 1 - j0 < ((p + q) / 2 + 1 - j0) / n * n + n := Nat.lt_div_mul_add hn0
    have key : (p + q) / 2 + 1 < (2 * (((p + q) / 2 + 1 - j0) / n) + 2) * n := by
      have e : (2 * (((p + q) / 2 + 1 - j0) / n) + 2) * n
          = 2 * (((p + q) / 2 + 1 - j0) / n * n) + 2 * n := by ring
      rw [e]
      generalize ((p + q) / 2 + 1 - j0) / n * n = u at h1 ⊢
      omega
    have := (Nat.div_lt_iff_lt_mul hn0).2 key
    generalize ((p + q) / 2 + 1) / n = s at this ⊢
    generalize ((p + q) / 2 + 1 - j0) / n = s' at this ⊢
    omega
  have hσ : excited (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β)
      c φ ((p + q) / 2 + 1) ≤ (1 / 2) ^ (((p + q) / 2 + 1) / n) :=
    calc _ ≤ (1 / 2) ^ (2 * (((p + q) / 2 + 1 - j0) / n))
          * excited (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β)
            c φ j0 := hadd
      _ ≤ (1 / 2) ^ (2 * (((p + q) / 2 + 1 - j0) / n)) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hexc' (by positivity)
      _ = (1 / 2) ^ (2 * (((p + q) / 2 + 1 - j0) / n) + 1) := by rw [pow_succ]
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hfl
  exact connTorus_uniform (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ) (kTG_symm β)
    hφm hφb hφ1 heig hc hgap hc0 ham hbm hab hbb p q hev hσ

/-! ## 3. The trace identity with insertions -/

include hβ in
/-- **The closed slice chain of `G` with two slices inserted, at any separation**
(`OpenAIBridgeUniform.Zc_trPair` over `G`, on the cubic torus of side `p + q + 2` of `TorusChainG`):
for bounded measurable `a`, `b` of the spatial links of one slice,
`ZcG (a(V 0) b(V (p+1))) = trPair (Haar) kTG a b p q`. `HiddenChain.chain_split` at `p + 1`,
`HiddenChain.chain_end_kern` on the second part and `HiddenChain.chain_end_iter` on the first, with
`TorusChainG.kern_wtG`.

DERIVED: `0` is the first slice; `1` the offset of `iter` and the second slice `p + 1`. -/
theorem Zc_trPairG (p q : ℕ)
    {a b : (SpT 0 (TorusChain.Tc (p + 1 + q)) → G) → ℝ} (hbm : Measurable b) {A B : ℝ}
    (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) :
    TorusChainG.ZcG G (p + 1 + q) β (fun V _ => a (V 0) * b (V (p + 1)))
      = trPair (hSG G 0 (TorusChain.Tc (p + 1 + q))) (kTG G 0 (TorusChain.Tc (p + 1 + q)) β)
          a b p q := by
  have hk : Bdd (kTG G 0 (TorusChain.Tc (p + 1 + q)) β) := bdd_kTG hβ
  unfold TorusChainG.ZcG trPair
  congr 1; funext x
  have step1 : HiddenChain.chain (hSG G 0 (TorusChain.Tc (p + 1 + q)))
      (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β) (p + 1 + q)
      (fun V _ => a (V 0) * b (V (p + 1)) * kTG G 0 (TorusChain.Tc (p + 1 + q)) β (V (p + 1 + q)) x) x
      = HiddenChain.chain (hSG G 0 (TorusChain.Tc (p + 1 + q)))
      (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β) (p + 1 + q)
      (fun V _ => a (V 0) * b (V (p + 1))
        * HiddenChain.kern (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β)
          (HiddenChain.sshift V (p + 1) q) x) x := by
    congr 1; funext V A
    rw [TorusChainG.kern_wtG]
    show _ = a (V 0) * b (V (p + 1)) * kTG G 0 (TorusChain.Tc (p + 1 + q)) β (V (q + (p + 1))) x
    rw [show q + (p + 1) = p + 1 + q by omega]
  have hsplit := HiddenChain.chain_split (μ := hSG G 0 (TorusChain.Tc (p + 1 + q)))
    (ν := hAG G 0 (TorusChain.Tc (p + 1 + q))) (w := TorusChainG.wtG G (p + 1 + q) β) (p + 1) q
    (G1 := fun V (_ : ℕ → TorusChainG.AxG G (p + 1 + q)) => a (V 0) * b (V (p + 1)))
    (fun V (_ : ℕ → TorusChainG.AxG G (p + 1 + q)) =>
      HiddenChain.kern (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β)
        (V q) x) x
    (fun V V' A A' hV _ => by
      show a (V 0) * b (V (p + 1)) = a (V' 0) * b (V' (p + 1))
      rw [hV 0 (Nat.zero_le _), hV (p + 1) le_rfl])
  refine step1.trans (hsplit.trans ?_)
  have hend : ∀ z, HiddenChain.chain (hSG G 0 (TorusChain.Tc (p + 1 + q)))
      (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β) q
      (fun V (_ : ℕ → TorusChainG.AxG G (p + 1 + q)) =>
        HiddenChain.kern (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β)
          (V q) x) z
      = iter (hSG G 0 (TorusChain.Tc (p + 1 + q))) (kTG G 0 (TorusChain.Tc (p + 1 + q)) β) q z x := by
    intro z; rw [HiddenChain.chain_end_kern x q z, TorusChainG.kern_wtG]
  simp only [hend]
  obtain ⟨Cq, hCq⟩ := (hk.iter (μ := hSG G 0 (TorusChain.Tc (p + 1 + q))) q).bdd
  set g' : (SpT 0 (TorusChain.Tc (p + 1 + q)) → G) → ℝ := fun z => a x * b z
    * iter (hSG G 0 (TorusChain.Tc (p + 1 + q))) (kTG G 0 (TorusChain.Tc (p + 1 + q)) β) q z x
    with hg'
  have hg'm : Measurable g' :=
    (measurable_const.mul hbm).mul ((hk.iter (μ := hSG G 0 (TorusChain.Tc (p + 1 + q))) q).col x)
  have hg'b : ∀ z, |g' z| ≤ A * B * Cq := fun z =>
    HiddenChain.abs_mul_le_of (HiddenChain.abs_mul_le_of (hab x) (hbb z)) (hCq z x)
  have step3 : HiddenChain.chain (hSG G 0 (TorusChain.Tc (p + 1 + q)))
      (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β) (p + 1)
      (fun V _ => a (V 0) * b (V (p + 1))
        * iter (hSG G 0 (TorusChain.Tc (p + 1 + q))) (kTG G 0 (TorusChain.Tc (p + 1 + q)) β) q
          (V (p + 1)) x) x
      = HiddenChain.chain (hSG G 0 (TorusChain.Tc (p + 1 + q)))
        (hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wtG G (p + 1 + q) β) (p + 1)
        (fun V _ => g' (V (p + 1))) x :=
    HiddenChain.chain_congr (p + 1) (fun V A hV => by rw [hg']; dsimp only; rw [hV])
  refine step3.trans ?_
  rw [HiddenChain.chain_end_iter (μ := hSG G 0 (TorusChain.Tc (p + 1 + q)))
    (ν := hAG G 0 (TorusChain.Tc (p + 1 + q))) (TorusChainG.wmeas_wtG β)
    (TorusChainG.abs_wtG_le hβ) hg'm hg'b p x, TorusChainG.kern_wtG]
  congr 1; funext z
  rw [hg']
  dsimp only
  ring

/-- **The spatial links of one time slice** of a configuration of the rectangular torus of `G`:
slice `t` along `μ`, link `(ν, y)` read at the site `join t y` (`OpenAIBridgeUniform.spSlice` over
`G`).

DERIVED: `4` is the spacetime dimension. -/
def spSliceG (L : Fin 4 → ℕ) (μ : Fin 4) (t : Fin (L μ)) (U : RLink L → G) : SpIdx L μ → G :=
  fun l => U (l.1.1, join L μ t l.2)

omit [Group G] [TopologicalSpace G] [GaugeGroup G] in
/-- `spSliceG L μ t` is measurable.

DERIVED: `4` is the spacetime dimension. -/
theorem measurable_spSliceG (L : Fin 4 → ℕ) (μ : Fin 4) (t : Fin (L μ)) :
    Measurable (spSliceG (G := G) L μ t) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- On a configuration of the cubic torus of `G` assembled from slices
(`RectWilsonG.ΦG` of `TorusChainG.joinWG A V`), the spatial links of slice `t` are `V t`
(`RectWilsonG.ΦG_sp`).

DERIVED: `0` is the slicing direction; `1` the successor of the extent `M + 1`. -/
theorem spSliceG_joinWG {M : ℕ} (A : Fin (M + 1) → TorusChainG.AxG G M)
    (V : Fin (M + 1) → TorusChainG.SlG G M) (t : Fin (M + 1)) :
    spSliceG (TorusChain.Lc M) 0 t (ΦG (TorusChain.Lc M) 0 (TorusChainG.joinWG A V)) = V t := by
  funext l
  exact ΦG_sp (TorusChainG.joinWG A V) t l.2 l.1

include hβ in
/-- **The Wilson correlation numerator of two slice observables of `G` is the trace with
insertions** (`OpenAIBridgeUniform.corrNum_slab` over `G`): on the cubic torus of side `p + q + 2`,
for bounded measurable `a`, `b` of the spatial links of one slice,
`∫ a(U|_0) b(U|_{p+1}) e^{−β S(U)} dU = trPair (Haar) kTG a b p q`. It is `TorusChainG.corrNum_eqG`
and `Zc_trPairG`.

DERIVED: `0` is the time direction and the first slice; `1` the offset of `iter`, the second slice
`p + 1` and the side `p + q + 2`; `4` the spacetime dimension. -/
theorem corrNum_slabG {p q : ℕ}
    {a b : (SpIdx (fun _ : Fin 4 => p + 1 + q + 1) 0 → G) → ℝ} (ham : Measurable a)
    (hbm : Measurable b) {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) :
    (sysRG G (fun _ : Fin 4 => p + 1 + q + 1)).corrNum (probHaar G) β
        (fun U => a (spSliceG (fun _ : Fin 4 => p + 1 + q + 1) 0 ⟨0, Nat.succ_pos _⟩ U)
          * b (spSliceG (fun _ : Fin 4 => p + 1 + q + 1) 0
            ⟨p + 1, Nat.lt_succ_of_le (Nat.le_add_right (p + 1) q)⟩ U))
      = trPair (hSG G 0 (tr (fun _ : Fin 4 => p + 1 + q + 1) 0))
          (kTG G 0 (tr (fun _ : Fin 4 => p + 1 + q + 1) 0) β) a b p q := by
  have hO : Measurable (fun U : RLink (TorusChain.Lc (p + 1 + q)) → G =>
      a (spSliceG (fun _ : Fin 4 => p + 1 + q + 1) 0 ⟨0, Nat.succ_pos _⟩ U)
        * b (spSliceG (fun _ : Fin 4 => p + 1 + q + 1) 0
          ⟨p + 1, Nat.lt_succ_of_le (Nat.le_add_right (p + 1) q)⟩ U)) :=
    (ham.comp (measurable_spSliceG _ 0 _)).mul (hbm.comp (measurable_spSliceG _ 0 _))
  refine (TorusChainG.corrNum_eqG (M := p + 1 + q) hβ hO (BO := A * B)
    (fun U => HiddenChain.abs_mul_le_of (hab _) (hbb _))
    (F := fun V _ => a (V 0) * b (V (p + 1)))
    ((ham.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
      (hbm.comp ((measurable_pi_apply (p + 1)).comp measurable_fst)))
    (BF := A * B) (fun V _ => HiddenChain.abs_mul_le_of (hab _) (hbb _)) ?_).trans
    (Zc_trPairG hβ p q hbm hab hbb)
  intro A' V
  simp only [spSliceG_joinWG]
  rw [extX_apply _ (show 0 < p + 1 + q + 1 by omega),
    extX_apply _ (show p + 1 < p + 1 + q + 1 by omega)]

variable (G) in
include hβ in
/-- **The partition function of `G` is the trace of the transfer power**: for `L 0 = m + 1`,
`ZRG G L β = trPow (Haar) kTG m` (`OpenAIBridgeCluster.ZR_eq_trPow` over `G`). It is
`RectTransferG.ZRG_eq_cyc` and `OpenAIBridgeCluster.trPow_eq_cyc`.

DERIVED: `0` is the time direction; `1` the offset of `trPow`. -/
theorem ZRG_eq_trPowG (L : Fin 4 → ℕ) (m : ℕ) (hL : L 0 = m + 1) :
    ZRG G L β = trPow (hSG G 0 (tr L 0)) (kTG G 0 (tr L 0) β) m := by
  rw [ZRG_eq_cyc (μ := 0) β, hL, trPow_eq_cyc (bdd_kTG hβ) m]

include hβ in
/-- **The connected trace ratio of `G` is the connected Wilson correlation**
(`OpenAIBridgeUniform.connTorus_eq_expect` over `G`): on the cubic torus of side
`L = p + q + 2`, for bounded measurable `a`, `b` of the spatial links of one slice, with `⟨·⟩` the
Wilson Gibbs expectation of the torus of `G`,

    connTorus (Haar) kTG a b p q = ⟨a(U|_0) b(U|_{p+1})⟩ − ⟨a(U|_0)⟩ ⟨b(U|_{p+1})⟩.

Numerators by `corrNum_slabG` (with `1` for the absent insertion, `trPair_one_right`,
`trPair_one_left`), the partition function by `ZRG_eq_trPowG`.

DERIVED: `0` is the time direction and the first slice; `1` the offset of `iter`, the second slice
`p + 1` and the side `p + q + 2`; `4` the spacetime dimension. -/
theorem connTorus_eq_expectG {L p q : ℕ} (hL : p + 1 + q + 1 = L)
    {a b : (SpIdx (fun _ : Fin 4 => L) 0 → G) → ℝ} (ham : Measurable a) (hbm : Measurable b)
    {A B : ℝ} (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) :
    connTorus (hSG G 0 (tr (fun _ : Fin 4 => L) 0)) (kTG G 0 (tr (fun _ : Fin 4 => L) 0) β) a b p q
      = (sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
          (fun U => a (spSliceG (fun _ : Fin 4 => L) 0
              ⟨0, by show 0 < L; exact hL ▸ Nat.succ_pos _⟩ U)
            * b (spSliceG (fun _ : Fin 4 => L) 0
              ⟨p + 1, by show p + 1 < L; exact hL ▸ Nat.lt_succ_of_le (Nat.le_add_right _ q)⟩ U))
        - (sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
            (fun U => a (spSliceG (fun _ : Fin 4 => L) 0
              ⟨0, by show 0 < L; exact hL ▸ Nat.succ_pos _⟩ U))
          * (sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
            (fun U => b (spSliceG (fun _ : Fin 4 => L) 0
              ⟨p + 1, by show p + 1 < L; exact hL ▸ Nat.lt_succ_of_le (Nat.le_add_right _ q)⟩ U)) := by
  subst hL
  have hab' := corrNum_slabG (G := G) hβ (p := p) (q := q) ham hbm hab hbb
  have hab1 := corrNum_slabG (G := G) hβ (p := p) (q := q) (b := fun _ => (1 : ℝ)) ham
    measurable_const hab (fun _ => abs_one.le)
  have h1b := corrNum_slabG (G := G) hβ (p := p) (q := q) (a := fun _ => (1 : ℝ)) measurable_const
    hbm (fun _ => abs_one.le) hbb
  simp only [mul_one, one_mul] at hab1 h1b
  have hZ : (sysRG G (fun _ : Fin 4 => p + 1 + q + 1)).partition (probHaar G) β
      = trPow (hSG G 0 (tr (fun _ : Fin 4 => p + 1 + q + 1) 0))
          (kTG G 0 (tr (fun _ : Fin 4 => p + 1 + q + 1) 0) β) (p + q + 1) :=
    ZRG_eq_trPowG G hβ _ (p + q + 1) (by show p + 1 + q + 1 = p + q + 1 + 1; omega)
  unfold connTorus LatticeGauge.System.expect
  rw [hab', hab1, h1b, hZ, trPair_one_right (bdd_kTG hβ) a p q,
    trPair_one_left (bdd_kTG hβ) (kTG_symm β) hbm hbb p q]

include hβ hn he in
/-- **Exponential clustering of the Wilson torus correlation of `G`, uniform in the torus, from the
seed** (`OpenAIBridgeUniform.wilson_conn_even_side` over a `GaugeGroup G`). If one torus of even side
`n ≥ 2` has `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` at `β ≥ 0`, then on the cubic Wilson torus of
`G` of every even side `L ≥ 2n`, for bounded measurable functions `a`, `b` of the spatial links of one
time slice (`|a| ≤ A`, `|b| ≤ B`), read at slices `0` and `p + 1` of the time extent `L = p + q + 2`,

    |⟨a_0 b_{p+1}⟩ − ⟨a_0⟩⟨b_{p+1}⟩| ≤ 6 A B ((1/2)^⌊(p+1)/n⌋ + (1/2)^⌊(q+1)/n⌋),

`⟨·⟩` the Wilson Gibbs expectation of the torus. The constant `6` and the rate `log 2 / n` do not
depend on `L`, the coupling, the observables or the group. It is `connTorus_even_side_uniformG` read
through `connTorus_eq_expectG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of
`connTorus_uniform`; `1/2` the contraction; `2` the doubled side, the least seed side and the least
ratio `L / n`; `0` the time direction, the first slice and the sign of the coupling; `1` the offset
of `iter`, the second slice `p + 1` and the time extent `p + q + 2`; `4` the spacetime dimension. -/
theorem wilson_conn_even_sideG
    (h0 : 16 * Real.log (ZRG G (fun _ => n) β) - Real.log (ZRG G (fun _ => 2 * n) β) ≤ 1 / 1000)
    (L : ℕ) (hLe : Even L) (hL : 2 * n ≤ L)
    (a b : (SpIdx (fun _ : Fin 4 => L) 0 → G) → ℝ) (ham : Measurable a)
    (hbm : Measurable b) (A B : ℝ) (hab : ∀ x, |a x| ≤ A) (hbb : ∀ x, |b x| ≤ B) (p q : ℕ)
    (hpq : p + 1 + q + 1 = L) :
    |(sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
        (fun U => a (spSliceG (fun _ : Fin 4 => L) 0 ⟨0, by show 0 < L; omega⟩ U)
          * b (spSliceG (fun _ : Fin 4 => L) 0 ⟨p + 1, by show p + 1 < L; omega⟩ U))
      - (sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
          (fun U => a (spSliceG (fun _ : Fin 4 => L) 0 ⟨0, by show 0 < L; omega⟩ U))
        * (sysRG G (fun _ : Fin 4 => L)).expect (probHaar G) β
          (fun U => b (spSliceG (fun _ : Fin 4 => L) 0 ⟨p + 1, by show p + 1 < L; omega⟩ U))|
      ≤ 6 * (A * B) * ((1 / 2) ^ ((p + 1) / n) + (1 / 2) ^ ((q + 1) / n)) := by
  obtain ⟨φ, c, hc0, hφ1, heig, hcl⟩ := connTorus_even_side_uniformG hβ hn he h0 L hLe hL
  have h := hcl a b ham hbm A B hab hbb p q (by omega)
  rw [connTorus_eq_expectG hβ hpq ham hbm hab hbb] at h
  exact h

end Wilson

/-! ## 4. On the OpenAI laws of every closed matrix group -/

/-- **Their probability Haar measure is our `probHaar`**: on the image `g.image ≤ U(n+1)` of any of
their gauge groups (compact by `OpenAIConfig.instGaugeGroupImage`), every left-invariant probability
measure is `probHaar g.image`. `haarMeasure_unique` at the default positive compact, which is all of
`g.image`. Their single-link measure is such a measure: `WilsonFamily.haar` carries
`IsProbabilityMeasure` and `IsHaarMeasure` (`PublicWilson.lean:41–43`). The model is
`OpenAIConfig.map_imageEquivSU_eq_probHaar`, without the isomorphism to `SU(n+1)`.

DERIVED: no numeral beyond the structural ones; `1` in `n + 1` is their matrix-size shift. -/
theorem eq_probHaar_image (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] : μ = probHaar g.image := by
  have h := MeasureTheory.Measure.haarMeasure_unique μ
    (default : TopologicalSpace.PositiveCompacts g.image)
  have hd : ((default : TopologicalSpace.PositiveCompacts g.image) : Set g.image) = Set.univ :=
    TopologicalSpace.PositiveCompacts.coe_top
  rw [hd, measure_univ, one_smul] at h
  exact h

/-- **Our expectation on the cubic torus of `g.image` is their law**: for any of their gauge groups
`g`, any left-invariant probability measure `μ` on `g.image` (their Haar measure), every side `L` and
every real observable `O` on their configurations, our Wilson Gibbs expectation at `β` on the cubic
torus of side `L` of `O ∘ configEquiv` is `∫ O ∂(wilsonLaw g L (2β) μ)`. It is
`TorusChainG.expect_cubicG` (the rectangular system at constant sides is the hypercubic one),
`OpenAIConfig.expect_eq_integral_openAILaw` and `eq_probHaar_image`.

DERIVED: `4` is the spacetime dimension; `2` the factor of
`OpenAIDictionary.action_eq_two_mul_wilsonEnergy` (two orientations of one plane). -/
theorem expect_eq_openAILawG (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (L : ℕ+) (β : ℝ)
    (O : OpenAIConfig.Configuration g L → ℝ) :
    (sysRG g.image (fun _ : Fin 4 => (L : ℕ))).expect (probHaar g.image) β
        (fun U => O (OpenAIConfig.configEquiv L U))
      = ∫ V, O V ∂(OpenAIConfig.wilsonLaw g L (2 * β) μ) := by
  rw [eq_probHaar_image g μ]
  obtain ⟨l, hl⟩ := L
  obtain ⟨M, rfl⟩ : ∃ M, l = M + 1 := ⟨l - 1, by omega⟩
  have h1 : (sysRG g.image (TorusChain.Lc M)).expect (probHaar g.image) β
        (fun U => O (OpenAIConfig.configEquiv ⟨M + 1, hl⟩ U))
      = (GaugeWilson.sysWilsonG g.image 4 (M + 1)).expect (probHaar g.image) β
        (fun U => O (OpenAIConfig.configEquiv ⟨M + 1, hl⟩ U)) :=
    (TorusChainG.expect_cubicG β _).symm
  exact h1.trans
    (OpenAIConfig.expect_eq_integral_openAILaw ⟨M + 1, hl⟩ g β (probHaar g.image) O)

set_option maxHeartbeats 800000 in
/-- **Theorem 4.46 on their laws, for every closed matrix group.** For any of their gauge groups `g`
(a closed subgroup of `U(n+1)`) with their Haar measure `μ` (`IsProbabilityMeasure`, `IsHaarMeasure`,
`PublicWilson.lean:41–43`), couplings `β m p ≥ 0` in their normalization, seed sides `n m` and torus
sides `Ls m p`: if for all large `m` the side `n m` is even and at least `2`, every `Ls m p` is even
and at least `2 n m`, and the seed `16 log ZRG(n⁴) − log ZRG((2n)⁴) ≤ 1/1000` of `g.image` holds at
`(n m, β m p / 2)`, then for all large `m`, all `p` and every `L = Ls m p`:

* their law at `β m p` on side `L` integrates every observable `O` as our Wilson Gibbs expectation at
  `β m p / 2` of `O ∘ configEquiv` on the cubic torus of `g.image` of side `L`
  (`expect_eq_openAILawG`);
* the transfer operator of that torus has a unit top eigenvector and its `n m`-th power contracts the
  orthogonal complement by `1/2` relative to `‖K‖^(n m)` (`gap_even_sideG`).

The `SU(n+1)` case is `OpenAIConfig.familyGap_on_openAI_laws'`; here no isomorphism to `SU(n+1)` and no
simplicity of their Lie algebra is used.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `4` the spacetime dimension; `2` the
halving of the coupling (`action_eq_two_mul_wilsonEnergy`), the doubled side, the least seed side,
the least ratio, the `L²` exponent and the contraction `1/2`; `0` the sign of the coupling and the
time direction of the slice; `1` the unit norm and the kernel bound. -/
theorem familyGap_on_openAI_lawsG (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (Ls : ℕ → ℕ → ℕ) (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      Even (Ls m p) ∧ 2 * n m ≤ Ls m p ∧
      16 * Real.log (ZRG g.image (fun _ => n m) (β m p / 2))
        - Real.log (ZRG g.image (fun _ => 2 * n m) (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in Filter.atTop, ∀ (p : ℕ) (L : ℕ+), (L : ℕ) = Ls m p →
      (∀ O : OpenAIConfig.Configuration g L → ℝ,
        (sysRG g.image (fun _ : Fin 4 => (L : ℕ))).expect (probHaar g.image) (β m p / 2)
            (fun U => O (OpenAIConfig.configEquiv L U))
          = ∫ V, O V ∂(OpenAIConfig.wilsonLaw g L (β m p) μ)) ∧
      ∃ ψ : Lp ℝ 2 (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0)), ‖ψ‖ = 1 ∧
        ∃ c : ℝ, |c| = ‖kernelCLM (kTG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0) (β m p / 2)) 1
            (continuous_kTG (β m p / 2)).measurable zero_le_one
            (abs_kTG_le (div_nonneg (hβ m p) zero_le_two))
            (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0))
            (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0))‖ ∧
        kernelCLM (kTG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0) (β m p / 2)) 1
            (continuous_kTG (β m p / 2)).measurable zero_le_one
            (abs_kTG_le (div_nonneg (hβ m p) zero_le_two))
            (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0))
            (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0)) ψ = c • ψ ∧
        ∀ f : Lp ℝ 2 (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0)), inner ℝ f ψ = 0 →
          ‖((kernelCLM (kTG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0) (β m p / 2)) 1
            (continuous_kTG (β m p / 2)).measurable zero_le_one
            (abs_kTG_le (div_nonneg (hβ m p) zero_le_two))
            (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0))
            (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0))) ^ n m) f‖
            ≤ 1 / 2 * ‖kernelCLM (kTG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0) (β m p / 2)) 1
              (continuous_kTG (β m p / 2)).measurable zero_le_one
              (abs_kTG_le (div_nonneg (hβ m p) zero_le_two))
              (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0))
              (hSG g.image 0 (tr (fun _ : Fin 4 => (L : ℕ)) 0))‖ ^ n m * ‖f‖ := by
  filter_upwards [hfam] with m hm p L hL
  obtain ⟨hn, he, h⟩ := hm
  obtain ⟨hLe, hL2, h0⟩ := h p
  have hLe' : Even (L : ℕ) := hL ▸ hLe
  have hL2' : 2 * n m ≤ (L : ℕ) := hL ▸ hL2
  refine ⟨fun O => ?_, gap_even_sideG (G := g.image) (div_nonneg (hβ m p) zero_le_two) hn he h0
    (L : ℕ) hLe' hL2'⟩
  have h1 := expect_eq_openAILawG g μ L (β m p / 2) O
  rw [show 2 * (β m p / 2) = β m p by ring] at h1
  exact h1

/-- **Theorem 4.47 on their laws, for every closed matrix group.** Under the hypotheses of
`familyGap_on_openAI_lawsG`: for all large `m`, all `p` and every torus of side `L = Ls m p`, for
bounded measurable functions `a`, `b` of the spatial links of one time slice (`|a| ≤ A`, `|b| ≤ B`),
read on their configurations through `configEquiv⁻¹` at slices `0` and `s + 1` of `L = s + t + 2`,
the connected correlation under their law at `β m p` satisfies

    |E[a_0 b_{s+1}] − E[a_0] E[b_{s+1}]| ≤ 6 A B ((1/2)^⌊(s+1)/n m⌋ + (1/2)^⌊(t+1)/n m⌋),

uniform in `m`, `p`, the side and the observables. It is `wilson_conn_even_sideG` at `g.image` and
`β m p / 2`, carried to their law by `expect_eq_openAILawG`.

DERIVED: `16` and `1000` are the seed of `wilson_gap_sharp`; `6` the constant of
`connTorus_uniform`; `1/2` the contraction; `4` the spacetime dimension; `2` the halving of the
coupling, the doubled side, the least seed side and the least ratio; `0` the first slice and the
time direction; `1` the offset of the second slice `s + 1` and of the side `s + t + 2`. -/
theorem familyConn_on_openAI_lawsG (g : OpenAIConfig.GaugeGroup) (μ : Measure g.image)
    [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
    (β : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (Ls : ℕ → ℕ → ℕ) (hβ : ∀ m p, 0 ≤ β m p)
    (hfam : ∀ᶠ m in Filter.atTop, 2 ≤ n m ∧ Even (n m) ∧ ∀ p,
      Even (Ls m p) ∧ 2 * n m ≤ Ls m p ∧
      16 * Real.log (ZRG g.image (fun _ => n m) (β m p / 2))
        - Real.log (ZRG g.image (fun _ => 2 * n m) (β m p / 2)) ≤ 1 / 1000) :
    ∀ᶠ m in Filter.atTop, ∀ (p : ℕ) (L : ℕ+), (L : ℕ) = Ls m p →
      ∀ (a b : (SpIdx (fun _ : Fin 4 => (L : ℕ)) 0 → g.image) → ℝ), Measurable a → Measurable b →
      ∀ A B : ℝ, (∀ x, |a x| ≤ A) → (∀ x, |b x| ≤ B) →
      ∀ (s t : ℕ) (hst : s + 1 + t + 1 = (L : ℕ)),
        |∫ V, a (spSliceG (fun _ : Fin 4 => (L : ℕ)) 0 ⟨0, by show 0 < (L : ℕ); omega⟩
              ((OpenAIConfig.configEquiv L).symm V))
            * b (spSliceG (fun _ : Fin 4 => (L : ℕ)) 0 ⟨s + 1, by show s + 1 < (L : ℕ); omega⟩
              ((OpenAIConfig.configEquiv L).symm V)) ∂(OpenAIConfig.wilsonLaw g L (β m p) μ)
          - (∫ V, a (spSliceG (fun _ : Fin 4 => (L : ℕ)) 0 ⟨0, by show 0 < (L : ℕ); omega⟩
              ((OpenAIConfig.configEquiv L).symm V)) ∂(OpenAIConfig.wilsonLaw g L (β m p) μ))
            * ∫ V, b (spSliceG (fun _ : Fin 4 => (L : ℕ)) 0
                ⟨s + 1, by show s + 1 < (L : ℕ); omega⟩ ((OpenAIConfig.configEquiv L).symm V))
                ∂(OpenAIConfig.wilsonLaw g L (β m p) μ)|
          ≤ 6 * (A * B) * ((1 / 2) ^ ((s + 1) / n m) + (1 / 2) ^ ((t + 1) / n m)) := by
  filter_upwards [hfam] with m hm p L hL a b ham hbm A B hab hbb s t hst
  obtain ⟨hn, he, h⟩ := hm
  obtain ⟨hLe, hL2, h0⟩ := h p
  have e : ∀ f : (RLink (fun _ : Fin 4 => (L : ℕ)) → g.image) → ℝ,
      (sysRG g.image (fun _ : Fin 4 => (L : ℕ))).expect (probHaar g.image) (β m p / 2) f
        = ∫ V, f ((OpenAIConfig.configEquiv L).symm V) ∂(OpenAIConfig.wilsonLaw g L (β m p) μ) := by
    intro f
    have h1 := expect_eq_openAILawG g μ L (β m p / 2)
      (fun V => f ((OpenAIConfig.configEquiv L).symm V))
    rw [show 2 * (β m p / 2) = β m p by ring] at h1
    refine Eq.trans ?_ h1
    congr 1
    funext U
    simp only [MeasurableEquiv.symm_apply_apply]
  have hc := wilson_conn_even_sideG (G := g.image) (div_nonneg (hβ m p) zero_le_two) hn he h0
    (L : ℕ) (by rw [hL]; exact hLe) (by rw [hL]; exact hL2) a b ham hbm A B hab hbb s t hst
  rw [e, e, e] at hc
  exact hc

end MassGap.OpenAIBridgeGroups

#print axioms MassGap.OpenAIBridgeGroups.Δ_corner0_ZRG
#print axioms MassGap.OpenAIBridgeGroups.wilson_gap_sharpG
#print axioms MassGap.OpenAIBridgeGroups.seqFactsG
#print axioms MassGap.OpenAIBridgeGroups.yWG_at
#print axioms MassGap.OpenAIBridgeGroups.yWG_next
#print axioms MassGap.OpenAIBridgeGroups.climb_yWG
#print axioms MassGap.OpenAIBridgeGroups.gap_side_excitedG
#print axioms MassGap.OpenAIBridgeGroups.gap_even_sideG
#print axioms MassGap.OpenAIBridgeGroups.cluster_even_sideG
#print axioms MassGap.OpenAIBridgeGroups.connTorus_even_side_uniformG
#print axioms MassGap.OpenAIBridgeGroups.Zc_trPairG
#print axioms MassGap.OpenAIBridgeGroups.measurable_spSliceG
#print axioms MassGap.OpenAIBridgeGroups.spSliceG_joinWG
#print axioms MassGap.OpenAIBridgeGroups.corrNum_slabG
#print axioms MassGap.OpenAIBridgeGroups.ZRG_eq_trPowG
#print axioms MassGap.OpenAIBridgeGroups.connTorus_eq_expectG
#print axioms MassGap.OpenAIBridgeGroups.wilson_conn_even_sideG
#print axioms MassGap.OpenAIBridgeGroups.eq_probHaar_image
#print axioms MassGap.OpenAIBridgeGroups.expect_eq_openAILawG
#print axioms MassGap.OpenAIBridgeGroups.familyGap_on_openAI_lawsG
#print axioms MassGap.OpenAIBridgeGroups.familyConn_on_openAI_lawsG
