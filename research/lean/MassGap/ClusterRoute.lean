import Mathlib
import MassGap.ScalePM

/-!
# MassGap.ClusterRoute — `OS0C` from a cluster bound on separated composites

`ScalePM.os0C_of_scalePM` bounds the flowed reading `msLat Wf c k s F = ν_k(∏ᵢ Xᵢ)`,
`Xᵢ = smear a_k (msProx Wf c k s iᵢ) fᵢ`, through `ObserverOS.abs_state_prod_le`: the product of `n`
separated factors by the single-point `2n`-th moment of each factor. Every pairing inside a factor is
present in that moment, so `n` insertions of a channel of dimension `d_j` cost about `γⁿ (n!)^{d_j/2}`, and
one `β` in `OS0C` needs one Gevrey index `r` over all channels (`ScalePM` §4). This module reads the
separation instead: it bounds the cumulants (connected moments) of the separated smeared factors, sums
them over partitions, and gets `|ν_k(∏ᵢ Xᵢ)| ≤ (e γ)ⁿ n! ∏ᵢ Kᵢ` with `β = 1` for composites of every
dimension. Declarations are in the namespace `MassGap.ClusterRoute`.

## 1. Cumulants and the moment bound (proved, general)

* `cum m B`: the cumulant of a moment function `m : Finset ι → ℝ` on a linearly ordered index set, by the
  recursion `m(B) = ∑_{A ⊆ B∖{i₀}} κ(A ∪ {i₀}) m(B ∖ (A ∪ {i₀}))`, `i₀ = min B` (`mom_eq_sum_cum`). This
  recursion is the moment–cumulant formula over set partitions grouped by the block of `i₀`; that `cum`
  is therefore the usual truncated (connected) function is argued, not proved here.
* `abs_mom_le_of_cum`: if `|κ(B)| ≤ c^{|B|} (|B| − 1)! ∏_{i∈B} Kᵢ` on every non-empty `B`, then
  `|m(B)| ≤ c^{|B|} |B|! ∏_{i∈B} Kᵢ`. The count is exact: `∑_{A ⊆ E} |A|! (|E| − |A|)! = (|E| + 1)!`
  (`sum_powerset_fact`), which corresponds to `∑_π ∏_{b∈π} (|b| − 1)! = n!` over set partitions (argued).
* `tree_count_le`: Cayley's count `n^{n−2}` of trees on `n` labelled points is at most `eⁿ (n − 1)!`
  (`n^n ≤ eⁿ n!`). `abs_state_prod_le_of_cluster`: a tree-graph bound
  `|κ(B)| ≤ γ^{|B|} |B|^{|B|−2} ∏_{i∈B} Kᵢ` on the cumulants of `n` observables in a state gives
  `|ν(∏ᵢ Yᵢ)| ≤ (e γ)ⁿ n! ∏ᵢ Kᵢ`.

## 2. The route input

`ClusterPM Wf c`: one ratio `θc > 0`, one tree weight `γ ≥ 0`, and per composite `i` one `Kcᵢ > 0`, `λᵢ`,
such that for every `n`, every continuous `d`-separated family `F` of `n` composites (`0 < d ≤ 1`), every flow
scale `0 < s ≤ θc d`, eventually in the step, every non-empty `B` has
`|κ_k(Xᵢ : i ∈ B)| ≤ γ^{|B|} |B|^{|B|−2} ∏_{i∈B} (wS(a_k, fᵢ) + a_k) Kc_{iᵢ} s^{−λ_{iᵢ}}`, the cumulant of the
smeared flowed proxies that `msLat` multiplies (`clX`). The factor constant is linear in each factor: no
moment order enters it. `ClusterGap Wf c m` is the same bound with the tree factor
`e^{−m d (|B| − 1)}`; `clusterPM_of_clusterGap` (`m ≥ 0`) drops it.

## 3. The route

* `abs_msLat_le_cl`, `abs_contC_le_cl`, `os0C_of_cluster`: `ConvC`, `ExpandR` and `ClusterPM` give `OS0C`
  with `α = 1 + θ'^ε`, `γ_OS = max(e γ, 1)`, `β = 1`, `Ccᵢ = Kcᵢ θ'^{−λᵢ} + |K_r|`, `κᵢ = max(λᵢ, κr_i)`.
  `CoefBound` is not read.
* The other consumers (`ConvC`, `OS1C`, `uv`) fix the number of insertions before the step limit, so a
  Gevrey index per channel serves them: `ScalePMChan b Wf γ γP` is `ScalePM.ScalePMAt` with `∃ rⱼ` inside
  the channel clause, no common `r` and no `1 ≤ r`; `ScalePMChan.uniform` takes the largest `rⱼ` on a finite channel
  set (`scaleChanPM_mono_r`). `scaleControlChan_of_PM`: `ScaleControlAllPM` gives it.
  `uv_of_chan`, `boundC_ren_of_chan`, `convC_of_chan`, `os1C_of_chan` re-prove the consumers from it.
* `SubstrateCoreCL`, `compOS_of_covC_cl`, `approxK_of_beyond_covC_cl`, `inputsAt_of_covC_phys_cl`,
  `NarrowInputsAtCL` and **`clayInputsN_of_narrowAtCL`**: `NarrowInputsAtCL N hN2 W r` gives
  `SUNBest.ClayInputsN N hN2`. Against `ScalePM.NarrowInputsAtPM` the scale clause has a Gevrey index per
  channel, `CoefBound` is gone, and `ClusterPM Wf cf` is added. The bundle's gap slot is `RunSeedN.EndpointN N`,
  refuted by `EndpointAudit.not_endpointN_of_levels_unbounded` under the argued growth of the zero-flux level
  count, so no `ClayStatement` capstone is stated from it here; `ClayRunSeed.clayStatement_of_narrowAtRS` is
  the capstone with `WDeltaRun.RunSeed N` in that slot.

## 4. Why `ClusterPM` is consistent, and what it asks (argued; no declaration)

The cumulant of the smeared factors is multilinear: it is `∑_{x} ∏ᵢ a⁴ fᵢ(xᵢ) κ_k(msProx_{iᵢ}(xᵢ))` over
lattice points `xᵢ` in the supports, pairwise at distance at least `d`, and `msProx` is a finite
combination of the flowed channels `msFlow_j`. A pointwise tree-graph bound
`|κ_k(O_{j₁}(x₁), …, O_{jₙ}(xₙ))| ≤ ∏ᵢ K_{jᵢ} μ_{jᵢ}(s)^{−1} ∑_{trees T} ∏_{(a,b) ∈ T} γ e^{−m|x_a − x_b|}` at
separated points therefore gives `ClusterPM`: every edge joins two distinct factors, so each edge weight
is at most `γ e^{−m d} ≤ γ`, Cayley's formula counts `|B|^{|B|−2}` trees, and summing the weights over the
points gives `∏ᵢ wS(a_k, fᵢ)`. The flowed channel at scale `s` has size `μ_j(s)^{−1} ≈ s^{−d_j}` up to
logarithms, which is the `s^{−λ}` of the factor constant.

The massive free field meets this. At separated points the Wick monomials have no pairing inside a factor,
and the Cauchy bound on the separated Gaussian moments gives `|ν(∏ᵢ :φ^{mᵢ}:(xᵢ))| ≤ ∏ᵢ (e K mᵢ)^{mᵢ/2}`
with `K = supᵢ ∑_{j≠i} |G(xᵢ − xⱼ)|`. Over `d`-separated points in four dimensions that sum is finite
uniformly in the number of points when `|G|` decays faster than `r^{−4}` (a mass, or derivatives); for the
massless scalar propagator it grows like `n^{1/2}`, which still fits `ClusterPM` for composites of few legs.
The moments are then bounded by a constant per factor, and Möbius inversion over partitions bounds the cumulants by
`Cⁿ n! ∏ᵢ Kᵢ`, within `ClusterPM`'s `γ^{|B|} |B|^{|B|−2}` after enlarging `γ`.

So `ClusterPM` is a uniform clustering (integrability) input that a convergent cluster expansion gives (a
spectral gap alone gives two-point clustering, not this): its content is the
uniformity of the per-factor constant in the number of separated insertions, which a decay rate `m > 0` of
the connected correlations gives (a cluster expansion converging at rate `m` has the tree-graph form
above). It asserts no decay rate itself: `ClusterPM` is `ClusterGap Wf c 0`, and `ClusterGap Wf c m` states
the bound with the decay explicit. The multilinear passage from separated lattice sites to the smeared
factors is proved in `ClusterPassage` (`clusterGap_of_pointGap`, `clusterPM_of_pointCluster`, and
`clusterPM_of_chan` from the flowed channels). The pointwise tree-graph bound for the Wilson state
(`ClusterPassage.PointCluster`, or `PointGapChanAt` with `CoefCtl`) is not proved.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `1` the top of the separation, the floor of `K` and `Γ`, and `β`; `2` Cayley's
exponent offset and the even moment powers; `e = exp 1` from `n^n ≤ eⁿ n!`; `0` the signs and limits.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ClusterRoute

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup MassGap.ContinuumReconstruction
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice
  MassGap.ProxyGenLimN MassGap.FlowCovN MassGap.ApproxJoint MassGap.ClayNarrow
  MassGap.ObserverMultigrid MassGap.ClayNarrowMG MassGap.ScalePC MassGap.ScalePM
open MassGap.ScaleControlFull (zOne)

/-! ## 1. Cumulants and the moment bound -/

section Cumulant

variable {ι : Type*} [LinearOrder ι]

/-- **The cumulant of a moment function**, by the recursion on the block of the least index:
`κ(B) = m(B) − ∑_{A ⊊ B∖{i₀}} κ(A ∪ {i₀}) m(B∖{i₀} ∖ A)`, `i₀ = min B`; `κ(∅) = 0`.
DERIVED: `0` the empty value. -/
def cum (m : Finset ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then
    m B - ∑ A ∈ ((B.erase (B.min' h)).powerset.erase (B.erase (B.min' h))).attach,
      cum m (insert (B.min' h) A.1) * m (B.erase (B.min' h) \ A.1)
  else 0
termination_by B.card
decreasing_by
  have hA := A.2
  rw [Finset.mem_erase, Finset.mem_powerset] at hA
  have hlt : A.1.card < (B.erase (B.min' h)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hA.2, hA.1⟩)
  rw [Finset.card_erase_of_mem (Finset.min'_mem B h)] at hlt
  have h1 := Finset.card_insert_le (B.min' h) A.1
  have h2 := Finset.card_pos.2 h
  omega

/-- The defining recursion of `cum` on a non-empty set. DERIVED: no numeral. -/
theorem cum_of_nonempty (m : Finset ι → ℝ) {B : Finset ι} (h : B.Nonempty) :
    cum m B = m B - ∑ A ∈ (B.erase (B.min' h)).powerset.erase (B.erase (B.min' h)),
      cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A) := by
  rw [cum, dif_pos h, Finset.sum_attach _
    (fun A => cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A))]

/-- **The moment–cumulant recursion**: with `m(∅) = 1`,
`m(B) = ∑_{A ⊆ B∖{i₀}} κ(A ∪ {i₀}) m(B∖{i₀} ∖ A)`. DERIVED: `1` the empty moment. -/
theorem mom_eq_sum_cum (m : Finset ι → ℝ) (h0 : m ∅ = 1) {B : Finset ι} (h : B.Nonempty) :
    m B = ∑ A ∈ (B.erase (B.min' h)).powerset,
      cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A) := by
  rw [← Finset.insert_erase (Finset.mem_powerset_self (B.erase (B.min' h))),
    Finset.sum_insert (Finset.notMem_erase _ _),
    Finset.insert_erase (Finset.min'_mem B h), sdiff_self, Finset.bot_eq_empty, h0, mul_one,
    cum_of_nonempty m h]
  ring

/-- **`∑_{A ⊆ E} |A|! (|E| − |A|)! = (|E| + 1)!`**: the number of permutations of `|E| + 1` points counted by
the cycle of the extra point. DERIVED: `1` the extra point. -/
theorem sum_powerset_fact {α : Type*} (E : Finset α) :
    ∑ A ∈ E.powerset, ((A.card.factorial : ℝ) * ((E.card - A.card).factorial : ℝ))
      = ((E.card + 1).factorial : ℝ) := by
  have h := Finset.sum_powerset_apply_card
    (fun a => ((a.factorial : ℝ) * ((E.card - a).factorial : ℝ))) (x := E)
  rw [h]
  have hterm : ∀ a ∈ Finset.range (E.card + 1),
      (E.card.choose a) • ((a.factorial : ℝ) * ((E.card - a).factorial : ℝ))
        = (E.card.factorial : ℝ) := by
    intro a ha
    rw [nsmul_eq_mul, ← mul_assoc]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha))
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.factorial_succ]
  push_cast
  ring

/-- **Cumulants with `(|B| − 1)!` growth give moments with `|B|!` growth**: if
`|κ(B)| ≤ c^{|B|} (|B| − 1)! ∏_{i∈B} Kᵢ` on every non-empty `B` and `m(∅) = 1`, then
`|m(B)| ≤ c^{|B|} |B|! ∏_{i∈B} Kᵢ`. DERIVED: `1` the empty moment and the block offset; `0` the signs. -/
theorem abs_mom_le_of_cum (m : Finset ι → ℝ) (h0 : m ∅ = 1) (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i) {c : ℝ}
    (hc : 0 ≤ c)
    (hcum : ∀ B : Finset ι, B.Nonempty →
      |cum m B| ≤ c ^ B.card * ((B.card - 1).factorial : ℝ) * ∏ i ∈ B, K i) :
    ∀ B : Finset ι, |m B| ≤ c ^ B.card * (B.card.factorial : ℝ) * ∏ i ∈ B, K i := by
  intro B
  induction B using Finset.strongInduction with
  | H B ih =>
    rcases B.eq_empty_or_nonempty with rfl | h
    · simp [h0]
    · rw [mom_eq_sum_cum m h0 h]
      have hi0B : B.min' h ∈ B := Finset.min'_mem B h
      have hcardB : (B.erase (B.min' h)).card + 1 = B.card := Finset.card_erase_add_one hi0B
      have hterm : ∀ A ∈ (B.erase (B.min' h)).powerset,
          |cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A)|
            ≤ c ^ B.card * (∏ i ∈ B, K i)
              * ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) := by
        intro A hA
        rw [Finset.mem_powerset] at hA
        have hi0A : B.min' h ∉ A := fun hm => Finset.notMem_erase (B.min' h) B (hA hm)
        have hAc : A.card ≤ (B.erase (B.min' h)).card := Finset.card_le_card hA
        have hsdc : (B.erase (B.min' h) \ A).card = (B.erase (B.min' h)).card - A.card := by
          have := Finset.card_sdiff_add_card_eq_card hA
          omega
        have hss : B.erase (B.min' h) \ A ⊂ B := by
          refine (Finset.ssubset_iff_of_subset
            ((Finset.sdiff_subset).trans (Finset.erase_subset _ _))).2 ⟨B.min' h, hi0B, ?_⟩
          intro hm
          exact Finset.notMem_erase (B.min' h) B (Finset.sdiff_subset hm)
        have hc1 := hcum (insert (B.min' h) A) (Finset.insert_nonempty _ _)
        rw [Finset.card_insert_of_notMem hi0A, Nat.add_sub_cancel] at hc1
        have hm1 := ih _ hss
        rw [hsdc] at hm1
        have hP : (∏ i ∈ insert (B.min' h) A, K i) * ∏ i ∈ B.erase (B.min' h) \ A, K i
            = ∏ i ∈ B, K i := by
          rw [Finset.prod_insert hi0A, mul_assoc, mul_comm (∏ i ∈ A, K i),
            Finset.prod_sdiff hA, Finset.mul_prod_erase B K hi0B]
        have hC : c ^ (A.card + 1) * c ^ ((B.erase (B.min' h)).card - A.card) = c ^ B.card := by
          rw [← pow_add]
          congr 1
          omega
        have hR0 : 0 ≤ c ^ (A.card + 1) * (A.card.factorial : ℝ) * ∏ i ∈ insert (B.min' h) A, K i :=
          mul_nonneg (mul_nonneg (pow_nonneg hc _) (Nat.cast_nonneg _))
            (Finset.prod_nonneg fun i _ => hK i)
        rw [abs_mul]
        calc |cum m (insert (B.min' h) A)| * |m (B.erase (B.min' h) \ A)|
            ≤ (c ^ (A.card + 1) * (A.card.factorial : ℝ) * ∏ i ∈ insert (B.min' h) A, K i)
              * (c ^ ((B.erase (B.min' h)).card - A.card)
                * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)
                * ∏ i ∈ B.erase (B.min' h) \ A, K i) :=
              mul_le_mul hc1 hm1 (abs_nonneg _) hR0
          _ = c ^ B.card * (∏ i ∈ B, K i)
              * ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) := by
              rw [← hC, ← hP]
              ring
      calc |∑ A ∈ (B.erase (B.min' h)).powerset,
            cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A)|
          ≤ ∑ A ∈ (B.erase (B.min' h)).powerset,
            |cum m (insert (B.min' h) A) * m (B.erase (B.min' h) \ A)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ A ∈ (B.erase (B.min' h)).powerset, c ^ B.card * (∏ i ∈ B, K i)
              * ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) :=
            Finset.sum_le_sum hterm
        _ = c ^ B.card * (∏ i ∈ B, K i) * ∑ A ∈ (B.erase (B.min' h)).powerset,
              ((A.card.factorial : ℝ) * (((B.erase (B.min' h)).card - A.card).factorial : ℝ)) :=
            (Finset.mul_sum _ _ _).symm
        _ = c ^ B.card * (B.card.factorial : ℝ) * ∏ i ∈ B, K i := by
            rw [sum_powerset_fact, hcardB]
            ring

end Cumulant

/-- **Cayley's tree count against the factorial**: `n^{n−2} ≤ eⁿ (n − 1)!` for `n ≥ 1` (`n^n ≤ eⁿ n!`).
DERIVED: `2` Cayley's exponent offset; `1` the least size and `e = exp 1`. -/
theorem tree_count_le (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (n - 2) ≤ Real.exp 1 ^ n * ((n - 1).factorial : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn0.le n
  rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n)] at h1
  have hexp : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have hfac : (n.factorial : ℝ) = n * ((n - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred (by omega : n ≠ 0)]
    push_cast
    ring
  have hpow : (n : ℝ) ^ (n - 2) ≤ (n : ℝ) ^ (n - 1) :=
    pow_le_pow_right₀ (by exact_mod_cast hn) (by omega)
  have hnn : (n : ℝ) ^ n = n * (n : ℝ) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hmain : (n : ℝ) * (n : ℝ) ^ (n - 1) ≤ (n : ℝ) * (Real.exp 1 ^ n * ((n - 1).factorial : ℝ)) := by
    rw [← hnn]
    calc (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := h1
      _ = (n : ℝ) * (Real.exp 1 ^ n * ((n - 1).factorial : ℝ)) := by rw [hexp, hfac]; ring
  exact hpow.trans (le_of_mul_le_mul_left hmain hn0)

/-- **The tree-graph form gives the factorial form**: `γ^b b^{b−2} P ≤ (e γ)^b (b − 1)! P`, `b ≥ 1`.
DERIVED: `2` Cayley's offset; `1` the least size. -/
theorem tree_le_fact {γ P : ℝ} (hγ : 0 ≤ γ) (hP : 0 ≤ P) (b : ℕ) (hb : 1 ≤ b) :
    γ ^ b * ((b : ℝ) ^ (b - 2)) * P ≤ (Real.exp 1 * γ) ^ b * ((b - 1).factorial : ℝ) * P := by
  refine mul_le_mul_of_nonneg_right ?_ hP
  rw [mul_pow, mul_comm (Real.exp 1 ^ b), mul_assoc]
  exact mul_le_mul_of_nonneg_left (tree_count_le b hb) (pow_nonneg hγ _)

/-- The moments of a family of observables in a state, `B ↦ ν(∏_{i∈B} Yᵢ)`. DERIVED: no numeral. -/
def stMom {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X) {ι : Type*}
    (Y : ι → C(X, ℝ)) (B : Finset ι) : ℝ :=
  ν (∏ i ∈ B, Y i)

/-- DERIVED: `1` the empty moment. -/
theorem stMom_empty {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    {ι : Type*} (Y : ι → C(X, ℝ)) : stMom ν Y ∅ = 1 := by
  rw [stMom, Finset.prod_empty, ν.map_one]

/-- **The product of `n` observables from a tree-graph bound on their cumulants**:
`|κ(B)| ≤ γ^{|B|} |B|^{|B|−2} ∏_{i∈B} Kᵢ` on every non-empty `B` gives `|ν(∏ᵢ Yᵢ)| ≤ (e γ)ⁿ n! ∏ᵢ Kᵢ`.
DERIVED: `2` Cayley's offset; `1` the least block size. -/
theorem abs_state_prod_le_of_cluster {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {ι : Type*} [Fintype ι] [LinearOrder ι] (Y : ι → C(X, ℝ))
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i) {γ : ℝ} (hγ : 0 ≤ γ)
    (hcl : ∀ B : Finset ι, B.Nonempty →
      |cum (stMom ν Y) B| ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * ∏ i ∈ B, K i) :
    |ν (∏ i, Y i)|
      ≤ (Real.exp 1 * γ) ^ Fintype.card ι * ((Fintype.card ι).factorial : ℝ) * ∏ i, K i := by
  have h := abs_mom_le_of_cum (stMom ν Y) (stMom_empty ν Y) K hK
    (mul_nonneg (Real.exp_pos 1).le hγ) (fun B hB => (hcl B hB).trans
      (tree_le_fact hγ (Finset.prod_nonneg fun i _ => hK i) B.card (Finset.card_pos.2 hB)))
    Finset.univ
  rwa [Finset.card_univ] at h

/-! ## 2. The route input -/

variable {N : ℕ}

/-- The smeared flowed proxies that `msLat` multiplies. DERIVED: no numeral. -/
def clX [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) {n : ℕ}
    (F : Fin n → CDatum (CbR N zOne)) : Fin n → C(Cfg N, ℝ) :=
  fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2

/-- **The cluster input**: one ratio `θc > 0`, one tree weight `γ ≥ 0`, per composite `Kcᵢ > 0`, `λᵢ`; on
every continuous `d`-separated family of `n` composites, `0 < d ≤ 1`, at every flow scale `0 < s ≤ θc d`,
eventually in the step, the cumulants of the smeared flowed proxies obey the tree-graph bound
`|κ_k(B)| ≤ γ^{|B|} |B|^{|B|−2} ∏_{i∈B} (wS(a_k, fᵢ) + a_k) Kc_{iᵢ} s^{−λ_{iᵢ}}`.
DERIVED: `2` Cayley's offset; `1` the top of the separation; `0` the signs. -/
def ClusterPM [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ (θc γ : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 ≤ γ ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
      ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ᶠ k in atTop, ∀ B : Finset (Fin n), B.Nonempty →
        |cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B|
          ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2))
            * ∏ i ∈ B, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
              * (Kc (F i).1 * s⁻¹ ^ lam (F i).1))

/-- **The cluster input with the decay explicit**: `ClusterPM`'s bound with the tree factor
`e^{−m d (|B| − 1)}`, which a tree-graph bound with edge weights `e^{−m|x_a − x_b|}` on `d`-separated
points gives. DERIVED: `1` the edge count offset; `2` Cayley's offset; `0` the signs. -/
def ClusterGap [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (m : ℝ) : Prop :=
  ∃ (θc γ : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 ≤ γ ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
      ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ᶠ k in atTop, ∀ B : Finset (Fin n), B.Nonempty →
        |cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B|
          ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * Real.exp (-(m * d * ((B.card : ℝ) - 1)))
            * ∏ i ∈ B, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
              * (Kc (F i).1 * s⁻¹ ^ lam (F i).1))

/-- **The decay factor is at most `1`**: `ClusterGap` at `m ≥ 0` gives `ClusterPM`.
DERIVED: `1` the edge count offset; `0` the signs. -/
theorem clusterPM_of_clusterGap [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {m : ℝ}
    (hm : 0 ≤ m) (h : ClusterGap Wf c m) : ClusterPM Wf c := by
  obtain ⟨θc, γ, Kc, lam, hθc, hγ, hKc, H⟩ := h
  refine ⟨θc, γ, Kc, lam, hθc, hγ, hKc, fun n F d hd hd1 hcont hsep s hs hsd => ?_⟩
  filter_upwards [H n F d hd hd1 hcont hsep s hs hsd] with k hk B hB
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hP : 0 ≤ ∏ i ∈ B, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
      * (Kc (F i).1 * s⁻¹ ^ lam (F i).1)) :=
    Finset.prod_nonneg fun i _ => mul_nonneg (add_nonneg (wS_nonneg ha _) ha.le)
      (mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _))
  have hb1 : (1 : ℝ) ≤ B.card := by exact_mod_cast Finset.card_pos.2 hB
  have hE : Real.exp (-(m * d * ((B.card : ℝ) - 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (mul_nonneg hm hd.le) (by linarith)
  have hT : 0 ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) :=
    mul_nonneg (pow_nonneg hγ _) (pow_nonneg (Nat.cast_nonneg _) _)
  refine (hk B hB).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hT hE) hP

/-! ## 3. `OS0C` from the cluster input -/

/-- **The flowed reading from the cluster bound at one step**: `|msLat| ≤ (e γ)ⁿ n! ∏ᵢ Kᵢ`.
DERIVED: `0` the signs. -/
theorem abs_msLat_le_cl [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) {s : ℝ}
    (hs : 0 < s) {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) {γ : ℝ} (hγ : 0 ≤ γ) (Kc lam : Ix0 → ℝ)
    (hKc : ∀ i, 0 < Kc i)
    (hB : ∀ B : Finset (Fin n), B.Nonempty →
      |cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B|
        ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2))
          * ∏ i ∈ B, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
            * (Kc (F i).1 * s⁻¹ ^ lam (F i).1))) :
    |msLat Wf c k s F|
      ≤ (Real.exp 1 * γ) ^ n * (n.factorial : ℝ)
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1)) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have h := abs_state_prod_le_of_cluster (stateK (NeZero.ne N) k) (clX Wf c k s F)
    (fun i => (wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1))
    (fun i => mul_nonneg (add_nonneg (wS_nonneg ha _) ha.le)
      (mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _))) hγ hB
  rw [Fintype.card_fin] at h
  exact h

/-- **The continuum reading from the cluster bound** (`abs_msLat_le_cl`, `tendsto_wS`):
`|contC F| ≤ (e γ)ⁿ n! ∏ᵢ ‖fᵢ‖₁ Kcᵢ s^{−λᵢ} + R` with `R` the expansion remainder. DERIVED: `0` the limit of the
spacing. -/
theorem abs_contC_le_cl [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {s : ℝ} (hs : 0 < s) {n : ℕ} (F : Fin n → CDatum (CRen N z μ))
    (hF : Adm F) {γ : ℝ} (hγ : 0 ≤ γ) (Kc lam : Ix0 → ℝ) (hKc : ∀ i, 0 < Kc i)
    (hS : ∀ᶠ k in atTop, ∀ B : Finset (Fin n), B.Nonempty →
      |cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B|
        ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2))
          * ∏ i ∈ B, ((wS (dySpacing N k) (F i).2 + dySpacing N k)
            * (Kc (F i).1 * s⁻¹ ^ lam (F i).1)))
    (hconv : ConvC (NeZero.ne N) (CRen N z μ)) {Rm : ℝ}
    (hrem : ∀ᶠ k in atTop, |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ Rm) :
    |contC (NeZero.ne N) (CRen N z μ) F|
      ≤ (Real.exp 1 * γ) ^ n * (n.factorial : ℝ)
        * ∏ i, (l1 (F i).2 * (Kc (F i).1 * s⁻¹ ^ lam (F i).1)) + Rm := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hlim : Tendsto (fun k => (Real.exp 1 * γ) ^ n * (n.factorial : ℝ)
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1)) + Rm)
      atTop (𝓝 ((Real.exp 1 * γ) ^ n * (n.factorial : ℝ)
        * ∏ i, (l1 (F i).2 * (Kc (F i).1 * s⁻¹ ^ lam (F i).1)) + Rm)) := by
    refine (Tendsto.const_mul _ (tendsto_finsetProd _ fun i _ => ?_)).add_const Rm
    have h1 := ((tendsto_wS (N := N) (F i).2 (hF.1 i)).add (tendsto_dySpacing N)).mul_const
      (Kc (F i).1 * s⁻¹ ^ lam (F i).1)
    rwa [add_zero] at h1
  have hev : ∀ᶠ k in (ultra : Filter ℕ), |latC (NeZero.ne N) (CRen N z μ) k F|
      ≤ (Real.exp 1 * γ) ^ n * (n.factorial : ℝ)
        * ∏ i, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1))
        + Rm := by
    refine Filter.Eventually.filter_mono ultra_le ?_
    filter_upwards [hS, hrem] with k hk hr
    have hP := abs_msLat_le_cl Wf c k hs F hγ Kc lam hKc hk
    have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F) (msLat Wf c k s F)
    linarith
  exact le_of_tendsto_of_tendsto ((hconv (Fin n) F hF).abs) (hlim.mono_left ultra_le) hev

/-- **`OS0C (CRen N z μ)` from `ConvC`, `ExpandR` and the cluster input**, with `β = 1`:
`α = 1 + θ'^ε`, `γ_OS = max(e γ, 1)`, `Ccᵢ = Kcᵢ θ'^{−λᵢ} + |K_r|`, `κᵢ = max(λᵢ, κr_i)`, `θ' = min(θ, θc, 1)`.
DERIVED: `1` the exponent `β`, the floor of `γ_OS` and the top of `θ'`. -/
theorem os0C_of_cluster [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hconv : ConvC (NeZero.ne N) (CRen N z μ))
    (hex : ExpandR Wf c z μ) (hcl : ClusterPM Wf c) : OS0C (NeZero.ne N) (CRen N z μ) := by
  obtain ⟨θc, γ, Kc, lam, hθc, hγ, hKc, hC⟩ := hcl
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  set θ' : ℝ := min θ (min θc 1) with hθ'def
  have hθ'0 : 0 < θ' := lt_min hθ (lt_min hθc one_pos)
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'c : θ' ≤ θc := (min_le_right _ _).trans (min_le_left _ _)
  set Γ : ℝ := max (Real.exp 1 * γ) 1 with hΓdef
  refine ⟨1 + θ' ^ ε, Γ, 1, fun i => Kc i * θ'⁻¹ ^ lam i + |Kr|, fun i => max (lam i) (κr i), ?_⟩
  intro n F d hd hd1 hcont hsep
  beta_reduce
  have hs : 0 < θ' * d := mul_pos hθ'0 hd
  have hsθ : θ' * d ≤ θ * d := mul_le_mul_of_nonneg_right hθ'θ hd.le
  have hsc : θ' * d ≤ θc * d := mul_le_mul_of_nonneg_right hθ'c hd.le
  have hA := abs_contC_le_cl hs F ⟨hcont, d, hd, hsep⟩ hγ Kc lam hKc
    (hC n F d hd hd1 hcont hsep (θ' * d) hs hsc) hconv
    (hE (Fin n) F d hd hcont hsep (θ' * d) hs hsθ)
  have hsd : θ' * d / d = θ' := mul_div_cancel_right₀ θ' hd.ne'
  rw [Fintype.card_fin, hsd] at hA
  have hl1 : ∀ i, 0 ≤ l1 (F i).2 := fun i => MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hfac : ∀ i, l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1)
      ≤ (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2
      ∧ |Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 := fun i =>
    os0_factor_le (hl1 i) (hKc _) hθ'0 hd hd1 rfl le_rfl
  have hθε : 0 ≤ θ' ^ ε := Real.rpow_nonneg hθ'0.le _
  have hZ0 : 0 ≤ ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_nonneg fun i _ => (mul_nonneg (abs_nonneg Kr)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i))).trans (hfac i).2
  have hF0 : ∀ i, 0 ≤ l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1) := fun i =>
    mul_nonneg (hl1 i) (mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _))
  have hPi1 : ∏ i, (l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1))
      ≤ ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => hF0 i) (fun i _ => (hfac i).1)
  have hPi10 : 0 ≤ ∏ i, (l1 (F i).2 * (Kc (F i).1 * (θ' * d)⁻¹ ^ lam (F i).1)) :=
    Finset.prod_nonneg fun i _ => hF0 i
  have hPi2 : ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
      ≤ ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 :=
    Finset.prod_le_prod (fun i _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i))) (fun i _ => (hfac i).2)
  have hrem : Kr ^ n * θ' ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ θ' ^ ε * ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := by
    have hPi : 0 ≤ ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) :=
      Finset.prod_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hd.le _)) (hl1 i)
    have hK : Kr ^ n ≤ |Kr| ^ n := (le_abs_self _).trans (abs_pow Kr n).le
    have e : ∏ i, (|Kr| * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
        = |Kr| ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e]
    calc Kr ^ n * θ' ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
        = θ' ^ ε * (Kr ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) := by ring
      _ ≤ θ' ^ ε * (|Kr| ^ n * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hPi) hθε
  have hM : (Real.exp 1 * γ) ^ n * (n.factorial : ℝ) ≤ Γ ^ n * (n.factorial : ℝ) :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (Real.exp_pos 1).le hγ) (le_max_left _ _) n) (Nat.cast_nonneg _)
  have hM1 : (1 : ℝ) ≤ Γ ^ n * (n.factorial : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_right _ _))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hM0 : 0 ≤ Γ ^ n * (n.factorial : ℝ) := zero_le_one.trans hM1
  have hT1 := mul_le_mul hM hPi1 hPi10 hM0
  have hT2 : Kr ^ n * θ' ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
      ≤ θ' ^ ε * (Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
        * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2) :=
    hrem.trans (mul_le_mul_of_nonneg_left (hPi2.trans (le_mul_of_one_le_left hZ0 hM1)) hθε)
  rw [Real.rpow_one]
  calc |contC (NeZero.ne N) (CRen N z μ) F| ≤ _ := hA
    _ ≤ Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2
        + θ' ^ ε * (Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2) := add_le_add hT1 hT2
    _ = (1 + θ' ^ ε) * Γ ^ n * (n.factorial : ℝ) * ∏ i, (Kc (F i).1 * θ'⁻¹ ^ lam (F i).1 + |Kr|)
          * (d ^ max (lam (F i).1) (κr (F i).1))⁻¹ * l1 (F i).2 := by ring

/-! ## 4. The scale input with a Gevrey index per channel -/

/-- **The moment scale input, one index per channel**: `ScalePM.ScalePMAt` with the growth index `rⱼ`
chosen per channel. DERIVED: `0` the lower end of the scale. -/
structure ScalePMChan [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) (γ : Ix0 → ℝ) (γP : ℝ) : Prop where
  /-- Every channel, its own index, every scale in `(0, b]`, every order, eventually in the step. -/
  chan : ∀ j : MIx, ∃ (r : ℕ) (t K : ℝ), 0 < t ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ,
    ∀ᶠ k in atTop, ScaleChanPM Wf r t K γ γP k s j p
  /-- The plaquette class at the physical scale, with one set of constants. -/
  top : ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop, ∀ q, ScaleChan Wf t C γ γP k b (Sum.inr q)

/-- **Control at every intermediate scale, by moments, one index per channel.** DERIVED: no numeral. -/
def ScaleControlChan [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (γ : Ix0 → ℝ) (γP : ℝ), ScalePMChan b Wf γ γP

/-- `ScaleControlAllPM` gives `ScaleControlChan` (the common index at every channel).
DERIVED: no numeral. -/
theorem scaleControlChan_of_PM [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N}
    (h : ScaleControlAllPM b Wf) : ScaleControlChan b Wf := by
  obtain ⟨r, γ, γP, H⟩ := h
  refine ⟨γ, γP, fun j => ?_, H.top⟩
  obtain ⟨t, K, ht, hj⟩ := H.chan j
  exact ⟨r, t, K, ht, hj⟩

/-- **A larger index keeps the moment bound** (`(2p)! ≥ 1`, `K ≥ 0`). DERIVED: `2` the even power; `0` the
signs. -/
theorem scaleChanPM_mono_r [NeZero N] {Wf : ℝ → ConfFlow N} {r r' : ℕ} {t K : ℝ} {γ : Ix0 → ℝ}
    {γP : ℝ} {k : ℕ} {s : ℝ} {j : MIx} {p : ℕ} (hs : 0 < s) (ht : 0 < t) (hK : 0 ≤ K) (hr : r ≤ r')
    (h : ScaleChanPM Wf r t K γ γP k s j p) : ScaleChanPM Wf r' t K γ γP k s j p := by
  unfold ScaleChanPM at h ⊢
  have hm := msMu_pos ht γ γP hs j
  have hf : ((2 * p).factorial : ℝ) ^ r ≤ ((2 * p).factorial : ℝ) ^ r' :=
    pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)) hr
  refine h.trans ?_
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hf (inv_nonneg.2 (pow_nonneg hm.le _))) hK

/-- **One index, one `t > 0`, one `K ≥ 1` on a finite channel set** (the largest index, the least rate,
the largest constant and `1`). DERIVED: `1` the floor of `K` and the extra rate. -/
theorem ScalePMChan.uniform [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N} {γ : Ix0 → ℝ} {γP : ℝ}
    (h : ScalePMChan b Wf γ γP) (T : Finset MIx) :
    ∃ (r : ℕ) (t K : ℝ), 0 < t ∧ 1 ≤ K ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ p : ℕ,
      ∀ᶠ k in atTop, ∀ j ∈ T, ScaleChanPM Wf r t K γ γP k s j p := by
  classical
  choose rf tf Kf htf hev using h.chan
  set t := (insert 1 (T.image tf)).min' (Finset.insert_nonempty _ _) with htdef
  set K := (insert 1 (T.image Kf)).max' (Finset.insert_nonempty _ _) with hKdef
  have ht : 0 < t := by
    refine (Finset.lt_min'_iff _ _).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact htf j
  have hK1 : 1 ≤ K := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨T.sup rf, t, K, ht, hK1, fun s hs hsb p => ?_⟩
  filter_upwards [(Filter.eventually_all_finset T).2 fun j _ => hev j s hs hsb p] with k hk j hj
  exact scaleChanPM_mono_r hs ht (by linarith) (Finset.le_sup hj)
    (scaleChanPM_mono hs ht
      (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)))
      (Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))) (by linarith)
      (hk j hj))

/-- **`uv` from the plaquette class at `s = b`** (`ScalePM.uv_of_scalePM`'s proof).
DERIVED: `4` the dimension; `2 · 1 + 3` the site count. -/
theorem uv_of_chan [NeZero N] {W : ConfFlow N} {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b)
    (htop : Wf b = W) (hsc : ScaleControlChan b Wf) :
    ∃ t C : ℝ, 0 < t ∧ FlowUV.SiteExp (NeZero.ne N) W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) C := by
  obtain ⟨γ, γP, H⟩ := hsc
  obtain ⟨t, C, ht, hev⟩ := H.top
  have hpos : 0 < t * b ^ 4 / afLog γP b := div_pos (mul_pos ht (pow_pos hb 4)) (afLog_pos _ _)
  refine ⟨t * b ^ 4 / afLog γP b / (2 * 1 + 3) ^ 4, C, div_pos hpos (by norm_num), ?_⟩
  rw [div_mul_cancel₀ _ (by norm_num : ((2 : ℝ) * 1 + 3) ^ 4 ≠ 0)]
  unfold FlowUV.SiteExp
  filter_upwards [hev] with k hk
  rintro O ⟨q, rfl⟩
  have h1 := hk q
  unfold ScaleChan at h1
  rw [htop, mField_inr, mDim_inr, msMu_inr] at h1
  have e : msAbs (W.fieldMap k (sym (plaqField q))).1 = (W.fieldMap k (sym (plaqField q))).1 := by
    ext U
    have key : ∀ O ∈ SymPlaqClass N, ∀ U, 0 ≤ (W.fieldMap k O).1 U :=
      fun O hO U => symPlaq_nonneg (NeZero.ne N) O hO (W.V k U)
    rw [msAbs_apply]
    exact abs_of_nonneg (key _ ⟨q, rfl⟩ U)
  rw [e] at h1
  exact h1

/-- **`BoundC (CRen N z μ)` from the per-channel moment input and `ExpandR`** (`ScalePM.boundC_ren_of_scalePM`
with the index of the family's finite channel set). DERIVED: `1` the spacing bound. -/
theorem boundC_ren_of_chan [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlChan b Wf)
    (hex : ExpandR Wf c z μ) : InputsTriage.BoundC (NeZero.ne N) (CRen N z μ) := by
  classical
  obtain ⟨γ, γP, H⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, -, hE⟩ := hex
  intro ι _ _ F hF
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hs : 0 < min (θ * d) b := lt_min (mul_pos hθ hd) hb
  obtain ⟨r, t, K, ht, hK1, hev⟩ :=
    H.uniform (Finset.univ.biUnion fun i => (c (F i).1 (min (θ * d) b)).support)
  refine ⟨(1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) ^ r * K))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP c (min (θ * d) b) (F i).1)
    + Kr ^ Fintype.card ι * (min (θ * d) b / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2), ?_⟩
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev _ hs (min_le_right _ _) (Fintype.card ι),
    hE ι F d hd hcont hsep (min (θ * d) b) hs (min_le_left _ _),
    (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hrem hk1
  have hP := abs_msLat_le_on_pm Wf c ht hs hk1.le F hK1 (fun i j hj =>
    hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩))
  have htri := abs_sub_abs_le_abs_sub (latC (NeZero.ne N) (CRen N z μ) k F)
    (msLat Wf c k (min (θ * d) b) F)
  linarith

/-- **`ConvC (CRen N z μ)` from the per-channel moment input and `ExpandR`.** DERIVED: no numeral. -/
theorem convC_of_chan [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlChan b Wf)
    (hex : ExpandR Wf c z μ) : ConvC (NeZero.ne N) (CRen N z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_ren_of_chan hb hsc hex)

/-- **`OS1C (CRen N z μ)` from the per-channel moment input and `ExpandR`** (`ScalePM.os1C_of_scalePM`'s
proof with the index of the family's finite channel set). DERIVED: `2` the halves; `0` the limit. -/
theorem os1C_of_chan [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hsc : ScaleControlChan b Wf)
    (hex : ExpandR Wf c z μ) : OS1C (NeZero.ne N) (CRen N z μ) := by
  classical
  have hconv : ConvC (NeZero.ne N) (CRen N z μ) := convC_of_chan hb hsc hex
  obtain ⟨γ, γP, H⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := hex
  intro ι _ _ F hF v
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hFv_c : ContD (fun i => translateD v (F i)) :=
    fun i => (hcont i).comp (continuous_id.sub continuous_const)
  have hFv_s : SepD d (fun i => translateD v (F i)) :=
    fun i j hij => ContinuumSep.sepBy_translate (hsep i j hij) v
  have hΔ : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
      - latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set A1 : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hA1
    set A2 : ℝ := Kr ^ Fintype.card ι
      * ∏ i, ((d ^ κr (translateD v (F i)).1)⁻¹ * l1 (translateD v (F i)).2) with hA2
    have hφ : Tendsto (fun s : ℝ => (|A1| + |A2|) * (s / d) ^ ε) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => s / d) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := (𝓝 (0 : ℝ)))).div_const d
      have h2 := (h1.rpow_const (Or.inr hε.le)).const_mul (|A1| + |A2|)
      rw [Real.zero_rpow hε.ne', mul_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    obtain ⟨s, hsQ, hsI⟩ := ((hφ.eventually (gt_mem_nhds (half_pos hη))).and
      (Ioo_mem_nhdsGT (lt_min (mul_pos hθ hd) hb) :
        ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (min (θ * d) b))).exists
    have hs : 0 < s := hsI.1
    have hsθ : s ≤ θ * d := hsI.2.le.trans (min_le_left _ _)
    have hsb : s ≤ b := hsI.2.le.trans (min_le_right _ _)
    have hx : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg hs.le hd.le) _
    obtain ⟨r, t, K, ht, hK1, hevU⟩ := H.uniform (Finset.univ.biUnion fun i => (c (F i).1 s).support)
    have hS : ∀ᶠ k in atTop, ∀ i, ∀ j ∈ (c (F i).1 s).support,
        ScaleChanPM Wf r t K γ γP k s j (Fintype.card ι) := by
      filter_upwards [hevU s hs hsb (Fintype.card ι)] with k hk i j hj
      exact hk j (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩)
    have hmid : Tendsto (fun k => msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F)
        atTop (𝓝 0) := msLat_translate_sub_tendsto_pm Wf c ht hs hK1 F hS hcont v
    filter_upwards [hE ι F d hd hcont hsep s hs hsθ, hE ι _ d hd hFv_c hFv_s s hs hsθ,
      (Metric.tendsto_nhds.mp hmid) (η / 2) (half_pos hη)] with k h1 h2 h3
    have h1' : |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf c k s F| ≤ |A1| * (s / d) ^ ε := by
      refine h1.trans ?_
      calc Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
          = A1 * (s / d) ^ ε := by rw [hA1]; ring
        _ ≤ |A1| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have h2' : |latC (NeZero.ne N) (CRen N z μ) k (fun i => translateD v (F i))
        - msLat Wf c k s (fun i => translateD v (F i))| ≤ |A2| * (s / d) ^ ε := by
      refine h2.trans ?_
      calc Kr ^ Fintype.card ι * (s / d) ^ ε
            * ∏ i, ((d ^ κr (translateD v (F i)).1)⁻¹ * l1 (translateD v (F i)).2)
          = A2 * (s / d) ^ ε := by rw [hA2]; ring
        _ ≤ |A2| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have h3' : |msLat Wf c k s (fun i => translateD v (F i)) - msLat Wf c k s F| < η / 2 := by
      rw [Real.dist_eq, sub_zero] at h3
      exact h3
    have hsQ' : (|A1| + |A2|) * (s / d) ^ ε < η / 2 := hsQ
    have hsQ'' : |A1| * (s / d) ^ ε + |A2| * (s / d) ^ ε < η / 2 := by rw [← add_mul]; exact hsQ'
    rw [Real.dist_eq, sub_zero]
    obtain ⟨a1l, a1r⟩ := abs_le.mp h1'
    obtain ⟨a2l, a2r⟩ := abs_le.mp h2'
    obtain ⟨a3l, a3r⟩ := abs_lt.mp h3'
    rw [abs_lt]
    constructor <;> linarith
  have h := (hconv ι F ⟨hcont, d, hd, hsep⟩).add (hΔ.mono_left ultra_le)
  rw [add_zero] at h
  refine h.congr fun k => ?_
  ring

/-! ## 5. The substrate core and the bundle -/

/-- **The substrate core with the per-channel moment input**: `ScalePM.SubstrateCorePM` with `scale`
replaced by `ScaleControlChan b Wf`. DERIVED: no numeral. -/
structure SubstrateCoreCL [NeZero N] (W : ConfFlow N) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) :
    Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale, per channel, by moments, one index per channel. -/
  scale : ScaleControlChan b Wf
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G

/-- `SubstrateCorePM` gives `SubstrateCoreCL`. DERIVED: no numeral. -/
theorem substrateCoreCL_of_corePM [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (S : SubstrateCorePM W z b Wf) : SubstrateCoreCL W z b Wf :=
  ⟨S.b_pos, S.top, scaleControlChan_of_PM S.scale, S.af⟩

/-- **`ClayNarrow.compOS_of_covC` from the per-channel core and the cluster input.** DERIVED: no numeral. -/
theorem compOS_of_covC_cl [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreCL W z b Wf)
    (hE : ExpandStrong Wf cf z μ) (hcl : ClusterPM Wf cf) (hV : CovC (NeZero.ne N) (CRen N z μ))
    (hP : CompNondeg (NeZero.ne N) (CRen N z μ)) : CompOS (NeZero.ne N) (CRen N z μ) :=
  ⟨convC_of_chan S.b_pos S.scale (expandR_of_strong hE),
    os0C_of_cluster (convC_of_chan S.b_pos S.scale (expandR_of_strong hE)) (expandR_of_strong hE) hcl,
    os1C_of_chan S.b_pos S.scale (expandR_of_strong hE), hV, hP⟩

/-- **`ClayNarrow.approxK_of_beyond_covC` from the per-channel core and the cluster input.**
DERIVED: `2` the least colour count; `0` the plane and the reference step. -/
theorem approxK_of_beyond_covC_cl (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreCL W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcl : ClusterPM Wf cf)
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r)
    (hB : ∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_chan S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_covC_cl S hE hcl hV hP
  let D := capData hN2 W hU hphys (CRen N z μ)
    (unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ) (reflCovLat_CRen z μ) hCO
  refine approxK_iff_forall.2 fun P => ?_
  obtain ⟨n, hn⟩ := exists_beyond_iterate (NeZero.ne N) r P
  exact approxKAt_of_iterate D 0 n P (hB _ hn)

/-- **`ClayNarrowMG.inputsAt_of_covC_phys` from the per-channel core and the cluster input.**
DERIVED: `2` the least colour count; `0` the lower end of the scale. -/
theorem inputsAt_of_covC_phys_cl (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {r : ℝ}
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreCL W (ZCanon.zFix N zri zwe) b Wf)
    (hE : ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ) (hcl : ClusterPM Wf cf)
    (hV : CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hW : WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe)))
    (hP : CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ))
    (hphys : (Φ0 W).PhysRange r)
    (hA : ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
      (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r))
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
    (hfar : WDeltaRun.RunSeed N) :
    ∃ (t C : ℝ) (G : ℝ → ℝ), SUNBest.InputsAt hN2 W r t |C| zri zwe μ G := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_chan S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  obtain ⟨G, hK, hAF⟩ := S.af
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨t, C, G,
    { t_pos := ht
      moments := hU
      phys := hphys
      far := hfar
      hri := hri
      hwe := hwe
      kernel := hK
      af := hAF
      low := obsLower_of_scale (ne_zero_of_two_le hN2) hℓ zri zwe h3'
      ward := hW
      comp := compOS_of_covC_cl S hE hcl hV hP
      approx := hA }⟩

/-- **The per-`N` inputs of the cluster route**: `ScalePM.NarrowInputsAtPM` with `SubstrateCorePM`
replaced by `SubstrateCoreCL` (a Gevrey index per channel) and `CoefBound cf` replaced by
`ClusterPM Wf cf`. DERIVED: `2` the least colour count; `0` the plane and the reference step. -/
def NarrowInputsAtCL (N : ℕ) (hN2 : 2 ≤ N) (W : ConfFlow N) (r : ℝ) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  (Φ0 W).PhysRange r ∧
  ∃ (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreCL W (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ ClusterPM Wf cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 W (CRen N (ZCanon.zFix N zri zwe) μ) r) (gramF hN2 W r) P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ RunSeedN.EndpointN N

/-- **`NarrowInputsAtCL` gives the general-`N` bundle at `W`** (`approxK_of_beyond_covC_cl`,
`RunSeedN.runSeed_of_endpointN`, `inputsAt_of_covC_phys_cl`). DERIVED: `2` the least colour count. -/
theorem clayInputsN_of_narrowAtCL (hN2 : 2 ≤ N) {W : ConfFlow N} {r : ℝ}
    (h : NarrowInputsAtCL N hN2 W r) : SUNBest.ClayInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hcl, hV, hW, hP, hB, h3, hEnd⟩ := h
  obtain ⟨t, C, G, I⟩ := inputsAt_of_covC_phys_cl hN2 hri hwe S hE hcl hV hW hP hphys
    (approxK_of_beyond_covC_cl hN2 S hE hcl hV hP hphys hB) h3 (RunSeedN.runSeed_of_endpointN hEnd)
  exact ⟨W, r, t, |C|, zri, zwe, μ, G, I⟩

end MassGap.ClusterRoute

end

#print axioms MassGap.ClusterRoute.cum
#print axioms MassGap.ClusterRoute.cum_of_nonempty
#print axioms MassGap.ClusterRoute.mom_eq_sum_cum
#print axioms MassGap.ClusterRoute.sum_powerset_fact
#print axioms MassGap.ClusterRoute.abs_mom_le_of_cum
#print axioms MassGap.ClusterRoute.tree_count_le
#print axioms MassGap.ClusterRoute.tree_le_fact
#print axioms MassGap.ClusterRoute.stMom_empty
#print axioms MassGap.ClusterRoute.abs_state_prod_le_of_cluster
#print axioms MassGap.ClusterRoute.clusterPM_of_clusterGap
#print axioms MassGap.ClusterRoute.abs_msLat_le_cl
#print axioms MassGap.ClusterRoute.abs_contC_le_cl
#print axioms MassGap.ClusterRoute.os0C_of_cluster
#print axioms MassGap.ClusterRoute.scaleControlChan_of_PM
#print axioms MassGap.ClusterRoute.scaleChanPM_mono_r
#print axioms MassGap.ClusterRoute.ScalePMChan.uniform
#print axioms MassGap.ClusterRoute.uv_of_chan
#print axioms MassGap.ClusterRoute.boundC_ren_of_chan
#print axioms MassGap.ClusterRoute.convC_of_chan
#print axioms MassGap.ClusterRoute.os1C_of_chan
#print axioms MassGap.ClusterRoute.substrateCoreCL_of_corePM
#print axioms MassGap.ClusterRoute.compOS_of_covC_cl
#print axioms MassGap.ClusterRoute.approxK_of_beyond_covC_cl
#print axioms MassGap.ClusterRoute.inputsAt_of_covC_phys_cl
#print axioms MassGap.ClusterRoute.clayInputsN_of_narrowAtCL
