import Mathlib
import MassGap.ClusterRoute

/-!
# MassGap.ClusterPassage — `ClusterPM` from a pointwise cluster bound at separated lattice sites

`ClusterRoute.ClusterPM Wf c` bounds the cumulants of the smeared flowed proxies
`clX = smear a_k (msProx Wf c k s iᵢ) fᵢ`. A smeared field is a finite lattice sum
`∑ₓ a⁴ f(a x) · T_x P`, and the cumulant `ClusterRoute.cum` of the moments of a state is linear in each
factor, so the cumulant of smeared factors is a weighted sum of cumulants of translated factors at lattice
sites. This module proves that passage: a bound on the cumulants at `d`-separated sites with a per-factor
constant gives the same bound on the smeared cumulants with the per-factor constant multiplied by
`wS(a_k, fᵢ)`, which is at most `ClusterPM`'s factor `wS(a_k, fᵢ) + a_k`. Declarations are in the namespace
`MassGap.ClusterPassage`.

## 1. Linearity of the cumulant (proved, general)

* `cum_congr`: `cum m B` reads `m` only on subsets of `B`.
* `cum_linear`: if `m(C) = ∑ₓ wₓ mₓ(C)` on every `C ∋ j` and `mₓ(C) = m(C)` on every `C ∌ j`, then
  `cum m C = ∑ₓ wₓ cum mₓ C` on every `C ∋ j` (strong induction through the recursion `cum_of_nonempty`:
  `j` lies in exactly one of the two sets of each recursion term).
* `cum_stMom_update`: for the moments `stMom ν Y` of a state, `Y_j = ∑ₓ wₓ • Zₓ` gives
  `cum (stMom ν Y) C = ∑ₓ wₓ cum (stMom ν (Y[j ↦ Zₓ])) C` on every `C ∋ j`.
* `abs_cum_le_of_expand`: every factor expanded, `Yᵢ = ∑_{x ∈ Sᵢ} wᵢ(x) • Zᵢ(x)`; a bound
  `|cum (stMom ν (i ↦ Zᵢ(σᵢ))) B| ≤ C_B ∏_{i∈B} Kᵢ(σᵢ)` at every choice `σᵢ ∈ Sᵢ` (`i ∈ B`) gives
  `|cum (stMom ν Y) B| ≤ C_B ∏_{i∈B} ∑_{x ∈ Sᵢ} |wᵢ(x)| Kᵢ(x)` (induction over the set of expanded factors).
  `C_B` is any real attached to `B`: a tree count, a decay factor, or both.

## 2. The pointwise inputs

* `PtSep a d x B`: the lattice sites `xᵢ`, `i ∈ B`, at spacing `a` are pairwise `d`-separated in some
  coordinate, the separation that `ContinuumSep.sepBy` gives for points in the supports.
* `PointGap Wf c m`: one `θc > 0`, `γ ≥ 0`, per composite `Kcᵢ > 0`, `λᵢ`; for every `n`, every assignment of
  composites, `0 < d ≤ 1`, `0 < s ≤ θc d`, eventually in the step, uniformly over the sites,
  `|κ_k(T_{xᵢ} msProxᵢ : i ∈ B)| ≤ γ^{|B|} |B|^{|B|−2} e^{−m d (|B|−1)} ∏_{i∈B} Kcᵢ s^{−λᵢ}` at
  `d`-separated sites. `PointCluster Wf c` is the same without the decay factor; `pointGap_zero_of_pointCluster`.
* `PointGapChanAt Wf m θc γ Kch lamCh`: the same bound for the flowed channels `T_{xᵢ} msFlow_{jᵢ}` with a
  per-channel constant `Kch_j s^{−lamCh_j}`. `CoefCtl c θc Kch lamCh Kc lam`: the expansion coefficients
  obey `∑_j |c_{ij}(s)| Kch_j s^{−lamCh_j} ≤ Kcᵢ s^{−λᵢ}` at `0 < s ≤ θc`.

## 3. The passage

* `clX_eq_sum`, `sum_abs_weight`: the smeared proxy as a sum over the sites where `fᵢ(a x) ≠ 0`, and the sum
  of its absolute weights is `wS(a, fᵢ)`.
* `pointGap_of_chan`: `PointGapChanAt` and `CoefCtl` give `PointGap` (linearity over channels).
* `clusterGap_of_pointGap`: `PointGap Wf c m` gives `ClusterRoute.ClusterGap Wf c m` (linearity over sites).
* **`clusterPM_of_pointCluster`**: `PointCluster Wf c` gives `ClusterRoute.ClusterPM Wf c`.

## 4. What the pointwise inputs ask

The usual tree-graph form is `|κ| ≤ γⁿ ∑_{trees T on B} ∏_{(a,b) ∈ T} w(x_a − x_b) ∏ Kᵢ`. `ClusterPM`'s factor
is `wS(a_k, fᵢ) + a_k`, the lattice `L¹` norm of each test function plus the spacing, so the passage sums every site against its
own test function and reads the edge weight only through its supremum over separated pairs: with
`w(x) ≤ e^{−m|x|}` every edge weight at `d`-separated sites is at most `e^{−m d}`, and the tree sum is at
most `|B|^{|B|−2} e^{−m d (|B|−1)}` by Cayley's count, which is `PointGap`. Summability of `w` is not read:
it would give the sharper `‖f₁‖₁ ∏_{i≥2} ‖fᵢ‖_∞`, which `ClusterPM` does not ask. Cayley's formula is not
formalised here, so the tree sum is stated already bounded, as `PointGap`. The pointwise
bound for the Wilson flowed channels is not proved here.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension and the cell-volume exponent; `2` Cayley's offset; `1` the edge
count offset and the top of the separation; `0` the signs, the empty decay rate and the vanishing weights.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ClusterPassage

open Filter
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.PreObserver MassGap.CompositesBuild MassGap.ClayData MassGap.ReflAvg
  MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll MassGap.MultiScaleOS
  MassGap.ScalePM MassGap.ClusterRoute
open MassGap.ScaleControlFull (zOne)

/-! ## 1. Linearity of the cumulant -/

section Linear

variable {ι : Type*} [LinearOrder ι]

/-- The sets of one recursion term of `cum` on `B`: for `A ⊊ B ∖ {i₀}`, `insert i₀ A ⊊ B`, `i₀ ∉ A`,
`A ⊆ B ∖ {i₀}`. DERIVED: no numeral. -/
theorem rec_sets {B : Finset ι} (hB : B.Nonempty) {A : Finset ι}
    (hA : A ∈ (B.erase (B.min' hB)).powerset.erase (B.erase (B.min' hB))) :
    insert (B.min' hB) A ⊂ B ∧ B.min' hB ∉ A ∧ A ⊆ B.erase (B.min' hB) := by
  have hAE : A ⊆ B.erase (B.min' hB) := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)
  have hAne : A ≠ B.erase (B.min' hB) := Finset.ne_of_mem_erase hA
  have hi0A : B.min' hB ∉ A := fun hm => Finset.notMem_erase (B.min' hB) B (hAE hm)
  have hsub : insert (B.min' hB) A ⊆ B :=
    Finset.insert_subset (Finset.min'_mem B hB) (hAE.trans (Finset.erase_subset _ _))
  refine ⟨Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun heq => hAne ?_⟩, hi0A, hAE⟩
  have h2 : (insert (B.min' hB) A).erase (B.min' hB) = B.erase (B.min' hB) := by rw [heq]
  rwa [Finset.erase_insert hi0A] at h2

/-- DERIVED: `0` the empty value. -/
theorem cum_empty (m : Finset ι → ℝ) : cum m ∅ = 0 := by
  rw [cum, dif_neg Finset.not_nonempty_empty]

/-- **`cum m B` reads `m` only on subsets of `B`.** DERIVED: no numeral. -/
theorem cum_congr {m m' : Finset ι → ℝ} (B : Finset ι) (h : ∀ C ⊆ B, m C = m' C) :
    cum m B = cum m' B := by
  revert h
  induction B using Finset.strongInduction with
  | H B ih =>
    intro h
    rcases B.eq_empty_or_nonempty with rfl | hB
    · rw [cum_empty, cum_empty]
    · rw [cum_of_nonempty m hB, cum_of_nonempty m' hB, h B subset_rfl]
      congr 1
      refine Finset.sum_congr rfl fun A hA => ?_
      obtain ⟨hss, -, -⟩ := rec_sets hB hA
      rw [ih _ hss (fun C hC => h C (hC.trans hss.subset)),
        h (B.erase (B.min' hB) \ A) (Finset.sdiff_subset.trans (Finset.erase_subset _ _))]

/-- **The cumulant is linear in one factor**: if `m(C) = ∑ₓ wₓ mₓ(C)` whenever `j ∈ C` and `mₓ(C) = m(C)`
whenever `j ∉ C`, then `cum m C = ∑ₓ wₓ cum mₓ C` whenever `j ∈ C`. DERIVED: no numeral. -/
theorem cum_linear {α : Type*} (m : Finset ι → ℝ) (mx : α → Finset ι → ℝ) (S : Finset α) (w : α → ℝ)
    (j : ι) (hin : ∀ C : Finset ι, j ∈ C → m C = ∑ x ∈ S, w x * mx x C)
    (hout : ∀ C : Finset ι, j ∉ C → ∀ x ∈ S, mx x C = m C) :
    ∀ C : Finset ι, j ∈ C → cum m C = ∑ x ∈ S, w x * cum (mx x) C := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro hjC
    have hC : C.Nonempty := ⟨j, hjC⟩
    have hR : ∀ x ∈ S, w x * cum (mx x) C
        = w x * mx x C - ∑ A ∈ (C.erase (C.min' hC)).powerset.erase (C.erase (C.min' hC)),
            w x * (cum (mx x) (insert (C.min' hC) A) * mx x (C.erase (C.min' hC) \ A)) := by
      intro x _
      rw [cum_of_nonempty (mx x) hC, mul_sub, Finset.mul_sum]
    rw [Finset.sum_congr rfl hR, Finset.sum_sub_distrib, Finset.sum_comm, ← hin C hjC,
      cum_of_nonempty m hC]
    congr 1
    refine Finset.sum_congr rfl fun A hA => ?_
    obtain ⟨hss, hi0A, -⟩ := rec_sets hC hA
    by_cases hj : j ∈ insert (C.min' hC) A
    · have hjo : j ∉ C.erase (C.min' hC) \ A := by
        intro hm
        rcases Finset.mem_insert.1 hj with h1 | h1
        · rw [h1] at hm
          exact Finset.notMem_erase (C.min' hC) C (Finset.sdiff_subset hm)
        · exact (Finset.mem_sdiff.1 hm).2 h1
      rw [ih _ hss hj, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hout _ hjo x hx]
      ring
    · have hji : j ∈ C.erase (C.min' hC) \ A := by
        refine Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨fun h1 => hj ?_, hjC⟩, fun h1 => hj ?_⟩
        · rw [h1]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem h1
      rw [hin _ hji, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [cum_congr _ (fun D hD => hout D (fun hjD => hj (hD hjD)) x hx)]
      ring

/-- **The cumulant of a state's moments is linear in one factor**: `Y_j = ∑ₓ wₓ • Zₓ` gives
`cum (stMom ν Y) C = ∑ₓ wₓ cum (stMom ν (Y[j ↦ Zₓ])) C` whenever `j ∈ C`. DERIVED: no numeral. -/
theorem cum_stMom_update {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) (Y : ι → C(X, ℝ)) (j : ι) {α : Type*} (S : Finset α) (w : α → ℝ)
    (Z : α → C(X, ℝ)) (hY : Y j = ∑ x ∈ S, w x • Z x) :
    ∀ C : Finset ι, j ∈ C →
      cum (stMom ν Y) C = ∑ x ∈ S, w x * cum (stMom ν (Function.update Y j (Z x))) C := by
  refine cum_linear _ _ S w j (fun C hjC => ?_) (fun C hjC x _ => ?_)
  · have hu : ∀ x, stMom ν (Function.update Y j (Z x)) C = ν (Z x * ∏ i ∈ C.erase j, Y i) := by
      intro x
      have hp : ∏ i ∈ C.erase j, Function.update Y j (Z x) i = ∏ i ∈ C.erase j, Y i :=
        Finset.prod_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
      rw [stMom, ← Finset.mul_prod_erase C _ hjC, Function.update_self, hp]
    rw [stMom, ← Finset.mul_prod_erase C _ hjC, hY, Finset.sum_mul, ν.map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hu, smul_mul_assoc, ν.map_smul]
  · have hp : ∏ i ∈ C, Function.update Y j (Z x) i = ∏ i ∈ C, Y i :=
      Finset.prod_congr rfl fun i hi => Function.update_of_ne (fun h : i = j => hjC (h ▸ hi)) _ _
    rw [stMom, stMom, hp]

/-- **Every factor expanded**: `Yᵢ = ∑_{x ∈ Sᵢ} wᵢ(x) • Zᵢ(x)` and a bound
`|cum (stMom ν (i ↦ Zᵢ(σᵢ))) B| ≤ C_B ∏_{i∈B} Kᵢ(σᵢ)` at every choice with `σᵢ ∈ Sᵢ` for `i ∈ B` give
`|cum (stMom ν Y) B| ≤ C_B ∏_{i∈B} ∑_{x∈Sᵢ} |wᵢ(x)| Kᵢ(x)`. DERIVED: no numeral. -/
theorem abs_cum_le_of_expand {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) [Fintype ι] {α : Type*} [Nonempty α] (Y : ι → C(X, ℝ))
    (S : ι → Finset α) (w : ι → α → ℝ) (Z : ι → α → C(X, ℝ))
    (hY : ∀ i, Y i = ∑ x ∈ S i, w i x • Z i x) (K : ι → α → ℝ) (B : Finset ι) (Cb : ℝ)
    (hpt : ∀ σ : ι → α, (∀ i ∈ B, σ i ∈ S i) →
      |cum (stMom ν (fun i => Z i (σ i))) B| ≤ Cb * ∏ i ∈ B, K i (σ i)) :
    |cum (stMom ν Y) B| ≤ Cb * ∏ i ∈ B, ∑ x ∈ S i, |w i x| * K i x := by
  have key : ∀ J : Finset ι, ∀ σ : ι → α, (∀ i ∈ B, i ∉ J → σ i ∈ S i) →
      |cum (stMom ν (fun i => if i ∈ J then Y i else Z i (σ i))) B|
        ≤ Cb * ∏ i ∈ B, (if i ∈ J then ∑ x ∈ S i, |w i x| * K i x else K i (σ i)) := by
    intro J
    induction J using Finset.induction with
    | empty =>
      intro σ hσ
      simp only [Finset.notMem_empty, ↓reduceIte]
      exact hpt σ fun i hi => hσ i hi (Finset.notMem_empty i)
    | insert j J hjJ ih =>
      intro σ hσ
      by_cases hjB : j ∈ B
      · have hMj : (fun i => if i ∈ insert j J then Y i else Z i (σ i)) j
            = ∑ x ∈ S j, w j x • Z j x := by
          simp only [Finset.mem_insert_self, ↓reduceIte]
          exact hY j
        have hupd : ∀ x, Function.update (fun i => if i ∈ insert j J then Y i else Z i (σ i)) j (Z j x)
            = fun i => if i ∈ J then Y i else Z i (Function.update σ j x i) := by
          intro x
          funext i
          by_cases hij : i = j
          · subst hij
            rw [Function.update_self, if_neg hjJ, Function.update_self]
          · rw [Function.update_of_ne hij, Function.update_of_ne hij]
            simp only [Finset.mem_insert, hij, false_or]
        rw [cum_stMom_update ν (fun i => if i ∈ insert j J then Y i else Z i (σ i)) j (S j) (w j)
          (Z j) hMj B hjB]
        have hb : ∀ x ∈ S j, |w j x * cum (stMom ν
              (Function.update (fun i => if i ∈ insert j J then Y i else Z i (σ i)) j (Z j x))) B|
            ≤ |w j x| * K j x * (Cb * ∏ i ∈ B.erase j,
                (if i ∈ insert j J then ∑ x ∈ S i, |w i x| * K i x else K i (σ i))) := by
          intro x hx
          rw [hupd, abs_mul]
          have h1 := ih (Function.update σ j x) (fun i hi hiJ => by
            by_cases hij : i = j
            · subst hij; rw [Function.update_self]; exact hx
            · rw [Function.update_of_ne hij]
              exact hσ i hi (fun hm => (Finset.mem_insert.1 hm).elim hij hiJ))
          have hP : ∏ i ∈ B, (if i ∈ J then ∑ x ∈ S i, |w i x| * K i x
                else K i (Function.update σ j x i))
              = K j x * ∏ i ∈ B.erase j,
                (if i ∈ insert j J then ∑ x ∈ S i, |w i x| * K i x else K i (σ i)) := by
            rw [← Finset.mul_prod_erase B _ hjB, if_neg hjJ, Function.update_self]
            congr 1
            refine Finset.prod_congr rfl fun i hi => ?_
            have hij := Finset.ne_of_mem_erase hi
            rw [Function.update_of_ne hij]
            simp only [Finset.mem_insert, hij, false_or]
          rw [hP] at h1
          calc |w j x| * |cum (stMom ν (fun i => if i ∈ J then Y i
                  else Z i (Function.update σ j x i))) B|
              ≤ |w j x| * (Cb * (K j x * ∏ i ∈ B.erase j,
                  (if i ∈ insert j J then ∑ x ∈ S i, |w i x| * K i x else K i (σ i)))) :=
                mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
            _ = |w j x| * K j x * (Cb * ∏ i ∈ B.erase j,
                  (if i ∈ insert j J then ∑ x ∈ S i, |w i x| * K i x else K i (σ i))) := by ring
        refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hb).trans (le_of_eq ?_))
        rw [← Finset.sum_mul, ← Finset.mul_prod_erase B _ hjB, if_pos (Finset.mem_insert_self _ _)]
        ring
      · have hC : cum (stMom ν (fun i => if i ∈ insert j J then Y i else Z i (σ i))) B
            = cum (stMom ν (fun i => if i ∈ J then Y i else Z i (σ i))) B := by
          refine cum_congr B fun C hC => ?_
          rw [stMom, stMom]
          congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          have hij : i ≠ j := fun h => hjB (h ▸ hC hi)
          simp only [Finset.mem_insert, hij, false_or]
        have hP : ∏ i ∈ B, (if i ∈ insert j J then ∑ x ∈ S i, |w i x| * K i x else K i (σ i))
            = ∏ i ∈ B, (if i ∈ J then ∑ x ∈ S i, |w i x| * K i x else K i (σ i)) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hij : i ≠ j := fun h => hjB (h ▸ hi)
          simp only [Finset.mem_insert, hij, false_or]
        rw [hC, hP]
        refine ih σ fun i hi hiJ => hσ i hi fun hm => (Finset.mem_insert.1 hm).elim
          (fun h => hjB (h ▸ hi)) hiJ
  have h := key Finset.univ (fun _ => Classical.arbitrary α) (fun i _ hi => (hi (Finset.mem_univ i)).elim)
  simp only [Finset.mem_univ, ↓reduceIte] at h
  exact h

end Linear

/-! ## 2. The pointwise inputs -/

variable {N : ℕ}

/-- **Separated lattice sites**: at spacing `a`, the sites `xᵢ`, `i ∈ B`, are pairwise at distance at least
`d` in some coordinate. DERIVED: `4` the dimension. -/
def PtSep (a d : ℝ) {n : ℕ} (x : Fin n → ISite) (B : Finset (Fin n)) : Prop :=
  ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∃ μ : Fin 4, d ≤ |site a (x i) μ - site a (x j) μ|

/-- **The pointwise cluster input with the decay explicit**: the cumulants of the translated flowed proxies
at `d`-separated lattice sites obey
`|κ_k(T_{xᵢ} msProxᵢ : i ∈ B)| ≤ γ^{|B|} |B|^{|B|−2} e^{−m d (|B|−1)} ∏_{i∈B} Kcᵢ s^{−λᵢ}`, eventually in
the step, uniformly over the sites. DERIVED: `2` Cayley's offset; `1` the edge count offset and the top of
the separation; `0` the signs. -/
def PointGap [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (m : ℝ) : Prop :=
  ∃ (θc γ : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 ≤ γ ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (ix : Fin n → Ix0) (d : ℝ), 0 < d → d ≤ 1 → ∀ s : ℝ, 0 < s → s ≤ θc * d →
      ∀ᶠ k in atTop, ∀ (x : Fin n → ISite) (B : Finset (Fin n)), B.Nonempty →
        PtSep (dySpacing N k) d x B →
        |cum (stMom (stateK (NeZero.ne N) k)
            (fun i => transObs (x i) (msProx Wf c k s (ix i)))) B|
          ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * Real.exp (-(m * d * ((B.card : ℝ) - 1)))
            * ∏ i ∈ B, (Kc (ix i) * s⁻¹ ^ lam (ix i))

/-- **The pointwise cluster input**: `PointGap` without the decay factor. DERIVED: `2` Cayley's offset; `1`
the top of the separation; `0` the signs. -/
def PointCluster [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ (θc γ : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 ≤ γ ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (ix : Fin n → Ix0) (d : ℝ), 0 < d → d ≤ 1 → ∀ s : ℝ, 0 < s → s ≤ θc * d →
      ∀ᶠ k in atTop, ∀ (x : Fin n → ISite) (B : Finset (Fin n)), B.Nonempty →
        PtSep (dySpacing N k) d x B →
        |cum (stMom (stateK (NeZero.ne N) k)
            (fun i => transObs (x i) (msProx Wf c k s (ix i)))) B|
          ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * ∏ i ∈ B, (Kc (ix i) * s⁻¹ ^ lam (ix i))

/-- `PointCluster` is `PointGap` at rate `0`. DERIVED: `0` the rate. -/
theorem pointGap_zero_of_pointCluster [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : PointCluster Wf c) : PointGap Wf c 0 := by
  obtain ⟨θc, γ, Kc, lam, hθc, hγ, hKc, H⟩ := h
  refine ⟨θc, γ, Kc, lam, hθc, hγ, hKc, fun n ix d hd hd1 s hs hsd => ?_⟩
  filter_upwards [H n ix d hd hd1 s hs hsd] with k hk x B hB hsep
  rw [zero_mul, zero_mul, neg_zero, Real.exp_zero, mul_one]
  exact hk x B hB hsep

/-- **The pointwise input on the flowed channels**, at given constants: the cumulants of the translated
connected flowed channels `T_{xᵢ} msFlow_{jᵢ}` at `d`-separated sites obey
`γ^{|B|} |B|^{|B|−2} e^{−m d (|B|−1)} ∏_{i∈B} Kch_{jᵢ} s^{−lamCh_{jᵢ}}`. DERIVED: `2` Cayley's offset;
`1` the edge count offset and the top of the separation; `0` the signs. -/
def PointGapChanAt [NeZero N] (Wf : ℝ → ConfFlow N) (m θc γ : ℝ) (Kch lamCh : MIx → ℝ) : Prop :=
  ∀ (n : ℕ) (d : ℝ), 0 < d → d ≤ 1 → ∀ s : ℝ, 0 < s → s ≤ θc * d →
    ∀ᶠ k in atTop, ∀ (x : Fin n → ISite) (jx : Fin n → MIx) (B : Finset (Fin n)), B.Nonempty →
      PtSep (dySpacing N k) d x B →
      |cum (stMom (stateK (NeZero.ne N) k) (fun i => transObs (x i) (msFlow Wf k s (jx i)))) B|
        ≤ γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * Real.exp (-(m * d * ((B.card : ℝ) - 1)))
          * ∏ i ∈ B, (Kch (jx i) * s⁻¹ ^ lamCh (jx i))

/-- **The expansion coefficients against the channel constants**: at `0 < s ≤ θc`,
`∑_j |c_{ij}(s)| Kch_j s^{−lamCh_j} ≤ Kcᵢ s^{−λᵢ}`. DERIVED: `0` the lower end of the scale. -/
def CoefCtl (c : Ix0 → ℝ → (MIx →₀ ℝ)) (θc : ℝ) (Kch lamCh : MIx → ℝ) (Kc lam : Ix0 → ℝ) : Prop :=
  ∀ (i : Ix0) (s : ℝ), 0 < s → s ≤ θc →
    ∑ j ∈ (c i s).support, |c i s j| * (Kch j * s⁻¹ ^ lamCh j) ≤ Kc i * s⁻¹ ^ lam i

/-! ## 3. The passage -/

/-- The translated proxy as a sum over channels. DERIVED: no numeral. -/
theorem transObs_msProx [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (i : Ix0) (x : ISite) :
    transObs x (msProx Wf c k s i) = ∑ j ∈ (c i s).support, c i s j • transObs x (msFlow Wf k s j) := by
  rw [msProx, map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul _ _ _

/-- **Channels to proxies**: `PointGapChanAt` and `CoefCtl` give `PointGap`. DERIVED: `0` the signs; `1`
the top of the separation. -/
theorem pointGap_of_chan [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {m θc γ : ℝ}
    {Kch lamCh : MIx → ℝ} {Kc lam : Ix0 → ℝ} (hθc : 0 < θc) (hγ : 0 ≤ γ) (hKch : ∀ j, 0 ≤ Kch j)
    (hKc : ∀ i, 0 < Kc i) (hctl : CoefCtl c θc Kch lamCh Kc lam)
    (hpt : PointGapChanAt Wf m θc γ Kch lamCh) : PointGap Wf c m := by
  haveI : Nonempty MIx := ⟨Sum.inr ((0, 0), 0)⟩
  refine ⟨θc, γ, Kc, lam, hθc, hγ, hKc, fun n ix d hd hd1 s hs hsd => ?_⟩
  have hsθ : s ≤ θc := hsd.trans (mul_le_of_le_one_right hθc.le hd1)
  filter_upwards [hpt n d hd hd1 s hs hsd] with k hk x B hB hsep
  set Cb : ℝ := γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * Real.exp (-(m * d * ((B.card : ℝ) - 1)))
  have hCb : 0 ≤ Cb := mul_nonneg (mul_nonneg (pow_nonneg hγ _) (pow_nonneg (Nat.cast_nonneg _) _))
    (Real.exp_pos _).le
  have h := abs_cum_le_of_expand (stateK (NeZero.ne N) k)
    (fun i => transObs (x i) (msProx Wf c k s (ix i))) (fun i => (c (ix i) s).support)
    (fun i j => c (ix i) s j) (fun i j => transObs (x i) (msFlow Wf k s j))
    (fun i => transObs_msProx Wf c k s (ix i) (x i)) (fun _ j => Kch j * s⁻¹ ^ lamCh j) B Cb
    (fun σ _ => hk x σ B hB hsep)
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.prod_le_prod
    (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg (hKch j) (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _)))
    (fun i _ => hctl (ix i) s hs hsθ)) hCb)

/-- **The sites where a test function is non-zero**, inside its box at spacing `a`.
DERIVED: `0` the vanishing value. -/
def supSites (a : ℝ) (f : TestFn) : Finset ISite :=
  (box ⌈tR f / a⌉₊).filter fun x => f.1 (site a x) ≠ 0

/-- **The smeared proxy as a sum over the support sites**:
`clXᵢ = ∑_{x ∈ supSites a fᵢ} (a⁴ fᵢ(a x)) • T_x msProxᵢ`. DERIVED: `4` the cell-volume exponent; `0` the
vanishing weights. -/
theorem clX_eq_sum [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) {n : ℕ}
    (F : Fin n → CDatum (CbR N zOne)) (i : Fin n) :
    clX Wf c k s F i = ∑ x ∈ supSites (dySpacing N k) (F i).2,
      (dySpacing N k ^ 4 * (F i).2.1 (site (dySpacing N k) x))
        • transObs x (msProx Wf c k s (F i).1) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  rw [clX, smear_eq_sum ha _ _ (tIs (F i).2) subset_rfl, supSites, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not] at h
    rw [h, mul_zero, zero_smul]

/-- **The absolute weights sum to `wS`**: `∑_{x ∈ supSites a f} |a⁴ f(a x)| · K = wS(a, f) · K`.
DERIVED: `4` the cell-volume exponent; `0` the vanishing weights. -/
theorem sum_abs_weight {a : ℝ} (ha : 0 < a) (f : TestFn) (K : ℝ) :
    ∑ x ∈ supSites a f, |a ^ 4 * f.1 (site a x)| * K = wS a f * K := by
  rw [wS, Finset.sum_mul, supSites]
  rw [Finset.sum_filter_of_ne (p := fun x => f.1 (site a x) ≠ 0)
    fun x _ hx h0 => hx (by rw [h0, mul_zero, abs_zero, zero_mul])]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [abs_mul, abs_of_nonneg (pow_nonneg ha.le 4)]

/-- **Sites to smeared factors**: `PointGap Wf c m` gives `ClusterRoute.ClusterGap Wf c m`.
DERIVED: `4` the cell-volume exponent; `0` the signs. -/
theorem clusterGap_of_pointGap [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {m : ℝ}
    (h : PointGap Wf c m) : ClusterGap Wf c m := by
  obtain ⟨θc, γ, Kc, lam, hθc, hγ, hKc, H⟩ := h
  refine ⟨θc, γ, Kc, lam, hθc, hγ, hKc, fun n F d hd hd1 _ hsep s hs hsd => ?_⟩
  filter_upwards [H n (fun i => (F i).1) d hd hd1 s hs hsd] with k hk B hB
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  set Cb : ℝ := γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * Real.exp (-(m * d * ((B.card : ℝ) - 1)))
  have hCb : 0 ≤ Cb := mul_nonneg (mul_nonneg (pow_nonneg hγ _) (pow_nonneg (Nat.cast_nonneg _) _))
    (Real.exp_pos _).le
  have hK0 : ∀ i : Fin n, 0 ≤ Kc (F i).1 * s⁻¹ ^ lam (F i).1 := fun i =>
    mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _)
  have h := abs_cum_le_of_expand (stateK (NeZero.ne N) k) (clX Wf c k s F)
    (fun i => supSites (dySpacing N k) (F i).2)
    (fun i x => dySpacing N k ^ 4 * (F i).2.1 (site (dySpacing N k) x))
    (fun i x => transObs x (msProx Wf c k s (F i).1)) (clX_eq_sum Wf c k s F)
    (fun i _ => Kc (F i).1 * s⁻¹ ^ lam (F i).1) B Cb (fun σ hσ => hk σ B hB (by
      intro i hi j hj hij
      have hi' := (Finset.mem_filter.1 (hσ i hi)).2
      have hj' := (Finset.mem_filter.1 (hσ j hj)).2
      exact hsep i j hij _ _ hi' hj'))
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun x _ =>
    mul_nonneg (abs_nonneg _) (hK0 i)) (fun i _ => ?_)) hCb
  rw [sum_abs_weight ha]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha.le) (hK0 i)

/-- **`ClusterPM` from the pointwise cluster input** (`pointGap_zero_of_pointCluster`,
`clusterGap_of_pointGap`, `ClusterRoute.clusterPM_of_clusterGap`). DERIVED: `0` the rate. -/
theorem clusterPM_of_pointCluster [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : PointCluster Wf c) : ClusterPM Wf c :=
  clusterPM_of_clusterGap le_rfl (clusterGap_of_pointGap (pointGap_zero_of_pointCluster h))

/-- **`ClusterPM` from the channel input**: `PointGapChanAt` at a rate `m ≥ 0` and `CoefCtl`.
DERIVED: `0` the signs. -/
theorem clusterPM_of_chan [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {m θc γ : ℝ}
    {Kch lamCh : MIx → ℝ} {Kc lam : Ix0 → ℝ} (hm : 0 ≤ m) (hθc : 0 < θc) (hγ : 0 ≤ γ)
    (hKch : ∀ j, 0 ≤ Kch j) (hKc : ∀ i, 0 < Kc i) (hctl : CoefCtl c θc Kch lamCh Kc lam)
    (hpt : PointGapChanAt Wf m θc γ Kch lamCh) : ClusterPM Wf c :=
  clusterPM_of_clusterGap hm (clusterGap_of_pointGap (pointGap_of_chan hθc hγ hKch hKc hctl hpt))

end MassGap.ClusterPassage

#print axioms MassGap.ClusterPassage.cum_congr
#print axioms MassGap.ClusterPassage.cum_linear
#print axioms MassGap.ClusterPassage.cum_stMom_update
#print axioms MassGap.ClusterPassage.abs_cum_le_of_expand
#print axioms MassGap.ClusterPassage.pointGap_zero_of_pointCluster
#print axioms MassGap.ClusterPassage.pointGap_of_chan
#print axioms MassGap.ClusterPassage.clX_eq_sum
#print axioms MassGap.ClusterPassage.sum_abs_weight
#print axioms MassGap.ClusterPassage.clusterGap_of_pointGap
#print axioms MassGap.ClusterPassage.clusterPM_of_pointCluster
#print axioms MassGap.ClusterPassage.clusterPM_of_chan
