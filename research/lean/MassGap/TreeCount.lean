import Mathlib
import MassGap.ClusterPassage

/-!
# MassGap.TreeCount — the tree-graph cluster bound and its reduction to `PointGap`

`ClusterPassage.PointGap Wf c m` states the cumulant bound at separated lattice sites with the tree sum already
bounded, `γ^{|B|} |B|^{|B|−2} e^{−m d (|B|−1)}`. This module states the tree-graph form itself, with an
explicit sum over the spanning trees of `B` and an edge weight `w`, and proves that it gives `PointGap`.
Declarations are in the namespace `MassGap.TreeCount`.

## 1. Trees on a finite set (general)

* `IsTreeOn B E`: `E` is a spanning tree of the finite set `B`: its edges are unordered pairs of distinct
  points of `B`, there are `|B| − 1` of them, and the graph they span joins every two points of `B`.
* `treeSet B`: the finite set of spanning trees of `B`; `mem_treeSet`.
* `card_treeSet_le`: `#treeSet B ≤ C(|B.sym2|, |B| − 1)`, since a tree is an `(|B| − 1)`-subset of the pairs.
  `card_sym2_le`: `|B.sym2| ≤ |B|²`.
* `sq_pow_le`: `(n²)^{n−1} ≤ (2e)ⁿ n^{n−2} (n − 1)!` for `n ≥ 1` (from `nⁿ ≤ eⁿ n!` and `n ≤ 2ⁿ`).
* **`card_treeSet_le_real`**: `#treeSet B ≤ (2e)^{|B|} |B|^{|B|−2}` for non-empty `B`. Cayley's exact count
  `n^{n−2}` is not used: the crude count by edge subsets carries the extra `(2e)ⁿ`, which the constant `γ`
  absorbs.

## 2. The tree sum at lattice sites

* `edgeW w a x`: the weight of the edge `{i, j}`, `i ≤ j`, of a tree on sites `x` at spacing `a` is
  `w(a xᵢ − a xⱼ)`.
* `treeSum w a x B = ∑_{T ∈ treeSet B} ∏_{e ∈ T} edgeW w a x e`.
* `edgeW_le`: with `0 ≤ m` and `w(v) ≤ e^{−m‖v‖}` (`‖·‖` the sup norm on `ℝ⁴`), an edge between sites that
  are `d`-apart in some coordinate has weight at most `e^{−m d}`.
* **`treeSum_le`**: at `d`-separated sites (`ClusterPassage.PtSep`) with `0 ≤ w`,
  `treeSum ≤ (2e)^{|B|} |B|^{|B|−2} e^{−m d (|B|−1)}`.

## 3. The tree-graph input and its reduction

* `TreeGap Wf c m w`: `0 ≤ w ≤ e^{−m‖·‖}`, and one `θc > 0`, `γ ≥ 0`, per composite `Kcᵢ > 0`, `λᵢ`; for
  every `n`, every assignment of composites, `0 < d ≤ 1`, `0 < s ≤ θc d`, eventually in the step, uniformly
  over the sites,
  `|κ_k(T_{xᵢ} msProxᵢ : i ∈ B)| ≤ γ^{|B|} ∑_{T tree on B} ∏_{{i,j} ∈ T} w(a xᵢ − a xⱼ) ∏_{i∈B} Kcᵢ s^{−λᵢ}` at
  `d`-separated sites.
* **`pointGap_of_treeGap`**: `0 ≤ m` and `TreeGap Wf c m w` give `ClusterPassage.PointGap Wf c m` with the
  constant `2eγ`. `clusterGap_of_treeGap`, `clusterPM_of_treeGap` follow through `ClusterPassage`.

The edge weight is read only through its supremum over separated pairs. The tree-graph bound for the Wilson
flowed proxies is not proved here.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension; `2` Cayley's offset, the square of the pair count and the base of
`n ≤ 2ⁿ`; `1` the edge-count offset, the least set size, the top of the separation and `e = exp 1`; `0` the
signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TreeCount

open Filter
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.PreObserver MassGap.CompositesBuild MassGap.ClayData MassGap.ReflAvg
  MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll MassGap.MultiScaleOS
  MassGap.ScalePM MassGap.ClusterRoute MassGap.ClusterPassage

/-! ## 1. Trees on a finite set -/

section Trees

variable {ι : Type*}

/-- **A spanning tree of `B`**: the edges are unordered pairs of distinct points of `B`, there are
`|B| − 1` of them, and the graph they span joins every two points of `B`. DERIVED: `1` the edge-count
offset. -/
def IsTreeOn (B : Finset ι) (E : Finset (Sym2 ι)) : Prop :=
  E ⊆ B.sym2 ∧ (∀ e ∈ E, ¬ e.IsDiag) ∧ E.card + 1 = B.card ∧
    ∀ i ∈ B, ∀ j ∈ B, (SimpleGraph.fromEdgeSet (E : Set (Sym2 ι))).Reachable i j

/-- **The spanning trees of `B`**, as edge sets. DERIVED: no numeral. -/
def treeSet (B : Finset ι) : Finset (Finset (Sym2 ι)) := by
  classical exact B.sym2.powerset.filter (IsTreeOn B)

/-- DERIVED: no numeral. -/
theorem mem_treeSet {B : Finset ι} {E : Finset (Sym2 ι)} : E ∈ treeSet B ↔ IsTreeOn B E := by
  classical
  rw [treeSet, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- **A tree is an `(|B| − 1)`-subset of the pairs**: `#treeSet B ≤ C(|B.sym2|, |B| − 1)`.
DERIVED: `1` the edge-count offset. -/
theorem card_treeSet_le (B : Finset ι) : (treeSet B).card ≤ (B.sym2.card).choose (B.card - 1) := by
  calc (treeSet B).card ≤ (B.sym2.powersetCard (B.card - 1)).card := by
        refine Finset.card_le_card fun E hE => ?_
        obtain ⟨h1, -, h3, -⟩ := mem_treeSet.1 hE
        exact Finset.mem_powersetCard.2 ⟨h1, by omega⟩
    _ = (B.sym2.card).choose (B.card - 1) := Finset.card_powersetCard _ _

/-- **The pair count**: `|B.sym2| = C(|B| + 1, 2) ≤ |B|²`. DERIVED: `2` the pair size; `1` the diagonal. -/
theorem card_sym2_le (B : Finset ι) : B.sym2.card ≤ B.card * B.card := by
  rw [Finset.card_sym2, Nat.choose_two_right, Nat.add_sub_cancel]
  exact Nat.div_le_of_le_mul (by nlinarith)

end Trees

/-- **The crude count against Cayley's**: `(n²)^{n−1} ≤ (2e)ⁿ n^{n−2} (n − 1)!` for `n ≥ 1`, from
`nⁿ ≤ eⁿ n!` and `n ≤ 2ⁿ`. DERIVED: `2` the square, Cayley's offset and the base of `n ≤ 2ⁿ`; `1` the least
size and `e = exp 1`. -/
theorem sq_pow_le (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) ^ 2) ^ (n - 1) ≤ (2 * Real.exp 1) ^ n * (n : ℝ) ^ (n - 2) * ((n - 1).factorial : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn0.le n
  rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n)] at h1
  have hexp : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have hfac : (n.factorial : ℝ) = n * ((n - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred (by omega : n ≠ 0)]
    push_cast
    ring
  have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hsplit : ((n : ℝ) ^ 2) ^ (n - 1) = (n : ℝ) ^ (n - 2) * (n : ℝ) ^ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      norm_num
    · rw [← pow_mul, ← pow_add]
      congr 1
      omega
  have hF : (0 : ℝ) ≤ ((n - 1).factorial : ℝ) := Nat.cast_nonneg _
  have hnn : (n : ℝ) ^ n ≤ (2 * Real.exp 1) ^ n * ((n - 1).factorial : ℝ) := by
    calc (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := h1
      _ = Real.exp 1 ^ n * ((n : ℝ) * ((n - 1).factorial : ℝ)) := by rw [hexp, hfac]
      _ ≤ Real.exp 1 ^ n * (2 ^ n * ((n - 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hF) (pow_nonneg (Real.exp_pos 1).le _)
      _ = (2 * Real.exp 1) ^ n * ((n - 1).factorial : ℝ) := by rw [mul_pow]; ring
  rw [hsplit]
  calc (n : ℝ) ^ (n - 2) * (n : ℝ) ^ n
      ≤ (n : ℝ) ^ (n - 2) * ((2 * Real.exp 1) ^ n * ((n - 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hnn (pow_nonneg hn0.le _)
    _ = (2 * Real.exp 1) ^ n * (n : ℝ) ^ (n - 2) * ((n - 1).factorial : ℝ) := by ring

/-- **The tree count**: `#treeSet B ≤ (2e)^{|B|} |B|^{|B|−2}` for non-empty `B`. DERIVED: `2` Cayley's offset
and the base; `1` the edge-count offset and `e = exp 1`. -/
theorem card_treeSet_le_real {ι : Type*} (B : Finset ι) (hB : B.Nonempty) :
    ((treeSet B).card : ℝ) ≤ (2 * Real.exp 1) ^ B.card * (B.card : ℝ) ^ (B.card - 2) := by
  have hn : 1 ≤ B.card := hB.card_pos
  have hf : (0 : ℝ) < ((B.card - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h1 : ((treeSet B).card : ℝ) ≤ ((B.sym2.card.choose (B.card - 1) : ℕ) : ℝ) := by
    exact_mod_cast card_treeSet_le B
  have h2 := Nat.choose_le_pow_div (α := ℝ) (B.card - 1) B.sym2.card
  have hsq : (B.sym2.card : ℝ) ≤ (B.card : ℝ) ^ 2 := by
    rw [sq]
    exact_mod_cast card_sym2_le B
  have h3 : (B.sym2.card : ℝ) ^ (B.card - 1) ≤ ((B.card : ℝ) ^ 2) ^ (B.card - 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hsq _
  calc ((treeSet B).card : ℝ)
      ≤ (B.sym2.card : ℝ) ^ (B.card - 1) / ((B.card - 1).factorial : ℝ) := h1.trans h2
    _ ≤ ((B.card : ℝ) ^ 2) ^ (B.card - 1) / ((B.card - 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right h3 hf.le
    _ ≤ (2 * Real.exp 1) ^ B.card * (B.card : ℝ) ^ (B.card - 2) := by
        rw [div_le_iff₀ hf]
        exact sq_pow_le B.card hn

/-! ## 2. The tree sum at lattice sites -/

/-- **The edge weight**: the edge `{i, j}`, `i ≤ j`, of a tree on the sites `x` at spacing `a` weighs
`w(a xᵢ − a xⱼ)`. DERIVED: `4` the dimension. -/
def edgeW (w : (Fin 4 → ℝ) → ℝ) (a : ℝ) {n : ℕ} (x : Fin n → ISite) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => if i ≤ j then w (site a (x i) - site a (x j)) else w (site a (x j) - site a (x i)),
    fun i j => by
      rcases le_total i j with h | h
      · rcases eq_or_lt_of_le h with rfl | hlt
        · rfl
        · dsimp only
          rw [if_pos h, if_neg (not_le.2 hlt)]
      · rcases eq_or_lt_of_le h with rfl | hlt
        · rfl
        · dsimp only
          rw [if_neg (not_le.2 hlt), if_pos h]⟩

/-- **The tree sum**: `∑_{T ∈ treeSet B} ∏_{e ∈ T} edgeW w a x e`. DERIVED: `4` the dimension. -/
def treeSum (w : (Fin 4 → ℝ) → ℝ) (a : ℝ) {n : ℕ} (x : Fin n → ISite) (B : Finset (Fin n)) : ℝ :=
  ∑ T ∈ treeSet B, ∏ e ∈ T, edgeW w a x e

/-- DERIVED: `4` the dimension; `0` the sign. -/
theorem edgeW_nonneg {w : (Fin 4 → ℝ) → ℝ} (hw0 : ∀ v, 0 ≤ w v) (a : ℝ) {n : ℕ} (x : Fin n → ISite)
    (e : Sym2 (Fin n)) : 0 ≤ edgeW w a x e := by
  refine Sym2.ind (f := fun e => 0 ≤ edgeW w a x e) (fun i j => ?_) e
  rw [edgeW, Sym2.lift_mk]
  dsimp only
  split_ifs
  · exact hw0 _
  · exact hw0 _

/-- **An edge between separated sites**: with `0 ≤ m` and `w(v) ≤ e^{−m‖v‖}`, sites `d`-apart in some
coordinate give `edgeW ≤ e^{−m d}`. DERIVED: `4` the dimension; `0` the sign of the rate. -/
theorem edgeW_le {w : (Fin 4 → ℝ) → ℝ} {m d a : ℝ} (hm : 0 ≤ m)
    (hw : ∀ v, w v ≤ Real.exp (-(m * ‖v‖))) {n : ℕ} (x : Fin n → ISite) (i j : Fin n) (μ : Fin 4)
    (hμ : d ≤ |site a (x i) μ - site a (x j) μ|) : edgeW w a x s(i, j) ≤ Real.exp (-(m * d)) := by
  have hd : d ≤ ‖site a (x i) - site a (x j)‖ := by
    refine hμ.trans ?_
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (site a (x i) - site a (x j)) μ
  have key : ∀ v, d ≤ ‖v‖ → w v ≤ Real.exp (-(m * d)) := fun v hv =>
    (hw v).trans (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hv hm)))
  rw [edgeW, Sym2.lift_mk]
  dsimp only
  split_ifs
  · exact key _ hd
  · exact key _ (by rwa [norm_sub_rev])

/-- **The tree sum at separated sites**: `0 ≤ m`, `0 ≤ w ≤ e^{−m‖·‖}` and `d`-separated sites give
`treeSum ≤ (2e)^{|B|} |B|^{|B|−2} e^{−m d (|B|−1)}`. DERIVED: `2` Cayley's offset and the base; `1` the
edge-count offset and `e = exp 1`. -/
theorem treeSum_le {w : (Fin 4 → ℝ) → ℝ} {m d a : ℝ} (hm : 0 ≤ m) (hw0 : ∀ v, 0 ≤ w v)
    (hw : ∀ v, w v ≤ Real.exp (-(m * ‖v‖))) {n : ℕ} (x : Fin n → ISite) (B : Finset (Fin n))
    (hB : B.Nonempty) (hsep : PtSep a d x B) :
    treeSum w a x B ≤ (2 * Real.exp 1) ^ B.card * (B.card : ℝ) ^ (B.card - 2)
      * Real.exp (-(m * d * ((B.card : ℝ) - 1))) := by
  have hT : ∀ T ∈ treeSet B, ∏ e ∈ T, edgeW w a x e ≤ Real.exp (-(m * d * ((B.card : ℝ) - 1))) := by
    intro T hT
    obtain ⟨hsub, hdiag, hcard, -⟩ := mem_treeSet.1 hT
    have he : ∀ e ∈ T, edgeW w a x e ≤ Real.exp (-(m * d)) := by
      intro e
      refine Sym2.ind (f := fun e => e ∈ T → edgeW w a x e ≤ Real.exp (-(m * d)))
        (fun i j he => ?_) e
      have hij := Finset.mk_mem_sym2_iff.1 (hsub he)
      have hne : i ≠ j := fun h => hdiag _ he (Sym2.mk_isDiag_iff.2 h)
      obtain ⟨μ, hμ⟩ := hsep i hij.1 j hij.2 hne
      exact edgeW_le hm hw x i j μ hμ
    have hc : (T.card : ℝ) = (B.card : ℝ) - 1 := by
      have := congrArg (Nat.cast (R := ℝ)) hcard
      push_cast at this
      linarith
    calc ∏ e ∈ T, edgeW w a x e ≤ ∏ _e ∈ T, Real.exp (-(m * d)) :=
          Finset.prod_le_prod (fun e _ => edgeW_nonneg hw0 a x e) he
      _ = Real.exp (-(m * d)) ^ T.card := Finset.prod_const _
      _ = Real.exp (-(m * d * ((B.card : ℝ) - 1))) := by
          rw [← Real.exp_nat_mul, hc]
          ring_nf
  calc treeSum w a x B ≤ ∑ _T ∈ treeSet B, Real.exp (-(m * d * ((B.card : ℝ) - 1))) :=
        Finset.sum_le_sum hT
    _ = ((treeSet B).card : ℝ) * Real.exp (-(m * d * ((B.card : ℝ) - 1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.exp 1) ^ B.card * (B.card : ℝ) ^ (B.card - 2)
          * Real.exp (-(m * d * ((B.card : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_right (card_treeSet_le_real B hB) (Real.exp_pos _).le

/-! ## 3. The tree-graph input and its reduction -/

variable {N : ℕ}

/-- **The tree-graph cluster input**: the edge weight obeys `0 ≤ w ≤ e^{−m‖·‖}`, and the cumulants of the
translated flowed proxies at `d`-separated lattice sites obey
`|κ_k(T_{xᵢ} msProxᵢ : i ∈ B)| ≤ γ^{|B|} ∑_{T tree on B} ∏_{{i,j} ∈ T} w(a xᵢ − a xⱼ) ∏_{i∈B} Kcᵢ s^{−λᵢ}`,
eventually in the step, uniformly over the sites. DERIVED: `4` the dimension; `1` the top of the
separation; `0` the signs. -/
def TreeGap [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (m : ℝ)
    (w : (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ (∀ v, w v ≤ Real.exp (-(m * ‖v‖))) ∧
  ∃ (θc γ : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 ≤ γ ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (ix : Fin n → Ix0) (d : ℝ), 0 < d → d ≤ 1 → ∀ s : ℝ, 0 < s → s ≤ θc * d →
      ∀ᶠ k in atTop, ∀ (x : Fin n → ISite) (B : Finset (Fin n)), B.Nonempty →
        PtSep (dySpacing N k) d x B →
        |cum (stMom (stateK (NeZero.ne N) k)
            (fun i => transObs (x i) (msProx Wf c k s (ix i)))) B|
          ≤ γ ^ B.card * treeSum w (dySpacing N k) x B * ∏ i ∈ B, (Kc (ix i) * s⁻¹ ^ lam (ix i))

/-- **The tree-graph form gives `PointGap`**: `0 ≤ m` and `TreeGap Wf c m w` give
`ClusterPassage.PointGap Wf c m` with the constant `2eγ` (`treeSum_le`). DERIVED: `2` the base of the count;
`1` `e = exp 1`; `0` the signs. -/
theorem pointGap_of_treeGap [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {m : ℝ}
    {w : (Fin 4 → ℝ) → ℝ} (hm : 0 ≤ m) (h : TreeGap Wf c m w) : PointGap Wf c m := by
  obtain ⟨hw0, hw, θc, γ, Kc, lam, hθc, hγ, hKc, H⟩ := h
  refine ⟨θc, 2 * Real.exp 1 * γ, Kc, lam, hθc,
    mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos 1).le) hγ, hKc,
    fun n ix d hd hd1 s hs hsd => ?_⟩
  filter_upwards [H n ix d hd hd1 s hs hsd] with k hk x B hB hsep
  have hP : 0 ≤ ∏ i ∈ B, (Kc (ix i) * s⁻¹ ^ lam (ix i)) := Finset.prod_nonneg fun i _ =>
    mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _)
  have ht := treeSum_le hm hw0 hw x B hB hsep
  refine (hk x B hB hsep).trans ?_
  calc γ ^ B.card * treeSum w (dySpacing N k) x B * ∏ i ∈ B, (Kc (ix i) * s⁻¹ ^ lam (ix i))
      ≤ γ ^ B.card * ((2 * Real.exp 1) ^ B.card * (B.card : ℝ) ^ (B.card - 2)
          * Real.exp (-(m * d * ((B.card : ℝ) - 1)))) * ∏ i ∈ B, (Kc (ix i) * s⁻¹ ^ lam (ix i)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (pow_nonneg hγ _)) hP
    _ = (2 * Real.exp 1 * γ) ^ B.card * ((B.card : ℝ) ^ (B.card - 2))
          * Real.exp (-(m * d * ((B.card : ℝ) - 1))) * ∏ i ∈ B, (Kc (ix i) * s⁻¹ ^ lam (ix i)) := by
        rw [mul_pow]
        ring

/-- **`ClusterGap` from the tree-graph input** (`pointGap_of_treeGap`,
`ClusterPassage.clusterGap_of_pointGap`). DERIVED: `0` the sign of the rate. -/
theorem clusterGap_of_treeGap [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {m : ℝ}
    {w : (Fin 4 → ℝ) → ℝ} (hm : 0 ≤ m) (h : TreeGap Wf c m w) : ClusterGap Wf c m :=
  clusterGap_of_pointGap (pointGap_of_treeGap hm h)

/-- **`ClusterPM` from the tree-graph input** (`clusterGap_of_treeGap`,
`ClusterRoute.clusterPM_of_clusterGap`). DERIVED: `0` the sign of the rate. -/
theorem clusterPM_of_treeGap [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {m : ℝ}
    {w : (Fin 4 → ℝ) → ℝ} (hm : 0 ≤ m) (h : TreeGap Wf c m w) : ClusterPM Wf c :=
  clusterPM_of_clusterGap hm (clusterGap_of_treeGap hm h)

end MassGap.TreeCount

#print axioms MassGap.TreeCount.mem_treeSet
#print axioms MassGap.TreeCount.card_treeSet_le
#print axioms MassGap.TreeCount.card_sym2_le
#print axioms MassGap.TreeCount.sq_pow_le
#print axioms MassGap.TreeCount.card_treeSet_le_real
#print axioms MassGap.TreeCount.edgeW_nonneg
#print axioms MassGap.TreeCount.edgeW_le
#print axioms MassGap.TreeCount.treeSum_le
#print axioms MassGap.TreeCount.pointGap_of_treeGap
#print axioms MassGap.TreeCount.clusterGap_of_treeGap
#print axioms MassGap.TreeCount.clusterPM_of_treeGap
