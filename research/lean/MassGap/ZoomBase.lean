import Mathlib
import MassGap.ScaleLightCone
import MassGap.ClusterPassage
import MassGap.FlowChoice
import MassGap.FreeBridge

/-!
# MassGap.ZoomBase — the coarse observer's clause of `ZoomSettles` holds at every coupling

`ScaleLightCone.ZoomSettles Wf c` has two conjuncts at the first step `k₀` whose spacing reaches the
separation `d`: the base `|relCum_{k₀}| ≤ 1` and the settling of the relative reading from `k₀`. This module
proves the base from the boundedness of the observables of a compact gauge group and the coefficient bound
`MultiScaleOS.CoefBound c`, at every state, every coupling and every family of composites, and splits
`ZoomSettles` into that base and the residual `ZoomSettling` (the settling conjunct alone). Declarations are
in the namespace `MassGap.ZoomBase`.

## 1. Cumulants of bounded observables (proved, general)

* `abs_stMom_le`: `‖Yᵢ‖ ≤ Mᵢ` gives `|ν(∏_{i∈D} Yᵢ)| ≤ ∏_{i∈D} Mᵢ` in every state.
* `sum_powerset_fact_le`: `1 + ∑_{A ⊊ E} 2^{|A|} |A|! ≤ 2^{|E|} |E|!`, from
  `∑_{a ≤ m} C(m, a) a! 2^a ≤ m! (2^{m+1} − 1)`.
* `abs_cum_le_of_mom`: a moment bound `|m(D)| ≤ ∏_{i∈D} Mᵢ` gives `|κ(B)| ≤ 2^{|B|−1} (|B| − 1)! ∏_{i∈B} Mᵢ`
  (strong induction through `ClusterRoute.cum_of_nonempty`).
* `fact_le_succ_pow`: `n! ≤ (n + 1)^{n−1}`; **`abs_cum_le_tree`**: the cumulant bound in Cayley's tree shape
  `2^{|B|} |B|^{|B|−2} ∏_{i∈B} Mᵢ`.

This is the Möbius-inversion bound of `ClusterRoute` §4 (moments bounded per factor give cumulants bounded by
`Cⁿ n! ∏ Kᵢ`); here the per-factor moment bound is the supremum norm, which a state never exceeds.

## 2. The base at the first step

* `kch N j = 2 ‖O_j‖`: the centred flowed channel `O_j ∘ V − ν(O_j ∘ V)` is at most twice the bare
  channel in supremum norm (`norm_msFlow_le`: `‖msFlow_j‖ ≤ a_k^{−d_j} kch_j`).
* `theta0 N = min(a₀, 1/2)`, `a₀ = dySpacing N 0`; `theta0_mul_le_spacing`: at the first step `k₀` of a
  separation `0 < d ≤ 1`, `theta0 · d ≤ a_{k₀}` (`a_{k₀} = a₀ ≥ a₀ d` at `k₀ = 0`, `a_{k₀} > d/2` after).
  So every flow scale `s ≤ theta0 · d` is at most one spacing of the first step, and
  `a_{k₀}^{−d_j} ≤ s^{−d_j}`: the lattice-unit normalisation of the channel is absorbed by the flow scale.
* `CoefBase N c Kc lam`: `ClusterPassage.CoefCtl` at `theta0 N` against `kch` and the canonical dimensions;
  `coefBase_of_coefBound`: `CoefBound c` gives it (`afLog_le`: `(1 + |log s|)^γ ≤ s^{−max(γ, 0)}` on
  `(0, 1]`).
* `norm_clX_le_base`: at the first step, `‖clXᵢ‖ ≤ (wS(a_{k₀}, fᵢ) + a_{k₀}) Kcᵢ s^{−λᵢ}`.
* **`abs_cum_le_base`**: `|κ_{k₀}(clXᵢ : i ∈ B)| ≤ treeW 2 Kc lam k₀ s F B`, in every state; **`zoomBase`**:
  `CoefBound c` gives the base clause of `ZoomSettles` with `θc = theta0 N`, `γ = 2`, with no separation and
  no continuity read.

## 3. The split

* `ZoomSettling Wf c`: `ZoomSettles Wf c` without its base conjunct.
* `tcW`, `pkW`, `treeW_eq`: the tree weight is a step-free factor times `∏ (wS(a_k, fᵢ) + a_k)`;
  `relCum_rescale`: changing the constants multiplies the relative reading by a step-free ratio, so a
  settling reading still settles at larger constants (`tcW_mono`).
* **`zoomSettles_of_settling`**: `CoefBound c` and `ZoomSettling Wf c` give `ZoomSettles Wf c`, with
  `θc = min(theta0 N, θ₁)`, `γ = max(2, γ₁)` and the pointwise maxima of the constants.
  `zoomSettles_iff_settling`: under `CoefBound c` the two are equivalent.
* The copy over the coupling family (`#along_generalize_more`) holds at every coupling family `B`, so at
  `cpl βs` along every tower.

## 4. The root

* `CoreInputsAlongWZB N βs`: `FreeBridge.CoreInputsAlongWFB N βs` with `CoefBound cf` and the copy of
  `ZoomSettling Wf cf` in place of the copy of `ZoomSettles Wf cf`; `coreWFB_of_coreWZB`.
* **`clayStatementOf_of_zoomBase`**: `StrongEnd N`, `ZoomSettlesUV` and `CoreInputsAlongWZB` along the towers
  near `0⁺` give `ClayStatementOf (SU N)`.

`CoreInputsAlongWZB` implies `CoreInputsAlongWFB`, not conversely: per witness it is `CoreInputsAlongWFB` with
`CoefBound cf` added and the base clause removed. `cf` is the bundle's existential coefficient, which also
meets `ExpandMatch`; `CoefBound` is proved on `cfScaled` and `cfLead`, and no member of that class is shown to
meet `ExpandMatch` (`FlowChoice` §1), so `CoefBound cf` is an input of the bundle. It reads the coefficients
only.

## 5. The regime, the tests, and what the base carries

Regime. The base holds at every coupling: no strong-coupling or cluster-expansion input is read. Along
`cpl βs` the state of step `k₀` is the periodic state at `βs k₀`; as `d → 0⁺` the first step `k₀ → ∞` and
`βs k₀ → ∞`, so the coarse step is at weak coupling for all small separations, outside the
strong-coupling interval `0 < β < β₀` of the pruned `PeriodicStrongCoupling` (archive 10-29) and the
Bakry–Émery range `β < N/(4H)` of `CondGap.beConst`, each of which covers finitely many steps only. The base
needs neither.

What the base carries. At the first step every flow scale read is at most one spacing, so the base is an a
priori bound: the supremum of a bounded observable, the per-channel factor `a_{k₀}^{−d_j} ≤ s^{−d_j}`, and the
Möbius count. It holds in every state, so it carries no infrared content of the step; the content of
`ZoomSettles` is its settling conjunct, which `ZoomSettling` keeps whole.

Tests.
* `cum_singleton`, `mom_bound_loadBearing`: the one-point cumulant is the one-point moment, so at a non-zero
  constant observable the bound of `abs_cum_le_of_mom` fails at `M = 0`: its moment hypothesis is
  load-bearing, in every state.
* `not_coefCtl_exp`: coefficients `e^{1/s}` on one channel meet no `CoefCtl`, at any constants: the
  coefficient clause excludes growth faster than every power of `1/s` and is not vacuous.
* `coefBase_cfLead`, `cfLead_ne_zero`: `CoefBase` holds at the route's leading coefficients `cfLead`, whose
  proxy coefficient is non-zero at every `s ≠ 0`: the clause is met by a non-trivial witness, and on
  `cfLead` (and every `cfScaled κ γ`) the residual of `ZoomSettles` is `ZoomSettling` alone.
* `base_only_unbounded`: a reading bounded at `k₀` and unbounded after it; with
  `ScaleLightCone.settlesFrom_zero_unbounded` (no rate, no bound) the settling conjunct and its rate
  `η > 0` are load-bearing for the uniform bound `clusterPM_of_zoomSettles` draws.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the empty values and the limit `0⁺`; `1` the unit of the relative
reading, the top of the separation, the top of the flow scale and the base of `1 + |log s|`; `1/2` the
ratio of consecutive spacings; `2` the centring (a centred observable is at most twice the observable), the
base of the Möbius count `∑_{a ≤ m} 2^a = 2^{m+1} − 1` (proof-internal, the tree weight `γ = 2`) and
Cayley's offset; `a₀ = dySpacing N 0` the first spacing (structural); `θ₁`, `γ₁`, `η`, `Kc`, `λ`
existential; `e` only in the test coefficient `e^{1/s}`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ZoomBase

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.PreObserver MassGap.CompositesBuild MassGap.ClayData MassGap.ReflAvg
  MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll MassGap.MultiScaleOS
  MassGap.ScalePM MassGap.ClusterRoute MassGap.ScaleLightCone
open MassGap.ScaleControlFull (zOne)

/-! ## 1. Cumulants of bounded observables -/

section Cumulant

/-- **Moments of bounded observables**: `‖Yᵢ‖ ≤ Mᵢ`, `Mᵢ ≥ 0`, give `|ν(∏_{i∈D} Yᵢ)| ≤ ∏_{i∈D} Mᵢ` in
every state. DERIVED: `0` the signs. -/
theorem abs_stMom_le {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
    {ι : Type*} (Y : ι → C(X, ℝ)) (M : ι → ℝ) (hM : ∀ i, 0 ≤ M i) (hY : ∀ i, ‖Y i‖ ≤ M i)
    (D : Finset ι) : |stMom ν Y D| ≤ ∏ i ∈ D, M i := by
  rw [stMom]
  refine (ν.abs_le_norm _).trans
    ((ContinuousMap.norm_le _ (Finset.prod_nonneg fun i _ => hM i)).2 fun x => ?_)
  rw [ContinuousMap.prod_apply, Real.norm_eq_abs, Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
  have h := (Y i).norm_coe_le_norm x
  rw [Real.norm_eq_abs] at h
  exact h.trans (hY i)

variable {ι : Type*} [LinearOrder ι]

/-- **The Möbius count**: `1 + ∑_{A ⊊ E} 2^{|A|} |A|! ≤ 2^{|E|} |E|!`. DERIVED: `1` the moment term; `2`
the base of the count. -/
theorem sum_powerset_fact_le (E : Finset ι) :
    1 + ∑ A ∈ E.powerset.erase E, (2 : ℝ) ^ A.card * (A.card.factorial : ℝ)
      ≤ 2 ^ E.card * (E.card.factorial : ℝ) := by
  have hcard := Finset.sum_powerset_apply_card (fun a : ℕ => (2 : ℝ) ^ a * (a.factorial : ℝ)) (x := E)
  try simp only at hcard
  have hterm : ∀ a ∈ Finset.range (E.card + 1),
      E.card.choose a • ((2 : ℝ) ^ a * (a.factorial : ℝ)) ≤ (E.card.factorial : ℝ) * 2 ^ a := by
    intro a ha
    rw [nsmul_eq_mul]
    have hle : a ≤ E.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    have h1 : E.card.choose a * a.factorial ≤ E.card.factorial :=
      (Nat.le_mul_of_pos_right _ (Nat.factorial_pos (E.card - a))).trans_eq
        (Nat.choose_mul_factorial_mul_factorial hle)
    have h1' : (E.card.choose a : ℝ) * (a.factorial : ℝ) ≤ (E.card.factorial : ℝ) := by exact_mod_cast h1
    calc (E.card.choose a : ℝ) * (2 ^ a * (a.factorial : ℝ))
        = 2 ^ a * ((E.card.choose a : ℝ) * (a.factorial : ℝ)) := by ring
      _ ≤ 2 ^ a * (E.card.factorial : ℝ) := mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = (E.card.factorial : ℝ) * 2 ^ a := by ring
  have hg : ∑ i ∈ Finset.range (E.card + 1), (2 : ℝ) ^ i = 2 * 2 ^ E.card - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    ring
  have hfull : ∑ A ∈ E.powerset, (2 : ℝ) ^ A.card * (A.card.factorial : ℝ)
      ≤ (E.card.factorial : ℝ) * (2 * 2 ^ E.card - 1) := by
    rw [hcard, ← hg, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsplit := Finset.sum_erase_add E.powerset
    (fun A => (2 : ℝ) ^ A.card * (A.card.factorial : ℝ)) (Finset.mem_powerset_self E)
  have hF : (1 : ℝ) ≤ (E.card.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  try simp only at hsplit
  linarith

/-- **Cumulants from moments**: `|m(D)| ≤ ∏_{i∈D} Mᵢ` on every `D`, `Mᵢ ≥ 0`, give
`|κ(B)| ≤ 2^{|B|−1} (|B| − 1)! ∏_{i∈B} Mᵢ` on every non-empty `B`. DERIVED: `1` the least index; `2` the
base of the count. -/
theorem abs_cum_le_of_mom {m : Finset ι → ℝ} {M : ι → ℝ} (hm : ∀ D : Finset ι, |m D| ≤ ∏ i ∈ D, M i)
    (hM : ∀ i, 0 ≤ M i) :
    ∀ B : Finset ι, B.Nonempty →
      |cum m B| ≤ 2 ^ (B.card - 1) * ((B.card - 1).factorial : ℝ) * ∏ i ∈ B, M i := by
  intro B
  induction B using Finset.strongInduction with
  | H B ih =>
    intro hB
    have hi₀ : B.min' hB ∈ B := Finset.min'_mem B hB
    have hEc : (B.erase (B.min' hB)).card = B.card - 1 := Finset.card_erase_of_mem hi₀
    have hprodB : ∏ i ∈ B, M i = M (B.min' hB) * ∏ i ∈ B.erase (B.min' hB), M i :=
      (Finset.mul_prod_erase B M hi₀).symm
    have hPB : 0 ≤ ∏ i ∈ B, M i := Finset.prod_nonneg fun i _ => hM i
    have hterm : ∀ A ∈ (B.erase (B.min' hB)).powerset.erase (B.erase (B.min' hB)),
        |cum m (insert (B.min' hB) A) * m (B.erase (B.min' hB) \ A)|
          ≤ (2 : ℝ) ^ A.card * (A.card.factorial : ℝ) * ∏ i ∈ B, M i := by
      intro A hA
      obtain ⟨hss, hi0A, hAE⟩ := MassGap.ClusterPassage.rec_sets hB hA
      have hc : (insert (B.min' hB) A).card = A.card + 1 := Finset.card_insert_of_notMem hi0A
      have h1 := ih _ hss (Finset.insert_nonempty _ _)
      rw [hc, Nat.add_sub_cancel] at h1
      have h2 := hm (B.erase (B.min' hB) \ A)
      have hP : (∏ i ∈ insert (B.min' hB) A, M i) * ∏ i ∈ B.erase (B.min' hB) \ A, M i
          = ∏ i ∈ B, M i := by
        rw [Finset.prod_insert hi0A, hprodB, ← Finset.prod_sdiff hAE]
        ring
      rw [abs_mul]
      calc |cum m (insert (B.min' hB) A)| * |m (B.erase (B.min' hB) \ A)|
          ≤ ((2 : ℝ) ^ A.card * (A.card.factorial : ℝ) * ∏ i ∈ insert (B.min' hB) A, M i)
              * ∏ i ∈ B.erase (B.min' hB) \ A, M i :=
            mul_le_mul h1 h2 (abs_nonneg _)
              (mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => hM i))
        _ = (2 : ℝ) ^ A.card * (A.card.factorial : ℝ) * ∏ i ∈ B, M i := by
            rw [← hP]
            ring
    have hsum := Finset.abs_sum_le_sum_abs
      (fun A => cum m (insert (B.min' hB) A) * m (B.erase (B.min' hB) \ A))
      ((B.erase (B.min' hB)).powerset.erase (B.erase (B.min' hB)))
    have hS := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul] at hS
    have hnum := sum_powerset_fact_le (B.erase (B.min' hB))
    rw [hEc] at hnum
    have htri := abs_add_le (m B)
      (-∑ A ∈ (B.erase (B.min' hB)).powerset.erase (B.erase (B.min' hB)),
        cum m (insert (B.min' hB) A) * m (B.erase (B.min' hB) \ A))
    rw [abs_neg, ← sub_eq_add_neg] at htri
    rw [cum_of_nonempty m hB]
    calc _ ≤ _ := htri
      _ ≤ ∏ i ∈ B, M i + (∑ A ∈ (B.erase (B.min' hB)).powerset.erase (B.erase (B.min' hB)),
            (2 : ℝ) ^ A.card * (A.card.factorial : ℝ)) * ∏ i ∈ B, M i :=
          add_le_add (hm B) (hsum.trans hS)
      _ = (1 + ∑ A ∈ (B.erase (B.min' hB)).powerset.erase (B.erase (B.min' hB)),
            (2 : ℝ) ^ A.card * (A.card.factorial : ℝ)) * ∏ i ∈ B, M i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum hPB

/-- `n! ≤ (n + 1)^{n−1}`. DERIVED: `1` the shift and the least power. -/
theorem fact_le_succ_pow : ∀ n : ℕ, n.factorial ≤ (n + 1) ^ (n - 1)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.factorial_succ]
    have ih := fact_le_succ_pow n
    calc (n + 1) * n.factorial ≤ (n + 1) * (n + 1) ^ (n - 1) := Nat.mul_le_mul_left _ ih
      _ = (n + 1) ^ n := by
          rcases n with _ | n
          · simp
          · rw [Nat.add_sub_cancel, ← pow_succ']
      _ ≤ (n + 1 + 1) ^ (n + 1 - 1) := by
          rw [Nat.add_sub_cancel]
          exact Nat.pow_le_pow_left (by omega) n

/-- **The tree shape**: under the moment bound, `|κ(B)| ≤ 2^{|B|} |B|^{|B|−2} ∏_{i∈B} Mᵢ`.
DERIVED: `2` the base of the count and Cayley's offset; `1` the least index. -/
theorem abs_cum_le_tree {m : Finset ι → ℝ} {M : ι → ℝ} (hm : ∀ D : Finset ι, |m D| ≤ ∏ i ∈ D, M i)
    (hM : ∀ i, 0 ≤ M i) {B : Finset ι} (hB : B.Nonempty) :
    |cum m B| ≤ 2 ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * ∏ i ∈ B, M i := by
  refine (abs_cum_le_of_mom hm hM B hB).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => hM i))
  have hc : 1 ≤ B.card := Finset.card_pos.2 hB
  have hf : ((B.card - 1).factorial : ℝ) ≤ (B.card : ℝ) ^ (B.card - 2) := by
    have h := fact_le_succ_pow (B.card - 1)
    rw [Nat.sub_add_cancel hc, show B.card - 1 - 1 = B.card - 2 by omega] at h
    exact_mod_cast h
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) hf (Nat.cast_nonneg _)
    (by positivity)

/-- **The one-point cumulant is the one-point moment.** DERIVED: no numeral. -/
theorem cum_singleton (m : Finset ι → ℝ) (i : ι) : cum m {i} = m {i} := by
  rw [cum_of_nonempty m (Finset.singleton_nonempty i)]
  simp [Finset.min'_singleton]

end Cumulant

/-- **The moment hypothesis is load-bearing**: at a non-zero constant observable `t • 1`, in every state,
the bound of `abs_cum_le_of_mom` fails at `M = 0`. DERIVED: `0` the dropped bound and the index; `1` the
one factor. -/
theorem mom_bound_loadBearing {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {t : ℝ} (ht : t ≠ 0) :
    ¬ |cum (stMom ν (fun _ : Fin 1 => t • (1 : C(X, ℝ)))) {0}|
        ≤ 2 ^ (({0} : Finset (Fin 1)).card - 1) * (((({0} : Finset (Fin 1)).card - 1).factorial : ℝ))
          * ∏ _i ∈ ({0} : Finset (Fin 1)), (0 : ℝ) := by
  rw [cum_singleton, stMom, Finset.prod_singleton, ν.map_smul, ν.map_one, Finset.prod_singleton,
    mul_zero, mul_one]
  exact not_le.2 (abs_pos.2 ht)

/-! ## 2. The base at the first step -/

variable {N : ℕ}

variable (N) in
/-- **The channel bound**: `2 ‖O_j‖`, the supremum of the centred bare channel. DERIVED: `2` the centring. -/
def kch (j : MIx) : ℝ := 2 * ‖(mField (N := N) j).1‖

theorem kch_nonneg (j : MIx) : 0 ≤ kch N j := by
  unfold kch
  positivity

/-- **The centred flowed channel**: `‖msFlow_j‖ ≤ a_k^{−d_j} kch_j`. DERIVED: `2` the centring. -/
theorem norm_msFlow_le [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    ‖msFlow Wf k s j‖ ≤ (dySpacing N k ^ mDim j)⁻¹ * kch N j := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hG : ‖((Wf s).fieldMap k (mField j)).1‖ ≤ ‖(mField (N := N) j).1‖ :=
    (ContinuousMap.norm_le ((Wf s).fieldMap k (mField j)).1 (norm_nonneg _)).mpr
      (fun U => (mField (N := N) j).1.norm_coe_le_norm ((Wf s).V k U))
  have hν := (stateK (NeZero.ne N) k).abs_le_norm ((Wf s).fieldMap k (mField j)).1
  show ‖(dySpacing N k ^ mDim j)⁻¹ • (((Wf s).fieldMap k (mField j)).1
      - stateK (NeZero.ne N) k ((Wf s).fieldMap k (mField j)).1 • (1 : C(Cfg N, ℝ)))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (pow_pos ha _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_pos ha _).le)
  refine (norm_sub_smul_one_le _ _).trans ?_
  unfold kch
  linarith

/-- **The flowed proxy**: `‖msProxᵢ‖ ≤ ∑_j |c_{ij}(s)| ‖msFlow_j‖`. DERIVED: no numeral. -/
theorem norm_msProx_le [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (i : Ix0) : ‖msProx Wf c k s i‖ ≤ ∑ j ∈ (c i s).support, |c i s j| * ‖msFlow Wf k s j‖ := by
  unfold msProx
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]

/-- **The smeared proxy**: `‖clXᵢ‖ ≤ wS(a_k, fᵢ) ‖msProxᵢ‖`. DERIVED: `4` the cell-volume exponent. -/
theorem norm_clX_le [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) {n : ℕ}
    (F : Fin n → CDatum (CbR N zOne)) (i : Fin n) :
    ‖clX Wf c k s F i‖ ≤ wS (dySpacing N k) (F i).2 * ‖msProx Wf c k s (F i).1‖ := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  rw [MassGap.ClusterPassage.clX_eq_sum, ← MassGap.ClusterPassage.sum_abs_weight ha]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_transObs_le _ _) (abs_nonneg _)

variable (N) in
/-- **The base ratio**: `min(a₀, 1/2)`, the first spacing against the ratio of consecutive spacings.
DERIVED: `1/2` the ratio of consecutive spacings; `0` the first step. -/
def theta0 : ℝ := min (dySpacing N 0) (1 / 2)

theorem theta0_pos [NeZero N] : 0 < theta0 N :=
  lt_min (dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 0) (by norm_num)

/-- DERIVED: `1/2` the ratio. -/
theorem theta0_le_half : theta0 N ≤ 1 / 2 := min_le_right _ _

/-- **The first step is at most one spacing below the separation's scale**: `theta0 · d ≤ a_{k₀}` at the
first step `k₀` of `0 < d ≤ 1`. DERIVED: `1/2` the ratio; `1` the top of the separation; `0` the first
step. -/
theorem theta0_mul_le_spacing [NeZero N] {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) {k : ℕ}
    (hk : FirstStep N d k) : theta0 N * d ≤ dySpacing N k := by
  rcases k with _ | j
  · calc theta0 N * d ≤ dySpacing N 0 * 1 :=
          mul_le_mul (min_le_left _ _) hd1 hd.le (dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 0).le
      _ = dySpacing N 0 := mul_one _
  · have h := hk.2 j (Nat.lt_succ_self j)
    have e := spacing_ratio_succ N 1 j
    simp only [div_one] at e
    calc theta0 N * d ≤ (1 / 2) * d := mul_le_mul_of_nonneg_right theta0_le_half hd.le
      _ ≤ dySpacing N (j + 1) := by linarith

/-- **A flow scale within one spacing**: `0 < s ≤ a` gives `a^{−m} ≤ s^{−m}`. DERIVED: no numeral. -/
theorem inv_pow_le_rpow {a s : ℝ} (hs : 0 < s) (hsa : s ≤ a) (m : ℕ) :
    (a ^ m)⁻¹ ≤ s⁻¹ ^ (m : ℝ) := by
  rw [Real.rpow_natCast, inv_pow]
  exact inv_anti₀ (pow_pos hs _) (pow_le_pow_left₀ hs.le hsa _)

variable (N) in
/-- **The coefficient clause of the base**: `ClusterPassage.CoefCtl` at `theta0 N`, against the channel
bound `kch` and the canonical dimensions. DERIVED: no numeral. -/
def CoefBase (c : Ix0 → ℝ → (MIx →₀ ℝ)) (Kc lam : Ix0 → ℝ) : Prop :=
  MassGap.ClusterPassage.CoefCtl c (theta0 N) (kch N) (fun j => (mDim j : ℝ)) Kc lam

/-- **The running-coupling factor on the unit interval**: `(1 + |log s|)^γ ≤ s^{−max(γ, 0)}` at
`0 < s ≤ 1`. DERIVED: `1` the top of the scale and the base; `0` the floor of the exponent. -/
theorem afLog_le (γ : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : afLog γ s ≤ s⁻¹ ^ max γ 0 := by
  have hl : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have hb1 : 1 ≤ 1 + |Real.log s| := le_add_of_nonneg_right (abs_nonneg _)
  have hbs : 1 + |Real.log s| ≤ s⁻¹ := by
    rw [abs_of_nonpos hl, ← Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos (inv_pos.2 hs)]
  unfold afLog
  calc (1 + |Real.log s|) ^ γ ≤ (1 + |Real.log s|) ^ max γ 0 :=
        Real.rpow_le_rpow_of_exponent_le hb1 (le_max_left _ _)
    _ ≤ s⁻¹ ^ max γ 0 := Real.rpow_le_rpow (by linarith) hbs (le_max_right _ _)

/-- **`CoefBound` gives the coefficient clause of the base**, with `Kcᵢ = 1 + ∑_{j∈Sᵢ} |Kᵢ| kch_j` and
`λᵢ = d_i + max(γᵢ, 0)`. DERIVED: `1` the floor of `Kc` and the top of the scale; `1/2` the ratio; `0` the
floor of the log exponent. -/
theorem coefBase_of_coefBound {c : Ix0 → ℝ → (MIx →₀ ℝ)} (hC : CoefBound c) :
    ∃ Kc lam : Ix0 → ℝ, (∀ i, 0 < Kc i) ∧ CoefBase N c Kc lam := by
  obtain ⟨S, K, γc, hC⟩ := hC
  have hsum0 : ∀ i, 0 ≤ ∑ j ∈ S i, |K i| * kch N j := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (kch_nonneg j)
  refine ⟨fun i => 1 + ∑ j ∈ S i, |K i| * kch N j, fun i => (cdim i.1 : ℝ) + max (γc i) 0,
    fun i => by linarith [hsum0 i], fun i s hs hsθ => ?_⟩
  have hs0 : s ≠ 0 := hs.ne'
  have hs1 : s ≤ 1 := hsθ.trans (theta0_le_half.trans (by norm_num))
  obtain ⟨hsup, hbd⟩ := hC i s hs hs1
  have hA := afLog_pos (γc i) s
  have hL0 : 0 ≤ (s ^ cdim i.1)⁻¹ * afLog (γc i) s :=
    mul_nonneg (inv_nonneg.2 (pow_nonneg hs.le _)) hA.le
  have hterm : ∀ j, |c i s j| * (kch N j * s⁻¹ ^ (mDim j : ℝ))
      ≤ |K i| * kch N j * ((s ^ cdim i.1)⁻¹ * afLog (γc i) s) := by
    intro j
    have hx : 0 ≤ s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s := by positivity
    have h1 : |c i s j| ≤ |K i| * (s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s) :=
      calc |c i s j| ≤ K i * s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s := hbd j
        _ = K i * (s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s) := by ring
        _ ≤ |K i| * (s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have hk0 : 0 ≤ kch N j * s⁻¹ ^ (mDim j : ℝ) :=
      mul_nonneg (kch_nonneg j) (Real.rpow_nonneg (inv_nonneg.2 hs.le) _)
    calc |c i s j| * (kch N j * s⁻¹ ^ (mDim j : ℝ))
        ≤ |K i| * (s ^ mDim j / s ^ cdim i.1 * afLog (γc i) s) * (kch N j * s⁻¹ ^ (mDim j : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hk0
      _ = |K i| * kch N j * ((s ^ cdim i.1)⁻¹ * afLog (γc i) s) := by
          rw [Real.rpow_natCast, inv_pow]
          field_simp
          try ring
  have hL : (s ^ cdim i.1)⁻¹ * afLog (γc i) s ≤ s⁻¹ ^ ((cdim i.1 : ℝ) + max (γc i) 0) := by
    rw [Real.rpow_add (inv_pos.2 hs), Real.rpow_natCast, inv_pow]
    exact mul_le_mul_of_nonneg_left (afLog_le _ hs hs1) (inv_nonneg.2 (pow_nonneg hs.le _))
  show ∑ j ∈ (c i s).support, |c i s j| * (kch N j * s⁻¹ ^ (mDim j : ℝ))
      ≤ (1 + ∑ j ∈ S i, |K i| * kch N j) * s⁻¹ ^ ((cdim i.1 : ℝ) + max (γc i) 0)
  calc ∑ j ∈ (c i s).support, |c i s j| * (kch N j * s⁻¹ ^ (mDim j : ℝ))
      ≤ ∑ j ∈ S i, |c i s j| * (kch N j * s⁻¹ ^ (mDim j : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsup fun j _ _ =>
          mul_nonneg (abs_nonneg _) (mul_nonneg (kch_nonneg j) (Real.rpow_nonneg (inv_nonneg.2 hs.le) _))
    _ ≤ ∑ j ∈ S i, |K i| * kch N j * ((s ^ cdim i.1)⁻¹ * afLog (γc i) s) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j ∈ S i, |K i| * kch N j) * ((s ^ cdim i.1)⁻¹ * afLog (γc i) s) := by
        rw [Finset.sum_mul]
    _ ≤ (1 + ∑ j ∈ S i, |K i| * kch N j) * s⁻¹ ^ ((cdim i.1 : ℝ) + max (γc i) 0) :=
        mul_le_mul (by linarith) hL hL0 (by linarith [hsum0 i])

/-- **The smeared proxy at the first step**: `‖clXᵢ‖ ≤ (wS(a_{k₀}, fᵢ) + a_{k₀}) Kcᵢ s^{−λᵢ}` at every
flow scale `0 < s ≤ theta0 · d`. DERIVED: `1` the top of the separation. -/
theorem norm_clX_le_base [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {Kc lam : Ix0 → ℝ}
    (hctl : CoefBase N c Kc lam) {n : ℕ} (F : Fin n → CDatum (CbR N zOne))
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) {s : ℝ} (hs : 0 < s) (hsd : s ≤ theta0 N * d) {k : ℕ}
    (hk : FirstStep N d k) (i : Fin n) :
    ‖clX Wf c k s F i‖
      ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hsa : s ≤ dySpacing N k := hsd.trans (theta0_mul_le_spacing hd hd1 hk)
  have hsθ : s ≤ theta0 N := hsd.trans (mul_le_of_le_one_right theta0_pos.le hd1)
  have hflow : ∀ j, ‖msFlow Wf k s j‖ ≤ kch N j * s⁻¹ ^ (mDim j : ℝ) := fun j =>
    (norm_msFlow_le Wf k s j).trans ((mul_comm _ _).le.trans
      (mul_le_mul_of_nonneg_left (inv_pow_le_rpow hs hsa _) (kch_nonneg j)))
  have hprox : ‖msProx Wf c k s (F i).1‖ ≤ Kc (F i).1 * s⁻¹ ^ lam (F i).1 :=
    (norm_msProx_le Wf c k s (F i).1).trans
      ((Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hflow j) (abs_nonneg _)).trans
        (hctl (F i).1 s hs hsθ))
  exact (norm_clX_le Wf c k s F i).trans
    (mul_le_mul (le_add_of_nonneg_right ha.le) hprox (norm_nonneg _)
      (add_nonneg (wS_nonneg ha _) ha.le))

/-- **The base cumulant bound**: at the first step `k₀` of `0 < d ≤ 1`, at every flow scale
`0 < s ≤ theta0 · d` and every non-empty block, `|κ_{k₀}(clXᵢ : i ∈ B)| ≤ treeW 2 Kc lam k₀ s F B`, in the
state of the step whatever its coupling. DERIVED: `2` the tree weight of the Möbius count. -/
theorem abs_cum_le_base [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {Kc lam : Ix0 → ℝ}
    (hKc : ∀ i, 0 < Kc i) (hctl : CoefBase N c Kc lam) {n : ℕ} (F : Fin n → CDatum (CbR N zOne))
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) {s : ℝ} (hs : 0 < s) (hsd : s ≤ theta0 N * d) {k : ℕ}
    (hk : FirstStep N d k) (B : Finset (Fin n)) (hB : B.Nonempty) :
    |cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B| ≤ treeW 2 Kc lam k s F B := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hM0 : ∀ i : Fin n, 0 ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k)
      * (Kc (F i).1 * s⁻¹ ^ lam (F i).1) := fun i =>
    mul_nonneg (add_nonneg (wS_nonneg ha _) ha.le)
      (mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.2 hs.le) _))
  have h := abs_cum_le_tree
    (abs_stMom_le (stateK (NeZero.ne N) k) (clX Wf c k s F) _ hM0
      (norm_clX_le_base hctl F hd hd1 hs hsd hk)) hM0 hB
  refine h.trans (le_of_eq ?_)
  unfold treeW
  ring

/-- **The base clause of `ZoomSettles` from `CoefBound`**: with `θc = theta0 N` and `γ = 2`, on every family
of composites, `0 < d ≤ 1`, every flow scale `0 < s ≤ θc d`, every non-empty block and the first step `k₀`,
`|relCum_{k₀}| ≤ 1`. No separation and no continuity is read. DERIVED: `2` the tree weight; `1` the unit of
the relative reading and the top of the separation; `0` the signs. -/
theorem zoomBase [NeZero N] (Wf : ℝ → ConfFlow N) {c : Ix0 → ℝ → (MIx →₀ ℝ)} (hC : CoefBound c) :
    ∃ (θc γ : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 < γ ∧ (∀ i, 0 < Kc i) ∧
      ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 →
        ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ B : Finset (Fin n), B.Nonempty → ∀ k₀ : ℕ, FirstStep N d k₀ →
          |relCum Wf c γ Kc lam k₀ s F B| ≤ 1 := by
  obtain ⟨Kc, lam, hKc, hctl⟩ := coefBase_of_coefBound (N := N) hC
  refine ⟨theta0 N, 2, Kc, lam, theta0_pos, two_pos, hKc,
    fun n F d hd hd1 s hs hsd B hB k₀ hk₀ => ?_⟩
  have hT := treeW_pos two_pos hKc lam k₀ hs F hB
  rw [relCum, abs_div, abs_of_pos hT, div_le_one hT]
  exact abs_cum_le_base hKc hctl F hd hd1 hs hsd hk₀ B hB

/-! ## 3. The split -/

variable [NeZero N]

/-- **The settling conjunct of `ZoomSettles`**, alone: one `θc > 0`, `γ > 0`, `η > 0`, per composite
`Kcᵢ > 0`, `λᵢ`; on every continuous `d`-separated family, `0 < d ≤ 1`, every flow scale `0 < s ≤ θc d` and
every non-empty block, the relative reading settles from the first step `k₀` at the ratios `a_k / d` with
rate `η`. DERIVED: `1` the top of the separation; `0` the signs. -/
def ZoomSettling (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ (θc γ η : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 < γ ∧ 0 < η ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
      ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ B : Finset (Fin n), B.Nonempty → ∀ k₀ : ℕ, FirstStep N d k₀ →
        SettlesFrom (fun k => relCum Wf c γ Kc lam k s F B) (fun k => dySpacing N k / d) η k₀

/-- `ZoomSettles` gives `ZoomSettling` (its second conjunct). DERIVED: no numeral. -/
theorem zoomSettling_of_zoomSettles {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ZoomSettles Wf c) : ZoomSettling Wf c := by
  obtain ⟨θc, γ, η, Kc, lam, hθc, hγ, hη, hKc, H⟩ := h
  exact ⟨θc, γ, η, Kc, lam, hθc, hγ, hη, hKc, fun n F d hd hd1 hc hs s hs0 hsd B hB k₀ hk₀ =>
    (H n F d hd hd1 hc hs s hs0 hsd B hB k₀ hk₀).2⟩

/-- **The step-free factor of the tree weight**: `γ^{|B|} |B|^{|B|−2} ∏_{i∈B} Kcᵢ s^{−λᵢ}`.
DERIVED: `2` Cayley's offset. -/
def tcW (γ : ℝ) (Kc lam : Ix0 → ℝ) (s : ℝ) {n : ℕ} (F : Fin n → CDatum (CbR N zOne))
    (B : Finset (Fin n)) : ℝ :=
  γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2)) * ∏ i ∈ B, (Kc (F i).1 * s⁻¹ ^ lam (F i).1)

/-- **The step factor of the tree weight**: `∏_{i∈B} (wS(a_k, fᵢ) + a_k)`. DERIVED: no numeral. -/
def pkW (k : ℕ) {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) (B : Finset (Fin n)) : ℝ :=
  ∏ i ∈ B, (wS (dySpacing N k) (F i).2 + dySpacing N k)

/-- DERIVED: no numeral. -/
theorem treeW_eq (γ : ℝ) (Kc lam : Ix0 → ℝ) (k : ℕ) (s : ℝ) {n : ℕ} (F : Fin n → CDatum (CbR N zOne))
    (B : Finset (Fin n)) : treeW γ Kc lam k s F B = tcW γ Kc lam s F B * pkW k F B := by
  unfold treeW tcW pkW
  rw [Finset.prod_mul_distrib]
  ring

/-- DERIVED: `0` the signs. -/
theorem pkW_pos (k : ℕ) {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) (B : Finset (Fin n)) :
    0 < pkW k F B := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  exact Finset.prod_pos fun i _ => add_pos_of_nonneg_of_pos (wS_nonneg ha _) ha

omit [NeZero N] in
/-- DERIVED: `0` the signs. -/
theorem tcW_pos {γ : ℝ} (hγ : 0 < γ) {Kc : Ix0 → ℝ} (hKc : ∀ i, 0 < Kc i) (lam : Ix0 → ℝ) {s : ℝ}
    (hs : 0 < s) {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) {B : Finset (Fin n)} (hB : B.Nonempty) :
    0 < tcW γ Kc lam s F B := by
  unfold tcW
  exact mul_pos (mul_pos (pow_pos hγ _) (pow_pos (Nat.cast_pos.2 (Finset.card_pos.2 hB)) _))
    (Finset.prod_pos fun i _ => mul_pos (hKc _) (Real.rpow_pos_of_pos (inv_pos.2 hs) _))

omit [NeZero N] in
/-- **Larger constants, larger step-free factor** (at `0 < s ≤ 1`). DERIVED: `1` the top of the flow
scale; `0` the signs. -/
theorem tcW_mono {γ₁ γ : ℝ} (hγ₁ : 0 ≤ γ₁) (hγ : γ₁ ≤ γ) {Kc₁ Kc lam₁ lam : Ix0 → ℝ}
    (hK₁ : ∀ i, 0 ≤ Kc₁ i) (hK : ∀ i, Kc₁ i ≤ Kc i) (hl : ∀ i, lam₁ i ≤ lam i) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) (B : Finset (Fin n)) :
    tcW γ₁ Kc₁ lam₁ s F B ≤ tcW γ Kc lam s F B := by
  have hs' : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs1
  have hs0 : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  unfold tcW
  refine mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hγ₁ hγ _)
      (pow_nonneg (Nat.cast_nonneg _) _))
    (Finset.prod_le_prod (fun i _ => mul_nonneg (hK₁ _) (Real.rpow_nonneg hs0 _))
      (fun i _ => mul_le_mul (hK _) (Real.rpow_le_rpow_of_exponent_le hs' (hl _))
        (Real.rpow_nonneg hs0 _) ((hK₁ _).trans (hK _))))
    (Finset.prod_nonneg fun i _ => mul_nonneg (hK₁ _) (Real.rpow_nonneg hs0 _))
    (mul_nonneg (pow_nonneg (hγ₁.trans hγ) _) (pow_nonneg (Nat.cast_nonneg _) _))

/-- **Changing the constants rescales the relative reading by a step-free ratio**:
`relCum_{γ,Kc,λ} = (tcW₁ / tcW) relCum_{γ₁,Kc₁,λ₁}` at every step. DERIVED: no numeral. -/
theorem relCum_rescale (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {γ γ₁ : ℝ}
    {Kc Kc₁ lam lam₁ : Ix0 → ℝ} (k : ℕ) (s : ℝ) {n : ℕ} (F : Fin n → CDatum (CbR N zOne))
    (B : Finset (Fin n)) (hT : 0 < tcW γ Kc lam s F B) (hT₁ : 0 < tcW γ₁ Kc₁ lam₁ s F B) :
    relCum Wf c γ Kc lam k s F B
      = tcW γ₁ Kc₁ lam₁ s F B / tcW γ Kc lam s F B * relCum Wf c γ₁ Kc₁ lam₁ k s F B := by
  have hP := pkW_pos k F B
  unfold relCum
  rw [treeW_eq, treeW_eq]
  field_simp
  try ring

/-- **`ZoomSettles` from the base and the settling**: `CoefBase N c Kc₀ lam₀` and `ZoomSettling Wf c` give
`ZoomSettles Wf c` with `θc = min(theta0 N, θ₁)`, `γ = max(2, γ₁)`, `Kc = max(Kc₀, Kc₁)`,
`λ = max(λ₀, λ₁)`. DERIVED: `2` the base tree weight; `1` the unit of the relative reading, the top of the
separation and of the flow scale; `1/2` the ratio; `0` the signs. -/
theorem zoomSettles_of_base {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} {Kc₀ lam₀ : Ix0 → ℝ}
    (hK₀ : ∀ i, 0 < Kc₀ i) (hctl : CoefBase N c Kc₀ lam₀) (h : ZoomSettling Wf c) :
    ZoomSettles Wf c := by
  obtain ⟨θ₁, γ₁, η, Kc₁, lam₁, hθ₁, hγ₁, hη, hK₁, H⟩ := h
  have hγ : (0 : ℝ) < max 2 γ₁ := lt_max_of_lt_left two_pos
  have hK : ∀ i, 0 < max (Kc₀ i) (Kc₁ i) := fun i => lt_max_of_lt_left (hK₀ i)
  refine ⟨min (theta0 N) θ₁, max 2 γ₁, η, fun i => max (Kc₀ i) (Kc₁ i), fun i => max (lam₀ i) (lam₁ i),
    lt_min theta0_pos hθ₁, hγ, hη, hK, fun n F d hd hd1 hcont hsep s hs hsd B hB k₀ hk₀ => ⟨?_, ?_⟩⟩
  · have hs1 : s ≤ 1 := by
      have h1 : s ≤ theta0 N * 1 :=
        hsd.trans (mul_le_mul (min_le_left _ _) hd1 hd.le theta0_pos.le)
      linarith [theta0_le_half (N := N)]
    have hT := treeW_pos hγ hK (fun i => max (lam₀ i) (lam₁ i)) k₀ hs F hB
    rw [relCum, abs_div, abs_of_pos hT, div_le_one hT]
    refine (abs_cum_le_base hK₀ hctl F hd hd1 hs
      (hsd.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hd.le)) hk₀ B hB).trans ?_
    rw [treeW_eq, treeW_eq]
    exact mul_le_mul_of_nonneg_right (tcW_mono two_pos.le (le_max_left _ _) (fun i => (hK₀ i).le)
      (fun i => le_max_left _ _) (fun i => le_max_left _ _) hs hs1 F B) (pkW_pos k₀ F B).le
  · have hs1 : s ≤ 1 := by
      have h1 : s ≤ theta0 N * 1 :=
        hsd.trans (mul_le_mul (min_le_left _ _) hd1 hd.le theta0_pos.le)
      linarith [theta0_le_half (N := N)]
    have hset := H n F d hd hd1 hcont hsep s hs
      (hsd.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hd.le)) B hB k₀ hk₀
    have hT := tcW_pos hγ hK (fun i => max (lam₀ i) (lam₁ i)) hs F hB
    have hT₁ := tcW_pos hγ₁ hK₁ lam₁ hs F hB
    have hρ0 : 0 < tcW γ₁ Kc₁ lam₁ s F B / tcW (max 2 γ₁) (fun i => max (Kc₀ i) (Kc₁ i))
        (fun i => max (lam₀ i) (lam₁ i)) s F B := div_pos hT₁ hT
    have hρ1 : tcW γ₁ Kc₁ lam₁ s F B / tcW (max 2 γ₁) (fun i => max (Kc₀ i) (Kc₁ i))
        (fun i => max (lam₀ i) (lam₁ i)) s F B ≤ 1 :=
      (div_le_one hT).2 (tcW_mono hγ₁.le (le_max_right _ _) (fun i => (hK₁ i).le)
        (fun i => le_max_right _ _) (fun i => le_max_right _ _) hs hs1 F B)
    intro k hk
    show |relCum Wf c (max 2 γ₁) (fun i => max (Kc₀ i) (Kc₁ i)) (fun i => max (lam₀ i) (lam₁ i))
        (k + 1) s F B - relCum Wf c (max 2 γ₁) (fun i => max (Kc₀ i) (Kc₁ i))
        (fun i => max (lam₀ i) (lam₁ i)) k s F B| ≤ (dySpacing N k / d) ^ η
    rw [relCum_rescale Wf c (k + 1) s F B hT hT₁, relCum_rescale Wf c k s F B hT hT₁, ← mul_sub,
      abs_mul, abs_of_pos hρ0]
    calc _ ≤ 1 * |relCum Wf c γ₁ Kc₁ lam₁ (k + 1) s F B - relCum Wf c γ₁ Kc₁ lam₁ k s F B| :=
          mul_le_mul_of_nonneg_right hρ1 (abs_nonneg _)
      _ ≤ (dySpacing N k / d) ^ η := by
          rw [one_mul]
          exact hset k hk

/-- **The split of `ZoomSettles`**: `CoefBound c` and `ZoomSettling Wf c` give `ZoomSettles Wf c`.
DERIVED: no numeral. -/
theorem zoomSettles_of_settling {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} (hC : CoefBound c)
    (h : ZoomSettling Wf c) : ZoomSettles Wf c := by
  obtain ⟨Kc₀, lam₀, hK₀, hctl⟩ := coefBase_of_coefBound (N := N) hC
  exact zoomSettles_of_base hK₀ hctl h

/-- **Under `CoefBound` the base clause is redundant**: `ZoomSettles Wf c ↔ ZoomSettling Wf c`.
DERIVED: no numeral. -/
theorem zoomSettles_iff_settling {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} (hC : CoefBound c) :
    ZoomSettles Wf c ↔ ZoomSettling Wf c :=
  ⟨zoomSettling_of_zoomSettles, zoomSettles_of_settling hC⟩

/-! ### The tests -/

omit [NeZero N] in
/-- **`CoefBase` holds at the route's leading coefficients.** DERIVED: no numeral. -/
theorem coefBase_cfLead : ∃ Kc lam : Ix0 → ℝ, (∀ i, 0 < Kc i) ∧ CoefBase N FlowChoice.cfLead Kc lam :=
  coefBase_of_coefBound (FlowChoice.coefBound_cfScaled _ _)

/-- **The leading coefficients are not zero**: `cfLead i s = e_{inl i} ≠ 0` at every `s ≠ 0`.
DERIVED: `1` the unit coefficient; `0` the excluded scale. -/
theorem cfLead_ne_zero (i : Ix0) {s : ℝ} (hs : s ≠ 0) : FlowChoice.cfLead i s ≠ 0 := by
  rw [FlowChoice.cfLead_eq i hs]
  exact Finsupp.single_ne_zero.2 one_ne_zero

/-- **The coefficient clause excludes super-power growth**: coefficients `e^{1/s}` on one channel `j₀`
with `Kch_{j₀} > 0` meet no `CoefCtl`, at any `θ > 0` and any constants. DERIVED: `1` the floor of the
test point; `0` the signs. -/
theorem not_coefCtl_exp (i : Ix0) (j₀ : MIx) {θ : ℝ} (hθ : 0 < θ) {Kch lamCh : MIx → ℝ}
    (hK : 0 < Kch j₀) (Kc lam : Ix0 → ℝ) :
    ¬ MassGap.ClusterPassage.CoefCtl (fun _ s => Finsupp.single j₀ (Real.exp s⁻¹)) θ Kch lamCh Kc lam := by
  intro h
  obtain ⟨x, hx1, hx2⟩ :=
    (((tendsto_exp_div_rpow_atTop (lam i - lamCh j₀)).eventually_gt_atTop (Kc i / Kch j₀)).and
      (eventually_ge_atTop (max θ⁻¹ 1))).exists
  have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx2)
  have hsθ : x⁻¹ ≤ θ := by
    rw [inv_le_comm₀ hx0 hθ]
    exact (le_max_left _ _).trans hx2
  have hc := h i x⁻¹ (inv_pos.2 hx0) hsθ
  beta_reduce at hc
  rw [Finsupp.support_single _ (Real.exp_pos _).ne', Finset.sum_singleton, Finsupp.single_eq_same,
    inv_inv, abs_of_pos (Real.exp_pos _)] at hc
  have key : Real.exp x / x ^ (lam i - lamCh j₀) ≤ Kc i / Kch j₀ := by
    rw [Real.rpow_sub hx0, div_div_eq_mul_div,
      div_le_div_iff₀ (Real.rpow_pos_of_pos hx0 _) hK]
    linarith [hc]
  exact absurd key (not_le.2 hx1)

/-- **The base alone bounds nothing after the first step**: a reading bounded at `k₀` and unbounded from
it. DERIVED: `1` the unit of the relative reading and the unit step. -/
theorem base_only_unbounded (k₀ : ℕ) :
    ∃ q : ℕ → ℝ, |q k₀| ≤ 1 ∧ ¬ ∃ C : ℝ, ∀ k, k₀ ≤ k → |q k| ≤ C := by
  refine ⟨fun k => (k : ℝ) - k₀, by simp, fun ⟨C, hC⟩ => ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have h := hC (k₀ + m) (Nat.le_add_right _ _)
  simp only [Nat.cast_add, add_sub_cancel_left, Nat.abs_cast] at h
  linarith

end MassGap.ZoomBase

end

/-! ### The copy over a coupling family -/

namespace MassGap.ZoomBase

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ZoomBase.zoomSettles_of_settling
  MassGap.ZoomBase.zoomBase

-- No copy mentions the source (every copy in `MassGap.CouplingGen.Along`, the new ones included).
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.ZoomBase

/-! ## 4. The root -/

noncomputable section

namespace MassGap.ZoomBase

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl)
open MassGap.CouplingTower (StrongEnd CouplingTower)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ScaleLightCone (ZoomSettlesUV)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The bridge bundle with the base discharged**: `FreeBridge.CoreInputsAlongWFB` with `CoefBound cf` and
the copy of `ZoomSettling Wf cf` in place of the copy of `ZoomSettles Wf cf`, every other field unchanged.
DERIVED: `0` the signs. -/
def CoreInputsAlongWZB (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.FreeBridge.ApertureBridge (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.ExpandMatch.ExpandMatch (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ MultiScaleOS.CoefBound cf
      ∧ CouplingGen.Along.ZoomBase.ZoomSettling (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

omit [Fact (2 ≤ N)] in
/-- **The base-discharged bundle gives the bridge bundle** (the copy of `zoomSettles_of_settling` at
`cpl βs`). DERIVED: no numeral. -/
theorem coreWFB_of_coreWZB {βs : ℕ → ℝ} (h : CoreInputsAlongWZB N βs) :
    FreeBridge.CoreInputsAlongWFB N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, hC, hS, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE,
    CouplingGen.Along.ZoomBase.zoomSettles_of_settling (cpl βs) hC hS, F⟩

/-- **The root at `SU(N)` with the base discharged**: `StrongEnd N`, the settling window reading and
`CoreInputsAlongWZB` along the towers near `0⁺` give `ClayStatementOf (SU N)`
(`FreeBridge.clayStatementOf_of_freeBridge`, `coreWFB_of_coreWZB`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_zoomBase (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWZB N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  FreeBridge.clayStatementOf_of_freeBridge hS hUV (hF.mono fun _ h βs hT => coreWFB_of_coreWZB (h βs hT))

end MassGap.ZoomBase

end

#print axioms MassGap.ZoomBase.abs_stMom_le
#print axioms MassGap.ZoomBase.sum_powerset_fact_le
#print axioms MassGap.ZoomBase.abs_cum_le_of_mom
#print axioms MassGap.ZoomBase.fact_le_succ_pow
#print axioms MassGap.ZoomBase.abs_cum_le_tree
#print axioms MassGap.ZoomBase.cum_singleton
#print axioms MassGap.ZoomBase.mom_bound_loadBearing
#print axioms MassGap.ZoomBase.norm_msFlow_le
#print axioms MassGap.ZoomBase.norm_clX_le
#print axioms MassGap.ZoomBase.theta0_mul_le_spacing
#print axioms MassGap.ZoomBase.afLog_le
#print axioms MassGap.ZoomBase.coefBase_of_coefBound
#print axioms MassGap.ZoomBase.norm_clX_le_base
#print axioms MassGap.ZoomBase.abs_cum_le_base
#print axioms MassGap.ZoomBase.zoomBase
#print axioms MassGap.CouplingGen.Along.ZoomBase.zoomBase
#print axioms MassGap.ZoomBase.tcW_mono
#print axioms MassGap.ZoomBase.relCum_rescale
#print axioms MassGap.ZoomBase.zoomSettles_of_base
#print axioms MassGap.ZoomBase.zoomSettles_of_settling
#print axioms MassGap.CouplingGen.Along.ZoomBase.zoomSettles_of_settling
#print axioms MassGap.ZoomBase.zoomSettles_iff_settling
#print axioms MassGap.ZoomBase.coefBase_cfLead
#print axioms MassGap.ZoomBase.cfLead_ne_zero
#print axioms MassGap.ZoomBase.not_coefCtl_exp
#print axioms MassGap.ZoomBase.base_only_unbounded
#print axioms MassGap.ZoomBase.coreWFB_of_coreWZB
#print axioms MassGap.ZoomBase.clayStatementOf_of_zoomBase
