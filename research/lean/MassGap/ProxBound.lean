import Mathlib
import MassGap.ZoomBase
import MassGap.CoefPin

/-!
# MassGap.ProxBound — the base of `ZoomSettles` from a bound on the proxies

`ZoomBase` proves the base clause of `ScaleLightCone.ZoomSettles Wf cf` from `MultiScaleOS.CoefBound cf`, and
`CoefPin` proves that the expansion cannot give `CoefBound` (the proxy map has a kernel) and names the escape:
a bound on the proxies, not on the coefficients. This module states that bound, proves the base from it, puts
it in the bundle in place of `CoefBound`, and asks whether the bundle's other clauses give it. Declarations
are in the namespace `MassGap.ProxBound`.

## 1. The clause and the base

* `ProxCtl N P Kc lam`: at every composite `i`, step `k` and flow scale `0 < s ≤ theta0 N` with
  `s ≤ a_k`, `‖P k s i‖ ≤ Kcᵢ s^{−λᵢ}`. These include every pair `(k, s)` the base reads: at the first
  step `k₀` of `0 < d ≤ 1` and `s ≤ theta0 · d`, `s ≤ theta0` and `s ≤ a_{k₀}`
  (`ZoomBase.theta0_mul_le_spacing`). `ProxBoundOf N P`: some `Kc > 0`, `λ` with `ProxCtl`.
* `ProxBound Wf cf = ProxBoundOf N (msProx Wf cf)`: a supremum-norm bound on the flowed proxies.
* `proxBound_of_coefBase`, **`proxBound_of_coefBound`**: `CoefBound cf ⇒ ProxBound Wf cf`, at every flow
  (`‖msFlow_j‖ ≤ a_k^{−d_j} kch_j ≤ s^{−d_j} kch_j` at `s ≤ a_k`).
* **`proxBound_spread`**: `ProxBound Wf (cfSpread cf) ↔ ProxBound Wf cf`; `proxBound_not_coefBound`:
  `cfSpread cfLead` meets `ProxBound` at every flow and fails `CoefBound`. So `ProxBound` is strictly weaker
  than `CoefBound` and invariant under the kernel `CoefPin` exhibits.
* `norm_clX_le_prox`, `abs_cum_le_base_prox`, **`zoomBase_of_proxBound`**: the base clause of `ZoomSettles`
  from `ProxBound`, `θc = theta0 N`, `γ = 2`; `zoomSettles_of_baseP`, **`zoomSettles_of_settling_prox`**:
  `ProxBound` and `ZoomSettling` give `ZoomSettles`. All copied over the coupling family.

## 2. Is `ProxBound` read by the bundle? (the obstruction)

* `window_finite`: at a flow scale `s > 0` the steps `ProxBound` reads, `{k | s ≤ a_k}`, are finitely many
  (`a_k → 0`).
* `TailRead T`: `T` is unchanged when the proxies are changed at finitely many steps at each scale (agreeing
  `∀ᶠ k in atTop` at every `s > 0`).
* **`tailRead_not_proxBound`**: a tail-read clause never gives `ProxBoundOf`: from any `P` meeting it,
  `spike P` (the proxies replaced by `e^{1/s}` on the finite window `s ≤ a_k`) meets it and fails
  `ProxBoundOf`.
* `ExpandMatchOf P z μ`: `ExpandMatch` with `msProx Wf cf` replaced by an arbitrary proxy family `P`;
  `expandMatch_iff_of`: `ExpandMatch Wf cf z μ ↔ ExpandMatchOf (msProx Wf cf) z μ` (the expansion reads `cf`
  only through `msProx`); **`tailRead_expandMatchOf`**: it is tail-read (both conjuncts read `∀ᶠ k in atTop`
  or along `ultra ≤ atTop`, at fixed `s`).
* **`expandMatch_tail_not_proxBound`**: if `ExpandMatch Wf cf z μ`, a proxy family equal to `msProx Wf cf`
  at all but finitely many steps of every scale meets the expansion and fails `ProxBound`. Copied over the
  coupling family.

Treating the proxies as an arbitrary family `P`, `ExpandMatchOf P` does not give `ProxBoundOf P`: it is
unchanged by any change of `P` at finitely many steps of each scale, and `spike P` is such a change that
fails the bound. The spike lies outside the span of the flowed channels (every `msProx` has `stateK k`-value
`0`, the spike has value `e^{1/s}`), so this is a statement about proxy families, not about any realised
coefficient family `cf`. Whether `ExpandMatch Wf cf z μ` gives `ProxBound Wf cf` for a step-independent `cf`
is not decided here. The same holds for each
clause of the bundle that reads `cf` or `Wf` at a fixed scale only eventually in the step (argued, by their
definitions: `FlowCovLim`, `FlowWard`, `ProxyNondeg` read `∀ᶠ k in ultra`; `ApertureBridge`, with
`FreeComparable`'s `LawClause` and the channel moment clause, and `ExpandRF` read `∀ᶠ k in atTop`;
`ProxyGenLimGerm` reads the limit forms `kernB`, `mixB`). The proof uses one property of those clauses,
the tail read; it does not use that `cf` is independent of the step.

The escape the obstruction names. A clause that gives `ProxBound` must read the proxies at the first step
`k₀` of every separation. In the bundle only `ZoomSettling` reads there, and it reads differences
`relCum_{k+1} − relCum_k` relative to a tree weight, not the size at `k₀`. Two further routes are open and not
taken here: (i) a cross-channel frame bound (a Gram lower bound of `{msFlow_j : j ∈ supp}` modulo the kernel
of the proxy map, uniform in the step at the tail, in a norm that reaches the supremum norm), which, with the
step-independence of `cf`, would carry the tail control `ExpandRF` gives to the first step; `FreeComparable`'s `SpecClause` bounds the Gram spectrum of the translates of one channel
(`screen Wf k s j`), not across channels, so it does not give it; (ii) a state-level form (moments of
`msProx` in `stateK k`): `ZoomBase.abs_cum_le_of_mom` needs `|ν(∏_{i∈D} clXᵢ)| ≤ ∏ Mᵢ` with `Mᵢ` free of `|D|`,
which by Hölder is the `L^∞(ν_k)` norm, so the state-level form is not weaker in the tree shape `treeW`
reads, and it is read at the same finite window, so the obstruction applies to it unchanged (argued).

## 3. The root

* `CoreInputsAlongWPB N βs`: `ZoomBase.CoreInputsAlongWZB N βs` with the copy of `ProxBound Wf cf` in place
  of `CoefBound cf`; **`coreWPB_of_coreWZB`** (`WZB ⇒ WPB`, the copy of `proxBound_of_coefBound`),
  `coreWFB_of_coreWPB` (the copy of `zoomSettles_of_settling_prox`), **`clayStatementOf_of_proxBound`**.

Input count. `CoreInputsAlongWZB`: 9 conjuncts (`ApertureBridge`, `ExpandMatch`, `CoefBound`,
`ZoomSettling`, `FlowCovLim`, `FlowWard`, `ProxyNondeg`, `ProxyGenLimGerm`, `ThreePointAtScale`).
`CoreInputsAlongWPB`: the same 9, with `ProxBound` (strictly weaker, kernel-invariant) in place of
`CoefBound`. The coefficient input is weakened, not folded: `expandMatch_tail_not_proxBound` shows the
expansion, read through the proxies alone, does not give it.

## 4. The tests

* `proxBound_cfLead`: `ProxBound` holds at the route's leading coefficients `cfLead` (non-zero at every
  `s ≠ 0`, `ZoomBase.cfLead_ne_zero`), at every flow: met by a non-trivial witness.
* `tailRead_not_proxBound` (its second conjunct): `ProxBoundOf` fails at `spike P` for every `P`, so the
  clause excludes growth faster than every power of `1/s` and is not vacuous on proxy families.
* `proxBound_not_coefBound`: `ProxBound` does not give `CoefBound`, at every flow.
* The `ProxBound` hypothesis of `zoomBase_of_proxBound` carries the moment bound of `abs_cum_le_of_mom`,
  whose hypothesis is load-bearing (`ZoomBase.mom_bound_loadBearing`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the first step and the limit `0⁺`; `1` the unit of the relative
reading, the top of the separation and the unit observable; `2` the tree weight of the Möbius count (as in
`ZoomBase`); `1/2` the ratio of consecutive spacings (in `theta0`); `e` and the exponent `1/s` only in the spike, a choice of growth faster than every power; `Kc`,
`λ` existential.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ProxBound

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.PreObserver MassGap.CompositesBuild MassGap.ClayData MassGap.ReflAvg
  MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll MassGap.MultiScaleOS
  MassGap.ScalePM MassGap.ClusterRoute MassGap.ScaleLightCone MassGap.ZoomBase
open MassGap.ScaleControlFull (zOne)

variable {N : ℕ}

/-! ## 1. The clause and the base -/

variable (N) in
/-- **The proxy control**: `‖P k s i‖ ≤ Kcᵢ s^{−λᵢ}` at every `i`, `k` and `0 < s ≤ theta0 N`, `s ≤ a_k`.
DERIVED: `0` the sign of the scale. -/
def ProxCtl (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) (Kc lam : Ix0 → ℝ) : Prop :=
  ∀ (i : Ix0) (k : ℕ) (s : ℝ), 0 < s → s ≤ theta0 N → s ≤ dySpacing N k →
    ‖P k s i‖ ≤ Kc i * s⁻¹ ^ lam i

variable (N) in
/-- **The proxy bound of a proxy family**: some `Kc > 0`, `λ` with `ProxCtl`. DERIVED: `0` the sign. -/
def ProxBoundOf (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) : Prop :=
  ∃ Kc lam : Ix0 → ℝ, (∀ i, 0 < Kc i) ∧ ProxCtl N P Kc lam

/-- **The proxy bound**: `ProxBoundOf` at the flowed proxies `msProx Wf cf`. DERIVED: no numeral. -/
def ProxBound [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ProxBoundOf N (msProx Wf cf)

/-- **The coefficient clause of the base gives the proxy control**: `‖msProxᵢ‖ ≤ ∑_j |c_{ij}| ‖msFlow_j‖`,
`‖msFlow_j‖ ≤ a_k^{−d_j} kch_j ≤ s^{−d_j} kch_j` at `s ≤ a_k`. DERIVED: no numeral. -/
theorem proxCtl_of_coefBase [NeZero N] (Wf : ℝ → ConfFlow N) {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {Kc lam : Ix0 → ℝ} (hctl : CoefBase N c Kc lam) : ProxCtl N (msProx Wf c) Kc lam :=
  fun i k s hs hsθ hsa =>
    (norm_msProx_le Wf c k s i).trans
      ((Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        ((norm_msFlow_le Wf k s j).trans ((mul_comm _ _).le.trans
          (mul_le_mul_of_nonneg_left (inv_pow_le_rpow hs hsa _) (kch_nonneg j)))) (abs_nonneg _)).trans
        (hctl i s hs hsθ))

/-- DERIVED: no numeral. -/
theorem proxBound_of_coefBase [NeZero N] (Wf : ℝ → ConfFlow N) {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {Kc lam : Ix0 → ℝ} (hK : ∀ i, 0 < Kc i) (hctl : CoefBase N c Kc lam) : ProxBound Wf c :=
  ⟨Kc, lam, hK, proxCtl_of_coefBase Wf hctl⟩

/-- **`CoefBound` gives `ProxBound`**, at every flow. DERIVED: no numeral. -/
theorem proxBound_of_coefBound [NeZero N] (Wf : ℝ → ConfFlow N) {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hC : CoefBound c) : ProxBound Wf c := by
  obtain ⟨Kc, lam, hK, hctl⟩ := coefBase_of_coefBound (N := N) hC
  exact proxBound_of_coefBase Wf hK hctl

/-- **`ProxBound` is invariant under the kernel of the proxy map.** DERIVED: no numeral. -/
theorem proxBound_spread [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) :
    ProxBound Wf (CoefPin.cfSpread cf) ↔ ProxBound Wf cf := by
  unfold ProxBound
  rw [CoefPin.msProx_spread]

/-- **The smeared proxy at the first step from the proxy control**: `‖clXᵢ‖ ≤ (wS(a_{k₀}, fᵢ) + a_{k₀})
Kcᵢ s^{−λᵢ}` at every `0 < s ≤ theta0 · d`. DERIVED: `1` the top of the separation. -/
theorem norm_clX_le_prox [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {Kc lam : Ix0 → ℝ} (hP : ProxCtl N (msProx Wf c) Kc lam) {n : ℕ} (F : Fin n → CDatum (CbR N zOne))
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) {s : ℝ} (hs : 0 < s) (hsd : s ≤ theta0 N * d) {k : ℕ}
    (hk : FirstStep N d k) (i : Fin n) :
    ‖clX Wf c k s F i‖
      ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hsa : s ≤ dySpacing N k := hsd.trans (theta0_mul_le_spacing hd hd1 hk)
  have hsθ : s ≤ theta0 N := hsd.trans (mul_le_of_le_one_right theta0_pos.le hd1)
  exact (norm_clX_le Wf c k s F i).trans
    (mul_le_mul (le_add_of_nonneg_right ha.le) (hP (F i).1 k s hs hsθ hsa) (norm_nonneg _)
      (add_nonneg (wS_nonneg ha _) ha.le))

/-- **The base cumulant bound from the proxy control**, in the state of the first step whatever its
coupling. DERIVED: `2` the tree weight of the Möbius count. -/
theorem abs_cum_le_base_prox [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {Kc lam : Ix0 → ℝ} (hKc : ∀ i, 0 < Kc i) (hP : ProxCtl N (msProx Wf c) Kc lam) {n : ℕ}
    (F : Fin n → CDatum (CbR N zOne)) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) {s : ℝ} (hs : 0 < s)
    (hsd : s ≤ theta0 N * d) {k : ℕ} (hk : FirstStep N d k) (B : Finset (Fin n)) (hB : B.Nonempty) :
    |cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B| ≤ treeW 2 Kc lam k s F B := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hM0 : ∀ i : Fin n, 0 ≤ (wS (dySpacing N k) (F i).2 + dySpacing N k)
      * (Kc (F i).1 * s⁻¹ ^ lam (F i).1) := fun i =>
    mul_nonneg (add_nonneg (wS_nonneg ha _) ha.le)
      (mul_nonneg (hKc _).le (Real.rpow_nonneg (inv_nonneg.2 hs.le) _))
  have h := abs_cum_le_tree
    (abs_stMom_le (stateK (NeZero.ne N) k) (clX Wf c k s F) _ hM0
      (norm_clX_le_prox hP F hd hd1 hs hsd hk)) hM0 hB
  refine h.trans (le_of_eq ?_)
  unfold treeW
  ring

/-- **The base clause of `ZoomSettles` from `ProxBound`**: `θc = theta0 N`, `γ = 2`. DERIVED: `2` the tree
weight; `1` the unit of the relative reading and the top of the separation; `0` the signs. -/
theorem zoomBase_of_proxBound [NeZero N] (Wf : ℝ → ConfFlow N) {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hPB : ProxBound Wf c) :
    ∃ (θc γ : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 < γ ∧ (∀ i, 0 < Kc i) ∧
      ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 →
        ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ B : Finset (Fin n), B.Nonempty → ∀ k₀ : ℕ, FirstStep N d k₀ →
          |relCum Wf c γ Kc lam k₀ s F B| ≤ 1 := by
  obtain ⟨Kc, lam, hKc, hP⟩ := hPB
  refine ⟨theta0 N, 2, Kc, lam, theta0_pos, two_pos, hKc,
    fun n F d hd hd1 s hs hsd B hB k₀ hk₀ => ?_⟩
  have hT := treeW_pos two_pos hKc lam k₀ hs F hB
  rw [relCum, abs_div, abs_of_pos hT, div_le_one hT]
  exact abs_cum_le_base_prox hKc hP F hd hd1 hs hsd hk₀ B hB

/-- **`ZoomSettles` from the proxy control and the settling**, with `θc = min(theta0 N, θ₁)`,
`γ = max(2, γ₁)` and the pointwise maxima of the constants (`ZoomBase.zoomSettles_of_base` with the proxy
control in place of the coefficient clause). DERIVED: `2` the base tree weight; `1` the unit of the relative
reading, the top of the separation and of the flow scale; `1/2` the ratio; `0` the signs. -/
theorem zoomSettles_of_baseP [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {Kc₀ lam₀ : Ix0 → ℝ} (hK₀ : ∀ i, 0 < Kc₀ i) (hP : ProxCtl N (msProx Wf c) Kc₀ lam₀)
    (h : ZoomSettling Wf c) : ZoomSettles Wf c := by
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
    refine (abs_cum_le_base_prox hK₀ hP F hd hd1 hs
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

/-- **The split of `ZoomSettles` at the proxy bound**: `ProxBound Wf c` and `ZoomSettling Wf c` give
`ZoomSettles Wf c`. DERIVED: no numeral. -/
theorem zoomSettles_of_settling_prox [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hPB : ProxBound Wf c) (h : ZoomSettling Wf c) : ZoomSettles Wf c := by
  obtain ⟨Kc₀, lam₀, hK₀, hP⟩ := hPB
  exact zoomSettles_of_baseP hK₀ hP h

/-! ### The tests of §1 -/

/-- **`ProxBound` holds at the leading coefficients**, at every flow. DERIVED: no numeral. -/
theorem proxBound_cfLead [NeZero N] (Wf : ℝ → ConfFlow N) : ProxBound Wf FlowChoice.cfLead :=
  proxBound_of_coefBound Wf FlowChoice.coefBound_cfLead

/-- **`ProxBound` is strictly weaker than `CoefBound`**: `cfSpread cfLead` meets the first and fails the
second, at every flow. DERIVED: no numeral. -/
theorem proxBound_not_coefBound [NeZero N] (Wf : ℝ → ConfFlow N) :
    ProxBound Wf (CoefPin.cfSpread FlowChoice.cfLead) ∧ ¬ CoefBound (CoefPin.cfSpread FlowChoice.cfLead) :=
  ⟨(proxBound_spread Wf _).2 (proxBound_cfLead Wf), CoefPin.not_coefBound_spread _⟩

/-! ## 2. The obstruction -/

variable (N) in
/-- **The window `ProxBound` reads at a scale is finite**: `{k | s ≤ a_k}` at `s > 0`. DERIVED: `0` the
limit of the spacing. -/
theorem window_finite {s : ℝ} (hs : 0 < s) : {k : ℕ | s ≤ dySpacing N k}.Finite := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_dySpacing N).eventually (gt_mem_nhds hs))
  refine (Set.finite_lt_nat K).subset fun k hk => ?_
  exact not_le.1 fun h => absurd (show s ≤ dySpacing N k from hk) (not_le.2 (hK k h))

variable (N) in
/-- **A tail read**: `T` is unchanged by a change of the proxies at finitely many steps of each scale.
DERIVED: `0` the sign of the scale. -/
def TailRead (T : (ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) → Prop) : Prop :=
  ∀ P Q : ℕ → ℝ → Ix0 → C(Cfg N, ℝ), (∀ s : ℝ, 0 < s → ∀ᶠ k in atTop, P k s = Q k s) → T P → T Q

/-- **The spike**: the proxies replaced by `e^{1/s}` times the unit observable on the window `s ≤ a_k`.
DERIVED: `1` the unit observable and the coefficient of `1/s`; `e` the base: a choice, since any growth faster
than every power of `1/s` serves (`tendsto_exp_div_rpow_atTop`). -/
def spike (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) : ℕ → ℝ → Ix0 → C(Cfg N, ℝ) := fun k s i =>
  if s ≤ dySpacing N k then Real.exp s⁻¹ • (1 : C(Cfg N, ℝ)) else P k s i

/-- The spike agrees with `P` off the window. DERIVED: `0` the limit of the spacing. -/
theorem spike_eventually (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, spike P k s = P k s :=
  ((tendsto_dySpacing N).eventually (gt_mem_nhds hs)).mono fun _ hk =>
    funext fun _ => if_neg (not_le.2 hk)

/-- **The spike fails the proxy bound**, at every `P`. DERIVED: `1` the floor of the test point and the
unit observable; `0` the first step and the signs. -/
theorem not_proxBoundOf_spike [NeZero N] (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) : ¬ ProxBoundOf N (spike P) := by
  rintro ⟨Kc, lam, -, hQ⟩
  let i : Ix0 := eI fun _ => 0
  have hθ : 0 < min (theta0 N) (dySpacing N 0) :=
    lt_min theta0_pos (dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 0)
  obtain ⟨x, hx1, hx2⟩ :=
    (((tendsto_exp_div_rpow_atTop (lam i)).eventually_gt_atTop (Kc i)).and
      (eventually_ge_atTop (max (min (theta0 N) (dySpacing N 0))⁻¹ 1))).exists
  have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx2)
  have hsθ : x⁻¹ ≤ min (theta0 N) (dySpacing N 0) := by
    rw [inv_le_comm₀ hx0 hθ]
    exact (le_max_left _ _).trans hx2
  have hw : x⁻¹ ≤ dySpacing N 0 := hsθ.trans (min_le_right _ _)
  have hb := hQ i 0 x⁻¹ (inv_pos.2 hx0) (hsθ.trans (min_le_left _ _)) hw
  have hS : spike P 0 x⁻¹ i = Real.exp x • (1 : C(Cfg N, ℝ)) := by
    unfold spike
    rw [if_pos hw, inv_inv]
  rw [hS, inv_inv] at hb
  have hn : Real.exp x ≤ ‖Real.exp x • (1 : C(Cfg N, ℝ))‖ := by
    have h := ContinuousMap.norm_coe_le_norm (Real.exp x • (1 : C(Cfg N, ℝ))) (fun _ => 1)
    rw [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos x)] at h
    exact h
  have key : Real.exp x / x ^ lam i ≤ Kc i := by
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)]
    linarith
  exact absurd key (not_le.2 hx1)

/-- **A tail-read clause never gives the proxy bound**: from any `P` meeting `T`, the spike meets `T`, fails
`ProxBoundOf` and agrees with `P` at all but finitely many steps of each scale. DERIVED: no numeral. -/
theorem tailRead_not_proxBound [NeZero N] {T : (ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) → Prop} (hT : TailRead N T)
    {P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)} (hP : T P) :
    ∃ Q, T Q ∧ ¬ ProxBoundOf N Q ∧ ∀ s : ℝ, 0 < s → ∀ᶠ k in atTop, Q k s = P k s :=
  ⟨spike P, hT P (spike P) (fun _ hs => (spike_eventually P hs).mono fun _ h => h.symm) hP,
    not_proxBoundOf_spike P, fun _ hs => spike_eventually P hs⟩

/-- The flowed reading of a proxy family. DERIVED: no numeral. -/
def latP [NeZero N] (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) (k : ℕ) (s : ℝ) {ι : Type} [Fintype ι]
    (F : ι → CDatum (CbR N zOne)) : ℝ :=
  stateK (NeZero.ne N) k (∏ i, smear (dySpacing N k) (P k s (F i).1) (F i).2)

/-- The proxy product of a proxy family. DERIVED: no numeral. -/
def proxBP [NeZero N] (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) (k : ℕ) (s : ℝ) (Q : TMonoG Ix0) : C(Cfg N, ℝ) :=
  ∏ i, smear (dySpacing N k) (P k s (Q.2 i).1) (Q.2 i).2

/-- **`ExpandMatch` at a proxy family**: `ExpandRF` and `RPGerm` with `msProx Wf cf` replaced by `P`.
DERIVED: `0` the plane and the limit point. -/
def ExpandMatchOf [NeZero N] (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) (z : Chan → ℕ → ℝ) (μ : OffMix) : Prop :=
  (∃ (θ ε : ℝ) (Kr κr : Ix0 → ℝ), 0 < θ ∧ 0 < ε ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (d : ℝ), 0 < d →
      ContD F → SepD d F → ∀ s : ℝ, 0 < s → s ≤ θ * d → ∀ᶠ k in atTop,
        |latC (NeZero.ne N) (CRen N z μ) k F - latP P k s F|
          ≤ (s / d) ^ ε * ((Fintype.card ι).factorial : ℝ)
            * ∏ i, (Kr (F i).1 * ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)))
  ∧ ∀ (R : TSepG (CRen N z μ).Ix 0) (η : ℝ), 0 < η →
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      proxBP P k s R.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k R.1) - proxBP P k s R.1)
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k R.1) - proxBP P k s R.1)
        ≤ η

/-- **The expansion reads `cf` only through the proxies.** DERIVED: no numeral. -/
theorem expandMatch_iff_of [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (z : Chan → ℕ → ℝ) (μ : OffMix) :
    ExpandMatch.ExpandMatch Wf cf z μ ↔ ExpandMatchOf (msProx Wf cf) z μ :=
  Iff.rfl

/-- **The expansion is a tail read.** DERIVED: `0` the limit point. -/
theorem tailRead_expandMatchOf [NeZero N] (z : Chan → ℕ → ℝ) (μ : OffMix) :
    TailRead N (fun P => ExpandMatchOf P z μ) := by
  rintro P Q hPQ ⟨⟨θ, ε, Kr, κr, hθ, hε, H⟩, hG⟩
  have hu : (ultra : Filter ℕ) ≤ atTop := by
    unfold ultra
    exact Ultrafilter.of_le _
  refine ⟨⟨θ, ε, Kr, κr, hθ, hε, fun ι _ _ F d hd hc hsep s hs hsd => ?_⟩, fun R η hη => ?_⟩
  · filter_upwards [H ι F d hd hc hsep s hs hsd, hPQ s hs] with k hk hk'
    unfold latP at hk ⊢
    rwa [← hk']
  · filter_upwards [hG R η hη, self_mem_nhdsWithin] with s hs hs0
    filter_upwards [hs, hu (hPQ s hs0)] with k hk hk'
    unfold proxBP at hk ⊢
    rwa [← hk']

/-- **The expansion does not give the proxy bound**: if `ExpandMatch Wf cf z μ`, a proxy family equal to
`msProx Wf cf` at all but finitely many steps of each scale meets the expansion and fails `ProxBoundOf`.
DERIVED: no numeral. -/
theorem expandMatch_tail_not_proxBound [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandMatch.ExpandMatch Wf cf z μ) :
    ∃ Q, ExpandMatchOf Q z μ ∧ ¬ ProxBoundOf N Q
      ∧ ∀ s : ℝ, 0 < s → ∀ᶠ k in atTop, Q k s = msProx Wf cf k s :=
  tailRead_not_proxBound (tailRead_expandMatchOf z μ) ((expandMatch_iff_of Wf cf z μ).1 hE)

end MassGap.ProxBound

end

/-! ### The copy over a coupling family -/

namespace MassGap.ProxBound

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ProxBound.zoomSettles_of_settling_prox
  MassGap.ProxBound.zoomBase_of_proxBound MassGap.ProxBound.proxBound_of_coefBound
  MassGap.ProxBound.expandMatch_tail_not_proxBound

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

end MassGap.ProxBound

/-! ## 3. The root -/

noncomputable section

namespace MassGap.ProxBound

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
/-- **The bridge bundle with the proxy bound**: `ZoomBase.CoreInputsAlongWZB` with the copy of
`ProxBound Wf cf` in place of `CoefBound cf`, every other field unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWPB (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.FreeBridge.ApertureBridge (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.ExpandMatch.ExpandMatch (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ProxBound.ProxBound (cpl βs) Wf cf
      ∧ CouplingGen.Along.ZoomBase.ZoomSettling (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

omit [Fact (2 ≤ N)] in
/-- **The coefficient bundle gives the proxy bundle** (the copy of `proxBound_of_coefBound` at `cpl βs`).
DERIVED: no numeral. -/
theorem coreWPB_of_coreWZB {βs : ℕ → ℝ} (h : ZoomBase.CoreInputsAlongWZB N βs) :
    CoreInputsAlongWPB N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, hC, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE,
    CouplingGen.Along.ProxBound.proxBound_of_coefBound (cpl βs) Wf hC, F⟩

omit [Fact (2 ≤ N)] in
/-- **The proxy bundle gives the bridge bundle** (the copy of `zoomSettles_of_settling_prox` at `cpl βs`).
DERIVED: no numeral. -/
theorem coreWFB_of_coreWPB {βs : ℕ → ℝ} (h : CoreInputsAlongWPB N βs) :
    FreeBridge.CoreInputsAlongWFB N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, hP, hS, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE,
    CouplingGen.Along.ProxBound.zoomSettles_of_settling_prox (cpl βs) hP hS, F⟩

/-- **The root at `SU(N)` with the proxy bound**: `StrongEnd N`, the settling window reading and
`CoreInputsAlongWPB` along the towers near `0⁺` give `ClayStatementOf (SU N)`
(`FreeBridge.clayStatementOf_of_freeBridge`, `coreWFB_of_coreWPB`). DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_proxBound (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWPB N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  FreeBridge.clayStatementOf_of_freeBridge hS hUV (hF.mono fun _ h βs hT => coreWFB_of_coreWPB (h βs hT))

end MassGap.ProxBound

end

#print axioms MassGap.ProxBound.proxCtl_of_coefBase
#print axioms MassGap.ProxBound.proxBound_of_coefBound
#print axioms MassGap.ProxBound.proxBound_spread
#print axioms MassGap.ProxBound.norm_clX_le_prox
#print axioms MassGap.ProxBound.abs_cum_le_base_prox
#print axioms MassGap.ProxBound.zoomBase_of_proxBound
#print axioms MassGap.ProxBound.zoomSettles_of_baseP
#print axioms MassGap.ProxBound.zoomSettles_of_settling_prox
#print axioms MassGap.ProxBound.proxBound_cfLead
#print axioms MassGap.ProxBound.proxBound_not_coefBound
#print axioms MassGap.ProxBound.window_finite
#print axioms MassGap.ProxBound.not_proxBoundOf_spike
#print axioms MassGap.ProxBound.tailRead_not_proxBound
#print axioms MassGap.ProxBound.expandMatch_iff_of
#print axioms MassGap.ProxBound.tailRead_expandMatchOf
#print axioms MassGap.ProxBound.expandMatch_tail_not_proxBound
#print axioms MassGap.CouplingGen.Along.ProxBound.zoomBase_of_proxBound
#print axioms MassGap.CouplingGen.Along.ProxBound.zoomSettles_of_settling_prox
#print axioms MassGap.CouplingGen.Along.ProxBound.proxBound_of_coefBound
#print axioms MassGap.CouplingGen.Along.ProxBound.expandMatch_tail_not_proxBound
#print axioms MassGap.ProxBound.coreWPB_of_coreWZB
#print axioms MassGap.ProxBound.coreWFB_of_coreWPB
#print axioms MassGap.ProxBound.clayStatementOf_of_proxBound
