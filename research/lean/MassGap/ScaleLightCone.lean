import Mathlib
import MassGap.ObserverTowerCL

/-!
# MassGap.ScaleLightCone — the zoom settles because finer observers share no light cone

A coarse observer reads a separation `d` through the zoom steps whose spacing `a_k` is at most `d`. A zoom
step `k → k + 1` adds detail at the spacing `a_k`, whose light cone has width about `a_k`; two factors `d`
apart sit in no light cone of width `a_k ≪ d` together, so the new detail moves their connected reading only
through what it leaves at the coarse scale, suppressed by the ratio of the two scales. The observers at
different zooms do not observe the same effects even when their light cones point the same way at the same
width: the fine observer sees only local, the coarse observer only coarse. This module states that mechanism
on the real objects, derives the cluster field `ClusterRoute.ClusterPM` and the (UV) hypothesis from it, and
states the root with it. Declarations are in the namespace `MassGap.ScaleLightCone`.

## 1. A reading that settles along the zoom (proved, general)

`SettlesFrom q r η k₀`: from step `k₀` on, one zoom step moves the reading `q` by at most `r_k^η`, where `r_k`
is the fine scale against the reading's own length. When the ratio halves per step (the spacing halves):

* `settles_step`: `|q_{k₀+m+1} − q_{k₀+m}| ≤ r_{k₀}^η (2^{−η})^m`;
* `settles_tendsto`: `q` converges (`η > 0`);
* **`settles_bound`**: if `r_{k₀} ≤ 1`, then `|q_k| ≤ |q_{k₀}| + (1 − 2^{−η})⁻¹` at every `k ≥ k₀`, uniformly
  in the number `k − k₀` of zoom steps;
* `settlesFrom_zero_unbounded`: at `η = 0` (no suppression) the reading `q_k = k` settles in this sense at
  every ratio and is unbounded, so the rate `η > 0` is what makes the bound uniform in the zoom.

The templates are the Lieb–Robinson bound (an effective light cone with a suppression outside it), the
Nachtergaele–Sims / Hastings–Koma clustering it feeds, and the scale-local multiscale expansions of
Bałaban (four-dimensional Yang–Mills, ultraviolet stability in finite volume), Gawędzki–Kupiainen and
Feldman–Magnen–Rivasseau–Sénéor (two-dimensional Gross–Neveu), where each scale's contribution is local at
its own length and suppressed by a power of the ratio of scales.

## 2. The mechanism on the separated composites

* `treeW γ Kc lam k s F B`: the tree weight `γ^{|B|} |B|^{|B|−2} ∏_{i∈B} (wS(a_k, fᵢ) + a_k) Kcᵢ s^{−λᵢ}` of
  `ClusterPM`; `relCum`: the cumulant of the smeared flowed proxies (`ClusterRoute.clX`) in units of it, the
  connected reading measured relative to its own size.
* `FirstStep N d k₀`: `k₀` is the first zoom step whose spacing reaches the separation, `a_{k₀} ≤ d < a_j`
  for `j < k₀` (`exists_firstStep`).
* **`ZoomSettles Wf c`**: one `θc > 0`, `γ > 0`, `η > 0`, per composite `Kcᵢ > 0`, `λᵢ`; on every continuous
  `d`-separated family of composites, `0 < d ≤ 1`, at every flow scale `0 < s ≤ θc d` and every block `B`,
  at the first step `k₀` of `d`: (the coarse observer) `|relCum_{k₀}| ≤ 1`, and (the zoom) the relative
  reading settles from `k₀` at the ratios `a_k / d` with rate `η`.
* **`clusterPM_of_zoomSettles`**: `ZoomSettles Wf c ⇒ ClusterPM Wf c`, with tree weight
  `(1 + (1 − 2^{−η})⁻¹) γ` and the same `θc`, `Kc`, `λ`.
* `relCum_tendsto_of_zoomSettles`: under `ZoomSettles` the relative reading of every separated family
  converges along the zoom. `ClusterPM` bounds it and does not make it converge (argued), so `ZoomSettles` is
  stronger than `ClusterPM`, not a restatement of it.

The number of zoom steps between `k₀` and `k` grows without bound as the spacing goes to `0`; the
suppression `(a_k / d)^η` makes their sum a geometric series whose total does not depend on `d`, `k` or the
data. `ClusterPM` at every step is reduced to its shape at the one step `k₀` per separation and the
per-step suppression.

## 3. The (UV) reading settles along the zoom

* `windowReading N βs k = 2^k m′(β_k)`, the measured mass in units of the window `2^k`.
* **`ZoomSettlesUV N βs`**: the reading is eventually finite, and for one length `ℓ > 0` (in window units),
  one `η > 0` and one `k₀` it settles from `k₀` at the ratios `2^{−k} / ℓ` (the spacing against the
  reading's length, in window units).
* **`uvConverges_of_zoomSettlesUV`**: `ZoomSettlesUV N βs ⇒ ∃ μ, UVConverges N βs id μ`. This is (UV) with a
  rate: the mechanism supplies the rate, it does not discharge (UV). The length `ℓ` enters only as the
  prefactor `ℓ^{−η}` of the rate.

## 4. The root

`#along_generalize_more` copies `clusterPM_of_zoomSettles` over the coupling family (kernel-checked); no
copy mentions `dyBeta`.

* `CoreInputsAlongWSL N βs`: `ObserverTowerCL.CoreInputsAlongWCL N βs` with the copy of `ZoomSettles Wf cf`
  in place of the copy of `ClusterPM Wf cf`; `coreWCL_of_coreWSL` gives `CoreInputsAlongWCL`.
* **`clayStatementOf_of_zoomSettles`**: `StrongEnd N`, `ZoomSettlesUV` along the towers near `0⁺` and
  `CoreInputsAlongWSL` along the towers near `0⁺` give `ClayStatementOf (SU N)`.

## 5. What the mechanism reaches, and the tests (argued; no declaration)

Reached: `ClusterPM` and (UV). Not reached: the per-channel moments and the plaquette exponential moment of
`ClusterRoute.SubstrateCoreCL`, its asymptotic-freedom kernel, and `ExpandStrong`. A single-point moment of
order `2p` and the small-flow-time expansion are readings at coincident points, inside one light cone common
to every insertion, where the mechanism says nothing; it reads only separated factors. `FlowCovLim`,
`FlowWard`, `ProxyNondeg`, the germ and the three-point clause carry no scale-locality content.

The free massless field. The lattice massless propagator differs from the continuum one by a relative
`O((a/|x|)²)` (Symanzik), so the relative connected reading of separated Wick composites moves by
`O((a_k/d)²)` per zoom step: `η = 2`, with no mass. At the first step the factors sit at least about one
spacing apart and the reading is the lattice propagator at a few lattice units, finite without a mass. The base
clause has `ClusterPM`'s tree shape at that step, so it carries `ClusterRoute` §4's caveat on the number of
legs for the massless propagator. The argument covers flow scales `s ≳ a_k`; at `s ≪ a_k` the artefacts of the
flowed proxy go like `(a_k/s)²`, covered only if `s^{−λ}` absorbs them. UV regularity does not need a gap here.

No decay at large distance. The derived constant `1 + (1 − 2^{−η})⁻¹` does not depend on `d`; the suppression
`(a_k / d)^η` compares the fine scale with the separation, and no clause carries a decay factor in `d`. For a
compact gauge group the base clause reads the state of the first step only through `|ν(O)| ≤ ‖O‖`: once
`θc ≤ min(a₀, 1/2)`, every flow scale it reads is at most one spacing of that step, so under
`MultiScaleOS.CoefBound` it holds in every state at every coupling (`ZoomBase.zoomBase`) and carries no
infrared content of the step. The content of `ZoomSettles` is its settling conjunct (`ZoomBase.ZoomSettling`),
the coarse observer's side of the route, not `StrongEnd`.

The rough tail. `ZoomSettles` bounds the cumulant of a fixed block of a fixed number of separated factors at
each step, a fixed-order quantity, before any limit; it asks no exponential moment and no single-point
moment. At fixed order the floor of `BlFamCore.RoughTail` tends to `0` (`ObserverTowerPM.tendsto_roughFloor`),
so `RoughTail` refutes no clause of `ZoomSettles`, and `ZoomSettles` does not imply `ScaleControlAll`
(`BlFamCore.not_scaleControlAll_of_roughTail` refutes that one).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lower ends and the limit `0⁺`; `1` the unit of the relative reading
(a normalisation, absorbed by `γ`), the top of the separation and the top of the ratio; `1/2` the ratio of consecutive spacings
(`a_{k+1} = a_k / 2`) and of consecutive windows; `2` Cayley's offset in the tree weight and the base of the
window; `η`, `γ`, `θc`, `ℓ`, `Kc`, `λ` existential. The prose of §5 cites `2` the Symanzik order and `2p`
the moment order.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScaleLightCone

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ScalePC MassGap.ScalePM
  MassGap.ClusterRoute MassGap.MeasuredSpacing
open MassGap.ScaleControlFull (zOne)
open MassGap.CouplingTower (UVConverges)

/-! ## 1. A reading that settles along the zoom -/

section Settles

/-- **A reading settles along the zoom from step `k₀`**: from `k₀` on, one zoom step moves the reading `q`
by at most `r_k^η`, `r_k` the fine scale against the reading's own length. DERIVED: `1` the step. -/
def SettlesFrom (q r : ℕ → ℝ) (η : ℝ) (k₀ : ℕ) : Prop :=
  ∀ k, k₀ ≤ k → |q (k + 1) - q k| ≤ r k ^ η

/-- **Halving ratios**: `r_{k₀+m} = r_{k₀} 2^{−m}`. DERIVED: `1/2` the ratio; `2` the halving. -/
theorem ratio_shift {r : ℕ → ℝ} (hr : ∀ k, r (k + 1) = r k / 2) (k₀ : ℕ) :
    ∀ m : ℕ, r (k₀ + m) = r k₀ * (1 / 2) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, hr, ih]
    ring

/-- **The suppression per step**: `r_{k₀+m}^η = r_{k₀}^η (2^{−η})^m` for halving ratios, `r_{k₀} ≥ 0`.
DERIVED: `1/2` the ratio; `2` the halving; `0` the sign. -/
theorem rpow_ratio_shift {r : ℕ → ℝ} (hr : ∀ k, r (k + 1) = r k / 2) {k₀ : ℕ} (h0 : 0 ≤ r k₀) (η : ℝ) :
    ∀ m : ℕ, r (k₀ + m) ^ η = r k₀ ^ η * ((1 / 2 : ℝ) ^ η) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hm : 0 ≤ r (k₀ + m) := by
      rw [ratio_shift hr k₀ m]
      exact mul_nonneg h0 (pow_nonneg (by norm_num) m)
    rw [← add_assoc, hr, show r (k₀ + m) / 2 = r (k₀ + m) * (1 / 2) by ring,
      Real.mul_rpow hm (by norm_num : (0 : ℝ) ≤ 1 / 2), ih]
    ring

/-- **One zoom step from `k₀ + m`**: `|q_{k₀+m+1} − q_{k₀+m}| ≤ r_{k₀}^η (2^{−η})^m`.
DERIVED: `1` the step; `1/2` the ratio; `2` the halving; `0` the sign. -/
theorem settles_step {q r : ℕ → ℝ} {η : ℝ} {k₀ : ℕ} (hq : SettlesFrom q r η k₀)
    (hr : ∀ k, r (k + 1) = r k / 2) (h0 : 0 ≤ r k₀) (m : ℕ) :
    |q (k₀ + m + 1) - q (k₀ + m)| ≤ r k₀ ^ η * ((1 / 2 : ℝ) ^ η) ^ m := by
  rw [← rpow_ratio_shift hr h0 η m]
  exact hq (k₀ + m) (Nat.le_add_right k₀ m)

/-- **A settling reading converges along the zoom** (`η > 0`; geometric increments).
DERIVED: `1/2` the ratio; `2` the halving; `0` the signs. -/
theorem settles_tendsto {q r : ℕ → ℝ} {η : ℝ} {k₀ : ℕ} (hq : SettlesFrom q r η k₀)
    (hr : ∀ k, r (k + 1) = r k / 2) (h0 : 0 ≤ r k₀) (hη : 0 < η) :
    ∃ L : ℝ, Tendsto q atTop (𝓝 L) := by
  have hρ1 : (1 / 2 : ℝ) ^ η < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hη
  have hc : CauchySeq (fun m => q (k₀ + m)) := by
    refine cauchySeq_of_le_geometric ((1 / 2 : ℝ) ^ η) (r k₀ ^ η) hρ1 fun m => ?_
    rw [Real.dist_eq, abs_sub_comm]
    exact settles_step hq hr h0 m
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨L, (tendsto_add_atTop_iff_nat k₀).1 (hL.congr fun m => by rw [add_comm])⟩

/-- **The bound uniform in the zoom**: if `0 ≤ r_{k₀} ≤ 1` and `η > 0`, then
`|q_k| ≤ |q_{k₀}| + (1 − 2^{−η})⁻¹` at every `k ≥ k₀`. DERIVED: `1` the top of the ratio and the geometric
sum; `1/2` the ratio; `2` the halving; `0` the signs. -/
theorem settles_bound {q r : ℕ → ℝ} {η : ℝ} {k₀ : ℕ} (hq : SettlesFrom q r η k₀)
    (hr : ∀ k, r (k + 1) = r k / 2) (h0 : 0 ≤ r k₀) (h1 : r k₀ ≤ 1) (hη : 0 < η) :
    ∀ k, k₀ ≤ k → |q k| ≤ |q k₀| + (1 - (1 / 2 : ℝ) ^ η)⁻¹ := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 / 2 : ℝ) ^ η := ⟨_, rfl⟩
  rw [← hρ]
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact Real.rpow_nonneg (by norm_num) η
  have hρ1 : ρ < 1 := by
    rw [hρ]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hη
  have hrη : r k₀ ^ η ≤ 1 := Real.rpow_le_one h0 h1 hη.le
  have hrη0 : 0 ≤ r k₀ ^ η := Real.rpow_nonneg h0 η
  have hsum : ∀ m : ℕ, |q (k₀ + m)| ≤ |q k₀| + r k₀ ^ η * ∑ i ∈ Finset.range m, ρ ^ i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hs := settles_step hq hr h0 m
      rw [← hρ] at hs
      have htri := abs_sub_abs_le_abs_sub (q (k₀ + m + 1)) (q (k₀ + m))
      show |q (k₀ + m + 1)| ≤ _
      rw [Finset.sum_range_succ, mul_add]
      linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hS : ∑ i ∈ Finset.range m, ρ ^ i ≤ (1 - ρ)⁻¹ := by
    have e : ∑ i ∈ Finset.range m, ρ ^ i = (1 - ρ ^ m) * (1 - ρ)⁻¹ := by
      rw [← geom_sum_mul_neg, mul_assoc, mul_inv_cancel₀ h1ρ.ne', mul_one]
    rw [e]
    have hle : 1 - ρ ^ m ≤ 1 := by linarith [pow_nonneg hρ0 m]
    calc (1 - ρ ^ m) * (1 - ρ)⁻¹ ≤ 1 * (1 - ρ)⁻¹ :=
          mul_le_mul_of_nonneg_right hle (inv_nonneg.2 h1ρ.le)
      _ = (1 - ρ)⁻¹ := one_mul _
  have hprod : r k₀ ^ η * ∑ i ∈ Finset.range m, ρ ^ i ≤ 1 * (1 - ρ)⁻¹ :=
    mul_le_mul hrη hS (Finset.sum_nonneg fun i _ => pow_nonneg hρ0 i) zero_le_one
  linarith [hsum m]

/-- **Without the suppression the zoom does not settle**: at `η = 0` the reading `q_k = k` moves by one
per step, within `r_k^0 = 1` at every ratio, and is unbounded. DERIVED: `0` the rate and the first step;
`1` the unit move. -/
theorem settlesFrom_zero_unbounded (r : ℕ → ℝ) :
    SettlesFrom (fun k => (k : ℝ)) r 0 0 ∧ ¬ ∃ C : ℝ, ∀ k : ℕ, |(k : ℝ)| ≤ C := by
  refine ⟨fun k _ => by simp, fun ⟨C, hC⟩ => ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have h := hC k
  rw [abs_of_nonneg (Nat.cast_nonneg k)] at h
  linarith

end Settles

/-! ## 2. The mechanism on the separated composites -/

variable {N : ℕ}

/-- **The first zoom step whose spacing reaches the separation**: `a_k ≤ d < a_j` for every `j < k`.
DERIVED: no numeral. -/
def FirstStep (N : ℕ) (d : ℝ) (k : ℕ) : Prop :=
  dySpacing N k ≤ d ∧ ∀ j < k, d < dySpacing N j

/-- Every positive separation has a first step. DERIVED: `0` the sign and the limit of the spacing. -/
theorem exists_firstStep (N : ℕ) {d : ℝ} (hd : 0 < d) : ∃ k, FirstStep N d k := by
  classical
  have hex : ∃ k, dySpacing N k ≤ d :=
    ((tendsto_order.1 (tendsto_dySpacing N)).2 d hd).exists.imp fun _ h => h.le
  exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_le.1 (Nat.find_min hex hj)⟩

/-- **The spacing halves per zoom step**, against any length `d`. DERIVED: `2` the halving. -/
theorem spacing_ratio_succ (N : ℕ) (d : ℝ) (k : ℕ) :
    dySpacing N (k + 1) / d = dySpacing N k / d / 2 := by
  unfold dySpacing
  ring

/-- **The tree weight of a block** (`ClusterRoute.ClusterPM`'s right side):
`γ^{|B|} |B|^{|B|−2} ∏_{i∈B} (wS(a_k, fᵢ) + a_k) Kcᵢ s^{−λᵢ}`. DERIVED: `2` Cayley's offset. -/
def treeW [NeZero N] (γ : ℝ) (Kc lam : Ix0 → ℝ) (k : ℕ) (s : ℝ) {n : ℕ}
    (F : Fin n → CDatum (CbR N zOne)) (B : Finset (Fin n)) : ℝ :=
  γ ^ B.card * ((B.card : ℝ) ^ (B.card - 2))
    * ∏ i ∈ B, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1))

/-- **The connected reading relative to its tree weight**: the cumulant of the smeared flowed proxies on
`B` at step `k`, divided by `treeW`. DERIVED: no numeral. -/
def relCum [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (γ : ℝ) (Kc lam : Ix0 → ℝ)
    (k : ℕ) (s : ℝ) {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) (B : Finset (Fin n)) : ℝ :=
  cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B / treeW γ Kc lam k s F B

/-- The tree weight is positive on a non-empty block. DERIVED: `0` the signs. -/
theorem treeW_pos [NeZero N] {γ : ℝ} (hγ : 0 < γ) {Kc : Ix0 → ℝ} (hKc : ∀ i, 0 < Kc i)
    (lam : Ix0 → ℝ) (k : ℕ) {s : ℝ} (hs : 0 < s) {n : ℕ} (F : Fin n → CDatum (CbR N zOne))
    {B : Finset (Fin n)} (hB : B.Nonempty) : 0 < treeW γ Kc lam k s F B := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold treeW
  exact mul_pos (mul_pos (pow_pos hγ _) (pow_pos (Nat.cast_pos.2 (Finset.card_pos.2 hB)) _))
    (Finset.prod_pos fun i _ => mul_pos (add_pos_of_nonneg_of_pos (wS_nonneg ha _) ha)
      (mul_pos (hKc _) (Real.rpow_pos_of_pos (inv_pos.2 hs) _)))

/-- **The zoom settles on separated composites** (the mechanism): one `θc > 0`, `γ > 0`, `η > 0`, per
composite `Kcᵢ > 0`, `λᵢ`; on every continuous `d`-separated family of `n` composites, `0 < d ≤ 1`, every
flow scale `0 < s ≤ θc d` and every non-empty block `B`, at the first step `k₀` whose spacing reaches `d`:
the coarse observer reads `|relCum_{k₀}| ≤ 1`, and each finer zoom step moves the relative reading by at
most `(a_k / d)^η`. DERIVED: `1` the unit of the relative reading and the top of the separation; `0` the
signs. -/
def ZoomSettles [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ (θc γ η : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 < γ ∧ 0 < η ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
      ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ B : Finset (Fin n), B.Nonempty → ∀ k₀ : ℕ, FirstStep N d k₀ →
        |relCum Wf c γ Kc lam k₀ s F B| ≤ 1
          ∧ SettlesFrom (fun k => relCum Wf c γ Kc lam k s F B) (fun k => dySpacing N k / d) η k₀

/-- **`ClusterPM` from the zoom**: `ZoomSettles Wf c` gives `ClusterRoute.ClusterPM Wf c` with tree weight
`(1 + (1 − 2^{−η})⁻¹) γ` (`settles_bound` from the first step). DERIVED: `1` the unit of the relative
reading; `1/2` the ratio; `0` the signs. -/
theorem clusterPM_of_zoomSettles [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ZoomSettles Wf c) : ClusterPM Wf c := by
  obtain ⟨θc, γ, η, Kc, lam, hθc, hγ, hη, hKc, H⟩ := h
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 1 + (1 - (1 / 2 : ℝ) ^ η)⁻¹ := ⟨_, rfl⟩
  have hρ1 : (1 / 2 : ℝ) ^ η < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hη
  have hΓ1 : 1 ≤ Γ := by
    have : 0 ≤ (1 - (1 / 2 : ℝ) ^ η)⁻¹ := inv_nonneg.2 (by linarith)
    linarith
  refine ⟨θc, Γ * γ, Kc, lam, hθc, mul_nonneg (by linarith) hγ.le, hKc,
    fun n F d hd hd1 hcont hsep s hs hsd => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_firstStep N hd
  filter_upwards [eventually_ge_atTop k₀] with k hk B hB
  obtain ⟨hbase, hset⟩ := H n F d hd hd1 hcont hsep s hs hsd B hB k₀ hk₀
  have ha0 : 0 < dySpacing N k₀ := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k₀
  have hrel : |relCum Wf c γ Kc lam k s F B|
      ≤ |relCum Wf c γ Kc lam k₀ s F B| + (1 - (1 / 2 : ℝ) ^ η)⁻¹ :=
    settles_bound hset (spacing_ratio_succ N d) (div_nonneg ha0.le hd.le) ((div_le_one hd).2 hk₀.1) hη k hk
  have hT := treeW_pos hγ hKc lam k hs F hB
  have hR : |relCum Wf c γ Kc lam k s F B| ≤ Γ := by linarith
  have hcum : cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B
      = relCum Wf c γ Kc lam k s F B * treeW γ Kc lam k s F B :=
    (div_mul_cancel₀ (cum (stMom (stateK (NeZero.ne N) k) (clX Wf c k s F)) B) hT.ne').symm
  rw [hcum, abs_mul, abs_of_pos hT]
  have hΓB : Γ ≤ Γ ^ B.card := le_self_pow₀ hΓ1 (Finset.card_pos.2 hB).ne'
  calc |relCum Wf c γ Kc lam k s F B| * treeW γ Kc lam k s F B
      ≤ Γ ^ B.card * treeW γ Kc lam k s F B := mul_le_mul_of_nonneg_right (hR.trans hΓB) hT.le
    _ = (Γ * γ) ^ B.card * ((B.card : ℝ) ^ (B.card - 2))
          * ∏ i ∈ B, ((wS (dySpacing N k) (F i).2 + dySpacing N k) * (Kc (F i).1 * s⁻¹ ^ lam (F i).1)) := by
        unfold treeW
        rw [mul_pow]
        ring

/-- **The relative reading converges along the zoom** under `ZoomSettles`, on every separated family and
block (`settles_tendsto`). DERIVED: `0` the signs; `1` the top of the separation. -/
theorem relCum_tendsto_of_zoomSettles [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    {θc γ η : ℝ} {Kc lam : Ix0 → ℝ} (hη : 0 < η)
    (H : ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
      ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ B : Finset (Fin n), B.Nonempty → ∀ k₀ : ℕ, FirstStep N d k₀ →
        |relCum Wf c γ Kc lam k₀ s F B| ≤ 1
          ∧ SettlesFrom (fun k => relCum Wf c γ Kc lam k s F B) (fun k => dySpacing N k / d) η k₀)
    {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hcont : ContD F)
    (hsep : SepD d F) {s : ℝ} (hs : 0 < s) (hsd : s ≤ θc * d) {B : Finset (Fin n)} (hB : B.Nonempty) :
    ∃ L : ℝ, Tendsto (fun k => relCum Wf c γ Kc lam k s F B) atTop (𝓝 L) := by
  obtain ⟨k₀, hk₀⟩ := exists_firstStep N hd
  have ha0 : 0 < dySpacing N k₀ := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k₀
  exact settles_tendsto (H n F d hd hd1 hcont hsep s hs hsd B hB k₀ hk₀).2 (spacing_ratio_succ N d)
    (div_nonneg ha0.le hd.le) hη

/-! ## 3. The (UV) reading settles along the zoom -/

/-- **The window reading**: the measured mass in units of the window `2^k`, `2^k m′(β_k)`.
DERIVED: `2` the window's base. -/
def windowReading (N : ℕ) [NeZero N] (βs : ℕ → ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * measSpacing (NeZero.ne N) (βs k)

/-- **The window reading settles along the zoom**: it is eventually finite, and for one length `ℓ > 0` in
window units, one `η > 0` and one `k₀`, it settles from `k₀` at the ratios `2^{−k} / ℓ`.
DERIVED: `1/2` the spacing in window units per step; `0` the signs. -/
def ZoomSettlesUV (N : ℕ) [NeZero N] (βs : ℕ → ℝ) : Prop :=
  (∀ᶠ k in atTop, mU (NeZero.ne N) (βs k) ≠ ⊤) ∧
    ∃ (ℓ η : ℝ) (k₀ : ℕ), 0 < ℓ ∧ 0 < η ∧
      SettlesFrom (windowReading N βs) (fun k => (1 / 2 : ℝ) ^ k / ℓ) η k₀

/-- **(UV) from the zoom**: `ZoomSettlesUV N βs` gives `UVConverges N βs id μ` for some `μ`.
DERIVED: `1/2` the ratio; `0` the signs. -/
theorem uvConverges_of_zoomSettlesUV [NeZero N] {βs : ℕ → ℝ} (h : ZoomSettlesUV N βs) :
    ∃ μ : ℝ, UVConverges N βs id μ := by
  obtain ⟨hfin, ℓ, η, k₀, hℓ, hη, hs⟩ := h
  obtain ⟨L, hL⟩ := settles_tendsto hs (fun k => by ring)
    (div_nonneg (pow_nonneg (by norm_num) _) hℓ.le) hη
  exact ⟨L, hfin, hL⟩

end MassGap.ScaleLightCone

end

/-! ### The copy over a coupling family -/

namespace MassGap.ScaleLightCone

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ScaleLightCone.clusterPM_of_zoomSettles

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

end MassGap.ScaleLightCone

/-! ## 4. The root -/

noncomputable section

namespace MassGap.ScaleLightCone

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ObserverTowerCL (CoreInputsAlongWCL clayStatementOf_of_coreObsCL)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` with the zoom mechanism**: `ObserverTowerCL.CoreInputsAlongWCL` with
the copy of `ZoomSettles Wf cf` in place of the copy of `ClusterRoute.ClusterPM Wf cf`, every other field
unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWSL (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    CouplingGen.Along.ClusterRoute.SubstrateCoreCL (cpl βs) W (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

omit [Fact (2 ≤ N)] in
/-- **The zoom bundle gives the cluster bundle** (the copy of `clusterPM_of_zoomSettles` at `cpl βs`).
DERIVED: no numeral. -/
theorem coreWCL_of_coreWSL {βs : ℕ → ℝ} (h : CoreInputsAlongWSL N βs) : CoreInputsAlongWCL N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hz, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE,
    CouplingGen.Along.ScaleLightCone.clusterPM_of_zoomSettles (cpl βs) hz, F⟩

/-- **The root at `SU(N)` from the strong end and the zoom**: `StrongEnd N`, the settling window reading
along the towers near `0⁺` and `CoreInputsAlongWSL` along the towers near `0⁺` give `ClayStatementOf (SU N)`
(`ObserverTowerCL.clayStatementOf_of_coreObsCL`, `uvConverges_of_zoomSettlesUV`, `coreWCL_of_coreWSL`).
DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_zoomSettles (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → CoreInputsAlongWSL N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_coreObsCL hS (hUV.mono fun _ h βs hT => uvConverges_of_zoomSettlesUV (h βs hT))
    (hF.mono fun _ h βs hT => coreWCL_of_coreWSL (h βs hT))

end MassGap.ScaleLightCone

end

#print axioms MassGap.ScaleLightCone.ratio_shift
#print axioms MassGap.ScaleLightCone.rpow_ratio_shift
#print axioms MassGap.ScaleLightCone.settles_step
#print axioms MassGap.ScaleLightCone.settles_tendsto
#print axioms MassGap.ScaleLightCone.settles_bound
#print axioms MassGap.ScaleLightCone.settlesFrom_zero_unbounded
#print axioms MassGap.ScaleLightCone.exists_firstStep
#print axioms MassGap.ScaleLightCone.spacing_ratio_succ
#print axioms MassGap.ScaleLightCone.treeW_pos
#print axioms MassGap.ScaleLightCone.clusterPM_of_zoomSettles
#print axioms MassGap.CouplingGen.Along.ScaleLightCone.clusterPM_of_zoomSettles
#print axioms MassGap.ScaleLightCone.relCum_tendsto_of_zoomSettles
#print axioms MassGap.ScaleLightCone.uvConverges_of_zoomSettlesUV
#print axioms MassGap.ScaleLightCone.coreWCL_of_coreWSL
#print axioms MassGap.ScaleLightCone.clayStatementOf_of_zoomSettles
