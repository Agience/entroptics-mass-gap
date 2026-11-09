import Mathlib
import MassGap.ProxBound

/-!
# MassGap.ConstructFold — the nine flowed-composite clauses and `ZoomSettlesUV` against the construction facts

`FinalBridge` splits the root's inputs into the mass read `B`, the ultraviolet half `ZoomSettlesUV` and the nine
conjuncts of `ProxBound.CoreInputsAlongWPB`. This module asks for their common source in Lüscher's gradient-flow
framework, tries the candidate single clause, and states what does and does not fold. Declarations are in the
namespace `MassGap.ConstructFold`. The theorems are at the base definitions; the bundle reads their
`CouplingGen.Along` copies at `cpl βs`, and the copies made here are listed in §5.

The five construction facts:

* (A) the continuum limit of the flowed composites exists at every fixed flow time `s > 0` (Lüscher 2010/2011:
  the flowed gauge field needs no renormalisation);
* (B) the small-flow-time expansion (Lüscher, Suzuki): composites as flowed fields with coefficients and a
  remainder;
* (C) continuum symmetry: `O(4)` covariance and the Ward identities;
* (D) non-triviality;
* (E) scale settling in the ultraviolet (asymptotic freedom, Bałaban's block-spin control).

## 1. The instance map (the definitions are read; the assignment of each part to (A)–(E) is interpretive)

Each entry names the definition, what it reads, and the fact it is an instance of.

* `FreeBridge.ApertureBridge z b Wf` (`ApertureBridgeAt (b0 N)`). Four parts, three facts. `FreeComparable Wf b`
  (law and spectral comparison of the flowed channels with the free law, at every `s ∈ (0, b]`, eventually in the
  step) and the plaquette clause at `b` (`|⟨plaq⟩_k| ≤ E a_k⁴`, a bounded second moment of `msFlow_b`) are (A):
  finiteness of flowed fields at fixed flow time, uniformly in the cutoff. The channel second-moment profile
  `⟨msFlow_j(s)²⟩ ≤ (σ runG(s)^{anom} / s^{mDim j})²` is (A) for its finiteness and (B) for its shape in `s`
  (the anomalous scaling the expansion predicts). The kernel clause `r⁸ G(r) / (trTree · runG(r)²) → 1` as
  `r → 0⁺` is (E), asymptotic freedom of the continuum two-point kernel. `ApertureBridge` is not one fact.
* `ExpandMatch.ExpandMatch Wf cf z μ = ExpandRF ∧ RPGerm`: (B), the expansion's remainder bound and its
  reflection-norm germ. Reads `k → ∞` at fixed `s`, then `s → 0⁺` (`ProxBound.tailRead_expandMatchOf`).
* `ProxBound.ProxBound Wf cf`: `‖msProx_k(s)ᵢ‖ ≤ Kcᵢ s^{−λᵢ}` on the window `s ≤ a_k`. (B) at the cutoff: the
  size of the expansion's coefficients, polynomial in `1/s` (Suzuki's coefficients are powers of `s` times
  powers of the running coupling). It reads the finite window `{k | s ≤ a_k}` (`ProxBound.window_finite`), not
  the continuum limit. In the bundle it is consumed only by the base of `ZoomSettles`
  (`ProxBound.coreWFB_of_coreWPB`), and given `ZoomSettling` that base is an (A) statement (§3).
* `ZoomBase.ZoomSettling Wf cf`: the relative connected read of the smeared flowed proxies settles from the
  first step `k₀` of every separation, with rate `(a_k / d)^η`. (A) with a rate (a Symanzik-type rate of
  approach to the continuum limit at fixed `s`); it gives the existence of the limit
  (`zoomSettling_limit_exists`), and is not given by it (§2).
* `FlowCovN.FlowCovLim Wf cf`: (C), `O(4)`; under `ExpandMatch` it is `CovC` (`FlowSym`).
* `WardFromLattice.FlowWard Wf cf`: (C), translation Ward; under `ExpandMatch` it is `WardT` (`FlowSym`).
* `NondegFromProxy.ProxyNondeg Wf cf`: (D), a separated two-point lower bound along `s → 0⁺`, `ultra`.
* `ProxyGenLimN.ProxyGenLimGerm W b Wf cf r`: none of (A)–(E). It reads only the limit forms `kernB`, `mixB`
  (so it sits on the (A) side), but its content is generation: the small-`s` proxies lie, in the limit
  reflection form, near the span of the margin monomials of the observer `W = Wf b`; under the core it is
  `ApproxK` (`ProxyGenLimN.approxK_iff_limGerm`). The flow smooths forward, so this is a density statement
  (the time-slice / Reeh–Schlieder kind), not the expansion.
* `NonGaussFromScale.ThreePointAtScale hN ℓ`: (D), a three-point lower bound `κ a_k¹²` on the bare Wilson
  states (non-Gaussianity).
* `ScaleLightCone.ZoomSettlesUV N βs`: (E), the window reading `2^k m′(β_k)` along a coupling tower is
  eventually finite and settles with a rate.

Grouped: (A) the finiteness parts of `ApertureBridge`, `ZoomSettling`, and the role of `ProxBound`; (B) the
profile part of `ApertureBridge`, `ExpandMatch`, `ProxBound`; (C) `FlowCovLim`, `FlowWard`; (D) `ProxyNondeg`,
`ThreePointAtScale`; (E) `ZoomSettlesUV`, the kernel part of `ApertureBridge`. `ProxyGenLimGerm` is in no group.

## 2. The candidate single clause (A) + (B), checked (proved)

`FlowLimRemOf P z μ`, on a proxy family `P`: the expansion `ProxBound.ExpandMatchOf P z μ` (remainder bound and
germ) and, at every fixed `s > 0` and every finite family, the flowed reading `latP P k s F` converges as
`k → ∞` (Lüscher's fixed-`s` limit).

* `tailRead_flowLimRemOf`: the candidate is a tail read (unchanged by a change of the proxies at finitely many
  steps of each scale).
* `flowLimRem_not_proxBound`: it does not give `ProxBoundOf`: from any `P` meeting it, the spike of
  `ProxBound.tailRead_not_proxBound` meets it and fails the bound. As in `ProxBound` §2 this is a statement
  about proxy families, not about a realised coefficient family.
* `firstStep_change_not_settles`: settling from a prescribed first step is not a tail statement: changing a
  read at the one step `k₀` (and nowhere else) defeats `SettlesFrom … η k₀` at every rate `η > 0` when
  `r_{k₀} ≤ 1`, and `r_{k₀} = a_{k₀}/d ≤ 1` at the first step of `d`. So no clause that reads only a tail of the relative
  read sequence gives settling from `k₀`
  (proved at the level of the read sequence; the realised `relCum` is not constructed here).
* `zoomSettling_limit_exists`: the converse direction holds: `ZoomSettling` gives the zoom limit of every
  relative connected read it controls. (A) for the cumulant read is contained in `ZoomSettling`, not a source of it.
* `ApertureBridge`'s moment clause reads the single channels `msFlow_j`; the candidate reads the proxies
  `msProx = Σ_j cf_{ij} msFlow_j`, and the proxy map has a kernel (`CoefPin`), so the channels are not recovered
  from the proxies (argued). A version of the candidate that carries the channel moments as a conjunct is a
  relabelled conjunction.

Plainly: the candidate does not give `ProxBoundOf` on proxy families (proved). It does not give settling from a
prescribed first step for arbitrary read sequences (proved; whether `relCum` realises the changed sequence is not
constructed). That it does not give `ApertureBridge`'s moment clause is argued.

## 3. The exchange for `ProxBound` (proved: `ProxBound ∧ ZoomSettling ⇒ ZoomSettlingLim`; not a fold; whether the implication is strict is not decided)

`relCum` scales as `γ^{−|B|}` in the tree weight (`relCum_rescale`), and `SettlesFrom` with the halving ratio
fixes the distance from the first step to the limit (`settles_dist_le`, `≤ (1 − 2^{−η})⁻¹`). So, under settling,
the base clause `|relCum_{k₀}| ≤ 1` (a read at the first step, in the lattice window) is the same as a uniform
bound on the zoom limit, after rescaling `γ` by `1 + |M| + (1 − 2^{−η})⁻¹`:

* `ZoomSettlingLim Wf c`: `ZoomSettling` with, at the same witnesses, every zoom limit `L` of the relative read
  bounded by one `M`.
* `zoomSettles_of_zoomSettlingLim`, `zoomSettlingLim_of_zoomSettles`, `zoomSettles_iff_zoomSettlingLim`:
  `ZoomSettles Wf c ↔ ZoomSettlingLim Wf c`.
* `zoomSettlingLim_of_proxBound`: `ProxBound ∧ ZoomSettling ⇒ ZoomSettlingLim`.

So what the base of `ZoomSettles` takes from `ProxBound` is a uniform tree-graph bound on the continuum limit of
the relative connected read: an (A) statement. This restates the input in a form that reads the zoom limit instead
of the first step; it removes none. `ZoomSettlingLim` is equivalent to `ZoomSettles`, which `ProxBound ∧ ZoomSettling`
already gives; whether `ZoomSettles` gives `ProxBound` back is not decided.
`ZoomSettlingLim` is `ZoomSettling` with one more conjunct at shared witnesses, so writing the bundle with it in
place of `ProxBound ∧ ZoomSettling` would be a relabelled conjunction. Whether `ZoomSettlingLim` is strictly
weaker than `ProxBound ∧ ZoomSettling` is not decided here.

Load tests: `settles_const`: a constant read `M` settles at every rate, from every step, with limit `M`; so
settling fixes no bound on the limit, and the limit-bound conjunct of `ZoomSettlingLim` is load-bearing. The
constant `0` is the read of a Gaussian (free) state at every block of size `≥ 3` (argued: the connected
correlators of a Gaussian field beyond order two vanish); it meets `ZoomSettlingLim`'s read with `M = 0`.
`firstStep_change_not_settles` shows the settling conjunct is not a tail read. `ScaleLightCone.settlesFrom_zero_unbounded`
shows the rate `η > 0` used by `settles_dist_le` is load-bearing.

## 4. Per pair, plainly

* (A) `ZoomSettling` / the finiteness of `ApertureBridge`: different reads (cumulants of smeared proxies against
  second moments of single channels); neither implies the other on the tree's statements (argued). The candidate
  (A) clause gives neither (§2).
* (B) `ExpandMatch` / `ProxBound`: `ProxBound.expandMatch_tail_not_proxBound`; the expansion is a tail read and
  the bound reads the window.
* (C) `FlowCovLim` / `FlowWard`: `FlowSym` §3(b): the translation Ward identity carries neither the moment current
  nor a spin contact term, and `CovC` fixes no normalisation of `Θ`.
* (D) `ProxyNondeg` / `ThreePointAtScale`: `NondegFold` §4: no argument that does not read the coefficients
  derives the first from the second (`NondegFold.threePoint_not_gives_proxyNondeg`); a Gaussian field has
  separated two-point reads and no connected three-point read.
* (E) `ZoomSettlesUV` / the kernel clause of `ApertureBridge`: one reads the mass along coupling towers, the
  other the short-distance shape of the continuum two-point kernel; no statement in the tree relates them
  (argued). `ZoomSettlesUV` and `ZoomSettling` share the template `SettlesFrom` with halving ratio, on different
  reads and different families (towers against `cpl βs`); one clause "every zoom read settles" would be a
  relabelled conjunction.

## 5. The count and the irreducible remainder

Before: 11 (`StrongEnd N` or, with `FinalBridge`'s template, `B`; `ZoomSettlesUV`; the 9 conjuncts). After: 11.
No genuine fold exists among the ten non-mass inputs on the tree's statements; no capstone with fewer inputs is
built. The remainder, by what it reads:

* the tail at fixed `s` then `s → 0⁺` (`k → ∞` along `atTop` or `ultra`): `ExpandMatch` (B), `FlowCovLim`,
  `FlowWard` (C), `ProxyNondeg` (D), `ApertureBridge`'s finiteness and profile parts (A, B), and, on the bare
  states, `ThreePointAtScale` (D);
* the limit forms only: `ProxyGenLimGerm` (generation, `ApproxK`);
* every step from the first step of a separation, with a rate: `ZoomSettling` (A with rate);
* the lattice window `s ≤ a_k`: `ProxBound` (B at the cutoff); its consumed content is a uniform bound on the
  zoom limit (§3);
* the coupling towers and the continuum kernel at `r → 0⁺`: `ZoomSettlesUV`, the kernel part of
  `ApertureBridge` (E).

A single clause implying a window read and a tail read must itself read the window (§2); a single clause implying
a lower bound (D) and an upper bound or approximation (`ProxyGenLimGerm`, `RPGerm`) must carry both directions
(`NondegFold` §3). Those are the two shapes that block a fold.

Copied over the coupling family (`#along_generalize_more`): `zoomSettles_iff_zoomSettlingLim`,
`zoomSettlingLim_of_proxBound`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs and the first step; `1` the bound of `r^η` at `r ≤ 1`, the unit of the
relative read and the top of the separation; `1/2` the halving ratio of consecutive spacings; `2` the halving
and the even moment; `(1 − 2^{−η})⁻¹` the geometric sum of the settling rate; `1 + |M| + (1 − 2^{−η})⁻¹` the
rescaling of the tree weight, from the read's own limit bound `M` and the settling sum. Counterexample choice:
the jump `2` in `firstStep_change_not_settles` (any value above `1` serves).
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ConstructFold

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

/-! ## 1. The read sequences -/

/-- **A settling read is within the geometric sum of its limit** at the first step: with halving ratios,
`0 ≤ r_{k₀} ≤ 1`, `η > 0` and `q → L`, `|q_{k₀} − L| ≤ (1 − 2^{−η})⁻¹`. DERIVED: `1/2` the ratio; `1` the top
of the ratio; `0` the signs. -/
theorem settles_dist_le {q r : ℕ → ℝ} {η : ℝ} {k₀ : ℕ} (hq : SettlesFrom q r η k₀)
    (hr : ∀ k, r (k + 1) = r k / 2) (h0 : 0 ≤ r k₀) (h1 : r k₀ ≤ 1) (hη : 0 < η)
    {L : ℝ} (hL : Tendsto q atTop (𝓝 L)) : |q k₀ - L| ≤ (1 - (1 / 2 : ℝ) ^ η)⁻¹ := by
  have hq' : SettlesFrom (fun k => q k - q k₀) r η k₀ := fun k hk => by
    have h := hq k hk
    show |(q (k + 1) - q k₀) - (q k - q k₀)| ≤ r k ^ η
    rwa [sub_sub_sub_cancel_right]
  have hb := settles_bound hq' hr h0 h1 hη
  have hlim : Tendsto (fun k => |q k - q k₀|) atTop (𝓝 |L - q k₀|) := (hL.sub_const _).abs
  have hle : |L - q k₀| ≤ (1 - (1 / 2 : ℝ) ^ η)⁻¹ := by
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
    have h : |q k - q k₀| ≤ |q k₀ - q k₀| + (1 - (1 / 2 : ℝ) ^ η)⁻¹ := hb k hk
    rwa [sub_self, abs_zero, zero_add] at h
  rwa [abs_sub_comm]

/-- **Load test: settling fixes no bound on the limit**: a constant read `M` settles at every rate from every
step, and converges to `M`. DERIVED: `0` the sign of the ratio. -/
theorem settles_const (M : ℝ) {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (η : ℝ) (k₀ : ℕ) :
    SettlesFrom (fun _ => M) r η k₀ ∧ Tendsto (fun _ : ℕ => M) atTop (𝓝 M) := by
  refine ⟨fun k _ => ?_, tendsto_const_nhds⟩
  show |M - M| ≤ r k ^ η
  rw [sub_self, abs_zero]
  exact Real.rpow_nonneg (hr k) η

/-- **Settling from a first step is not a tail statement**: for every read `q` and `0 ≤ r_{k₀} ≤ 1`, the read
changed at the one step `k₀` agrees with `q` at every other step (so eventually) and settles from `k₀` at no
rate `η > 0`. Counterexample choice: the jump `2` (any value above `1` serves). DERIVED: `1` the bound of
`r^η`; `0` the signs. -/
theorem firstStep_change_not_settles (q r : ℕ → ℝ) (k₀ : ℕ) (h0 : 0 ≤ r k₀) (h1 : r k₀ ≤ 1) :
    ∃ q' : ℕ → ℝ, (∀ k, k ≠ k₀ → q' k = q k) ∧ (∀ᶠ k in atTop, q' k = q k)
      ∧ ∀ η : ℝ, 0 < η → ¬ SettlesFrom q' r η k₀ := by
  classical
  refine ⟨fun k => if k = k₀ then q (k₀ + 1) + 2 else q k, fun k hk => if_neg hk,
    (eventually_gt_atTop k₀).mono fun k hk => if_neg hk.ne', fun η hη hs => ?_⟩
  have hne : k₀ + 1 ≠ k₀ := Nat.succ_ne_self k₀
  have h : |(if k₀ + 1 = k₀ then q (k₀ + 1) + 2 else q (k₀ + 1))
      - (if k₀ = k₀ then q (k₀ + 1) + 2 else q k₀)| ≤ r k₀ ^ η := hs k₀ le_rfl
  rw [if_neg hne, if_pos (rfl : k₀ = k₀),
    show q (k₀ + 1) - (q (k₀ + 1) + 2) = -2 by ring, abs_neg, abs_two] at h
  have hr : r k₀ ^ η ≤ 1 := Real.rpow_le_one h0 h1 hη.le
  linarith

/-! ## 2. The relative read -/

/-- **The relative read scales with the tree weight**: `relCum` at `γ t` is `relCum` at `γ` over `t^{|B|}`.
DERIVED: no numeral. -/
theorem relCum_rescale [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (γ t : ℝ)
    (Kc lam : Ix0 → ℝ) (k : ℕ) (s : ℝ) {n : ℕ} (F : Fin n → CDatum (CbR N zOne)) (B : Finset (Fin n)) :
    relCum Wf c (γ * t) Kc lam k s F B = relCum Wf c γ Kc lam k s F B / t ^ B.card := by
  unfold relCum treeW
  rw [mul_pow]
  ring

/-- The ratio at the first step lies in `[0, 1]`. DERIVED: `0` the sign; `1` the top. -/
theorem firstStep_ratio [NeZero N] {d : ℝ} (hd : 0 < d) {k₀ : ℕ} (hk₀ : FirstStep N d k₀) :
    0 ≤ dySpacing N k₀ / d ∧ dySpacing N k₀ / d ≤ 1 :=
  ⟨div_nonneg (dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k₀).le hd.le, (div_le_one hd).2 hk₀.1⟩

/-- **`ZoomSettling` gives the zoom limit of the relative read** (fact (A) for the cumulant read is contained in
it): at its witnesses, every relative read it controls converges along the zoom. DERIVED: `0` the signs; `1`
the top of the separation. -/
theorem zoomSettling_limit_exists [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ZoomSettling Wf c) :
    ∃ (θc γ η : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 < γ ∧ 0 < η ∧ (∀ i, 0 < Kc i) ∧
      ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
        ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ B : Finset (Fin n), B.Nonempty →
          ∃ L : ℝ, Tendsto (fun k => relCum Wf c γ Kc lam k s F B) atTop (𝓝 L) := by
  obtain ⟨θc, γ, η, Kc, lam, hθc, hγ, hη, hKc, H⟩ := h
  refine ⟨θc, γ, η, Kc, lam, hθc, hγ, hη, hKc, fun n F d hd hd1 hc hsep s hs hsd B hB => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_firstStep N hd
  exact settles_tendsto (H n F d hd hd1 hc hsep s hs hsd B hB k₀ hk₀) (spacing_ratio_succ N d)
    (firstStep_ratio hd hk₀).1 hη

/-! ## 3. The exchange for the base -/

/-- **Settling with a bounded zoom limit**: `ZoomSettling` with, at the same witnesses, every zoom limit of the
relative read bounded by one `M`. DERIVED: `1` the top of the separation; `0` the signs. -/
def ZoomSettlingLim [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ (θc γ η M : ℝ) (Kc lam : Ix0 → ℝ), 0 < θc ∧ 0 < γ ∧ 0 < η ∧ (∀ i, 0 < Kc i) ∧
    ∀ (n : ℕ) (F : Fin n → CDatum (CbR N zOne)) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
      ∀ s : ℝ, 0 < s → s ≤ θc * d → ∀ B : Finset (Fin n), B.Nonempty → ∀ k₀ : ℕ, FirstStep N d k₀ →
        SettlesFrom (fun k => relCum Wf c γ Kc lam k s F B) (fun k => dySpacing N k / d) η k₀
          ∧ ∀ L : ℝ, Tendsto (fun k => relCum Wf c γ Kc lam k s F B) atTop (𝓝 L) → |L| ≤ M

/-- **A bounded zoom limit gives the base**: `ZoomSettlingLim ⇒ ZoomSettles`, with the tree weight rescaled by
`t = 1 + |M| + (1 − 2^{−η})⁻¹`. DERIVED: `1` the floor `t ≥ 1` that `t ≤ t^|B|` needs (slack: `S > 1` already gives it); `1/2` the ratio; `0` the signs. -/
theorem zoomSettles_of_zoomSettlingLim [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ZoomSettlingLim Wf c) : ZoomSettles Wf c := by
  obtain ⟨θc, γ, η, M, Kc, lam, hθc, hγ, hη, hKc, H⟩ := h
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (1 - (1 / 2 : ℝ) ^ η)⁻¹ := ⟨_, rfl⟩
  have hρ1 : (1 / 2 : ℝ) ^ η < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hη
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact inv_nonneg.2 (by linarith)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 + |M| + S := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by
    have := abs_nonneg M
    linarith
  have ht0 : 0 < t := by linarith
  refine ⟨θc, γ * t, η, Kc, lam, hθc, mul_pos hγ ht0, hη, hKc,
    fun n F d hd hd1 hc hsep s hs hsd B hB k₀ hk₀ => ?_⟩
  obtain ⟨hset, hlim⟩ := H n F d hd hd1 hc hsep s hs hsd B hB k₀ hk₀
  have hcard : B.card ≠ 0 := (Finset.card_pos.2 hB).ne'
  have htc : t ≤ t ^ B.card := le_self_pow₀ ht1 hcard
  have htc1 : 1 ≤ t ^ B.card := ht1.trans htc
  have htc0 : 0 < t ^ B.card := lt_of_lt_of_le one_pos htc1
  obtain ⟨ha0, ha1⟩ := firstStep_ratio hd hk₀
  obtain ⟨L, hL⟩ := settles_tendsto hset (spacing_ratio_succ N d) ha0 hη
  have hdist : |relCum Wf c γ Kc lam k₀ s F B - L| ≤ S := by
    rw [hS]
    exact settles_dist_le hset (spacing_ratio_succ N d) ha0 ha1 hη hL
  have hLM := hlim L hL
  refine ⟨?_, fun k hk => ?_⟩
  · rw [relCum_rescale, abs_div, abs_of_pos htc0, div_le_one htc0]
    have h1 := abs_sub_abs_le_abs_sub (relCum Wf c γ Kc lam k₀ s F B) L
    have h2 := le_abs_self M
    linarith
  · show |relCum Wf c (γ * t) Kc lam (k + 1) s F B - relCum Wf c (γ * t) Kc lam k s F B|
      ≤ (dySpacing N k / d) ^ η
    rw [relCum_rescale, relCum_rescale, ← sub_div, abs_div, abs_of_pos htc0, div_le_iff₀ htc0]
    have h1 : |relCum Wf c γ Kc lam (k + 1) s F B - relCum Wf c γ Kc lam k s F B|
        ≤ (dySpacing N k / d) ^ η := hset k hk
    have h2 : 0 ≤ (dySpacing N k / d) ^ η :=
      Real.rpow_nonneg (div_nonneg (dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k).le hd.le) η
    exact h1.trans (le_mul_of_one_le_right h2 htc1)

/-- **The base gives a bounded zoom limit**: `ZoomSettles ⇒ ZoomSettlingLim`, with `M = 1 + (1 − 2^{−η})⁻¹`
(`ScaleLightCone.settles_bound`). DERIVED: `1` the unit of the relative read; `1/2` the ratio; `0` the
signs. -/
theorem zoomSettlingLim_of_zoomSettles [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ZoomSettles Wf c) : ZoomSettlingLim Wf c := by
  obtain ⟨θc, γ, η, Kc, lam, hθc, hγ, hη, hKc, H⟩ := h
  refine ⟨θc, γ, η, 1 + (1 - (1 / 2 : ℝ) ^ η)⁻¹, Kc, lam, hθc, hγ, hη, hKc,
    fun n F d hd hd1 hc hsep s hs hsd B hB k₀ hk₀ => ?_⟩
  obtain ⟨hbase, hset⟩ := H n F d hd hd1 hc hsep s hs hsd B hB k₀ hk₀
  refine ⟨hset, fun L hL => ?_⟩
  obtain ⟨ha0, ha1⟩ := firstStep_ratio hd hk₀
  have hb := settles_bound hset (spacing_ratio_succ N d) ha0 ha1 hη
  refine le_of_tendsto hL.abs (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
  have h1 : |relCum Wf c γ Kc lam k s F B|
      ≤ |relCum Wf c γ Kc lam k₀ s F B| + (1 - (1 / 2 : ℝ) ^ η)⁻¹ := hb k hk
  show |relCum Wf c γ Kc lam k s F B| ≤ 1 + (1 - (1 / 2 : ℝ) ^ η)⁻¹
  linarith

/-- **`ZoomSettles ↔ ZoomSettlingLim`**: under settling, the base at the first step is a uniform bound on the
zoom limit. DERIVED: no numeral. -/
theorem zoomSettles_iff_zoomSettlingLim [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)} :
    ZoomSettles Wf c ↔ ZoomSettlingLim Wf c :=
  ⟨zoomSettlingLim_of_zoomSettles, zoomSettles_of_zoomSettlingLim⟩

/-- `ZoomSettlingLim` gives `ZoomSettling` (drop the limit bound). DERIVED: no numeral. -/
theorem zoomSettling_of_zoomSettlingLim [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ZoomSettlingLim Wf c) : ZoomSettling Wf c := by
  obtain ⟨θc, γ, η, M, Kc, lam, hθc, hγ, hη, hKc, H⟩ := h
  exact ⟨θc, γ, η, Kc, lam, hθc, hγ, hη, hKc, fun n F d hd hd1 hc hsep s hs hsd B hB k₀ hk₀ =>
    (H n F d hd hd1 hc hsep s hs hsd B hB k₀ hk₀).1⟩

/-- **The proxy bound with settling gives the bounded zoom limit** (`ProxBound.zoomSettles_of_settling_prox`).
DERIVED: no numeral. -/
theorem zoomSettlingLim_of_proxBound [NeZero N] {Wf : ℝ → ConfFlow N} {c : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hP : MassGap.ProxBound.ProxBound Wf c) (h : ZoomSettling Wf c) : ZoomSettlingLim Wf c :=
  zoomSettlingLim_of_zoomSettles (MassGap.ProxBound.zoomSettles_of_settling_prox hP h)

/-! ## 4. The candidate single clause -/

/-- **The candidate (A) + (B) clause on a proxy family**: the expansion (`ProxBound.ExpandMatchOf`) and, at
every fixed `s > 0`, the convergence of every flowed reading as `k → ∞`. DERIVED: `0` the sign of the
scale. -/
def FlowLimRemOf [NeZero N] (P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)) (z : Chan → ℕ → ℝ) (μ : OffMix) : Prop :=
  MassGap.ProxBound.ExpandMatchOf P z μ
    ∧ ∀ (ι : Type) [Fintype ι] (F : ι → CDatum (CbR N zOne)) (s : ℝ), 0 < s →
        ∃ L : ℝ, Tendsto (fun k => MassGap.ProxBound.latP P k s F) atTop (𝓝 L)

/-- **The candidate is a tail read.** DERIVED: no numeral. -/
theorem tailRead_flowLimRemOf [NeZero N] (z : Chan → ℕ → ℝ) (μ : OffMix) :
    MassGap.ProxBound.TailRead N (fun P => FlowLimRemOf P z μ) := by
  rintro P Q hPQ ⟨hE, hL⟩
  refine ⟨MassGap.ProxBound.tailRead_expandMatchOf z μ P Q hPQ hE, fun ι _ F s hs => ?_⟩
  obtain ⟨L, hL'⟩ := hL ι F s hs
  refine ⟨L, hL'.congr' ?_⟩
  filter_upwards [hPQ s hs] with k hk
  unfold MassGap.ProxBound.latP
  rw [hk]

/-- **The candidate does not give the proxy bound**: from any proxy family meeting it, one equal to it at all
but finitely many steps of each scale meets it and fails `ProxBoundOf`. DERIVED: no numeral. -/
theorem flowLimRem_not_proxBound [NeZero N] {P : ℕ → ℝ → Ix0 → C(Cfg N, ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hP : FlowLimRemOf P z μ) :
    ∃ Q, FlowLimRemOf Q z μ ∧ ¬ MassGap.ProxBound.ProxBoundOf N Q
      ∧ ∀ s : ℝ, 0 < s → ∀ᶠ k in atTop, Q k s = P k s :=
  MassGap.ProxBound.tailRead_not_proxBound (tailRead_flowLimRemOf z μ) hP

end MassGap.ConstructFold

end

/-! ### The copy over a coupling family -/

namespace MassGap.ConstructFold

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from MassGap.ConstructFold.zoomSettles_iff_zoomSettlingLim
  MassGap.ConstructFold.zoomSettlingLim_of_proxBound

end MassGap.ConstructFold

#print axioms MassGap.ConstructFold.settles_dist_le
#print axioms MassGap.ConstructFold.settles_const
#print axioms MassGap.ConstructFold.firstStep_change_not_settles
#print axioms MassGap.ConstructFold.relCum_rescale
#print axioms MassGap.ConstructFold.firstStep_ratio
#print axioms MassGap.ConstructFold.zoomSettling_limit_exists
#print axioms MassGap.ConstructFold.zoomSettles_of_zoomSettlingLim
#print axioms MassGap.ConstructFold.zoomSettlingLim_of_zoomSettles
#print axioms MassGap.ConstructFold.zoomSettles_iff_zoomSettlingLim
#print axioms MassGap.ConstructFold.zoomSettling_of_zoomSettlingLim
#print axioms MassGap.ConstructFold.zoomSettlingLim_of_proxBound
#print axioms MassGap.ConstructFold.tailRead_flowLimRemOf
#print axioms MassGap.ConstructFold.flowLimRem_not_proxBound
#print axioms MassGap.CouplingGen.Along.ConstructFold.zoomSettles_iff_zoomSettlingLim
#print axioms MassGap.CouplingGen.Along.ConstructFold.zoomSettlingLim_of_proxBound
