import Mathlib
import MassGap.SU2Best

/-!
# MassGap.NondegFromProxy — `CompNondeg` from the two-point readings of the flowed proxies

The `SU(2)` target asks `CompNondeg h2N (CRen 2 z μ)`: for every combination `c` whose
top-dimension classical part is non-zero on some on-shell admissible potential, some separated
two-point continuum reading `∑ᵢ ∑ⱼ cᵢ cⱼ contC((i, f), (j, h))` of the renormalised composites is non-zero.
This module states the same non-vanishing for the flowed proxies `msProx Wf cf` at small flow time
(`ProxyNondeg Wf cf`), proves that under the expansion `ExpandR` and `ConvC` it is equivalent to
`CompNondeg (CRen 2 z μ)`.
Declarations are in the namespace `MassGap.NondegFromProxy`.

## 1. The clause

For a combination `c : Ix0 →₀ ℝ` and test functions `f`, `h`, at step `k` and scale `s`:
`proxRead Wf cf c f h k s = ∑ᵢ ∑ⱼ cᵢ cⱼ msLat Wf cf k s ((i, f), (j, h))` (the proxies' lattice two-point
reading), `latRead z μ c f h k = ∑ᵢ ∑ⱼ cᵢ cⱼ latC (CRen N z μ) k ((i, f), (j, h))`, and
`contRead z μ c f h = ∑ᵢ ∑ⱼ cᵢ cⱼ contC (CRen N z μ) ((i, f), (j, h))`.

`OnShellTop c` is the premise of `CompNondeg` at `CRen 2 z μ` (its classical part reads `cl i = i.1`,
so it does not depend on `z`, `μ`).

**`ProxyNondeg Wf cf`**: for every `c` with `OnShellTop c` there are continuous `f`, `h`, `d`-separated
for some `d > 0`, and `δ > 0` such that, for scales `s` arbitrarily close to `0` (`∃ᶠ s in 𝓝[>] 0`),
eventually along `ultra`, `δ ≤ |proxRead Wf cf c f h k s|`.

It reads the flowed fields `(Wf s).fieldMap`, the coefficients `cf`, the state `stateK` and the classical
data of `c`. It reads no composite field of `CRen 2 z μ`, no continuum limit `contC`, and neither `z` nor
`μ`.

## 2. What is proved

* `adm_pair`: the two-point family `((i, f), (j, h))` with continuous `d`-separated `f`, `h` is `ContD` and
  `SepD d`.
* `latRead_sub_proxRead_le`: under `ExpandR Wf cf z μ` with constants `θ`, `ε`: for every `c` and
  continuous `d`-separated `f`, `h` there is `M` with, for every `0 < s ≤ θ d`, eventually in `k`,
  `|latRead k − proxRead k s| ≤ M (s/d)^ε`.
* **`compNondeg_of_proxy`**: `ExpandR Wf cf z μ`, `ConvC (CRen 2 z μ)` and `ProxyNondeg Wf cf` give
  `CompNondeg (CRen 2 z μ)`. Choose `s` with `M (s/d)^ε < δ/2`, `s ≤ θ d` and the proxy lower bound;
  along `ultra`, `|latRead| > δ/2`; `latRead → contRead` by `ConvC`, so `contRead = 0` is excluded.
* **`proxyNondeg_of_compNondeg`**: `ExpandR`, `ConvC` and `CompNondeg (CRen 2 z μ)` give
  `ProxyNondeg Wf cf` (with `δ = |contRead|/2`, at every small `s`).
* **`proxyNondeg_iff`**: under `ExpandR` and `ConvC` the two clauses are equivalent: `ProxyNondeg Wf cf` is
  `CompNondeg (CRen 2 z μ)` moved onto the flowed proxies through the expansion, neither stronger nor
  weaker. It remains an input; nothing here discharges it.
* `proxRead_zero`, `not_proxyNondeg_zero`: at `cf = 0` every `proxRead` is `0`, so `ProxyNondeg Wf 0`
  fails as soon as one `c` has `OnShellTop c`.
* `convC_of_props`: `ConvC (CRen 2 z μ)` from `SubstrateAt` and `GradientFlowProps`
  (`CompositesRenAll.boundC_ren_of_scale_expand`, `InputsTriage.convC_iff_boundC`).
* `compNondeg_of_props`: `CompNondeg (CRen 2 z μ)` from `SubstrateAt`, `GradientFlowProps` and
  `ProxyNondeg Wf cf`.
* `GradientFlowPropsN`: `GradientFlowProps` with the field `nondeg : ProxyNondeg Wf cf`.
* At every `SU(N)` (`[NeZero N]`): `proxRead`, `latRead`, `contRead`, `OnShellTopN N`, `ProxyNondeg`,
  `latRead_sub_proxRead_le`, `tendsto_latRead`, `compNondeg_of_proxy`, `proxyNondeg_of_compNondeg`,
  `proxyNondeg_iff`, `proxRead_zero`, `not_proxyNondeg_zero`, `GradientFlowPropsN`; `convC_of_core`,
  `compNondeg_of_core` from `SU2Best.SubstrateCoreAt`. `OnShellTop` is `OnShellTopN 2`; the statements
  above that name `CRen 2` are the `N = 2` instances.
* No `ClayStatementAt` capstone is stated through `SU2Best.SubstrateAt`: its `endpoint` field,
  `MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.

## 3. Argued (no declaration)

* **Folding.** `ProxyNondeg Wf cf` reads only `Wf`, `cf` and classical data, the same data as the other
  fields of `GradientFlowProps` (`expand` also reads `z`, `μ`). So it belongs with the flow-side clauses,
  and `GradientFlowPropsN` holds it there. It does not belong with the substrate: `SubstrateAt` reads
  no coefficients `cf`.
* **What it asks.** At separation `d` fixed and `s → 0`, a uniform lower bound on the two-point
  function of the flowed proxies, smoothed fields at one scale `s`. `CoefBound` gives upper bounds
  `|c_{ij}(s)| ≤ K s^{d_j−d_i}(…)` only; no clause in the development gives a lower bound on the
  leading coefficient, so the classical premise `OnShellTop c` does not reduce to a condition on `cf`
  here. A route through the classical lead would state that `cf i s` contains the flowed monomial
  `i.1` itself with coefficient tending to `1`; even with it, the non-vanishing of the proxies'
  separated two-point function is a dynamical statement about the flowed measure.
* **The tree route (`ShortDistance.TreeNondeg`).** It needs leading short-distance values `T c` of
  every composite two-point function, the Gaussian (Wick) limit of the interacting readings. The
  development builds such values for the trace only; for general monomials they need the Gaussian
  limit of the gauge-field measure and its Wick contractions of products of field strengths, which are
  not formalised. Not pursued here.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the two points and the halves of the lower bound; `4` the
quarters of the lower bound and the dimension; `0` the limit of the scale, the zero coefficients and
the excluded value; `1` the smearing scale of the observer and the bound below `r`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.NondegFromProxy

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
  MassGap.ObserverChoice MassGap.SU2Best

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The clause -/

/-- The two-point family `((i, f), (j, h))`. DERIVED: `2` the two points. -/
abbrev pairF (i j : Ix0) (f h : TestFn) : Fin 2 → Ix0 × TestFn := ![(i, f), (j, h)]

/-- **The proxies' two-point reading** of the combination `c` at step `k`, scale `s`.
DERIVED: no numeral. -/
def proxRead [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (c : Ix0 →₀ ℝ) (f h : TestFn)
    (k : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ c.support, ∑ j ∈ c.support, c i * c j * msLat Wf cf k s (pairF i j f h)

/-- **The composites' lattice two-point reading** of `c` at step `k`. DERIVED: no numeral. -/
def latRead [NeZero N] (z : Chan → ℕ → ℝ) (μ : OffMix) (c : Ix0 →₀ ℝ) (f h : TestFn) (k : ℕ) : ℝ :=
  ∑ i ∈ c.support, ∑ j ∈ c.support, c i * c j * latC (NeZero.ne N) (CRen N z μ) k (pairF i j f h)

/-- **The composites' continuum two-point reading** of `c`. DERIVED: no numeral. -/
def contRead [NeZero N] (z : Chan → ℕ → ℝ) (μ : OffMix) (c : Ix0 →₀ ℝ) (f h : TestFn) : ℝ :=
  ∑ i ∈ c.support, ∑ j ∈ c.support, c i * c j * contC (NeZero.ne N) (CRen N z μ) (pairF i j f h)

/-- **The premise of `CompNondeg` at `SU(N)`**: the top-dimension classical part of `c` is non-zero on
some on-shell admissible potential. DERIVED: `0` the excluded value. -/
def OnShellTopN (N : ℕ) (c : Ix0 →₀ ℝ) : Prop :=
  ∃ (A : GPot N) (g : ℝ), GPot.Adm A ∧ OnShell g A
    ∧ ∑ i ∈ c.support.filter (fun i => cdim i.1 = c.support.sup (fun j => cdim j.1)),
        c i * g ^ cnF i.1 * cval g A i.1 ≠ 0

/-- **The premise of `CompNondeg` at `SU(2)`**: `OnShellTopN 2`. DERIVED: `2` the colour count. -/
abbrev OnShellTop (c : Ix0 →₀ ℝ) : Prop := OnShellTopN 2 c

/-- **Non-degeneracy of the flowed proxies**: module docstring, §1. DERIVED: `0` the limit of the
scale and the sign of the separation. -/
def ProxyNondeg [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∀ c : Ix0 →₀ ℝ, OnShellTopN N c →
    ∃ f h : TestFn, Continuous f.1 ∧ Continuous h.1 ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h)
      ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
          δ ≤ |proxRead Wf cf c f h k s|

/-! ## 2. The two-point bound from the expansion -/

/-- **The two-point family is admissible.** DERIVED: `2` the two points. -/
theorem adm_pair {i j : Ix0} {f h : TestFn} (hf : Continuous f.1) (hh : Continuous h.1) {d : ℝ}
    (hfh : ContinuumSep.sepBy d f h) : ContD (pairF i j f h) ∧ SepD d (pairF i j f h) := by
  have hhf : ContinuumSep.sepBy d h f := fun y w hy hw => by
    obtain ⟨m, hm⟩ := hfh w y hw hy
    exact ⟨m, by rw [abs_sub_comm]; exact hm⟩
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · fin_cases x
    exacts [hf, hh]
  · fin_cases x <;> fin_cases y
    · exact (hxy rfl).elim
    · exact hfh
    · exact hhf
    · exact (hxy rfl).elim

/-- **The two-point remainder of the expansion**: module docstring, §2. DERIVED: `2` the two points. -/
theorem latRead_sub_proxRead_le [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} {θ ε Kr : ℝ} {κr : Ix0 → ℝ}
    (hE : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CRen N z μ)) (d : ℝ), 0 < d →
      ContD F → SepD d F → ∀ s : ℝ, 0 < s → s ≤ θ * d → ∀ᶠ k in atTop,
        |latC (NeZero.ne N) (CRen N z μ) k F - msLat Wf cf k s F|
          ≤ Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2))
    (c : Ix0 →₀ ℝ) {f h : TestFn} (hf : Continuous f.1) (hh : Continuous h.1) {d : ℝ} (hd : 0 < d)
    (hfh : ContinuumSep.sepBy d f h) :
    ∃ M : ℝ, ∀ s : ℝ, 0 < s → s ≤ θ * d → ∀ᶠ k in atTop,
      |latRead (N := N) z μ c f h k - proxRead Wf cf c f h k s| ≤ M * (s / d) ^ ε := by
  set A : Ix0 → Ix0 → ℝ := fun i j => Kr ^ Fintype.card (Fin 2)
    * ∏ x, ((d ^ κr (pairF i j f h x).1)⁻¹ * l1 (pairF i j f h x).2) with hAdef
  refine ⟨∑ i ∈ c.support, ∑ j ∈ c.support, |c i * c j| * |A i j|, fun s hs hsd => ?_⟩
  have hx : 0 ≤ (s / d) ^ ε := Real.rpow_nonneg (div_nonneg hs.le hd.le) _
  have hev : ∀ᶠ k in atTop, ∀ i ∈ c.support, ∀ j ∈ c.support,
      |latC (NeZero.ne N) (CRen N z μ) k (pairF i j f h) - msLat Wf cf k s (pairF i j f h)|
        ≤ Kr ^ Fintype.card (Fin 2) * (s / d) ^ ε
          * ∏ x, ((d ^ κr (pairF i j f h x).1)⁻¹ * l1 (pairF i j f h x).2) :=
    (Filter.eventually_all_finset c.support).2 fun i _ =>
      (Filter.eventually_all_finset c.support).2 fun j _ =>
        hE (Fin 2) (pairF i j f h) d hd (adm_pair hf hh hfh).1 (adm_pair hf hh hfh).2 s hs hsd
  filter_upwards [hev] with k hk
  have e : latRead (N := N) z μ c f h k - proxRead Wf cf c f h k s
      = ∑ i ∈ c.support, ∑ j ∈ c.support, c i * c j
          * (latC (NeZero.ne N) (CRen N z μ) k (pairF i j f h) - msLat Wf cf k s (pairF i j f h)) := by
    unfold latRead proxRead
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have h1 := hk i hi j hj
  have h2 : Kr ^ Fintype.card (Fin 2) * (s / d) ^ ε
      * ∏ x, ((d ^ κr (pairF i j f h x).1)⁻¹ * l1 (pairF i j f h x).2) ≤ |A i j| * (s / d) ^ ε := by
    calc Kr ^ Fintype.card (Fin 2) * (s / d) ^ ε
          * ∏ x, ((d ^ κr (pairF i j f h x).1)⁻¹ * l1 (pairF i j f h x).2)
        = A i j * (s / d) ^ ε := by simp only [hAdef]; ring
      _ ≤ |A i j| * (s / d) ^ ε := mul_le_mul_of_nonneg_right (le_abs_self _) hx
  rw [abs_mul]
  calc |c i * c j| * |latC (NeZero.ne N) (CRen N z μ) k (pairF i j f h) - msLat Wf cf k s (pairF i j f h)|
      ≤ |c i * c j| * (|A i j| * (s / d) ^ ε) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
    _ = |c i * c j| * |A i j| * (s / d) ^ ε := by ring

/-- `latRead → contRead` along `ultra` under `ConvC`. DERIVED: no numeral. -/
theorem tendsto_latRead [NeZero N] {z : Chan → ℕ → ℝ} {μ : OffMix} (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (c : Ix0 →₀ ℝ) {f h : TestFn} (hf : Continuous f.1) (hh : Continuous h.1) {d : ℝ} (hd : 0 < d)
    (hfh : ContinuumSep.sepBy d f h) :
    Tendsto (fun k => latRead (N := N) z μ c f h k) (ultra : Filter ℕ) (𝓝 (contRead (N := N) z μ c f h)) := by
  unfold latRead contRead
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  exact (hC (Fin 2) (pairF i j f h)
    ⟨(adm_pair hf hh hfh).1, d, hd, (adm_pair hf hh hfh).2⟩).const_mul (c i * c j)

/-! ## 3. The equivalence -/

/-- **`CompNondeg` from the proxies**: module docstring, §2. DERIVED: `2` the half of the lower bound;
`0` the excluded value. -/
theorem compNondeg_of_proxy [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ)) (hP : ProxyNondeg Wf cf) :
    CompNondeg (NeZero.ne N) (CRen N z μ) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro c hon
  obtain ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, δ, hδ, hfr⟩ := hP c hon
  refine ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, ?_⟩
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE'⟩ := hE
  obtain ⟨M, hM⟩ := latRead_sub_proxRead_le hE' c hf hh hd hfh
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), M * (s / d) ^ ε < δ / 2 ∧ s < θ * d ∧ 0 < s :=
    (eventually_rate_lt hε M (half_pos hδ)).and
      (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin.mono fun s hs => hs))
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (hfr.and_eventually hev).exists
  have hT := tendsto_latRead hC c hf hh hd hfh
  intro h0
  change contRead (N := N) z μ c f h = 0 at h0
  rw [h0] at hT
  have hsmall : ∀ᶠ k in (ultra : Filter ℕ), |latRead (N := N) z μ c f h k| < δ / 2 := by
    filter_upwards [(Metric.tendsto_nhds.mp hT) (δ / 2) (half_pos hδ)] with k hk
    rwa [Real.dist_eq, sub_zero] at hk
  obtain ⟨k, hk1, hk2, hk3⟩ :=
    (hsmall.and (hs1.and ((hM s hs4 hs3.le).filter_mono ultra_le))).exists
  have htri := abs_sub_abs_le_abs_sub (proxRead Wf cf c f h k s) (latRead (N := N) z μ c f h k)
  rw [abs_sub_comm] at htri
  linarith

/-- **The proxies from `CompNondeg`**: module docstring, §2. DERIVED: `2` the half of the lower bound;
`4` its quarters; `0` the excluded value and the limit of the scale. -/
theorem proxyNondeg_of_compNondeg [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (hN : CompNondeg (NeZero.ne N) (CRen N z μ)) : ProxyNondeg Wf cf := by
  intro c hon
  obtain ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, hne⟩ := hN c hon
  have hL : contRead (N := N) z μ c f h ≠ 0 := hne
  have hLp : 0 < |contRead (N := N) z μ c f h| := abs_pos.2 hL
  refine ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, |contRead (N := N) z μ c f h| / 2, half_pos hLp, ?_⟩
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE'⟩ := hE
  obtain ⟨M, hM⟩ := latRead_sub_proxRead_le hE' c hf hh hd hfh
  have hT := tendsto_latRead hC c hf hh hd hfh
  refine Filter.Eventually.frequently ?_
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      M * (s / d) ^ ε < |contRead (N := N) z μ c f h| / 4 ∧ s < θ * d ∧ 0 < s :=
    (eventually_rate_lt hε M (by positivity)).and
      (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin.mono fun s hs => hs))
  filter_upwards [hev] with s ⟨hs1, hs2, hs3⟩
  filter_upwards [(Metric.tendsto_nhds.mp hT) (|contRead (N := N) z μ c f h| / 4) (by positivity),
    (hM s hs3 hs2.le).filter_mono ultra_le] with k hk1 hk2
  rw [Real.dist_eq] at hk1
  have t1 := abs_sub_abs_le_abs_sub (contRead (N := N) z μ c f h) (latRead (N := N) z μ c f h k)
  have t2 := abs_sub_abs_le_abs_sub (latRead (N := N) z μ c f h k) (proxRead Wf cf c f h k s)
  rw [abs_sub_comm] at t1
  linarith

/-- **The equivalence under the expansion**: module docstring, §2. DERIVED: no numeral. -/
theorem proxyNondeg_iff [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hE : ExpandR Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ)) :
    ProxyNondeg Wf cf ↔ CompNondeg (NeZero.ne N) (CRen N z μ) :=
  ⟨compNondeg_of_proxy hE hC, proxyNondeg_of_compNondeg hE hC⟩

/-! ## 4. The zero coefficients -/

/-- At `cf = 0` every proxy two-point reading is `0`. DERIVED: `0` the zero coefficients. -/
theorem proxRead_zero [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 →₀ ℝ) (f h : TestFn) (k : ℕ) (s : ℝ) :
    proxRead Wf 0 c f h k s = 0 := by
  unfold proxRead
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have : msLat Wf 0 k s (pairF i j f h) = 0 := by
    unfold msLat
    rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 2))
      (by rw [msProx_zero, smear_zero_field]), MassGap.DLRLimit.State.map_zero]
  rw [this, mul_zero]

/-- **`ProxyNondeg` fails at the zero coefficients** as soon as one `c` has `OnShellTop c`.
DERIVED: `0` the zero coefficients. -/
theorem not_proxyNondeg_zero [NeZero N] (Wf : ℝ → ConfFlow N) {c : Ix0 →₀ ℝ} (hon : OnShellTopN N c) :
    ¬ ProxyNondeg Wf 0 := by
  intro H
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨f, h, -, -, -, δ, hδ, hfr⟩ := H c hon
  obtain ⟨s, hs⟩ := hfr.exists
  obtain ⟨k, hk⟩ := hs.exists
  rw [proxRead_zero, abs_zero] at hk
  linarith

/-! ## 5. The flow bundle -/

/-- **`ConvC` from the bundles** (`boundC_ren_of_scale_expand`, `expandR_of_strong`,
`InputsTriage.convC_iff_boundC`). DERIVED: no
numeral. -/
theorem convC_of_props {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) : ConvC h2N (CRen 2 z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2
    (boundC_ren_of_scale_expand S.b_pos S.scale (expandR_of_strong F.expand))

/-- **`CompNondeg` from the bundles and `ProxyNondeg`.** DERIVED: no numeral. -/
theorem compNondeg_of_props {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) (hP : ProxyNondeg Wf cf) : CompNondeg h2N (CRen 2 z μ) :=
  compNondeg_of_proxy (expandR_of_strong F.expand) (convC_of_props S F) hP

/-- **`ConvC` from the substrate core and the flow-side clauses**, at every `SU(N)`. DERIVED: no
numeral. -/
theorem convC_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) : ConvC (NeZero.ne N) (CRen N z μ) :=
  (InputsTriage.convC_iff_boundC _ _).2
    (boundC_ren_of_scale_expand S.b_pos S.scale (expandR_of_strong F.expand))

/-- **`CompNondeg` from the substrate core, the flow-side clauses and `ProxyNondeg`**, at every `SU(N)`.
DERIVED: no numeral. -/
theorem compNondeg_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf)
    (F : GradientFlowProps Wf cf z μ) (hP : ProxyNondeg Wf cf) : CompNondeg (NeZero.ne N) (CRen N z μ) :=
  compNondeg_of_proxy (expandR_of_strong F.expand) (convC_of_core S F) hP

/-- **The flow-side clauses with the proxies' non-degeneracy.** -/
structure GradientFlowPropsN [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop where
  props : GradientFlowProps Wf cf z μ
  /-- The flowed proxies' separated two-point readings are non-degenerate at small flow time. -/
  nondeg : ProxyNondeg Wf cf

end MassGap.NondegFromProxy

end

#print axioms MassGap.NondegFromProxy.adm_pair
#print axioms MassGap.NondegFromProxy.latRead_sub_proxRead_le
#print axioms MassGap.NondegFromProxy.tendsto_latRead
#print axioms MassGap.NondegFromProxy.compNondeg_of_proxy
#print axioms MassGap.NondegFromProxy.proxyNondeg_of_compNondeg
#print axioms MassGap.NondegFromProxy.proxyNondeg_iff
#print axioms MassGap.NondegFromProxy.proxRead_zero
#print axioms MassGap.NondegFromProxy.not_proxyNondeg_zero
#print axioms MassGap.NondegFromProxy.convC_of_props
#print axioms MassGap.NondegFromProxy.compNondeg_of_props
#print axioms MassGap.NondegFromProxy.convC_of_core
#print axioms MassGap.NondegFromProxy.compNondeg_of_core
