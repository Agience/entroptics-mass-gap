import Mathlib
import MassGap.SU2Best
import MassGap.NondegFromProxy
import MassGap.NonGaussFromScale

/-!
# MassGap.ProxyGenObserver — `ProxyGen` split into a uniform bound and a step-free generation clause

`ProxyGen obsW b Wf cf r` (`ApproxFromExpand`) is: for every
separated positive-time monomial `P`, every `0 < s ≤ b` and `η > 0`, coefficients `a` on the margin
monomials of `obsW` with, eventually along `ultra`, `⟪B_k^s − Y_k(a), B_k^s − Y_k(a)⟫_k ≤ η`. The
quantifiers are `∃ a, ∀ᶠ k`: one finitely supported coefficient vector serves every step of a set in
`ultra`. This module reads that order of quantifiers, proves what a step-by-step approximation gives
and does not give, and proves `ProxyGen` equivalent, under `UniformBoundF (Φ0 W)`, `PhysRange r` and `ProxyMem`, to two
clauses: a bound on the proxies' reflection
readings uniform in the step (`ProxyBound`), and the generation statement for the `ultra` limits of
those readings (`ProxyGenLim`), which reads no step. Declarations are in the namespace
`MassGap.ProxyGenObserver`.

Notation as in `ApproxFromExpand`: `B_k^s(P) = proxB Wf cf k s P`, `Y_k(a) = yW W k a`,
`V_k(Q) = prodSmear a_k ((Φ0 W).mono k Q)`, `⟪X, X'⟫_k = rform (stateK k) θ X X'`, `θ = ireflObs 0 0`.

## 1. A step-by-step approximation does not give fixed coefficients (proved, abstract)

The escape model on `ℕ` (margin monomials indexed by `ℕ`): orthonormal Gram kernel `escG`, mixed
kernel `escX k = 1` at `Q = k` and `0` elsewhere, diagonal `1`; `escD k a = 1 − 2 xL(escX k) a +
gForm escG a a`, the squared distance of the `k`-th unit vector from `∑ a_Q e_Q`.
* `esc_perStep`: at every step `k`, `escD k (single k 1) = 0`.
* `esc_fixed`: for every `a`, eventually in `k` (`k` beyond the support of `a`), `1 ≤ escD k a`.
* **`esc_not_fixed`**: no `a` has `escD k a ≤ 1/2` eventually along `ultra`.
* `tendsto_escX`, **`esc_limit_not_approxK`**: the three kernels converge (diagonal `1`, mixed `0`,
  Gram `escG`) and `ApproxK` fails for the limits.
So exact approximation at each step, with every reading bounded and convergent, does not give the
`∃ a, ∀ᶠ k` of `ProxyGen`: the approximant may use a monomial that moves with the step and whose
overlap with every fixed monomial vanishes in the limit.

ARGUED (not built), idea (a) read against this. At one step `k` the observer's margin monomials are
continuous functions of `obsW.V k U`, and `LoopsGenerate.exists_adjoin_near` (Stone–Weierstrass through
a family, on any compact space) approximates uniformly every continuous function constant on the
fibres of the family. Two points stand between this and `ProxyGen`:
* the fibre condition. `B_k^s` at `s < b` is a function of `(Wf s).V k U`; it is constant on the fibres
  of the observer's step-`k` fields only when the information of `(Wf s).V k U` on the half-space is
  recoverable from `obsW.V k U` up to gauge, a property of the APE map at step `k` that no declaration
  states. `LoopsGenerate.giles` separates the gauge orbits of the unflowed slice configuration, not of
  its image under a flow. This is `ApproxFromExpand` §4 (a flow at smaller time is not a function of
  the flow at larger time) at one fixed step.
* the order of quantifiers. A fixed continuum test function covers more lattice sites as `k` grows,
  so a single-site field at step `k` is reached only by test functions that shrink with `a_k`, that is
  by coefficients that move with `k`. `esc_not_fixed` shows that this is not a removable technicality:
  an approximation at each step is compatible with the failure of `ProxyGen`.

## 2. The split (proved)

Every declaration of this section is stated at every `SU(N)` (`[NeZero N]`, `Wf : ℝ → ConfFlow N`), as is
`uB_of_core` (the uniform bound from `SU2Best.SubstrateCoreAt`); `uB_of_substrate` (§3) is at `SU(2)`.

* `proxD`, `proxX`: the proxies' diagonal reading `⟪B_k^s, B_k^s⟫_k` and their mixed reading
  `⟪B_k^s, V_k(Q)⟫_k` against a margin monomial `Q` of `W`.
* `rform_sub_proxB`: `⟪B − Y(a), B − Y(a)⟫_k = proxD − 2 xL(proxX) a + gForm(latSF) a a`
  (`JointRP.rform_expand`, `JointRP.latSF_pair_eq`).
* `rform_yW_self`: `⟪Y(a), Y(a)⟫_k = gForm(latSF) a a`.
* `tendsto_limUnder_ultra`: a real sequence bounded eventually along `ultra` converges along `ultra`
  to its `limUnder` (`[−C, C]` is compact, `ultra` is an ultrafilter).
* **`ProxyBound W b Wf cf r`**: for every `P` and `0 < s ≤ b`, `|proxD|` is bounded eventually along
  `ultra`, and for every margin monomial `Q`, `|proxX(Q)|` is bounded eventually along `ultra`.
* `kernB`, `mixB`: the `ultra` limits (`limUnder`) of the proxies' readings, indexed by `ProxyIx b`
  (pairs `(P, s)` with `0 < s ≤ b`).
* **`ProxyGenLim W b Wf cf r`**: `ApproxK (kernB Wf cf b) (mixB W Wf cf b) (gramFN W r)`, `gramFN` the
  observer's flowed kernel `CompositeLink.gramF` with hypothesis `N ≠ 0`.
  It reads no step: in the joint limit form of the proxies and the observer's margin monomials, each
  proxy is in the closure of the span of the observer's margin monomials.
* **`proxyGen_of_lim`**: `UniformBoundF (Φ0 W)`, `ProxyBound` and `ProxyGenLim` give `ProxyGen`.
* **`proxyGenLim_of_proxyGen`**: `UniformBoundF (Φ0 W)`, `ProxyBound` and `ProxyGen` give
  `ProxyGenLim`.
* `abs_form_le`: `|F(x, y)| ≤ (F(x, x) + F(y, y)) / 2` for a symmetric bilinear form nonnegative at
  `x ± y`.
* **`proxyBound_of_proxyGen`**: `UniformBoundF (Φ0 W)`, `PhysRange r`, `ProxyMem b Wf cf` (the proxy
  products eventually in the half-space algebra along `ultra`) and `ProxyGen` give `ProxyBound`.
* **`proxyGen_iff`**: under `UniformBoundF (Φ0 W)`, `PhysRange r` and `ProxyMem`,
  `ProxyGen ↔ ProxyBound ∧ ProxyGenLim`. Neither clause of the split is stronger than `ProxyGen`
  needs.

## 3. The uniform bound from the substrate (proved)

* `uB_of_substrate`: `SubstrateAt W z b Wf` gives `UniformBoundF h2N (Φ0 W)`
  (`CompositesRenAll.uv_of_scale`, `ClaySUFinal.classMoments_of_siteExp`, `ClaySUGap.uB`).

The module states no `ClayStatement` capstone: one through `SubstrateAt` would carry its `endpoint` field,
`MultiScale.Endpoint`, which `InputAudit.not_multiScaleEndpoint` refutes under the argued growth of the
zero-flux level count.

## 4. What remains (argued; no declaration)

* `ProxyBound` is a moment bound on the flowed proxies at each fixed `0 < s ≤ b`, uniform in the
  step. `SubstrateAt.scale` (`ScaleControlAll`) bounds one-site exponential moments of
  `a_k^{−d_j} |O_j ∘ V_k^{(s)}|` for `s ∈ [a_k, b]`; the passage from these to `ProxyBound` is
  `ProxyBoundFromScale.proxyBound_of_substrate` (each reflected reading bounded by the two squares, the
  proxy side by `abs_msLat_le`, the observer side by `UniformBoundF`), which needs no half-space
  membership; `proxyBound_of_proxyGen` here is the converse route through `ProxyMem`.
* `ProxyGenLim` is the generation statement with the step removed: in the limit reflection form, the
  vector of every flowed proxy at `0 < s ≤ b` lies in the closure of the span of the vectors of the
  observer's margin monomials. `esc_limit_not_approxK` shows that convergent, positive limit kernels do
  not give it; it is a generating property of `obsW` in the continuum limit, not a lattice
  Stone–Weierstrass statement.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the cross-term factor and the parallelogram factor; `0` the
plane, the reflection constant, the signs and the limit; `1` the unit vector, the unit diagonal and the
margin of the bound; `1/2` the tolerance of the abstract model and the halving of `η`; `4` the
dimension.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ProxyGenObserver

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
  MassGap.ObserverChoice MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The escape model -/

/-- The orthonormal Gram kernel on `ℕ`. DERIVED: `1`, `0` the entries. -/
def escG : ℕ → ℕ → ℝ := fun Q Q' => if Q = Q' then 1 else 0

/-- The mixed kernel at step `k`: the `k`-th unit vector. DERIVED: `1`, `0` the entries. -/
def escX (k : ℕ) : ℕ → ℝ := fun Q => if Q = k then 1 else 0

/-- The squared distance at step `k` of the `k`-th unit vector from `∑ a_Q e_Q`. DERIVED: `1` the
unit diagonal; `2` the cross-term factor. -/
def escD (k : ℕ) (a : ℕ →₀ ℝ) : ℝ := 1 - 2 * xL (escX k) a + gForm escG a a

/-- DERIVED: no numeral. -/
theorem xL_escX (k : ℕ) (a : ℕ →₀ ℝ) : xL (escX k) a = a k := by
  unfold xL escX
  rw [Finsupp.sum, Finset.sum_eq_single k]
  · simp
  · intro Q _ hQ
    simp [hQ]
  · intro hk
    rw [Finsupp.mem_support_iff, not_not] at hk
    simp [hk]

/-- DERIVED: no numeral. -/
theorem gForm_escG (a : ℕ →₀ ℝ) : gForm escG a a = ∑ P ∈ a.support, a P * a P := by
  unfold gForm escG
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finsupp.sum, Finset.sum_eq_single P]
  · simp
  · intro Q _ hQ
    simp [Ne.symm hQ]
  · intro h
    exact absurd hP h

/-- DERIVED: `0` the sign. -/
theorem gForm_escG_nonneg (a : ℕ →₀ ℝ) : 0 ≤ gForm escG a a := by
  rw [gForm_escG]
  exact Finset.sum_nonneg fun P _ => mul_self_nonneg _

/-- **Exact approximation at every step**: `escD k (single k 1) = 0`. DERIVED: `1` the coefficient;
`0` the distance. -/
theorem esc_perStep (k : ℕ) : escD k (Finsupp.single k 1) = 0 := by
  rw [escD, xL_escX, gForm_single]
  simp [escG]
  norm_num

/-- **A fixed coefficient vector is eventually at distance at least `1`**: beyond the support of `a`.
DERIVED: `1` the bound. -/
theorem esc_fixed (a : ℕ →₀ ℝ) : ∀ᶠ k in atTop, 1 ≤ escD k a := by
  filter_upwards [eventually_gt_atTop (a.support.sup id)] with k hk
  have hk0 : a k = 0 := by
    by_contra h
    have hm : k ∈ a.support := Finsupp.mem_support_iff.mpr h
    exact lt_irrefl k (lt_of_le_of_lt (Finset.le_sup (f := id) hm) hk)
  rw [escD, xL_escX, hk0]
  linarith [gForm_escG_nonneg a]

/-- **Step-by-step approximation does not give fixed coefficients**: exact approximation at every
step, and no `a` with `escD k a ≤ 1/2` eventually along `ultra`. Module docstring, §1.
DERIVED: `1/2` the tolerance; `0` the distance. -/
theorem esc_not_fixed :
    (∀ k : ℕ, ∃ a : ℕ →₀ ℝ, escD k a = 0)
      ∧ ¬ ∃ a : ℕ →₀ ℝ, ∀ᶠ k in (ultra : Filter ℕ), escD k a ≤ 1 / 2 := by
  refine ⟨fun k => ⟨_, esc_perStep k⟩, ?_⟩
  rintro ⟨a, ha⟩
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨k, hk1, hk2⟩ := (ha.and ((esc_fixed a).filter_mono ultra_le)).exists
  linarith

/-- The mixed kernel of the escape model converges to `0` at every monomial. DERIVED: `0` the
limit. -/
theorem tendsto_escX (Q : ℕ) : Tendsto (fun k => escX k Q) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop Q] with k hk
  simp [escX, ne_of_lt hk]

/-- **`ApproxK` fails for the limit kernels of the escape model**: diagonal `1`, mixed `0`, Gram
`escG`. DERIVED: `1` the diagonal; `0` the mixed kernel; `1/2` the tolerance. -/
theorem esc_limit_not_approxK :
    ¬ ApproxK (fun _ _ : Unit => (1 : ℝ)) (fun (_ : Unit) (_ : ℕ) => (0 : ℝ)) escG := by
  intro h
  obtain ⟨c, hc⟩ := h () (1 / 2) (by norm_num)
  have hx : xL (fun _ : ℕ => (0 : ℝ)) c = 0 := by
    unfold xL
    simp
  have hc' : 1 - 2 * xL (fun _ : ℕ => (0 : ℝ)) c + gForm escG c c ≤ 1 / 2 := hc
  rw [hx] at hc'
  linarith [gForm_escG_nonneg c]

/-! ## 2. The split -/

/-- **The proxies' diagonal reflection reading** `⟪B_k^s, B_k^s⟫_k`. DERIVED: `0` the plane and the
reflection constant. -/
def proxD [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) (P : TMonoG Ix0) : ℝ :=
  rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxB Wf cf k s P) (proxB Wf cf k s P)

/-- **The proxies' mixed reflection reading** `⟪B_k^s, V_k(Q)⟫_k` against a margin monomial `Q` of
`W`. DERIVED: `0` the plane and the reflection constant. -/
def proxX [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) {r : ℝ} (k : ℕ)
    (s : ℝ) (P : TMonoG Ix0) (Q : MarginMono N 0 r) : ℝ :=
  rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxB Wf cf k s P)
    (prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1))

/-- **The squared reflection distance of a proxy from an observer combination**:
`⟪B − Y(a), B − Y(a)⟫_k = proxD − 2 xL(proxX) a + gForm(latSF) a a`. DERIVED: `2` the cross-term
factor; `0` the plane. -/
theorem rform_sub_proxB [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    {r : ℝ} (k : ℕ) (s : ℝ) (P : TMonoG Ix0) (a : MarginMono N 0 r →₀ ℝ) :
    rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
        (proxB Wf cf k s P - yW W k a) (proxB Wf cf k s P - yW W k a)
      = proxD Wf cf k s P - 2 * xL (fun Q => proxX W Wf cf k s P Q) a
        + gForm (fun Q Q' : MarginMono N 0 r => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1)) a a := by
  have h := rform_expand (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)) (rform_symm_k k)
    (proxB Wf cf k s P) (proxB Wf cf k s P)
    (fun Q : MarginMono N 0 r => prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)) 0 a
  rw [zero_smul, add_zero] at h
  rw [show yW W k a = a.sum (fun Q x => x • prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)) from rfl, h]
  simp only [latSF_pair_eq, proxD, proxX]
  ring

/-- **The observer combination's own reading**: `⟪Y(a), Y(a)⟫_k = gForm(latSF) a a`.
DERIVED: `0` the plane. -/
theorem rform_yW_self [NeZero N] (W : ConfFlow N) {r : ℝ} (k : ℕ) (a : MarginMono N 0 r →₀ ℝ) :
    rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (yW W k a) (yW W k a)
      = gForm (fun Q Q' : MarginMono N 0 r => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1)) a a := by
  have h := rform_expand (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)) (rform_symm_k k)
    0 0 (fun Q : MarginMono N 0 r => prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)) 0 a
  have hx0 : xL (fun _ : MarginMono N 0 r => (0 : ℝ)) a = 0 := by
    unfold xL
    simp
  simp only [smul_zero, add_zero, zero_sub, map_neg, LinearMap.neg_apply, neg_neg, map_zero,
    LinearMap.zero_apply, hx0] at h
  simp only [latSF_pair_eq]
  rw [show yW W k a = a.sum (fun Q x => x • prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)) from rfl]
  linear_combination h

/-- **A real sequence bounded along `ultra` converges along `ultra`** to its `limUnder`.
DERIVED: no numeral. -/
theorem tendsto_limUnder_ultra {x : ℕ → ℝ} {C : ℝ}
    (h : ∀ᶠ k in (ultra : Filter ℕ), |x k| ≤ C) :
    Tendsto x (ultra : Filter ℕ) (𝓝 (limUnder (ultra : Filter ℕ) x)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨y, -, hy⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds'
    (Ultrafilter.map x ultra) (Ultrafilter.mem_map.mpr (h.mono fun k hk => abs_le.mp hk))
  have ht : Tendsto x (ultra : Filter ℕ) (𝓝 y) := by
    rw [Ultrafilter.coe_map] at hy
    exact hy
  rw [ht.limUnder_eq]
  exact ht

/-- **The uniform bound**: for every `P` and `0 < s ≤ b`, the proxies' diagonal reading and each
mixed reading against a margin monomial of `W` are bounded eventually along `ultra`.
DERIVED: `0` the lower end of the scale. -/
def ProxyBound [NeZero N] (W : ConfFlow N) (b : ℝ) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (r : ℝ) :
    Prop :=
  ∀ (P : TSepG Ix0 0) (s : ℝ), 0 < s → s ≤ b →
    (∃ C : ℝ, ∀ᶠ k in (ultra : Filter ℕ), |proxD Wf cf k s P.1| ≤ C)
      ∧ ∀ Q : MarginMono N 0 r, ∃ C : ℝ, ∀ᶠ k in (ultra : Filter ℕ), |proxX W Wf cf k s P.1 Q| ≤ C

/-- **The proxies' half-space membership**: for every `P` and `0 < s ≤ b`, the proxy product is in
the half-space algebra eventually along `ultra`. DERIVED: `0` the plane and the lower end of the
scale. -/
def ProxyMem [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∀ (P : TSepG Ix0 0) (s : ℝ), 0 < s → s ≤ b → ∀ᶠ k in (ultra : Filter ℕ),
    proxB Wf cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0

/-- The index of the proxies: a separated positive-time monomial and a scale `0 < s ≤ b`.
DERIVED: `0` the plane and the lower end of the scale. -/
abbrev ProxyIx (b : ℝ) : Type := {x : TSepG Ix0 0 × ℝ // 0 < x.2 ∧ x.2 ≤ b}

/-- **The proxies' limit reflection kernel**: the `ultra` limit of `⟪B_k^{s}(P), B_k^{s'}(P')⟫_k`
(read by `ProxyGenLim` only on the diagonal, where `ProxyBound` makes it a limit).
DERIVED: `0` the plane and the reflection constant. -/
def kernB [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (b : ℝ) (x y : ProxyIx b) : ℝ :=
  limUnder (ultra : Filter ℕ) fun k =>
    rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
      (proxB Wf cf k x.1.2 x.1.1.1) (proxB Wf cf k y.1.2 y.1.1.1)

/-- **The proxies' limit mixed kernel** against the margin monomials of `W`: the `ultra` limit of
`proxX`. DERIVED: no numeral. -/
def mixB [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (b : ℝ) {r : ℝ}
    (x : ProxyIx b) (Q : MarginMono N 0 r) : ℝ :=
  limUnder (ultra : Filter ℕ) fun k => proxX W Wf cf k x.1.2 x.1.1.1 Q

/-- **The observer's flowed kernel on margin monomials** at `SU(N)`: `CompositeLink.gramF` with the
colour-count hypothesis `N ≠ 0` in place of `2 ≤ N` (the two are equal as functions). DERIVED: `0` the
plane. -/
abbrev gramFN [NeZero N] (W : ConfFlow N) (r : ℝ) (Q Q' : MarginMono N 0 r) : ℝ :=
  kernF (NeZero.ne N) (Φ0 W) 0 Q.1 Q'.1

/-- **Generation in the limit form**: `ApproxK` for the proxies' limit kernels against the observer's
flowed kernel on margin monomials. No step is read. DERIVED: no numeral. -/
def ProxyGenLim [NeZero N] (W : ConfFlow N) (b : ℝ) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (r : ℝ) : Prop :=
  ApproxK (kernB Wf cf b) (fun x (Q : MarginMono N 0 r) => mixB W Wf cf b x Q)
    (gramFN W r)

/-- **The squared distance converges to its limit form** under `UniformBoundF (Φ0 W)` and the bounds
of `ProxyBound` at one `(P, s)`. DERIVED: `2` the cross-term factor. -/
theorem tendsto_dist [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) (x : ProxyIx b)
    (hD : ∃ C : ℝ, ∀ᶠ k in (ultra : Filter ℕ), |proxD Wf cf k x.1.2 x.1.1.1| ≤ C)
    (hQ : ∀ Q : MarginMono N 0 r, ∃ C : ℝ, ∀ᶠ k in (ultra : Filter ℕ),
      |proxX W Wf cf k x.1.2 x.1.1.1 Q| ≤ C)
    (a : MarginMono N 0 r →₀ ℝ) :
    Tendsto (fun k => rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
        (proxB Wf cf k x.1.2 x.1.1.1 - yW W k a) (proxB Wf cf k x.1.2 x.1.1.1 - yW W k a))
      (ultra : Filter ℕ)
      (𝓝 (kernB Wf cf b x x - 2 * xL (fun Q => mixB W Wf cf b x Q) a
        + gForm (gramFN W r) a a)) := by
  obtain ⟨C, hC⟩ := hD
  have h1 : Tendsto (fun k => proxD Wf cf k x.1.2 x.1.1.1) (ultra : Filter ℕ)
      (𝓝 (kernB Wf cf b x x)) := tendsto_limUnder_ultra hC
  have h2 : Tendsto (fun k => xL (fun Q => proxX W Wf cf k x.1.2 x.1.1.1 Q) a) (ultra : Filter ℕ)
      (𝓝 (xL (fun Q => mixB W Wf cf b x Q) a)) :=
    tendsto_xL (g := fun k (Q : MarginMono N 0 r) => proxX W Wf cf k x.1.2 x.1.1.1 Q)
      (fun Q => tendsto_limUnder_ultra (hQ Q).choose_spec) a
  have h3 : Tendsto (fun k => gForm (fun Q Q' : MarginMono N 0 r =>
      latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1)) a a) (ultra : Filter ℕ)
      (𝓝 (gForm (gramFN W r) a a)) :=
    tendsto_gForm (G := fun k (Q Q' : MarginMono N 0 r) => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1))
      (fun Q Q' => tendsto_contSF (NeZero.ne N) (Φ0 W) hB (pairFam 0 Q.1 Q'.1)) a
  exact ((h1.sub (h2.const_mul 2)).add h3).congr fun k =>
    (rform_sub_proxB W Wf cf k x.1.2 x.1.1.1 a).symm

/-- **`ProxyGen` from the uniform bound and generation in the limit form.** Module docstring, §2.
DERIVED: `2` the halving of `η`. -/
theorem proxyGen_of_lim [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) (hb : ProxyBound W b Wf cf r)
    (hL : ProxyGenLim W b Wf cf r) : ProxyGen W b Wf cf r := by
  intro P s hs hsb η hη
  obtain ⟨a, ha⟩ := hL ⟨(P, s), hs, hsb⟩ (η / 2) (half_pos hη)
  refine ⟨a, ?_⟩
  obtain ⟨hD, hQ⟩ := hb P s hs hsb
  have hT := tendsto_dist hB ⟨(P, s), hs, hsb⟩ hD hQ a
  have hlt : kernB Wf cf b ⟨(P, s), hs, hsb⟩ ⟨(P, s), hs, hsb⟩
      - 2 * xL (fun Q => mixB W Wf cf b ⟨(P, s), hs, hsb⟩ Q) a
      + gForm (gramFN W r) a a < η := by
    have ha' : kernB Wf cf b ⟨(P, s), hs, hsb⟩ ⟨(P, s), hs, hsb⟩
        - 2 * xL (fun Q => mixB W Wf cf b ⟨(P, s), hs, hsb⟩ Q) a
        + gForm (gramFN W r) a a ≤ η / 2 := ha
    linarith
  filter_upwards [hT.eventually (gt_mem_nhds hlt)] with k hk
  exact hk.le

/-- **Generation in the limit form from `ProxyGen` and the uniform bound.** Module docstring, §2.
DERIVED: no numeral. -/
theorem proxyGenLim_of_proxyGen [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) (hb : ProxyBound W b Wf cf r)
    (hG : ProxyGen W b Wf cf r) : ProxyGenLim W b Wf cf r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  rintro ⟨⟨P, s⟩, hs, hsb⟩ ε hε
  obtain ⟨a, ha⟩ := hG P s hs hsb ε hε
  refine ⟨a, ?_⟩
  obtain ⟨hD, hQ⟩ := hb P s hs hsb
  exact le_of_tendsto (tendsto_dist hB ⟨(P, s), hs, hsb⟩ hD hQ a) ha

/-- **The mixed value of a symmetric form** is at most the mean of the diagonal values when the form
is nonnegative at `x − y` and `x + y`. DERIVED: `2` the mean and the cross-term factor. -/
theorem abs_form_le {X : Type*} [AddCommGroup X] [Module ℝ X] (F : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
    (hs : ∀ x y, F x y = F y x) (x y : X) (h1 : 0 ≤ F (x - y) (x - y))
    (h2 : 0 ≤ F (x + y) (x + y)) : |F x y| ≤ (F x x + F y y) / 2 := by
  have e1 : F (x - y) (x - y) = F x x - 2 * F x y + F y y := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hs y x]
    ring
  have e2 : F (x + y) (x + y) = F x x + 2 * F x y + F y y := by
    simp only [map_add, LinearMap.add_apply]
    rw [hs y x]
    ring
  rw [abs_le]
  constructor <;> linarith

/-- The reflection form is nonnegative on the half-space algebra. DERIVED: `0` the plane and the
sign. -/
theorem rform_nonneg_k [NeZero N] (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    0 ≤ rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) X X := by
  rw [rform_apply]
  exact stateK_rp (NeZero.ne N) k 0 X hX

/-- **The uniform bound from `ProxyGen`**, under `UniformBoundF (Φ0 W)`, `PhysRange r` and the
proxies' half-space membership. Module docstring, §2. DERIVED: `1` the tolerance read from
`ProxyGen` and the margin above each limit; `2` the parallelogram factor and the mean. -/
theorem proxyBound_of_proxyGen [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) (hphys : (Φ0 W).PhysRange r)
    (hM : ProxyMem b Wf cf) (hG : ProxyGen W b Wf cf r) : ProxyBound W b Wf cf r := by
  have hpos := Flow.posPreserving_of_physRange (NeZero.ne N) (Φ0 W) hphys 0
  intro P s hs hsb
  obtain ⟨a, ha⟩ := hG P s hs hsb 1 one_pos
  have hQa : ∀ᶠ k in atTop, ∀ Q ∈ a.support, prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    (Filter.eventually_all_finset a.support).mpr fun Q _ => eventually_flow_mem (Φ0 W) hpos Q
  have hYY : Tendsto (fun k => rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
      (yW W k a) (yW W k a)) (ultra : Filter ℕ) (𝓝 (gForm (gramFN W r) a a)) :=
    (tendsto_gForm (G := fun k (Q Q' : MarginMono N 0 r) => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1))
      (fun Q Q' => tendsto_contSF (NeZero.ne N) (Φ0 W) hB (pairFam 0 Q.1 Q'.1)) a).congr
      fun k => (rform_yW_self W k a).symm
  set g := gForm (gramFN W r) a a with hg
  have hdiag : ∀ᶠ k in (ultra : Filter ℕ),
      0 ≤ proxD Wf cf k s P.1 ∧ proxD Wf cf k s P.1 ≤ 2 * 1 + 2 * (g + 1) := by
    filter_upwards [hM P s hs hsb, ha, hQa.filter_mono ultra_le,
      hYY.eventually (gt_mem_nhds (lt_add_one g))] with k hBm hk hY hYk
    have hYm : yW W k a ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
      Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem _ _ (hY Q hQ)
    have hp := rform_para_le (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0))
      (rform_symm_k k) (proxB Wf cf k s P.1) (yW W k a) 0
      (rform_nonneg_k k (sub_mem (sub_mem hBm hYm) (sub_mem hYm (zero_mem _))))
    simp only [sub_zero] at hp
    exact ⟨rform_nonneg_k k hBm, by unfold proxD; linarith⟩
  refine ⟨⟨2 * 1 + 2 * (g + 1), hdiag.mono fun k hk => by
    rw [abs_le]; constructor <;> linarith [hk.1, hk.2,
      (show (0 : ℝ) ≤ 2 * 1 + 2 * (g + 1) by linarith [hk.1, hk.2])]⟩, fun Q => ?_⟩
  have hVV : Tendsto (fun k => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q.1)) (ultra : Filter ℕ)
      (𝓝 (gramFN W r Q Q)) := tendsto_contSF (NeZero.ne N) (Φ0 W) hB (pairFam 0 Q.1 Q.1)
  refine ⟨(2 * 1 + 2 * (g + 1) + (gramFN W r Q Q + 1)) / 2, ?_⟩
  filter_upwards [hdiag, hM P s hs hsb, (eventually_flow_mem (Φ0 W) hpos Q).filter_mono ultra_le,
    hVV.eventually (gt_mem_nhds (lt_add_one _))] with k hk hBm hVm hVk
  rw [latSF_pair_eq] at hVk
  have hab := abs_form_le (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)) (rform_symm_k k)
    (proxB Wf cf k s P.1) (prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1))
    (rform_nonneg_k k (sub_mem hBm hVm)) (rform_nonneg_k k (add_mem hBm hVm))
  unfold proxX
  unfold proxD at hk
  linarith [hk.2]

/-- **`ProxyGen` is the uniform bound together with generation in the limit form**, under
`UniformBoundF (Φ0 W)`, `PhysRange r` and the proxies' half-space membership. Module docstring, §2.
DERIVED: no numeral. -/
theorem proxyGen_iff [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) (hphys : (Φ0 W).PhysRange r)
    (hM : ProxyMem b Wf cf) :
    ProxyGen W b Wf cf r ↔ ProxyBound W b Wf cf r ∧ ProxyGenLim W b Wf cf r :=
  ⟨fun hG => ⟨proxyBound_of_proxyGen hB hphys hM hG,
      proxyGenLim_of_proxyGen hB (proxyBound_of_proxyGen hB hphys hM hG) hG⟩,
    fun h => proxyGen_of_lim hB h.1 h.2⟩

/-! ## 3. The uniform bound from the substrate -/

/-- **The uniform bound of the observer's flow from the substrate core**, at every `SU(N)`
(`CompositesRenAll.uv_of_scale`, `ClaySUFinal.classMoments_of_siteExp`, `ClaySUGap.uB`). -/
theorem uB_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCoreAt W z b Wf) : UniformBoundF (NeZero.ne N) (Φ0 W) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  exact ClaySUGap.uB (NeZero.ne N) W (ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS)

/-- **The uniform bound of the observer's flow from the substrate.** DERIVED: `2` the rank. -/
theorem uB_of_substrate {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow 2}
    (S : SubstrateAt W z b Wf) : UniformBoundF h2N (Φ0 W) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  exact ClaySUGap.uB h2N W (ClaySUFinal.classMoments_of_siteExp h2N W ht hS)

end MassGap.ProxyGenObserver

end

#print axioms MassGap.ProxyGenObserver.xL_escX
#print axioms MassGap.ProxyGenObserver.gForm_escG
#print axioms MassGap.ProxyGenObserver.esc_perStep
#print axioms MassGap.ProxyGenObserver.esc_fixed
#print axioms MassGap.ProxyGenObserver.esc_not_fixed
#print axioms MassGap.ProxyGenObserver.tendsto_escX
#print axioms MassGap.ProxyGenObserver.esc_limit_not_approxK
#print axioms MassGap.ProxyGenObserver.rform_sub_proxB
#print axioms MassGap.ProxyGenObserver.rform_yW_self
#print axioms MassGap.ProxyGenObserver.tendsto_limUnder_ultra
#print axioms MassGap.ProxyGenObserver.tendsto_dist
#print axioms MassGap.ProxyGenObserver.proxyGen_of_lim
#print axioms MassGap.ProxyGenObserver.proxyGenLim_of_proxyGen
#print axioms MassGap.ProxyGenObserver.abs_form_le
#print axioms MassGap.ProxyGenObserver.proxyBound_of_proxyGen
#print axioms MassGap.ProxyGenObserver.proxyGen_iff
#print axioms MassGap.ProxyGenObserver.uB_of_core
#print axioms MassGap.ProxyGenObserver.uB_of_substrate
