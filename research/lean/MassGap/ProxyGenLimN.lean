import Mathlib
import MassGap.FlowChoice
import MassGap.ApproxObserver

/-!
# MassGap.ProxyGenLimN — the part of `ProxyGenLim` the capstone consumes is `ApproxK`

`FlowChoice.FlowChoiceInputsN` (equivalently `SUNFromScale.FlowInputsN`) carries, at each `N ≥ 2`,
`ProxyGenObserver.ProxyGenLim W b Wf cf r` at the block-step observer `W = sunFam hN2 c hc0 hc s₀`: for
every separated positive-time monomial `P` and every flow time `0 < s ≤ b`, the `ultra` limit vector of
the flowed proxy `B^s(P)` lies in the closure of the span of the margin monomials of `W` (times beyond
`r > s₀`), in the limit reflection form. In the `FlowChoiceInputsN` chain it is read once, in
`SUNFromScale.inputsAt_of_flow`, through `ProxyGenObserver.proxyGen_of_lim` (with `uB_of_core`,
`proxyBound_of_core`) and `ApproxFromExpand.approxK_of_expandRP_SU`, to produce the field `approx` of
`SUNBest.InputsAt`: `ApproxK (kernC (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r)`. (The
`SU(2)` capstones at `obsW` in `ProxyGenObserver` and `ProxyBoundFromScale` take `ProxyGenLim` too.)
This module proves that, under `SubstrateCoreAt`, `GradientFlowPropsN` and `PhysRange r`, the part of
`ProxyGenLim` that this derivation uses (its germ at `s → 0⁺`) is equivalent to that `ApproxK`, states the capstone with `ApproxK` in place of `ProxyGenLim`, and proves what the choices of
`r`, `Wf`, `cf` change. Declarations are in the namespace `MassGap.ProxyGenLimN`.

## 1. The margin `r` (proved)

* `xL_mapDomainTo`, `gForm_mapDomainTo`: the mixed and Gram forms of a combination pushed along a map
  of observer indices are the forms of the pulled-back kernels.
* `approxK_comap`: `ApproxK Kc X G` passes to any `X'`, `G'` that restrict to `X`, `G` along a map.
* `marginIncl`: for `r' ≤ r`, every margin monomial beyond `r` is a margin monomial beyond `r'`.
* **`proxyGenLim_mono_r`**, **`approxKG_mono_r`**: `ProxyGenLim` and the capstone's `ApproxK` at `r` give
  them at every `r' ≤ r`. A smaller margin is weaker; the best choice is `r` close to `s₀`.

## 2. The germ of `ProxyGenLim` at `s → 0⁺` is `ApproxK` (proved)

`ExpandStrong` makes the composite `A(P)` its proxy `B^s(P)` in the reflection norm for all small `s`,
not only at one `s`; so the derivation of `ApproxK` needs the generation of the proxies only at
arbitrarily small `s`, and conversely `ApproxK` gives the generation at arbitrarily small `s`.

* `eventually_expandRP`: `ExpandStrong` gives, for every `P` and `η > 0`, for all small `s > 0`,
  eventually along `ultra`, `B_k^s(P)` in the half-space algebra and `⟪A_k − B_k^s, A_k − B_k^s⟫_k ≤ η`
  (`ExpandStrong.expandRP_of_strong` with the scale kept free).
* **`ProxyGenGerm W Wf cf r`**: for every `P` and `η > 0`, frequently as `s → 0⁺`, real coefficients
  `a` on the margin monomials with, eventually along `ultra`, `⟪B^s − Y(a), B^s − Y(a)⟫_k ≤ η`.
* **`ProxyGenLimGerm W b Wf cf r`**: the same in the limit form of `ProxyGenLim` (`kernB`, `mixB`,
  `gramFN`), at scales `0 < s ≤ b`.
* `limGerm_of_proxyGenLim`: `ProxyGenLim → ProxyGenLimGerm` (`0 < b`).
* `germ_of_limGerm`, `limGerm_of_germ`: under `UniformBoundF (Φ0 W)` and `ProxyBound`, the two germs are
  equivalent (`ProxyGenObserver.tendsto_dist`).
* **`approxK_of_germ`**: `ClassMoments`, `PhysRange r`, `CompOS (CRen N z μ)`, `ExpandStrong` and
  `ProxyGenGerm` give `ApproxK`: at a scale where both the germ and `eventually_expandRP` hold,
  `⟪A − Y⟫ ≤ 2⟪A − B⟫ + 2⟪B − Y⟫` (`ApproxFromExpand.rform_para_le`, all three in the half-space
  algebra), and the lattice value converges to the `ApproxK` expression.
* **`germ_of_approxK`**: the same inputs with `ApproxK` give `ProxyGenGerm`:
  `⟪B − Y⟫ ≤ 2⟪B − A⟫ + 2⟪A − Y⟫`.
* `compOS_of_core`: `SubstrateCoreAt` and `GradientFlowPropsN` give `CompOS (CRen N z μ)` (the block of
  `SUNFromScale.inputsAt_of_flow`).
* **`approxK_iff_limGerm`**: under `SubstrateCoreAt W z b Wf`, `GradientFlowPropsN Wf cf z μ` and
  `PhysRange r`, `ApproxK ↔ ProxyGenLimGerm W b Wf cf r`.
* **`approxK_of_proxyGenLim`**: under the same inputs, `ProxyGenLim → ApproxK`.
* **`limGerm_choice_iff`**: for two choices `(b, Wf, cf)`, `(b', Wf', cf')` meeting the core and the flow
  bundle at the same `W`, `z`, `μ`, `r`, the germ holds at one iff at the other. `ApproxK` reads neither
  `Wf` nor `cf`, so among choices meeting the core and the flow bundle, none makes the consumed clause
easier.

So the content of `ProxyGenLim` that `approxK_of_proxyGenLim` uses is its germ at `s → 0⁺`, which under
these inputs is equivalent to `ApproxK`; its content at `s` bounded away from `0` is not used.
`ProxyGenLim` itself is only shown to imply `ApproxK`.

## 3. `ApproxK` at the capstone's kernels: saturation, and what does not imply it (proved)

* `jointRPK_core`: `JointRPK (kernC) (mixKG) (gramF)` from `ClassMoments`, `PhysRange r`, `CompOS`
  (`CompositesRen.jointRPKG_of_reflLim`).
* **`approxK_iff_isLUB_core`**: under the core and the flow bundle, `ApproxK` holds iff for every
  composite `P`, `kernC(P, P)` is the least upper bound over finite real combinations `a` of
  `2 xL(mixKG P) a − gForm(gramF) a a` (`ApproxObserver.approxK_iff_isLUB`): the composite's reflected
  two-point function is saturated by the observer's margin monomials. Given vectors realising these
  kernels, this is membership of each composite vector in the closure of the real combinations of the margin
  vectors (`CompositeLink.approx_iff`); argued, since such vectors are not built for the composites (§5).
* `pairPos_of_jointRPK`, `gForm_nonneg_of_jointRPK`: `JointRPK Kc X G` makes `Kc` positive on pairs and
  `gForm G` non-negative.
* **`decoupled_of_jointRPK`**: if `JointRPK Kc X G` and `Kc(P, P) > 0` at one `P`, then with the same
  `Kc`, `G` and the mixed kernel replaced by `0`, `JointRPK` holds and `ApproxK` fails (the zero-mixing
  construction of `ApproxObserver.exists_jointRPK_not_approxK` at the given `Kc` and `G`).
* **`decoupled_core`**: at the capstone's own `kernC` and `gramF` (under `ClassMoments`, `PhysRange r`,
  `CompOS`), whenever `kernC(P, P) > 0` at one composite, zero mixing keeps `JointRPK` and refutes
  `ApproxK`. So `ApproxK` does not follow from `kernC`, `gramF` and `JointRPK` alone.

Argued (no declaration): no clause among `ExpandStrong`, `CoefBound`, `FlowCov`, `FlowWard`,
`ProxyNondeg`, `ScaleControlAll` and the substrate core reads a composite or a proxy against a margin
monomial of `W`. `ExpandStrong` reads composites against proxies at small `s`; the scale clause reads
one-site moments of each `Wf s`, including `Wf b = W`. Whether these clauses jointly force the lattice
`mixKG` is not proved either way.

## 4. The capstone (proved)

* `inputsAt_of_approx`: `SUNFromScale.inputsAt_of_flow` with `ProxyGenLim` replaced by `ApproxK`.
* `FlowApproxInputsN N hN2`: `FlowChoice.FlowChoiceInputsN` with `ProxyGenLim (sunFam …) b Wf cf r`
  replaced by `ApproxK (kernC (CRen N z μ) 0) (mixKG hN2 (sunFam …) (CRen N z μ) r) (gramF hN2 (sunFam …) r)`.
* `flowApproxInputsN_of_choice`: `FlowChoiceInputsN N hN2 → FlowApproxInputsN N hN2`.
* **`clayStatement_of_approx`**: `FlowApproxInputsN N hN2` at every `N ≥ 2` gives `ClayStatementDy`.

Per-`N` inputs of `clayStatement_of_approx`: `SubstrateCoreAt`, `ExpandStrong`, `CoefBound`, `FlowCov`,
`WardT`, `CompNondeg`, `ApproxK` at `r` (any `r > s₀`; by `approxKG_mono_r` the weakest is `r` near
`s₀`), the three-point clause and `WDeltaRun.RunSeed N`. `ApproxK` reads neither `Wf` nor `cf`.

## 5. What remains (argued; no declaration)

`ApproxK` at `W = sunFam hN2 c hc0 hc s₀`, margin `r > s₀`: each separated positive-time monomial of
renormalised composites of `CRen N z μ` (including times in `(0, r]`) is, in the limit reflection form, a limit of finite real
combinations of the observer's margin monomials beyond `r`. Two parts:
* the margin. `ApproxObserver.mem_of_apply_mem` reduces composites at times `≤ r` to their time
  translates beyond `r` in a Hilbert space holding both families with one injective transfer; that
  space is not built for the composites (their vectors are constructed from `ApproxK`,
  `CompositeLink.exists_link`).
* the generation. `Φ0 W` scales the plaquette class by `a_k⁻⁴` and every other field by `1`; the
  composites carry `a_k^{−d}` and their own subtractions. `decoupled_core` shows the clause does not
  follow from the composites' and the observer's own kernels with `JointRPK`. A semigroup `Wf` does not supply it: under
  `Wf b = Wf s` followed by the flow over `b − s`, the fields of `W` are functions of those of `Wf s`,
  the inclusion opposite to the one asked (`ApproxFromExpand` §4); and §2 shows that only `s → 0⁺` is
  read, where the proxies converge to the composites in the reflection norm (`eventually_expandRP`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count, the cross-term factor, the parallelogram factor and
the halving of `η`; `3` the sum of the three bounds of `ExpandStrong`; `4`, `8` the splits of the
tolerance; `0` the plane, the reflection constant, the limit of the scale, the zero mixed kernel and the
zero combination; `1` the sign `t = −1` reading the Gram form; `12` the bound of the block-step flow.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ProxyGenLimN

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
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ObserverFlowSUN MassGap.FlowChoice

variable {N : ℕ}

/-! ## 1. The margin -/

/-- The mixed form of a combination pushed along `g`. DERIVED: `0` the zero coefficient. -/
theorem xL_mapDomainTo {M M' : Type} (g : M → M') (X' : M' → ℝ) (c : M →₀ ℝ) :
    xL X' (c.mapDomain g) = xL (fun Q => X' (g Q)) c := by
  unfold xL
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- The Gram form of a combination pushed along `g`. DERIVED: `0` the zero coefficient. -/
theorem gForm_mapDomainTo {M M' : Type} (g : M → M') (G' : M' → M' → ℝ) (c : M →₀ ℝ) :
    gForm G' (c.mapDomain g) (c.mapDomain g) = gForm (fun Q Q' => G' (g Q) (g Q')) c c := by
  unfold gForm
  rw [Finsupp.sum_mapDomain_index (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr (fun P _ => ?_)
  exact Finsupp.sum_mapDomain_index (fun Q => by simp)
    (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

/-- **`ApproxK` passes along a map of observer indices** to kernels that restrict to the given ones.
DERIVED: no numeral. -/
theorem approxK_comap {I M M' : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ}
    {X' : I → M' → ℝ} {G' : M' → M' → ℝ} (g : M → M')
    (hX : ∀ P Q, X' P (g Q) = X P Q) (hG : ∀ Q Q', G' (g Q) (g Q') = G Q Q')
    (h : ApproxK Kc X G) : ApproxK Kc X' G' := by
  intro P ε hε
  obtain ⟨c, hc⟩ := h P ε hε
  refine ⟨c.mapDomain g, ?_⟩
  rw [xL_mapDomainTo, gForm_mapDomainTo]
  simp only [hX, hG]
  exact hc

/-- **A margin monomial beyond `r` is a margin monomial beyond every `r' ≤ r`.** DERIVED: `0` the
plane. -/
def marginIncl {r r' : ℝ} (h : r' ≤ r) (Q : MarginMono N 0 r) : MarginMono N 0 r' :=
  ⟨Q.1, by
    obtain ⟨d, hd, hrd, hP⟩ := Q.2
    exact ⟨d, hd, lt_of_le_of_lt h hrd, hP⟩⟩

/-- **`ProxyGenLim` at `r` gives it at every `r' ≤ r`.** DERIVED: no numeral. -/
theorem proxyGenLim_mono_r [NeZero N] {W : ConfFlow N} {b : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {r r' : ℝ} (h : r' ≤ r) (hL : ProxyGenLim W b Wf cf r) :
    ProxyGenLim W b Wf cf r' := by
  unfold ProxyGenLim at hL ⊢
  exact approxK_comap (marginIncl h) (fun _ _ => rfl) (fun _ _ => rfl) hL

/-- **The capstone's `ApproxK` at `r` gives it at every `r' ≤ r`.** DERIVED: `2` the least colour
count; `0` the plane. -/
theorem approxKG_mono_r (hN2 : 2 ≤ N) (W : ConfFlow N) (Cs : Composites N) {r r' : ℝ} (h : r' ≤ r)
    (hA : ApproxK (kernC (ne_zero_of_two_le hN2) Cs 0) (mixKG hN2 W Cs r) (gramF hN2 W r)) :
    ApproxK (kernC (ne_zero_of_two_le hN2) Cs 0) (mixKG hN2 W Cs r') (gramF hN2 W r') :=
  approxK_comap (marginIncl h) (fun _ _ => rfl) (fun _ _ => rfl) hA

/-! ## 2. The germ -/

/-- **`ExpandRP` at all small scales**: `ExpandStrong` gives, for every `P` and `η > 0`, for all small
`s > 0`, eventually along `ultra`, the proxy product in the half-space algebra and
`⟪A_k − B_k^s, A_k − B_k^s⟫_k ≤ η`. DERIVED: `3` the sum of the three bounds; `0` the plane and the limit
of the scale. -/
theorem eventually_expandRP [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (h : ExpandStrong Wf cf z μ) (P : TSepG (CRen N z μ).Ix 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      proxB Wf cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - proxB Wf cf k s P.1)
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - proxB Wf cf k s P.1)
        ≤ η := by
  obtain ⟨⟨θ, ε, Kr, κr, hθ, hε, hE⟩, hmem⟩ := h
  obtain ⟨hcont, d, hd, hsep⟩ := adm_pairC (CRen N z μ) P P
  have hc : ContD (jointD P.1 P.1.2) := hcont
  have hsd : SepD d (jointD P.1 P.1.2) := hsep
  obtain ⟨s₀, hs₀, hM⟩ := hmem P
  set c : ℝ := Kr ^ Fintype.card (Fin P.1.1 ⊕ Fin P.1.1)
    * ∏ x, ((d ^ κr (jointD P.1 P.1.2 x).1)⁻¹ * l1 (jointD P.1 P.1.2 x).2) with hcdef
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c * (s / d) ^ ε < η / 3 ∧ s < θ * d ∧ s < s₀ ∧ 0 < s :=
    (eventually_rate_lt hε c (by positivity : 0 < η / 3)).and
      (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
        (((gt_mem_nhds hs₀).filter_mono nhdsWithin_le_nhds).and
          (eventually_mem_nhdsWithin.mono fun s hs => hs)))
  filter_upwards [hev] with s hs
  obtain ⟨hs1, hs2, hs4, hs5⟩ := hs
  filter_upwards [(rform_sub_le_of_strong hE P.1 hd hc hsd hs5 hs2.le).filter_mono ultra_le,
    hM s hs5 hs4.le] with k hk hm
  refine ⟨hm, ?_⟩
  have hr : Kr ^ Fintype.card (Fin P.1.1 ⊕ Fin P.1.1) * (s / d) ^ ε
      * ∏ x, ((d ^ κr (jointD P.1 P.1.2 x).1)⁻¹ * l1 (jointD P.1 P.1.2 x).2) = c * (s / d) ^ ε := by
    rw [hcdef]
    ring
  rw [hr] at hk
  show rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
      (compF z μ k P.1.2 - proxF Wf cf k s P.1.2) (compF z μ k P.1.2 - proxF Wf cf k s P.1.2) ≤ η
  linarith

/-- **Generation of the proxies at arbitrarily small flow time**, in the lattice reflection form.
DERIVED: `0` the plane, the signs and the limit of the scale. -/
def ProxyGenGerm [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (r : ℝ) : Prop :=
  ∀ (P : TSepG Ix0 0) (η : ℝ), 0 < η → ∃ᶠ s in 𝓝[>] (0 : ℝ), ∃ a : MarginMono N 0 r →₀ ℝ,
    ∀ᶠ k in (ultra : Filter ℕ),
      rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
        (proxB Wf cf k s P.1 - yW W k a) (proxB Wf cf k s P.1 - yW W k a) ≤ η

/-- **Generation of the proxies at arbitrarily small flow time**, in the limit form of
`ProxyGenLim`. DERIVED: `2` the cross-term factor; `0` the signs and the limit of the scale. -/
def ProxyGenLimGerm [NeZero N] (W : ConfFlow N) (b : ℝ) (Wf : ℝ → ConfFlow N)
    (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (r : ℝ) : Prop :=
  ∀ (P : TSepG Ix0 0) (η : ℝ), 0 < η → ∃ᶠ s in 𝓝[>] (0 : ℝ), ∃ hs : 0 < s ∧ s ≤ b,
    ∃ a : MarginMono N 0 r →₀ ℝ,
      kernB Wf cf b ⟨(P, s), hs⟩ ⟨(P, s), hs⟩
        - 2 * xL (fun Q => mixB W Wf cf b ⟨(P, s), hs⟩ Q) a + gForm (gramFN W r) a a ≤ η

/-- The scales `0 < s ≤ b` are a neighbourhood of `0⁺`. DERIVED: `0` the limit of the scale. -/
theorem eventually_scale_window {b : ℝ} (hb : 0 < b) : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ b :=
  (eventually_mem_nhdsWithin.mono fun _ hs => hs).and
    (((gt_mem_nhds hb).filter_mono nhdsWithin_le_nhds).mono fun _ hs => le_of_lt hs)

/-- **`ProxyGenLim` gives its germ.** DERIVED: `0` the lower end of the scale. -/
theorem limGerm_of_proxyGenLim [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hb0 : 0 < b) (hL : ProxyGenLim W b Wf cf r) :
    ProxyGenLimGerm W b Wf cf r := by
  intro P η hη
  apply Filter.Eventually.frequently
  filter_upwards [eventually_scale_window hb0] with s hs
  exact ⟨hs, hL ⟨(P, s), hs⟩ η hη⟩

/-- **The lattice germ from the limit germ**, under `UniformBoundF (Φ0 W)` and `ProxyBound`.
DERIVED: `2` the halving of `η`. -/
theorem germ_of_limGerm [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hB : UniformBoundF (NeZero.ne N) (Φ0 W))
    (hb : ProxyBound W b Wf cf r) (hL : ProxyGenLimGerm W b Wf cf r) : ProxyGenGerm W Wf cf r := by
  intro P η hη
  apply (hL P (η / 2) (half_pos hη)).mono
  rintro s ⟨hs, a, ha⟩
  refine ⟨a, ?_⟩
  obtain ⟨hD, hQ⟩ := hb P s hs.1 hs.2
  have hT := tendsto_dist hB ⟨(P, s), hs⟩ hD hQ a
  have hlt : kernB Wf cf b ⟨(P, s), hs⟩ ⟨(P, s), hs⟩
      - 2 * xL (fun Q => mixB W Wf cf b ⟨(P, s), hs⟩ Q) a + gForm (gramFN W r) a a < η := by
    linarith
  filter_upwards [hT.eventually (gt_mem_nhds hlt)] with k hk
  exact hk.le

/-- **The limit germ from the lattice germ**, under `UniformBoundF (Φ0 W)`, `ProxyBound` and `0 < b`.
DERIVED: `0` the lower end of the scale. -/
theorem limGerm_of_germ [NeZero N] {W : ConfFlow N} {b r : ℝ} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hB : UniformBoundF (NeZero.ne N) (Φ0 W))
    (hb : ProxyBound W b Wf cf r) (hb0 : 0 < b) (hG : ProxyGenGerm W Wf cf r) :
    ProxyGenLimGerm W b Wf cf r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro P η hη
  apply ((hG P η hη).and_eventually (eventually_scale_window hb0)).mono
  rintro s ⟨⟨a, ha⟩, hs⟩
  refine ⟨hs, a, ?_⟩
  obtain ⟨hD, hQ⟩ := hb P s hs.1 hs.2
  exact le_of_tendsto (tendsto_dist hB ⟨(P, s), hs⟩ hD hQ a) ha

/-- **`ApproxK` from `ExpandStrong` and the germ**, at every `SU(N)`. Module docstring, §2.
DERIVED: `4` and `2` the split `ε = 2 (ε/4) + 2 (ε/4)`; `2` the least colour count; `0` the plane. -/
theorem approxK_of_germ (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hCO : CompOS (NeZero.ne N) (CRen N z μ)) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandStrong Wf cf z μ) (hG : ProxyGenGerm W Wf cf r) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r)
      (gramF hN2 W r) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hUL : UnifLocal (CRen N z μ) := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  have hMC := mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO
  have hRL := reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO hMC
  have hpos := Flow.posPreserving_of_physRange (NeZero.ne N) (Φ0 W) hphys 0
  intro P ε hε
  obtain ⟨s, ⟨a, ha⟩, hEs⟩ := ((hG P (ε / 4) (by positivity)).and_eventually
    (eventually_expandRP hE P (by positivity : (0 : ℝ) < ε / 4))).exists
  refine ⟨a, ?_⟩
  have hX : Tendsto (fun k => xL (fun Q : MarginMono N 0 r =>
      rMixC (NeZero.ne N) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1) a) (ultra : Filter ℕ)
      (𝓝 (xL (mixKG hN2 W (CRen N z μ) r P) a)) :=
    tendsto_xL (g := fun k (Q : MarginMono N 0 r) => rMixC (NeZero.ne N) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1)
      (fun Q => hRL.2 P Q) a
  have hGr : Tendsto (fun k => gForm (fun Q Q' : MarginMono N 0 r =>
      latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1)) a a) (ultra : Filter ℕ)
      (𝓝 (gForm (gramF hN2 W r) a a)) :=
    tendsto_gForm (G := fun k (Q Q' : MarginMono N 0 r) => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1))
      (fun Q Q' => tendsto_contSF (NeZero.ne N) (Φ0 W) (ClaySUGap.uB (NeZero.ne N) W hU) (pairFam 0 Q.1 Q'.1)) a
  have hT := (((hRL.1 P P).sub (hX.const_mul 2)).add hGr).congr fun k =>
    (rform_sub_yW W z μ k P.1 a).symm
  have hQ : ∀ᶠ k in atTop, ∀ Q ∈ a.support, prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    (Filter.eventually_all_finset a.support).mpr fun Q _ => eventually_flow_mem (Φ0 W) hpos Q
  have hev : ∀ᶠ k in (ultra : Filter ℕ),
      rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
        (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - yW W k a)
        (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - yW W k a) ≤ ε := by
    filter_upwards [hEs, ha, (eventually_cMono_mem (NeZero.ne N) (CRen N z μ) hUL P).filter_mono ultra_le,
      hQ.filter_mono ultra_le] with k hk1 hk2 hA hY
    have hYm : yW W k a ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
      Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem _ _ (hY Q hQ)
    have hp := rform_para_le (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0))
      (rform_symm_k k)
      (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1)) (proxB Wf cf k s P.1) (yW W k a)
      (by
        rw [rform_apply]
        exact stateK_rp (NeZero.ne N) k 0 _ (sub_mem (sub_mem hA hk1.1) (sub_mem hk1.1 hYm)))
    linarith [hk1.2]
  exact le_of_tendsto hT hev

/-- **The germ from `ExpandStrong` and `ApproxK`**, at every `SU(N)`. Module
docstring, §2. DERIVED: `8`, `4` and `2` the split `η = 2 (η/4) + 2 (η/4)` with `η/8 < η/4`; `2` the
least colour count; `0` the plane. -/
theorem germ_of_approxK (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hCO : CompOS (NeZero.ne N) (CRen N z μ)) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandStrong Wf cf z μ)
    (hA : ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r)
      (gramF hN2 W r)) :
    ProxyGenGerm W Wf cf r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hUL : UnifLocal (CRen N z μ) := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  have hMC := mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO
  have hRL := reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO hMC
  have hpos := Flow.posPreserving_of_physRange (NeZero.ne N) (Φ0 W) hphys 0
  intro P η hη
  obtain ⟨a, ha⟩ := hA P (η / 8) (by positivity)
  have hX : Tendsto (fun k => xL (fun Q : MarginMono N 0 r =>
      rMixC (NeZero.ne N) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1) a) (ultra : Filter ℕ)
      (𝓝 (xL (mixKG hN2 W (CRen N z μ) r P) a)) :=
    tendsto_xL (g := fun k (Q : MarginMono N 0 r) => rMixC (NeZero.ne N) (CRen N z μ) (Φ0 W) 0 k P.1 Q.1)
      (fun Q => hRL.2 P Q) a
  have hGr : Tendsto (fun k => gForm (fun Q Q' : MarginMono N 0 r =>
      latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1)) a a) (ultra : Filter ℕ)
      (𝓝 (gForm (gramF hN2 W r) a a)) :=
    tendsto_gForm (G := fun k (Q Q' : MarginMono N 0 r) => latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 Q.1 Q'.1))
      (fun Q Q' => tendsto_contSF (NeZero.ne N) (Φ0 W) (ClaySUGap.uB (NeZero.ne N) W hU) (pairFam 0 Q.1 Q'.1)) a
  have hT := (((hRL.1 P P).sub (hX.const_mul 2)).add hGr).congr fun k =>
    (rform_sub_yW W z μ k P.1 a).symm
  have hlt : kernC (NeZero.ne N) (CRen N z μ) 0 P P - 2 * xL (mixKG hN2 W (CRen N z μ) r P) a
      + gForm (gramF hN2 W r) a a < η / 4 := lt_of_le_of_lt ha (by linarith)
  have hAY := hT.eventually (gt_mem_nhds hlt)
  have hQ : ∀ᶠ k in atTop, ∀ Q ∈ a.support, prodSmear (dySpacing N k) ((Φ0 W).mono k Q.1)
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    (Filter.eventually_all_finset a.support).mpr fun Q _ => eventually_flow_mem (Φ0 W) hpos Q
  apply Filter.Eventually.frequently
  filter_upwards [eventually_expandRP hE P (by positivity : (0 : ℝ) < η / 4)] with s hs
  refine ⟨a, ?_⟩
  filter_upwards [hs, hAY, (eventually_cMono_mem (NeZero.ne N) (CRen N z μ) hUL P).filter_mono ultra_le,
    hQ.filter_mono ultra_le] with k hk1 hk2 hA' hY
  have hYm : yW W k a ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem _ _ (hY Q hQ)
  set A := prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) with hAdef
  set B := proxB Wf cf k s P.1 with hBdef
  set Y := yW W k a with hYdef
  have hp := rform_para_le (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0))
    (rform_symm_k k) B A Y
    (by
      rw [rform_apply]
      exact stateK_rp (NeZero.ne N) k 0 _ (sub_mem (sub_mem hk1.1 hA') (sub_mem hA' hYm)))
  have hsym : rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (B - A) (B - A)
      = rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (A - B) (A - B) := by
    rw [show B - A = -(A - B) from (neg_sub A B).symm]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  have h1 := hk1.2
  have h2 := hk2.le
  linarith

/-- **`CompOS` of the renormalised composites from the substrate core and the flow bundle** (the block
of `SUNFromScale.inputsAt_of_flow`). DERIVED: no numeral. -/
theorem compOS_of_core [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf)
    (F : GradientFlowPropsN Wf cf z μ) : CompOS (NeZero.ne N) (CRen N z μ) :=
  ⟨convC_of_core S F.props,
    os0C_of_scale_expand_coef S.b_pos S.scale (expandR_of_strong F.props.expand) F.props.coef,
    os1C_of_scale_expand S.b_pos S.scale (expandR_of_strong F.props.expand),
    covC_of_scale_strong S.b_pos S.scale F.props.expand F.props.cov,
    compNondeg_of_core S F.props F.nondeg⟩

/-- **The consumed part of `ProxyGenLim` is `ApproxK`**: under the substrate core, the flow bundle and
`PhysRange r`, `ApproxK ↔ ProxyGenLimGerm`. Module docstring, §2. DERIVED: `2` the least colour count;
`0` the plane. -/
theorem approxK_iff_limGerm (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b Wf)
    (F : GradientFlowPropsN Wf cf z μ) (hphys : (Φ0 W).PhysRange r) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r)
      ↔ ProxyGenLimGerm W b Wf cf r := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_core S F
  have hB := uB_of_core S
  have hb : ProxyBound W b Wf cf r := proxyBound_of_core S
  exact ⟨fun hA => limGerm_of_germ hB hb S.b_pos (germ_of_approxK hN2 hU hphys hCO F.props.expand hA),
    fun hL => approxK_of_germ hN2 hU hphys hCO F.props.expand (germ_of_limGerm hB hb hL)⟩

/-- **`ProxyGenLim` gives `ApproxK`** under the substrate core, the flow bundle and `PhysRange r`.
DERIVED: `2` the least colour count; `0` the plane. -/
theorem approxK_of_proxyGenLim (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (F : GradientFlowPropsN Wf cf z μ) (hphys : (Φ0 W).PhysRange r)
    (hL : ProxyGenLim W b Wf cf r) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) :=
  (approxK_iff_limGerm hN2 S F hphys).2 (limGerm_of_proxyGenLim S.b_pos hL)

/-- **The germ does not depend on the choice** of `(b, Wf, cf)` among those meeting the substrate core
and the flow bundle at the same `W`, `z`, `μ`, `r`. DERIVED: `2` the least colour count. -/
theorem limGerm_choice_iff (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    {b b' r : ℝ} {Wf Wf' : ℝ → ConfFlow N} {cf cf' : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (F : GradientFlowPropsN Wf cf z μ)
    (S' : SubstrateCoreAt W z b' Wf') (F' : GradientFlowPropsN Wf' cf' z μ)
    (hphys : (Φ0 W).PhysRange r) :
    ProxyGenLimGerm W b Wf cf r ↔ ProxyGenLimGerm W b' Wf' cf' r :=
  (approxK_iff_limGerm hN2 S F hphys).symm.trans (approxK_iff_limGerm hN2 S' F' hphys)

/-! ## 3. Saturation and the decoupled mixed kernel -/

/-- **Joint reflection positivity at the capstone's kernels.** DERIVED: `2` the least colour count;
`0` the plane. -/
theorem jointRPK_core (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hCO : CompOS (NeZero.ne N) (CRen N z μ)) :
    JointRPK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) := by
  have hUL : UnifLocal (CRen N z μ) := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  exact jointRPKG_of_reflLim hN2 W hU hphys (CRen N z μ) hUL
    (reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO
      (mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO))

/-- **`ApproxK` is the saturation of the composites' reflected two-point function** by the observer's
margin monomials, under the substrate core, the flow bundle and `PhysRange r`. Module docstring, §3.
DERIVED: `2` the least colour count; `0` the plane. -/
theorem approxK_iff_isLUB_core (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (F : GradientFlowPropsN Wf cf z μ) (hphys : (Φ0 W).PhysRange r) :
    ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r)
      ↔ ∀ P, IsLUB (Set.range (ApproxObserver.gain (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P))
          (kernC (NeZero.ne N) (CRen N z μ) 0 P P) := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  exact ApproxObserver.approxK_iff_isLUB (jointRPK_core hN2 hU hphys (compOS_of_core S F))

/-- The mixed form of the zero combination is `0`. DERIVED: `0` the zero combination. -/
theorem xL_zero_coef {M : Type} (g : M → ℝ) : xL g (0 : M →₀ ℝ) = 0 := by
  unfold xL
  exact Finsupp.sum_zero_index

/-- **`JointRPK` makes the composites' kernel positive on pairs** (`c = 0`). DERIVED: `0` the zero
combination. -/
theorem pairPos_of_jointRPK {I M : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ}
    (hJ : JointRPK Kc X G) : ApproxObserver.PairPos Kc := by
  intro P P' t
  have h := hJ P P' t 0
  rw [xL_zero_coef, xL_zero_coef, gForm_zero_left] at h
  show 0 ≤ Kc P P + 2 * t * Kc P P' + t ^ 2 * Kc P' P'
  linarith

/-- **`JointRPK` makes the observer's Gram form non-negative** (`P' = P`, `t = −1`). DERIVED: `1` the
sign `t = −1`; `0` the sign. -/
theorem gForm_nonneg_of_jointRPK {I M : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ}
    (hJ : JointRPK Kc X G) (P : I) (c : M →₀ ℝ) : 0 ≤ gForm G c c := by
  have h := hJ P P (-1) c
  have e : Kc P P + 2 * (-1) * Kc P P + (-1) ^ 2 * Kc P P - 2 * xL (X P) c - 2 * (-1) * xL (X P) c
      + gForm G c c = gForm G c c := by ring
  linarith

/-- **The decoupled mixed kernel**: from `JointRPK Kc X G` and `Kc(P, P) > 0`, the same `Kc`, `G` with
mixed kernel `0` satisfy `JointRPK` and not `ApproxK`. Module docstring, §3. DERIVED: `0` the zero mixed
kernel; `2` the halving of `Kc(P, P)` and the cross-term factor. -/
theorem decoupled_of_jointRPK {I M : Type} {Kc : I → I → ℝ} {X : I → M → ℝ} {G : M → M → ℝ}
    (hJ : JointRPK Kc X G) {P : I} (hP : 0 < Kc P P) :
    JointRPK Kc (fun (_ : I) (_ : M) => (0 : ℝ)) G
      ∧ ¬ ApproxK Kc (fun (_ : I) (_ : M) => (0 : ℝ)) G := by
  have hx : ∀ c : M →₀ ℝ, xL (fun _ : M => (0 : ℝ)) c = 0 := fun c => by
    unfold xL
    simp
  refine ⟨fun P₁ P₂ t c => ?_, fun hA => ?_⟩
  · have h1 := pairPos_of_jointRPK hJ P₁ P₂ t
    have h2 := gForm_nonneg_of_jointRPK hJ P c
    show 0 ≤ Kc P₁ P₁ + 2 * t * Kc P₁ P₂ + t ^ 2 * Kc P₂ P₂ - 2 * xL (fun _ : M => (0 : ℝ)) c
      - 2 * t * xL (fun _ : M => (0 : ℝ)) c + gForm G c c
    rw [hx]
    have h1' : 0 ≤ Kc P₁ P₁ + 2 * t * Kc P₁ P₂ + t ^ 2 * Kc P₂ P₂ := h1
    linarith
  · obtain ⟨c, hc⟩ := hA P (Kc P P / 2) (by positivity)
    have hc' : Kc P P - 2 * xL (fun _ : M => (0 : ℝ)) c + gForm G c c ≤ Kc P P / 2 := hc
    rw [hx] at hc'
    linarith [gForm_nonneg_of_jointRPK hJ P c]

/-- **The decoupled mixed kernel at the capstone's own kernels**: whenever `kernC(P, P) > 0` at one
composite, `kernC`, `gramF` with zero mixing satisfy `JointRPK` and not `ApproxK`. Module docstring,
§3. DERIVED: `2` the least colour count; `0` the plane and the zero mixed kernel. -/
theorem decoupled_core (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hCO : CompOS (NeZero.ne N) (CRen N z μ))
    {P : TSepG (CRen N z μ).Ix 0} (hP : 0 < kernC (NeZero.ne N) (CRen N z μ) 0 P P) :
    JointRPK (kernC (NeZero.ne N) (CRen N z μ) 0)
        (fun (_ : TSepG (CRen N z μ).Ix 0) (_ : MarginMono N 0 r) => (0 : ℝ)) (gramF hN2 W r)
      ∧ ¬ ApproxK (kernC (NeZero.ne N) (CRen N z μ) 0)
        (fun (_ : TSepG (CRen N z μ).Ix 0) (_ : MarginMono N 0 r) => (0 : ℝ)) (gramF hN2 W r) :=
  decoupled_of_jointRPK (jointRPK_core hN2 hU hphys hCO) hP

/-! ## 4. The capstone -/

/-- **`SUNFromScale.inputsAt_of_flow` with `ApproxK` in place of `ProxyGenLim`.** DERIVED: `2` the
least colour count; `0` the lower end of the observer's scale; `12` the bound of the block-step flow. -/
theorem inputsAt_of_approx (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ r : ℝ} (hs0 : 0 ≤ s₀) (hr : s₀ < r)
    {zri zwe : ℕ → ℝ} (hri : ∀ k, zri k ≠ 0) (hwe : ∀ k, zwe k ≠ 0) {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf)
    (F : GradientFlowPropsN Wf cf (ZCanon.zFix N zri zwe) μ)
    (hA : ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
      (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
      (gramF hN2 (sunFam hN2 c hc0 hc s₀) r))
    (h3 : ∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
    (hfar : WDeltaRun.RunSeed N) :
    ∃ (t C : ℝ) (G : ℝ → ℝ),
      SUNBest.InputsAt hN2 (sunFam hN2 c hc0 hc s₀) r t |C| zri zwe μ G := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) (sunFam hN2 c hc0 hc s₀) ht hS
  obtain ⟨G, hK, hAF⟩ := S.af
  obtain ⟨ℓ, hℓ, h3'⟩ := h3
  exact ⟨t, C, G,
    { t_pos := ht
      moments := hU
      phys := sunFam_physRange hN2 hc0 hc hs0 hr
      far := hfar
      hri := hri
      hwe := hwe
      kernel := hK
      af := hAF
      low := obsLower_of_scale (ne_zero_of_two_le hN2) hℓ zri zwe h3'
      ward := wardT_of_core S F.props
      comp := compOS_of_core S F
      approx := hA }⟩

/-- **The per-`N` inputs with `ApproxK` in place of `ProxyGenLim`**: `FlowChoice.FlowChoiceInputsN` with
its clause `ProxyGenLim (sunFam …) b Wf cf r` replaced by the capstone's `ApproxK` at `r`.
DERIVED: `2` the least colour count; `0` the lower end of the observer's scale; `12` the bound of the
block-step flow. -/
def FlowApproxInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ FlowCov Wf cf
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ ApproxK (kernC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ) 0)
          (mixKG hN2 (sunFam hN2 c hc0 hc s₀) (CRen N (ZCanon.zFix N zri zwe) μ) r)
          (gramF hN2 (sunFam hN2 c hc0 hc s₀) r)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ WDeltaRun.RunSeed N

/-- **`FlowChoiceInputsN` gives `FlowApproxInputsN`** (`approxK_of_proxyGenLim`). DERIVED: `2` the
least colour count. -/
theorem flowApproxInputsN_of_choice (hN2 : 2 ≤ N) (h : FlowChoiceInputsN N hN2) :
    FlowApproxInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hL, h3,
    hfar⟩ := h
  exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
    approxK_of_proxyGenLim hN2 S ((gradientFlowPropsN_iff S.b_pos S.scale).2 ⟨hE, hC, hV, hW, hP⟩)
      (sunFam_physRange hN2 hc0 hc hs0 hr) hL, h3, hfar⟩

/-- **`ClayStatementDy` from `FlowApproxInputsN` at every `N ≥ 2`** (`SUNBest.clayStatement_of_inputs`).
DERIVED: `2` the least colour count. -/
theorem clayStatement_of_approx (h : ∀ (N : ℕ) (hN2 : 2 ≤ N), FlowApproxInputsN N hN2) :
    MassGap.ClayStatementDy :=
  SUNBest.clayStatement_of_inputs fun N hN2 => by
    haveI : NeZero N := ⟨by omega⟩
    obtain ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hA, h3,
      hfar⟩ := h N hN2
    obtain ⟨t, C, G, I⟩ := inputsAt_of_approx hN2 hc0 hc hs0 hr hri hwe S
      ((gradientFlowPropsN_iff S.b_pos S.scale).2 ⟨hE, hC, hV, hW, hP⟩) hA h3 hfar
    exact ⟨sunFam hN2 c hc0 hc s₀, r, t, |C|, zri, zwe, μ, G, I⟩

end MassGap.ProxyGenLimN

end

#print axioms MassGap.ProxyGenLimN.xL_mapDomainTo
#print axioms MassGap.ProxyGenLimN.gForm_mapDomainTo
#print axioms MassGap.ProxyGenLimN.approxK_comap
#print axioms MassGap.ProxyGenLimN.proxyGenLim_mono_r
#print axioms MassGap.ProxyGenLimN.approxKG_mono_r
#print axioms MassGap.ProxyGenLimN.eventually_expandRP
#print axioms MassGap.ProxyGenLimN.eventually_scale_window
#print axioms MassGap.ProxyGenLimN.limGerm_of_proxyGenLim
#print axioms MassGap.ProxyGenLimN.germ_of_limGerm
#print axioms MassGap.ProxyGenLimN.limGerm_of_germ
#print axioms MassGap.ProxyGenLimN.approxK_of_germ
#print axioms MassGap.ProxyGenLimN.germ_of_approxK
#print axioms MassGap.ProxyGenLimN.compOS_of_core
#print axioms MassGap.ProxyGenLimN.approxK_iff_limGerm
#print axioms MassGap.ProxyGenLimN.approxK_of_proxyGenLim
#print axioms MassGap.ProxyGenLimN.limGerm_choice_iff
#print axioms MassGap.ProxyGenLimN.jointRPK_core
#print axioms MassGap.ProxyGenLimN.approxK_iff_isLUB_core
#print axioms MassGap.ProxyGenLimN.xL_zero_coef
#print axioms MassGap.ProxyGenLimN.pairPos_of_jointRPK
#print axioms MassGap.ProxyGenLimN.gForm_nonneg_of_jointRPK
#print axioms MassGap.ProxyGenLimN.decoupled_of_jointRPK
#print axioms MassGap.ProxyGenLimN.decoupled_core
#print axioms MassGap.ProxyGenLimN.inputsAt_of_approx
#print axioms MassGap.ProxyGenLimN.flowApproxInputsN_of_choice
#print axioms MassGap.ProxyGenLimN.clayStatement_of_approx
