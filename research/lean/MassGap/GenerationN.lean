import Mathlib
import MassGap.ClayNarrow

/-!
# MassGap.GenerationN — what the generation clause of `NarrowInputsN` asks, per composite

`ClayNarrow.NarrowInputsN N hN2` carries the generation clause
`∀ P, BeyondR r P → ApproxKAt (kernC (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P` at
`W = sunFam hN2 c hc0 hc s₀`. This module reads its objects, reduces the clause per composite to a lattice
statement about the flowed proxies, gives a sufficient identification, and proves the clause outright at the
constant flow `Wf ≡ W` with coefficients on the plaquette channels. Declarations are in the namespace
`MassGap.GenerationN`.

## 0. The objects (read from their definitions)

* A margin monomial `Q : MarginMono N 0 r` is a monomial `⟨n, (Oᵢ, fᵢ)ᵢ⟩` of arbitrary local gauge-invariant
  fields `Oᵢ : LField` with test functions `fᵢ` vanishing below a time `d > max(0, r)`. The observer reads
  it through `Φ0 W = energy0 W (SymPlaqClass N)`: at step `k`, `Oᵢ ∘ V_k^W` scaled by `a_k⁻⁴` if `Oᵢ` is a
  symmetrised plaquette, by `1` otherwise, no subtraction (`phi0_map_of_mem`, `phi0_map_of_not_mem`). The
  field `Oᵢ` does not depend on `k`; only the flow `V_k^W` and the class factor do. Every local
  gauge-invariant field enters a margin monomial (`oneMargin`). For the channel fields `bR N i`,
  `SubstrateCoreAt.scale` at `s = b` (with `top`) gives `ν_k |bR ∘ V_k^W| = O(a_k^{cdim})` (`cdim ≥ 2`), so
  those observer readings vanish in the limit (argued from `scale` at `s = b`; no declaration — the plaquette
  analogue is `plaqMean_bound`); the entries off the plaquette class that can contribute are
  fields outside the channel list, about which nothing is proved here.
* The proxy `B_k^s(P) = proxB Wf cf k s P` is `∏ᵢ smear a_k (∑_j cf(Pᵢ, s, j) · msFlow j) fᵢ` with
  `msFlow Wf k s j = a_k^{−d_j} (O_j ∘ V_k^{(s)} − ν_k(O_j ∘ V_k^{(s)}))`, `O_j = mField j` (a bare monomial
  `bR N i` of dimension `cdim`, or a symmetrised plaquette of dimension `4`), flowed by `Wf s`.
* A real combination of margin monomials at step `k` is `yW W k a = ∑_Q a_Q ∏ smear a_k (Φ0 W field) f`.

## 1. The clause per composite (proved)

* `ProxyGermAt W Wf cf r P`: for every `η > 0`, frequently as `s → 0⁺`, coefficients `a` on the margin
  monomials with, eventually along `ultra`, `⟪B^s(P) − Y(a), B^s(P) − Y(a)⟫_k ≤ η`.
  `proxyGenGerm_iff`: `ProxyGenLimN.ProxyGenGerm` is `ProxyGermAt` at every `P`.
* `approxKAt_of_germAt`, `germAt_of_approxKAt`: `ProxyGenLimN.approxK_of_germ` and `germ_of_approxK` at one
  composite.
* **`approxKAt_iff_germAt`**: under the narrow core (`SubstrateCoreAt`, `ExpandStrong`, `CoefBound`, `CovC`,
  `CompNondeg`) and `PhysRange r`, `ApproxKAt … P ↔ ProxyGermAt W Wf cf r P`, at each `P`.
* **`generation_iff_germ`**: the generation clause of `NarrowInputsN` is `ProxyGermAt` at every `P` beyond `r`.
* `germAt_choice_iff`: two choices `(b, Wf, cf)` meeting the narrow core at the same `W`, `z`, `μ`, `r`
  have the same germ at every `P`.

## 2. A sufficient identification (proved)

* `CoefFamAt W Wf cf r P`: frequently as `s → 0⁺`, a finite family of margin monomials `Q m` and
  coefficients `β k m`, each eventually bounded in `k`, with `B_k^s(P) = ∑_m β k m · Y_k(Q m)` eventually
  along `ultra`. (Bounded sequences converge along `ultra`, so `k`-dependent subtraction constants are
  allowed.)
* `rform_fam_eq`: `⟪∑ e_m V_m, ∑ e_m V_m⟫_k` is the double sum of `e_m e_m' latSF(ΘQ_m ∪ Q_m')`.
* **`germAt_of_coefFam`**: under `UniformBoundF (Φ0 W)`, `CoefFamAt → ProxyGermAt`.
* **`generation_of_coefFam`**: under the narrow core and `PhysRange r`, `CoefFamAt` at every `P` beyond `r`
  gives the generation clause.

`SubstrateCoreAt` does not exclude `Wf s = W` frequently as `s → 0⁺` (`Wf ≡ W` meets `top`, and `scale`
reduces to the moment at `s = b`, `MultiScaleAll.scale_const`). §4 proves `CoefFamAt` there; the content
then sits in `ExpandStrong` at that flow. For flows with `Wf s ≠ W` at small `s`, `generation_of_coefFam`
has no term-by-term use.

## 3. The channels (proved)

* **`msFlow_plaq_of_eq`**: at a scale with `Wf s = W`, the plaquette channel of the proxy is the observer's
  own field less a constant: `msFlow Wf k s (inr q) = (Φ0 W).map k (mField (inr q)) − c_k · 1`,
  `c_k = a_k⁻⁴ ν_k(mField (inr q) ∘ V_k^W)`. `msFlow_plaq_top`: at `s = b` this holds by `top`.
* **`msFlow_of_not_mem`**: at a scale with `Wf s = W`, a channel `j` whose field is outside the plaquette
  class is `a_k^{−d_j}` times the observer's field less a constant. The coefficient `a_k^{−d_j}` is matched
  by an observer field of size `O(a_k^{d_j})` (by `scale`): the product is bounded, but the observer's
  margin monomial in that field reads `0` in the limit.

## 4. The constant flow on the plaquette channels (proved)

* `oneF`: the constant field `1`; `phi0_one`: `(Φ0 W).map k oneF = z1 k · 1`, `z1 k ∈ {1, a_k⁻⁴}`.
* `smear_sub_const`, `smear_smul_one`: smearing a field less a constant, and a constant.
* `plaqMean_bound`: under `SubstrateCoreAt`, `|a_k⁻⁴ ν_k(mField (inr q) ∘ V_k^W)| ≤ C / μ_q(b)` eventually
  (`ScaleAt` at `s = b`, `y ≤ e^y`).
* `PlaqSupp cf`: every `cf i s` is supported on plaquette channels `Sum.inr q`.
* `smear_msProx_const`, **`proxB_const`**: at `Wf ≡ W` and `PlaqSupp cf`, each slot of the proxy is
  `∑_{o ∈ insertNone (cf i s).support} gam o · smear a_k ((Φ0 W).map k (fldO o)) fᵢ` (the constant term
  carried by `oneF`), so `B_k^s(P)` is a finite combination of margin monomials with coefficients
  `∏ᵢ gam (σ i)`.
* **`coefFam_const`**: under `SubstrateCoreAt W z b (fun _ => W)`, `PlaqSupp cf` and `0 ≤ r`, `CoefFamAt`
  holds at every `P` beyond `r`.
* **`generation_of_const`**: at `Wf ≡ W`, `PlaqSupp cf` and `0 ≤ r`, the narrow core and `PhysRange r` give
  the generation clause outright.

## 5. The bundle with the germ (proved)

* `NarrowGermInputsN N hN2`: `NarrowInputsN` with the generation clause replaced by `ProxyGermAt` beyond `r`.
* **`narrowInputsN_iff_germ`**: `NarrowGermInputsN N hN2 ↔ NarrowInputsN N hN2` (same witnesses).
* No `ClayStatement` capstone is stated from `NarrowGermInputsN`: like `NarrowInputsN` it carries
  `RunSeedN.EndpointN N`, refuted by `EndpointAudit.not_endpointN_of_levels_unbounded` under the argued growth
  of the zero-flux level count.

## 6. What remains (argued; no declaration)

At `Wf ≡ W` with `PlaqSupp cf`, generation is discharged and the rest of `NarrowInputsN` must hold at that
choice. `ExpandStrong (fun _ => W) cf z μ` then asks that every renormalised composite reading be, to
`K (s/d)^ε`, the reading of a combination with coefficients `cf(·, s)` of `W`-flowed plaquette densities
(at `s`-independent `cf`, one fixed combination: `FlowChoice.tendsto_latC_sub_of_expandR_const`). Its
membership clause asks that, for every separated positive-time `P`, the proxy lie in the half-space algebra
for all small `s`. At the constant flow the proxy depends on `s` only through `cf`; for `P` with times in
`(0, r)` the `W`-flowed fields read links within the physical range of `W` on both sides of the plane, so
membership asks cancellation or `cf(Pᵢ, s) = 0` on those composites, and vanishing of all `cf · s` at
scales accumulating at `0` contradicts `CompNondeg` (`FlowChoice.not_compNondeg_of_frequently_zero'`). Not
proved here: whether `ExpandStrong` at the constant flow with plaquette-supported `cf` is compatible with
`CompNondeg` and `CovC`. A rank argument does not close it: `IPlaq` carries a site, so the plaquette
channels are infinitely many, and `cf` may depend on `s`.

For flows with `Wf s ≠ W` at small `s`, `ProxyGermAt` at `W = sunFam … s₀` asks that the proxy fields at
small flow time be recovered from fields at flow time `s₀` beyond `r` with `k`-independent coefficients. In
the margin algebra the fields that can serve are the `W`-flowed local fields of `{x₀ > r}` whose readings
survive the limit (the plaquette class yes, the `bR` channels no): a cyclicity statement of Reeh–Schlieder
type in the joint reflection form (time step `ApproxObserver.mem_of_apply_mem`). Not proved either way;
`ProxyGenLimN.decoupled_core` shows it does not follow from the kernels and joint positivity alone.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` the least colour count and the halving/cross-term factors; `4`, `8` the splits
of the tolerance and the plaquette dimension; `0` the plane, the lower end of the scale, the zero
subtraction and the limit of the coefficient differences; `1` the one-factor monomial, the unit observable,
the constant field and the spacing bound; `12` the bound of the block-step flow.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.GenerationN

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

variable {N : ℕ}

/-! ## 0. The observer's fields -/

/-- **The observer on a symmetrised plaquette**: `a_k⁻⁴ (O ∘ V_k^W)`. DERIVED: `4` the dimension; `0` the
zero subtraction. -/
theorem phi0_map_of_mem (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ SymPlaqClass N)
    (k : ℕ) : ((Φ0 W).map k O).1 = (dySpacing N k ^ 4)⁻¹ • (W.fieldMap k O).1 := by
  rw [Φ0, energy0, energyOn_map_of_mem W (symPlaq_refl N) (s0_refl N) hO k]
  simp [s0]

/-- **The observer off the plaquette class**: `O ∘ V_k^W`, factor `1`. DERIVED: `1` the factor; `0` the
zero subtraction. -/
theorem phi0_map_of_not_mem (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)}
    (hO : O ∉ SymPlaqClass N) (k : ℕ) : ((Φ0 W).map k O).1 = (W.fieldMap k O).1 := by
  show zOn (SymPlaqClass N) k O • ((W.fieldMap k O).1
    - sOn (SymPlaqClass N) (s0 N) k O • (1 : C(Cfg N, ℝ))) = _
  rw [zOn_of_not_mem hO, sOn_of_not_mem hO]
  simp

/-- **Every local field enters a margin monomial**: the one-factor monomial `(O, f)` with `f` vanishing
below a time `d > max(0, r)`. DERIVED: `1` the one factor; `0` the plane. -/
def oneMargin (O : LField (MassGap.SUN.SU N)) (f : TestFn) {r d : ℝ} (hd : 0 < d) (hrd : r < d)
    (hf : ∀ y, f.1 y ≠ 0 → d ≤ y 0) : MarginMono N 0 r :=
  ⟨⟨1, fun _ => (O, f)⟩, d, hd, hrd, fun _ y hy => hf y hy⟩

/-! ## 1. The clause per composite -/

/-- **Generation of the proxies of one composite at arbitrarily small flow time**, in the lattice
reflection form. DERIVED: `0` the plane, the signs and the limit of the scale. -/
def ProxyGermAt [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (r : ℝ) (P : TSepG Ix0 0) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ᶠ s in 𝓝[>] (0 : ℝ), ∃ a : MarginMono N 0 r →₀ ℝ,
    ∀ᶠ k in (ultra : Filter ℕ),
      rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
        (proxB Wf cf k s P.1 - yW W k a) (proxB Wf cf k s P.1 - yW W k a) ≤ η

/-- `ProxyGenGerm` is `ProxyGermAt` at every composite. DERIVED: no numeral. -/
theorem proxyGenGerm_iff [NeZero N] {W : ConfFlow N} {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {r : ℝ} :
    ProxyGenGerm W Wf cf r ↔ ∀ P, ProxyGermAt W Wf cf r P := Iff.rfl

/-- **`ApproxKAt` from `ExpandStrong` and the germ at one composite** (`ProxyGenLimN.approxK_of_germ` at
`P`). DERIVED: `4` and `2` the split `ε = 2 (ε/4) + 2 (ε/4)`; `2` the least colour count; `0` the plane. -/
theorem approxKAt_of_germAt (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hCO : CompOS (NeZero.ne N) (CRen N z μ)) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandStrong Wf cf z μ) (P : TSepG (CRen N z μ).Ix 0)
    (hG : ProxyGermAt W Wf cf r P) :
    ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hUL : UnifLocal (CRen N z μ) := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  have hMC := mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO
  have hRL := reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO hMC
  have hpos := Flow.posPreserving_of_physRange (NeZero.ne N) (Φ0 W) hphys 0
  intro ε hε
  obtain ⟨s, ⟨a, ha⟩, hEs⟩ := ((hG (ε / 4) (by positivity)).and_eventually
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

/-- **The germ at one composite from `ExpandStrong` and `ApproxKAt`** (`ProxyGenLimN.germ_of_approxK` at
`P`). DERIVED: `8`, `4` and `2` the split `η = 2 (η/4) + 2 (η/4)` with `η/8 < η/4`; `2` the least colour
count; `0` the plane. -/
theorem germAt_of_approxKAt (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {t C : ℝ}
    (hU : ClassMoments (NeZero.ne N) W (SymPlaqClass N) t C) {r : ℝ} (hphys : (Φ0 W).PhysRange r)
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hCO : CompOS (NeZero.ne N) (CRen N z μ)) {Wf : ℝ → ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hE : ExpandStrong Wf cf z μ) (P : TSepG (CRen N z μ).Ix 0)
    (hA : ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r)
      (gramF hN2 W r) P) :
    ProxyGermAt W Wf cf r P := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hUL : UnifLocal (CRen N z μ) := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  have hcov : ReflCovLat (CRen N z μ) 0 := reflCovLat_CRen z μ
  have hMC := mixConvG_of_cov hN2 W hU hphys (CRen N z μ) hUL hcov hCO
  have hRL := reflLimG_of_cov hN2 W (CRen N z μ) r hcov hCO hMC
  have hpos := Flow.posPreserving_of_physRange (NeZero.ne N) (Φ0 W) hphys 0
  intro η hη
  obtain ⟨a, ha⟩ := hA (η / 8) (by positivity)
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

/-- **The generation clause at one composite is the germ**, under the narrow core and `PhysRange r`.
DERIVED: `2` the least colour count; `0` the plane. -/
theorem approxKAt_iff_germAt (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r) (P : TSepG (CRen N z μ).Ix 0) :
    ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0) (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P
      ↔ ProxyGermAt W Wf cf r P := by
  obtain ⟨t, C, ht, hS⟩ := uv_of_scale S.b_pos S.top S.scale
  have hU := ClaySUFinal.classMoments_of_siteExp (NeZero.ne N) W ht hS
  have hCO := compOS_of_covC S hE hcb hV hP
  exact ⟨germAt_of_approxKAt hN2 hU hphys hCO hE P, approxKAt_of_germAt hN2 hU hphys hCO hE P⟩

/-- **The generation clause of `NarrowInputsN` is the germ beyond the margin.** DERIVED: `2` the least
colour count; `0` the plane. -/
theorem generation_iff_germ (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r) :
    (∀ P : TSepG (CRen N z μ).Ix 0, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
        (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P)
      ↔ ∀ P : TSepG (CRen N z μ).Ix 0, BeyondR r P → ProxyGermAt W Wf cf r P :=
  forall_congr' fun P => imp_congr_right fun _ => approxKAt_iff_germAt hN2 S hE hcb hV hP hphys P

/-- **The germ does not depend on the choice** of `(b, Wf, cf)` among those meeting the narrow core at the
same `W`, `z`, `μ`, `r`. DERIVED: `2` the least colour count. -/
theorem germAt_choice_iff (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    {b b' r : ℝ} {Wf Wf' : ℝ → ConfFlow N} {cf cf' : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf)
    (S' : SubstrateCoreAt W z b' Wf') (hE' : ExpandStrong Wf' cf' z μ) (hcb' : CoefBound cf')
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r) (P : TSepG (CRen N z μ).Ix 0) :
    ProxyGermAt W Wf cf r P ↔ ProxyGermAt W Wf' cf' r P :=
  (approxKAt_iff_germAt hN2 S hE hcb hV hP hphys P).symm.trans
    (approxKAt_iff_germAt hN2 S' hE' hcb' hV hP hphys P)

/-! ## 2. A sufficient identification -/

/-- **The proxies are finite margin combinations with bounded coefficients**: frequently as `s → 0⁺`, a
finite family `Q` of margin monomials and coefficients `β k m`, each eventually bounded in `k`, with
`B_k^s(P) = ∑_m β k m · Y_k(Q m)` eventually along `ultra`. DERIVED: `0` the plane and the limit of the
scale. -/
def CoefFamAt [NeZero N] (W : ConfFlow N) (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ))
    (r : ℝ) (P : TSepG Ix0 0) : Prop :=
  ∃ᶠ s in 𝓝[>] (0 : ℝ), ∃ (M : Type) (_ : Fintype M) (Q : M → MarginMono N 0 r) (β : ℕ → M → ℝ),
    (∀ m, ∃ B : ℝ, ∀ᶠ k in atTop, |β k m| ≤ B)
      ∧ ∀ᶠ k in (ultra : Filter ℕ),
        proxB Wf cf k s P.1 = ∑ m, β k m • prodSmear (dySpacing N k) ((Φ0 W).mono k (Q m).1)

/-- **The reflection form of a finite margin combination** as a double sum of flowed lattice readings.
DERIVED: `0` the plane. -/
theorem rform_fam_eq [NeZero N] (W : ConfFlow N) {r : ℝ} (k : ℕ) {M : Type} [Fintype M]
    (Q : M → MarginMono N 0 r) (e : M → ℝ) :
    rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
        (∑ m, e m • prodSmear (dySpacing N k) ((Φ0 W).mono k (Q m).1))
        (∑ m, e m • prodSmear (dySpacing N k) ((Φ0 W).mono k (Q m).1))
      = ∑ m, ∑ m', e m * e m' * latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 (Q m).1 (Q m').1) := by
  simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    latSF_pair_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring

/-- **The germ from a finite margin combination with bounded coefficients**, under
`UniformBoundF (Φ0 W)`. DERIVED: `0` the limit of the coefficient differences. -/
theorem germAt_of_coefFam [NeZero N] {W : ConfFlow N} {r : ℝ}
    (hB : UniformBoundF (NeZero.ne N) (Φ0 W)) {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {P : TSepG Ix0 0} (h : CoefFamAt W Wf cf r P) : ProxyGermAt W Wf cf r P := by
  classical
  intro η hη
  refine h.mono ?_
  rintro s ⟨M, hM, Q, β, hβ, hEq⟩
  have hlim : ∀ m, ∃ x, Tendsto (fun k => β k m) (ultra : Filter ℕ) (𝓝 x) := fun m => by
    obtain ⟨B, hB'⟩ := hβ m
    exact exists_tendsto_ultra _ B hB'
  choose β0 hβ0 using hlim
  refine ⟨∑ m, Finsupp.single (Q m) (β0 m), ?_⟩
  have hY : ∀ k, yW W k (∑ m, Finsupp.single (Q m) (β0 m))
      = ∑ m, β0 m • prodSmear (dySpacing N k) ((Φ0 W).mono k (Q m).1) := by
    intro k
    unfold yW
    rw [← Finsupp.sum_finsetSum_index
      (h := fun (Q' : MarginMono N 0 r) (x : ℝ) => x • prodSmear (dySpacing N k) ((Φ0 W).mono k Q'.1))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finset.sum_congr rfl fun m _ => Finsupp.sum_single_index (zero_smul _ _)
  have hT : Tendsto (fun k => ∑ m, ∑ m', (β k m - β0 m) * (β k m' - β0 m')
      * latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 (Q m).1 (Q m').1)) (ultra : Filter ℕ) (𝓝 0) := by
    have h0 : Tendsto (fun k => ∑ m, ∑ m', (β k m - β0 m) * (β k m' - β0 m')
        * latSF (NeZero.ne N) (Φ0 W) k (pairFam 0 (Q m).1 (Q m').1)) (ultra : Filter ℕ)
        (𝓝 (∑ m, ∑ m', (β0 m - β0 m) * (β0 m' - β0 m')
          * contSF (NeZero.ne N) (Φ0 W) (pairFam 0 (Q m).1 (Q m').1))) :=
      tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun m' _ =>
        (((hβ0 m).sub tendsto_const_nhds).mul ((hβ0 m').sub tendsto_const_nhds)).mul
          (tendsto_contSF (NeZero.ne N) (Φ0 W) hB _)
    simpa only [sub_self, zero_mul, Finset.sum_const_zero] using h0
  filter_upwards [hT.eventually (gt_mem_nhds hη), hEq] with k hk hkE
  have hD : proxB Wf cf k s P.1 - yW W k (∑ m, Finsupp.single (Q m) (β0 m))
      = ∑ m, (β k m - β0 m) • prodSmear (dySpacing N k) ((Φ0 W).mono k (Q m).1) := by
    rw [hkE, hY, ← Finset.sum_sub_distrib]
    simp only [sub_smul]
  rw [hD]
  exact (rform_fam_eq W k Q (fun m => β k m - β0 m)).le.trans hk.le

/-- **The generation clause from finite margin combinations with bounded coefficients** beyond the
margin, under the narrow core and `PhysRange r`. DERIVED: `2` the least colour count; `0` the plane. -/
theorem generation_of_coefFam (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (S : SubstrateCoreAt W z b Wf) (hE : ExpandStrong Wf cf z μ) (hcb : CoefBound cf)
    (hV : CovC (NeZero.ne N) (CRen N z μ)) (hP : CompNondeg (NeZero.ne N) (CRen N z μ))
    (hphys : (Φ0 W).PhysRange r)
    (hI : ∀ P : TSepG (CRen N z μ).Ix 0, BeyondR r P → CoefFamAt W Wf cf r P) :
    ∀ P : TSepG (CRen N z μ).Ix 0, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P :=
  (generation_iff_germ hN2 S hE hcb hV hP hphys).2 fun P hP' =>
    germAt_of_coefFam (uB_of_core S) (hI P hP')

/-! ## 3. The channels -/

/-- **The plaquette channel at a scale where the flow is the observer's**: the observer's own field less
a constant. DERIVED: `4` the plaquette dimension; `0` the zero subtraction. -/
theorem msFlow_plaq_of_eq [NeZero N] {W : ConfFlow N} {Wf : ℝ → ConfFlow N} {s : ℝ} (hs : Wf s = W)
    (k : ℕ) (q : MassGap.GibbsSpec.IPlaq) :
    msFlow Wf k s (Sum.inr q) = ((Φ0 W).map k (mField (Sum.inr q))).1
      - ((dySpacing N k ^ 4)⁻¹ * stateK (NeZero.ne N) k (W.fieldMap k (mField (Sum.inr q))).1)
        • (1 : C(Cfg N, ℝ)) := by
  have hO : (mField (Sum.inr q) : LField (MassGap.SUN.SU N)) ∈ SymPlaqClass N := ⟨q, rfl⟩
  rw [phi0_map_of_mem W hO k]
  unfold msFlow
  rw [hs, mDim_inr, smul_sub, smul_smul]

/-- **At the top scale the plaquette channel is the observer's field less a constant** (`top`).
DERIVED: `4` the plaquette dimension. -/
theorem msFlow_plaq_top [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCoreAt W z b Wf) (k : ℕ) (q : MassGap.GibbsSpec.IPlaq) :
    msFlow Wf k b (Sum.inr q) = ((Φ0 W).map k (mField (Sum.inr q))).1
      - ((dySpacing N k ^ 4)⁻¹ * stateK (NeZero.ne N) k (W.fieldMap k (mField (Sum.inr q))).1)
        • (1 : C(Cfg N, ℝ)) :=
  msFlow_plaq_of_eq S.top k q

/-- **A channel off the plaquette class at a scale where the flow is the observer's**: `a_k^{−d_j}` times
the observer's field less a constant. DERIVED: no numeral. -/
theorem msFlow_of_not_mem [NeZero N] {W : ConfFlow N} {Wf : ℝ → ConfFlow N} {s : ℝ} (hs : Wf s = W)
    (k : ℕ) (j : MIx) (hj : (mField j : LField (MassGap.SUN.SU N)) ∉ SymPlaqClass N) :
    msFlow Wf k s j = (dySpacing N k ^ mDim j)⁻¹ • (((Φ0 W).map k (mField j)).1
      - stateK (NeZero.ne N) k ((Φ0 W).map k (mField j)).1 • (1 : C(Cfg N, ℝ))) := by
  rw [phi0_map_of_not_mem W hj k]
  unfold msFlow
  rw [hs]

/-! ## 4. The constant flow on the plaquette channels -/

/-- **The constant field `1`.** DERIVED: `1` the constant. -/
def oneF : LField (MassGap.SUN.SU N) :=
  ⟨1, ⟨⟨∅, fun _ _ _ => rfl⟩, fun _ _ => rfl⟩⟩

/-- The class factor of the constant field: `a_k⁻⁴` if it lies in the plaquette class, `1` otherwise.
DERIVED: no numeral. -/
def z1 (k : ℕ) : ℝ := zOn (SymPlaqClass N) k (oneF (N := N))

/-- **The observer on the constant field**: `z1 k · 1`. DERIVED: `0` the zero subtraction; `1` the
constant. -/
theorem phi0_one (W : ConfFlow N) (k : ℕ) :
    ((Φ0 W).map k oneF).1 = z1 (N := N) k • (1 : C(Cfg N, ℝ)) := by
  show zOn (SymPlaqClass N) k oneF • ((W.fieldMap k oneF).1
    - sOn (SymPlaqClass N) (s0 N) k oneF • (1 : C(Cfg N, ℝ))) = _
  have h1 : (W.fieldMap k (oneF (N := N))).1 = 1 := by
    ext U
    rfl
  have h2 : sOn (SymPlaqClass N) (s0 N) k (oneF (N := N)) = 0 := by
    unfold sOn s0
    split_ifs <;> rfl
  rw [h1, h2, zero_smul, sub_zero]
  rfl

/-- `z1` does not vanish. DERIVED: `0` the excluded value. -/
theorem z1_ne [NeZero N] (k : ℕ) : z1 (N := N) k ≠ 0 := by
  have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold z1 zOn canonZ
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ ha.ne')
  · exact one_ne_zero

/-- `|z1⁻¹| ≤ 1` eventually (`a_k < 1`). DERIVED: `1` the spacing bound. -/
theorem z1_inv_le [NeZero N] : ∀ᶠ k in atTop, |(z1 (N := N) k)⁻¹| ≤ 1 := by
  filter_upwards [(tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk
  have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold z1 zOn canonZ
  split_ifs
  · rw [inv_inv, abs_of_pos (pow_pos ha 4)]
    exact pow_le_one₀ ha.le hk.le
  · simp

/-- **Smearing a field less a constant.** DERIVED: `4` the cell volume. -/
theorem smear_sub_const {a : ℝ} (ha : 0 < a) (G : C(Cfg N, ℝ)) (m : ℝ) (f : TestFn) :
    smear a (G - m • (1 : C(Cfg N, ℝ))) f
      = smear a G f - (m * LocalClosing.wsum a f) • (1 : C(Cfg N, ℝ)) := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha _ f hf (Finset.Subset.refl _), smear_eq_sum ha _ f hf (Finset.Subset.refl _),
    LocalClosing.wsum_eq ha hf, Finset.mul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have ht : transObs x (G - m • (1 : C(Cfg N, ℝ))) = transObs x G - m • (1 : C(Cfg N, ℝ)) := by
    ext U
    simp [transObs_apply]
  rw [ht, smul_sub, smul_smul, mul_comm m]

/-- **Smearing a constant.** DERIVED: `4` the cell volume. -/
theorem smear_smul_one {a : ℝ} (ha : 0 < a) (c : ℝ) (f : TestFn) :
    smear a (c • (1 : C(Cfg N, ℝ))) f = (c * LocalClosing.wsum a f) • (1 : C(Cfg N, ℝ)) := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha _ f hf (Finset.Subset.refl _), LocalClosing.wsum_eq ha hf, Finset.mul_sum,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  have ht : transObs x (c • (1 : C(Cfg N, ℝ))) = c • (1 : C(Cfg N, ℝ)) := by
    ext U
    simp [transObs_apply]
  rw [ht, smul_smul, mul_comm c]

/-- **The plaquette mean at the observer's flow is `O(a_k^4)`**: under `SubstrateCoreAt`,
`|a_k⁻⁴ ν_k(mField (inr q) ∘ V_k^W)|` is eventually bounded (`ScaleAt` at `s = b`, `y ≤ e^y`).
DERIVED: `4` the plaquette dimension; `1` from `y + 1 ≤ e^y`. -/
theorem plaqMean_bound [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCoreAt W z b Wf) (q : MassGap.GibbsSpec.IPlaq) :
    ∃ B : ℝ, ∀ᶠ k in atTop, |(dySpacing N k ^ 4)⁻¹
      * stateK (NeZero.ne N) k (W.fieldMap k (mField (Sum.inr q))).1| ≤ B := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := S.scale
  have hμ := msMu_pos ht γ γP S.b_pos (Sum.inr q)
  refine ⟨C / msMu t γ γP (Sum.inr q) b, ?_⟩
  filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds S.b_pos)] with k hk hkb
  have hS := hk b hkb.le le_rfl (Sum.inr q)
  rw [S.top, mDim_inr] at hS
  set F := (W.fieldMap k (mField (Sum.inr q))).1 with hF
  set μ := msMu t γ γP (Sum.inr q) b with hμdef
  have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hx : 0 < (dySpacing N k ^ 4)⁻¹ := inv_pos.2 (pow_pos ha 4)
  have h1 : |stateK (NeZero.ne N) k F| ≤ stateK (NeZero.ne N) k (msAbs F) :=
    abs_state_le_of_abs_le _ F (msAbs F) (fun U => le_of_eq (msAbs_apply F U).symm)
  have h2 : stateK (NeZero.ne N) k ((μ / dySpacing N k ^ 4) • msAbs F) ≤ C := by
    refine le_trans ((stateK (NeZero.ne N) k).mono fun U => ?_) hS
    rw [expC_apply]
    have := Real.add_one_le_exp (((μ / dySpacing N k ^ 4) • msAbs F) U)
    linarith
  rw [MassGap.DLRLimit.State.map_smul, div_eq_mul_inv] at h2
  rw [abs_mul, abs_of_pos hx, le_div_iff₀ hμ]
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hx.le) hμ.le
  nlinarith

/-- **Plaquette-supported coefficients**: every `cf i s` is supported on plaquette channels.
DERIVED: no numeral. -/
def PlaqSupp (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∀ i s, ∀ j ∈ (cf i s).support, ∃ q : MassGap.GibbsSpec.IPlaq, j = Sum.inr q

/-- The field of a slot choice: the constant field, or a channel field. DERIVED: no numeral. -/
def fldO : Option MIx → LField (MassGap.SUN.SU N)
  | none => oneF
  | some j => mField j

/-- The plaquette mean of a channel, `a_k⁻⁴ ν_k(mField j ∘ V_k^W)`. DERIVED: `4` the plaquette dimension. -/
def mK [NeZero N] (W : ConfFlow N) (k : ℕ) (j : MIx) : ℝ :=
  (dySpacing N k ^ 4)⁻¹ * stateK (NeZero.ne N) k (W.fieldMap k (mField j)).1

/-- The coefficient of a slot choice: `c j` on a channel, `−(∑_j c j mK j) / z1` on the constant field.
DERIVED: no numeral. -/
def gam [NeZero N] (W : ConfFlow N) (c : MIx →₀ ℝ) (k : ℕ) : Option MIx → ℝ
  | none => -(∑ j ∈ c.support, c j * mK W k j) * (z1 (N := N) k)⁻¹
  | some j => c j

/-- **One slot of the proxy at the constant flow** on plaquette-supported coefficients. DERIVED: `4` the
plaquette dimension. -/
theorem smear_msProx_const [NeZero N] (W : ConfFlow N) {c : MIx →₀ ℝ}
    (hc : ∀ j ∈ c.support, ∃ q : MassGap.GibbsSpec.IPlaq, j = Sum.inr q) (k : ℕ) (s : ℝ) (f : TestFn) :
    smear (dySpacing N k) (∑ j ∈ c.support, c j • msFlow (fun _ => W) k s j) f
      = ∑ o ∈ c.support.insertNone, gam W c k o • smear (dySpacing N k) ((Φ0 W).map k (fldO o)).1 f := by
  have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hj : ∀ j ∈ c.support, c j • smear (dySpacing N k) (msFlow (fun _ => W) k s j) f
      = c j • smear (dySpacing N k) ((Φ0 W).map k (mField j)).1 f
        - (c j * (mK W k j * LocalClosing.wsum (dySpacing N k) f)) • (1 : C(Cfg N, ℝ)) := by
    intro j hjm
    obtain ⟨q, rfl⟩ := hc j hjm
    rw [msFlow_plaq_of_eq (W := W) (Wf := fun _ => W) rfl k q, smear_sub_const ha, smul_sub, smul_smul]
    rfl
  rw [CompReduce.smear_sum_smul ha, Finset.sum_congr rfl hj, Finset.sum_sub_distrib, ← Finset.sum_smul,
    Finset.sum_insertNone]
  have hn : gam W c k none • smear (dySpacing N k) ((Φ0 W).map k (fldO none)).1 f
      = (-(∑ j ∈ c.support, c j * (mK W k j * LocalClosing.wsum (dySpacing N k) f)))
        • (1 : C(Cfg N, ℝ)) := by
    show gam W c k none • smear (dySpacing N k) ((Φ0 W).map k oneF).1 f = _
    rw [phi0_one, smear_smul_one ha, smul_smul]
    congr 1
    have hz : (z1 (N := N) k)⁻¹ * z1 (N := N) k = 1 := inv_mul_cancel₀ (z1_ne k)
    have hsum : ∑ j ∈ c.support, c j * (mK W k j * LocalClosing.wsum (dySpacing N k) f)
        = (∑ j ∈ c.support, c j * mK W k j) * LocalClosing.wsum (dySpacing N k) f := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum]
    simp only [gam]
    linear_combination (-(∑ j ∈ c.support, c j * mK W k j) * LocalClosing.wsum (dySpacing N k) f) * hz
  rw [hn, neg_smul]
  have hs : ∑ j ∈ c.support, gam W c k (some j) • smear (dySpacing N k) ((Φ0 W).map k (fldO (some j))).1 f
      = ∑ j ∈ c.support, c j • smear (dySpacing N k) ((Φ0 W).map k (mField j)).1 f := rfl
  rw [hs]
  abel

/-- A product of scaled functions is the product of the scales times the product of the functions.
DERIVED: no numeral. -/
theorem prod_smul_eq {ι X : Type*} [TopologicalSpace X] (s : Finset ι) (c : ι → ℝ)
    (h : ι → C(X, ℝ)) : ∏ i ∈ s, c i • h i = (∏ i ∈ s, c i) • ∏ i ∈ s, h i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih, smul_mul_smul_comm]

/-- **The proxy at the constant flow** on plaquette-supported coefficients is a finite combination of
margin-shaped monomials. DERIVED: no numeral. -/
theorem proxB_const [NeZero N] (W : ConfFlow N) {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hcf : PlaqSupp cf)
    (k : ℕ) (s : ℝ) (P : TMonoG Ix0) :
    proxB (fun _ => W) cf k s P
      = ∑ σ ∈ Fintype.piFinset (fun i : Fin P.1 => (cf (P.2 i).1 s).support.insertNone),
          (∏ i, gam W (cf (P.2 i).1 s) k (σ i))
            • prodSmear (dySpacing N k) ((Φ0 W).mono k ⟨P.1, fun i => (fldO (σ i), (P.2 i).2)⟩) := by
  unfold proxB msProx
  rw [Finset.prod_congr rfl fun i _ => smear_msProx_const W (hcf (P.2 i).1 s) k s (P.2 i).2,
    Finset.prod_univ_sum]
  exact Finset.sum_congr rfl fun σ _ => prod_smul_eq Finset.univ _ _

/-- An eventually bounded sum. DERIVED: no numeral. -/
theorem evBdd_sum {ι : Type*} (s : Finset ι) (g : ℕ → ι → ℝ)
    (h : ∀ i ∈ s, ∃ B : ℝ, ∀ᶠ k in atTop, |g k i| ≤ B) :
    ∃ B : ℝ, ∀ᶠ k in atTop, |∑ i ∈ s, g k i| ≤ B := by
  classical
  choose! B hB using h
  refine ⟨∑ i ∈ s, B i, ?_⟩
  filter_upwards [(Filter.eventually_all_finset s).2 hB] with k hk
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hk)

/-- An eventually bounded product. DERIVED: `0` the sign of the absolute values. -/
theorem evBdd_prod {ι : Type*} (s : Finset ι) (g : ℕ → ι → ℝ)
    (h : ∀ i ∈ s, ∃ B : ℝ, ∀ᶠ k in atTop, |g k i| ≤ B) :
    ∃ B : ℝ, ∀ᶠ k in atTop, |∏ i ∈ s, g k i| ≤ B := by
  classical
  choose! B hB using h
  refine ⟨∏ i ∈ s, B i, ?_⟩
  filter_upwards [(Filter.eventually_all_finset s).2 hB] with k hk
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) hk

/-- **The slot coefficients are eventually bounded** under `SubstrateCoreAt`. DERIVED: `1` the bound of
`|z1⁻¹|`. -/
theorem gam_bdd [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (S : SubstrateCoreAt W z b Wf) {c : MIx →₀ ℝ}
    (hc : ∀ j ∈ c.support, ∃ q : MassGap.GibbsSpec.IPlaq, j = Sum.inr q) (o : Option MIx) :
    ∃ B : ℝ, ∀ᶠ k in atTop, |gam W c k o| ≤ B := by
  cases o with
  | some j => exact ⟨|c j|, Filter.Eventually.of_forall fun _ => le_rfl⟩
  | none =>
    obtain ⟨B, hB⟩ := evBdd_sum c.support (fun k j => c j * mK W k j) fun j hj => by
      obtain ⟨q, rfl⟩ := hc j hj
      obtain ⟨B, hB⟩ := plaqMean_bound S q
      refine ⟨|c (Sum.inr q)| * B, ?_⟩
      filter_upwards [hB] with k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    refine ⟨B, ?_⟩
    filter_upwards [hB, z1_inv_le (N := N)] with k hk hz
    show |-(∑ j ∈ c.support, c j * mK W k j) * (z1 (N := N) k)⁻¹| ≤ B
    rw [abs_mul, abs_neg]
    calc |∑ j ∈ c.support, c j * mK W k j| * |(z1 (N := N) k)⁻¹|
        ≤ |∑ j ∈ c.support, c j * mK W k j| * 1 :=
          mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ ≤ B := by rw [mul_one]; exact hk

/-- **`CoefFamAt` at the constant flow** on plaquette-supported coefficients, at every composite beyond
`r ≥ 0`. DERIVED: `0` the lower end of the margin. -/
theorem coefFam_const [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b r : ℝ}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (S : SubstrateCoreAt W z b (fun _ => W)) (hr : 0 ≤ r)
    (hcf : PlaqSupp cf) (P : TSepG Ix0 0) (hP : BeyondR r P) : CoefFamAt W (fun _ => W) cf r P := by
  classical
  obtain ⟨d, hrd, hd⟩ := hP
  refine Filter.Frequently.of_forall fun s => ?_
  let T : Fin P.1.1 → Finset (Option MIx) := fun i => (cf (P.1.2 i).1 s).support.insertNone
  let Q : ↥(Fintype.piFinset T) → MarginMono N 0 r := fun σ =>
    ⟨⟨P.1.1, fun i => (fldO (σ.1 i), (P.1.2 i).2)⟩, d, lt_of_le_of_lt hr hrd, hrd,
      fun i y hy => hd i y hy⟩
  refine ⟨↥(Fintype.piFinset T), inferInstance, Q,
    fun k σ => ∏ i, gam W (cf (P.1.2 i).1 s) k (σ.1 i), fun σ => ?_, ?_⟩
  · exact evBdd_prod Finset.univ (fun k i => gam W (cf (P.1.2 i).1 s) k (σ.1 i))
      fun i _ => gam_bdd S (hcf _ s) _
  · refine Filter.Eventually.of_forall fun k => ?_
    rw [proxB_const W hcf k s P.1]
    exact (Finset.sum_coe_sort (Fintype.piFinset T) (fun σ => (∏ i, gam W (cf (P.1.2 i).1 s) k (σ i))
      • prodSmear (dySpacing N k)
        ((Φ0 W).mono k ⟨P.1.1, fun i => (fldO (σ i), (P.1.2 i).2)⟩))).symm

/-- **Generation at the constant flow**: at `Wf ≡ W` with plaquette-supported coefficients and `0 ≤ r`,
the narrow core and `PhysRange r` give the generation clause. DERIVED: `2` the least colour count; `0` the
plane and the lower end of the margin. -/
theorem generation_of_const (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {b r : ℝ} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hr : 0 ≤ r)
    (S : SubstrateCoreAt W z b (fun _ => W)) (hE : ExpandStrong (fun _ => W) cf z μ)
    (hcb : CoefBound cf) (hV : CovC (NeZero.ne N) (CRen N z μ))
    (hP : CompNondeg (NeZero.ne N) (CRen N z μ)) (hphys : (Φ0 W).PhysRange r) (hcf : PlaqSupp cf) :
    ∀ P : TSepG (CRen N z μ).Ix 0, BeyondR r P → ApproxKAt (kernC (NeZero.ne N) (CRen N z μ) 0)
      (mixKG hN2 W (CRen N z μ) r) (gramF hN2 W r) P :=
  generation_of_coefFam hN2 S hE hcb hV hP hphys fun P hP' => coefFam_const S hr hcf P hP'

/-! ## 5. The bundle with the germ -/

/-- **The per-`N` inputs with the germ**: `ClayNarrow.NarrowInputsN` with its generation clause replaced
by `ProxyGermAt` beyond `r`. DERIVED: `2` the least colour count; `0` the lower end of the observer's
scale; `12` the bound of the block-step flow. -/
def NarrowGermInputsN (N : ℕ) (hN2 : 2 ≤ N) : Prop :=
  haveI : NeZero N := ⟨by omega⟩
  ∃ (c : ℝ) (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N)) (s₀ r : ℝ) (_ : 0 ≤ s₀) (_ : s₀ < r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)),
    SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) (ZCanon.zFix N zri zwe) b Wf
      ∧ ExpandStrong Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CoefBound cf
      ∧ CovC (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ WardT (NeZero.ne N) (rhoD (fR N) (ZCanon.zFix N zri zwe))
      ∧ CompNondeg (NeZero.ne N) (CRen N (ZCanon.zFix N zri zwe) μ)
      ∧ (∀ P : TSepG (CRen N (ZCanon.zFix N zri zwe) μ).Ix 0, BeyondR r P →
          ProxyGermAt (sunFam hN2 c hc0 hc s₀) Wf cf r P)
      ∧ (∃ ℓ : ℝ, 0 < ℓ ∧ ThreePointAtScale (ne_zero_of_two_le hN2) ℓ)
      ∧ RunSeedN.EndpointN N

/-- **`NarrowGermInputsN` is `NarrowInputsN`** at the same witnesses (`generation_iff_germ`).
DERIVED: `2` the least colour count. -/
theorem narrowInputsN_iff_germ (hN2 : 2 ≤ N) : NarrowGermInputsN N hN2 ↔ NarrowInputsN N hN2 := by
  haveI : NeZero N := ⟨by omega⟩
  constructor
  · rintro ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hG, h3,
      hEnd⟩
    exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
      (generation_iff_germ hN2 S hE hC hV hP (sunFam_physRange hN2 hc0 hc hs0 hr)).2 hG, h3, hEnd⟩
  · rintro ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP, hB, h3,
      hEnd⟩
    exact ⟨c, hc0, hc, s₀, r, hs0, hr, zri, zwe, hri, hwe, μ, b, Wf, cf, S, hE, hC, hV, hW, hP,
      (generation_iff_germ hN2 S hE hC hV hP (sunFam_physRange hN2 hc0 hc hs0 hr)).1 hB, h3, hEnd⟩

end MassGap.GenerationN

end

#print axioms MassGap.GenerationN.phi0_map_of_mem
#print axioms MassGap.GenerationN.phi0_map_of_not_mem
#print axioms MassGap.GenerationN.oneMargin
#print axioms MassGap.GenerationN.proxyGenGerm_iff
#print axioms MassGap.GenerationN.approxKAt_of_germAt
#print axioms MassGap.GenerationN.germAt_of_approxKAt
#print axioms MassGap.GenerationN.approxKAt_iff_germAt
#print axioms MassGap.GenerationN.generation_iff_germ
#print axioms MassGap.GenerationN.germAt_choice_iff
#print axioms MassGap.GenerationN.msFlow_plaq_of_eq
#print axioms MassGap.GenerationN.msFlow_plaq_top
#print axioms MassGap.GenerationN.msFlow_of_not_mem
#print axioms MassGap.GenerationN.narrowInputsN_iff_germ
#print axioms MassGap.GenerationN.rform_fam_eq
#print axioms MassGap.GenerationN.germAt_of_coefFam
#print axioms MassGap.GenerationN.generation_of_coefFam
#print axioms MassGap.GenerationN.oneF
#print axioms MassGap.GenerationN.phi0_one
#print axioms MassGap.GenerationN.z1_ne
#print axioms MassGap.GenerationN.z1_inv_le
#print axioms MassGap.GenerationN.smear_sub_const
#print axioms MassGap.GenerationN.smear_smul_one
#print axioms MassGap.GenerationN.plaqMean_bound
#print axioms MassGap.GenerationN.smear_msProx_const
#print axioms MassGap.GenerationN.prod_smul_eq
#print axioms MassGap.GenerationN.proxB_const
#print axioms MassGap.GenerationN.evBdd_sum
#print axioms MassGap.GenerationN.evBdd_prod
#print axioms MassGap.GenerationN.gam_bdd
#print axioms MassGap.GenerationN.coefFam_const
#print axioms MassGap.GenerationN.generation_of_const
