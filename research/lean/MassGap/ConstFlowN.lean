import Mathlib
import MassGap.GenerationN
import MassGap.ExistenceFlow
import MassGap.ExistencePosNonnull
import MassGap.PlaneVariance
import MassGap.ScaleIdentityNoGo

/-!
# MassGap.ConstFlowN — the membership clause of `ExpandStrong` at the constant flow `Wf ≡ W`

`GenerationN.generation_of_const` discharges the generation clause of `ClayNarrow.NarrowInputsN` at the
constant flow `Wf ≡ W`, `W = sunFam hN2 c hc0 hc s₀`, with plaquette-supported coefficients (`PlaqSupp cf`).
`GenerationN` §6 argues that the membership clause of `StrongExpand.ExpandStrong` then conflicts with
`CompNondeg`. This module decides where that argument holds and where it fails. Declarations are in the
namespace `MassGap.ConstFlowN`.

## 1. Reach and depth (proved)

* `ReachLE V R`: every output link of `V` reads only links within `R` of it (the shape of
  `ConfFlow.local_V`). `reachLE_range`: every `ConfFlow` at its own `range k`; `reachLE_id`: the identity
  at `0`.
* `exists_depth_msProx`: for `Wf`, `cf`, `s`, `i` there is a depth `D` (independent of the step) such that,
  whenever `(Wf s).V k` has reach `R`, `msProx Wf cf k s i` is local on a link set no deeper than `D + R`
  below the plane `x₀ = 0`. `D` is the deepest of the bare channel fields in the support of `cf i s`.
* **`exists_depth_proxB`**: for every monomial `P` there is `D` such that `proxB Wf cf k s P` lies in
  `halfSpaceAlg 0 0` whenever `(Wf s).V k` has reach `R`, every test function of `P` vanishes below time
  `d`, and `a_k (D + R) ≤ d` (`ContinuumField.smear_mem_halfSpaceAlg`, `halfSpaceAlg_prod_mem`).

## 2. Membership holds wherever the flow does not reach the plane (proved)

* `MembershipClause Wf cf`: the second conjunct of `ExpandStrong Wf cf z μ` (`membershipClause_of_expandStrong`).
* **`eventually_mem_sunFam`**: at `W = sunFam … s₀` (any `c`), for every composite monomial beyond `s₀`
  (`BeyondR s₀ P`) and every `cf`, `s`: `proxB (fun _ => W) cf k s P ∈ halfSpaceAlg 0 0` for all large `k`.
  The reach is `⌊s₀/a_k⌋ + 3`, so `a_k (D + reach) ≤ s₀ + a_k (D + 3) < d`.
* **`membership_sunFam_zero`**: at `s₀ = 0` the membership clause holds for every `cf` (plaquette-supported
  or not).
* `sunStep_of_eq_zero`, `sunFam_V_of_c_zero`: at `c = 0` the block step returns the link (`polar W = W`,
  phase `1`), so `sunFam … s₀` is the identity at every step. **`membership_c_zero`**: at `c = 0` the
  membership clause holds for every `s₀` and every `cf`.

## 3. The coefficient-level statement is false for every flow (proved)

* `NonMemConst W` states non-membership under the hypothesis `cf i s ≠ 0`. That constrains the finitely
  supported coefficient vector, not the field: the degenerate plaquette `((0, 0), 0)` has holonomy `1`
  (`GibbsSpec.ihol_degenerate`) and density `0`, so its channel field is `0` (`msFlow_degenerate`), and
  `cfDeg := single (inr ((0, 0), 0)) 1` is plaquette-supported, non-zero, and gives `proxB = ∏ 0`, which is
  in the algebra at every step. **`not_nonMemConst_all`**: `¬ NonMemConst W` for every `W`. So
  `not_compNondeg_of_nonMemConst` and `not_narrow_const` hold but have a hypothesis no flow meets; they are
  kept, with `eventually_cf_zero` and `contC_eq_zero_of_coef`, for importers.

## 4. The obstruction on the field (proved)

* `NonMemConstF W`: for every composite index `i` there is a separated positive-time monomial `P` such that
  for every plaquette-supported `cf` and every `s` at which the proxy field `msProx (fun _ => W) cf k s i` is
  not eventually `0` along `ultra`, `proxB (fun _ => W) cf k s P` is not eventually in `halfSpaceAlg 0 0`
  along `ultra`.
* `eventually_prox_zero`: `NonMemConstF W`, `PlaqSupp cf` and the membership clause give, for each `i`, for
  all small `s > 0`, `msProx … i = 0` eventually along `ultra`.
* `contC_eq_zero_of_prox`: under `ExpandR`, a separated family one of whose proxy fields is, for all small
  `s`, eventually `0` along `ultra` has `contC F = 0` (the reading tends to `0` along `ultra`).
* **`not_compNondeg_of_nonMemConstF`**, **`not_narrow_constF`**: `NonMemConstF W`, `PlaqSupp cf` and
  `ExpandStrong (fun _ => W) cf z μ` give `¬ CompNondeg (CRen N z μ)` at `N ≥ 2`; at `W = sunFam … s₀` a
  `NarrowInputsN` witness with `Wf ≡ W` and `PlaqSupp cf` needs `¬ NonMemConstF W`.
* `msProx_cfOne_ne_of_id`: when `(Wf s).V k = id`, the proxy of `cfOne` (the plaquette `((0, 1), 0)`) is not
  `0`: `sym plaq` reads `0` at the unit configuration (`ExistenceFlow.symPlaq_one`) and a positive value at
  the unit configuration with one link set to an element of positive density.
* **`not_nonMemConstF_sunFam_zero`**, **`not_nonMemConstF_c_zero`**: `NonMemConstF` is false at `s₀ = 0`
  and at `c = 0`. The coefficient-level `not_nonMemConst_sunFam_zero`, `not_nonMemConst_c_zero` are kept.
  `nonMemConst_witness_not_beyond`: at any `s₀ ≥ 0`, a monomial whose proxy is not eventually in the
  algebra is not beyond `s₀`.

## 5. What remains (argued; no declaration)

The §6 obstruction is a theorem modulo `NonMemConstF (sunFam … s₀)`, and that lemma is false at `s₀ = 0`
and at `c = 0`. Those values are admitted by `NarrowInputsN` (`0 ≤ c`, `0 ≤ s₀ < r`), so the membership
clause does not exclude the constant-flow route on its own: at `s₀ = 0` or `c = 0` the observer `W` is the
identity flow, generation is discharged (`generation_of_const`), membership holds, and the remaining content
of `ExpandStrong (fun _ => W) cf z μ` is its rate clause: the renormalised composites read, at rate
`(s/d)^ε`, as combinations with coefficients `cf(·, s)` of bare plaquette densities at spacing `a_k`.

That escape is closed by another clause of the same bundle (proved). `SubstrateCoreAt` carries the scale
clause, which fails at an eventually identity observer (`ScaleIdentityNoGo.not_substrateCoreAt_of_id`):
`ScaleIdentityNoGo.not_substrateCoreAt_sunFam_zero` excludes `s₀ = 0` and
**`not_substrateCoreAt_sunFam_c_zero`** (this module) excludes `c = 0`. A `NarrowInputsN` witness therefore
has `c > 0` and `s₀ > 0`: the region where `NonMemConstF` is open.

At `c > 0` and `s₀ > 0`, `NonMemConstF (sunFam … s₀)` is the open lemma. For a single slot `(i, f)` with
`f` supported at times in `(0, s₀)` it asks: whenever the proxy field `∑_q c_q a⁻⁴ (sym plaq_q ∘ V_k − ν_k)`
is not eventually `0`, its smear against `f` depends, eventually along `ultra`, on links at negative times.
Cancellation is not excluded by the coefficients alone: degenerate plaquettes give the zero field, and
plaquettes with swapped axes give the same symmetrised field, so a non-zero `c` can give a zero field. The
hypothesis is therefore placed on the field. The open part is that `⌊(s₀/a_k)²⌋` iterated block steps
carry the dependence across `δ/a_k` lattice units and that the smear against `f` does not cancel it.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the plane, the reach of the identity, the zero coupling, the zero scale and the
limits; `1` the scale bound of the membership witness and the unit phase; `2` the least colour count and
the two points; `3` the range beyond the box; `4` the dimension.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ConstFlowN

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
  MassGap.ProxyGenLimN MassGap.FlowCovN MassGap.ApproxJoint MassGap.ClayNarrow MassGap.GenerationN

variable {N : ℕ}

/-! ## 1. Reach and depth -/

/-- **Reach at most `R`**: every output link of `V` reads only links within `R` of it.
DERIVED: `4` the dimension. -/
def ReachLE (V : Cfg N → Cfg N) (R : ℕ) : Prop :=
  ∀ l : ILink, ∃ T : Finset ILink, (∀ l' ∈ T, ∀ i, |l'.2 i - l.2 i| ≤ (R : ℤ)) ∧
    ∀ U U' : Cfg N, (∀ l' ∈ T, U l' = U' l') → V U l = V U' l

/-- A configuration flow has reach `range k` at step `k`. DERIVED: no numeral. -/
theorem reachLE_range (W : ConfFlow N) (k : ℕ) : ReachLE (W.V k) (W.range k) := W.local_V k

/-- The identity has reach `0`. DERIVED: `0` the reach. -/
theorem reachLE_id : ReachLE (id : Cfg N → Cfg N) 0 := fun l =>
  ⟨{l}, fun l' hl' i => by rw [Finset.mem_singleton.mp hl']; simp,
    fun _ _ h => h l (Finset.mem_singleton_self l)⟩

/-- A local field is local on a set of some depth below the plane `x₀ = 0`. DERIVED: `0` the plane. -/
theorem exists_depth_field (O : LField (MassGap.SUN.SU N)) :
    ∃ (S : Finset ILink) (D : ℕ), IsLocalOn S (O.1 : Cfg N → ℝ) ∧ ∀ l ∈ S, -(l.2 0) ≤ (D : ℤ) := by
  obtain ⟨S, hS⟩ := O.2.1
  obtain ⟨D, hD⟩ := exists_depth 0 S
  exact ⟨S, D, hS, hD⟩

/-- A field of depth `D`, flowed by a map of reach `R`, has depth `D + R`. DERIVED: `0` the plane. -/
theorem flowed_local (O : LField (MassGap.SUN.SU N)) {S : Finset ILink} {D : ℕ}
    (hS : IsLocalOn S (O.1 : Cfg N → ℝ)) (hD : ∀ l ∈ S, -(l.2 0) ≤ (D : ℤ)) {V : Cfg N → Cfg N} {R : ℕ}
    (hV : ReachLE V R) :
    ∃ S' : Finset ILink, IsLocalOn S' (fun U => O.1 (V U)) ∧ ∀ l ∈ S', -(l.2 0) ≤ ((D + R : ℕ) : ℤ) := by
  obtain ⟨S', h1, h2⟩ := isLocalOn_comp hV hS
  refine ⟨S', h1, fun l' hl' => ?_⟩
  obtain ⟨l, hl, hll⟩ := h2 l' hl'
  have a := hD l hl
  have b := (abs_le.mp (hll 0)).1
  push_cast
  omega

/-- Scaling and subtracting a constant keeps locality. DERIVED: `1` the unit observable. -/
theorem isLocalOn_scaleSub {S : Finset ILink} {F : C(Cfg N, ℝ)} (hF : IsLocalOn S (F : Cfg N → ℝ))
    (r m : ℝ) : IsLocalOn S ((r • (F - m • (1 : C(Cfg N, ℝ))) : C(Cfg N, ℝ)) : Cfg N → ℝ) := by
  intro U V h
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply, smul_eq_mul]
  rw [hF U V h]

/-- A finite sum of functions local on `S` is local on `S`. DERIVED: no numeral. -/
theorem isLocalOn_sum {ι : Type*} (s : Finset ι) (g : ι → C(Cfg N, ℝ)) {S : Finset ILink}
    (h : ∀ j ∈ s, IsLocalOn S (g j : Cfg N → ℝ)) :
    IsLocalOn S ((∑ j ∈ s, g j : C(Cfg N, ℝ)) : Cfg N → ℝ) := by
  intro U V hUV
  simp only [ContinuousMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j hj => h j hj U V hUV

/-- **The depth of a proxy**: a step-independent `D` with `msProx Wf cf k s i` local on a set no deeper
than `D + R` whenever `(Wf s).V k` has reach `R`. DERIVED: `0` the plane. -/
theorem exists_depth_msProx [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ)
    (i : Ix0) : ∃ D : ℕ, ∀ k R : ℕ, ReachLE ((Wf s).V k) R →
      ∃ S : Finset ILink, IsLocalOn S (msProx Wf cf k s i : Cfg N → ℝ)
        ∧ ∀ l ∈ S, -(l.2 0) ≤ ((D + R : ℕ) : ℤ) := by
  classical
  choose S D hS hD using fun j : MIx => exists_depth_field (N := N) (mField j)
  refine ⟨(cf i s).support.sup D, fun k R hV => ?_⟩
  choose S' hS' hD' using fun j : MIx => flowed_local (mField j) (hS j) (hD j) hV
  refine ⟨(cf i s).support.biUnion S', ?_, ?_⟩
  · unfold msProx
    refine isLocalOn_sum _ _ fun j hj => ?_
    have h1 : IsLocalOn ((cf i s).support.biUnion S') (((Wf s).fieldMap k (mField j)).1 : Cfg N → ℝ) :=
      (hS' j).mono (Finset.subset_biUnion_of_mem S' hj)
    intro U V h
    have := isLocalOn_scaleSub h1 (dySpacing N k ^ mDim j)⁻¹
      (stateK (NeZero.ne N) k ((Wf s).fieldMap k (mField j)).1) U V h
    simp only [msFlow, ContinuousMap.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
  · intro l hl
    obtain ⟨j, hj, hl'⟩ := Finset.mem_biUnion.mp hl
    have h1 := hD' j l hl'
    have h2 : D j ≤ (cf i s).support.sup D := Finset.le_sup hj
    push_cast at h1 ⊢
    omega

/-- **The proxy of a monomial is in the half-space algebra once the flowed depth fits below its lowest
time**: there is `D` such that, whenever `(Wf s).V k` has reach `R`, every test function of `P` vanishes
below `d` and `a_k (D + R) ≤ d`, `proxB Wf cf k s P ∈ halfSpaceAlg 0 0`. DERIVED: `0` the plane. -/
theorem exists_depth_proxB [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ)
    (P : TMonoG Ix0) : ∃ D : ℕ, ∀ k R : ℕ, ReachLE ((Wf s).V k) R → ∀ d : ℝ,
      (∀ i y, (P.2 i).2.1 y ≠ 0 → d ≤ y 0) → dySpacing N k * ((D + R : ℕ) : ℝ) ≤ d →
        proxB Wf cf k s P ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  classical
  choose D hD using fun i : Fin P.1 => exists_depth_msProx Wf cf s (P.2 i).1
  refine ⟨Finset.univ.sup D, fun k R hV d hd hk => ?_⟩
  unfold proxB
  refine HalfSpaceAlgebra.halfSpaceAlg_prod_mem 0 0 Finset.univ _ fun i _ => ?_
  obtain ⟨S, hS, hSD⟩ := hD i k R hV
  have ha := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hle : D i ≤ Finset.univ.sup D := Finset.le_sup (Finset.mem_univ i)
  refine smear_mem_halfSpaceAlg ha 0 hS hSD ?_ (P.2 i).2 (hd i)
  calc dySpacing N k * ((D i + R : ℕ) : ℝ)
      ≤ dySpacing N k * ((Finset.univ.sup D + R : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ ha.le
        exact_mod_cast Nat.add_le_add_right hle R
    _ ≤ d := hk

/-! ## 2. Membership where the flow does not reach the plane -/

/-- **The membership clause** of `ExpandStrong Wf cf z μ`. DERIVED: `0` the plane and the lower end of the
scale. -/
def MembershipClause [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∀ P : TSepG Ix0 0, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
    ∀ᶠ k in (ultra : Filter ℕ),
      proxB Wf cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0

/-- `ExpandStrong` carries the membership clause. DERIVED: no numeral. -/
theorem membershipClause_of_expandStrong [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (h : ExpandStrong Wf cf z μ) : MembershipClause Wf cf := h.2

/-- **Beyond `s₀` the proxy at the constant flow `sunFam … s₀` is in the half-space algebra** for all
large `k`, at every `cf` and `s`. DERIVED: `1` the least `N` of the spacing and the margin of the bound;
`2` the least colour count; `3` the range beyond the box; `0` the plane; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem eventually_mem_sunFam (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ : ℝ} (hs0 : 0 ≤ s₀) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ)
    (P : TSepG Ix0 0) (hP : BeyondR s₀ P) :
    ∀ᶠ k in atTop, proxB (fun _ => sunFam hN2 c hc0 hc s₀) cf k s P.1
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  obtain ⟨d, hsd, hd⟩ := hP
  obtain ⟨D, hD⟩ := exists_depth_proxB (fun _ => sunFam hN2 c hc0 hc s₀) cf s P.1
  have hpos : 0 < (d - s₀) / ((D : ℝ) + 3 + 1) := div_pos (by linarith) (by positivity)
  have hev : ∀ᶠ k in atTop, dySpacing N k < (d - s₀) / ((D : ℝ) + 3 + 1) :=
    (tendsto_dySpacing N).eventually (eventually_lt_nhds hpos)
  filter_upwards [hev] with k hk
  refine hD k _ ((sunFam hN2 c hc0 hc s₀).local_V k) d hd ?_
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  have hfl : (⌊s₀ / dySpacing N k⌋₊ : ℝ) ≤ s₀ / dySpacing N k := Nat.floor_le (div_nonneg hs0 ha.le)
  show dySpacing N k * ((D + (⌊s₀ / dySpacing N k⌋₊ + 3) : ℕ) : ℝ) ≤ d
  push_cast
  have e : dySpacing N k * (s₀ / dySpacing N k) = s₀ := by field_simp
  have h2 : dySpacing N k * ((D : ℝ) + 3 + 1) < d - s₀ := by
    rw [lt_div_iff₀ (by positivity)] at hk
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hfl ha.le]

/-- **At `s₀ = 0` the membership clause holds at the constant flow, for every `cf`.** DERIVED: `0` the
scale of the observer; `1` the scale bound of the witness; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem membership_sunFam_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) :
    MembershipClause (fun _ => sunFam hN2 c hc0 hc 0) cf := by
  intro P
  refine ⟨1, one_pos, fun s _ _ => ?_⟩
  obtain ⟨-, d, hd, hpos, -⟩ := P.2
  exact (eventually_mem_sunFam hN2 hc0 hc le_rfl cf s P ⟨d, hd, fun i y hy => hpos i y hy⟩).filter_mono
    ultra_le

open scoped ComplexOrder in
/-- **At `c = 0` the block step returns the link**: `polar W = W` and the phase is `1`. DERIVED: `0` the
coupling; `1` the determinant and the phase; `2` the least colour count; `6` the staple count;
`12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem sunStep_of_eq_zero (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (h : c = 0) (W : MassGap.SUN.SU N) (S : Fin 6 → MassGap.SUN.SU N) : sunStep hN c hc0 hc W S = W := by
  subst h
  apply Subtype.ext
  have hW := Matrix.mem_specialUnitaryGroup_iff.mp W.2
  have hB : blockMatN 0 W S = (W : Matrix (Fin N) (Fin N) ℂ) := by simp [blockMatN]
  have hdet : (W : Matrix (Fin N) (Fin N) ℂ).det = 1 := hW.2
  have hWW : Matrix.conjTranspose (W : Matrix (Fin N) (Fin N) ℂ) * (W : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hW.1
  have hpol : polar (W : Matrix (Fin N) (Fin N) ℂ) = W :=
    (polar_unique (by rw [hdet]; exact one_ne_zero) hW.1 (by rw [hWW]; exact Matrix.PosSemidef.one)).symm
  show projMat (blockMatN 0 W S) = W
  rw [hB, projMat, hpol, phase, hdet]
  simp

/-- **At `c = 0` the family is the identity at every step and scale.** DERIVED: `0` the coupling;
`2` the least colour count; `12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem sunFam_V_of_c_zero (hN2 : 2 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (hc : 12 * c < Real.sin (Real.pi / N))
    (h : c = 0) (s : ℝ) (k : ℕ) : (sunFam hN2 c hc0 hc s).V k = id := by
  have hstep : ∀ U : Cfg N, stepConf (sunBlockStep hN2 c hc0 hc) U = U :=
    fun U => funext fun l => sunStep_of_eq_zero hN2 hc0 hc h _ _
  have hon : ∀ (S : Set ILink) (U : Cfg N), stepOn (sunBlockStep hN2 c hc0 hc) S U = U := by
    intro S U
    funext l
    unfold stepOn
    split_ifs
    · exact congrFun (hstep U) l
    · rfl
  funext U
  show obsFlowG (sunBlockStep hN2 c hc0 hc) ⌊(s / dySpacing N k) ^ 2⌋₊ ⌊s / dySpacing N k⌋₊ U = U
  funext l
  unfold obsFlowG
  rw [Function.iterate_fixed (hon _ U)]

/-- **At `c = 0` the membership clause holds at the constant flow**, for every `s₀` and `cf`.
DERIVED: `0` the coupling and the reach; `1` the scale bound and the margin; `2` the least colour count;
`12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem membership_c_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (h : c = 0) (s₀ : ℝ) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) :
    MembershipClause (fun _ => sunFam hN2 c hc0 hc s₀) cf := by
  intro P
  refine ⟨1, one_pos, fun s _ _ => ?_⟩
  obtain ⟨-, d, hd, hpos, -⟩ := P.2
  obtain ⟨D, hD⟩ := exists_depth_proxB (fun _ => sunFam hN2 c hc0 hc s₀) cf s P.1
  have hev : ∀ᶠ k in atTop, dySpacing N k < d / ((D : ℝ) + 1) :=
    (tendsto_dySpacing N).eventually (eventually_lt_nhds (div_pos hd (by positivity)))
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev] with k hk
  have hV : ReachLE ((sunFam hN2 c hc0 hc s₀).V k) 0 := by
    rw [sunFam_V_of_c_zero hN2 hc0 hc h]
    exact reachLE_id
  refine hD k 0 hV d hpos ?_
  have ha := dySpacing_pos (by omega : 1 ≤ N) k
  rw [lt_div_iff₀ (by positivity)] at hk
  push_cast
  nlinarith

/-! ## 3. The coefficient-level statement -/

/-- **Non-membership at the constant flow, on the coefficients**: per composite index, a separated
positive-time monomial whose proxy, at every plaquette-supported `cf` and scale `s` with `cf i s ≠ 0`, is
not eventually in the half-space algebra along `ultra`. False for every `W` (`not_nonMemConst_all`): a
non-zero coefficient vector can give the zero field. `NonMemConstF` places the hypothesis on the field.
DERIVED: `0` the plane. -/
def NonMemConst [NeZero N] (W : ConfFlow N) : Prop :=
  ∀ i : Ix0, ∃ P : TSepG Ix0 0, ∀ (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ), PlaqSupp cf → cf i s ≠ 0 →
    ¬ ∀ᶠ k in (ultra : Filter ℕ),
      proxB (fun _ => W) cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0

/-- **Non-membership and the membership clause force the coefficients to vanish at small scales.**
DERIVED: `0` the limit of the scale and the zero coefficients. -/
theorem eventually_cf_zero [NeZero N] {W : ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hW : NonMemConst W) (hcf : PlaqSupp cf) (hM : MembershipClause (fun _ => W) cf) (i : Ix0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), cf i s = 0 := by
  obtain ⟨P, hP⟩ := hW i
  obtain ⟨s₀, hs₀, hm⟩ := hM P
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ s₀ :=
    (eventually_mem_nhdsWithin.mono fun s hs => hs).and
      ((eventually_le_nhds hs₀).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hev] with s hs
  by_contra hne
  exact hP cf s hcf hne (hm s hs.1 hs.2)

/-- A proxy with zero coefficients is `0`. DERIVED: `0` the coefficients. -/
theorem msProx_of_coef_zero [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {s : ℝ}
    {i : Ix0} (h : cf i s = 0) (k : ℕ) : msProx Wf cf k s i = 0 := by
  unfold msProx
  rw [h]
  simp

/-- **`ExpandR` with one index's coefficients vanishing at small scales forces the reading to `0`.**
DERIVED: `0` the limit of the scale, the zero coefficients and the limit value. -/
theorem contC_eq_zero_of_coef [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → CDatum (CRen N z μ)) (x₀ : ι) (h0 : ∀ᶠ s in 𝓝[>] (0 : ℝ), cf (F x₀).1 s = 0) {d : ℝ}
    (hd : 0 < d) (hc : ContD F) (hs : SepD d F) : contC (NeZero.ne N) (CRen N z μ) F = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  have hT : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set c : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hcdef
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c * (s / d) ^ ε < η ∧ s < θ * d ∧ 0 < s :=
      (eventually_rate_lt hε c hη).and
        (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
          (eventually_mem_nhdsWithin.mono fun s hs => hs))
    obtain ⟨s, hz, hs1, hs2, hs3⟩ := (h0.and hev).exists
    filter_upwards [hEx ι F d hd hc hs s hs3 hs2.le] with k hk
    have hlat : msLat Wf cf k s F = 0 := by
      unfold msLat
      rw [Finset.prod_eq_zero (Finset.mem_univ x₀)
        (by rw [msProx_of_coef_zero hz, smear_zero_field]), MassGap.DLRLimit.State.map_zero]
    rw [hlat, sub_zero] at hk
    rw [Real.dist_eq, sub_zero]
    have hr : Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
        = c * (s / d) ^ ε := by
      rw [hcdef]
      ring
    linarith
  exact (hT.mono_left ultra_le).limUnder_eq

/-- **`NonMemConst W` with `ExpandStrong` contradicts `CompNondeg`.** Its hypothesis is met by no `W`
(`not_nonMemConst_all`); the field-level form is `not_compNondeg_of_nonMemConstF`. DERIVED: `2` the least
colour count and the two points; `0` the first point. -/
theorem not_compNondeg_of_nonMemConst (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hW : NonMemConst W) (hcf : PlaqSupp cf)
    (hE : ExpandStrong (fun _ => W) cf z μ) : ¬ CompNondeg (NeZero.ne N) (CRen N z μ) := by
  intro hN
  have hR := expandR_of_strong hE
  obtain ⟨c, hon⟩ := exists_onShellTopN hN2
  obtain ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, hne⟩ := hN c hon
  apply hne
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hz := contC_eq_zero_of_coef hR (pairF i j f h) 0 (eventually_cf_zero hW hcf hE.2 i) hd
    (adm_pair hf hh hfh).1 (adm_pair hf hh hfh).2
  rw [show contC (NeZero.ne N) (CRen N z μ) (![(i, f), (j, h)] : Fin 2 → CDatum (CRen N z μ)) = 0
    from hz, mul_zero]

/-- **At `W = sunFam … s₀`**: under `NonMemConst W`, no choice `Wf ≡ W` with `PlaqSupp cf` meets
`ExpandStrong` and `CompNondeg` together. Its hypothesis is met by no `W` (`not_nonMemConst_all`); the
field-level form is `not_narrow_constF`. DERIVED: `2` the least colour count; `12 = 2 · 6` the coupling
bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_narrow_const (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ : ℝ} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hW : NonMemConst (sunFam hN2 c hc0 hc s₀)) (hcf : PlaqSupp cf) :
    ¬ (ExpandStrong (fun _ => sunFam hN2 c hc0 hc s₀) cf z μ ∧ CompNondeg (NeZero.ne N) (CRen N z μ)) :=
  fun ⟨hE, hP⟩ => not_compNondeg_of_nonMemConst hN2 hW hcf hE hP

/-- One plaquette channel with coefficient `1`, at every index and scale. DERIVED: `0`, `1` the axes of
the plane and the coefficient; `0` the site. -/
def cfOne : Ix0 → ℝ → (MIx →₀ ℝ) := fun _ _ => Finsupp.single (Sum.inr (((0, 1), 0) : MassGap.GibbsSpec.IPlaq)) 1

/-- `cfOne` is plaquette-supported. DERIVED: no numeral. -/
theorem plaqSupp_cfOne : PlaqSupp cfOne := by
  intro i s j hj
  refine ⟨((0, 1), 0), ?_⟩
  by_contra hne
  have h0 : cfOne i s j = 0 := by simp [cfOne, Ne.symm hne]
  exact (Finsupp.mem_support_iff.mp hj) h0

/-- `cfOne` is non-zero at every index and scale. DERIVED: `0` the excluded value. -/
theorem cfOne_ne (i : Ix0) (s : ℝ) : cfOne i s ≠ 0 := by
  simp [cfOne]

/-- **`NonMemConst` fails whenever the membership clause holds for one plaquette-supported `cf` that is
non-zero at every index and scale.** DERIVED: `0` the plane; `1` the coefficient. -/
theorem not_nonMemConst_of_membership [NeZero N] {W : ConfFlow N}
    (hM : MembershipClause (fun _ => W) cfOne) : ¬ NonMemConst W := by
  intro hW
  have i : Ix0 := eI ![0, 1, 0, 1]
  obtain ⟨P, hP⟩ := hW i
  obtain ⟨s₀, hs₀, hm⟩ := hM P
  exact hP cfOne s₀ plaqSupp_cfOne (cfOne_ne i s₀) (hm s₀ hs₀ le_rfl)

/-- **`NonMemConst` is false at `s₀ = 0`.** DERIVED: `0` the scale of the observer; `2` the least colour
count; `12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_nonMemConst_sunFam_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) : ¬ NonMemConst (sunFam hN2 c hc0 hc 0) :=
  not_nonMemConst_of_membership (membership_sunFam_zero hN2 hc0 hc cfOne)

/-- **`NonMemConst` is false at `c = 0`**, at every `s₀`. DERIVED: `0` the coupling; `2` the least colour
count; `12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_nonMemConst_c_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (h : c = 0) (s₀ : ℝ) :
    ¬ NonMemConst (sunFam hN2 c hc0 hc s₀) :=
  not_nonMemConst_of_membership (membership_c_zero hN2 hc0 hc h s₀ cfOne)

/-- **A witness of non-membership is not beyond `s₀`**: if the proxy of `P` fails to be eventually in the
half-space algebra at one `cf`, `s`, then `P` has times at or below `s₀`. DERIVED: `0` the plane;
`12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem nonMemConst_witness_not_beyond (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ : ℝ} (hs0 : 0 ≤ s₀) (P : TSepG Ix0 0)
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {s : ℝ}
    (hn : ¬ ∀ᶠ k in (ultra : Filter ℕ), proxB (fun _ => sunFam hN2 c hc0 hc s₀) cf k s P.1
      ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) : ¬ BeyondR s₀ P :=
  fun hP => hn ((eventually_mem_sunFam hN2 hc0 hc hs0 cf s P hP).filter_mono ultra_le)

/-- A flowed field reads the field at the flowed configuration. DERIVED: no numeral. -/
theorem fieldMap_apply (W : ConfFlow N) (k : ℕ) (O : LField (MassGap.SUN.SU N)) (U : Cfg N) :
    (W.fieldMap k O).1 U = O.1 (W.V k U) := rfl

/-- The plaquette field is the Wilson density of the holonomy. DERIVED: no numeral. -/
theorem plaqField_apply (q : MassGap.GibbsSpec.IPlaq) (U : Cfg N) :
    (plaqField (N := N) q).1 U
      = MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) q U) := rfl

/-- **A degenerate plaquette has the zero symmetrised field**: its holonomy is `1` in every frame.
DERIVED: `0` the density at the unit. -/
theorem symPlaq_degenerate [NeZero N] (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 = q.1.2) (U : Cfg N) :
    (sym (plaqField (N := N) q)).1 U = 0 := by
  rw [sym_apply]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [plaqField_apply, MassGap.GibbsSpec.ihol_degenerate q hq]
  exact MassGap.WilsonAction.wilsonDensity_one (NeZero.ne N)

/-- A degenerate plaquette channel is the zero field at every flow, step and scale. DERIVED: `0` the zero
field. -/
theorem msFlow_degenerate_of [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ)
    (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 = q.1.2) : msFlow Wf k s (Sum.inr q) = 0 := by
  have hF : ((Wf s).fieldMap k (mField (N := N) (Sum.inr q))).1 = 0 := by
    ext U
    rw [fieldMap_apply, mField_inr, symPlaq_degenerate q hq]
    rfl
  unfold msFlow
  rw [hF, MassGap.DLRLimit.State.map_zero]
  simp

/-- **The degenerate plaquette channel is the zero field**: `((0, 0), 0)` has holonomy `1` and density `0`,
so its flowed channel `msFlow` is `0` at every flow, step and scale. DERIVED: `0` the axes of the
degenerate plaquette, its site and the zero field. -/
theorem msFlow_degenerate [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) :
    msFlow Wf k s (Sum.inr (((0, 0), 0) : MassGap.GibbsSpec.IPlaq)) = 0 :=
  msFlow_degenerate_of Wf k s _ rfl

/-- The degenerate plaquette channel with coefficient `1`, at every index and scale. DERIVED: `0` the
axes and the site; `1` the coefficient. -/
def cfDeg : Ix0 → ℝ → (MIx →₀ ℝ) := fun _ _ => Finsupp.single (Sum.inr (((0, 0), 0) : MassGap.GibbsSpec.IPlaq)) 1

/-- `cfDeg` is plaquette-supported. DERIVED: no numeral. -/
theorem plaqSupp_cfDeg : PlaqSupp cfDeg := by
  intro i s j hj
  refine ⟨((0, 0), 0), ?_⟩
  by_contra hne
  have h0 : cfDeg i s j = 0 := by simp [cfDeg, Ne.symm hne]
  exact (Finsupp.mem_support_iff.mp hj) h0

/-- **`NonMemConst` is false for every flow**: `cfDeg` is plaquette-supported and non-zero, but every
proxy it gives is `0`, so every `proxB` is a product of zeros and lies in the half-space algebra.
DERIVED: `0` the plane, the zero field and the scale; `1` the coefficient. -/
theorem not_nonMemConst_all [NeZero N] (W : ConfFlow N) : ¬ NonMemConst W := by
  intro hW
  obtain ⟨P, hP⟩ := hW (eI ![0, 1, 0, 1])
  refine hP cfDeg 0 plaqSupp_cfDeg (by simp [cfDeg]) (Filter.Eventually.of_forall fun k => ?_)
  have hz : ∀ i : Ix0, msProx (fun _ => W) cfDeg k 0 i = 0 := by
    intro i
    unfold msProx
    simp [cfDeg, msFlow_degenerate]
  unfold proxB
  refine HalfSpaceAlgebra.halfSpaceAlg_prod_mem 0 0 Finset.univ _ fun i _ => ?_
  rw [hz, smear_zero_field]
  exact Submodule.zero_mem _

/-! ## 4. The obstruction on the field -/

/-- **Non-membership at the constant flow, on the field**: per composite index, a separated positive-time
monomial whose proxy, at every plaquette-supported `cf` and scale `s` at which the proxy field of `i` is not
eventually `0` along `ultra`, is not eventually in the half-space algebra along `ultra`.
DERIVED: `0` the plane and the zero field. -/
def NonMemConstF [NeZero N] (W : ConfFlow N) : Prop :=
  ∀ i : Ix0, ∃ P : TSepG Ix0 0, ∀ (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ), PlaqSupp cf →
    (¬ ∀ᶠ k in (ultra : Filter ℕ), msProx (fun _ => W) cf k s i = 0) →
    ¬ ∀ᶠ k in (ultra : Filter ℕ),
      proxB (fun _ => W) cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0

/-- **Field-level non-membership and the membership clause force the proxy fields to vanish at small
scales**, eventually along `ultra`. DERIVED: `0` the limit of the scale and the zero field. -/
theorem eventually_prox_zero [NeZero N] {W : ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hW : NonMemConstF W) (hcf : PlaqSupp cf) (hM : MembershipClause (fun _ => W) cf) (i : Ix0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ), msProx (fun _ => W) cf k s i = 0 := by
  obtain ⟨P, hP⟩ := hW i
  obtain ⟨s₀, hs₀, hm⟩ := hM P
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ s₀ :=
    (eventually_mem_nhdsWithin.mono fun s hs => hs).and
      ((eventually_le_nhds hs₀).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hev] with s hs
  by_contra hne
  exact hP cf s hcf hne (hm s hs.1 hs.2)

/-- **`ExpandR` with one proxy field vanishing along `ultra` at small scales forces the reading to `0`.**
DERIVED: `0` the limit of the scale, the zero field and the limit value. -/
theorem contC_eq_zero_of_prox [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hE : ExpandR Wf cf z μ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → CDatum (CRen N z μ)) (x₀ : ι)
    (h0 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ), msProx Wf cf k s (F x₀).1 = 0) {d : ℝ}
    (hd : 0 < d) (hc : ContD F) (hs : SepD d F) : contC (NeZero.ne N) (CRen N z μ) F = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hEx⟩ := hE
  have hT : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k F) (ultra : Filter ℕ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set c : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hcdef
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c * (s / d) ^ ε < η ∧ s < θ * d ∧ 0 < s :=
      (eventually_rate_lt hε c hη).and
        (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
          (eventually_mem_nhdsWithin.mono fun s hs => hs))
    obtain ⟨s, hz, hs1, hs2, hs3⟩ := (h0.and hev).exists
    filter_upwards [(hEx ι F d hd hc hs s hs3 hs2.le).filter_mono ultra_le, hz] with k hk hzk
    have hlat : msLat Wf cf k s F = 0 := by
      unfold msLat
      rw [Finset.prod_eq_zero (Finset.mem_univ x₀) (by rw [hzk, smear_zero_field]),
        MassGap.DLRLimit.State.map_zero]
    rw [hlat, sub_zero] at hk
    rw [Real.dist_eq, sub_zero]
    have hr : Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
        = c * (s / d) ^ ε := by
      rw [hcdef]
      ring
    linarith
  exact hT.limUnder_eq

/-- **The §6 obstruction, modulo `NonMemConstF`**: at the constant flow with plaquette-supported
coefficients, `NonMemConstF W` and `ExpandStrong` contradict `CompNondeg`. DERIVED: `2` the least colour
count and the two points; `0` the first point. -/
theorem not_compNondeg_of_nonMemConstF (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N}
    {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ} {μ : OffMix} (hW : NonMemConstF W)
    (hcf : PlaqSupp cf) (hE : ExpandStrong (fun _ => W) cf z μ) :
    ¬ CompNondeg (NeZero.ne N) (CRen N z μ) := by
  intro hN
  have hR := expandR_of_strong hE
  obtain ⟨c, hon⟩ := exists_onShellTopN hN2
  obtain ⟨f, h, hf, hh, ⟨d, hd, hfh⟩, hne⟩ := hN c hon
  apply hne
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hz := contC_eq_zero_of_prox hR (pairF i j f h) 0 (eventually_prox_zero hW hcf hE.2 i) hd
    (adm_pair hf hh hfh).1 (adm_pair hf hh hfh).2
  rw [show contC (NeZero.ne N) (CRen N z μ) (![(i, f), (j, h)] : Fin 2 → CDatum (CRen N z μ)) = 0
    from hz, mul_zero]

/-- **At `W = sunFam … s₀`**: under `NonMemConstF W`, no choice `Wf ≡ W` with `PlaqSupp cf` meets
`ExpandStrong` and `CompNondeg` together. DERIVED: `2` the least colour count; `12 = 2 · 6` the coupling
bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_narrow_constF (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) {s₀ : ℝ} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hW : NonMemConstF (sunFam hN2 c hc0 hc s₀)) (hcf : PlaqSupp cf) :
    ¬ (ExpandStrong (fun _ => sunFam hN2 c hc0 hc s₀) cf z μ ∧ CompNondeg (NeZero.ne N) (CRen N z μ)) :=
  fun ⟨hE, hP⟩ => not_compNondeg_of_nonMemConstF hN2 hW hcf hE hP

/-- The proxy of `cfOne` is the `((0, 1), 0)` plaquette channel. DERIVED: `0`, `1` the axes and the site;
`1` the coefficient. -/
theorem msProx_cfOne [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (i : Ix0) :
    msProx Wf cfOne k s i = msFlow Wf k s (Sum.inr (((0, 1), 0) : MassGap.GibbsSpec.IPlaq)) := by
  unfold msProx
  simp [cfOne]

/-- **A non-degenerate symmetrised plaquette is positive at the unit configuration with its head link set
to an element of positive density.** The identity frame of the symmetrisation reads the plaquette itself,
whose holonomy is that element; every other frame is non-negative. DERIVED: `0` the sign; `1` the unit
configuration and the identity frame. -/
theorem symPlaq_pos_update [NeZero N] (μ ν : Fin 4) (hμν : μ ≠ ν) (x : ISite) {g : MassGap.SUN.SU N}
    (hg : 0 < MassGap.WilsonAction.wilsonDensity g) :
    0 < (sym (plaqField (N := N) ((μ, ν), x))).1 (Function.update (1 : Cfg N) (μ, x) g) := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [sym_apply]
  have hnn : ∀ y ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4) × (Fin 4 → Bool))),
      0 ≤ (plaqField (N := N) ((μ, ν), x)).1
        (reflAll y.2 (ContinuumHypercubic.iaxisConf y.1 (Function.update (1 : Cfg N) (μ, x) g))) :=
    fun y _ => by rw [plaqField_apply]; exact MassGap.WilsonAction.wilsonDensity_nonneg hN _
  have key := Finset.single_le_sum hnn (Finset.mem_univ ((1 : Equiv.Perm (Fin 4)), fun _ : Fin 4 => false))
  have e : reflAll (fun _ : Fin 4 => false)
      (ContinuumHypercubic.iaxisConf (1 : Equiv.Perm (Fin 4)) (Function.update (1 : Cfg N) (μ, x) g))
        = Function.update (1 : Cfg N) (μ, x) g := rfl
  dsimp only at key
  rw [e] at key
  refine lt_of_lt_of_le ?_ key
  have hA : ((ν, MassGap.GibbsSpec.ishift μ x) : ILink) ≠ (μ, x) := fun h => hμν (congrArg Prod.fst h).symm
  have hB : ((μ, MassGap.GibbsSpec.ishift ν x) : ILink) ≠ (μ, x) := fun h => by
    have h' := congrFun (congrArg Prod.snd h) ν
    simp [MassGap.GibbsSpec.ishift] at h'
  have hC : ((ν, x) : ILink) ≠ (μ, x) := fun h => hμν (congrArg Prod.fst h).symm
  rw [plaqField_apply, MassGap.PlaneVariance.ihol_eq_head_mul]
  dsimp only
  rw [Function.update_self, Function.update_of_ne hA, Function.update_of_ne hB, Function.update_of_ne hC]
  simpa using hg

/-- **At an identity step a non-degenerate plaquette channel is not `0`**: `sym plaq` reads `0` at the unit
configuration (`ExistenceFlow.symPlaq_one`) and a positive value at `symPlaq_pos_update`'s configuration,
so it is not constant. DERIVED: `0` the excluded field; `1` the unit configuration; `2` the least colour
count. -/
theorem msFlow_ne_of_id (hN2 : 2 ≤ N) [NeZero N] {Wf : ℝ → ConfFlow N} {k : ℕ} {s : ℝ}
    (hV : (Wf s).V k = id) (μ ν : Fin 4) (hμν : μ ≠ ν) (x : ISite) :
    msFlow Wf k s (Sum.inr ((μ, ν), x)) ≠ 0 := by
  intro h0
  have hN : N ≠ 0 := NeZero.ne N
  have ha := dySpacing_pos (Nat.pos_of_ne_zero hN) k
  have key : ∀ U : Cfg N, (mField (N := N) (Sum.inr ((μ, ν), x))).1 U
      = stateK (NeZero.ne N) k ((Wf s).fieldMap k (mField (N := N) (Sum.inr ((μ, ν), x)))).1 := by
    intro U
    have e := congrArg (fun G : C(Cfg N, ℝ) => G U) h0
    simp only [msFlow, ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
      ContinuousMap.zero_apply, smul_eq_mul, mul_one] at e
    rw [fieldMap_apply, hV] at e
    rcases mul_eq_zero.mp e with h | h
    · exact absurd h (inv_ne_zero (pow_ne_zero _ ha.ne'))
    · rw [id_eq] at h
      linarith
  have v1 : (mField (N := N) (Sum.inr ((μ, ν), x))).1 (1 : Cfg N) = 0 := by
    rw [mField_inr]
    exact MassGap.ExistenceFlow.symPlaq_one hN _ ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := MassGap.ExistencePosNonnull.exists_wilsonDensity_pos hN2
  have v2 : 0 < (mField (N := N) (Sum.inr ((μ, ν), x))).1 (Function.update (1 : Cfg N) (μ, x) g) := by
    rw [mField_inr]
    exact symPlaq_pos_update μ ν hμν x hg
  have k1 := key 1
  have k2 := key (Function.update (1 : Cfg N) (μ, x) g)
  linarith

/-- **At an identity step the proxy of `cfOne` is not `0`** (`msFlow_ne_of_id` at the plaquette
`((0, 1), 0)`). DERIVED: `0`, `1` the axes and the site; `2` the least colour count. -/
theorem msProx_cfOne_ne_of_id (hN2 : 2 ≤ N) [NeZero N] {Wf : ℝ → ConfFlow N} {k : ℕ} {s : ℝ}
    (hV : (Wf s).V k = id) (i : Ix0) : msProx Wf cfOne k s i ≠ 0 := by
  rw [msProx_cfOne]
  exact msFlow_ne_of_id hN2 hV 0 1 (by decide) 0

/-- **`NonMemConstF` fails at a flow that is the identity at every step** and meets the membership clause
for `cfOne`. DERIVED: `0` the plane; `1` the coefficient; `2` the least colour count. -/
theorem not_nonMemConstF_of_id (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} (hV : ∀ k, W.V k = id)
    (hM : MembershipClause (fun _ => W) cfOne) : ¬ NonMemConstF W := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  intro hW
  obtain ⟨P, hP⟩ := hW (eI ![0, 1, 0, 1])
  obtain ⟨s₀, hs₀, hm⟩ := hM P
  refine hP cfOne s₀ plaqSupp_cfOne (fun hz => ?_) (hm s₀ hs₀ le_rfl)
  obtain ⟨k, hk⟩ := hz.exists
  exact msProx_cfOne_ne_of_id hN2 (Wf := fun _ => W) (hV k) _ hk

/-- **`NonMemConstF` is false at `s₀ = 0`.** DERIVED: `0` the scale of the observer; `1` the least `N` of
the spacing; `2` the least colour count; `12 = 2 · 6` the coupling bound of
`ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_nonMemConstF_sunFam_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) : ¬ NonMemConstF (sunFam hN2 c hc0 hc 0) :=
  not_nonMemConstF_of_id hN2
    (fun k => sunFam_V_of_lt hN2 hc0 hc le_rfl (dySpacing_pos (by omega : 1 ≤ N) k))
    (membership_sunFam_zero hN2 hc0 hc cfOne)

/-- **`NonMemConstF` is false at `c = 0`**, at every `s₀`. DERIVED: `0` the coupling; `2` the least colour
count; `12 = 2 · 6` the coupling bound of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_nonMemConstF_c_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (h : c = 0) (s₀ : ℝ) :
    ¬ NonMemConstF (sunFam hN2 c hc0 hc s₀) :=
  not_nonMemConstF_of_id hN2 (fun k => sunFam_V_of_c_zero hN2 hc0 hc h s₀ k)
    (membership_c_zero hN2 hc0 hc h s₀ cfOne)

/-- **No substrate core at `sunFam … s₀` with `c = 0`**, at every `s₀`: the family is the identity at every
step (`sunFam_V_of_c_zero`), and `ScaleIdentityNoGo.not_substrateCoreAt_of_id` excludes an eventually
identity observer. DERIVED: `0` the coupling; `2` the least colour count; `12 = 2 · 6` the coupling bound
of `ObserverFlowSUN.det_blockMatN_mem_slitPlane`. -/
theorem not_substrateCoreAt_sunFam_c_zero (hN2 : 2 ≤ N) [NeZero N] {c : ℝ} (hc0 : 0 ≤ c)
    (hc : 12 * c < Real.sin (Real.pi / N)) (h : c = 0) (s₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ)
    (Wf : ℝ → ConfFlow N) : ¬ SubstrateCoreAt (sunFam hN2 c hc0 hc s₀) z b Wf :=
  MassGap.ScaleIdentityNoGo.not_substrateCoreAt_of_id hN2
    (Filter.Eventually.of_forall fun k => sunFam_V_of_c_zero hN2 hc0 hc h s₀ k) z b Wf

end MassGap.ConstFlowN

end

#print axioms MassGap.ConstFlowN.reachLE_range
#print axioms MassGap.ConstFlowN.reachLE_id
#print axioms MassGap.ConstFlowN.exists_depth_field
#print axioms MassGap.ConstFlowN.flowed_local
#print axioms MassGap.ConstFlowN.isLocalOn_scaleSub
#print axioms MassGap.ConstFlowN.isLocalOn_sum
#print axioms MassGap.ConstFlowN.exists_depth_msProx
#print axioms MassGap.ConstFlowN.exists_depth_proxB
#print axioms MassGap.ConstFlowN.membershipClause_of_expandStrong
#print axioms MassGap.ConstFlowN.eventually_mem_sunFam
#print axioms MassGap.ConstFlowN.membership_sunFam_zero
#print axioms MassGap.ConstFlowN.sunStep_of_eq_zero
#print axioms MassGap.ConstFlowN.sunFam_V_of_c_zero
#print axioms MassGap.ConstFlowN.membership_c_zero
#print axioms MassGap.ConstFlowN.eventually_cf_zero
#print axioms MassGap.ConstFlowN.msProx_of_coef_zero
#print axioms MassGap.ConstFlowN.contC_eq_zero_of_coef
#print axioms MassGap.ConstFlowN.not_compNondeg_of_nonMemConst
#print axioms MassGap.ConstFlowN.not_narrow_const
#print axioms MassGap.ConstFlowN.plaqSupp_cfOne
#print axioms MassGap.ConstFlowN.cfOne_ne
#print axioms MassGap.ConstFlowN.not_nonMemConst_of_membership
#print axioms MassGap.ConstFlowN.not_nonMemConst_sunFam_zero
#print axioms MassGap.ConstFlowN.not_nonMemConst_c_zero
#print axioms MassGap.ConstFlowN.nonMemConst_witness_not_beyond
#print axioms MassGap.ConstFlowN.msFlow_degenerate
#print axioms MassGap.ConstFlowN.plaqSupp_cfDeg
#print axioms MassGap.ConstFlowN.not_nonMemConst_all
#print axioms MassGap.ConstFlowN.eventually_prox_zero
#print axioms MassGap.ConstFlowN.contC_eq_zero_of_prox
#print axioms MassGap.ConstFlowN.not_compNondeg_of_nonMemConstF
#print axioms MassGap.ConstFlowN.not_narrow_constF
#print axioms MassGap.ConstFlowN.msProx_cfOne
#print axioms MassGap.ConstFlowN.msProx_cfOne_ne_of_id
#print axioms MassGap.ConstFlowN.not_nonMemConstF_of_id
#print axioms MassGap.ConstFlowN.not_nonMemConstF_sunFam_zero
#print axioms MassGap.ConstFlowN.not_nonMemConstF_c_zero
#print axioms MassGap.ConstFlowN.fieldMap_apply
#print axioms MassGap.ConstFlowN.plaqField_apply
#print axioms MassGap.ConstFlowN.symPlaq_degenerate
#print axioms MassGap.ConstFlowN.msFlow_degenerate_of
#print axioms MassGap.ConstFlowN.symPlaq_pos_update
#print axioms MassGap.ConstFlowN.msFlow_ne_of_id
#print axioms MassGap.ConstFlowN.not_substrateCoreAt_sunFam_c_zero
