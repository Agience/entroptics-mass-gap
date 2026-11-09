import Mathlib
import MassGap.ShortDistance

/-!
# MassGap.ExpandStrong — one expansion clause in reflection-form, giving `ExpandR` and `ExpandRP`

The `SU(2)` route through `ApproxFromExpand` uses two expansion clauses:
`CompositesRenAll.ExpandR` (the `expand` field of `MultiScaleAllRenAt`: all-composite readings of separated
families against the flowed proxy readings `msLat`, with the rate `(s/d)^ε`) and
`ApproxFromExpand.ExpandRP` (the reflection norm `⟪A − B^s, A − B^s⟫` small at some scale, proxies in the
half-space algebra). This module states one clause `ExpandStrong` and proves both from it. Declarations
are in the namespace `MassGap.StrongExpand`.

Notation. For a family `F` of data `(i, f)`, `A_k(F) = ∏ smear a_k (cField(F_x)) f_x` (`compF`, the
composite product of `CRen 2 z μ`), `B_k^s(F) = ∏ smear a_k (msProx(s, i_x)) f_x` (`proxF`, the flowed proxy
product), `⟪X, Y⟫_k = ν_k(θX · Y)` with `θ = ireflObs 0 0` (`JointRP.rform` at `stateK`). For a monomial
`P` and a family `F`, `ΘP ∪ F` is `jointD P F` (the test functions of `P` reflected, as in `pairC`).

## 1. The clause

`ExpandStrong Wf cf z μ` is the conjunction of

* **(rate)** `∃ θ ε K_r κ_r, 0 < θ, 0 < ε`: for every monomial `P`, every family `F`, every `d > 0` with
  `ΘP ∪ F` continuous and `d`-separated, every `0 < s ≤ θ d`, eventually in `k`,
  `|⟪A(P), A(F)⟫ − ⟪B^s(P), B^s(F)⟫| ≤ R` and `|⟪B^s(P), A(F)⟫ − ⟪B^s(P), B^s(F)⟫| ≤ R`, with
  `R = K_r^{#(ΘP ∪ F)} (s/d)^ε ∏_{x ∈ ΘP ∪ F} d^{−κ_r(i_x)} ‖f_x‖_{L¹}` (the size factors of `ExpandR`, read
  on the joint family). This is the expansion in operator form: inside a reflected correlation the
  right-hand composites are their proxies, against a composite or a proxy left factor.
* **(membership)** for every separated positive-time monomial `P` there is `s₀ > 0` such that for every
  `0 < s ≤ s₀`, eventually along `ultra`, `B_k^s(P)` lies in the half-space algebra. This is the membership
  clause of `ExpandRP`, required on an interval of scales instead of at one scale.

## 2. What is proved

* `compF`, `proxF`, `ExpandStrong`, `expandR_of_strong`, `rform_sub_le_of_strong`, `expandRP_of_strong`,
  `contC_eq_zero_of_expandR_zero` are stated at every `SU(N)` (`[NeZero N]`); `MultiScaleStrongAt`,
  and `not_compNondeg_of_expandStrong_zero` are at `SU(2)`.
* `rform_one_left`: `⟪1, Y⟫_k = ν_k(Y)` (`θ1 = 1`).
* `expandR_of_strong`: `ExpandStrong → ExpandR`. Take `P` empty: both left factors are `1`, so the first
  bound is `|ν(A(F)) − ν(B^s(F))| ≤ R`, which is `|latC − msLat| ≤ R`; the joint family is `F`.
* `rform_sub_le_of_strong`: for every `P` with `ΘP ∪ P` continuous and `d`-separated and every
  `0 < s ≤ θ d`, eventually in `k`, `⟪A(P) − B^s(P), A(P) − B^s(P)⟫_k ≤ 3R`. By symmetry of the form
  (`rform_symm_k`), `⟪A − B, A − B⟫ = (⟪A, A⟫ − ⟪B, B⟫) − 2(⟪B, A⟫ − ⟪B, B⟫)`. This is the
  reflection-norm distance with the rate.
* `expandRP_of_strong`: `ExpandStrong → ExpandRP b` for every `b > 0`. `ΘP ∪ P` is admissible
  (`CompositeLink.adm_pairC`); choose `0 < s ≤ min(θ d, b, s₀)` with `3R(s) ≤ η` (`R(s) → 0` as `s → 0⁺`).
* `contC_eq_zero_of_expandR_zero`, `not_compNondeg_of_expandStrong_zero`: at `cf = 0` every proxy is `0`,
  so `ExpandR` forces every non-empty separated composite reading to `0` (`contC F = 0`), and
  `ExpandStrong Wf 0 z μ` contradicts `CompNondeg (CRen 2 z μ)` as soon as one combination has a non-zero
  on-shell top-dimension classical part (`CompositesRenAll.not_compNondeg_comb`). So the clause is not met
  by the zero coefficients alongside the capstone's `CompNondeg` input.
* `MultiScaleStrongAt`: `MultiScaleAllRenAt` with `expand : ExpandStrong`. `MultiScaleStrongAt.toRenAt`
  gives `MultiScaleAllRenAt`.
* No `ClayStatement` capstone is stated from `MultiScaleStrongAt`: its `endpoint` field,
  `MultiScale.Endpoint`, is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the
  zero-flux level count. `expandRP_of_strong` derives `ExpandRP` from `ExpandStrong`.

## 3. Argued (no declaration)

* **Why the operator form and not the norm alone.** `ExpandR` reads families at arbitrary times. The
  reflection norm `⟪X, X⟫` is non-negative only on the half-space algebra, so Cauchy–Schwarz
  `|⟪1, X⟫|² ≤ ⟪1, 1⟫⟪X, X⟫` reaches `ν(X)` only for positive-time `X`. The state norm `ν(X²)` would reach
  every family (`ν(X)² ≤ ν(X²)`) and dominates the reflection norm in a reflection-invariant state, but
  `X²` places every insertion at coincident points: for dimension-4 composites `ν((A_k − B_k^s)²)` is
  expected to grow as `a_k → 0`, so a `k`-independent bound on it is expected to fail. The bilinear form
  above keeps every reading separated (`ΘP ∪ F` is `d`-separated), reads arbitrary-time `F` through the
  empty `P`, and gives the reflection-norm distance by symmetry.
* **Non-circular.** `ExpandStrong` reads the lattice composites `CRen 2 z μ`, the flowed proxies
  `msProx Wf cf`, the state `stateK` and the reflection. It reads no continuum limit, no observer field of
  `W`, no `ApproxK`, `ProxyGen`, `CompNondeg` or `ClayStatementAt`.
* **Added content.** Both bounds at `P ≠ ∅` go beyond `ExpandR` and `ExpandRP`. With `ExpandR` and the
  reflection covariance of `CRen 2 z μ`, the first bound makes the proxies reflection covariant, with the
  composites' signs, inside separated correlations; this is not stated as a separate hypothesis. The
  second bound, a proxy left factor against composites on the right, is a mixed reading that neither
  clause states; it is the small-flow-time expansion inside a correlation with flowed fields.
* **Membership** is a range condition on `Wf s` at small `s` (`ApproxFromExpand` §3, `ProxyGen`); it is
  not derived from the rate clause.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)`, the parallelogram factor, the two points and the limits of the
scalar and pseudoscalar factors; `3` the sum of the three bounds; `4` the dimension; `0` the plane, the
reflection constant, the empty monomial, the zero coefficients and the limit; `1` the unit observable.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.StrongExpand

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
  MassGap.MultiScaleOS MassGap.ApproxFromExpand

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The clause -/

/-- **The composite product of a family** at step `k`: `∏ smear a_k (cField(F_x)) f_x` for `CRen 2 z μ`.
DERIVED: no numeral. -/
def compF [NeZero N] (z : Chan → ℕ → ℝ) (μ : OffMix) (k : ℕ) {ι : Type} [Fintype ι] (F : ι → Ix0 × TestFn) :
    C(Cfg N, ℝ) :=
  ∏ i, smear (dySpacing N k) (cField (NeZero.ne N) (CRen N z μ) k (F i)).1.1 (F i).2

/-- **The flowed proxy product of a family** at step `k` and scale `s`. DERIVED: no numeral. -/
def proxF [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) {ι : Type} [Fintype ι]
    (F : ι → Ix0 × TestFn) : C(Cfg N, ℝ) :=
  ∏ i, smear (dySpacing N k) (msProx Wf cf k s (F i).1) (F i).2

/-- **`ΘP ∪ F`**: the data of `P` with test functions reflected, then `F` (as `pairC`).
DERIVED: `0` the plane. -/
def jointD (P : TMonoG Ix0) {ι : Type} (F : ι → Ix0 × TestFn) : Fin P.1 ⊕ ι → Ix0 × TestFn :=
  Sum.elim (fun i => ((P.2 i).1, (P.2 i).2.reflect 0)) F

/-- **The expansion in operator form**: module docstring, §1. The rate clause bounds, inside a
reflected correlation, the change from composites to proxies on the right against a composite or a proxy
left factor; the membership clause is that of `ExpandRP` on an interval of scales.
DERIVED: `0` the plane, the reflection constant and the signs. -/
def ExpandStrong [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ) (μ : OffMix) :
    Prop :=
  (∃ (θ ε Kr : ℝ) (κr : Ix0 → ℝ), 0 < θ ∧ 0 < ε ∧
    ∀ (P : TMonoG Ix0) (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → Ix0 × TestFn) (d : ℝ), 0 < d →
      ContD (jointD P F) → SepD d (jointD P F) → ∀ s : ℝ, 0 < s → s ≤ θ * d → ∀ᶠ k in atTop,
        |rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (compF z μ k P.2) (compF z μ k F)
            - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxF Wf cf k s P.2)
                (proxF Wf cf k s F)|
          ≤ Kr ^ Fintype.card (Fin P.1 ⊕ ι) * (s / d) ^ ε
              * ∏ x, ((d ^ κr (jointD P F x).1)⁻¹ * l1 (jointD P F x).2)
        ∧ |rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxF Wf cf k s P.2) (compF z μ k F)
            - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxF Wf cf k s P.2)
                (proxF Wf cf k s F)|
          ≤ Kr ^ Fintype.card (Fin P.1 ⊕ ι) * (s / d) ^ ε
              * ∏ x, ((d ^ κr (jointD P F x).1)⁻¹ * l1 (jointD P F x).2))
  ∧ ∀ P : TSepG Ix0 0, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ᶠ k in (ultra : Filter ℕ),
        proxB Wf cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0

/-! ## 2. `ExpandR` from `ExpandStrong` -/

/-- **`θ1 = 1`, so `⟪1, Y⟫_k = ν_k(Y)`.** DERIVED: `1` the unit observable; `0` the plane. -/
theorem rform_one_left [NeZero N] (k : ℕ) (Y : C(Cfg N, ℝ)) :
    rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) 1 Y = stateK (NeZero.ne N) k Y := by
  have h1 : LatticeReflection.ireflObs (G := MassGap.SUN.SU N) 0 0 (1 : C(Cfg N, ℝ)) = 1 := by
    ext U
    simp [LatticeReflection.ireflObs_apply]
  rw [rform_apply, h1, one_mul]

/-- The empty monomial. DERIVED: `0` the empty count. -/
def emptyMono : TMonoG Ix0 := ⟨0, Fin.elim0⟩

instance : IsEmpty (Fin emptyMono.1) := (inferInstance : IsEmpty (Fin 0))

/-- **`ExpandR` from `ExpandStrong`**: the rate clause at the empty monomial. DERIVED: `0` the empty
monomial. -/
theorem expandR_of_strong [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (h : ExpandStrong Wf cf z μ) : ExpandR Wf cf z μ := by
  obtain ⟨⟨θ, ε, Kr, κr, hθ, hε, hE⟩, -⟩ := h
  refine ⟨θ, ε, Kr, κr, hθ, hε, fun ι _ _ F d hd hcont hsep s hs hsd => ?_⟩
  have hc : ContD (jointD emptyMono F) := by
    rintro (i | i)
    · exact (IsEmpty.false i).elim
    · exact hcont i
  have hsp : SepD d (jointD emptyMono F) := by
    rintro (i | i) (j | j) hij
    · exact (IsEmpty.false i).elim
    · exact (IsEmpty.false i).elim
    · exact (IsEmpty.false j).elim
    · exact hsep i j (fun e => hij (e ▸ rfl))
  filter_upwards [hE emptyMono ι F d hd hc hsp s hs hsd] with k hk
  have hA : compF (N := N) z μ k emptyMono.2 = 1 := Fintype.prod_empty _
  have hB : proxF Wf cf k s emptyMono.2 = 1 := Fintype.prod_empty _
  have e1 : latC (NeZero.ne N) (CRen N z μ) k F
      = rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (compF z μ k emptyMono.2)
          (compF z μ k F) := by
    rw [hA, rform_one_left]
    rfl
  have e2 : msLat Wf cf k s F
      = rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxF Wf cf k s emptyMono.2)
          (proxF Wf cf k s F) := by
    rw [hB, rform_one_left]
    rfl
  have hcard : Fintype.card (Fin emptyMono.1 ⊕ ι) = Fintype.card ι := by
    rw [Fintype.card_sum, Fintype.card_eq_zero (α := Fin emptyMono.1), zero_add]
  have hprod : ∏ x, ((d ^ κr (jointD emptyMono F x).1)⁻¹ * l1 (jointD emptyMono F x).2)
      = ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) := by
    rw [Fintype.prod_sum_type, Fintype.prod_empty, one_mul]
    rfl
  have h1 := hk.1
  rw [hcard, hprod, ← e1, ← e2] at h1
  exact h1

/-! ## 3. The reflection-norm distance and `ExpandRP` -/

/-- **The reflection-norm distance with the rate**: module docstring, §2. DERIVED: `3` the sum of the
three bounds; `2` the parallelogram factor; `0` the plane. -/
theorem rform_sub_le_of_strong [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} {θ ε Kr : ℝ} {κr : Ix0 → ℝ}
    (hE : ∀ (P : TMonoG Ix0) (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → Ix0 × TestFn) (d : ℝ),
      0 < d → ContD (jointD P F) → SepD d (jointD P F) → ∀ s : ℝ, 0 < s → s ≤ θ * d →
      ∀ᶠ k in atTop,
        |rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (compF z μ k P.2) (compF z μ k F)
            - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxF Wf cf k s P.2)
                (proxF Wf cf k s F)|
          ≤ Kr ^ Fintype.card (Fin P.1 ⊕ ι) * (s / d) ^ ε
              * ∏ x, ((d ^ κr (jointD P F x).1)⁻¹ * l1 (jointD P F x).2)
        ∧ |rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxF Wf cf k s P.2) (compF z μ k F)
            - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxF Wf cf k s P.2)
                (proxF Wf cf k s F)|
          ≤ Kr ^ Fintype.card (Fin P.1 ⊕ ι) * (s / d) ^ ε
              * ∏ x, ((d ^ κr (jointD P F x).1)⁻¹ * l1 (jointD P F x).2))
    (P : TMonoG Ix0) {d : ℝ} (hd : 0 < d) (hc : ContD (jointD P P.2)) (hs : SepD d (jointD P P.2))
    {s : ℝ} (hs0 : 0 < s) (hsd : s ≤ θ * d) :
    ∀ᶠ k in atTop,
      rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
          (compF z μ k P.2 - proxF Wf cf k s P.2) (compF z μ k P.2 - proxF Wf cf k s P.2)
        ≤ 3 * (Kr ^ Fintype.card (Fin P.1 ⊕ Fin P.1) * (s / d) ^ ε
              * ∏ x, ((d ^ κr (jointD P P.2 x).1)⁻¹ * l1 (jointD P P.2 x).2)) := by
  filter_upwards [hE P (Fin P.1) P.2 d hd hc hs s hs0 hsd] with k hk
  set A := compF (N := N) z μ k P.2
  set B := proxF Wf cf k s P.2
  have e : rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (A - B) (A - B)
      = (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) A A
          - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) B B)
        - 2 * (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) B A
          - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) B B) := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [rform_symm_k k A B]
    ring
  rw [e]
  have h1 := (abs_le.1 hk.1).2
  have h2 := (abs_le.1 hk.2).1
  linarith

/-- For any constant `c`, `c (s/d)^ε < η` for all small `s > 0`. DERIVED: `0` the limit of the scale. -/
theorem eventually_rate_lt {ε d : ℝ} (hε : 0 < ε) (c : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), c * (s / d) ^ ε < η := by
  have hrp : Tendsto (fun s : ℝ => c * (s / d) ^ ε) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℝ => c * (s / d) ^ ε) 0 :=
      continuousAt_const.mul ((continuousAt_id.div_const d).rpow_const (Or.inr hε.le))
    have h0 := hc.tendsto
    simp only [zero_div, Real.zero_rpow hε.ne', mul_zero] at h0
    exact h0
  exact (hrp.eventually (gt_mem_nhds hη)).filter_mono nhdsWithin_le_nhds

/-- **`ExpandRP` from `ExpandStrong`**, at every `b > 0`. Module docstring, §2. DERIVED: `3` the sum of
the three bounds; `0` the plane. -/
theorem expandRP_of_strong [NeZero N] {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (h : ExpandStrong Wf cf z μ) : ExpandRP b Wf cf z μ := by
  obtain ⟨⟨θ, ε, Kr, κr, hθ, hε, hE⟩, hmem⟩ := h
  intro P η hη
  obtain ⟨hcont, d, hd, hsep⟩ := adm_pairC (CRen N z μ) P P
  have hc : ContD (jointD P.1 P.1.2) := hcont
  have hs : SepD d (jointD P.1 P.1.2) := hsep
  obtain ⟨s₀, hs₀, hM⟩ := hmem P
  set c : ℝ := Kr ^ Fintype.card (Fin P.1.1 ⊕ Fin P.1.1)
    * ∏ x, ((d ^ κr (jointD P.1 P.1.2 x).1)⁻¹ * l1 (jointD P.1 P.1.2 x).2) with hcdef
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      c * (s / d) ^ ε < η / 3 ∧ s < θ * d ∧ s < b ∧ s < s₀ ∧ 0 < s :=
    (eventually_rate_lt hε c (by positivity : 0 < η / 3)).and
      (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
        (((gt_mem_nhds hb).filter_mono nhdsWithin_le_nhds).and
          (((gt_mem_nhds hs₀).filter_mono nhdsWithin_le_nhds).and
            (eventually_mem_nhdsWithin.mono fun s hs => hs))))
  obtain ⟨s, hs1, hs2, hs3, hs4, hs5⟩ := hev.exists
  refine ⟨s, hs5, hs3.le, ?_⟩
  filter_upwards [(rform_sub_le_of_strong hE P.1 hd hc hs hs5 hs2.le).filter_mono ultra_le,
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

/-! ## 4. The zero coefficients -/

/-- At `cf = 0` every proxy is `0`. DERIVED: `0` the zero coefficients. -/
theorem msProx_zero [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (i : Ix0) : msProx Wf 0 k s i = 0 := by
  unfold msProx
  simp

/-- The smear of the zero field is `0`. DERIVED: `0` the zero field. -/
theorem smear_zero_field (a : ℝ) (f : TestFn) : smear a (0 : C(Cfg N, ℝ)) f = 0 := by
  unfold smear
  simp

/-- **At `cf = 0`, `ExpandR` forces every non-empty separated composite reading to `0`.**
DERIVED: `0` the zero coefficients and the limit. -/
theorem contC_eq_zero_of_expandR_zero [NeZero N] {Wf : ℝ → ConfFlow N} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : ExpandR Wf 0 z μ) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → CDatum (CRen N z μ)) {d : ℝ} (hd : 0 < d) (hc : ContD F) (hs : SepD d F) :
    contC (NeZero.ne N) (CRen N z μ) F = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨θ, ε, Kr, κr, hθ, hε, hE⟩ := h
  have hz : ∀ k s, msLat Wf 0 k s F = 0 := fun k s => by
    unfold msLat
    rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι))
      (by rw [msProx_zero, smear_zero_field]), MassGap.DLRLimit.State.map_zero]
  have hT : Tendsto (fun k => latC (NeZero.ne N) (CRen N z μ) k F) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set c : ℝ := Kr ^ Fintype.card ι * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2) with hcdef
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), c * (s / d) ^ ε < η ∧ s < θ * d ∧ 0 < s :=
      (eventually_rate_lt hε c hη).and
        (((gt_mem_nhds (mul_pos hθ hd)).filter_mono nhdsWithin_le_nhds).and
          (eventually_mem_nhdsWithin.mono fun s hs => hs))
    obtain ⟨s, hs1, hs2, hs3⟩ := hev.exists
    filter_upwards [hE ι F d hd hc hs s hs3 hs2.le] with k hk
    rw [hz, sub_zero] at hk
    rw [Real.dist_eq, sub_zero]
    have hr : Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)
        = c * (s / d) ^ ε := by
      rw [hcdef]
      ring
    linarith
  exact (hT.mono_left ultra_le).limUnder_eq

/-- **`ExpandStrong` at the zero coefficients contradicts `CompNondeg`** as soon as one combination has a
non-zero on-shell top-dimension classical part. DERIVED: `0` the zero coefficients; `2` the two points. -/
theorem not_compNondeg_of_expandStrong_zero {Wf : ℝ → ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix}
    (h : ExpandStrong Wf 0 z μ) (c : Ix0 →₀ ℝ)
    (hon : ∃ (A : GPot 2) (g : ℝ), GPot.Adm A ∧ OnShell g A
      ∧ ∑ i ∈ c.support.filter (fun i => cdim i.1 = c.support.sup (fun j => cdim j.1)),
          c i * g ^ cnF i.1 * cval g A i.1 ≠ 0) :
    ¬ CompNondeg h2N (CRen 2 z μ) := by
  have hR := expandR_of_strong h
  refine not_compNondeg_comb h2N (CRen 2 z μ) c hon fun f g hf hg hsep => ?_
  obtain ⟨d, hd, hfg⟩ := hsep
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hc : ContD (![(i, f), (j, g)] : Fin 2 → CDatum (CRen 2 z μ)) := by
    intro x
    fin_cases x
    exacts [hf, hg]
  have hgf : ContinuumSep.sepBy d g f := fun y w hy hw => by
    obtain ⟨m, hm⟩ := hfg w y hw hy
    exact ⟨m, by rw [abs_sub_comm]; exact hm⟩
  have hs : SepD d (![(i, f), (j, g)] : Fin 2 → CDatum (CRen 2 z μ)) := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact (hxy rfl).elim
    · exact hfg
    · exact hgf
    · exact (hxy rfl).elim
  rw [contC_eq_zero_of_expandR_zero hR _ hd hc hs, mul_zero]

/-! ## 5. The `SU(2)` record -/

/-- **The multi-scale statement with the operator-form expansion**: `MultiScaleAllRenAt` with
`expand : ExpandStrong`. -/
structure MultiScaleStrongAt (W : ConfFlow 2) (z : Chan → ℕ → ℝ) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow 2) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale: the asymptotic-freedom moments of every monomial. -/
  scale : ScaleControlAll b Wf
  /-- The small-flow-time expansion in operator form. -/
  expand : ExpandStrong Wf cf z μ
  /-- Asymptotic freedom: a two-point kernel of the trace at `z` with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel h2N (rhoD (fR 2) z) G ∧ AFCoefficient 2 G
  /-- Strong coupling at the physical scale: the slice endpoint with the odd levels. -/
  endpoint : MultiScale.Endpoint

/-- `MultiScaleStrongAt` gives `MultiScaleAllRenAt` (`expandR_of_strong`). -/
theorem MultiScaleStrongAt.toRenAt {W : ConfFlow 2} {z : Chan → ℕ → ℝ} {μ : OffMix} {b : ℝ}
    {Wf : ℝ → ConfFlow 2} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (H : MultiScaleStrongAt W z μ b Wf cf) :
    MultiScaleAllRenAt W z μ b Wf cf :=
  ⟨H.b_pos, H.top, H.scale, expandR_of_strong H.expand, H.af, H.endpoint⟩

end MassGap.StrongExpand

end

#print axioms MassGap.StrongExpand.rform_one_left
#print axioms MassGap.StrongExpand.expandR_of_strong
#print axioms MassGap.StrongExpand.rform_sub_le_of_strong
#print axioms MassGap.StrongExpand.eventually_rate_lt
#print axioms MassGap.StrongExpand.expandRP_of_strong
#print axioms MassGap.StrongExpand.msProx_zero
#print axioms MassGap.StrongExpand.smear_zero_field
#print axioms MassGap.StrongExpand.contC_eq_zero_of_expandR_zero
#print axioms MassGap.StrongExpand.not_compNondeg_of_expandStrong_zero
#print axioms MassGap.StrongExpand.MultiScaleStrongAt.toRenAt
