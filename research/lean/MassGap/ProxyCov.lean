import Mathlib
import MassGap.ExpandMatch
import MassGap.ApertureThing
import MassGap.ConstFlowN

/-!
# MassGap.ProxyCov — reflection covariance of the flowed proxies and their translated smearings

The flowed proxies `msProx Wf cf k s i = ∑ⱼ cf i s j · msFlow Wf k s j` are read by `ProxyNondeg`
(through `proxRead`) and by `ExpandMatch.RPGerm` (through `proxB`). This module proves, at every finite
step `k`, how they transform under the time reflection `θ = ireflObs 0 0` and the lattice translations,
and uses it to identify `proxRead` with the reflected gap read `ApertureThing.gK` and the diagonal half of
`RPGerm` with `ExpandFam.ExpandLim`. Declarations are in the namespace `MassGap.ProxyCov`.

## 1. Covariance (proved from the definitions)

* `mPar j`: the number of time indices of the scale index `j` (`ctau 0` of the monomial for `inl i`,
  `0` for the symmetrised plaquette density).
* `mField_refl`: `θ (mField j) = (−1)^{mPar j} mField j`. For a monomial the bare field is the reflection
  average `reflAvg (ctau 0 i) (bareF i)` (`ReflAvg.reflAvg_refl`); the plaquette density is the
  hypercubic symmetrisation (`ObserverSymField.sym_refl`). This is the sign of the electric channels:
  `electric_sign` exhibits a monomial (`F₀₁F₁₂`) with sign `−1`, `magnetic_sign` one (`F₁₂F₁₂`) with `+1`.
* `fieldMap_mField_refl`, `msFlow_refl`: every flow `ConfFlow` commutes with `θ` (its field `refl`),
  and the periodic state is reflection invariant, so `θ (msFlow j) = (−1)^{mPar j} msFlow j` at every
  step, scale and flow. No hypothesis enters.
* `CfParity cf`: every coefficient `cf i s j ≠ 0` joins indices of the same reflection sign,
  `(−1)^{mPar j} = (−1)^{ctau 0 i}`. Under it, `msProx_refl`: `θ (msProx i) = (−1)^{ctau 0 i} msProx i`,
  the sign of the composite `i` in `CompositesRen.reflCovLat_CRen`; `smear_msProx_refl`, `proxB_refl` carry
  it through the smearing (`ContinuumField.ireflObs_smear`) and the product.
* Translation: `transObs_cXs`. The proxy `msProx i` is one observable; its smearing against `f` translated
  by `a n` is its smearing against `f` translated by `n` lattice steps (`ContinuumField.smear_translate`).
  Together with the translation invariance of the state (`ContinuumNontrivial.stateK_transObs`, inside
  `ApertureThing.reflShiftK`) this is the whole translation covariance the identifications read; the
  translation covariance of the flow itself is not read.

`CfParity` is the one structural input. It is a condition on the chosen coefficients, not on the flow:
`cf` is free data of the bundle, and a coefficient may join an electric to a magnetic monomial
(`not_cfParity_mix` exhibits one; that the two flowed monomials are then independent, so that
`θ (msProx i)` is not `± msProx i`, is not proved). `cfParity_cfScaled` proves it for every
leading-logarithm family `FlowChoice.cfScaled κ γ` whose `κ` joins same-sign indices, and
`cfParity_cfLead` for `FlowChoice.cfLead` (each proxy its own flowed monomial).

## 2. The diagonal half of `RPGerm` (proved)

* `proxD_eq`: `⟪B, B⟫ = sgn(P) · msLat(pairC P P)`, `B = proxB P`, under `CfParity`.
* `diag_germ`: `ExpandLim` and `CfParity` give, for every separated positive-time monomial `P` and
  `η > 0`, for all small `s > 0`, eventually in the step, `|⟪A, A⟫ − ⟪B, B⟫| ≤ η`, `A` the composite product.
  `⟪A, A⟫ = sgn(P) latC(pairC P P)` (`JointRP.rReadC_of_cov`), `⟪B, B⟫ = sgn(P) msLat(pairC P P)`, and
  `ExpandLim` reads the admissible family `pairC P P` (`CompositeLink.adm_pairC`).
* `MixGerm`: the mixed germ, `|⟪B, A⟫ − ⟪B, B⟫| ≤ η` with the proxy product in the half-space algebra.
* `rpGerm_iff_mixGerm`: under `ExpandLim` and `CfParity`, `RPGerm ↔ MixGerm`. Forward by
  `ExpandMatch.form_sub_split` and `diag_germ`; backward by the same split, with
  `0 ≤ ⟪A − B, A − B⟫` from reflection positivity (`A` eventually in the half-space algebra,
  `JointRP.eventually_cMono_mem`). `expandMatch_of_mixGerm`: `ExpandRF`, `CfParity` and `MixGerm` give
  `ExpandMatch`.

## 3. The reflected gap read (proved)

`cX c f = ∑ᵢ cᵢ smear(msProx i, f)`; `proxRead_eq`: `proxRead c f h = ν_k(cX c f · cX c h)`.

* `proxRead_refl_split`: under `CfParity`, for every combination `c`, positive-time `g` and gap `m`,
  `proxRead c (θg) (T_{2m} g) = gK k Y₊ m − gK k Y₋ m`, `Y₊`, `Y₋` the parts of `cX c g` over the even and
  the odd indices of `c` (`T_{2m}` the translation by `2m` lattice steps in time). The cross terms cancel:
  the time step is symmetric for the reflection form (`ApertureThing.shift_pow`).
* `abs_proxRead_pure`: for a combination of one reflection sign (`PureC c`) with `cX c g` in the
  half-space algebra, `|proxRead c (θg) (T_{2m} g)| = gK k (cX c g) m`.
* `floor_of_reads`, `gK_far_floor`: for `X` in the half-space algebra, from `δ ≤ gK(m₁)`, `gK(0) ≤ U`,
  `1 ≤ m₁ ≤ m`:
  `U · min(δ/U, 1)^{m/m₁} ≤ gK(m)` (`ApertureThing.far_ge_rpow`).
* `proxRead_far`: the same along any filter of steps, in physical gaps `t₁ = 2 m₁ a_k`, `t = 2 m a_k`:
  the exponent is the ratio of the physical gaps `t/t₁`.
* `contact_bound`: the contact read `proxRead c (θg) g` is itself a separated read (`θg` and `g` are
  `2d`-separated, `sep_refl_translate`), so `ExpandLim` and `ConvC` bound it by `|contRead| + η` for all
  small `s`, eventually along `ultra`.
* `gapRead_far`: under `ExpandLim`, `ConvC` and `CfParity`, for a combination of one reflection sign
  and a positive-time `g`, non-degeneracy at one physical gap `t₁` (`δ ≤ |proxRead c (θg) (T_{t₁} g)|`,
  with `cX c g` in the half-space algebra) gives non-degeneracy at every larger gap `t` the lattice
  resolves, with the floor `U · min(δ/U, 1)^{t/t₁}`, `U = |contRead c (θg) g| + δ`: every number is a
  read. `rep_dyadic`: every dyadic gap `t = j a₀ / 2^{k₀}` (`a₀ = aRun N 1`) is resolved from the step
  `k₀` on, so the representation hypothesis is met at every pair of dyadic gaps `t₁ ≤ t`
  (`gapRead_far_dyadic`).
* `exists_depth_cX`, `eventually_cX_mem`: the half-space membership of `cX c g` holds, eventually in the
  step, whenever `g` vanishes below a time `d` and the flow at scale `s` has physical range eventually at
  most some `r < d` (`ConstFlowN.exists_depth_msProx`, `ContinuumField.smear_mem_halfSpaceAlg`).
  `gapRead_far_of_range`: `gapRead_far` with that membership discharged by the range condition for all
  small `s`.
* `proxyNondeg_of_gapRead`: `ProxyNondeg` follows from `GapRead` at every combination. `GapRead` is
  `ProxyNondeg`'s own clause with the pair pinned to `(θg, T_t g)` (the separation is
  `sep_refl_translate`); the theorem restates, it does not discharge. Its content is what the pinning
  gives: for a combination of one sign the pinned read is the reflected gap read, and `gapRead_far`
  carries it from one gap to every larger one. At a combination of both signs it gives nothing.

## 4. The load-bearing tests (proved)

* `not_cfParity_mix`: the coefficients joining `F₀₁F₁₂` and `F₁₂F₁₂` fail `CfParity`.
* `parity_load_bearing`: an abstract model, not a lattice one. On `ℝ²` with the dot product as the state
  and `θ = diag(1, −1)` (an even and an electric channel), the pure vectors have `|⟨θX, X⟩| = ⟨X, X⟩`, and
  the mixed vector `(1, 1)` has reflected read `0` and direct read `2`: the shape of the identification
  `|proxRead| = gK` of `abs_proxRead_pure` fails once one reflection sign is dropped.
* `mixed_no_propagate`: a mixed combination reads `g₊ − g₋` (`proxRead_refl_split`); with
  `g₊(m) = (4 · 2^{−m})²` and `g₋(m) = 1`, two `ReflShift` reads (`ApertureThing.geom_sharp`), the
  difference is `3` at gap `1` and `0` at gap `2`. An abstract model: for a difference of two
  log-convex reads non-degeneracy at one gap does not propagate; that the even and odd parts of a lattice
  combination realise these reads is not shown. `gapRead_far` needs `PureC`.

## 5. What remains

* `CfParity` is an input on the coefficients (§1); `cfLead` meets it. Projecting `cf` onto its
  same-sign part is not shown to preserve `ExpandLim`: no reflection identity removes the two-point
  reading of the opposite-sign part (`RoutePin.projection_load_bearing`, an abstract model).
* `MixGerm`: the mixed germ `⟪B^s, A⟫ − ⟪B^s, B^s⟫ → 0`, a reading with proxies on the reflected side and
  composites on the other. `ExpandLim` reads one family with every composite replaced; it does not read
  this mixed family. `ExpandMatch.diag_not_enough` shows the mixed term cannot be dropped.
* `GapRead` at one gap, per combination of one sign: the separated reflected read of the proxies is
  bounded below at one gap. The far floor is proved; the inner read is not removed
  (`ApertureThing.inner_load_bearing`). The half-space membership of `cX c g` in `gapRead_far` is met
  wherever the flow's physical range stays below the margin of `g` (`gapRead_far_of_range`). `ConfFlow`
  does not tie its range to the scale `s`; for the route's `Wf` that `a_k · range k` eventually stays below
  every positive margin as `s → 0⁺` is not a field of the bundle (`(Φ0 W).PhysRange r` bounds the range of
  `Wf b = W` only). At the family `Wf = ObserverFlowSUN.sunFam …` it holds at every positive margin
  (`RoutePin.sunFam_range_small`).
* A combination of both signs: its reflected read is the difference `g₊ − g₋` of two log-convex reads;
  `ProxyNondeg` at such a combination is not reduced (`mixed_no_propagate`).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the time axis, the plane, the contact gap, the signs, the even parity count and
the limit point; `1` the unit step, the least inner gap, the cap of `min(·, 1)` and the unit
coefficient; `2` the two steps of one gap, the two points, the parallelogram factor, the parity modulus
and the separation `2d` of `θg` from `g`; `4` the quarter of the split `ε/2 + 2 · ε/4`; `−1` the
reflection sign; the indices `0, 1, 2` of `F₀₁F₁₂`, `F₁₂F₁₂`; `3`, `16`, `1/2`, `4` the values of the
mixed test; `δ`, `U`, `t₁`, `t`, `j`, `k₀` reads or hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ProxyCov

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
  MassGap.CompositesBuild MassGap.MultiScaleAll MassGap.CompositesRen MassGap.ApproxFromExpand
  MassGap.NondegFromProxy MassGap.ClayData MassGap.ReflAvg

variable {N : ℕ}

/-! ## 1. Covariance -/

/-- The reflection parity count of a scale index: the time indices of the monomial, `0` for the
symmetrised plaquette density. DERIVED: `0` the time axis and the even count. -/
def mPar : MIx → ℕ
  | Sum.inl i => ctau 0 i.1
  | Sum.inr _ => 0

/-- The fields of the scale indices are reflection covariant. DERIVED: `0` the plane; `−1` the
sign. -/
theorem mField_refl (j : MIx) :
    ((mField j : LField (MassGap.SUN.SU N)).refl 0).1
      = ((-1 : ℝ) ^ mPar j) • (mField j : LField (MassGap.SUN.SU N)).1 := by
  cases j with
  | inl i => exact reflAvg_refl _ _
  | inr q =>
    rw [mField_inr, MassGap.ObserverSymField.sym_refl]
    simp [mPar]

/-- A flowed field of a scale index is reflection covariant, for every flow. DERIVED: `0` the
plane; `−1` the sign. -/
theorem fieldMap_mField_refl (W : ConfFlow N) (k : ℕ) (j : MIx) :
    ((W.fieldMap k (mField j)).refl 0).1 = ((-1 : ℝ) ^ mPar j) • (W.fieldMap k (mField j)).1 := by
  rw [← W.fieldMap_refl]
  ext U
  show ((mField j : LField (MassGap.SUN.SU N)).refl 0).1 (W.V k U)
    = ((-1 : ℝ) ^ mPar j) * (mField j : LField (MassGap.SUN.SU N)).1 (W.V k U)
  rw [mField_refl]
  rfl

/-- The connected flowed monomial is reflection covariant: `θ (msFlow j) = (−1)^{mPar j} msFlow j`,
at every step, scale and flow. DERIVED: `0` the plane; `−1` the sign. -/
theorem msFlow_refl [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    LatticeReflection.ireflObs 0 0 (msFlow Wf k s j) = ((-1 : ℝ) ^ mPar j) • msFlow Wf k s j := by
  have h := refl_sub_cov (NeZero.ne N) k 0 ((Wf s).fieldMap k (mField j)) (mPar j)
    (fieldMap_mField_refl (Wf s) k j)
  unfold msFlow
  rw [map_smul, smul_comm ((-1 : ℝ) ^ mPar j)]
  congr 1

/-- The coefficients join indices of one reflection sign. Module docstring, §1. DERIVED: `−1` the
sign; `0` the plane. -/
def CfParity (cf : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∀ (i : Ix0) (s : ℝ) (j : MIx), j ∈ (cf i s).support → (-1 : ℝ) ^ mPar j = (-1 : ℝ) ^ ctau 0 i.1

/-- The flowed proxy is reflection covariant with the sign of its composite. DERIVED: `0` the
plane; `−1` the sign. -/
theorem msProx_refl [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hP : CfParity cf)
    (k : ℕ) (s : ℝ) (i : Ix0) :
    LatticeReflection.ireflObs 0 0 (msProx Wf cf k s i) = ((-1 : ℝ) ^ ctau 0 i.1) • msProx Wf cf k s i := by
  unfold msProx
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_smul, msFlow_refl, hP i s j hj, smul_comm]

/-- The smeared proxy under reflection. DERIVED: `0` the plane; `−1` the sign. -/
theorem smear_msProx_refl [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hP : CfParity cf) (k : ℕ) (s : ℝ) (i : Ix0) (f : TestFn) :
    LatticeReflection.ireflObs 0 0 (smear (dySpacing N k) (msProx Wf cf k s i) f)
      = ((-1 : ℝ) ^ ctau 0 i.1) • smear (dySpacing N k) (msProx Wf cf k s i) (f.reflect 0) := by
  have ha := dySpacing_pos (one_le_of_ne_zero (NeZero.ne N)) k
  rw [ireflObs_smear ha, msProx_refl hP, smear_smul ha]

/-- The coefficients of one-sign leading-logarithm families meet `CfParity`. DERIVED: `−1` the
sign. -/
theorem cfParity_cfScaled (κ : Ix0 → MIx →₀ ℝ) (γ : Ix0 → ℝ)
    (hκ : ∀ i j, j ∈ (κ i).support → (-1 : ℝ) ^ mPar j = (-1 : ℝ) ^ ctau 0 i.1) :
    CfParity (FlowChoice.cfScaled κ γ) :=
  fun i _ j hj => hκ i j (Finsupp.support_onFinset_subset hj)

/-- `cfLead` meets `CfParity`. DERIVED: `1` the unit coefficient. -/
theorem cfParity_cfLead : CfParity FlowChoice.cfLead :=
  cfParity_cfScaled _ _ fun i j hj => by
    have hj' := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
    subst hj'
    rfl

/-- The electric monomial `F₀₁F₁₂`. DERIVED: `0`, `1`, `2` the indices. -/
abbrev eE : Ix0 := eI (![0, 1, 1, 2] : Idx4)

/-- The magnetic monomial `F₁₂F₁₂`. DERIVED: `1`, `2` the indices. -/
abbrev eM : Ix0 := eI (![1, 2, 1, 2] : Idx4)

/-- An electric channel has reflection sign `−1`. DERIVED: `−1` the sign. -/
theorem electric_sign : (-1 : ℝ) ^ mPar (Sum.inl eE) = -1 := by
  show (-1 : ℝ) ^ ctau 0 (emono (![0, 1, 1, 2] : Idx4)) = -1
  rw [sign_emono]
  simp [sθ, rsg, Fin.prod_univ_four]

/-- A magnetic channel has reflection sign `+1`. DERIVED: `1` the sign. -/
theorem magnetic_sign : (-1 : ℝ) ^ mPar (Sum.inl eM) = 1 := by
  show (-1 : ℝ) ^ ctau 0 (emono (![1, 2, 1, 2] : Idx4)) = 1
  rw [sign_emono]
  simp [sθ, rsg, Fin.prod_univ_four]

/-- A coefficient joining an electric and a magnetic monomial fails `CfParity`. DERIVED: `1` the
unit coefficients; `0` the scale. -/
theorem not_cfParity_mix :
    ¬ CfParity (fun _ _ => Finsupp.single (Sum.inl eE) 1 + Finsupp.single (Sum.inl eM) 1 :
      Ix0 → ℝ → (MIx →₀ ℝ)) := by
  classical
  intro h
  have hne : (Sum.inl eE : MIx) ≠ Sum.inl eM := fun he => by
    have h1 := electric_sign
    rw [he, magnetic_sign] at h1
    norm_num at h1
  have hmem : (Sum.inl eM : MIx) ∈
      (Finsupp.single (Sum.inl eE) (1 : ℝ) + Finsupp.single (Sum.inl eM) 1).support := by
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg hne,
      Finsupp.single_eq_same]
    norm_num
  have h2 := h eE 0 (Sum.inl eM) hmem
  have h3 : (-1 : ℝ) ^ ctau 0 eE.1 = -1 := electric_sign
  rw [magnetic_sign, h3] at h2
  norm_num at h2

/-! ## 2. The diagonal half of `RPGerm` -/

/-- The reflection sign of a monomial of composites. DERIVED: `0` the plane; `−1` the sign. -/
def sgnP (P : TMonoG Ix0) : ℝ := ∏ i, (-1 : ℝ) ^ ctau 0 (P.2 i).1.1

/-- DERIVED: `1` the modulus of the sign. -/
theorem abs_sgnP (P : TMonoG Ix0) : |sgnP P| = 1 := by
  unfold sgnP
  rw [Finset.abs_prod]
  simp

/-- `sgnC` of the renormalised composites is `sgnP`. DERIVED: `0` the plane. -/
theorem sgnC_CRen (z : Chan → ℕ → ℝ) (μ : OffMix) (P : TMonoG (CRen N z μ).Ix) :
    sgnC (CRen N z μ) 0 P = sgnP P := rfl

/-- The proxy product under reflection. DERIVED: `0` the plane. -/
theorem proxB_refl [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hP : CfParity cf)
    (k : ℕ) (s : ℝ) (P : TMonoG Ix0) :
    LatticeReflection.ireflObs 0 0 (proxB Wf cf k s P)
      = sgnP P • ∏ i, smear (dySpacing N k) (msProx Wf cf k s (P.2 i).1) ((P.2 i).2.reflect 0) := by
  have hθ : LatticeReflection.ireflObs 0 0 (proxB Wf cf k s P)
      = ∏ i, LatticeReflection.ireflObs 0 0
          (smear (dySpacing N k) (msProx Wf cf k s (P.2 i).1) (P.2 i).2) :=
    (LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) 0 0).theta_prod Finset.univ
      (fun i => smear (dySpacing N k) (msProx Wf cf k s (P.2 i).1) (P.2 i).2)
  rw [hθ, Finset.prod_congr rfl (fun i _ => smear_msProx_refl hP k s (P.2 i).1 (P.2 i).2),
    prod_smul_eq, sgnP]

/-- The proxies' diagonal reflection read is the flowed reading of `ΘP ∪ P`. DERIVED: `0` the
plane. -/
theorem proxD_eq [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hP : CfParity cf)
    (z : Chan → ℕ → ℝ) (μ : OffMix) (k : ℕ) (s : ℝ) (P : TMonoG (CRen N z μ).Ix) :
    rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxB Wf cf k s P) (proxB Wf cf k s P)
      = sgnP P * msLat Wf cf k s (pairC (CRen N z μ) 0 P P) := by
  rw [rform_apply, proxB_refl hP, smul_mul_assoc, MassGap.DLRLimit.State.map_smul]
  congr 1
  unfold msLat proxB
  rw [Fintype.prod_sum_type]
  rfl

/-- The diagonal germ from `ExpandLim`: module docstring, §2. DERIVED: `0` the plane and the limit
point. -/
theorem diag_germ [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ) (hP : CfParity cf) (P : TSepG (CRen N z μ).Ix 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in atTop,
      |rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1))
          (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1))
        - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
          (proxB Wf cf k s P.1) (proxB Wf cf k s P.1)| ≤ η := by
  filter_upwards [hL _ (pairC (CRen N z μ) 0 P.1 P.1) (adm_pairC (CRen N z μ) P P) η hη] with s hs
  filter_upwards [hs] with k hk
  rw [← rReadC_eq, rReadC_of_cov (NeZero.ne N) (CRen N z μ) 0 (reflCovLat_CRen z μ), proxD_eq hP z μ,
    sgnC_CRen, ← mul_sub, abs_mul, abs_sgnP, one_mul]
  exact hk

/-- The mixed germ: module docstring, §2. DERIVED: `0` the plane and the limit point. -/
def MixGerm [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (z : Chan → ℕ → ℝ)
    (μ : OffMix) : Prop :=
  ∀ (P : TSepG (CRen N z μ).Ix 0) (η : ℝ), 0 < η →
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      proxB Wf cf k s P.1 ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ |rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0) (proxB Wf cf k s P.1)
            (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1))
          - rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
            (proxB Wf cf k s P.1) (proxB Wf cf k s P.1)| ≤ η

/-- `RPGerm` from the mixed germ, under `ExpandLim` and `CfParity`. DERIVED: `2` the halving and the
parallelogram factor; `4` the quarter. -/
theorem rpGerm_of_mixGerm [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ) (hP : CfParity cf)
    (hM : MixGerm Wf cf z μ) : ExpandMatch.RPGerm Wf cf z μ := by
  intro P η hη
  filter_upwards [diag_germ hL hP P (half_pos hη), hM P (η / 4) (by positivity)] with s hd hm
  filter_upwards [hd.filter_mono ultra_le, hm] with k hk1 hk2
  refine ⟨hk2.1, ?_⟩
  rw [ExpandMatch.form_sub_split _ (rform_symm_k k)]
  linarith [(abs_le.mp hk1).2, (abs_le.mp hk2.2).1]

/-- The mixed germ from `RPGerm`, under `ExpandLim` and `CfParity`. DERIVED: `0` the sign of the
reflection norm; `2` the parallelogram factor. -/
theorem mixGerm_of_rpGerm [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ) (hP : CfParity cf)
    (hR : ExpandMatch.RPGerm Wf cf z μ) : MixGerm Wf cf z μ := by
  intro P η hη
  have hUL : UnifLocal (CRen N z μ) := unifLocal_buildRen (rhoD (fR N) z) (bareD (fR N) (bR N)) μ
  filter_upwards [diag_germ hL hP P hη, hR P η hη] with s hd hr
  filter_upwards [hd.filter_mono ultra_le, hr,
    (eventually_cMono_mem (NeZero.ne N) (CRen N z μ) hUL P).filter_mono ultra_le] with k hk1 hk2 hA
  refine ⟨hk2.1, ?_⟩
  have h0 : 0 ≤ rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0)
      (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - proxB Wf cf k s P.1)
      (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1) - proxB Wf cf k s P.1) := by
    rw [rform_apply]
    exact stateK_rp (NeZero.ne N) k 0 _ (sub_mem hA hk2.1)
  have e := ExpandMatch.form_sub_split (rform (stateK (NeZero.ne N) k) (LatticeReflection.ireflObs 0 0))
    (rform_symm_k k) (prodSmear (dySpacing N k) (cMono (NeZero.ne N) (CRen N z μ) k P.1))
    (proxB Wf cf k s P.1)
  rw [abs_le]
  constructor <;> linarith [(abs_le.mp hk1).1, (abs_le.mp hk1).2, hk2.2]

/-- `RPGerm` is the mixed germ, under `ExpandLim` and `CfParity`. DERIVED: no numeral. -/
theorem rpGerm_iff_mixGerm [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ) (hP : CfParity cf) :
    ExpandMatch.RPGerm Wf cf z μ ↔ MixGerm Wf cf z μ :=
  ⟨mixGerm_of_rpGerm hL hP, rpGerm_of_mixGerm hL hP⟩

/-- `ExpandMatch` from `ExpandRF`, `CfParity` and the mixed germ. DERIVED: no numeral. -/
theorem expandMatch_of_mixGerm [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hRF : ExpandFam.ExpandRF Wf cf z μ) (hP : CfParity cf)
    (hM : MixGerm Wf cf z μ) : ExpandMatch.ExpandMatch Wf cf z μ :=
  ⟨hRF, rpGerm_of_mixGerm (ExpandFam.expandLim_of_expandRF hRF) hP hM⟩

/-! ## 3. The reflected gap read -/

/-- The smeared combination over a set of indices: `∑_{i ∈ S} cᵢ smear(msProx i, f)`. DERIVED: no
numeral. -/
def cXs [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) (S : Finset Ix0)
    (c : Ix0 →₀ ℝ) (f : TestFn) : C(Cfg N, ℝ) :=
  ∑ i ∈ S, c i • smear (dySpacing N k) (msProx Wf cf k s i) f

/-- The smeared combination `cX c f = ∑ᵢ cᵢ smear(msProx i, f)`. DERIVED: no numeral. -/
abbrev cX [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (c : Ix0 →₀ ℝ) (f : TestFn) : C(Cfg N, ℝ) :=
  cXs Wf cf k s c.support c f

/-- The proxies' two-point read is the state of the product of the two combinations. DERIVED: `2`
the two points. -/
theorem proxRead_eq [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (c : Ix0 →₀ ℝ)
    (f h : TestFn) (k : ℕ) (s : ℝ) :
    proxRead Wf cf c f h k s = stateK (NeZero.ne N) k (cX Wf cf k s c f * cX Wf cf k s c h) := by
  unfold proxRead cX cXs
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [MassGap.DLRLimit.State.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MassGap.DLRLimit.State.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, MassGap.DLRLimit.State.map_smul]
  unfold msLat
  rw [Fin.prod_univ_two]
  rfl

/-- Translation of the smeared combination by `n` lattice steps is its smearing against the test
function translated by `a n`. DERIVED: no numeral. -/
theorem transObs_cXs [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (n : ISite) (S : Finset Ix0) (c : Ix0 →₀ ℝ) (g : TestFn) :
    transObs n (cXs Wf cf k s S c g) = cXs Wf cf k s S c (g.translate (site (dySpacing N k) n)) := by
  unfold cXs
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smear_translate (dySpacing_pos (one_le_of_ne_zero (NeZero.ne N)) k)]

/-- A set of indices of one reflection sign `σ`. DERIVED: `0` the plane; `−1` the sign. -/
def PureOn (S : Finset Ix0) (σ : ℝ) : Prop := ∀ i ∈ S, (-1 : ℝ) ^ ctau 0 i.1 = σ

/-- The smeared combination over one sign is reflection covariant. DERIVED: `0` the plane. -/
theorem refl_cXs [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hP : CfParity cf)
    (k : ℕ) (s : ℝ) {S : Finset Ix0} {σ : ℝ} (hS : PureOn S σ) (c : Ix0 →₀ ℝ) (g : TestFn) :
    LatticeReflection.ireflObs 0 0 (cXs Wf cf k s S c g) = σ • cXs Wf cf k s S c (g.reflect 0) := by
  unfold cXs
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, smear_msProx_refl hP, hS i hi, smul_comm]

/-- The even indices of `c`. DERIVED: `2` the parity modulus; `0` the even residue. -/
def evenS (c : Ix0 →₀ ℝ) : Finset Ix0 := c.support.filter fun i => ctau 0 i.1 % 2 = 0

/-- The odd indices of `c`. DERIVED: `2` the parity modulus; `0` the even residue. -/
def oddS (c : Ix0 →₀ ℝ) : Finset Ix0 := c.support.filter fun i => ¬ ctau 0 i.1 % 2 = 0

/-- DERIVED: `1` the sign. -/
theorem pure_even (c : Ix0 →₀ ℝ) : PureOn (evenS c) 1 := by
  intro i hi
  rw [evenS, Finset.mem_filter] at hi
  rw [neg_one_pow_eq_pow_mod_two, hi.2, pow_zero]

/-- DERIVED: `−1` the sign. -/
theorem pure_odd (c : Ix0 →₀ ℝ) : PureOn (oddS c) (-1) := by
  intro i hi
  rw [oddS, Finset.mem_filter] at hi
  rw [neg_one_pow_eq_pow_mod_two, (Nat.mod_two_eq_zero_or_one _).resolve_left hi.2, pow_one]

/-- The combination is the sum of its even and odd parts. DERIVED: no numeral. -/
theorem cX_split [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ)
    (c : Ix0 →₀ ℝ) (f : TestFn) :
    cX Wf cf k s c f = cXs Wf cf k s (evenS c) c f + cXs Wf cf k s (oddS c) c f :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The reflected-translate read splits into the gap reads of the even and the odd part: module
docstring, §3. DERIVED: `0` the plane; `2` the two steps of one gap. -/
theorem proxRead_refl_split [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hP : CfParity cf) (c : Ix0 →₀ ℝ) (g : TestFn) (k : ℕ) (s : ℝ) (m : ℕ) :
    proxRead Wf cf c (g.reflect 0) (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s
      = ApertureThing.gK k (cXs Wf cf k s (evenS c) c g) m
        - ApertureThing.gK k (cXs Wf cf k s (oddS c) c g) m := by
  set Ye := cXs Wf cf k s (evenS c) c g with hYe
  set Yo := cXs Wf cf k s (oddS c) c g with hYo
  have he : cXs Wf cf k s (evenS c) c (g.reflect 0) = LatticeReflection.ireflObs 0 0 Ye := by
    rw [hYe, refl_cXs hP k s (pure_even c), one_smul]
  have ho : cXs Wf cf k s (oddS c) c (g.reflect 0) = -LatticeReflection.ireflObs 0 0 Yo := by
    rw [hYo, refl_cXs hP k s (pure_odd c), neg_one_smul, neg_neg]
  rw [proxRead_eq, cX_split, cX_split, ← transObs_cXs, ← transObs_cXs, he, ho]
  have e1 : LatticeReflection.ireflObs 0 0 Ye + -LatticeReflection.ireflObs 0 0 Yo
      = LatticeReflection.ireflObs 0 0 (Ye - Yo) := by
    rw [map_sub, sub_eq_add_neg]
  have e2 : transObs ((2 * m) • ApertureThing.eT) Ye + transObs ((2 * m) • ApertureThing.eT) Yo
      = (ApertureThing.tStep ^ (2 * m)) (Ye + Yo) := by
    rw [ApertureThing.tStep_pow, map_add]
  rw [e1, e2]
  have hg : ∀ X : C(Cfg N, ℝ),
      ApertureThing.gK k X m = ApertureThing.bK k X ((ApertureThing.tStep ^ (2 * m)) X) := fun X => by
    rw [ApertureThing.tStep_pow]
    rfl
  have hcross : ApertureThing.bK k Yo ((ApertureThing.tStep ^ (2 * m)) Ye)
      = ApertureThing.bK k Ye ((ApertureThing.tStep ^ (2 * m)) Yo) :=
    (ApertureThing.shift_pow (ApertureThing.reflShiftK k) Yo Ye (2 * m)).symm.trans
      ((ApertureThing.reflShiftK k).symm _ _)
  show ApertureThing.bK k (Ye - Yo) ((ApertureThing.tStep ^ (2 * m)) (Ye + Yo)) = _
  rw [hg Ye, hg Yo]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  rw [hcross]
  ring

/-- A combination of one reflection sign. DERIVED: `2` the parity modulus; `0` the even residue. -/
def PureC (c : Ix0 →₀ ℝ) : Prop :=
  (∀ i ∈ c.support, ctau 0 i.1 % 2 = 0) ∨ (∀ i ∈ c.support, ¬ ctau 0 i.1 % 2 = 0)

/-- The reflected gap read of a half-space observable is non-negative. DERIVED: `0` the sign. -/
theorem gK_nonneg [NeZero N] (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) (m : ℕ) :
    0 ≤ ApertureThing.gK k X m := by
  have h := ApertureThing.gapRead_nonneg (ApertureThing.reflShiftK k) hX m
  rwa [ApertureThing.gapRead_eq_K] at h

/-- The gap read of the zero observable is `0`. DERIVED: `0` the observable. -/
theorem gK_zero [NeZero N] (k m : ℕ) : ApertureThing.gK k (0 : C(Cfg N, ℝ)) m = 0 := by
  unfold ApertureThing.gK
  rw [map_zero, map_zero, zero_mul, MassGap.DLRLimit.State.map_zero]

/-- For a combination of one reflection sign the reflected-translate read is the gap read, up to
sign. DERIVED: `0` the plane; `2` the two steps of one gap. -/
theorem abs_proxRead_pure [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (hP : CfParity cf) {c : Ix0 →₀ ℝ} (hc : PureC c) (g : TestFn) (k : ℕ) (s : ℝ)
    (hX : cX Wf cf k s c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) (m : ℕ) :
    |proxRead Wf cf c (g.reflect 0) (g.translate (site (dySpacing N k) ((2 * m) • ApertureThing.eT))) k s|
      = ApertureThing.gK k (cX Wf cf k s c g) m := by
  rw [proxRead_refl_split hP]
  rcases hc with h | h
  · have hE : evenS c = c.support := Finset.filter_true_of_mem h
    have hO : oddS c = ∅ := Finset.filter_false_of_mem fun i hi hn => hn (h i hi)
    rw [hE, hO, show cXs Wf cf k s ∅ c g = 0 from Finset.sum_empty, gK_zero, sub_zero,
      abs_of_nonneg (gK_nonneg k hX m)]
  · have hE : evenS c = ∅ := Finset.filter_false_of_mem fun i hi hn => h i hi hn
    have hO : oddS c = c.support := Finset.filter_true_of_mem h
    rw [hE, hO, show cXs Wf cf k s ∅ c g = 0 from Finset.sum_empty, gK_zero, zero_sub, abs_neg,
      abs_of_nonneg (gK_nonneg k hX m)]

/-- The floor from two reads: `δ ≤ g₁`, `0 < g₀ ≤ U`, `1 ≤ p` and `g₀ (g₁/g₀)^p ≤ g_m` give
`U · min(δ/U, 1)^p ≤ g_m`. DERIVED: `1` the cap and the least exponent; `0` the signs. -/
theorem floor_of_reads {g0 g1 gm U δ p : ℝ} (hg0 : 0 < g0) (hU : g0 ≤ U) (hδ : 0 < δ) (h1 : δ ≤ g1)
    (hp : 1 ≤ p) (hfar : g0 * (g1 / g0) ^ p ≤ gm) : U * min (δ / U) 1 ^ p ≤ gm := by
  have hU0 : 0 < U := lt_of_lt_of_le hg0 hU
  set q := min (δ / U) 1 with hqdef
  have hq0 : 0 < q := lt_min (div_pos hδ hU0) one_pos
  have hqle : q ≤ δ / U := min_le_left _ _
  have hx1 : 1 ≤ U / g0 := (one_le_div hg0).mpr hU
  have hb : q * (U / g0) ≤ g1 / g0 := by
    calc q * (U / g0) ≤ δ / U * (U / g0) := mul_le_mul_of_nonneg_right hqle (by positivity)
      _ = δ / g0 := by rw [div_mul_div_comm, mul_comm δ U, mul_div_mul_left _ _ hU0.ne']
      _ ≤ g1 / g0 := by gcongr
  have h2 : (q * (U / g0)) ^ p ≤ (g1 / g0) ^ p := Real.rpow_le_rpow (by positivity) hb (by linarith)
  have h3 : (q * (U / g0)) ^ p = q ^ p * (U / g0) ^ p := Real.mul_rpow hq0.le (by positivity)
  have h4 : U / g0 ≤ (U / g0) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hp
  have hqp : 0 ≤ q ^ p := Real.rpow_nonneg hq0.le p
  have e : g0 * (U / g0) = U := by rw [mul_comm]; exact div_mul_cancel₀ U hg0.ne'
  calc U * q ^ p = g0 * (q ^ p * (U / g0)) := by rw [mul_left_comm, e, mul_comm]
    _ ≤ g0 * (q ^ p * (U / g0) ^ p) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hqp) hg0.le
    _ = g0 * (q * (U / g0)) ^ p := by rw [h3]
    _ ≤ g0 * (g1 / g0) ^ p := mul_le_mul_of_nonneg_left h2 hg0.le
    _ ≤ gm := hfar

/-- The far floor of the reflected gap read: `δ ≤ gK(m₁)`, `gK(0) ≤ U`, `1 ≤ m₁ ≤ m` give
`U · min(δ/U, 1)^{m/m₁} ≤ gK(m)`. DERIVED: `0` the contact gap; `1` the least inner gap and the cap. -/
theorem gK_far_floor [NeZero N] (k : ℕ) {X : C(Cfg N, ℝ)}
    (hX : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0) {m₁ m : ℕ} (hm₁ : 1 ≤ m₁)
    (hm : m₁ ≤ m) {U δ : ℝ} (hδ : 0 < δ) (h1 : δ ≤ ApertureThing.gK k X m₁)
    (hU : ApertureThing.gK k X 0 ≤ U) :
    U * min (δ / U) 1 ^ ((m : ℝ) / m₁) ≤ ApertureThing.gK k X m := by
  have hn : ∀ n, 0 ≤ ApertureThing.gK k X n := gK_nonneg k hX
  have hL : ApertureThing.LogConvexSeq (ApertureThing.gK k X) := by
    intro n
    have h := ApertureThing.gapRead_logConvex (ApertureThing.reflShiftK k) hX n
    simp only [ApertureThing.gapRead_eq_K] at h
    exact h
  have hpos := ApertureThing.pos_of_logConvex hn hL hm₁ (lt_of_lt_of_le hδ h1)
  have hp : (1 : ℝ) ≤ (m : ℝ) / m₁ :=
    (one_le_div (Nat.cast_pos.mpr hm₁)).mpr (by exact_mod_cast hm)
  exact floor_of_reads (hpos 0) hU hδ h1 hp (ApertureThing.far_ge_rpow hn hL hm₁ hm)

/-- `2m` time steps at spacing `a` is the physical time vector `2 m a`. DERIVED: `0` the time axis;
`2` the two steps of one gap. -/
theorem site_gap (a : ℝ) (m : ℕ) :
    site a ((2 * m) • ApertureThing.eT) = Pi.single 0 (2 * (m : ℝ) * a) := by
  funext i
  fin_cases i <;> simp [site, ApertureThing.eT]
  ring

/-- Translating by the zero time vector. DERIVED: `0` the zero vector. -/
theorem translate_single_zero (g : TestFn) : g.translate (Pi.single 0 0) = g := by
  apply Subtype.ext
  funext y
  show g.1 (y - Pi.single 0 0) = g.1 y
  rw [Pi.single_zero, sub_zero]

/-- The far floor along a filter of steps, in physical gaps: module docstring, §3. DERIVED: `0`
the plane and the contact gap; `1` the least inner gap and the cap; `2` the two steps of one gap. -/
theorem proxRead_far [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} (hP : CfParity cf)
    {c : Ix0 →₀ ℝ} (hc : PureC c) (g : TestFn) (s : ℝ) {l : Filter ℕ} {t₁ t δ U : ℝ} (hδ : 0 < δ)
    (m₁ m : ℕ → ℕ)
    (h : ∀ᶠ k in l, cX Wf cf k s c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ 1 ≤ m₁ k ∧ m₁ k ≤ m k
      ∧ 2 * (m₁ k : ℝ) * dySpacing N k = t₁ ∧ 2 * (m k : ℝ) * dySpacing N k = t
      ∧ δ ≤ |proxRead Wf cf c (g.reflect 0) (g.translate (Pi.single 0 t₁)) k s|
      ∧ |proxRead Wf cf c (g.reflect 0) g k s| ≤ U) :
    ∀ᶠ k in l, U * min (δ / U) 1 ^ (t / t₁)
      ≤ |proxRead Wf cf c (g.reflect 0) (g.translate (Pi.single 0 t)) k s| := by
  filter_upwards [h] with k ⟨hX, h1, h2, ht₁, ht, hd, hu⟩
  have hr := abs_proxRead_pure hP hc g k s hX
  have ha := dySpacing_pos (one_le_of_ne_zero (NeZero.ne N)) k
  have e₁ : g.translate (Pi.single 0 t₁)
      = g.translate (site (dySpacing N k) ((2 * m₁ k) • ApertureThing.eT)) := by
    rw [site_gap, ht₁]
  have e : g.translate (Pi.single 0 t)
      = g.translate (site (dySpacing N k) ((2 * m k) • ApertureThing.eT)) := by
    rw [site_gap, ht]
  have e₀ : g = g.translate (site (dySpacing N k) ((2 * 0) • ApertureThing.eT)) := by
    rw [site_gap]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    rw [translate_single_zero]
  rw [e₁, hr] at hd
  have hu' : |proxRead Wf cf c (g.reflect 0)
      (g.translate (site (dySpacing N k) ((2 * 0) • ApertureThing.eT))) k s| ≤ U := by
    rw [← e₀]
    exact hu
  rw [hr] at hu'
  rw [e, hr]
  have hratio : t / t₁ = (m k : ℝ) / m₁ k := by
    rw [← ht, ← ht₁, show 2 * (m k : ℝ) * dySpacing N k = (m k : ℝ) * (2 * dySpacing N k) by ring,
      show 2 * (m₁ k : ℝ) * dySpacing N k = (m₁ k : ℝ) * (2 * dySpacing N k) by ring,
      mul_div_mul_right _ _ (by positivity)]
  rw [hratio]
  exact gK_far_floor k hX h1 h2 hδ hd hu'

/-- The reflected and the translated test function are separated: for `g` vanishing below the time
`d ≥ 0`, `θg` and `T_t g`, `t ≥ 0`, are `2d`-separated. DERIVED: `0` the time axis and the sign of `t`; `2`
the two margins. -/
theorem sep_refl_translate {g : TestFn} {d : ℝ} (hd : 0 ≤ d) (hg : ∀ y, g.1 y ≠ 0 → d ≤ y 0) {t : ℝ}
    (ht : 0 ≤ t) :
    ContinuumSep.sepBy (2 * d) (g.reflect 0) (g.translate (Pi.single 0 t)) := by
  intro y w hy hw
  refine ⟨0, ?_⟩
  have h1 : d ≤ reflR 0 y 0 := hg _ hy
  have h2 : d ≤ (w - Pi.single 0 t : Fin 4 → ℝ) 0 := hg _ hw
  simp only [reflR, Function.update_self] at h1
  simp only [Pi.sub_apply, Pi.single_eq_same] at h2
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- A positive-time continuous test function: continuous and vanishing below some time `d > 0`.
DERIVED: `0` the time axis and the sign of the margin. -/
def PosT (g : TestFn) : Prop := Continuous g.1 ∧ ∃ d : ℝ, 0 < d ∧ ∀ y, g.1 y ≠ 0 → d ≤ y 0

/-- DERIVED: `0` the time axis. -/
theorem continuous_reflect0 {g : TestFn} (hg : Continuous g.1) : Continuous (g.reflect 0).1 :=
  hg.comp (continuous_id.update 0 (continuous_apply 0).neg)

/-- DERIVED: no numeral. -/
theorem continuous_translate {g : TestFn} (hg : Continuous g.1) (v : Fin 4 → ℝ) :
    Continuous (g.translate v).1 :=
  hg.comp (continuous_id.sub continuous_const)

/-- The contact read is bounded by the composites' contact read: under `ExpandLim` and `ConvC`, for
every `η > 0`, for all small `s`, eventually along `ultra`, `|proxRead c (θg) g| ≤ |contRead c (θg) g| + η`.
DERIVED: `2` the halving and the separation `2d`; `0` the contact gap. -/
theorem contact_bound [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (c : Ix0 →₀ ℝ) {g : TestFn} (hg : PosT g) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      |proxRead Wf cf c (g.reflect 0) g k s| ≤ |contRead (N := N) z μ c (g.reflect 0) g| + η := by
  obtain ⟨hgc, d, hd, hgd⟩ := hg
  have hsep : ContinuumSep.sepBy (2 * d) (g.reflect 0) g := by
    have h := sep_refl_translate hd.le hgd (le_refl (0 : ℝ))
    rwa [translate_single_zero] at h
  have hT := tendsto_latRead hC c (continuous_reflect0 hgc) hgc (by positivity) hsep
  filter_upwards [ExpandFam.latRead_sub_proxRead_small hL c (continuous_reflect0 hgc) hgc
    (by positivity) hsep (half_pos hη)] with s hs
  filter_upwards [(Metric.tendsto_nhds.mp hT) (η / 2) (half_pos hη), hs.filter_mono ultra_le]
    with k hk1 hk2
  rw [Real.dist_eq] at hk1
  have t1 := abs_sub_abs_le_abs_sub (proxRead Wf cf c (g.reflect 0) g k s)
    (latRead (N := N) z μ c (g.reflect 0) g k)
  have t2 := abs_sub_abs_le_abs_sub (latRead (N := N) z μ c (g.reflect 0) g k)
    (contRead (N := N) z μ c (g.reflect 0) g)
  rw [abs_sub_comm] at t1
  linarith

/-- Non-degeneracy of the reflected-translate read at the gap `t`: some `δ > 0` with, for scales
arbitrarily close to `0`, eventually along `ultra`, `δ ≤ |proxRead c (θg) (T_t g)|`. DERIVED: `0` the time
axis, the plane and the limit of the scale. -/
def GapRead [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (c : Ix0 →₀ ℝ) (g : TestFn)
    (t : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
    δ ≤ |proxRead Wf cf c (g.reflect 0) (g.translate (Pi.single 0 t)) k s|

/-- Non-degeneracy at one physical gap propagates to every larger resolved gap: module docstring, §3.
DERIVED: `0` the plane and the contact gap; `1` the least inner gap and the cap; `2` the two steps of one
gap. -/
theorem gapRead_far [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)} {z : Chan → ℕ → ℝ}
    {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ) (hC : ConvC (NeZero.ne N) (CRen N z μ))
    (hP : CfParity cf) {c : Ix0 →₀ ℝ} (hc : PureC c) {g : TestFn} (hg : PosT g) {t₁ t : ℝ}
    (m₁ m : ℕ → ℕ)
    (hrep : ∀ᶠ k in atTop, 1 ≤ m₁ k ∧ m₁ k ≤ m k
      ∧ 2 * (m₁ k : ℝ) * dySpacing N k = t₁ ∧ 2 * (m k : ℝ) * dySpacing N k = t)
    {δ : ℝ} (hδ : 0 < δ)
    (h1 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      cX Wf cf k s c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ δ ≤ |proxRead Wf cf c (g.reflect 0) (g.translate (Pi.single 0 t₁)) k s|) :
    ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      (|contRead (N := N) z μ c (g.reflect 0) g| + δ)
          * min (δ / (|contRead (N := N) z μ c (g.reflect 0) g| + δ)) 1 ^ (t / t₁)
        ≤ |proxRead Wf cf c (g.reflect 0) (g.translate (Pi.single 0 t)) k s| := by
  refine (h1.and_eventually (contact_bound hL hC c hg hδ)).mono fun s ⟨hs1, hs2⟩ => ?_
  exact proxRead_far hP hc g s hδ m₁ m
    ((hs1.and (hs2.and (hrep.filter_mono ultra_le))).mono fun k ⟨⟨hX, hd⟩, hu, r1, r2, r3, r4⟩ =>
      ⟨hX, r1, r2, r3, r4, hd, hu⟩)

/-- The depth of a smeared combination: a step-independent `D` with `cX c g` in the half-space algebra
whenever `(Wf s).V k` has reach `R`, `g` vanishes below the time `d` and `a_k (D + R) ≤ d`
(`ConstFlowN.exists_depth_msProx`, `ContinuumField.smear_mem_halfSpaceAlg`). DERIVED: `0` the plane. -/
theorem exists_depth_cX [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ)
    (c : Ix0 →₀ ℝ) : ∃ D : ℕ, ∀ k R : ℕ, ConstFlowN.ReachLE ((Wf s).V k) R → ∀ (g : TestFn) (d : ℝ),
      (∀ y, g.1 y ≠ 0 → d ≤ y 0) → dySpacing N k * ((D + R : ℕ) : ℝ) ≤ d →
        cX Wf cf k s c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  classical
  choose D hD using fun i : Ix0 => ConstFlowN.exists_depth_msProx Wf cf s i
  refine ⟨c.support.sup D, fun k R hV g d hg hk => ?_⟩
  unfold cX cXs
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  obtain ⟨S, hS, hSD⟩ := hD i k R hV
  have ha := dySpacing_pos (one_le_of_ne_zero (NeZero.ne N)) k
  have hle : D i ≤ c.support.sup D := Finset.le_sup hi
  refine smear_mem_halfSpaceAlg ha 0 hS hSD ?_ g hg
  calc dySpacing N k * ((D i + R : ℕ) : ℝ)
      ≤ dySpacing N k * ((c.support.sup D + R : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ ha.le
        exact_mod_cast Nat.add_le_add_right hle R
    _ ≤ d := hk

/-- The half-space membership of `gapRead_far` from the flow's physical range: if `g` vanishes below
the time `d` and the flow at scale `s` has physical range eventually at most `r < d`, then `cX c g` is
eventually in the half-space algebra. DERIVED: `0` the plane and the limit of `a_k D`. -/
theorem eventually_cX_mem [NeZero N] (Wf : ℝ → ConfFlow N) (cf : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ)
    (c : Ix0 →₀ ℝ) {g : TestFn} {d r : ℝ} (hg : ∀ y, g.1 y ≠ 0 → d ≤ y 0) (hrd : r < d)
    (hR : ∀ᶠ k in atTop, dySpacing N k * ((Wf s).range k : ℝ) ≤ r) :
    ∀ᶠ k in atTop, cX Wf cf k s c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  obtain ⟨D, hD⟩ := exists_depth_cX Wf cf s c
  have ht : Tendsto (fun k => dySpacing N k * (D : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_dySpacing N).mul_const (D : ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hrd)), hR] with k hk hkr
  refine hD k _ (ConstFlowN.reachLE_range (Wf s) k) g d hg ?_
  have e : ((D + (Wf s).range k : ℕ) : ℝ) = (D : ℝ) + ((Wf s).range k : ℝ) := Nat.cast_add _ _
  rw [e, mul_add]
  linarith

/-- `gapRead_far` with the half-space membership discharged by the flow's physical range: for all
small `s` the flow at `s` has physical range eventually below the margin `d` of `g`. DERIVED: `0` the
plane and the contact gap; `1` the least inner gap and the cap; `2` the two steps of one gap. -/
theorem gapRead_far_of_range [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ)
    (hC : ConvC (NeZero.ne N) (CRen N z μ)) (hP : CfParity cf) {c : Ix0 →₀ ℝ} (hc : PureC c)
    {g : TestFn} (hg : PosT g) {d : ℝ} (hgd : ∀ y, g.1 y ≠ 0 → d ≤ y 0)
    (hR : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ r, r < d ∧ ∀ᶠ k in atTop, dySpacing N k * ((Wf s).range k : ℝ) ≤ r)
    {t₁ t : ℝ} (m₁ m : ℕ → ℕ)
    (hrep : ∀ᶠ k in atTop, 1 ≤ m₁ k ∧ m₁ k ≤ m k
      ∧ 2 * (m₁ k : ℝ) * dySpacing N k = t₁ ∧ 2 * (m k : ℝ) * dySpacing N k = t)
    {δ : ℝ} (hδ : 0 < δ)
    (h1 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      δ ≤ |proxRead Wf cf c (g.reflect 0) (g.translate (Pi.single 0 t₁)) k s|) :
    ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      (|contRead (N := N) z μ c (g.reflect 0) g| + δ)
          * min (δ / (|contRead (N := N) z μ c (g.reflect 0) g| + δ)) 1 ^ (t / t₁)
        ≤ |proxRead Wf cf c (g.reflect 0) (g.translate (Pi.single 0 t)) k s| :=
  gapRead_far hL hC hP hc hg m₁ m hrep hδ ((h1.and_eventually hR).mono fun s ⟨hs, r, hr, hk⟩ =>
    ((eventually_cX_mem Wf cf s c hgd hr hk).filter_mono ultra_le).and hs)

/-- The floor of `gapRead_far` is positive. DERIVED: `0` the sign; `1` the cap. -/
theorem far_floor_pos {C δ p : ℝ} (hδ : 0 < δ) :
    0 < (|C| + δ) * min (δ / (|C| + δ)) 1 ^ p := by
  have h0 : 0 < |C| + δ := by positivity
  exact mul_pos h0 (Real.rpow_pos_of_pos (lt_min (div_pos hδ h0) one_pos) p)

/-- Every dyadic gap is resolved from its step on: `t = j a₀ / 2^{k₀}` is `2 m a_k` with
`m = j 2^{k − k₀}` at every `k ≥ k₀`. DERIVED: `2` the dyadic base and the two steps of one gap; `1` the
coupling of `aRun N 1`. -/
theorem dyadic_gap (j k₀ k : ℕ) (hk : k₀ ≤ k) :
    2 * ((j * 2 ^ (k - k₀) : ℕ) : ℝ) * dySpacing N k = j * AsymptoticScaling.aRun N 1 / 2 ^ k₀ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  unfold dySpacing
  push_cast
  rw [pow_succ, pow_add]
  field_simp

/-- The representation hypothesis at two dyadic gaps `t₁ = j₁ a₀ / 2^{k₀} ≤ t = j a₀ / 2^{k₀}`,
`1 ≤ j₁`. DERIVED: `1` the least numerator; `2` the dyadic base. -/
theorem rep_dyadic {j₁ j k₀ : ℕ} (h1 : 1 ≤ j₁) (h2 : j₁ ≤ j) :
    ∀ᶠ k in atTop, 1 ≤ j₁ * 2 ^ (k - k₀) ∧ j₁ * 2 ^ (k - k₀) ≤ j * 2 ^ (k - k₀)
      ∧ 2 * ((j₁ * 2 ^ (k - k₀) : ℕ) : ℝ) * dySpacing N k = j₁ * AsymptoticScaling.aRun N 1 / 2 ^ k₀
      ∧ 2 * ((j * 2 ^ (k - k₀) : ℕ) : ℝ) * dySpacing N k = j * AsymptoticScaling.aRun N 1 / 2 ^ k₀ := by
  filter_upwards [eventually_ge_atTop k₀] with k hk
  exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity)),
    Nat.mul_le_mul_right _ h2, dyadic_gap j₁ k₀ k hk, dyadic_gap j k₀ k hk⟩

/-- `gapRead_far` at dyadic gaps: the representation is met, the floor is positive, so `GapRead` at
`t₁` (with the half-space membership) gives `GapRead` at every larger dyadic gap. DERIVED: `0` the plane;
`1` the least numerator; `2` the dyadic base. -/
theorem gapRead_far_dyadic [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {z : Chan → ℕ → ℝ} {μ : OffMix} (hL : ExpandFam.ExpandLim Wf cf z μ)
    (hC : ConvC (NeZero.ne N) (CRen N z μ)) (hP : CfParity cf) {c : Ix0 →₀ ℝ} (hc : PureC c)
    {g : TestFn} (hg : PosT g) {j₁ j k₀ : ℕ} (hj₁ : 1 ≤ j₁) (hj : j₁ ≤ j) {δ : ℝ} (hδ : 0 < δ)
    (h1 : ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
      cX Wf cf k s c g ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0
      ∧ δ ≤ |proxRead Wf cf c (g.reflect 0)
          (g.translate (Pi.single 0 (j₁ * AsymptoticScaling.aRun N 1 / 2 ^ k₀))) k s|) :
    GapRead Wf cf c g (j * AsymptoticScaling.aRun N 1 / 2 ^ k₀) :=
  ⟨_, far_floor_pos (C := contRead (N := N) z μ c (g.reflect 0) g) hδ,
    gapRead_far hL hC hP hc hg (fun k => j₁ * 2 ^ (k - k₀)) (fun k => j * 2 ^ (k - k₀))
      (rep_dyadic hj₁ hj) hδ h1⟩

/-- `ProxyNondeg`'s clause of `c` from one reflected-translate read. DERIVED: `2` the two margins;
`0` the sign of the gap. -/
theorem proxyNondeg_clause_of_gapRead [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    {c : Ix0 →₀ ℝ} {g : TestFn} (hg : PosT g) {t : ℝ} (ht : 0 ≤ t) (h : GapRead Wf cf c g t) :
    ∃ f h' : TestFn, Continuous f.1 ∧ Continuous h'.1 ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h')
      ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ k in (ultra : Filter ℕ),
          δ ≤ |proxRead Wf cf c f h' k s| := by
  obtain ⟨hgc, d, hd, hgd⟩ := hg
  exact ⟨g.reflect 0, g.translate (Pi.single 0 t), continuous_reflect0 hgc,
    continuous_translate hgc _, ⟨2 * d, by positivity, sep_refl_translate hd.le hgd ht⟩, h⟩

/-- `ProxyNondeg` from one reflected-translate read per combination. DERIVED: `0` the sign of the
gap. -/
theorem proxyNondeg_of_gapRead [NeZero N] {Wf : ℝ → ConfFlow N} {cf : Ix0 → ℝ → (MIx →₀ ℝ)}
    (h : ∀ c : Ix0 →₀ ℝ, OnShellTopN N c → ∃ (g : TestFn) (t : ℝ), PosT g ∧ 0 ≤ t ∧ GapRead Wf cf c g t) :
    ProxyNondeg Wf cf := fun c hc => by
  obtain ⟨g, t, hg, ht, hr⟩ := h c hc
  exact proxyNondeg_clause_of_gapRead hg ht hr

/-! ## 4. The load-bearing tests -/

/-- The time reflection `diag(1, −1)` of an even and an electric channel. DERIVED: `−1` the electric
sign. -/
def thetaE : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x.1, -x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, neg_add]
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Prod.smul_mk, mul_neg]

/-- One reflection sign is load-bearing: module docstring, §4. DERIVED: `0`, `1` the coordinates;
`2` the direct read of `(1, 1)`; `−1` the electric sign. -/
theorem parity_load_bearing :
    thetaE ((1 : ℝ), (0 : ℝ)) = ((1 : ℝ), (0 : ℝ)) ∧ thetaE ((0 : ℝ), (1 : ℝ)) = -((0 : ℝ), (1 : ℝ))
      ∧ (∀ x : ℝ × ℝ, (thetaE x = x ∨ thetaE x = -x)
          → |ExpandMatch.dotF (thetaE x) x| = ExpandMatch.dotF x x)
      ∧ ExpandMatch.dotF (thetaE ((1 : ℝ), (1 : ℝ))) ((1 : ℝ), (1 : ℝ)) = 0
      ∧ ExpandMatch.dotF ((1 : ℝ), (1 : ℝ)) ((1 : ℝ), (1 : ℝ)) = 2 := by
  have hpos : ∀ x : ℝ × ℝ, 0 ≤ ExpandMatch.dotF x x := fun x => by
    simp only [ExpandMatch.dotF, LinearMap.mk₂_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  refine ⟨?_, ?_, fun x hx => ?_, ?_, ?_⟩
  · show ((1 : ℝ), -(0 : ℝ)) = _
    rw [neg_zero]
  · show ((0 : ℝ), -(1 : ℝ)) = _
    rw [Prod.neg_mk, neg_zero]
  · rcases hx with h | h
    · rw [h, abs_of_nonneg (hpos x)]
    · rw [h, map_neg, LinearMap.neg_apply, abs_neg, abs_of_nonneg (hpos x)]
  · show ExpandMatch.dotF ((1 : ℝ), -(1 : ℝ)) ((1 : ℝ), (1 : ℝ)) = 0
    simp only [ExpandMatch.dotF, LinearMap.mk₂_apply]
    norm_num
  · simp only [ExpandMatch.dotF, LinearMap.mk₂_apply]
    norm_num

/-- `(c · id)ᵐ v = cᵐ v` on `ℝ`. DERIVED: `1` the step. -/
theorem cS_pow (c : ℝ) (m : ℕ) (v : ℝ) : (ApertureThing.cS c ^ m) v = c ^ m * v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ApertureThing.pow_succ_apply, ih]
    simp only [ApertureThing.cS, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, pow_succ]
    ring

/-- For a mixed combination one gap does not fix the next: module docstring, §4. DERIVED: `1/2`, `4`,
`1` the two scales and amplitudes; `1`, `2` the gaps; `3` the difference at gap `1`. -/
theorem mixed_no_propagate :
    ApertureThing.ReflShift ApertureThing.mB ⊤ (ApertureThing.cS (1 / 2))
      ∧ ApertureThing.ReflShift ApertureThing.mB ⊤ (ApertureThing.cS 1)
      ∧ ApertureThing.gapRead ApertureThing.mB (ApertureThing.cS (1 / 2)) 4 1
          - ApertureThing.gapRead ApertureThing.mB (ApertureThing.cS 1) 1 1 = 3
      ∧ ApertureThing.gapRead ApertureThing.mB (ApertureThing.cS (1 / 2)) 4 2
          - ApertureThing.gapRead ApertureThing.mB (ApertureThing.cS 1) 1 2 = 0 := by
  refine ⟨(ApertureThing.geom_sharp (1 / 2) (by norm_num)).1,
    (ApertureThing.geom_sharp 1 one_ne_zero).1, ?_, ?_⟩
  · simp only [ApertureThing.gapRead, cS_pow, ApertureThing.mB_apply]
    norm_num
  · simp only [ApertureThing.gapRead, cS_pow, ApertureThing.mB_apply]
    norm_num

end MassGap.ProxyCov

end

#print axioms MassGap.ProxyCov.mField_refl
#print axioms MassGap.ProxyCov.fieldMap_mField_refl
#print axioms MassGap.ProxyCov.msFlow_refl
#print axioms MassGap.ProxyCov.msProx_refl
#print axioms MassGap.ProxyCov.smear_msProx_refl
#print axioms MassGap.ProxyCov.cfParity_cfScaled
#print axioms MassGap.ProxyCov.cfParity_cfLead
#print axioms MassGap.ProxyCov.electric_sign
#print axioms MassGap.ProxyCov.magnetic_sign
#print axioms MassGap.ProxyCov.not_cfParity_mix
#print axioms MassGap.ProxyCov.proxB_refl
#print axioms MassGap.ProxyCov.proxD_eq
#print axioms MassGap.ProxyCov.diag_germ
#print axioms MassGap.ProxyCov.rpGerm_of_mixGerm
#print axioms MassGap.ProxyCov.mixGerm_of_rpGerm
#print axioms MassGap.ProxyCov.rpGerm_iff_mixGerm
#print axioms MassGap.ProxyCov.expandMatch_of_mixGerm
#print axioms MassGap.ProxyCov.proxRead_eq
#print axioms MassGap.ProxyCov.transObs_cXs
#print axioms MassGap.ProxyCov.refl_cXs
#print axioms MassGap.ProxyCov.proxRead_refl_split
#print axioms MassGap.ProxyCov.abs_proxRead_pure
#print axioms MassGap.ProxyCov.floor_of_reads
#print axioms MassGap.ProxyCov.gK_far_floor
#print axioms MassGap.ProxyCov.proxRead_far
#print axioms MassGap.ProxyCov.sep_refl_translate
#print axioms MassGap.ProxyCov.contact_bound
#print axioms MassGap.ProxyCov.gapRead_far
#print axioms MassGap.ProxyCov.exists_depth_cX
#print axioms MassGap.ProxyCov.eventually_cX_mem
#print axioms MassGap.ProxyCov.gapRead_far_of_range
#print axioms MassGap.ProxyCov.dyadic_gap
#print axioms MassGap.ProxyCov.rep_dyadic
#print axioms MassGap.ProxyCov.gapRead_far_dyadic
#print axioms MassGap.ProxyCov.proxyNondeg_of_gapRead
#print axioms MassGap.ProxyCov.parity_load_bearing
#print axioms MassGap.ProxyCov.mixed_no_propagate
