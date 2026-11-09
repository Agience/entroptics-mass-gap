import Mathlib
import MassGap.MultiScale

/-!
# MassGap.MultiScaleAll — control at every intermediate scale, as one statement

`MultiScale W` states the two ends of the renormalisation-group flow (the short-distance moment `uv` at the
flow `W`, the strong-coupling `endpoint`) and the coefficient `af`. Both the substrate side and the composite
side need control at every scale `s` between the lattice spacing `a_k` and the physical scale `b`
(`FlowComposites` docstring §5). This module states that control as one `Prop`, `MultiScaleAll W`, derives
`MultiScale W` and the composite clause `BoundC` from it.

## 1. `MultiScaleAll W` (the statement)

`MultiScaleAll W` is `∃ b Wf c, MultiScaleAllAt W b Wf c`: a physical scale `b > 0`, a family of
configuration flows `Wf : ℝ → ConfFlow 2` (the flow to scale `s`) with `Wf b = W`, and expansion
coefficients `c`. The fields of `MultiScaleAllAt`:

* `scale` (`ScaleControlAll b Wf`): one `t > 0`, one `C`, log exponents `γ` (one per monomial) and `γP` (the
  plaquette class) such that, eventually in the step `k`, for **every** `s` with `a_k ≤ s ≤ b` and every index
  `j` of `MIx` (every admissible monomial `i : Ix0`, read through its bare field `bR 2 i` at dimension
  `cdim i`, and every symmetrised plaquette `sym (plaqField q)` at dimension `4`),

    `ν_k(exp((μ_j(s) / a_k^{d_j}) · |O_j ∘ V_k^{(s)}|)) ≤ C`,  `μ_j(s) = t s^{d_j} / (1 + |log s|)^{γ_j}`.

  This is the asymptotic-freedom scaling: the flowed field of dimension `d` at scale `s`, in physical units
  `a_k^{−d} O ∘ V^{(s)}`, has size `s^{−d}` times a power of `log s` (the running-coupling factor), with one
  exponential moment uniform in `β` and in `s`.
* `expand` (`Expand Wf c`): the small-flow-time expansion of the bare composites `CbR 2 zOne`. For every
  continuous, `d`-separated family `F` of composites and every `0 < s ≤ θ d`, eventually in the step,

    `|latC F − msLat(s) F| ≤ K_r^{#F} (s/d)^ε ∏ᵢ d^{−κᵢ} ‖fᵢ‖_{L¹}`,  `ε > 0`,

  where `msLat(s)` reads, in place of each composite `i`, the combination `∑_j c_{ij}(s) · a_k^{−d_j}(O_j ∘
  V_k^{(s)} − ν_k(O_j ∘ V_k^{(s)}))` of connected flowed monomials at scale `s`. The remainder vanishes as
  `s/d → 0`; nothing is asserted about the size of `latC F` itself.
* `af`, `endpoint`: as in `MultiScale` (the asymptotic-freedom kernel of the trace channel at `zOne`, the
  slice endpoint with the odd levels).

No clause is a clause of the target or the gap restated: `scale` reads one-site exponential moments of flowed
fields, `expand` the difference of two lattice readings, `endpoint` the slice transfer at the window. Neither
`scale` nor `expand` mentions distances larger than `θ d`, clustering or the gap.

## 2. What is derived (proved)

* **The scale side at every `SU(N)`.** `mField`, `ScaleAt`, `ScaleControlAll`, `msFlow`, `msProx`, `msLat` and
  the moment bounds `msFlow_moment`, `msProx_moment`, `abs_msLat_le`, `scale_const` take
  `Wf : ℝ → ConfFlow N` with `[NeZero N]`; their proofs read only `stateK`, `dySpacing N` and the index type.
  `Expand`, `MultiScaleAllAt`, `MultiScaleAll` and the theorems below that read them are at `SU(2)`.
* **`multiScale_of_all`: `MultiScaleAll W → MultiScale W`.** `uv` is `scale` at `s = b` on the plaquette
  indices (`Wf b = W`, the class is non-negative, so `|O ∘ V| = O ∘ V`), through
  `MultiScale.uvSplit_iff`; `af` and `endpoint` are copied.
* **`boundC_of_all`: `MultiScaleAll W → BoundC (CbR 2 zOne)`.** For an admissible family at separation `d`,
  take `s = min(θ d, b)`. The flowed reading is bounded uniformly in the step (`abs_msLat_le`):
  - `exp_abs_sub_le`: an exponential moment of `|G|` gives one of `|G − ν(G)|`, with constant `e^C C`;
  - `msFlow_moment`: hence `ν_k((a^{−d}(G − νG))^{2p}) ≤ (2p)! μ^{−2p} e^C C`, independent of `k`;
  - `msProx_moment`: for the finite combination, `ν_k(P^{2p}) ≤ (2p)! e^C C (|S| B + 1)^{2p}`,
    `B = ∑_j |c_j| / μ_j` (Jensen for powers, `pow_sum_le_card_mul_sum_pow`);
  - `ObserverEnergyMoments.moment_smear_le` (translation invariance of `stateK`) for the smearing, and
    `ObserverOS.abs_state_prod_le` for the product.
  `expand` adds the remainder at `s`, a constant. So `BoundC` holds, hence `ConvC`
  (`InputsTriage.convC_iff_boundC`).
* **`scale_const`**: the constant family `Wf s = W` meets `scale` whenever the moment holds at `s = b` with
  `γ = γP = 0`.
* No `ClayStatementAt` capstone is stated from `MultiScaleAll W`: its `endpoint` field, `MultiScale.Endpoint`,
  is refuted by `InputAudit.not_multiScaleEndpoint` under the argued growth of the zero-flux level count.

## 3. What is not derived, and why (argued from the definitions; no declaration)

* `OS0C` (the `d^{−κ} ‖f‖_{L¹}` form): the chain above bounds each factor by `M (2R + 3)⁴`, the sup bound of the
  test function times its box, not by `‖f‖_{L¹}`. The `L¹` form needs, at the limit, that the lattice sums
  `a⁴ ∑ₓ |f(a x)|` of a continuous compactly supported `f` converge to `∫ |f|`; that lemma is not in the tree
  (`ContinuumNontrivial.riemann_le` is the upper bound only). With it, the same chain at `s = θ d` and a
  coefficient bound `|c_{ij}(s)| ≤ K s^{d_j − d_i} (1 + |log s|)^{γ}` would give `OS0C` with `κᵢ = dᵢ + γ⁺` and
  `(2n)! ≤ 4ⁿ (n!)²`. Neither the lemma nor the coefficient bound is stated here.
* `OS1C` (continuum translation invariance): lattice translations are exact (`stateK_transObs`); the residual
  shift `|v − a n| < a` moves each test function by a uniformly small amount (continuous, compact support),
  and the telescoped difference is bounded by the same moment chain on the flowed readings plus the remainder
  of `expand` for both families. So `OS1C` should follow from `scale` and `expand` alone; not built.
* `CovC` (`O(4)` covariance): moment bounds are blind to rotations and the lattice breaks `O(4)`. It needs the
  restoration of `O(4)` in the flowed readings at each fixed `s` as `k → ∞`, and coefficients `c(s)` that
  intertwine `rep`; that is a symmetry clause on the flowed fields, not a size bound, and it is not part of
  `MultiScaleAll`. Stays a separate input.
* `CompNondeg`, `ObsLower` (non-vanishing): upper bounds do not give lower bounds. `ObsLower` is, given `comp`,
  the target clause `NonGaussianT` (`InputsTriage.nonGaussianT_rhoD_iff_lower`), so it cannot be a clause of
  `MultiScaleAll` without restating the target. Off the tensor indices the composites of `CbR 2 z` are the
  bare fields `bR 2 i` for every `z` and every step (`renF` at `dec = none`), with no renormalisation factor.
  They are dimensionless lattice operators of size `a^{4}` or smaller (mixing with `tr F²`), so their separated
  two-point functions are expected to vanish as `a → 0`, and `CompNondeg (CbR 2 z)` is expected to fail at
  every `z` on a combination supported on one such index with an on-shell classical value
  (`CompositeNondeg.not_compNondeg_of_vanish`). At `zOne` the same holds at the tensor indices with no
  `sc`/`ps` component (`z = 1` on `ri`, `we`). Not proved here (it needs the vanishing); the `comp` input of
  every capstone at `build (rhoD …) (bareD …)` is affected, not only at `zOne`.
* `WardT`: an identity of the trace channel `rhoD (fR 2) zOne` in the limit; size bounds do not give an
  identity, and `ρ` is fixed bare by `TIn` (`FlowComposites.trace_ren_eq`). Stays separate.
* `phys`, `approx`: as in `MultiScale` §4.

`Wf` is not required to have range `≈ s / a_k`. The choice `Wf s = W` for every `s` meets `scale` whenever the
moment at `s = b` holds with `γ = γP = 0` (then `μ_j(s) = t s^{d_j}` increases with `s` and the exponential
moment is monotone in its rate; `scale_const`); it is `expand`, which asks the flowed readings
to reproduce the bare ones as `s → 0` at every separation `d`, that forces `Wf s` to resolve the scale `s`
(argued).

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `2` is `SU(2)` and makes the moment powers even; `4` the dimension of the plaquette
density; `1` the floor `1 + |log s|`, the unit field, the spacing bound and the `+ 1` that keeps the
product bounds positive; `3` and `2 R` the box of `riemann_le`; `0` the signs.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.MultiScaleAll

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
  MassGap.MixConvRP
open MassGap.ScaleControlFull (zOne)

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 1. The monomials, their dimensions and the asymptotic-freedom strength -/

/-- **The indices of the scale clause**: the admissible monomials and the plaquettes. -/
abbrev MIx : Type := Ix0 ⊕ MassGap.GibbsSpec.IPlaq

/-- The field of an index: the bare field `bR N i` of a monomial, the symmetrised plaquette density. -/
def mField : MIx → LField (MassGap.SUN.SU N)
  | Sum.inl i => bR N i
  | Sum.inr q => sym (plaqField q)

/-- The canonical dimension of an index: `cdim` of the monomial, `4` for the plaquette density. -/
def mDim : MIx → ℕ
  | Sum.inl i => cdim i.1
  | Sum.inr _ => 4

/-- **The running-coupling factor** `(1 + |log s|)^γ`. -/
def afLog (γ s : ℝ) : ℝ := (1 + |Real.log s|) ^ γ

theorem afLog_pos (γ s : ℝ) : 0 < afLog γ s := Real.rpow_pos_of_pos (by positivity) γ

/-- **The strength at scale `s`**: `μ_j(s) = t s^{d_j} / (1 + |log s|)^{γ_j}`, with one exponent per monomial
and one for the plaquette class. -/
def msMu (t : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) : MIx → ℝ → ℝ
  | Sum.inl i, s => t * s ^ cdim i.1 / afLog (γ i) s
  | Sum.inr _, s => t * s ^ 4 / afLog γP s

theorem mField_inr (q : MassGap.GibbsSpec.IPlaq) :
    (mField (Sum.inr q) : LField (MassGap.SUN.SU N)) = sym (plaqField q) := rfl

theorem mDim_inr (q : MassGap.GibbsSpec.IPlaq) : mDim (Sum.inr q) = 4 := rfl

theorem msMu_inr (t : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (q : MassGap.GibbsSpec.IPlaq) (s : ℝ) :
    msMu t γ γP (Sum.inr q) s = t * s ^ 4 / afLog γP s := rfl

theorem msMu_pos {t : ℝ} (ht : 0 < t) (γ : Ix0 → ℝ) (γP : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ j : MIx, 0 < msMu t γ γP j s
  | Sum.inl _ => div_pos (mul_pos ht (pow_pos hs _)) (afLog_pos _ _)
  | Sum.inr _ => div_pos (mul_pos ht (pow_pos hs _)) (afLog_pos _ _)

/-- The pointwise absolute value of a continuous function. -/
def msAbs {X : Type*} [TopologicalSpace X] (G : C(X, ℝ)) : C(X, ℝ) :=
  (⟨abs, continuous_abs⟩ : C(ℝ, ℝ)).comp G

@[simp] theorem msAbs_apply {X : Type*} [TopologicalSpace X] (G : C(X, ℝ)) (U : X) :
    msAbs G U = |G U| := rfl

/-! ## 2. The statement -/

/-- **The scale clause at one step and one scale**: for every index `j`,
`ν_k(exp((μ_j(s) / a_k^{d_j}) · |O_j ∘ V_k^{(s)}|)) ≤ C`. -/
def ScaleAt [NeZero N] (Wf : ℝ → ConfFlow N) (t C : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (k : ℕ) (s : ℝ) : Prop :=
  ∀ j : MIx, stateK (NeZero.ne N) k
    (expC ((msMu t γ γP j s / dySpacing N k ^ mDim j) • msAbs ((Wf s).fieldMap k (mField j)).1)) ≤ C

/-- **Control at every intermediate scale**: one `t > 0`, `C`, `γ`, `γP` with, eventually in the step,
`ScaleAt` at every `s ∈ [a_k, b]`. -/
def ScaleControlAll [NeZero N] (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (t C : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < t ∧
    ∀ᶠ k in atTop, ∀ s : ℝ, dySpacing N k ≤ s → s ≤ b → ScaleAt Wf t C γ γP k s

/-- **The connected flowed monomial at scale `s`, in physical units**: `a_k^{−d_j}(O_j ∘ V_k^{(s)} − ν_k(·))`. -/
def msFlow [NeZero N] (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) : C(Cfg N, ℝ) :=
  (dySpacing N k ^ mDim j)⁻¹ • (((Wf s).fieldMap k (mField j)).1
    - stateK (NeZero.ne N) k ((Wf s).fieldMap k (mField j)).1 • (1 : C(Cfg N, ℝ)))

/-- **The flowed proxy of a composite**: `∑_j c_{ij}(s) · msFlow j`. -/
def msProx [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) (i : Ix0) :
    C(Cfg N, ℝ) :=
  ∑ j ∈ (c i s).support, c i s j • msFlow Wf k s j

/-- **The flowed reading of a family of composites**: the lattice reading with each composite replaced by
its flowed proxy at scale `s`. -/
def msLat [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (k : ℕ) (s : ℝ) {ι : Type}
    [Fintype ι] (F : ι → CDatum (CbR N zOne)) : ℝ :=
  stateK (NeZero.ne N) k (∏ i, smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)

/-- **The small-flow-time expansion of the bare composites `CbR 2 zOne`**: on every continuous `d`-separated
family, at every `0 < s ≤ θ d`, eventually in the step, the bare reading is the flowed reading up to
`K_r^{#F} (s/d)^ε ∏ᵢ d^{−κᵢ} ‖fᵢ‖_{L¹}`, `ε > 0`. -/
def Expand (Wf : ℝ → ConfFlow 2) (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop :=
  ∃ (θ ε Kr : ℝ) (κr : Ix0 → ℝ), 0 < θ ∧ 0 < ε ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum (CbR 2 zOne)) (d : ℝ), 0 < d →
      ContD F → SepD d F → ∀ s : ℝ, 0 < s → s ≤ θ * d → ∀ᶠ k in atTop,
        |latC h2N (CbR 2 zOne) k F - msLat Wf c k s F|
          ≤ Kr ^ Fintype.card ι * (s / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2)

/-- **The multi-scale statement at its data**: the physical scale `b`, the flows `Wf` with `Wf b = W`, the
expansion coefficients `c`. Module docstring, §1. -/
structure MultiScaleAllAt (W : ConfFlow 2) (b : ℝ) (Wf : ℝ → ConfFlow 2)
    (c : Ix0 → ℝ → (MIx →₀ ℝ)) : Prop where
  b_pos : 0 < b
  /-- The flow to the physical scale is `W`. -/
  top : Wf b = W
  /-- Every intermediate scale: the asymptotic-freedom moments of every monomial. -/
  scale : ScaleControlAll b Wf
  /-- The small-flow-time expansion of the bare composites. -/
  expand : Expand Wf c
  /-- Asymptotic freedom: a two-point kernel of the trace with the asymptotic-freedom coefficient. -/
  af : ∃ G : ℝ → ℝ, TwoPointKernel h2N (rhoD (fR 2) zOne) G ∧ AFCoefficient 2 G
  /-- Strong coupling at the physical scale: the slice endpoint with the odd levels. -/
  endpoint : MultiScale.Endpoint

end MassGap.MultiScaleAll

namespace MassGap

open MassGap.ContinuumFlow MassGap.CompositesBuild MultiScaleAll in
/-- **Control at every intermediate scale** (`SU(2)`, at the flow `W`). -/
def MultiScaleAll (W : ConfFlow 2) : Prop :=
  ∃ (b : ℝ) (Wf : ℝ → ConfFlow 2) (c : Ix0 → ℝ → (MIx →₀ ℝ)), MultiScaleAllAt W b Wf c

end MassGap

namespace MassGap.MultiScaleAll

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
  MassGap.MixConvRP
open MassGap.ScaleControlFull (zOne)

local notation "h2N" => (ne_zero_of_two_le (le_refl 2) : (2 : ℕ) ≠ 0)

variable {N : ℕ}

/-! ## 3. `MultiScale` from `MultiScaleAll` -/

/-- **`MultiScaleAll W` gives `MultiScale W`**: `uv` is the scale clause at `s = b` on the plaquette
indices. -/
theorem multiScale_of_all {W : ConfFlow 2} (h : MultiScaleAll W) : MultiScale W := by
  obtain ⟨b, Wf, c, H⟩ := h
  obtain ⟨t, C, γ, γP, ht, hev⟩ := H.scale
  have hb := H.b_pos
  refine ⟨?_, H.af, H.endpoint⟩
  have hpos : 0 < t * b ^ 4 / afLog γP b := div_pos (mul_pos ht (pow_pos hb 4)) (afLog_pos _ _)
  refine (MultiScale.uvSplit_iff W).2
    ⟨t * b ^ 4 / afLog γP b / (2 * 1 + 3) ^ 4, C, div_pos hpos (by norm_num), ?_⟩
  rw [div_mul_cancel₀ _ (by norm_num : ((2 : ℝ) * 1 + 3) ^ 4 ≠ 0)]
  unfold FlowUV.SiteExp
  filter_upwards [hev, (tendsto_dySpacing 2).eventually (gt_mem_nhds hb)] with k hk hkb
  rintro O ⟨q, rfl⟩
  have h1 := hk b hkb.le le_rfl (Sum.inr q)
  rw [H.top, mField_inr, mDim_inr, msMu_inr] at h1
  have e : msAbs (W.fieldMap k (sym (plaqField q))).1 = (W.fieldMap k (sym (plaqField q))).1 := by
    ext U
    have key : ∀ O ∈ SymPlaqClass 2, ∀ U, 0 ≤ (W.fieldMap k O).1 U :=
      fun O hO U => symPlaq_nonneg h2N O hO (W.V k U)
    rw [msAbs_apply]
    exact abs_of_nonneg (key _ ⟨q, rfl⟩ U)
  rw [e] at h1
  exact h1

/-! ## 4. The flowed readings are bounded uniformly in the step -/

/-- **An exponential moment of `|G|` gives one of `|G − ν(G)|`**: `ν(e^{l|G|}) ≤ C`, `l ≥ 0`, gives `1 ≤ C`
and `ν(e^{l|G − ν G|}) ≤ e^C C` (`l |ν G| ≤ ν(l|G|) ≤ ν(e^{l|G|})`). -/
theorem exp_abs_sub_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) (G : C(X, ℝ)) {l C : ℝ} (hl : 0 ≤ l)
    (h : ν (expC (l • msAbs G)) ≤ C) :
    1 ≤ C ∧ ν (expC (l • msAbs (G - ν G • (1 : C(X, ℝ))))) ≤ Real.exp C * C := by
  have hone : (1 : ℝ) ≤ ν (expC (l • msAbs G)) := by
    have h1 := ν.mono (f := (1 : C(X, ℝ))) (g := expC (l • msAbs G)) (fun U => by
      simp only [ContinuousMap.one_apply, expC_apply, ContinuousMap.smul_apply, smul_eq_mul,
        msAbs_apply]
      exact Real.one_le_exp (mul_nonneg hl (abs_nonneg _)))
    rwa [ν.map_one] at h1
  have hC : 1 ≤ C := hone.trans h
  have hm : l * |ν G| ≤ C := by
    have h1 : |ν G| ≤ ν (msAbs G) := abs_state_le_of_abs_le ν G (msAbs G) (fun U => le_rfl)
    have h2 : ν (l • msAbs G) ≤ ν (expC (l • msAbs G)) := ν.mono (fun U => by
      simp only [expC_apply, ContinuousMap.smul_apply, smul_eq_mul, msAbs_apply]
      linarith [Real.add_one_le_exp (l * |G U|)])
    rw [ν.map_smul] at h2
    calc l * |ν G| ≤ l * ν (msAbs G) := mul_le_mul_of_nonneg_left h1 hl
      _ ≤ C := h2.trans h
  have hpt : ∀ U, expC (l • msAbs (G - ν G • (1 : C(X, ℝ)))) U
      ≤ (Real.exp C • expC (l • msAbs G)) U := by
    intro U
    simp only [expC_apply, ContinuousMap.smul_apply, smul_eq_mul, msAbs_apply,
      ContinuousMap.sub_apply, ContinuousMap.one_apply, mul_one]
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h3 : l * |G U - ν G| ≤ l * |G U| + l * |ν G| := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) hl
    linarith
  refine ⟨hC, (ν.mono hpt).trans ?_⟩
  rw [ν.map_smul]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- **Even moments from an exponential moment**: `ν(e^{l|Y|}) ≤ K`, `l > 0`, gives
`ν(Y^{2p}) ≤ (2p)! / l^{2p} · K`. -/
theorem state_pow_le_of_exp {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) (Y : C(X, ℝ)) {l K : ℝ} (hl : 0 < l)
    (h : ν (expC (l • msAbs Y)) ≤ K) (p : ℕ) :
    ν (Y ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) / l ^ (2 * p) * K := by
  have hf : (0 : ℝ) < ((2 * p).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hlp : 0 < l ^ (2 * p) := pow_pos hl _
  have hpt : ∀ U, (Y ^ (2 * p)) U
      ≤ ((((2 * p).factorial : ℝ) / l ^ (2 * p)) • expC (l • msAbs Y)) U := by
    intro U
    simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul, expC_apply,
      msAbs_apply]
    have h1 := Real.pow_div_factorial_le_exp (l * |Y U|) (mul_nonneg hl.le (abs_nonneg (Y U))) (2 * p)
    rw [div_le_iff₀ hf, mul_pow] at h1
    have e : Y U ^ (2 * p) = |Y U| ^ (2 * p) := (Even.pow_abs ⟨p, by ring⟩ (Y U)).symm
    rw [e, div_mul_eq_mul_div, le_div_iff₀ hlp]
    calc |Y U| ^ (2 * p) * l ^ (2 * p) = l ^ (2 * p) * |Y U| ^ (2 * p) := mul_comm _ _
      _ ≤ Real.exp (l * |Y U|) * ((2 * p).factorial : ℝ) := h1
      _ = ((2 * p).factorial : ℝ) * Real.exp (l * |Y U|) := mul_comm _ _
  calc ν (Y ^ (2 * p))
      ≤ ν ((((2 * p).factorial : ℝ) / l ^ (2 * p)) • expC (l • msAbs Y)) := ν.mono hpt
    _ = ((2 * p).factorial : ℝ) / l ^ (2 * p) * ν (expC (l • msAbs Y)) := ν.map_smul _ _
    _ ≤ ((2 * p).factorial : ℝ) / l ^ (2 * p) * K :=
        mul_le_mul_of_nonneg_left h (div_nonneg hf.le hlp.le)

/-- **The moments of a connected flowed monomial**, uniform in the step: under `ScaleAt` at `(k, s)`,
`1 ≤ C` and `ν_k(msFlow j^{2p}) ≤ (2p)! / μ_j(s)^{2p} · e^C C`. -/
theorem msFlow_moment [NeZero N] (Wf : ℝ → ConfFlow N) {t C : ℝ} {γ : Ix0 → ℝ} {γP : ℝ} (ht : 0 < t) {k : ℕ}
    {s : ℝ} (hs : 0 < s) (hS : ScaleAt Wf t C γ γP k s) (j : MIx) (p : ℕ) :
    1 ≤ C ∧ stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) / msMu t γ γP j s ^ (2 * p) * (Real.exp C * C) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have had : 0 < dySpacing N k ^ mDim j := pow_pos ha _
  have hmu := msMu_pos ht γ γP hs j
  set G : C(Cfg N, ℝ) := ((Wf s).fieldMap k (mField j)).1 with hG
  have hl : 0 ≤ msMu t γ γP j s / dySpacing N k ^ mDim j := (div_pos hmu had).le
  obtain ⟨h1, h2⟩ := exp_abs_sub_le (stateK (NeZero.ne N) k) G hl (hS j)
  refine ⟨h1, ?_⟩
  have e : expC (msMu t γ γP j s • msAbs (msFlow Wf k s j))
      = expC ((msMu t γ γP j s / dySpacing N k ^ mDim j)
        • msAbs (G - stateK (NeZero.ne N) k G • (1 : C(Cfg N, ℝ)))) := by
    ext U
    simp only [msFlow, expC_apply, ContinuousMap.smul_apply, smul_eq_mul, msAbs_apply,
      ContinuousMap.sub_apply, ContinuousMap.one_apply, mul_one, ← hG]
    congr 1
    rw [abs_mul, abs_inv, abs_of_pos had, div_eq_mul_inv]
    ring
  have h3 : stateK (NeZero.ne N) k (expC (msMu t γ γP j s • msAbs (msFlow Wf k s j))) ≤ Real.exp C * C := by
    rw [e]; exact h2
  exact state_pow_le_of_exp (stateK (NeZero.ne N) k) (msFlow Wf k s j) hmu h3 p

/-- **The size of a proxy**: `|S| · ∑_{j ∈ S} |c_j| / μ_j(s) + 1`, `S` the support of `c i s`. -/
def msPsize (t : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (c : Ix0 → ℝ → (MIx →₀ ℝ)) (s : ℝ) (i : Ix0) : ℝ :=
  ((c i s).support.card : ℝ) * ∑ j ∈ (c i s).support, |c i s j| / msMu t γ γP j s + 1

theorem msPsize_pos {t : ℝ} (ht : 0 < t) (γ : Ix0 → ℝ) (γP : ℝ) (c : Ix0 → ℝ → (MIx →₀ ℝ))
    {s : ℝ} (hs : 0 < s) (i : Ix0) : 0 < msPsize t γ γP c s i := by
  have hB : 0 ≤ ∑ j ∈ (c i s).support, |c i s j| / msMu t γ γP j s :=
    Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le
  have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) (c i s).support.card) hB
  unfold msPsize
  linarith

/-- **The moments of a proxy**, uniform in the step: under `ScaleAt` at `(k, s)`,
`ν_k(msProx i^{2p}) ≤ (2p)! e^C C · msPsize^{2p}`. -/
theorem msProx_moment [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {t C : ℝ} {γ : Ix0 → ℝ}
    {γP : ℝ} (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) (hS : ScaleAt Wf t C γ γP k s) (i : Ix0)
    (p : ℕ) :
    stateK (NeZero.ne N) k (msProx Wf c k s i ^ (2 * p))
      ≤ ((2 * p).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s i ^ (2 * p) := by
  obtain ⟨hC1, -⟩ := msFlow_moment Wf ht hs hS (Sum.inl i) 0
  have hK1 : 1 ≤ Real.exp C * C := by
    have := Real.add_one_le_exp C
    nlinarith
  set S := (c i s).support with hSdef
  set B := ∑ j ∈ S, |c i s j| / msMu t γ γP j s
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le
  rcases p with _ | n
  · simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one,
      (stateK (NeZero.ne N) k).map_one]
    exact hK1
  · set m := 2 * (n + 1)
    have hm' : m = (2 * n + 1) + 1 := by omega
    have hev : Even m := ⟨n + 1, by omega⟩
    have hpt : ∀ U, (msProx Wf c k s i ^ m) U
        ≤ (((S.card : ℝ) ^ (2 * n + 1)) • ∑ j ∈ S, (|c i s j| ^ m) • msFlow Wf k s j ^ m) U := by
      intro U
      have hP : msProx Wf c k s i U = ∑ j ∈ S, c i s j * msFlow Wf k s j U := by
        simp only [msProx, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
          smul_eq_mul, hSdef]
      simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, ContinuousMap.coe_sum,
        Finset.sum_apply, smul_eq_mul]
      rw [hP]
      have hab : |∑ j ∈ S, c i s j * msFlow Wf k s j U|
          ≤ ∑ j ∈ S, |c i s j| * |msFlow Wf k s j U| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => abs_mul _ _))
      calc (∑ j ∈ S, c i s j * msFlow Wf k s j U) ^ m
          = |∑ j ∈ S, c i s j * msFlow Wf k s j U| ^ m := (hev.pow_abs _).symm
        _ ≤ (∑ j ∈ S, |c i s j| * |msFlow Wf k s j U|) ^ m := pow_le_pow_left₀ (abs_nonneg _) hab m
        _ ≤ (S.card : ℝ) ^ (2 * n + 1) * ∑ j ∈ S, (|c i s j| * |msFlow Wf k s j U|) ^ m := by
            rw [hm']
            exact pow_sum_le_card_mul_sum_pow
              (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) _
        _ = (S.card : ℝ) ^ (2 * n + 1) * ∑ j ∈ S, |c i s j| ^ m * msFlow Wf k s j U ^ m := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_pow, hev.pow_abs (msFlow Wf k s j U)]
    have hsum : ∑ j ∈ S, (|c i s j| / msMu t γ γP j s) ^ m ≤ (S.card : ℝ) * B ^ m := by
      calc ∑ j ∈ S, (|c i s j| / msMu t γ γP j s) ^ m ≤ ∑ _j ∈ S, B ^ m :=
            Finset.sum_le_sum fun j hj => pow_le_pow_left₀
              (div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le)
              (Finset.single_le_sum (f := fun j => |c i s j| / msMu t γ γP j s)
                (fun j _ => div_nonneg (abs_nonneg _) (msMu_pos ht γ γP hs j).le) hj) m
        _ = (S.card : ℝ) * B ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    have hK0 : 0 ≤ Real.exp C * C := by linarith
    calc stateK (NeZero.ne N) k (msProx Wf c k s i ^ m)
        ≤ stateK (NeZero.ne N) k (((S.card : ℝ) ^ (2 * n + 1)) • ∑ j ∈ S, (|c i s j| ^ m) • msFlow Wf k s j ^ m) :=
          (stateK (NeZero.ne N) k).mono hpt
      _ = (S.card : ℝ) ^ (2 * n + 1)
            * ∑ j ∈ S, |c i s j| ^ m * stateK (NeZero.ne N) k (msFlow Wf k s j ^ m) := by
          rw [(stateK (NeZero.ne N) k).map_smul, (stateK (NeZero.ne N) k).map_sum]
          simp only [(stateK (NeZero.ne N) k).map_smul]
      _ ≤ (S.card : ℝ) ^ (2 * n + 1)
            * ∑ j ∈ S, |c i s j| ^ m * ((m.factorial : ℝ) / msMu t γ γP j s ^ m * (Real.exp C * C)) := by
          gcongr with j hj
          exact (msFlow_moment Wf ht hs hS j (n + 1)).2
      _ = (m.factorial : ℝ) * (Real.exp C * C)
            * ((S.card : ℝ) ^ (2 * n + 1) * ∑ j ∈ S, (|c i s j| / msMu t γ γP j s) ^ m) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [div_pow]
          ring
      _ ≤ (m.factorial : ℝ) * (Real.exp C * C) * ((S.card : ℝ) ^ (2 * n + 1) * ((S.card : ℝ) * B ^ m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (pow_nonneg (Nat.cast_nonneg _) _))
            (mul_nonneg (Nat.cast_nonneg _) hK0)
      _ = (m.factorial : ℝ) * (Real.exp C * C) * ((S.card : ℝ) * B) ^ m := by
          rw [hm']
          ring
      _ ≤ (m.factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s i ^ m := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hB0) ?_ m)
            (mul_nonneg (Nat.cast_nonneg _) hK0)
          show (S.card : ℝ) * B ≤ (S.card : ℝ) * B + 1
          linarith

/-- The cube radius of a test function. -/
def tR (f : TestFn) : ℝ := f.2.choose

/-- The bound of a test function. -/
def tM (f : TestFn) : ℝ := f.2.choose_spec.choose

theorem tIs (f : TestFn) : IsTest f.1 (tR f) (tM f) := f.2.choose_spec.choose_spec

/-- **The size of a test function**: `M (2R + 3)⁴ + 1` (`ContinuumNontrivial.riemann_le`'s box).

DERIVED: Inherited: `2`, `3` from `ContinuumNontrivial.riemann_le` (`a(2⌈R/a⌉ + 1) < 2R + 3a` at `a ≤ 1`);
`1` keeps the size positive. -/
def msTsize (f : TestFn) : ℝ := tM f * (2 * tR f + 3) ^ 4 + 1

theorem msTsize_pos (f : TestFn) : 0 < msTsize f := by
  have h := mul_nonneg (tIs f).M_nonneg (by positivity : (0 : ℝ) ≤ (2 * tR f + 3) ^ 4)
  unfold msTsize
  linarith

/-- **The flowed reading is bounded uniformly in the step**: under `ScaleAt` at `(k, s)`, `a_k ≤ 1`,
`|msLat| ≤ (1 + n (2n)! e^C C) ∏ᵢ msTsize fᵢ · msPsize i`. -/
theorem abs_msLat_le [NeZero N] (Wf : ℝ → ConfFlow N) (c : Ix0 → ℝ → (MIx →₀ ℝ)) {t C : ℝ} {γ : Ix0 → ℝ}
    {γP : ℝ} (ht : 0 < t) {k : ℕ} {s : ℝ} (hs : 0 < s) (hk1 : dySpacing N k ≤ 1)
    (hS : ScaleAt Wf t C γ γP k s) {ι : Type} [Fintype ι] (F : ι → CDatum (CbR N zOne)) :
    |msLat Wf c k s F|
      ≤ (1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
        * ∏ i, (msTsize (F i).2 * msPsize t γ γP c s (F i).1) := by
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  unfold msLat
  refine abs_state_prod_le (stateK (NeZero.ne N) k)
    (fun i => smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2)
    (fun i => msTsize (F i).2 * msPsize t γ γP c s (F i).1)
    (fun i => mul_pos (msTsize_pos _) (msPsize_pos ht γ γP c hs _)) (fun i => ?_)
  obtain ⟨hC1, -⟩ := msFlow_moment Wf ht hs hS (Sum.inl (F i).1) 0
  have hK0 : 0 ≤ Real.exp C * C := mul_nonneg (Real.exp_pos _).le (by linarith)
  set n := Fintype.card ι
  have h1 := moment_smear_le (stateK (NeZero.ne N) k) (MassGap.ContinuumNontrivial.stateK_transObs (NeZero.ne N) k) ha hk1
    (msProx Wf c k s (F i).1) (F i).2 (tIs (F i).2) n
  have h2 := msProx_moment Wf c ht hs hS (F i).1 n
  have hT0 : 0 ≤ tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4 :=
    mul_nonneg (tIs (F i).2).M_nonneg (by positivity)
  have hT : (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n) ≤ msTsize (F i).2 ^ (2 * n) :=
    pow_le_pow_left₀ hT0 (by unfold msTsize; linarith) _
  have hP0 : 0 ≤ ((2 * n).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s (F i).1 ^ (2 * n) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK0) (pow_nonneg (msPsize_pos ht γ γP c hs _).le _)
  calc stateK (NeZero.ne N) k (smear (dySpacing N k) (msProx Wf c k s (F i).1) (F i).2 ^ (2 * n))
      ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * stateK (NeZero.ne N) k (msProx Wf c k s (F i).1 ^ (2 * n)) := h1
    _ ≤ (tM (F i).2 * (2 * tR (F i).2 + 3) ^ 4) ^ (2 * n)
          * (((2 * n).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hT0 _)
    _ ≤ msTsize (F i).2 ^ (2 * n)
          * (((2 * n).factorial : ℝ) * (Real.exp C * C) * msPsize t γ γP c s (F i).1 ^ (2 * n)) :=
        mul_le_mul_of_nonneg_right hT hP0
    _ = ((2 * n).factorial : ℝ) * (Real.exp C * C)
          * (msTsize (F i).2 * msPsize t γ γP c s (F i).1) ^ (2 * n) := by
        rw [mul_pow]; ring

/-! ## 5. `BoundC` of the bare composites -/

/-- **`BoundC (CbR 2 zOne)` from the scale clause and the expansion**: at `s = min(θ d, b)`, the bare reading
is the flowed reading (bounded uniformly in the step, `abs_msLat_le`) up to the remainder of `Expand`. -/
theorem boundC_of_scale_expand {b : ℝ} (hb : 0 < b) {Wf : ℝ → ConfFlow 2}
    {c : Ix0 → ℝ → (MIx →₀ ℝ)} (hsc : ScaleControlAll b Wf) (hex : Expand Wf c) :
    InputsTriage.BoundC h2N (CbR 2 zOne) := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := hsc
  obtain ⟨θ, ε, Kr, κr, hθ, -, hE⟩ := hex
  intro ι _ _ F hF
  obtain ⟨hcont, d, hd, hsep⟩ := hF
  have hs : 0 < min (θ * d) b := lt_min (mul_pos hθ hd) hb
  refine ⟨(1 + Fintype.card ι * (((2 * Fintype.card ι).factorial : ℝ) * (Real.exp C * C)))
      * ∏ i, (msTsize (F i).2 * msPsize t γ γP c (min (θ * d) b) (F i).1)
    + Kr ^ Fintype.card ι * (min (θ * d) b / d) ^ ε * ∏ i, ((d ^ κr (F i).1)⁻¹ * l1 (F i).2), ?_⟩
  refine Filter.Eventually.filter_mono ultra_le ?_
  filter_upwards [hev, hE ι F d hd hcont hsep (min (θ * d) b) hs (min_le_left _ _),
    (tendsto_dySpacing 2).eventually (gt_mem_nhds hs),
    (tendsto_dySpacing 2).eventually (gt_mem_nhds one_pos)] with k hk hrem hks hk1
  have hP := abs_msLat_le Wf c ht hs hk1.le (hk _ hks.le (min_le_right _ _)) F
  have htri := abs_sub_abs_le_abs_sub (latC h2N (CbR 2 zOne) k F) (msLat Wf c k (min (θ * d) b) F)
  linarith

/-- **`BoundC (CbR 2 zOne)` from `MultiScaleAll`.** -/
theorem boundC_of_all {W : ConfFlow 2} (h : MultiScaleAll W) :
    InputsTriage.BoundC h2N (CbR 2 zOne) := by
  obtain ⟨b, Wf, c, H⟩ := h
  exact boundC_of_scale_expand H.b_pos H.scale H.expand

/-- **`ConvC (CbR 2 zOne)` from `MultiScaleAll`** (`InputsTriage.convC_iff_boundC`). -/
theorem convC_of_all {W : ConfFlow 2} (h : MultiScaleAll W) : ConvC h2N (CbR 2 zOne) :=
  (InputsTriage.convC_iff_boundC _ _).2 (boundC_of_all h)

/-! ## 6. The constant family -/

/-- **`Wf s = W` meets `scale`** whenever the moment holds at `s = b` with `γ = γP = 0`. -/
theorem scale_const [NeZero N] {W : ConfFlow N} {b t C : ℝ} (ht : 0 < t)
    (h : ∀ᶠ k in atTop, ScaleAt (fun _ => W) t C (fun _ => 0) 0 k b) :
    ScaleControlAll b (fun _ => W) := by
  refine ⟨t, C, fun _ => 0, 0, ht, ?_⟩
  filter_upwards [h] with k hk
  intro s hs hsb j
  have ha : 0 < dySpacing N k := dySpacing_pos (Nat.pos_of_ne_zero (NeZero.ne N)) k
  have hs0 : 0 < s := ha.trans_le hs
  have hmu : msMu t (fun _ => 0) 0 j s ≤ msMu t (fun _ => 0) 0 j b := by
    cases j <;> simp only [msMu, afLog, Real.rpow_zero, div_one] <;>
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0.le hsb _) ht.le
  refine le_trans ((stateK (NeZero.ne N) k).mono fun U => ?_) (hk j)
  simp only [expC_apply, ContinuousMap.smul_apply, smul_eq_mul, msAbs_apply]
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  exact div_le_div_of_nonneg_right hmu (pow_pos ha _).le

end MassGap.MultiScaleAll

end

#print axioms MassGap.MultiScaleAll.afLog_pos
#print axioms MassGap.MultiScaleAll.msMu_pos
#print axioms MassGap.MultiScaleAll.multiScale_of_all
#print axioms MassGap.MultiScaleAll.exp_abs_sub_le
#print axioms MassGap.MultiScaleAll.state_pow_le_of_exp
#print axioms MassGap.MultiScaleAll.msFlow_moment
#print axioms MassGap.MultiScaleAll.msPsize_pos
#print axioms MassGap.MultiScaleAll.msProx_moment
#print axioms MassGap.MultiScaleAll.msTsize_pos
#print axioms MassGap.MultiScaleAll.abs_msLat_le
#print axioms MassGap.MultiScaleAll.boundC_of_scale_expand
#print axioms MassGap.MultiScaleAll.boundC_of_all
#print axioms MassGap.MultiScaleAll.convC_of_all
#print axioms MassGap.MultiScaleAll.scale_const
