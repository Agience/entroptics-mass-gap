import Mathlib
import MassGap.HalfSpaceAlgebra
import MassGap.InfiniteShift
import MassGap.GibbsSpec
import MassGap.WilsonDLR
import MassGap.ReflectionHalfSpace
import MassGap.WilsonTransferReduction

/-!
# MassGap.GaugeInvariantAlgebra — the local gauge action on `ℤ⁴`, and the invariant subalgebra

`LocalGauge` defines a genuine local gauge action and proves invariance of `plaqObs`,
`wilsonAction` and `corrClay` — all on the **periodic** lattice `Site d n`. Nothing carries it to
`ℤ⁴`, so no statement about the infinite-volume theory can mention gauge invariance. This module is
that carry, and the subalgebra it makes available.

## Why it matters for the gap

`WilsonTransferReduction.transferData_of_state_facts` builds its transfer data on
`HalfSpaceAlgebra.halfSpaceAlg`, which is a locality predicate: `halfLinkObs l f`, an arbitrary
continuous function of a **single link variable**, belongs to it by `halfLinkObs_mem`. So `GapAt` on
that data demands a connected-correlator bound for observables that are not gauge invariant, while
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` bounds a **plaquette-pair**
correlator. The two do not meet.

The construction is not bespoke, though: `transferData_of_state_facts` is
`WilsonTransferReduction.assembleTransferData` applied to `halfSpaceAlg`, and that builder takes the
algebra as an argument. A smaller algebra needs only its own closure facts, and reflection
positivity on a subset is inherited from the superset for free. `gaugeInvHalfSpaceAlg` is that
smaller algebra, with the two closure facts the builder asks of it proved here.

## What is here

The action and the invariant subalgebra; the transfer data on it, since
`TransferAssembly.assembleTransferData` takes the algebra as an argument; the three predicates
restricted from the larger algebra — reflection positivity, `PositiveTransfer`, `GapAt` — each
because it quantifies over the algebra; the `GapAt` characterisation as a pairing inequality; and a
non-trivial member, since `ihol_igaugeTransform` makes the plaquette holonomy conjugate and a class
function of it invariant.

## Scope

The remaining obligation is the pairing inequality itself, and
`forall_span_of_forall_finite_combination` says where to attack it: `GapAt` is quadratic, so a bound
on plaquette observables does not extend to their span by linearity, but a bound on finite
combinations does — a Gram-matrix condition whose entries are two-observable connected pairings.
Nothing here proves that condition.

Two things are taken as hypotheses rather than proved, both deliberately: an observable is named by
`hF` rather than constructed, because nothing in the tree proves the holonomy continuous; and the
spanning set in `gaugeInv_pairing_of_spanning` is supplied by the caller, because nothing here shows
the invariant algebra is spanned by plaquette observables.
-/

namespace MassGap.GaugeInvariantAlgebra

open MassGap.InfiniteLattice MassGap.InfiniteShift MassGap.HalfSpaceAlgebra

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- **The local gauge action on `ℤ⁴`.** A gauge function `g : ISite → G` acts on a configuration by
`g` at the link's source site and `g⁻¹` at its target, the target being `ishift l.1 l.2`.

This is `LocalGauge.gaugeTransform` with the periodic `Site d n` replaced by `ISite` and the periodic
`shift` by `InfiniteShift.ishift`. The genuine local group, not the constant/centre subgroup that
`CompactGauge.confConj` conjugates by.

DERIVED: `4` is the spacetime dimension, the `Fin 4` a direction ranges over and the `Fin 4 → ℤ`
a site is; no other numeral occurs. `l.1` and `l.2` are the link's direction and base site. -/
def igaugeTransform (g : ISite → G) (U : IConf G) : IConf G :=
  fun l => g l.2 * U l * (g (ishift l.1 l.2))⁻¹

/-- **Gauge invariance of an observable on `ℤ⁴`.** Quantified over every gauge function, with no
continuity or support condition on it — the local group, not a subgroup of it.

DERIVED: `4` is the spacetime dimension, the `Fin 4` a direction ranges over and the `Fin 4 → ℤ`
a site is. No other numeral occurs. -/
def IsIGaugeInvariant (F : C(IConf G, ℝ)) : Prop :=
  ∀ (g : ISite → G) (U : IConf G), F (igaugeTransform g U) = F U

/-- **The gauge action is covariant under translation**: translating a gauge-transformed
configuration is the same as gauge-transforming the translated one, with the gauge function itself
translated.

The mathematical content is `InfiniteShift.ishift_comm` — the two unit translations commute, so the
target site of a translated link is the translation of the target site. That is the same fact
`LocalGauge.hol_gaugeTransform` turns on, at the infinite lattice.

DERIVED: `4` is the spacetime dimension, the `Fin 4` a direction ranges over and the `Fin 4 → ℤ`
a site is. No other numeral occurs. -/
theorem ishiftConf_igaugeTransform (μ : Fin 4) (g : ISite → G) (U : IConf G) :
    ishiftConf μ (igaugeTransform g U)
      = igaugeTransform (fun x => g (ishift μ x)) (ishiftConf μ U) := by
  funext l
  simp only [ishiftConf, ishiftLink, igaugeTransform]
  rw [ishift_comm μ l.1 l.2]

#print axioms ishiftConf_igaugeTransform

/-- Gauge invariance survives translation. This is one of the two closure facts
`assembleTransferData` asks of its algebra, for the invariant one.

The translated gauge function is `g ∘ ishift μ`, and invariance is quantified over **every** gauge
function, so the substitution costs nothing — which is why the local group rather than a subgroup is
the right quantifier here.

DERIVED: `4` is the spacetime dimension, the `Fin 4` a direction ranges over and the `Fin 4 → ℤ`
a site is. No other numeral occurs. -/
theorem IsIGaugeInvariant.ishiftObsCM {F : C(IConf G, ℝ)} (hF : IsIGaugeInvariant F)
    (μ : Fin 4) : IsIGaugeInvariant (MassGap.HalfSpaceAlgebra.ishiftObsCM μ F) := by
  intro g U
  show F (ishiftConf μ (igaugeTransform g U)) = F (ishiftConf μ U)
  rw [ishiftConf_igaugeTransform]
  exact hF _ _

#print axioms IsIGaugeInvariant.ishiftObsCM

/-- The unit observable is gauge invariant: it does not read the configuration at all.

DERIVED: `1` is the unit of `C(IConf G, ℝ)`, the constant function one; `4` is the spacetime
dimension. -/
theorem isIGaugeInvariant_one : IsIGaugeInvariant (1 : C(IConf G, ℝ)) := fun _ _ => rfl

#print axioms isIGaugeInvariant_one

/-- **The plaquette holonomy conjugates.** `ihol q (igaugeTransform g U) = g x · ihol q U · (g x)⁻¹`
at the plaquette's base site `x = q.2`.

The four boundary factors each pick up `g` at their source and `g⁻¹` at their target, and the
adjacent ones cancel in pairs, leaving the base site's factor at each end. The one step that is not
formal is the far corner: the third factor's target is `ishift μ (ishift ν x)` and the second
factor's is `ishift ν (ishift μ x)`, and they cancel only because `InfiniteShift.ishift_comm` makes
them the same site. That is the statement that the loop closes.

DERIVED: `4` is the spacetime dimension; `1` and `2` in `q.1.1`, `q.1.2` and `q.2` are projections,
not quantities. -/
theorem ihol_igaugeTransform (q : MassGap.GibbsSpec.IPlaq) (g : ISite → G) (U : IConf G) :
    MassGap.GibbsSpec.ihol q (igaugeTransform g U)
      = g q.2 * MassGap.GibbsSpec.ihol q U * (g q.2)⁻¹ := by
  have hbridge : ∀ (μ : Fin 4) (x : ISite),
      MassGap.GibbsSpec.ishift μ x = MassGap.InfiniteLattice.ishift μ x := fun _ _ => rfl
  simp only [MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd,
    igaugeTransform, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_true, if_false, mul_inv_rev, inv_inv, hbridge]
  first
    | rw [MassGap.InfiniteShift.ishift_comm q.1.1 q.1.2 q.2]
    | rw [MassGap.InfiniteShift.ishift_comm q.1.2 q.1.1 q.2]
    | skip
  group

#print axioms ihol_igaugeTransform

/-- **A class function of the plaquette holonomy is gauge invariant.** The holonomy conjugates, and a
conjugation-invariant `φ` does not see the conjugation.

`MassGap.WilsonAction.wilsonDensity_conj` is such a `φ`, so the invariant algebra contains genuine
plaquette observables and is not the constants — which is what the whole route turns on. The
observable is taken as a `C(IConf G, ℝ)` with `hF` naming it, so no continuity plumbing enters here.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
theorem isIGaugeInvariant_of_classFun {φ : G → ℝ}
    (hφ : ∀ h k : G, φ (h * k * h⁻¹) = φ k) (q : MassGap.GibbsSpec.IPlaq)
    {F : C(IConf G, ℝ)} (hF : ∀ U, F U = φ (MassGap.GibbsSpec.ihol q U)) :
    IsIGaugeInvariant F := by
  intro g U
  rw [hF, hF, ihol_igaugeTransform, hφ]

#print axioms isIGaugeInvariant_of_classFun

/-- **The gauge-invariant observables form a submodule.** The gauge action is applied to the
ARGUMENT, so linearity passes straight through: a sum of invariant observables is invariant at the
same gauge function, and so is a scalar multiple.

DERIVED: `4` is the spacetime dimension; `0` is the zero observable. No other numeral occurs. -/
def igaugeInv : Submodule ℝ C(IConf G, ℝ) where
  carrier := {F | IsIGaugeInvariant F}
  add_mem' {F H} hF hH := fun g U => by
    simp only [ContinuousMap.add_apply, hF g U, hH g U]
  zero_mem' := fun _ _ => rfl
  smul_mem' c F hF := fun g U => by
    simp only [ContinuousMap.smul_apply, hF g U]

/-- **The gauge-invariant half-space algebra**: local on a finite set inside the positive half, and
invariant under the local gauge group. A `Submodule`, because `InfiniteReflection.ReflPositiveOn`
asks for one.

`HalfSpaceAlgebra.halfLinkObs l f` lies in `halfSpaceAlg` for every continuous `f`, and is not in
general a member of this one — which is the whole point of the restriction.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
def gaugeInvHalfSpaceAlg (τ : Fin 4) (c : ℤ) : Submodule ℝ C(IConf G, ℝ) :=
  halfSpaceAlg (G := G) τ c ⊓ igaugeInv

/-- The invariant algebra sits inside the locality one, so reflection positivity on `halfSpaceAlg`
restricts to it at no cost. That is why this route needs no new positivity result.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
theorem gaugeInvHalfSpaceAlg_le (τ : Fin 4) (c : ℤ) :
    gaugeInvHalfSpaceAlg (G := G) τ c ≤ halfSpaceAlg (G := G) τ c :=
  inf_le_left

#print axioms gaugeInvHalfSpaceAlg_le

/-- **Reflection positivity, restricted.** `ReflPositiveOn` quantifies over the algebra, so a smaller
algebra inherits it from a larger one by composition with the inclusion. No integral is re-estimated.

DERIVED: `4` is the spacetime dimension; `0` is the lower bound reflection positivity asserts. -/
theorem reflPositiveOn_gaugeInv {R : MassGap.InfiniteReflection.Reflection (IConf G)}
    {ν : MassGap.DLRLimit.State (IConf G)} (τ : Fin 4) (c : ℤ)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn R (halfSpaceAlg (G := G) τ c) ν) :
    MassGap.InfiniteReflection.ReflPositiveOn R (gaugeInvHalfSpaceAlg (G := G) τ c) ν :=
  fun f hf => hpos f (gaugeInvHalfSpaceAlg_le τ c hf)

#print axioms reflPositiveOn_gaugeInv

/-- `1` belongs to the invariant algebra: `one_mem_halfSpaceAlg` and `isIGaugeInvariant_one`.

DERIVED: `1` is the unit observable; `4` is the spacetime dimension. -/
theorem one_mem_gaugeInvHalfSpaceAlg (τ : Fin 4) (c : ℤ) :
    (1 : C(IConf G, ℝ)) ∈ gaugeInvHalfSpaceAlg (G := G) τ c :=
  Submodule.mem_inf.mpr ⟨one_mem_halfSpaceAlg τ c, isIGaugeInvariant_one⟩

#print axioms one_mem_gaugeInvHalfSpaceAlg

/-- **The invariant algebra is shift stable.** Locality is carried by
`HalfSpaceAlgebra.halfSpaceAlg_shift_stable` and invariance by `IsIGaugeInvariant.ishiftObsCM`, so
both components transport and nothing new is needed.

With `one_mem_gaugeInvHalfSpaceAlg` and `reflPositiveOn_gaugeInv` this is every input
`TransferAssembly.assembleTransferData` asks about the algebra; its remaining six are shared with the
`halfSpaceAlg` instantiation and carry over unchanged.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
theorem gaugeInvHalfSpaceAlg_shift_stable (τ : Fin 4) (c : ℤ) {F : C(IConf G, ℝ)}
    (hF : F ∈ gaugeInvHalfSpaceAlg (G := G) τ c) :
    MassGap.HalfSpaceAlgebra.ishiftObsCM τ F ∈ gaugeInvHalfSpaceAlg (G := G) τ c :=
  Submodule.mem_inf.mpr
    ⟨halfSpaceAlg_shift_stable τ c (Submodule.mem_inf.mp hF).1,
      (Submodule.mem_inf.mp hF).2.ishiftObsCM τ⟩

#print axioms gaugeInvHalfSpaceAlg_shift_stable

/-- **The invariant algebra contains genuine plaquette observables.** A conjugation-invariant
function of the holonomy of a plaquette whose links all lie in the positive half belongs to
`gaugeInvHalfSpaceAlg`.

Both components are discharged: locality on `ilinks q` is `MassGap.GibbsSpec.ihol_congr`, which says
the holonomy reads only its own links, and invariance is `isIGaugeInvariant_of_classFun`.
`MassGap.WilsonAction.wilsonDensity_conj` supplies such a `φ`, so the algebra is not the constants
and the route through it is not vacuous.

The observable is taken as a `C(IConf G, ℝ)` named by `hF`, so continuity of the holonomy — which
nothing in the tree states — does not enter. A caller exhibiting a concrete plaquette observable
supplies it.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
theorem mem_gaugeInvHalfSpaceAlg_of_classFun {φ : G → ℝ}
    (hφ : ∀ h k : G, φ (h * k * h⁻¹) = φ k) (q : MassGap.GibbsSpec.IPlaq)
    {F : C(IConf G, ℝ)} (hF : ∀ U, F U = φ (MassGap.GibbsSpec.ihol q U))
    (τ : Fin 4) (c : ℤ)
    (hq : ∀ l ∈ MassGap.GibbsSpec.ilinks q, l ∈ MassGap.HalfSpaceAlgebra.posHalf τ c) :
    F ∈ gaugeInvHalfSpaceAlg (G := G) τ c := by
  classical
  refine Submodule.mem_inf.mpr
    ⟨⟨(MassGap.GibbsSpec.ilinks q).toFinset, ?_, ?_⟩, isIGaugeInvariant_of_classFun hφ q hF⟩
  · intro l hl
    exact hq l (List.mem_toFinset.mp (Finset.mem_coe.mp hl))
  · intro U V h
    rw [hF, hF]
    exact congrArg φ (MassGap.GibbsSpec.ihol_congr q U V
      (fun l hl => h l (List.mem_toFinset.mpr hl)))

#print axioms mem_gaugeInvHalfSpaceAlg_of_classFun

/-! ### The plaquette observable, constructed -/

section Constructed

variable {N : ℕ}


/-- **The plaquette observable on `ℤ⁴`, constructed**: the Wilson density of the plaquette holonomy,
bundled as a continuous map.

Everything above took such an observable as a hypothesis named by `hF`, because nothing in the tree
proved the holonomy continuous. `continuous_ihol` does, so it can be built.

DERIVED: no numeral occurs; `N` is the caller's gauge rank. -/
noncomputable def iplaqObs (q : MassGap.GibbsSpec.IPlaq) :
    C(MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N), ℝ) :=
  ⟨fun U => MassGap.WilsonAction.wilsonDensity
      (MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) q U),
    MassGap.WilsonAction.continuous_wilsonDensity.comp
      (MassGap.WilsonDLR.continuous_ihol q)⟩

#print axioms iplaqObs

/-- **The invariant algebra provably contains a plaquette observable** — nothing assumed.

`WilsonAction.wilsonDensity_conj` makes the density a class function, `ihol_igaugeTransform` makes
the holonomy conjugate, and `mem_gaugeInvHalfSpaceAlg_of_classFun` does the rest. The only hypothesis
is that the plaquette's links lie in the positive half, which is a statement about where the
plaquette sits and not about the observable.

This settles non-vacuity of the route: `gaugeInvHalfSpaceAlg` is not the constants, and no continuity
or membership is taken on trust.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
theorem iplaqObs_mem_gaugeInvHalfSpaceAlg (q : MassGap.GibbsSpec.IPlaq) (τ : Fin 4) (c : ℤ)
    (hq : ∀ l ∈ MassGap.GibbsSpec.ilinks q, l ∈ MassGap.HalfSpaceAlgebra.posHalf τ c) :
    iplaqObs (N := N) q ∈ gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ c :=
  mem_gaugeInvHalfSpaceAlg_of_classFun
    (fun h k => MassGap.WilsonAction.wilsonDensity_conj h k) q (fun _ => rfl) τ c hq

#print axioms iplaqObs_mem_gaugeInvHalfSpaceAlg

/-- A lattice step never lowers a coordinate: `ishift μ` raises the `μ`-th by one and fixes the rest.

DERIVED: `4` is the spacetime dimension, the range of the direction index. -/
theorem le_ishift_apply (μ τ : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    x τ ≤ MassGap.GibbsSpec.ishift μ x τ := by
  unfold MassGap.GibbsSpec.ishift
  by_cases h : τ = μ
  · subst h; simp
  · rw [Function.update_of_ne h]

#print axioms le_ishift_apply

/-- **A plaquette based at or above the plane lies in the positive half.** Its four links sit at its
base site or one step up from it (`GibbsSpec.ilinks_eq`), and a step never lowers the `τ`-coordinate.

DERIVED: `4` is the spacetime dimension, the range of the direction index. -/
theorem ilinks_mem_posHalf_of_le {τ : Fin 4} {p : ℤ} (q : MassGap.GibbsSpec.IPlaq)
    (hq : p ≤ q.2 τ) :
    ∀ l ∈ MassGap.GibbsSpec.ilinks q, l ∈ MassGap.HalfSpaceAlgebra.posHalf τ p := by
  intro l hl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  have h1 := le_ishift_apply q.1.1 τ q.2
  have h2 := le_ishift_apply q.1.2 τ q.2
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [MassGap.HalfSpaceAlgebra.posHalf, Set.mem_setOf_eq] <;> omega

#print axioms ilinks_mem_posHalf_of_le

/-- The plaquette observable of a plaquette based at or above the plane is in the gauge-invariant
half-space algebra. `iplaqObs_mem_gaugeInvHalfSpaceAlg` with its link hypothesis discharged.

DERIVED: `4` is the spacetime dimension, the range of the direction index. -/
theorem iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le (q : MassGap.GibbsSpec.IPlaq) (τ : Fin 4) (p : ℤ)
    (hq : p ≤ q.2 τ) :
    iplaqObs (N := N) q ∈ gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p :=
  iplaqObs_mem_gaugeInvHalfSpaceAlg q τ p (ilinks_mem_posHalf_of_le q hq)

#print axioms iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le

/-- **The reflection carries a plaquette observable to the observable at the reflected plaquette.**

`LatticeReflection.ihol_ireflConf` says the holonomy of a plaquette in the reflected configuration is
**conjugate** to the holonomy of the reflected plaquette — the mirror reverses the loop, so the two
agree only up to a conjugating element, which is existential and depends on the configuration.
`WilsonAction.wilsonDensity_conj` annihilates it, because the density is a class function.

**This is what makes the reflected pairing a correlator at a separation.** The pairing
`ν (ireflObs τ c (iplaqObs q) * iplaqObs q')` becomes a correlator of two plaquette observables, one
of them at `ireflPlaq τ c q`; and `ReflectionHalfSpace.ireflPlaq_maps_plus_to_minus` sends the
positive half to the negative one, so their separation grows with the reflection depth. That is the
geometric structure `ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` bounds.

DERIVED: `4` is the spacetime dimension, the `Fin 4` the reflection axis `τ` ranges over. No other
numeral occurs; `c` is the reflection constant. -/
theorem ireflObs_iplaqObs (τ : Fin 4) (c : ℤ) (q : MassGap.GibbsSpec.IPlaq) :
    MassGap.LatticeReflection.ireflObs τ c (iplaqObs (N := N) q)
      = iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q) := by
  ext U
  obtain ⟨g, hg⟩ := MassGap.LatticeReflection.ihol_ireflConf τ c q U
  show MassGap.WilsonAction.wilsonDensity
      (MassGap.WilsonLattice.wilsonHol MassGap.InfiniteLattice.ibd q
        (MassGap.LatticeReflection.ireflConf τ c U)) = _
  rw [hg]
  exact MassGap.WilsonAction.wilsonDensity_conj g _

#print axioms ireflObs_iplaqObs

/-- **The shift moves a plaquette observable to the observable of the shifted plaquette.**

The analogue of `ireflObs_iplaqObs` for the translation. `InfiniteShift.wilsonHol_ishiftPlaq` says
the holonomy of a translated plaquette on a configuration is the holonomy of the original on the
translated configuration, and `ishiftObsL` is precomposition by that translation — so the two agree
with no conjugation step, unlike the reflection, where the holonomy moves only up to conjugacy.

`ishiftObsL` is the translation `gaugeInvTransferData` is assembled from, so this is what turns the
shift appearing in `ClayCapstone.gaugeInv_clay_gap_of_state_decay`'s hypothesis into a plaquette
observable at a translated plaquette.

DERIVED: `4` is the spacetime dimension, indexing the translation's direction. -/
theorem ishiftObsL_iplaqObs (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) :
    MassGap.ReflectionShift.ishiftObsL τ (iplaqObs (N := N) q)
      = iplaqObs (N := N) (MassGap.InfiniteShift.ishiftPlaq τ q) := by
  ext U
  show MassGap.WilsonAction.wilsonDensity
      (MassGap.WilsonLattice.wilsonHol MassGap.InfiniteLattice.ibd q
        (MassGap.InfiniteShift.ishiftConf τ U)) = _
  rw [← MassGap.InfiniteShift.wilsonHol_ishiftPlaq τ q U]
  rfl

#print axioms ishiftObsL_iplaqObs

/-- **Iterated**: `m` translations of a plaquette observable is the observable of the `m`-fold
translated plaquette.

This is the form the obligation consumes. `ClayCapstone.gaugeInv_clay_gap_of_state_decay` asks about
`(ishiftObsL τ)^[2 * n] x`; at `x = iplaqObs q` that is `iplaqObs` of the `2 * n`-translate of `q`,
and `ReflectionHalfSpace.axis_sep_irefl_shift` bounds that plaquette's separation from
`ireflPlaq τ (2 * p) q` below by `2 * n`.

DERIVED: `4` is the spacetime dimension; `m` is the caller's. -/
theorem ishiftObsL_iterate_iplaqObs (τ : Fin 4) (m : ℕ) (q : MassGap.GibbsSpec.IPlaq) :
    (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] (iplaqObs (N := N) q)
      = iplaqObs (N := N) ((MassGap.InfiniteShift.ishiftPlaq τ)^[m] q) := by
  induction m with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact ishiftObsL_iplaqObs τ _

#print axioms ishiftObsL_iterate_iplaqObs

/-- **The box-carrier plaquette observable is the infinite-lattice one, read through `splice`.**

`WilsonReal.wilsonPlaqObs bd p` is `wilsonDensity ∘ wilsonHol bd p`, and
`ReflectionHalfSpace.wilsonHol_boxBd` identifies the box holonomy with `GibbsSpec.ihol` at the
spliced configuration. So the two observables agree, for any plaquette of the box.

**This is the join.** `ReflectionHalfSpace.stateFree_eq_expect_boxBd` expects exactly
`fun u => f (splice Λ u ω)`, so `stateFree`'s expectation of `iplaqObs q` is the box system's
expectation of `wilsonPlaqObs (boxBd Λ) q`, and its connected correlator of two of them is
`WilsonBridge.wilsonCorrConn (boxBd Λ)` — the object
`ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` bounds geometrically and uniformly in the box.

DERIVED: no numeral occurs; `Λ`, `q`, `u` and `ω` are the caller's. -/
theorem iplaqObs_splice_eq_wilsonPlaqObs (Λ : Finset MassGap.InfiniteLattice.ILink)
    (q : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq) (MassGap.GibbsSpec.splice Λ u ω)
      = MassGap.WilsonReal.wilsonPlaqObs (N := N) (MassGap.ReflectionHalfSpace.boxBd Λ) q u := by
  show MassGap.WilsonAction.wilsonDensity
      (MassGap.GibbsSpec.ihol (q : MassGap.GibbsSpec.IPlaq)
        (MassGap.GibbsSpec.splice Λ u ω)) = _
  rw [← MassGap.ReflectionHalfSpace.wilsonHol_boxBd Λ q u ω]
  rfl

#print axioms iplaqObs_splice_eq_wilsonPlaqObs

/-- **`stateFree`'s expectation of a plaquette observable is the box system's.**

`ReflectionHalfSpace.stateFree_eq_expect_boxBd` sends `stateFree … f` to the box system's
expectation of `fun u => f (splice Λ u ω)`, and `iplaqObs_splice_eq_wilsonPlaqObs` identifies that
function with `WilsonReal.wilsonPlaqObs (boxBd Λ) q`.

This is the half of the composition that lives at the box.
`pairing_iplaqObs_eq_connected` states the reflected pairing as a connected correlator at any state;
`ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` bounds it at the box system; and this is what lets
a statement about `stateFree` be read as one about that system — which
`InfiniteReflection.connected_pairing_le_of_eventually` then carries to the limiting state.

The density is instantiated at `WilsonAction.wilsonDensity`, since `wilsonPlaqObs` is the matching
observable only for that one.

DERIVED: `0` and `2` are `wilsonDensity`'s range, carried in exactly as `stateFree` takes them;
`β`, `Λ`, `ω` and `q` are the caller's. -/
theorem stateFree_iplaqObs (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (q : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
      = (MassGap.WilsonLattice.wilsonSystem (MassGap.ReflectionHalfSpace.boxBd Λ)
          MassGap.WilsonAction.wilsonDensity).expect
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) β
          (MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.ReflectionHalfSpace.boxBd Λ) q) := by
  rw [MassGap.ReflectionHalfSpace.stateFree_eq_expect_boxBd]
  congr 1
  funext u
  exact iplaqObs_splice_eq_wilsonPlaqObs Λ q u ω

#print axioms stateFree_iplaqObs

/-- The product case of `stateFree_iplaqObs`: `stateFree`'s expectation of a product of two plaquette
observables is `WilsonBridge.wilsonCorr` at the box carrier.

DERIVED: `0` and `2` are `wilsonDensity`'s range, as `stateFree` takes them. -/
theorem stateFree_iplaqObs_mul
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (q q' : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)
          * iplaqObs (N := N) (q' : MassGap.GibbsSpec.IPlaq))
      = MassGap.WilsonBridge.wilsonCorr (Nc := N)
          (MassGap.ReflectionHalfSpace.boxBd Λ) q β q' := by
  rw [MassGap.ReflectionHalfSpace.stateFree_eq_expect_boxBd]
  congr 1
  funext u
  show iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq) (MassGap.GibbsSpec.splice Λ u ω)
      * iplaqObs (N := N) (q' : MassGap.GibbsSpec.IPlaq) (MassGap.GibbsSpec.splice Λ u ω) = _
  rw [iplaqObs_splice_eq_wilsonPlaqObs Λ q u ω, iplaqObs_splice_eq_wilsonPlaqObs Λ q' u ω]

#print axioms stateFree_iplaqObs_mul

/-- **`stateFree`'s connected correlator of two plaquette observables is `wilsonCorrConn` at the box
carrier.**

`WilsonBridge.wilsonCorrConn` is `wilsonCorr` minus the product of the one-point expectations;
`stateFree_iplaqObs_mul` gives the first and `stateFree_iplaqObs` the other two.

**This completes the identification.** `ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` bounds the
right-hand side geometrically and uniformly in the box, and
`pairing_iplaqObs_eq_connected` says the reflected pairing the gap obligation is stated on is exactly
a connected correlator of this shape — with the reflected plaquette in the opposite half by
`ReflectionHalfSpace.ireflPlaq_maps_plus_to_minus`, so the separation grows with the reflection depth.

DERIVED: `0` and `2` are `wilsonDensity`'s range, as `stateFree` takes them. -/
theorem stateFree_connected_eq_wilsonCorrConn
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (q q' : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)
          * iplaqObs (N := N) (q' : MassGap.GibbsSpec.IPlaq))
      - MassGap.ReflectionHalfSpace.stateFree
          MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
          (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
        * MassGap.ReflectionHalfSpace.stateFree
            MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
            (iplaqObs (N := N) (q' : MassGap.GibbsSpec.IPlaq))
      = MassGap.WilsonBridge.wilsonCorrConn (Nc := N)
          (MassGap.ReflectionHalfSpace.boxBd Λ) q β q' := by
  rw [stateFree_iplaqObs_mul hφ0 hφ2 β Λ ω q q',
    stateFree_iplaqObs hφ0 hφ2 β Λ ω q, stateFree_iplaqObs hφ0 hφ2 β Λ ω q']
  rfl

#print axioms stateFree_connected_eq_wilsonCorrConn

/-- **`stateFree`'s expectation of a PRODUCT of plaquette observables is the box system's.**

The family counterpart of `stateFree_iplaqObs`. `ReflectionHalfSpace.stateFree_eq_expect_boxBd`
moves to the box, `ContinuousMap.prod_apply` evaluates the product of continuous maps pointwise, and
`iplaqObs_splice_eq_wilsonPlaqObs` identifies each factor.

DERIVED: `0` and `2` are `wilsonDensity`'s range, carried in exactly as `stateFree` takes them. -/
theorem stateFree_iplaqObsF
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (Ao : Finset ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
      = (MassGap.WilsonLattice.wilsonSystem (MassGap.ReflectionHalfSpace.boxBd Λ)
          MassGap.WilsonAction.wilsonDensity).expect
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) β
          (fun u => ∏ p ∈ Ao, MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.ReflectionHalfSpace.boxBd Λ) p u) := by
  rw [MassGap.ReflectionHalfSpace.stateFree_eq_expect_boxBd]
  congr 1
  funext u
  have h : ∀ q : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ),
      iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq) (MassGap.GibbsSpec.splice Λ u ω)
        = MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.ReflectionHalfSpace.boxBd Λ) q u :=
    fun q => iplaqObs_splice_eq_wilsonPlaqObs Λ q u ω
  simp only [ContinuousMap.prod_apply, h]

#print axioms stateFree_iplaqObsF

/-- **`stateFree`'s joint expectation of two PRODUCTS of plaquette observables is `wilsonCorrF` at
the box carrier.** The family counterpart of `stateFree_iplaqObs_mul`.

DERIVED: `0` and `2` are `wilsonDensity`'s range. -/
theorem stateFree_iplaqObsF_mul
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (Ao Bo : Finset ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        ((∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
          * ∏ q ∈ Bo, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
      = MassGap.WilsonBridge.wilsonCorrF (Nc := N)
          (MassGap.ReflectionHalfSpace.boxBd Λ) Ao β Bo := by
  rw [MassGap.ReflectionHalfSpace.stateFree_eq_expect_boxBd]
  unfold MassGap.WilsonBridge.wilsonCorrF
  congr 1
  funext u
  have h : ∀ q : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ),
      iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq) (MassGap.GibbsSpec.splice Λ u ω)
        = MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.ReflectionHalfSpace.boxBd Λ) q u :=
    fun q => iplaqObs_splice_eq_wilsonPlaqObs Λ q u ω
  simp only [ContinuousMap.mul_apply, ContinuousMap.prod_apply, h]

#print axioms stateFree_iplaqObsF_mul

/-- **`stateFree`'s connected correlator of two PRODUCTS of plaquette observables is
`wilsonCorrConnF` at the box carrier.**

The family counterpart of `stateFree_connected_eq_wilsonCorrConn`, and the identification that was
standing between the strong-coupling family estimate and the gap obligation.
`StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow` bounds the right-hand side
geometrically, so the left-hand side — a connected correlator of arbitrary products of plaquette
observables, which is what a gauge-invariant observable of any extent is built from — now inherits
that bound.

DERIVED: `0` and `2` are `wilsonDensity`'s range. -/
theorem stateFree_connectedF_eq_wilsonCorrConnF
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (Ao Bo : Finset ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        ((∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
          * ∏ q ∈ Bo, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
      - MassGap.ReflectionHalfSpace.stateFree
          MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
          (∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
        * MassGap.ReflectionHalfSpace.stateFree
            MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
            (∏ q ∈ Bo, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
      = MassGap.WilsonBridge.wilsonCorrConnF (Nc := N)
          (MassGap.ReflectionHalfSpace.boxBd Λ) Ao β Bo := by
  rw [stateFree_iplaqObsF_mul hφ0 hφ2 β Λ ω Ao Bo,
    stateFree_iplaqObsF hφ0 hφ2 β Λ ω Ao, stateFree_iplaqObsF hφ0 hφ2 β Λ ω Bo]
  rfl

#print axioms stateFree_connectedF_eq_wilsonCorrConnF


/-- The reflection fixes the unit observable: precomposition does not move a constant.

DERIVED: `4` is the spacetime dimension; `1` is the unit observable. -/
theorem ireflObs_one (τ : Fin 4) (c : ℤ) :
    MassGap.LatticeReflection.ireflObs (G := MassGap.SUN.SU N) τ c 1 = 1 := rfl

#print axioms ireflObs_one

/-- **The reflected pairing of two plaquette observables is a connected correlator.**

`ireflObs_iplaqObs` carries the reflection onto the plaquette and `ireflObs_one` leaves the mean term
alone, so the pairing is a product of two mean-subtracted plaquette observables. Reflection
invariance of the state identifies `ν (iplaqObs (ireflPlaq τ c q))` with `ν (iplaqObs q)`, and the
four cross terms collapse to `ν (A * B) - ν A * ν B`.

**That is `WilsonBridge.wilsonCorrConn`.** With `iplaqObs_splice_eq_wilsonPlaqObs` identifying the
observables at the box carrier and `ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` bounding it
geometrically and uniformly in the box, this puts the strong-coupling estimate on the gap
obligation's own expression. `ReflectionHalfSpace.ireflPlaq_maps_plus_to_minus` is what gives the
bound its force: the reflected plaquette sits in the opposite half, so the separation the geometric factor
is raised to grows with the reflection depth.

The product expansion is not a `module` identity — it multiplies two ring elements — so moving the
scalars past the product is `smul_mul_assoc` and `mul_smul_comm`, with `smul_smul` collapsing the
constant term. The state's linearity is applied to the expanded form, since `ring` normalises inside
the state and cannot push it through a sum.

DERIVED: `4` is the spacetime dimension; `1` is the unit observable. -/
theorem pairing_iplaqObs_eq_connected (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N)))
    (hinv : ∀ f, ν (MassGap.LatticeReflection.ireflObs τ c f) = ν f)
    (q q' : MassGap.GibbsSpec.IPlaq) :
    ν (MassGap.LatticeReflection.ireflObs τ c
          (iplaqObs (N := N) q - ν (iplaqObs (N := N) q) • 1)
        * (iplaqObs (N := N) q' - ν (iplaqObs (N := N) q') • 1))
      = ν (iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q)
            * iplaqObs (N := N) q')
        - ν (iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q))
          * ν (iplaqObs (N := N) q') := by
  have hA : MassGap.LatticeReflection.ireflObs τ c
        (iplaqObs (N := N) q - ν (iplaqObs (N := N) q) • 1)
      = iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q)
        - ν (iplaqObs (N := N) q) • 1 := by
    rw [map_sub, map_smul, ireflObs_iplaqObs, ireflObs_one]
  have hprod : (iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q)
        - ν (iplaqObs (N := N) q) • 1)
      * (iplaqObs (N := N) q' - ν (iplaqObs (N := N) q') • 1)
      = iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q) * iplaqObs (N := N) q'
        - ν (iplaqObs (N := N) q') • iplaqObs (N := N)
            (MassGap.LatticeReflection.ireflPlaq τ c q)
        - ν (iplaqObs (N := N) q) • iplaqObs (N := N) q'
        + (ν (iplaqObs (N := N) q) * ν (iplaqObs (N := N) q')) • 1 := by
    ext U
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [hA, hprod, ν.map_add, ν.map_sub, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_smul,
    ν.map_one]
  ring

#print axioms pairing_iplaqObs_eq_connected

/-- **The reflected, mean-subtracted pairing is a connected correlator — for ANY observable.**

`pairing_iplaqObs_eq_connected` is this statement for two single plaquette observables. Reading its
proof, only one step mentions plaquettes at all: rewriting `ireflObs τ c (iplaqObs q)`. Everything
else is the expansion of a product of two mean-subtracted observables and the linearity of the
state, so it generalises with the plaquette structure removed.

Generalising also shows what the special case did not need. `pairing_iplaqObs_eq_connected` takes a
reflection-invariance hypothesis on the state; this does not, because the two `ν f` terms cancel in
the expansion. What survives is `ν (ireflObs τ c f)`, kept as it stands rather than converted to
`ν f` — which is exactly the conversion that hypothesis was spent on.

DERIVED: `4` is the spacetime dimension, indexing the reflection's direction; `1` is the unit
observable carrying the subtracted means. -/
theorem pairing_eq_connected (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N)))
    (f g : C(MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N), ℝ)) :
    ν (MassGap.LatticeReflection.ireflObs τ c (f - ν f • 1) * (g - ν g • 1))
      = ν (MassGap.LatticeReflection.ireflObs τ c f * g)
        - ν (MassGap.LatticeReflection.ireflObs τ c f) * ν g := by
  have hA : MassGap.LatticeReflection.ireflObs τ c (f - ν f • 1)
      = MassGap.LatticeReflection.ireflObs τ c f - ν f • 1 := by
    rw [map_sub, map_smul, ireflObs_one]
  have hprod : (MassGap.LatticeReflection.ireflObs τ c f - ν f • 1) * (g - ν g • 1)
      = MassGap.LatticeReflection.ireflObs τ c f * g
        - ν g • MassGap.LatticeReflection.ireflObs τ c f
        - ν f • g
        + (ν f * ν g) • 1 := by
    ext U
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [hA, hprod, ν.map_add, ν.map_sub, ν.map_sub, ν.map_smul, ν.map_smul, ν.map_smul,
    ν.map_one]
  ring

#print axioms pairing_eq_connected

/-- **A finite-volume bound on the mean-subtracted pairing reaches the limiting state.**

This closes the box-to-limit step. The obstacle was that the mean-subtracted observable is not
fixed: its means are taken in the finite-volume state, so it moves with the box and no bound on it
is a bound on a fixed observable. `pairing_eq_connected` removes that — it rewrites the pairing at
ANY state into the connected form `state (θ x · y) − state (θ x) · state y`, whose value is a
convergent combination of one- and two-point functions — and
`DLRLimit.abs_connected_le_of_eventually` transports exactly that shape.

Stated over an arbitrary family of states along an arbitrary filter, so the `stateFree` family over
an exhausting sequence of boxes instantiates it; the bound `C` must not depend on the index, which is
the volume-uniformity `coreConst` and `coreRate` already have.

DERIVED: `4` is the spacetime dimension, indexing the reflection's direction; `1` is the unit
observable carrying the subtracted means. -/
theorem nu_pairing_abs_le_of_eventually {ι : Type*} {l : Filter ι} [l.NeBot]
    (μ : ι → MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N)))
    (ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun i => μ i f) l (nhds (ν f)))
    (τ : Fin 4) (c : ℤ)
    (x y : C(MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N), ℝ)) (C : ℝ)
    (h : ∀ᶠ i in l, |μ i (MassGap.LatticeReflection.ireflObs τ c (x - μ i x • 1)
        * (y - μ i y • 1))| ≤ C) :
    |ν (MassGap.LatticeReflection.ireflObs τ c x * y)
      - ν (MassGap.LatticeReflection.ireflObs τ c x) * ν y| ≤ C := by
  refine MassGap.DLRLimit.abs_connected_le_of_eventually htend
    (MassGap.LatticeReflection.ireflObs τ c x) y C ?_
  filter_upwards [h] with i hi
  rwa [pairing_eq_connected τ c (μ i) x y] at hi

#print axioms nu_pairing_abs_le_of_eventually

/-- **The reflection of a product of plaquette observables is the product over reflected
plaquettes.** `ireflObs` is precomposition, so it commutes with a finite product pointwise;
`ContinuousMap.prod_apply` evaluates the product and `ireflObs_iplaqObs` moves each factor.

`ireflObs` is bundled only as a linear map, so `map_prod` does not apply and this is proved by
extensionality instead.

DERIVED: `4` is the spacetime dimension, indexing the reflection's direction. -/
theorem ireflObs_prod_iplaqObs (τ : Fin 4) (c : ℤ) (A : Finset MassGap.GibbsSpec.IPlaq) :
    MassGap.LatticeReflection.ireflObs τ c (∏ q ∈ A, iplaqObs (N := N) q)
      = ∏ q ∈ A, iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q) := by
  ext U
  simp only [MassGap.LatticeReflection.ireflObs_apply, ContinuousMap.prod_apply]
  exact Finset.prod_congr rfl fun q _ =>
    DFunLike.congr_fun (ireflObs_iplaqObs (N := N) τ c q) U

#print axioms ireflObs_prod_iplaqObs

/-- **The reflected pairing of two PRODUCTS of plaquette observables is a connected correlator.**

The family counterpart of `pairing_iplaqObs_eq_connected`, and one of the two halves the family
route needed. `pairing_eq_connected` does the algebra and `ireflObs_prod_iplaqObs` identifies the
reflected product; neither step knows anything about the box.

The other half is `stateFree_connectedF_eq_wilsonCorrConnF`, which identifies the right-hand side
with `WilsonBridge.wilsonCorrConnF` at the box carrier —
`StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow` then bounds it geometrically. Joining
the two at a box needs the reflected plaquettes to lie in that box, which is a hypothesis about the
box's symmetry and is not discharged here.

DERIVED: `4` is the spacetime dimension; `1` is the unit observable carrying the subtracted means. -/
theorem pairing_iplaqObsF_eq_connected (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf (MassGap.SUN.SU N)))
    (A B : Finset MassGap.GibbsSpec.IPlaq) :
    ν (MassGap.LatticeReflection.ireflObs τ c
          ((∏ q ∈ A, iplaqObs (N := N) q) - ν (∏ q ∈ A, iplaqObs (N := N) q) • 1)
        * ((∏ q ∈ B, iplaqObs (N := N) q) - ν (∏ q ∈ B, iplaqObs (N := N) q) • 1))
      = ν ((∏ q ∈ A, iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q))
            * ∏ q ∈ B, iplaqObs (N := N) q)
        - ν (∏ q ∈ A, iplaqObs (N := N) (MassGap.LatticeReflection.ireflPlaq τ c q))
          * ν (∏ q ∈ B, iplaqObs (N := N) q) := by
  rw [pairing_eq_connected τ c ν, ireflObs_prod_iplaqObs]

#print axioms pairing_iplaqObsF_eq_connected

/-- **The reflection of a box family's product, as a product over a box family.**

`ireflObs_prod_iplaqObs` sends a product over plaquettes to the product over their reflections, but
leaves the index type as bare plaquettes. To meet `stateFree_connectedF_eq_wilsonCorrConnF`, whose
families are drawn from the box, the reflected family must itself be a box family.

`ρ` carries exactly that: a map of the box's plaquettes to itself which `hρ` proves is the
reflection. A symmetric box supplies one; nothing here assumes the box is symmetric, it just names
what is needed. `hinj` is injectivity, which `ireflPlaq` being involutive gives.

DERIVED: `4` is the spacetime dimension, indexing the reflection's direction. -/
theorem ireflObs_prod_iplaqObs_box (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ρ : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ) → ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (hρ : ∀ q, (ρ q : MassGap.GibbsSpec.IPlaq)
      = MassGap.LatticeReflection.ireflPlaq τ c (q : MassGap.GibbsSpec.IPlaq))
    (hinj : Function.Injective ρ)
    (Ao : Finset ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.LatticeReflection.ireflObs τ c
        (∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
      = ∏ q ∈ Ao.image ρ, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq) := by
  rw [Finset.prod_image (fun x _ y _ h => hinj h)]
  ext U
  simp only [MassGap.LatticeReflection.ireflObs_apply, ContinuousMap.prod_apply]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [hρ q]
  exact DFunLike.congr_fun (ireflObs_iplaqObs (N := N) τ c (q : MassGap.GibbsSpec.IPlaq)) U

#print axioms ireflObs_prod_iplaqObs_box

/-- **The reflected pairing of two box families IS `wilsonCorrConnF` at the box carrier.**

The join. `pairing_eq_connected` does the algebra with no plaquette structure and no reflection
invariance; `ireflObs_prod_iplaqObs_box` moves the reflection onto the index family; and
`stateFree_connectedF_eq_wilsonCorrConnF` identifies the result at the box.

**This is the gap obligation's own expression, at families, equal to the object strong coupling
bounds.** `StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow` applies to the right-hand
side directly.

DERIVED: `0` and `2` are `wilsonDensity`'s range, carried as `stateFree` takes them; `4` is the
spacetime dimension; `1` is the unit observable carrying the subtracted means. -/
theorem stateFree_pairingF_eq_wilsonCorrConnF
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (τ : Fin 4) (c : ℤ)
    (ρ : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ) → ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (hρ : ∀ q, (ρ q : MassGap.GibbsSpec.IPlaq)
      = MassGap.LatticeReflection.ireflPlaq τ c (q : MassGap.GibbsSpec.IPlaq))
    (hinj : Function.Injective ρ)
    (Ao Bo : Finset ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)) :
    MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ c
            ((∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)) • 1)
          * ((∏ q ∈ Bo, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (∏ q ∈ Bo, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)) • 1))
      = MassGap.WilsonBridge.wilsonCorrConnF (Nc := N)
          (MassGap.ReflectionHalfSpace.boxBd Λ) (Ao.image ρ) β Bo := by
  rw [pairing_eq_connected τ c _, ireflObs_prod_iplaqObs_box τ c Λ ρ hρ hinj Ao,
    stateFree_connectedF_eq_wilsonCorrConnF hφ0 hφ2 β Λ ω (Ao.image ρ) Bo]

#print axioms stateFree_pairingF_eq_wilsonCorrConnF

/-- **The reflected pairing of two plaquette FAMILIES decays geometrically.**

The family counterpart of `stateFree_pairing_abs_le`, and the completion of the family route.
`stateFree_pairingF_eq_wilsonCorrConnF` rewrites the gap obligation's own expression as
`WilsonBridge.wilsonCorrConnF` at the box carrier;
`StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow` bounds that geometrically. Nothing
else happens here — the content is in those two.

The advance over `stateFree_pairing_abs_le` is that `Ao` and `Bo` are families rather than single
plaquettes, so the estimate reaches products of plaquette observables, which is what a
gauge-invariant observable of any extent is built from. `GaugeInvariantAlgebra.gapEntry` is stated
over such a family, so this is the shape its off-diagonal entries need.

`ρ` is the reflection acting on the box's own plaquettes, which a box symmetric about the plane
supplies. `hconnA` and `hconnB` ask each family to be internally touch-connected, which is what a
Wilson loop is. `hr` is the strong-coupling condition, and it is the one place a coupling
restriction enters this chain.

DERIVED: `0` is the coupling's lower end and `2` is `wilsonDensity`'s upper one, both carried as
`stateFree` takes them; `2` is also the two anchor plaquettes, the smallest separation a core can
span; `1` is `coreRate`'s convergence threshold and the unit observable carrying the subtracted
means; `4` is the spacetime dimension, indexing the reflection's direction. -/
theorem stateFree_pairingF_abs_le (hN : N ≠ 0)
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (τ : Fin 4) (c : ℤ)
    (ρ : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ) → ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (hρ : ∀ q, (ρ q : MassGap.GibbsSpec.IPlaq)
      = MassGap.LatticeReflection.ireflPlaq τ c (q : MassGap.GibbsSpec.IPlaq))
    (hinj : Function.Injective ρ)
    (Ao Bo : Finset ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (hod : Disjoint (Ao.image ρ) Bo)
    {a b : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ)} (ha : a ∈ Ao.image ρ) (hb : b ∈ Bo)
    (hconnA : ∀ p ∈ Ao.image ρ,
      MassGap.StrongCoupling.Reach (MassGap.ReflectionHalfSpace.boxBd Λ) (Ao.image ρ) a p)
    (hconnB : ∀ p ∈ Bo,
      MassGap.StrongCoupling.Reach (MassGap.ReflectionHalfSpace.boxBd Λ) Bo b p)
    (hint : ∀ D E : Finset ↥(MassGap.ReflectionHalfSpace.iplqAll Λ), MeasureTheory.Integrable
      (fun U => (∏ p ∈ D, MassGap.WilsonReal.wilsonPlaqObs (N := N)
            (MassGap.ReflectionHalfSpace.boxBd Λ) p U)
        * ∏ p ∈ E, (Real.exp (-(β * MassGap.WilsonAction.wilsonDensity
            (MassGap.WilsonLattice.wilsonHol (MassGap.ReflectionHalfSpace.boxBd Λ) p U))) - 1))
      (MeasureTheory.Measure.pi fun _ => MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)))
    (hr : MassGap.StrongCoupling.coreRate
      (MassGap.StrongCoupling.touchDeg (MassGap.ReflectionHalfSpace.boxBd Λ)) β < 1)
    (k : ℕ) (hu : ((Ao.image ρ) ∪ Bo).card ≤ k + 2)
    (hlow : ∀ x ∈ MassGap.StrongCoupling.corePairsF
        (MassGap.ReflectionHalfSpace.boxBd Λ) a (Ao.image ρ) Bo,
      k + 2 ≤ (MassGap.StrongCoupling.coreSpanF (Ao.image ρ) Bo x).card) :
    |MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ c
            ((∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (∏ q ∈ Ao, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)) • 1)
          * ((∏ q ∈ Bo, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (∏ q ∈ Bo, iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)) • 1))|
      ≤ MassGap.StrongCoupling.coreConstF
          (MassGap.StrongCoupling.touchDeg (MassGap.ReflectionHalfSpace.boxBd Λ)) β
          (Ao.image ρ).card Bo.card ((Ao.image ρ) ∪ Bo).card
        * MassGap.StrongCoupling.coreRate
            (MassGap.StrongCoupling.touchDeg (MassGap.ReflectionHalfSpace.boxBd Λ)) β
            ^ (k + 2 - ((Ao.image ρ) ∪ Bo).card) := by
  rw [stateFree_pairingF_eq_wilsonCorrConnF hφ0 hφ2 β Λ ω τ c ρ hρ hinj Ao Bo]
  exact MassGap.StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow hN
    (MassGap.ReflectionHalfSpace.boxBd Λ) (Ao.image ρ) Bo hod ha hb hconnA hconnB hβ hint hr k
    hu hlow

#print axioms stateFree_pairingF_abs_le

/-- **The reflected pairing of two plaquette observables decays geometrically.**

This composes the three links: `pairing_iplaqObs_eq_connected` makes the reflected, mean-subtracted
pairing a connected correlator; `stateFree_connected_eq_wilsonCorrConn` identifies that with
`WilsonBridge.wilsonCorrConn` at the box carrier; and
`ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le` bounds it by `coreConst · coreRate ^ k`, uniformly
in the box since `touchDeg_boxBd_le` carries no box dependence.

**This is the gap obligation's own expression with a strong-coupling bound on it.**
`ReflectionHalfSpace.ireflPlaq_maps_plus_to_minus` is why the bound has force: the reflected plaquette
sits in the opposite half, so the boundary-word separation `k` grows with the reflection depth, and
the factor is raised to it.

`hinv` is reflection invariance of the box state — a real hypothesis, true when the box is symmetric
about the plane, which is what the `symCube` families are built to be. `hrefl` asks the reflected
plaquette to lie in the box, which `ireflPlaq_mem_plaqsIn` supplies for a symmetric one.

Scope: two SINGLE plaquettes. `GaugeInvariantAlgebra.gapEntry` is stated over a spanning family, and
`WilsonBridge.wilsonCorrConnF` — the `Finset` version, products of plaquettes — has no geometric bound
yet. That is the cluster expansion, and it is not this.

DERIVED: `16 * 4` is `touchDeg_boxBd_le`'s bound, transcribed; `0` and `2` are `wilsonDensity`'s
range and the coupling's lower end; `1` is `coreRate`'s convergence threshold; `4` is the spacetime
dimension. -/
theorem stateFree_pairing_abs_le (hN : N ≠ 0)
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (τ : Fin 4) (c : ℤ)
    (hinv : ∀ f, MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ c f)
      = MassGap.ReflectionHalfSpace.stateFree
          MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω f)
    (q q' : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (hrefl : MassGap.LatticeReflection.ireflPlaq τ c (q : MassGap.GibbsSpec.IPlaq)
      ∈ MassGap.ReflectionHalfSpace.iplqAll Λ)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (k : ℕ)
    (hk : q' ∉ MassGap.StrongCoupling.ball (MassGap.ReflectionHalfSpace.boxBd Λ)
      ⟨MassGap.LatticeReflection.ireflPlaq τ c (q : MassGap.GibbsSpec.IPlaq), hrefl⟩ k) :
    |MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ c
            (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)) • 1)
          * (iplaqObs (N := N) (q' : MassGap.GibbsSpec.IPlaq)
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (iplaqObs (N := N) (q' : MassGap.GibbsSpec.IPlaq)) • 1))|
      ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
        * MassGap.StrongCoupling.coreRate (16 * 4) β ^ k := by
  rw [pairing_iplaqObs_eq_connected τ c _ hinv (q : MassGap.GibbsSpec.IPlaq)
      (q' : MassGap.GibbsSpec.IPlaq),
    stateFree_connected_eq_wilsonCorrConn hφ0 hφ2 β Λ ω
      ⟨MassGap.LatticeReflection.ireflPlaq τ c (q : MassGap.GibbsSpec.IPlaq), hrefl⟩ q']
  exact MassGap.ReflectionHalfSpace.wilsonCorrConn_boxBd_abs_le hN Λ _ q' hβ hr k hk

#print axioms stateFree_pairing_abs_le

/-- **The reflected pairing of a plaquette observable with its own TRANSLATE decays geometrically in
the translation.**

`stateFree_pairing_abs_le` places no relation between its two plaquettes, so the second may be the
`m`-fold translate of the first; `ReflectionHalfSpace.not_mem_ball_of_irefl_shift` then discharges
its separation hypothesis, because a plaquette at `τ`-height at or above the plane reflects to `2p −
h` and translates to `h + m`, putting the two at axis distance at least `m`.

`hq` is that height condition, and it is what `p` is for: the plaquette must lie in the positive
half, which is where the half-space algebra's members live.

DERIVED: `16 * 4` is `touchDeg_boxBd_le`'s bound on the box word's touch degree, transcribed; `2` is
the reflection plane's spacing in lattice units; `4` is the spacetime dimension; `0` is the
coupling's lower end; `1` is the unit observable and `coreRate`'s convergence threshold. -/
theorem stateFree_pairing_shift_abs_le (hN : N ≠ 0)
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (τ : Fin 4) (p : ℤ)
    (hinv : ∀ f, MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ (2 * p) f)
      = MassGap.ReflectionHalfSpace.stateFree
          MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω f)
    (q : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (hq : p ≤ (q : MassGap.GibbsSpec.IPlaq).2 τ)
    (hrefl : MassGap.LatticeReflection.ireflPlaq τ (2 * p) (q : MassGap.GibbsSpec.IPlaq)
      ∈ MassGap.ReflectionHalfSpace.iplqAll Λ)
    (m : ℕ)
    (hshift : (MassGap.InfiniteShift.ishiftPlaq τ)^[m] (q : MassGap.GibbsSpec.IPlaq)
      ∈ MassGap.ReflectionHalfSpace.iplqAll Λ)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (k : ℕ) (hk : k < m) :
    |MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)) • 1)
          * (iplaqObs (N := N)
                ((MassGap.InfiniteShift.ishiftPlaq τ)^[m] (q : MassGap.GibbsSpec.IPlaq))
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (iplaqObs (N := N)
                    ((MassGap.InfiniteShift.ishiftPlaq τ)^[m]
                      (q : MassGap.GibbsSpec.IPlaq))) • 1))|
      ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
        * MassGap.StrongCoupling.coreRate (16 * 4) β ^ k :=
  stateFree_pairing_abs_le hN hφ0 hφ2 hβ Λ ω τ (2 * p) hinv q
    ⟨(MassGap.InfiniteShift.ishiftPlaq τ)^[m] (q : MassGap.GibbsSpec.IPlaq), hshift⟩
    hrefl hr k
    (MassGap.ReflectionHalfSpace.not_mem_ball_of_irefl_shift Λ τ p
      (q : MassGap.GibbsSpec.IPlaq) hq m k hk hrefl hshift)

#print axioms stateFree_pairing_shift_abs_le

/-- **The same bound, with the translate written as an iterated shift observable.**

`ishiftObsL_iterate_iplaqObs` rewrites the translated plaquette's observable as the shift applied
`m` times to the original's. **This is the shape the obligation has**:
`ClayCapstone.gaugeInv_clay_gap_of_state_decay` asks for a bound on
`ν (ireflObs τ (2 * p) x · (ishiftObsL τ)^[2 * n] x)`, and at `x` a plaquette observable this is
that quantity, at `stateFree` on a box and with the means subtracted.

Two differences from the obligation remain, and neither is closed here: this is at `stateFree` on a
finite box rather than at the limiting state `ν`, and it carries the means subtracted explicitly
where the obligation gets them from the vacuum complement.
`DLRLimit.abs_le_of_eventually_abs_le` is the tool for the first.

DERIVED: `16 * 4` is `touchDeg_boxBd_le`'s bound on the box word's touch degree, transcribed; `2` is
the reflection plane's spacing in lattice units; `4` is the spacetime dimension; `0` is the
coupling's lower end; `1` is the unit observable and `coreRate`'s convergence threshold. All are
`stateFree_pairing_shift_abs_le`'s, unchanged. -/
theorem stateFree_pairing_shiftObs_abs_le (hN : N ≠ 0)
    (hφ0 : ∀ g : MassGap.SUN.SU N, 0 ≤ MassGap.WilsonAction.wilsonDensity g)
    (hφ2 : ∀ g : MassGap.SUN.SU N, MassGap.WilsonAction.wilsonDensity g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (τ : Fin 4) (p : ℤ)
    (hinv : ∀ f, MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ (2 * p) f)
      = MassGap.ReflectionHalfSpace.stateFree
          MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω f)
    (q : ↥(MassGap.ReflectionHalfSpace.iplqAll Λ))
    (hq : p ≤ (q : MassGap.GibbsSpec.IPlaq).2 τ)
    (hrefl : MassGap.LatticeReflection.ireflPlaq τ (2 * p) (q : MassGap.GibbsSpec.IPlaq)
      ∈ MassGap.ReflectionHalfSpace.iplqAll Λ)
    (m : ℕ)
    (hshift : (MassGap.InfiniteShift.ishiftPlaq τ)^[m] (q : MassGap.GibbsSpec.IPlaq)
      ∈ MassGap.ReflectionHalfSpace.iplqAll Λ)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (k : ℕ) (hk : k < m) :
    |MassGap.ReflectionHalfSpace.stateFree
        MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
        (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq)) • 1)
          * ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m]
                (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))
              - MassGap.ReflectionHalfSpace.stateFree
                  MassGap.WilsonAction.measurable_wilsonDensity hφ0 hφ2 β Λ ω
                  ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m]
                    (iplaqObs (N := N) (q : MassGap.GibbsSpec.IPlaq))) • 1))|
      ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
        * MassGap.StrongCoupling.coreRate (16 * 4) β ^ k := by
  rw [ishiftObsL_iterate_iplaqObs τ m (q : MassGap.GibbsSpec.IPlaq)]
  exact stateFree_pairing_shift_abs_le hN hφ0 hφ2 hβ Λ ω τ p hinv q hq hrefl m hshift hr k hk

#print axioms stateFree_pairing_shiftObs_abs_le

/-- **The connected reflected-shifted plaquette pairing in the infinite-volume state decays at rate
`coreRate`.**

`ν` is the `atTop` limit of the free box states along `ReflectionHalfSpace.mixCube`. Along its even
members — the reflection-symmetric boxes `ReflectionHalfSpace.symCube` — the box states are reflection
invariant (`ReflectionHalfSpace.stateFree_symCube_reflection_invariant` at the identity boundary,
fixed by `ReflectionHalfSpace.ireflConf_one`), and a plaquette, its mirror and its `m`-th translate
all lie in the box eventually (`ReflectionHalfSpace.eventually_mem_iplqAll_refl_shift`). There
`stateFree_pairing_shiftObs_abs_le` bounds the box pairing, and `nu_pairing_abs_le_of_eventually`
carries the bound to `ν`, where the mean subtraction becomes the connected form.

The bound is `coreConst · coreRateᵏ` for every `k < m`, uniform in the volume: the touch degree
`16 · 4` is the only lattice quantity in it.

DERIVED: `16 * 4` is the touch degree of the four-dimensional box, `16` plaquettes per link per
dimension; `2` is the doubling of the reflection plane and of the even box index; `1` is the identity
boundary configuration; `0` is the lower bound on `β` and the excluded rank in `hN`. -/
theorem nu_connected_shift_abs_le (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (q : MassGap.GibbsSpec.IPlaq) (hqd : q.1.1 ≠ q.1.2) (hq : p ≤ q.2 τ) (m k : ℕ) (hk : k < m) :
    |ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (iplaqObs (N := N) q)
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] (iplaqObs (N := N) q))
      - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (iplaqObs (N := N) q))
          * ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] (iplaqObs (N := N) q))|
      ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
        * MassGap.StrongCoupling.coreRate (16 * 4) β ^ k := by
  have htendS := MassGap.ReflectionHalfSpace.tendsto_symCube_even_of_mixCube τ p hN β ν htend
  refine nu_pairing_abs_le_of_eventually (l := Filter.atTop)
    (fun n => MassGap.ReflectionHalfSpace.stateFree (φ := MassGap.WilsonAction.wilsonDensity)
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β
      (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) 1)
    ν htendS τ (2 * p) (iplaqObs (N := N) q)
    ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] (iplaqObs (N := N) q)) _ ?_
  have hdouble : Filter.Tendsto (fun j : ℕ => 2 * j) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have hev := hdouble.eventually
    (MassGap.ReflectionHalfSpace.eventually_mem_iplqAll_refl_shift τ p q hqd m)
  filter_upwards [hev] with n hn
  simp only [MassGap.ReflectionHalfSpace.mixCube_even] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  exact stateFree_pairing_shiftObs_abs_le hN (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) hβ
    (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) 1 τ p
    (fun f => MassGap.ReflectionHalfSpace.stateFree_symCube_reflection_invariant hN τ (2 * p) n β
      (MassGap.ReflectionHalfSpace.ireflConf_one τ (2 * p)) f)
    ⟨q, h1⟩ hq h2 m h3 hr k hk

#print axioms nu_connected_shift_abs_le

/-! ### The pairing as a connected correlator

`pairing_iplaqObs_eq_connected` states the identity for single plaquettes and
`pairing_iplaqObsF_eq_connected` for families, both over the observable-generic
`pairing_eq_connected`. `stateFree_connected_eq_wilsonCorrConn` and
`stateFree_connectedF_eq_wilsonCorrConnF` identify the result with `WilsonBridge.wilsonCorrConn`
and `wilsonCorrConnF` at the box carrier, and `stateFree_pairing_abs_le` and
`stateFree_pairingF_abs_le` compose those with the strong-coupling estimates.

`ReflectionHalfSpace.ireflPlaq_maps_plus_to_minus` is why the bound has force: the reflected
plaquette sits in the opposite half, so the separation the geometric factor is raised to grows with
the reflection depth. -/


end Constructed

/-- **The transfer data on the gauge-invariant algebra.**

`TransferAssembly.assembleTransferData` takes the algebra as an argument, so nothing in the
construction has to be rewritten. Six of its nine inputs are shared with
`WilsonTransferReduction.transferData_of_state_facts` and carry over unchanged — the shift
compatibility, the unit's image, and the two norm bounds. The algebra-specific three are
`reflPositiveOn_gaugeInv`, which RESTRICTS reflection positivity from `halfSpaceAlg` rather than
re-proving it, `gaugeInvHalfSpaceAlg_shift_stable`, and `one_mem_gaugeInvHalfSpaceAlg`.

**Why this data and not the other.** `transferData_of_state_facts` builds on `halfSpaceAlg`, a
locality predicate that contains `HalfSpaceAlgebra.halfLinkObs l f` — an arbitrary continuous
function of a single link variable. A `GapAt` bound there must hold for observables that are not
gauge invariant, while `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` bounds a
plaquette-pair correlator. On this algebra that mismatch is gone.

The hypothesis is `hpos` on the LARGER algebra, since that is the form the tree produces.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`,
`ReflectionHalfSpace`'s own index convention. -/
noncomputable def gaugeInvTransferData (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) :
    MassGap.Transfer.TransferData ↑↑(gaugeInvHalfSpaceAlg (G := G) τ p) :=
  MassGap.TransferAssembly.assembleTransferData
    (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν
    (gaugeInvHalfSpaceAlg (G := G) τ p) hinv (reflPositiveOn_gaugeInv τ p hpos)
    (MassGap.WilsonTransferReduction.shiftCompat_of_nu_T τ (2 * p) ν hnu)
    (fun _ hf => gaugeInvHalfSpaceAlg_shift_stable τ p hf)
    (one_mem_gaugeInvHalfSpaceAlg τ p)
    (MassGap.WilsonTransferReduction.ishiftObsL_one τ)
    (MassGap.WilsonTransferReduction.norm_ishiftObsL_le τ)
    (MassGap.WilsonTransferReduction.norm_ireflObs_le τ (2 * p))

#print axioms gaugeInvTransferData

/-- **Shift invariance iterates.** A state invariant under one step is invariant under `n`.

DERIVED: `4` is the spacetime dimension, the range of the direction index. -/
theorem state_iterate_shift_eq (ν : MassGap.DLRLimit.State (IConf G)) (τ : Fin 4)
    (hnu : ∀ f : C(IConf G, ℝ), ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) (n : ℕ)
    (f : C(IConf G, ℝ)) :
    ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[n] f) = ν f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, hnu]

#print axioms state_iterate_shift_eq

/-- **The shift commutes with mean subtraction**: it is linear and fixes the constant `1`
(`WilsonTransferReduction.ishiftObsL_one`).

DERIVED: `1` is the constant observable; `4` is the spacetime dimension, the range of the direction
index. -/
theorem iterate_shift_sub_smul_one (τ : Fin 4) (n : ℕ) (f : C(IConf G, ℝ)) (c : ℝ) :
    (⇑(MassGap.ReflectionShift.ishiftObsL (G := G) τ))^[n] (f - c • 1)
      = (⇑(MassGap.ReflectionShift.ishiftObsL (G := G) τ))^[n] f - c • 1 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_sub, map_smul,
      MassGap.WilsonTransferReduction.ishiftObsL_one, ih]

#print axioms iterate_shift_sub_smul_one

/-- **The gauge-invariant transfer form at a translated observable, as a state pairing.**

`gaugeInvTransferData` is `TransferAssembly.assembleTransferData` at the lattice reflection and the
lattice shift, so `assembleTransferData_form_pow` specialises directly: the form of `x` against `x`
translated `n` steps is the state's pairing of `ireflObs τ (2 * p) x` with `(ishiftObsL τ)^[n] x`.

Nothing of the GNS construction survives on the right — it is the state, the reflection and the
shift.

DERIVED: `2` is the reflection plane's spacing in lattice units, carried from
`gaugeInvTransferData`; `4` is the spacetime dimension indexing the direction; `n` is the caller's.
-/
theorem gaugeInv_form_pow (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (x : ↥(gaugeInvHalfSpaceAlg (G := G) τ p)) (n : ℕ) :
    (gaugeInvTransferData τ p ν hinv hpos hnu).form x
        (((gaugeInvTransferData τ p ν hinv hpos hnu).T ^ n) x)
      = ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (x : C(IConf G, ℝ))
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[n] (x : C(IConf G, ℝ))) :=
  MassGap.TransferAssembly.assembleTransferData_form_pow _ _ _ _ _ _ _ _ _ _ _ x n

#print axioms gaugeInv_form_pow

/-- **Positivity restricts too.** `GNSHilbert.PositiveTransfer D` is `∀ x, 0 ≤ D.form x (D.T x)`,
quantified over the algebra, and both transfer data compute that number the same way — the form is
`ν (θ ↑x * ↑y)` and the shift is applied to the underlying continuous map, neither depending on which
algebra the element is taken from. So an element of the invariant algebra, viewed in the larger one,
has the same value and the bound transports.

With `reflPositiveOn_gaugeInv` this is the second hypothesis this route gets for free from the
`halfSpaceAlg` development, leaving `TransferGap.GapAt` below one as the only input — and that one is
now asked on an algebra with no arbitrary single-link observables in it.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`; `0` is
positivity's own threshold. -/
theorem positiveTransfer_gaugeInv (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (hP : MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu)) :
    MassGap.GNSHilbert.PositiveTransfer (gaugeInvTransferData τ p ν hinv hpos hnu) :=
  fun x => hP ⟨(x : C(IConf G, ℝ)), gaugeInvHalfSpaceAlg_le τ p x.2⟩

#print axioms positiveTransfer_gaugeInv

/-- **The gap restricts as well, and that is the point of the route.**
`TransferGap.GapAt D r` is universally quantified over the algebra, so the invariant algebra inherits
it from the locality one. Both transfer data compute the form and the shift on the underlying
continuous map, so the inequality at an invariant element is the same inequality.

The direction matters. This does not help prove the gap — it says the demand on the smaller algebra
is **weaker**, which is exactly why the route was taken: `GapAt` there quantifies over no
`HalfSpaceAlgebra.halfLinkObs l f`, no arbitrary continuous function of a single link variable, and
those were what no plaquette-pair bound could reach.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p` and the
exponent in `GapAt`'s own statement. -/
theorem gapAt_gaugeInv_of_gapAt (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    {r : ℝ}
    (hg : MassGap.TransferGap.GapAt
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu) r) :
    MassGap.TransferGap.GapAt (gaugeInvTransferData τ p ν hinv hpos hnu) r :=
  fun x hx => hg ⟨(x : C(IConf G, ℝ)), gaugeInvHalfSpaceAlg_le τ p x.2⟩ hx

#print axioms gapAt_gaugeInv_of_gapAt

/-- **`GapAt` on the invariant algebra, as a pairing inequality.** The form the finite-volume work
produces, at the gauge-invariant transfer data.

`WilsonTransferReduction` reaches the same shape for `halfSpaceAlg` in three steps —
`gapAt_iff_pairing`, `gapAt_iff_pairing_of_mean_zero`, `gapAt_iff_subtracted_pairing` — and each
touches the algebra only through the quantifier and through membership of `1`. The one substantive
ingredient, `gapAt_pairing_eq`, is a statement about observables and takes no algebra at all. So the
chain generalises, and this is it in one theorem.

Reading it: `GapAt` holds exactly when every mean-subtracted invariant observable's reflected pairing
at depth `2p−2` is at most `r²` times its pairing at depth `2p`. Moving the reflection plane out by
two must cost a factor `r²` — that is the gap, in the coordinates the box family works in.

**This is the last structural piece.** With an `hfin` quantified over gauge-invariant observables,
`InfiniteReflection.connected_pairing_le_of_eventually` — which takes the algebra as an argument —
supplies the right-hand side, and `ClayCapstone.gaugeInv_clay_gap_of_gapAt` turns the result into the
mass gap.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`, the two
planes' separation in `2 * p - 2`, and the exponent in `GapAt`'s own statement; `1` is the unit
observable; `0` is the mean the subtraction produces. -/
theorem gaugeInv_gapAt_iff_subtracted_pairing (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(IConf G, ℝ), ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) (r : ℝ) :
    MassGap.TransferGap.GapAt (gaugeInvTransferData τ p ν hinv hpos hnu) r
      ↔ ∀ F ∈ gaugeInvHalfSpaceAlg (G := G) τ p,
          ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
            ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F - ν F • 1)
              * (F - ν F • 1)) := by
  have hmean : ∀ F : C(IConf G, ℝ),
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p) F * 1) = ν F := by
    intro F
    rw [mul_one]
    exact hinv F
  have hbase : MassGap.TransferGap.GapAt (gaugeInvTransferData τ p ν hinv hpos hnu) r
      ↔ ∀ F ∈ gaugeInvHalfSpaceAlg (G := G) τ p, ν F = 0 →
          ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) F * F)
            ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) F * F) := by
    constructor
    · intro h F hF hz
      have hx : ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (MassGap.ReflectionShift.ishiftObsL τ F) * MassGap.ReflectionShift.ishiftObsL τ F)
          ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) F * F) :=
        h ⟨F, hF⟩ (by
          show ν (MassGap.LatticeReflection.ireflObs τ (2 * p) F * 1) = 0
          rw [hmean]
          exact hz)
      rwa [MassGap.WilsonTransferReduction.gapAt_pairing_eq τ (2 * p) ν hnu F] at hx
    · intro h x hvac
      have hx := h (x : C(IConf G, ℝ)) x.2 (by rw [← hmean]; exact hvac)
      rw [← MassGap.WilsonTransferReduction.gapAt_pairing_eq τ (2 * p) ν hnu
        (x : C(IConf G, ℝ))] at hx
      exact hx
  rw [hbase]
  constructor
  · intro h F hF
    exact h _ (Submodule.sub_mem _ hF
        (Submodule.smul_mem _ _ (one_mem_gaugeInvHalfSpaceAlg τ p)))
      (by rw [ν.map_sub, ν.map_smul, ν.one']; ring)
  · intro h F hF hz
    have hsub : F - ν F • (1 : C(IConf G, ℝ)) = F := by
      rw [hz]
      simp
    have hFF := h F hF
    rwa [hsub] at hFF

#print axioms gaugeInv_gapAt_iff_subtracted_pairing

/-! ### Checking on a spanning set -/

/-- **A property of every finite combination of a spanning set holds on the whole span.**

This is the shape the remaining obligation has to be attacked in. `TransferGap.GapAt` is QUADRATIC in
the observable, so a bound proved for plaquette observables does **not** extend to their span by
linearity — which is exactly what stopped
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow`, a plaquette-pair bound, from reaching
it. What does extend is a bound checked on finite linear combinations, and for a quadratic form that
is a **Gram-matrix condition**: over any finite family of plaquette observables, the depth-`2p−2`
Gram matrix dominated by `r²` times the depth-`2p` one. Entry by entry that is a two-plaquette
connected correlator, which is what the strong-coupling machinery bounds.

`Submodule.mem_span_set'` is the entire proof — every element of a span is a finite combination — so
this is a change of quantifier, not new mathematics. Its value is that it names the right quantifier.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
theorem forall_span_of_forall_finite_combination {S : Set C(IConf G, ℝ)}
    (Pr : C(IConf G, ℝ) → Prop)
    (hS : ∀ (n : ℕ) (c : Fin n → ℝ) (F : Fin n → C(IConf G, ℝ)), (∀ i, F i ∈ S) →
      Pr (∑ i, c i • F i)) :
    ∀ F ∈ Submodule.span ℝ S, Pr F := by
  intro F hF
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hF
  have := hS n c (fun i => (g i : C(IConf G, ℝ))) (fun i => (g i).2)
  rwa [hsum] at this

#print axioms forall_span_of_forall_finite_combination

/-- **The pairing inequality, reduced to a Gram condition on a spanning set.**

If the invariant algebra is spanned by `S` — plaquette observables, say — then
`gaugeInv_gapAt_iff_subtracted_pairing`'s hypothesis follows from the same inequality checked on
finite combinations of `S`. For a fixed finite family that is a matrix inequality between the two
reflected Gram matrices, whose entries are two-observable connected pairings.

The mean subtraction `F ↦ F - ν F • 1` is linear, so it commutes with taking combinations and does
not obstruct the reduction.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`, the two
planes' separation in `2 * p - 2`, and the exponent in the bound; `1` is the unit observable. -/
theorem gaugeInv_pairing_of_spanning (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) {r : ℝ} {S : Set C(IConf G, ℝ)}
    (hspan : gaugeInvHalfSpaceAlg (G := G) τ p = Submodule.span ℝ S)
    (hS : ∀ (n : ℕ) (c : Fin n → ℝ) (F : Fin n → C(IConf G, ℝ)), (∀ i, F i ∈ S) →
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2)
            ((∑ i, c i • F i) - ν (∑ i, c i • F i) • 1)
          * ((∑ i, c i • F i) - ν (∑ i, c i • F i) • 1))
        ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            ((∑ i, c i • F i) - ν (∑ i, c i • F i) • 1)
          * ((∑ i, c i • F i) - ν (∑ i, c i • F i) • 1))) :
    ∀ F ∈ gaugeInvHalfSpaceAlg (G := G) τ p,
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
        ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F - ν F • 1)
          * (F - ν F • 1)) := by
  rw [hspan]
  exact forall_span_of_forall_finite_combination _ hS

#print axioms gaugeInv_pairing_of_spanning

/-- **The reflected pairing expands as a Gram double sum.** `LatticeReflection.ireflObs` is a linear
map and `ν` is linear, so the pairing is bilinear and a combination expands.

`ReflectionStrong.form_sum_sum` is the same step for a `Transfer.PreForm`; this is the version for
the raw pairing at a given depth, which is the shape the obligation is stated on.

DERIVED: `4` is the spacetime dimension. No other numeral occurs. -/
theorem pairing_sum_sum (τ : Fin 4) (c : ℤ) (ν : MassGap.DLRLimit.State (IConf G))
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (F : ι → C(IConf G, ℝ)) :
    ν (MassGap.LatticeReflection.ireflObs τ c (∑ i, a i • F i) * (∑ j, a j • F j))
      = ∑ i, ∑ j, a i * a j * ν (MassGap.LatticeReflection.ireflObs τ c (F i) * F j) := by
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, ν.map_sum, ν.map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

#print axioms pairing_sum_sum

/-- Mean subtraction commutes with taking combinations: it is linear.

So a Gram condition may be stated on the mean-subtracted generators with no loss — the
mean-subtracted combination is the combination of the subtracted generators.

DERIVED: `4` is the spacetime dimension; `1` is the unit observable. -/
theorem sub_mean_sum (ν : MassGap.DLRLimit.State (IConf G))
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (F : ι → C(IConf G, ℝ)) :
    (∑ i, a i • F i) - ν (∑ i, a i • F i) • (1 : C(IConf G, ℝ))
      = ∑ i, a i • (F i - ν (F i) • (1 : C(IConf G, ℝ))) := by
  have hterm : ∀ i, a i • (F i - ν (F i) • (1 : C(IConf G, ℝ)))
      = a i • F i - (a i * ν (F i)) • (1 : C(IConf G, ℝ)) := by
    intro i
    rw [smul_sub, smul_smul]
  simp only [hterm, Finset.sum_sub_distrib, ν.map_sum, ν.map_smul, ← Finset.sum_smul]

#print axioms sub_mean_sum

/-- **The obligation as a Gram-matrix inequality over a spanning set.**

Combining `gaugeInv_pairing_of_spanning` with the two expansions above: it is enough that, over every
finite family drawn from a spanning set and every choice of real coefficients, the depth-`2p−2` Gram
matrix of the mean-subtracted generators is dominated by `r²` times the depth-`2p` one.

**That is a matrix inequality, not an entry-wise one**, and the difference matters:
`ReflectionStrong.pairing_gram_nonneg` and `OSPositivity.wilson_gram_nonneg_monomials` give
positive semidefiniteness of the depth-`2p` Gram matrix on the periodic lattice — the `B` side — and
this needs `r²B − A` semidefinite. Bounds on the entries of `A`, which is what
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` supplies, constrain the entries but do
not by themselves give the form inequality.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`, the two
planes' separation in `2 * p - 2`, and the exponent in the bound; `1` is the unit observable. -/
theorem gaugeInv_pairing_of_gram (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) {r : ℝ} {S : Set C(IConf G, ℝ)}
    (hspan : gaugeInvHalfSpaceAlg (G := G) τ p = Submodule.span ℝ S)
    (hgram : ∀ (n : ℕ) (a : Fin n → ℝ) (F : Fin n → C(IConf G, ℝ)), (∀ i, F i ∈ S) →
      ∑ i, ∑ j, a i * a j * ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2)
            (F i - ν (F i) • 1) * (F j - ν (F j) • 1))
        ≤ r ^ 2 * ∑ i, ∑ j, a i * a j * ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (F i - ν (F i) • 1) * (F j - ν (F j) • 1))) :
    ∀ F ∈ gaugeInvHalfSpaceAlg (G := G) τ p,
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
        ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F - ν F • 1)
          * (F - ν F • 1)) := by
  refine gaugeInv_pairing_of_spanning τ p ν hspan (fun n a F hF => ?_)
  rw [sub_mean_sum ν a F, pairing_sum_sum τ (2 * p - 2) ν a _,
    pairing_sum_sum τ (2 * p) ν a _]
  exact hgram n a F hF

#print axioms gaugeInv_pairing_of_gram

/-! ### From entry bounds to a form inequality -/

/-- **A symmetric, diagonally dominant matrix has a nonnegative quadratic form.**

This is the tool the Gram route is missing. `gaugeInv_pairing_of_gram` needs `r²B − A` positive
semidefinite; what `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` supplies is **bounds
on entries** — off-diagonal connected correlators small. Diagonal dominance is the bridge, and
nothing in this tree had it: `Matrix.PosSemidef` occurs only in the cell modules, and there is no
Gershgorin, no diagonal-dominance and no Schur-complement result anywhere.

Stated on the quadratic form rather than through `Matrix.PosSemidef`, because a double sum over a
finite family is what `pairing_sum_sum` produces and `gaugeInv_pairing_of_gram` consumes.

Dominance is written as `∑ j, offDiag i j ≤ M i i` with the off-diagonal selected by an `if`, rather
than with `Finset.erase`, so that `Finset.sum_comm` applies to the double sum directly and the
symmetry fold needs no set manipulation.

Carrier-free: no lattice, no state, no reflection. It sits here because this is where it is needed.

DERIVED: `0` is the lower bound asserted and the value the diagonal is excluded by; `2` is the
exponent in the arithmetic–geometric mean step. -/
theorem sum_sum_nonneg_of_diagDominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hsymm : ∀ i j, M i j = M j i)
    (hdom : ∀ i, (∑ j, if j = i then (0 : ℝ) else |M i j|) ≤ M i i) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * M i j := by
  classical
  -- termwise: the (i, j) entry is at least the diagonal part minus a symmetric penalty
  have hterm : ∀ i j : ι, (if j = i then c i * c i * M i i else 0)
      - (if j = i then (0 : ℝ) else (c i ^ 2 + c j ^ 2) / 2 * |M i j|)
      ≤ c i * c j * M i j := by
    intro i j
    by_cases h : j = i
    · subst h; simp
    · simp only [h, if_false, sub_zero, zero_sub, neg_le]
      have h1 : -(c i * c j * M i j) ≤ |c i * c j| * |M i j| := by
        rw [← abs_mul]
        exact neg_le_abs _
      have h2 : |c i * c j| ≤ (c i ^ 2 + c j ^ 2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|c i| - |c j|), abs_nonneg (c i), abs_nonneg (c j),
          sq_abs (c i), sq_abs (c j)]
      calc -(c i * c j * M i j) ≤ |c i * c j| * |M i j| := h1
        _ ≤ (c i ^ 2 + c j ^ 2) / 2 * |M i j| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum (fun i _ =>
    Finset.sum_le_sum (fun j _ => hterm i j)))
  -- the penalty folds onto the diagonal by symmetry of `M`
  have hsplit : ∀ i : ι, ∑ j, ((if j = i then c i * c i * M i i else 0)
        - (if j = i then (0 : ℝ) else (c i ^ 2 + c j ^ 2) / 2 * |M i j|))
      = c i ^ 2 * M i i
        - ((∑ j, if j = i then (0 : ℝ) else c i ^ 2 / 2 * |M i j|)
          + ∑ j, if j = i then (0 : ℝ) else c j ^ 2 / 2 * |M i j|) := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i, ← Finset.sum_add_distrib]
    simp only [Finset.mem_univ, if_true]
    congr 1
    · ring
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : j = i
      · simp [h]
      · simp only [h, if_false]; ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i)]
  -- swap the second penalty's indices and use `|M i j| = |M j i|`
  have hswap : ∑ i, ∑ j, (if j = i then (0 : ℝ) else c j ^ 2 / 2 * |M i j|)
      = ∑ i, ∑ j, (if j = i then (0 : ℝ) else c i ^ 2 / 2 * |M i j|) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases h : i = j
    · simp [h]
    · have h' : j ≠ i := fun hh => h hh.symm
      simp only [h, h', if_false, hsymm j i]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hswap, ← Finset.sum_add_distrib]
  rw [sub_nonneg]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hd := hdom i
  have hc : (0 : ℝ) ≤ c i ^ 2 := sq_nonneg _
  have hcollect : (∑ j, if j = i then (0 : ℝ) else c i ^ 2 / 2 * |M i j|)
        + (∑ j, if j = i then (0 : ℝ) else c i ^ 2 / 2 * |M i j|)
      = c i ^ 2 * (∑ j, if j = i then (0 : ℝ) else |M i j|) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : j = i
    · simp [h]
    · simp only [h, if_false]; ring
  rw [hcollect]
  exact mul_le_mul_of_nonneg_left hd hc

#print axioms sum_sum_nonneg_of_diagDominant

/-- **A weighted diagonal-dominance test.** The sign of a quadratic form is unchanged by a positive
diagonal rescaling `M ↦ D M D`, so dominance may be tested after any such rescaling.
`sum_sum_nonneg_of_diagDominant` is this at `w = 1`.

**This is not a convenience — the unweighted test is the wrong one here.** For a Gram matrix whose
entries decay geometrically in a separation, write `d i` for member `i`'s height above the
reflection plane. The depth-`2p` diagonal entry sits at separation `2 · d i`, while the off-diagonal
entry against the member `j` nearest the plane sits at `d i + d j`. On saturated bounds the
off-diagonal is then LARGER than the whole diagonal excess by a factor geometric in `d i - d j`, at
every member above the family's minimum height. A spanning family of the half-space algebra contains
members at different heights, so unweighted dominance is not something such a family can be expected
to satisfy, and it is not provable from the upper bounds strong coupling supplies.

Weighting by `w i` geometric in `-d i` rebalances exactly this, and costs nothing, because the
conclusion is about the form and the form does not see the rescaling.

DERIVED: `0` is the strict lower bound on each weight and the value the diagonal term is excluded
by; `2` is the exponent on the weight, matching the two factors `w i * w j` contributes at `j = i`. -/
theorem sum_sum_nonneg_of_weighted_diagDominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hsymm : ∀ i j, M i j = M j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hdom : ∀ i, (∑ j, if j = i then (0 : ℝ) else w i * w j * |M i j|) ≤ w i ^ 2 * M i i)
    (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * M i j := by
  classical
  have hsymm' : ∀ i j, w i * w j * M i j = w j * w i * M j i := by
    intro i j; rw [hsymm i j]; ring
  have hdom' : ∀ i, (∑ j, if j = i then (0 : ℝ) else |w i * w j * M i j|)
      ≤ w i * w i * M i i := by
    intro i
    have hcong : ∀ j : ι, (if j = i then (0 : ℝ) else |w i * w j * M i j|)
        = (if j = i then (0 : ℝ) else w i * w j * |M i j|) := by
      intro j
      by_cases h : j = i
      · simp [h]
      · simp only [h, if_false, abs_mul, abs_of_pos (hw i), abs_of_pos (hw j)]
    rw [Finset.sum_congr rfl (fun j _ => hcong j)]
    refine le_trans (hdom i) (le_of_eq ?_)
    ring
  have key := sum_sum_nonneg_of_diagDominant (fun i j => w i * w j * M i j) hsymm' hdom'
    (fun i => c i / w i)
  refine le_of_le_of_eq key ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi : w i ≠ 0 := (hw i).ne'
  have hj : w j ≠ 0 := (hw j).ne'
  field_simp

#print axioms sum_sum_nonneg_of_weighted_diagDominant

/-- The `(i, j)` entry of `r²B − A`: the matrix the gap obligation asks to be positive semidefinite,
over a family of observables with their means subtracted.

`B` is the pairing at reflection depth `2p` and `A` the pairing at `2p−2`. Off-diagonal entries are
two-observable connected pairings at separation — what a strong-coupling expansion bounds — and the
diagonal is a contact term.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`, the two
planes' separation in `2 * p - 2`, and the exponent on `r`; `1` is the unit observable. -/
noncomputable def gapEntry (τ : Fin 4) (p : ℤ) (ν : MassGap.DLRLimit.State (IConf G)) (r : ℝ)
    {ι : Type*} (F : ι → C(IConf G, ℝ)) (i j : ι) : ℝ :=
  r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F i - ν (F i) • 1)
      * (F j - ν (F j) • 1))
    - ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F i - ν (F i) • 1)
      * (F j - ν (F j) • 1))

/-- **The gap obligation, reduced to entries.**

Composing `sum_sum_nonneg_of_diagDominant` with `gaugeInv_pairing_of_gram`: if over every finite
family drawn from a spanning set the matrix `r²B − A` is symmetric and diagonally dominant, then the
pairing inequality holds on the whole invariant algebra — and with
`ClayCapstone.gaugeInv_clay_gap_of_pairing`, the mass gap follows.

**This is the first statement in the development whose hypothesis has the same shape as the
strong-coupling output.** It asks, at each observable of the family, that the diagonal excess
dominate the sum of the off-diagonal entries. Those off-diagonal entries are two-observable
connected pairings at separation, which
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` bounds geometrically.

⛔ THE DIAGONAL HAS NO PROVED LOWER BOUND, and it is not a contact term. Writing `d` for a member's
height above the reflection plane, the depth-`2p` diagonal pairing is a correlator between a
plaquette and its mirror, at separation `2d` — the two arguments coincide only for a member lying in
the plane. `ContactFloor` bounds `wilsonCorrConn bd p β p`, the SAME plaquette twice, at lag zero;
that is a different quantity and does not apply here. Every strictly positive floor in the
development is likewise a contact value — `ReflectionHalfSpace.irefl_box_pairing_pos_witness` and
`BoxNumericFloor.box_reflection_form_ge_number` are both stated at a link of `boxR`, the links the
reflection FIXES, hence at separation zero.

⛔ AND THE OBVIOUS REPAIR IS CLOSED. `ReflectionHalfSpace.irefl_box_pairing_ge_variance` does bound a
reflected box pairing below, by a uniform weight floor times a free-measure variance, and its floor
carries `(iplqZero τ p Λ).card` — the whole plane — so it decays as the box grows. That factor is a
crude sup bound on the plane Boltzmann weight and could be localized. Localizing it does not help:
`ActionSplit.pairing_eq_zero_of_indep_R` proves the subtracted reflection pairing is IDENTICALLY
ZERO, at every coupling, whenever the observable reads the open half alone and the weight reads the
plane alone — and `iplaneWeight_local` and `iplaneWeight_nonneg` give the weight side. Under the
product Haar measure the two open halves are independent, so a weight-floor-times-free-variance
argument can only ever return `0 ≤`, which is already
`ReflectionHalfSpace.irefl_box_pairing_nonneg`.

The escape named by that theorem's own hypotheses: the observable it closes on must read the open
half alone. The observable that actually appears is dressed — `ReflectionHalfSpace.idressed`, the
observable times `ihalfBoltz`, which reads every plaquette of the positive half — so it fails that
hypothesis, and the entire nonzero value of the pairing is carried by the dressing.

A volume-uniform positive lower bound on the reflected connected two-point function at separation
`2d` is the open estimate this route rests on. It cannot come from monotonicity of `exp` against
`0 ≤ φ ≤ 2`; it needs an expansion that keeps the leading connected term WITH ITS SIGN. Strong
coupling supplies bounds on the modulus only, and a modulus bound cannot be turned around.

What it does not do is prove that hypothesis, and two things stand between: the invariant algebra is
not shown to be spanned by plaquette observables, and the strong-coupling bounds are stated for
plaquette PAIRS on the periodic lattice rather than for pairings of general invariant observables in
the infinite-volume state.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling, the planes'
separation, and the exponent on `r`; `1` is the unit observable; `0` is the value the diagonal is
excluded by. -/
theorem gaugeInv_pairing_of_diagDominant (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) {r : ℝ} {S : Set C(IConf G, ℝ)}
    (hspan : gaugeInvHalfSpaceAlg (G := G) τ p = Submodule.span ℝ S)
    (hsymm : ∀ (n : ℕ) (F : Fin n → C(IConf G, ℝ)), (∀ i, F i ∈ S) →
      ∀ i j, gapEntry τ p ν r F i j = gapEntry τ p ν r F j i)
    (hdom : ∀ (n : ℕ) (F : Fin n → C(IConf G, ℝ)), (∀ i, F i ∈ S) →
      ∀ i, (∑ j, if j = i then (0 : ℝ) else |gapEntry τ p ν r F i j|)
        ≤ gapEntry τ p ν r F i i) :
    ∀ F ∈ gaugeInvHalfSpaceAlg (G := G) τ p,
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
        ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F - ν F • 1)
          * (F - ν F • 1)) := by
  classical
  refine gaugeInv_pairing_of_gram τ p ν hspan (fun n a F hF => ?_)
  have hpsd := sum_sum_nonneg_of_diagDominant (gapEntry τ p ν r F) (hsymm n F hF)
    (hdom n F hF) a
  rw [← sub_nonneg]
  refine le_of_le_of_eq hpsd ?_
  simp only [gapEntry, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;>
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

#print axioms gaugeInv_pairing_of_diagDominant

/-- **The gap obligation, reduced to weighted entries.** `gaugeInv_pairing_of_diagDominant` with the
weighted test in place of the unweighted one, and the weight chosen per family.

The weight is existential and inside the family quantifier, so a caller picks it knowing the family
— which is necessary, since the rebalancing `sum_sum_nonneg_of_weighted_diagDominant` describes
depends on where the family's members sit relative to the reflection plane.

This is strictly weaker as a hypothesis than the unweighted form, and reaches the same conclusion:
`w = 1` recovers `gaugeInv_pairing_of_diagDominant`.

DERIVED: `2` is the reflection plane's spacing in lattice units, so consecutive planes are `2p` and
`2p − 2`, and is also the Rayleigh exponent on `r` and the exponent on the weight; `0` is the
excluded diagonal term and the strict lower bound on each weight; `1` is the unit observable
carrying the subtracted mean; `4` is the spacetime dimension. -/
theorem gaugeInv_pairing_of_weighted_diagDominant (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) {r : ℝ} {S : Set C(IConf G, ℝ)}
    (hspan : gaugeInvHalfSpaceAlg (G := G) τ p = Submodule.span ℝ S)
    (hsymm : ∀ (n : ℕ) (F : Fin n → C(IConf G, ℝ)), (∀ i, F i ∈ S) →
      ∀ i j, gapEntry τ p ν r F i j = gapEntry τ p ν r F j i)
    (hdom : ∀ (n : ℕ) (F : Fin n → C(IConf G, ℝ)), (∀ i, F i ∈ S) →
      ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ i,
        (∑ j, if j = i then (0 : ℝ) else w i * w j * |gapEntry τ p ν r F i j|)
          ≤ w i ^ 2 * gapEntry τ p ν r F i i) :
    ∀ F ∈ gaugeInvHalfSpaceAlg (G := G) τ p,
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
        ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F - ν F • 1)
          * (F - ν F • 1)) := by
  classical
  refine gaugeInv_pairing_of_gram τ p ν hspan (fun n a F hF => ?_)
  obtain ⟨w, hw, hd⟩ := hdom n F hF
  have hpsd := sum_sum_nonneg_of_weighted_diagDominant (gapEntry τ p ν r F) (hsymm n F hF)
    w hw hd a
  rw [← sub_nonneg]
  refine le_of_le_of_eq hpsd ?_
  simp only [gapEntry, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;>
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

#print axioms gaugeInv_pairing_of_weighted_diagDominant

/-- **An off-diagonal `gapEntry` is bounded by its two constituent pairings.**

`gapEntry τ p ν r F i j` is `r² · (pairing at 2p) − (pairing at 2p − 2)`, and both pairings are the
reflected, mean-subtracted two-observable pairing of `stateFree_pairing_abs_le` — which bounds them
by `coreConst · coreRate ^ k`, geometrically in the separation. A triangle inequality is the whole
content of this lemma.

Its point is joinery. `gaugeInv_pairing_of_diagDominant`'s `hdom` asks that the diagonal excess
dominate the sum of the off-diagonal moduli, and until now nothing in the development produced an
off-diagonal modulus in a form that hypothesis could consume. This does: with
`stateFree_pairing_abs_le` at each of the two reflection depths, an entry of the Gram matrix is
bounded by a strong-coupling quantity.

The two depths differ by one lattice step, so at fixed separation the two bounds differ only in
which reflection plane they are taken about, and `M` and `M'` are kept separate rather than merged
so that a caller supplying different separations at the two depths is not forced to weaken either.

What this does not supply is `hdom` itself. That needs the sum over `j` to converge against the
diagonal, which is a statement about how spread out the family is, and it is not proved here for any
family.

DERIVED: `2` is the reflection plane's spacing in lattice units — reflections sit at even
coordinates, so consecutive planes are `2p` and `2p − 2` — and is also the Rayleigh exponent on `r`;
`0` is the lower end of `r`, a modulus ratio being non-negative; `1` is the algebra's unit, which
carries the subtracted mean; `4` is the spacetime dimension, indexing the direction `τ` the
reflection is taken in. -/
theorem gapEntry_abs_le (τ : Fin 4) (p : ℤ) (ν : MassGap.DLRLimit.State (IConf G)) {r : ℝ}
    (hr : 0 ≤ r) {ι : Type*} (F : ι → C(IConf G, ℝ)) (i j : ι) {M M' : ℝ}
    (hM : |ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F i - ν (F i) • 1)
        * (F j - ν (F j) • 1))| ≤ M)
    (hM' : |ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F i - ν (F i) • 1)
        * (F j - ν (F j) • 1))| ≤ M') :
    |gapEntry τ p ν r F i j| ≤ r ^ 2 * M + M' := by
  unfold gapEntry
  set A := ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F i - ν (F i) • 1)
    * (F j - ν (F j) • 1)) with hA
  set B := ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F i - ν (F i) • 1)
    * (F j - ν (F j) • 1)) with hB
  rw [abs_le] at hM hM' ⊢
  constructor <;> nlinarith [sq_nonneg r, hM.1, hM.2, hM'.1, hM'.2]

#print axioms gapEntry_abs_le

/-- **The dominance hypothesis, reduced to numeric inputs.** `U` and `U'` bound the two constituent
pairings at each pair of family members, `Lo` floors the diagonal, and `hsum` is the arithmetic that
has to hold between them.

Nothing about coupling, lattice or state enters: every bound is a parameter, so any estimate that
produces `U`, `U'` and `Lo` discharges `gaugeInv_pairing_of_diagDominant`'s `hdom` through this.
`gapEntry_abs_le` does the per-entry work.

`Lo` is the one that has no supplier. Strong coupling produces upper bounds; the diagonal floor is
the open estimate, as `gapEntry`'s own docstring records.

DERIVED: `0` is the lower bound on `r` and the excluded diagonal term; `2` is the Rayleigh exponent
on `r` and the reflection plane's spacing in lattice units; `4` is the spacetime dimension; `1` is
the unit observable carrying the subtracted mean. -/
theorem gapEntry_diagDominant_of_bounds (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) {r : ℝ} (hr : 0 ≤ r)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → C(IConf G, ℝ))
    (U U' : ι → ι → ℝ)
    (hU : ∀ i j, |ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F i - ν (F i) • 1)
            * (F j - ν (F j) • 1))| ≤ U i j)
    (hU' : ∀ i j, |ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F i - ν (F i) • 1)
            * (F j - ν (F j) • 1))| ≤ U' i j)
    (Lo : ι → ℝ) (hL : ∀ i, Lo i ≤ gapEntry τ p ν r F i i)
    (hsum : ∀ i, (∑ j, if j = i then (0 : ℝ) else r ^ 2 * U i j + U' i j) ≤ Lo i) :
    ∀ i, (∑ j, if j = i then (0 : ℝ) else |gapEntry τ p ν r F i j|)
      ≤ gapEntry τ p ν r F i i := by
  classical
  intro i
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (le_trans (hsum i) (hL i))
  by_cases h : j = i
  · simp [h]
  · simp only [h, if_false]
    exact gapEntry_abs_le τ p ν hr F i j (hU i j) (hU' i j)

#print axioms gapEntry_diagDominant_of_bounds

/-- **The weighted dominance hypothesis, reduced to the same numeric inputs.** The form
`gaugeInv_pairing_of_weighted_diagDominant` consumes, with the weight supplied by the caller.

This is the one a geometric estimate can meet: `sum_sum_nonneg_of_weighted_diagDominant` explains
why the unweighted test is the wrong one for entries decaying in a separation, and this is its
numeric reduction.

DERIVED: `0` is the lower bound on `r`, the strict lower bound on each weight, and the excluded
diagonal term; `2` is the Rayleigh exponent, the weight's exponent and the plane spacing; `4` is the
spacetime dimension; `1` is the unit observable. -/
theorem gapEntry_weighted_diagDominant_of_bounds (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) {r : ℝ} (hr : 0 ≤ r)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → C(IConf G, ℝ))
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (U U' : ι → ι → ℝ)
    (hU : ∀ i j, |ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F i - ν (F i) • 1)
            * (F j - ν (F j) • 1))| ≤ U i j)
    (hU' : ∀ i j, |ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F i - ν (F i) • 1)
            * (F j - ν (F j) • 1))| ≤ U' i j)
    (Lo : ι → ℝ) (hL : ∀ i, Lo i ≤ gapEntry τ p ν r F i i)
    (hsum : ∀ i, (∑ j, if j = i then (0 : ℝ) else w i * w j * (r ^ 2 * U i j + U' i j))
      ≤ w i ^ 2 * Lo i) :
    ∀ i, (∑ j, if j = i then (0 : ℝ) else w i * w j * |gapEntry τ p ν r F i j|)
      ≤ w i ^ 2 * gapEntry τ p ν r F i i := by
  classical
  intro i
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (le_trans (hsum i) (mul_le_mul_of_nonneg_left (hL i) (sq_nonneg _)))
  by_cases h : j = i
  · simp [h]
  · simp only [h, if_false]
    exact mul_le_mul_of_nonneg_left (gapEntry_abs_le τ p ν hr F i j (hU i j) (hU' i j))
      (le_of_lt (mul_pos (hw i) (hw j)))

#print axioms gapEntry_weighted_diagDominant_of_bounds

end MassGap.GaugeInvariantAlgebra
