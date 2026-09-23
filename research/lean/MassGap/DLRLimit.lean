import Mathlib

/-!
# MassGap.DLRLimit — a limit state on `C(X, ℝ)` for `X` compact, and its DLR consistency

Builds a state on the continuous functions of a compact space as a limit of a family of states, shows
the consistency relation passes to that limit, and represents the result as a probability measure.
Everything is then instantiated at `IConf G = ILink → G`, the configuration space of the infinite
four-dimensional lattice, which is compact by `Pi.compactSpace` (`compactSpace_iconf`).

## The argument

`State X` is a positive normalised linear functional on `C(X, ℝ)`. Positivity and normalisation alone
give `|ν f| ≤ ‖f‖` (`State.abs_le_norm`), so every state's value at `f` lies in the compact interval
`Set.Icc (-‖f‖) ‖f‖` fixed by `f` alone (`State.mem_Icc`). `exists_limit_state` runs
`isCompact_Icc.ultrafilter_le_nhds` at one interval per observable: for any `NeBot` filter `l` on any
index type and any family of states, there are an ultrafilter `u ≤ l` and a state `ν` with
`μ i f → ν f` along `u`, simultaneously at every `f`. Linearity, positivity and normalisation of the
limit come from `tendsto_nhds_unique` and `ge_of_tendsto'`.

`IsDLR γ ν` is `∀ k f, ν (γ k f) = ν f` for a specification `γ : κ → C(X, ℝ) → C(X, ℝ)` acting on
observables. `isDLR_of_tendsto` carries it to the limit, since the relation is an equality of two
convergent numbers. `exists_dlr_state` assembles the two over a `SemilatticeSup` index, where
directedness turns "for every `j ≤ i`" into "eventually in `i`".
`tendsto_of_unique_dlr` upgrades the ultrafilter limit to convergence along `l` itself when the DLR
state is unique.

`State.eq_of_eqOn_dense`, `State.eq_of_eqOn_subalgebra` and `State.eq_of_eqOn_localObs` are the
determination results: a state is `1`-Lipschitz (`State.abs_sub_le`) hence continuous, so agreement on
a dense set extends; Stone–Weierstrass turns a point-separating subalgebra into a dense one; and
`localObsAlg`, the observables local on some finite link set, separates points of `IConf G` when the
gauge group is compact Hausdorff (`localObsAlg_separatesPoints`,
`continuousMap_separatesPoints_of_t2`).

`IsPointMass` and `variance_eq_zero_of_isPointMass` set up the non-degeneracy check:
`variance_ge_of_eventually` carries a variance floor to the limit and
`not_isPointMass_of_uniform_variance` concludes `ν 1 = 1` together with `¬ IsPointMass ν`.

`stateCc` presents a state as a positive linear map on `C_c(X, ℝ)`, which on a compact space is every
continuous function; `gibbsMeasure` is `RealRMK.rieszMeasure` of it, `integral_gibbsMeasure` the
representation, and `instIsProbabilityMeasure` the total mass.

`exists_infinite_volume_gibbs_state`, `exists_infinite_volume_gibbs_state_nondegenerate` and
`exists_infinite_volume_gibbs_measure` are the instantiations at `Finset ILink` and `IConf G`.

## Scope

* `γ` and `μ` are hypotheses in every theorem here. No statement identifies them with a Wilson
  specification or with Wilson–Gibbs states, and no Wilson action appears.
* The limit is subsequential: an ultrafilter refining `atTop` exists, and nothing shows the net
  itself converges. `tendsto_of_unique_dlr` is the conditional upgrade, whose hypothesis `huniq` is
  supplied at coupling zero by `WilsonDLR.dlr_unique_at_zero_eq`.
* Uniqueness and translation invariance of the limit are not proved.
* `ν 1 = 1` is a field of `State`, so it holds of the limit by construction; it excludes the zero
  functional and nothing else. A limit of point masses is a point mass, so ruling one out needs more
  input: `not_isPointMass_of_uniform_variance` takes a variance floor `c ≤ μ i (f * f) - (μ i f) ^ 2`
  holding uniformly in the index, and that floor is a hypothesis here.
  `InfiniteVolume.exists_uniform_contact_floor` supplies one `δ₀ > 0` with
  `exp (-128 * β) * δ₀ ≤ wilsonCorrAt N β 0` at every aperture and every `β ≥ 0`, and
  `PlaqVariance.corrClay_zero_eq` makes that contact value a plaquette variance;
  `ClayNontriviality.clay_nontriviality_of_wilson_variance` composes the two. What is not supplied
  is the bridge between that aperture indexing and the `Finset ILink` indexing used here.
* `gibbsMeasure` needs the Borel structure of `IConf G` to be its product σ-algebra, which over an
  infinite index requires a countable index and a second-countable factor. `ILink` is countable, so
  `SecondCountableTopology G` is a hypothesis of the measure statements and not of the state ones
  (`borelSpace_iconf`).

Build: `python research/code/lean_build.py build MassGap.DLRLimit`.
-/

namespace MassGap.DLRLimit

open Filter
open scoped Topology CompactlySupported

/-! ## Part 0 — the infinite-lattice skeleton

Written here rather than imported so the file stands alone. The four declarations mirror
`MassGap.InfiniteLattice`'s; being `abbrev`s they are reducible, so the two copies are
interchangeable wherever both are in scope. -/

/-- `Fin 4 → ℤ`: a site of the infinite four-dimensional lattice, one integer coordinate per
direction. The lattice is infinite in each direction — the coordinate type is `ℤ`, not `Fin n`.

DERIVED: `4` is the number of spacetime directions, the same `d` `WilsonHypercubic` is instantiated
at for the Clay instance. It is an index range, not an extent. -/
abbrev ISite : Type := Fin 4 → ℤ

#print axioms ISite

/-- `Fin 4 × ISite`: an oriented link, given by its direction and the site it leaves. Countable,
which `borelSpace_iconf` spends.

DERIVED: `4` is the number of spacetime directions, over which a link's direction ranges — the same
constant as in `ISite`. -/
abbrev ILink : Type := Fin 4 × ISite

#print axioms ILink

/-- `(Fin 4 × Fin 4) × ISite`: a plaquette, given by the ordered pair of directions spanning its
plane and the site at its corner. `WilsonHypercubic.Plaq` carries the same pair.

DERIVED: `4` occurs twice, as the number of spacetime directions each of the two spanning directions
ranges over. A plane needs an ordered pair, so the dimension appears twice. -/
abbrev IPlaq : Type := (Fin 4 × Fin 4) × ISite

#print axioms IPlaq

/-- `ILink → G`: a configuration of the infinite lattice, one group element per link. Compact
whenever `G` is, by `compactSpace_iconf`.

DERIVED: no numeral appears in the statement. -/
abbrev IConf (G : Type) : Type := ILink → G

#print axioms IConf

/-- `CompactSpace (IConf G)` whenever `G` is compact, by `inferInstance` — it is `Pi.compactSpace`,
Tychonoff for a product of compact spaces. Recorded so that the instance is visibly available at this
type, which is what the compactness arguments below need.

DERIVED: no numeral appears in the statement. -/
theorem compactSpace_iconf (G : Type) [TopologicalSpace G] [CompactSpace G] :
    CompactSpace (IConf G) := inferInstance

#print axioms compactSpace_iconf

/-! ## Part 1 — states, and what positivity alone gives

A state is a positive normalised linear functional on the continuous functions. On a compact space
Riesz–Markov–Kakutani makes it a probability measure (Part 5), but the functional is what the limit
argument moves, so it is the primitive here. -/

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A state on `C(X, ℝ)` for `X` compact: a functional `toFun` that is additive and homogeneous,
sends pointwise nonnegative observables to nonnegative reals, and sends the constant `1` to `1`.

The positivity and normalisation fields alone give the uniform bound `|ν f| ≤ ‖f‖`
(`State.abs_le_norm`) that the compactness argument runs on; no continuity is assumed.

DERIVED: `0` occurs twice in the `nonneg'` field, as the pointwise lower bound on `f` and as the
lower bound on its value; `1` occurs twice in the `one'` field, as the constant observable and as the
value it takes. -/
structure State (X : Type*) [TopologicalSpace X] [CompactSpace X] where
  /-- The underlying functional on `C(X, ℝ)`. DERIVED: no numeral. -/
  toFun : C(X, ℝ) → ℝ
  /-- Additivity: the functional carries a sum of observables to the sum of their values.
  DERIVED: no numeral. -/
  map_add' : ∀ f g : C(X, ℝ), toFun (f + g) = toFun f + toFun g
  /-- Homogeneity: scaling an observable by a real scales its value by the same factor.
  DERIVED: no numeral. -/
  map_smul' : ∀ (c : ℝ) (f : C(X, ℝ)), toFun (c • f) = c * toFun f
  /-- Positivity: an observable nonnegative at every point has a nonnegative value.
  DERIVED: `0` appears twice, as the lower bound hypothesised pointwise and as the lower bound
  concluded of the value. -/
  nonneg' : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ toFun f
  /-- Normalisation: the constant observable `1` has value `1`.
  DERIVED: `1` appears twice, as the constant observable and as its value; together with positivity
  this is what makes a `State` a probability rather than a general positive functional. -/
  one' : toFun 1 = 1

#print axioms State

instance instCoeFunState : CoeFun (State X) (fun _ => C(X, ℝ) → ℝ) := ⟨State.toFun⟩

#print axioms instCoeFunState

theorem State.map_add (ν : State X) (f g : C(X, ℝ)) : ν (f + g) = ν f + ν g := ν.map_add' f g

#print axioms State.map_add

theorem State.map_smul (ν : State X) (c : ℝ) (f : C(X, ℝ)) : ν (c • f) = c * ν f := ν.map_smul' c f

#print axioms State.map_smul

theorem State.nonneg (ν : State X) (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) : 0 ≤ ν f := ν.nonneg' f hf

#print axioms State.nonneg

theorem State.map_one (ν : State X) : ν (1 : C(X, ℝ)) = 1 := ν.one'

#print axioms State.map_one

theorem State.map_zero (ν : State X) : ν (0 : C(X, ℝ)) = 0 := by
  have h := ν.map_smul (0 : ℝ) (0 : C(X, ℝ))
  simpa using h

#print axioms State.map_zero

theorem State.map_sub (ν : State X) (f g : C(X, ℝ)) : ν (f - g) = ν f - ν g := by
  have h : ν ((f - g) + g) = ν (f - g) + ν g := ν.map_add _ _
  have hfg : (f - g) + g = f := by abel
  rw [hfg] at h
  linarith

#print axioms State.map_sub

theorem State.map_neg (ν : State X) (f : C(X, ℝ)) : ν (-f) = -ν f := by
  have h := ν.map_sub 0 f
  rw [zero_sub, ν.map_zero, zero_sub] at h
  exact h

#print axioms State.map_neg

/-- `ν f ≤ ν g` whenever `f x ≤ g x` at every point: positivity applied to `g - f`, with
`State.map_sub` splitting the value.

DERIVED: no numeral appears in the statement. -/
theorem State.mono (ν : State X) {f g : C(X, ℝ)} (h : ∀ x, f x ≤ g x) : ν f ≤ ν g := by
  have h0 : 0 ≤ ν (g - f) := ν.nonneg _ (fun x => by simpa using sub_nonneg.mpr (h x))
  rw [ν.map_sub] at h0
  linarith

#print axioms State.mono

/-- `ν f ≤ ‖f‖` at every observable. `f x ≤ ‖f‖` pointwise, so `State.mono` against the constant
observable `‖f‖ • 1` gives it, and `State.map_smul` with `State.map_one` evaluates that.

Scope: no continuity of `ν` is assumed — positivity and normalisation give the bound. This is the
uniform bound the compactness argument runs on.

DERIVED: no numeral appears in the statement. -/
theorem State.le_norm (ν : State X) (f : C(X, ℝ)) : ν f ≤ ‖f‖ := by
  have hle : ∀ x, f x ≤ ((‖f‖ : ℝ) • (1 : C(X, ℝ))) x := by
    intro x
    have h1 : ‖f x‖ ≤ ‖f‖ := f.norm_coe_le_norm x
    have h2 : f x ≤ ‖f‖ := le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at h1)
    simpa using h2
  have h3 := ν.mono hle
  rwa [ν.map_smul, ν.map_one, mul_one] at h3

#print axioms State.le_norm

/-- `|ν f| ≤ ‖f‖` at every observable: `State.le_norm` at `f` and at `-f`, the latter through
`State.map_neg` and `norm_neg`.

DERIVED: no numeral appears in the statement. -/
theorem State.abs_le_norm (ν : State X) (f : C(X, ℝ)) : |ν f| ≤ ‖f‖ := by
  refine abs_le.mpr ⟨?_, ν.le_norm f⟩
  have h := ν.le_norm (-f)
  rw [ν.map_neg, norm_neg] at h
  linarith

#print axioms State.abs_le_norm

/-- `ν f ∈ Set.Icc (-‖f‖) ‖f‖`, from `State.abs_le_norm`. The interval depends on `f` alone and not
on the state, which is what lets `exists_limit_state` apply compactness of one interval per
observable.

DERIVED: no numeral appears in the statement. -/
theorem State.mem_Icc (ν : State X) (f : C(X, ℝ)) : ν f ∈ Set.Icc (-‖f‖) ‖f‖ :=
  Set.mem_Icc.mpr (abs_le.mp (ν.abs_le_norm f))

#print axioms State.mem_Icc


/-- `|ν f - ν g| ≤ ‖f - g‖`: `State.map_sub` turns the left side into `|ν (f - g)|` and
`State.abs_le_norm` bounds it. So a state is Lipschitz with constant one, which is forced by
positivity and normalisation rather than assumed.

DERIVED: no numeral appears in the statement; the Lipschitz constant is the implicit factor one on
the right. -/
theorem State.abs_sub_le (ν : State X) (f g : C(X, ℝ)) : |ν f - ν g| ≤ ‖f - g‖ := by
  rw [← ν.map_sub]
  exact ν.abs_le_norm (f - g)

#print axioms State.abs_sub_le

/-- `Continuous (fun f : C(X, ℝ) => ν f)`, from `State.abs_sub_le` with `δ := ε` in the metric
criterion. This is what lets agreement on a dense set extend.

DERIVED: no numeral appears in the statement. -/
theorem State.continuous (ν : State X) : Continuous (fun f : C(X, ℝ) => ν f) := by
  refine Metric.continuous_iff.mpr (fun f ε hε => ⟨ε, hε, fun g hg => ?_⟩)
  have h := ν.abs_sub_le g f
  rw [Real.dist_eq]
  have hgf : ‖g - f‖ < ε := by rwa [dist_eq_norm] at hg
  exact lt_of_le_of_lt h hgf

#print axioms State.continuous

/-- Two states agreeing on a dense set `s ⊆ C(X, ℝ)` agree everywhere. Both are continuous by
`State.continuous`, so `Continuous.ext_on` applies.

Scope: density of `s` is a hypothesis. `State.eq_of_eqOn_subalgebra` obtains it from point
separation via Stone–Weierstrass, and `State.eq_of_eqOn_localObs` at the local observables.

DERIVED: no numeral appears in the statement. -/
theorem State.eq_of_eqOn_dense {ν₁ ν₂ : State X} {s : Set C(X, ℝ)} (hs : Dense s)
    (h : ∀ f ∈ s, ν₁ f = ν₂ f) : ∀ f : C(X, ℝ), ν₁ f = ν₂ f := by
  have := Continuous.ext_on hs ν₁.continuous ν₂.continuous h
  exact fun f => congrFun this f

#print axioms State.eq_of_eqOn_dense

/-- Two states agreeing on a subalgebra `A ⊆ C(X, ℝ)` that separates points agree everywhere.
`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints` makes `A` dense on the
compact `X`, and `State.eq_of_eqOn_dense` finishes.

DERIVED: no numeral appears in the statement. -/
theorem State.eq_of_eqOn_subalgebra {ν₁ ν₂ : State X} (A : Subalgebra ℝ C(X, ℝ))
    (hsep : A.SeparatesPoints) (h : ∀ f ∈ A, ν₁ f = ν₂ f) : ∀ f : C(X, ℝ), ν₁ f = ν₂ f := by
  have htop : A.topologicalClosure = ⊤ :=
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hdense : Dense (A : Set C(X, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, htop]
    simp
  exact State.eq_of_eqOn_dense hdense h

#print axioms State.eq_of_eqOn_subalgebra

/-- `Nonempty X` for any state on `C(X, ℝ)`. On an empty space the constant observable `1` is the
zero observable, so `State.map_one` and `State.map_zero` would give `1 = 0`.

So anything needing a base configuration can take one from the state.

DERIVED: no numeral appears in the statement. The `1` and `0` compared in the proof are the values a
state takes on the unit and the zero observable. -/
theorem State.nonempty (ν : State X) : Nonempty X := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hzero : (1 : C(X, ℝ)) = 0 := by
    ext x
    exact (IsEmpty.false x).elim
  have hone := ν.map_one
  rw [hzero, ν.map_zero] at hone
  exact zero_ne_one hone

#print axioms State.nonempty

/-- Two states with equal functionals are equal. The other four fields are `Prop`s, so proof
irrelevance settles them once `toFun` matches. `tendsto_of_unique_dlr` needs equality of states, and
a uniqueness argument delivers agreement at every observable, so this is the bridge.

DERIVED: no numeral appears in the statement. -/
theorem State.eq_of_apply_eq {ν₁ ν₂ : State X} (h : ∀ f : C(X, ℝ), ν₁ f = ν₂ f) : ν₁ = ν₂ := by
  obtain ⟨t₁, _, _, _, _⟩ := ν₁
  obtain ⟨t₂, _, _, _, _⟩ := ν₂
  have ht : t₁ = t₂ := funext (fun f => h f)
  subst ht
  rfl

#print axioms State.eq_of_apply_eq



section LocalObservables

variable {G : Type} [TopologicalSpace G] [CompactSpace G]

/-- `∀ U V : IConf G, (∀ l ∈ S, U l = V l) → F U = F V`: a bundled continuous observable is local on
the finite link set `S` when it is unchanged by the links outside `S`.
`InfiniteLattice.IsLocalOn` is the unbundled twin; here continuity is carried by the type of `F`
rather than by a conjunct.

DERIVED: no numeral appears in the statement. -/
def IsLocalOnC (S : Finset ILink) (F : C(IConf G, ℝ)) : Prop :=
  ∀ U V : IConf G, (∀ l ∈ S, U l = V l) → F U = F V

#print axioms IsLocalOnC

/-- The subalgebra `{F | ∃ S : Finset ILink, IsLocalOnC S F}` of `C(IConf G, ℝ)`. Closure under
products and sums holds because an observable local on `S` and one local on `T` are both local on
`S ∪ T`, again finite; the constants are local on `∅`.
`InfiniteLattice.quasiLocalAlg` is the same object one coercion away.

DERIVED: no numeral appears in the statement. -/
def localObsAlg (G : Type) [TopologicalSpace G] [CompactSpace G] :
    Subalgebra ℝ C(IConf G, ℝ) where
  carrier := {F | ∃ S : Finset ILink, IsLocalOnC S F}
  mul_mem' := by
    rintro F H ⟨S, hF⟩ ⟨T, hH⟩
    refine ⟨S ∪ T, fun U V h => ?_⟩
    simp only [ContinuousMap.mul_apply]
    rw [hF U V (fun l hl => h l (Finset.mem_union_left _ hl)),
        hH U V (fun l hl => h l (Finset.mem_union_right _ hl))]
  add_mem' := by
    rintro F H ⟨S, hF⟩ ⟨T, hH⟩
    refine ⟨S ∪ T, fun U V h => ?_⟩
    simp only [ContinuousMap.add_apply]
    rw [hF U V (fun l hl => h l (Finset.mem_union_left _ hl)),
        hH U V (fun l hl => h l (Finset.mem_union_right _ hl))]
  one_mem' := ⟨∅, fun _ _ _ => rfl⟩
  zero_mem' := ⟨∅, fun _ _ _ => rfl⟩
  algebraMap_mem' := fun _ => ⟨∅, fun _ _ _ => rfl⟩

#print axioms localObsAlg

/-- `F ∈ localObsAlg G ↔ ∃ S : Finset ILink, IsLocalOnC S F`, by `Iff.rfl`. Mirrors
`InfiniteLattice.mem_quasiLocalAlg`.

DERIVED: no numeral appears in the statement. -/
theorem mem_localObsAlg {F : C(IConf G, ℝ)} :
    F ∈ localObsAlg G ↔ ∃ S : Finset ILink, IsLocalOnC S F := Iff.rfl

#print axioms mem_localObsAlg


/-- `(localObsAlg G).SeparatesPoints`, given that `C(G, ℝ)` separates the points of `G`. Two distinct
configurations differ at some link `l`; composing a separating `g : C(G, ℝ)` with evaluation at `l`
gives an observable local on the singleton `{l}` that tells them apart.

Scope: the separation hypothesis on `G` is the caller's;
`continuousMap_separatesPoints_of_t2` discharges it for a compact Hausdorff group.

DERIVED: no numeral appears in the statement. -/
theorem localObsAlg_separatesPoints
    (hG : ∀ a b : G, a ≠ b → ∃ g : C(G, ℝ), g a ≠ g b) :
    (localObsAlg G).SeparatesPoints := by
  intro U V hUV
  have hex : ∃ l : ILink, U l ≠ V l := by
    by_contra hcon
    push_neg at hcon
    exact hUV (funext hcon)
  obtain ⟨l, hl⟩ := hex
  obtain ⟨g, hg⟩ := hG (U l) (V l) hl
  have hcont : Continuous (fun W : IConf G => g (W l)) := g.continuous.comp (continuous_apply l)
  refine ⟨(⟨fun W : IConf G => g (W l), hcont⟩ : C(IConf G, ℝ)), ⟨_, ⟨{l}, ?_⟩, rfl⟩, hg⟩
  intro A B h
  simp only [ContinuousMap.coe_mk]
  rw [h l (Finset.mem_singleton_self l)]

#print axioms localObsAlg_separatesPoints

/-- For a compact Hausdorff `G` and distinct `a`, `b`, there is a `g : C(G, ℝ)` with `g a ≠ g b`. The
two singletons are disjoint closed sets, so `exists_continuous_zero_one_of_isClosed` produces a
continuous function taking the value `0` on one and `1` on the other.

DERIVED: no numeral appears in the statement. The `0` and `1` are the values Urysohn's lemma
produces in the proof; any two distinct reals would serve, and Mathlib's statement fixes these. -/
theorem continuousMap_separatesPoints_of_t2 (G : Type) [TopologicalSpace G] [CompactSpace G]
    [T2Space G] (a b : G) (hab : a ≠ b) : ∃ g : C(G, ℝ), g a ≠ g b := by
  obtain ⟨g, hga, hgb, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := a))
      (isClosed_singleton (x := b)) (Set.disjoint_singleton.mpr hab)
  have h0 : g a = 0 := hga rfl
  have h1 : g b = 1 := hgb rfl
  refine ⟨g, ?_⟩
  rw [h0, h1]
  norm_num

#print axioms continuousMap_separatesPoints_of_t2

/-- Two states on `C(IConf G, ℝ)` agreeing on `localObsAlg G` agree everywhere, for `G` compact
Hausdorff. It is `State.eq_of_eqOn_subalgebra` with separation supplied by
`localObsAlg_separatesPoints` and `continuousMap_separatesPoints_of_t2`.

Scope: no density or separation hypothesis is left to the caller; what is left is agreement on the
local observables, which is the input. Together with `State.eq_of_apply_eq` it gives equality of
states, which `tendsto_of_unique_dlr` consumes.

DERIVED: no numeral appears in the statement. -/
theorem State.eq_of_eqOn_localObs {G : Type} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    {ν₁ ν₂ : State (IConf G)} (h : ∀ F ∈ localObsAlg G, ν₁ F = ν₂ F) :
    ∀ F : C(IConf G, ℝ), ν₁ F = ν₂ F :=
  State.eq_of_eqOn_subalgebra _
    (localObsAlg_separatesPoints (fun a b hab => continuousMap_separatesPoints_of_t2 G a b hab)) h

#print axioms State.eq_of_eqOn_localObs

end LocalObservables



/-! ## Part 2 — the limit state

The ultrafilter-and-compactness move of `InfiniteVolume.exists_filter_tendsto_all_lags`, one level
up: there the coordinates are lags and the compact set is `Set.Icc (-4) 4`; here the coordinates are
observables and the compact set is `Set.Icc (-‖f‖) ‖f‖`. The limit functional is assembled
coordinate by coordinate, each of its four defining properties transported by uniqueness of
limits. -/

/-- For any `NeBot` filter `l` on any index type `ι` and any family `μ : ι → State X`, there are an
ultrafilter `u` with `(u : Filter ι) ≤ l` and a state `ν` such that `μ i f → ν f` along `u`,
simultaneously at every observable `f`.

`u` is `Ultrafilter.of l`. For each `f`, `State.mem_Icc` places every `μ i f` in
`Set.Icc (-‖f‖) ‖f‖`, and `isCompact_Icc.ultrafilter_le_nhds` produces the limit value; `choose`
collects them into a functional `L`. Additivity and homogeneity follow by `tendsto_nhds_unique`,
positivity by `ge_of_tendsto'`, and normalisation by uniqueness against a constant sequence.

Scope: no structure on the index is used — not directedness, not countability. The hypotheses are
`l.NeBot` and that each `μ i` is a state. The conclusion is along `u`, not along `l`;
`tendsto_of_unique_dlr` is the conditional upgrade.

DERIVED: no numeral appears in the statement. -/
theorem exists_limit_state {ι : Type*} (l : Filter ι) [l.NeBot] (μ : ι → State X) :
    ∃ (u : Ultrafilter ι) (ν : State X), (u : Filter ι) ≤ l ∧
      ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) (u : Filter ι) (𝓝 (ν f)) := by
  classical
  let u : Ultrafilter ι := Ultrafilter.of l
  have hle : (u : Filter ι) ≤ l := Ultrafilter.of_le l
  haveI hub : (u : Filter ι).NeBot := u.neBot'
  -- one limit value per observable, by compactness of the interval that observable's norm fixes
  have hk : ∀ f : C(X, ℝ), ∃ a ∈ Set.Icc (-‖f‖) ‖f‖,
      Tendsto (fun i => μ i f) (u : Filter ι) (𝓝 a) := by
    intro f
    have hmem : Set.Icc (-‖f‖) ‖f‖ ∈ (Ultrafilter.map (fun i => μ i f) u : Filter ℝ) := by
      rw [Ultrafilter.coe_map]
      exact Filter.mem_map.mpr (Filter.univ_mem' (fun i => (μ i).mem_Icc f))
    obtain ⟨a, _ha, hlim⟩ := isCompact_Icc.ultrafilter_le_nhds
      (Ultrafilter.map (fun i => μ i f) u) (le_principal_iff.mpr hmem)
    refine ⟨a, _ha, ?_⟩
    have hmap : Filter.map (fun i => μ i f) (u : Filter ι) ≤ 𝓝 a := by
      rw [← Ultrafilter.coe_map]
      exact hlim
    exact hmap
  choose L _hLmem hLtend using hk
  -- the limit functional is additive
  have hadd : ∀ f g : C(X, ℝ), L (f + g) = L f + L g := by
    intro f g
    have h1 : Tendsto (fun i => μ i f + μ i g) (u : Filter ι) (𝓝 (L (f + g))) :=
      (hLtend (f + g)).congr (fun i => (μ i).map_add f g)
    have h2 : Tendsto (fun i => μ i f + μ i g) (u : Filter ι) (𝓝 (L f + L g)) :=
      (hLtend f).add (hLtend g)
    exact tendsto_nhds_unique h1 h2
  -- homogeneous
  have hsmul : ∀ (c : ℝ) (f : C(X, ℝ)), L (c • f) = c * L f := by
    intro c f
    have h1 : Tendsto (fun i => c * μ i f) (u : Filter ι) (𝓝 (L (c • f))) :=
      (hLtend (c • f)).congr (fun i => (μ i).map_smul c f)
    have h2 : Tendsto (fun i => c * μ i f) (u : Filter ι) (𝓝 (c * L f)) := (hLtend f).const_mul c
    exact tendsto_nhds_unique h1 h2
  -- positive: a closed condition, so `ge_of_tendsto'`
  have hnn : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f := by
    intro f hf
    exact ge_of_tendsto' (hLtend f) (fun i => (μ i).nonneg f hf)
  -- normalised
  have hone : L 1 = 1 := by
    have h1 : Tendsto (fun _ : ι => (1 : ℝ)) (u : Filter ι) (𝓝 (L 1)) :=
      (hLtend 1).congr (fun i => (μ i).map_one)
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  exact ⟨u, ⟨L, hadd, hsmul, hnn, hone⟩, hle, hLtend⟩

#print axioms exists_limit_state

/-! ## Part 3 — the DLR property at the limit

A specification is carried by its action on observables, `γ k : C(X, ℝ) → C(X, ℝ)`. That a
finite-volume kernel with boundary conditions sends continuous functions to continuous functions —
the Feller property — is therefore carried by the type of `γ` and is a hypothesis on whoever supplies
it. The DLR equation is an equality of two numbers, so it passes to limits by uniqueness of
limits. -/

/-- `∀ (k : κ) (f : C(X, ℝ)), ν (γ k f) = ν f`: the state is unmoved by every kernel of the
specification `γ`, read through its action on observables.

DERIVED: no numeral appears in the statement. -/
def IsDLR {κ : Type*} (γ : κ → C(X, ℝ) → C(X, ℝ)) (ν : State X) : Prop :=
  ∀ (k : κ) (f : C(X, ℝ)), ν (γ k f) = ν f

#print axioms IsDLR

/-- If `μ i f → ν f` along `l` at every observable, and `fun i => μ i (γ k f)` agrees with
`fun i => μ i f` eventually along `l` for every `k` and `f`, then `IsDLR γ ν`. It is
`tendsto_nhds_unique` on the two sequences, which have the same eventual values.

Scope: the hypothesis `hev` is the finite-volume consistency, required only eventually.

DERIVED: no numeral appears in the statement. -/
theorem isDLR_of_tendsto {ι κ : Type*} {l : Filter ι} [l.NeBot] {γ : κ → C(X, ℝ) → C(X, ℝ)}
    (μ : ι → State X) (ν : State X)
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (hev : ∀ (k : κ) (f : C(X, ℝ)),
      (fun i => μ i (γ k f)) =ᶠ[l] (fun i => μ i f)) :
    IsDLR γ ν := by
  intro k f
  exact tendsto_nhds_unique ((htend (γ k f)).congr' (hev k f)) (htend f)

#print axioms isDLR_of_tendsto


/-- If every state satisfying `IsDLR γ` equals `ν`, and the finite-volume consistency `hev` holds
eventually along `l`, then `μ i f → ν f` along `l` itself at every observable.

`Filter.tendsto_iff_ultrafilter` reduces it to every refining ultrafilter `u`. `exists_limit_state`
at `u` produces a limit state `ν'` — and `u.unique` makes the refining ultrafilter `u` itself —
`isDLR_of_tendsto` gives `IsDLR γ ν'`, and `huniq` identifies `ν'` with `ν`.

Scope: `huniq` is a hypothesis, and it is what upgrades the ultrafilter limit of
`exists_limit_state` to convergence along `l`. `WilsonDLR.dlr_unique_at_zero_eq` supplies it for the
Wilson specification at coupling zero, where the kernel does not read the boundary.

DERIVED: no numeral appears in the statement. -/
theorem tendsto_of_unique_dlr {ι κ : Type*} {l : Filter ι} [l.NeBot]
    {γ : κ → C(X, ℝ) → C(X, ℝ)} (μ : ι → State X) (ν : State X)
    (hev : ∀ (k : κ) (f : C(X, ℝ)),
      (fun i => μ i (γ k f)) =ᶠ[l] (fun i => μ i f))
    (huniq : ∀ ν' : State X, IsDLR γ ν' → ν' = ν) :
    ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)) := by
  intro f
  rw [Filter.tendsto_iff_ultrafilter]
  intro u hu
  haveI : (u : Filter ι).NeBot := u.neBot'
  obtain ⟨u', ν', hle, htend'⟩ := exists_limit_state (X := X) (u : Filter ι) μ
  -- an ultrafilter below an ultrafilter is that ultrafilter
  have hueq : (u' : Filter ι) = (u : Filter ι) := u.unique hle
  have htendu : ∀ g : C(X, ℝ), Tendsto (fun i => μ i g) (u : Filter ι) (𝓝 (ν' g)) := by
    intro g
    have := htend' g
    rwa [hueq] at this
  have hevu : ∀ (k : κ) (g : C(X, ℝ)),
      (fun i => μ i (γ k g)) =ᶠ[(u : Filter ι)] (fun i => μ i g) := by
    intro k g
    exact (hev k g).filter_mono hu
  have hdlr : IsDLR γ ν' := isDLR_of_tendsto (l := (u : Filter ι)) μ ν' htendu hevu
  have : ν' = ν := huniq ν' hdlr
  rw [← this]
  exact htendu f

#print axioms tendsto_of_unique_dlr


/-- For a `SemilatticeSup` index `ι` and a family `μ : ι → State X` with `μ i (γ j f) = μ i f` at
every `j ≤ i`, there are an ultrafilter `u ≤ atTop` and a state `ν` with `μ i f → ν f` along `u` at
every observable, satisfying `IsDLR γ ν`.

`exists_limit_state` gives the limit and `isDLR_of_tendsto` the consistency; the eventual form of
`hcons` comes from `eventually_ge_atTop j`, which is where the index's directedness is used.

Scope: `hcons` is a hypothesis. The conclusion is along `u`, not along `atTop`.

DERIVED: no numeral appears in the statement. -/
theorem exists_dlr_state {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    (γ : ι → C(X, ℝ) → C(X, ℝ)) (μ : ι → State X)
    (hcons : ∀ i j : ι, j ≤ i → ∀ f : C(X, ℝ), μ i (γ j f) = μ i f) :
    ∃ (u : Ultrafilter ι) (ν : State X),
      (u : Filter ι) ≤ atTop ∧
      (∀ f : C(X, ℝ), Tendsto (fun i => μ i f) (u : Filter ι) (𝓝 (ν f))) ∧
      IsDLR γ ν := by
  classical
  obtain ⟨u, ν, hle, htend⟩ := exists_limit_state (atTop : Filter ι) μ
  haveI hub : (u : Filter ι).NeBot := u.neBot'
  refine ⟨u, ν, hle, htend, ?_⟩
  refine isDLR_of_tendsto μ ν htend ?_
  intro j f
  show ∀ᶠ i in (u : Filter ι), μ i (γ j f) = μ i f
  have hge : ∀ᶠ i in (u : Filter ι), j ≤ i := (eventually_ge_atTop j).filter_mono hle
  filter_upwards [hge] with i hi using hcons i j hi f

#print axioms exists_dlr_state

/-! ## Part 4 — excluding a point mass, from a variance floor

`ν 1 = 1` is a field of `State`, so it holds of the limit by construction; it excludes the zero
functional and nothing else. A limit of point masses is a point mass, so excluding one needs more
input. What the theorems below take is a variance floor at a single observable, holding uniformly in
the index.

`InfiniteVolume.exists_uniform_contact_floor` supplies one `δ₀ > 0`, fixed before the aperture, with
`exp (-128 * β) * δ₀ ≤ wilsonCorrAt N β 0` at every aperture and every `β ≥ 0`, and
`PlaqVariance.corrClay_zero_eq` makes that contact value a plaquette variance;
`ClayNontriviality.clay_nontriviality_of_wilson_variance` composes it with
`not_isPointMass_of_uniform_variance`. The bridge between that aperture indexing and the
`Finset ILink` indexing used here is not in this file. -/

/-- `∃ x : X, ∀ f : C(X, ℝ), ν f = f x`: the state is evaluation at a single point.

DERIVED: no numeral appears in the statement. -/
def IsPointMass (ν : State X) : Prop := ∃ x : X, ∀ f : C(X, ℝ), ν f = f x

#print axioms IsPointMass

/-- `ν (f * f) - (ν f) ^ 2 = 0` at every observable, for a point mass: both terms evaluate to
`f x ^ 2` at the witness point.

DERIVED: the exponent `2` is the square in the variance; `0` is its value at a point mass. -/
theorem variance_eq_zero_of_isPointMass {ν : State X} (h : IsPointMass ν) (f : C(X, ℝ)) :
    ν (f * f) - (ν f) ^ 2 = 0 := by
  obtain ⟨x, hx⟩ := h
  simp only [hx, ContinuousMap.mul_apply]
  ring

#print axioms variance_eq_zero_of_isPointMass

/-- `¬ IsPointMass ν` whenever some observable has `0 < ν (f * f) - (ν f) ^ 2`, by
`variance_eq_zero_of_isPointMass`.

DERIVED: `0` is the strict lower bound on the variance; the exponent `2` is the square in it. -/
theorem not_isPointMass_of_variance_pos {ν : State X} {f : C(X, ℝ)}
    (h : 0 < ν (f * f) - (ν f) ^ 2) : ¬ IsPointMass ν := by
  intro hp
  rw [variance_eq_zero_of_isPointMass hp f] at h
  exact lt_irrefl _ h

#print axioms not_isPointMass_of_variance_pos

/-- `c ≤ ν f` whenever `c ≤ μ i f` eventually along `l` and `μ i f → ν f`, by `ge_of_tendsto`.

DERIVED: no numeral appears in the statement; `c` is the caller's bound. -/
theorem le_of_eventually_le {ι : Type*} {l : Filter ι} [l.NeBot] {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (f : C(X, ℝ)) (c : ℝ) (h : ∀ᶠ i in l, c ≤ μ i f) : c ≤ ν f :=
  ge_of_tendsto (htend f) h

#print axioms le_of_eventually_le

/-- `c ≤ ν (f * f) - (ν f) ^ 2` whenever `c ≤ μ i (f * f) - (μ i f) ^ 2` eventually along `l`. The
variance is built from two convergent sequences by subtraction and squaring, so
`Tendsto.sub` and `Tendsto.pow` give its convergence and `ge_of_tendsto` the bound.

DERIVED: the exponent `2` occurs twice, as the square in the finite-index variance and in the limit
variance. -/
theorem variance_ge_of_eventually {ι : Type*} {l : Filter ι} [l.NeBot] {μ : ι → State X}
    {ν : State X} (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (f : C(X, ℝ)) (c : ℝ) (h : ∀ᶠ i in l, c ≤ μ i (f * f) - (μ i f) ^ 2) :
    c ≤ ν (f * f) - (ν f) ^ 2 :=
  ge_of_tendsto ((htend (f * f)).sub ((htend f).pow 2)) h

#print axioms variance_ge_of_eventually

/-- Given `0 < c` and a variance floor `c ≤ μ i (f * f) - (μ i f) ^ 2` holding eventually along `l`,
the limit satisfies `ν 1 = 1` and `¬ IsPointMass ν`. The first is `State.map_one`, true by
construction; the second is `variance_ge_of_eventually` followed by
`not_isPointMass_of_variance_pos`.

Scope: the floor is a hypothesis at a single observable, holding uniformly in the index. `ν 1 = 1`
excludes the zero functional and nothing else.

DERIVED: `0` is the strict lower bound on `c`; the exponent `2` is the square in the variance; `1`
occurs twice, as the constant observable and as its value under `ν`. -/
theorem not_isPointMass_of_uniform_variance {ι : Type*} {l : Filter ι} [l.NeBot]
    {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (f : C(X, ℝ)) (c : ℝ) (hc : 0 < c)
    (h : ∀ᶠ i in l, c ≤ μ i (f * f) - (μ i f) ^ 2) :
    ν 1 = 1 ∧ ¬ IsPointMass ν :=
  ⟨ν.map_one, not_isPointMass_of_variance_pos
    (lt_of_lt_of_le hc (variance_ge_of_eventually htend f c h))⟩

#print axioms not_isPointMass_of_uniform_variance

/-! ## Part 5 — the state as a measure

Riesz–Markov–Kakutani, following `MomentMeasure.stateCc` and `MomentMeasure.spectralMeasure`: on a
compact space every continuous function is compactly supported, so a state is a positive linear map
on `C_c(X, ℝ)` and `RealRMK.rieszMeasure` represents it. The measure is a probability measure because
the state is normalised, which is the `f = 1` case of the representation. -/

section Measure

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The state as a `C_c(X, ℝ) →ₚ[ℝ] ℝ`: the positive linear map Riesz–Markov–Kakutani consumes. On a
compact space every continuous function is compactly supported, so the underlying function is
`fun f => ν f.toContinuousMap`. Additivity and homogeneity are the state's own; monotonicity is
positivity applied to the difference.

DERIVED: no numeral appears in the statement. The `0` in the monotonicity obligation is the lower
bound in `0 ≤ ν (g - f)`, which is what nonnegativity means. -/
def stateCc (ν : State X) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := ν f.toContinuousMap
  map_add' f g := by
    show ν (f + g).toContinuousMap = ν f.toContinuousMap + ν g.toContinuousMap
    rw [← ν.map_add]
    rfl
  map_smul' r f := by
    show ν (r • f).toContinuousMap = (RingHom.id ℝ) r • ν f.toContinuousMap
    rw [RingHom.id_apply, smul_eq_mul, ← ν.map_smul]
    rfl
  monotone' := by
    intro f g hfg
    have hsub : 0 ≤ ν (g.toContinuousMap - f.toContinuousMap) := by
      refine ν.nonneg _ (fun x => ?_)
      have hx := CompactlySupportedContinuousMap.le_def.mp hfg x
      simpa using hx
    rw [ν.map_sub] at hsub
    show ν f.toContinuousMap ≤ ν g.toContinuousMap
    linarith

#print axioms stateCc

/-- `RealRMK.rieszMeasure (stateCc ν)`: the Riesz–Markov–Kakutani representative of the state, as a
`MeasureTheory.Measure X`. `integral_gibbsMeasure` states the representation and
`instIsProbabilityMeasure` the total mass.

DERIVED: no numeral appears in the statement. -/
noncomputable def gibbsMeasure (ν : State X) : MeasureTheory.Measure X :=
  RealRMK.rieszMeasure (stateCc ν)

#print axioms gibbsMeasure

instance instIsFiniteMeasure (ν : State X) : MeasureTheory.IsFiniteMeasure (gibbsMeasure ν) :=
  inferInstanceAs (MeasureTheory.IsFiniteMeasure (RealRMK.rieszMeasure (stateCc ν)))

#print axioms instIsFiniteMeasure

/-- `∫ x, f x ∂(gibbsMeasure ν) = ν f` at every continuous observable. The observable is transported
to `C_c(X, ℝ)` by `CompactlySupportedContinuousMap.continuousMapEquiv` — the two agree pointwise on a
compact space — and `RealRMK.integral_rieszMeasure` evaluates the integral.

DERIVED: no numeral appears in the statement. -/
theorem integral_gibbsMeasure (ν : State X) (f : C(X, ℝ)) :
    ∫ x, f x ∂(gibbsMeasure ν) = ν f := by
  set F : C_c(X, ℝ) := CompactlySupportedContinuousMap.continuousMapEquiv f with hF
  have hFval : ∀ x : X, F x = f x := by intro x; simp [hF]
  rw [gibbsMeasure]
  calc ∫ x, f x ∂(RealRMK.rieszMeasure (stateCc ν))
      = ∫ x, F x ∂(RealRMK.rieszMeasure (stateCc ν)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => (hFval x).symm)
    _ = stateCc ν F := RealRMK.integral_rieszMeasure (stateCc ν) F
    _ = ν f := rfl

#print axioms integral_gibbsMeasure

/-- `(gibbsMeasure ν Set.univ).toReal = 1`. It is `integral_gibbsMeasure` at the constant observable
`1`, where `State.map_one` gives the right side and `MeasureTheory.integral_const` the left.
`(1 : C(X, ℝ)) x` is `(1 : ℝ)` definitionally, so no rewriting is needed at that step.

DERIVED: `1` is the total mass, which is the state's value at the constant observable `1`. -/
theorem gibbsMeasure_univ_toReal (ν : State X) : (gibbsMeasure ν Set.univ).toReal = 1 := by
  have h := integral_gibbsMeasure ν 1
  rw [ν.map_one] at h
  have h1 : (∫ _x : X, (1 : ℝ) ∂(gibbsMeasure ν)) = 1 := h
  rw [MeasureTheory.integral_const, smul_eq_mul, mul_one] at h1
  exact h1

#print axioms gibbsMeasure_univ_toReal

/-- `MeasureTheory.IsProbabilityMeasure (gibbsMeasure ν)`. The measure is finite, so
`ENNReal.ofReal_toReal` transports `gibbsMeasure_univ_toReal` back to `ENNReal`.

DERIVED: no numeral appears in the statement; the total mass one is inside
`IsProbabilityMeasure`. -/
instance instIsProbabilityMeasure (ν : State X) :
    MeasureTheory.IsProbabilityMeasure (gibbsMeasure ν) := by
  refine ⟨?_⟩
  have hne : gibbsMeasure ν Set.univ ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have h2 : ENNReal.ofReal ((gibbsMeasure ν Set.univ).toReal) = gibbsMeasure ν Set.univ :=
    ENNReal.ofReal_toReal hne
  rw [gibbsMeasure_univ_toReal ν] at h2
  rw [← h2]
  simp

#print axioms instIsProbabilityMeasure

end Measure

/-! ## Part 6 — the instantiation at `Finset ILink` and `IConf G`

`Finset ILink` is a `SemilatticeSup` with a bottom element, so `atTop` is `NeBot` and the
directedness hypothesis of `exists_dlr_state` is discharged by the lattice structure of finite sets.
`IConf G` is compact by Part 0. -/

/-- `exists_dlr_state` at `ι := Finset ILink` and `X := IConf G`, with normalisation and positivity
of the limit re-exported: there are an ultrafilter `u ≤ atTop` and a state `ν` on `C(IConf G, ℝ)`
with `μ Λ f → ν f` along `u` at every observable, satisfying `IsDLR γ ν`, `ν 1 = 1`, and
`0 ≤ ν f` for every pointwise nonnegative `f`.

Scope: `γ` and `μ` are hypotheses — a specification applied to observables and a family of
finite-volume states — and `hcons` is their consistency. No Wilson action enters, and the limit is
along `u` rather than along `atTop`. The last two conjuncts are fields of `State`, re-exported for
readability.

DERIVED: `1` occurs twice, as the constant observable and as its value under `ν`; `0` occurs twice,
as the pointwise lower bound on `f` and as the lower bound on `ν f`. -/
theorem exists_infinite_volume_gibbs_state (G : Type) [TopologicalSpace G] [CompactSpace G]
    (γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ))
    (μ : Finset ILink → State (IConf G))
    (hcons : ∀ Λ Λ' : Finset ILink, Λ' ≤ Λ → ∀ f : C(IConf G, ℝ), μ Λ (γ Λ' f) = μ Λ f) :
    ∃ (u : Ultrafilter (Finset ILink)) (ν : State (IConf G)),
      (u : Filter (Finset ILink)) ≤ atTop ∧
      (∀ f : C(IConf G, ℝ), Tendsto (fun Λ => μ Λ f) (u : Filter (Finset ILink)) (𝓝 (ν f))) ∧
      IsDLR γ ν ∧ ν 1 = 1 ∧ ∀ f : C(IConf G, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ ν f := by
  classical
  obtain ⟨u, ν, hle, htend, hdlr⟩ := exists_dlr_state γ μ hcons
  exact ⟨u, ν, hle, htend, hdlr, ν.map_one, fun f hf => ν.nonneg f hf⟩

#print axioms exists_infinite_volume_gibbs_state

/-- `exists_infinite_volume_gibbs_state` with a variance floor attached: given `0 < c` and
`c ≤ μ Λ (f₀ * f₀) - (μ Λ f₀) ^ 2` at every finite volume, there is a state `ν` with `IsDLR γ ν`,
`ν 1 = 1` and `¬ IsPointMass ν`. It is `exists_dlr_state` followed by
`not_isPointMass_of_uniform_variance`, the eventual form of the floor coming from
`Filter.Eventually.of_forall`.

Scope: `hvar` is a hypothesis at every volume, stronger than the eventual form
`not_isPointMass_of_uniform_variance` takes. `ν 1 = 1` excludes the zero functional and nothing
else; the variance floor is what excludes a point mass.

DERIVED: `0` is the strict lower bound on `c`; the exponent `2` is the square in the variance; `1`
occurs twice, as the constant observable and as its value under `ν`. -/
theorem exists_infinite_volume_gibbs_state_nondegenerate (G : Type) [TopologicalSpace G]
    [CompactSpace G]
    (γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ))
    (μ : Finset ILink → State (IConf G))
    (hcons : ∀ Λ Λ' : Finset ILink, Λ' ≤ Λ → ∀ f : C(IConf G, ℝ), μ Λ (γ Λ' f) = μ Λ f)
    (f₀ : C(IConf G, ℝ)) (c : ℝ) (hc : 0 < c)
    -- `hvar` is supplied by the caller; nothing in this file derives a variance floor.
    (hvar : ∀ Λ : Finset ILink, c ≤ μ Λ (f₀ * f₀) - (μ Λ f₀) ^ 2) :
    ∃ ν : State (IConf G), IsDLR γ ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν := by
  classical
  obtain ⟨u, ν, _hle, htend, hdlr⟩ := exists_dlr_state γ μ hcons
  haveI hub : (u : Filter (Finset ILink)).NeBot := u.neBot'
  obtain ⟨hone, hpm⟩ :=
    not_isPointMass_of_uniform_variance htend f₀ c hc (Filter.Eventually.of_forall hvar)
  exact ⟨ν, hdlr, hone, hpm⟩

#print axioms exists_infinite_volume_gibbs_state_nondegenerate

/-! ### The limit state as a measure on `IConf G`

`gibbsMeasure` needs the Borel structure of `IConf G` to be its product σ-algebra, and over an
infinite index those agree only when the index is countable and the factor second countable.
`ILink = Fin 4 × (Fin 4 → ℤ)` is countable, so the hypothesis lands on the gauge group. -/

/-- `BorelSpace (IConf G)` for a second-countable `G` with its Borel structure, by `inferInstance`.
This is where the countability of `ILink` is spent: without it the product σ-algebra would be
strictly smaller than the topology's Borel σ-algebra, and `gibbsMeasure` would name a measure on the
wrong one.

DERIVED: no numeral appears in the statement. -/
theorem borelSpace_iconf (G : Type) [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] : BorelSpace (IConf G) := inferInstance

#print axioms borelSpace_iconf

/-- The same limit as a measure: there are a probability measure `P` on `IConf G` and a state `ν`
with `∫ U, f U ∂P = ν f` at every continuous observable and `IsDLR γ ν`. It is `exists_dlr_state`
followed by `gibbsMeasure`, `integral_gibbsMeasure` and `instIsProbabilityMeasure`.

Scope: `P` is a measure on the configuration space of the full lattice, not a sequence of
finite-volume numbers. `γ` and `μ` remain hypotheses, so nothing ties `P` to the Wilson action. The
extra instances on `G` — Hausdorff, second countable, Borel — are what `gibbsMeasure` and
`borelSpace_iconf` require.

DERIVED: no numeral appears in the statement. -/
theorem exists_infinite_volume_gibbs_measure (G : Type) [TopologicalSpace G] [CompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ))
    (μ : Finset ILink → State (IConf G))
    (hcons : ∀ Λ Λ' : Finset ILink, Λ' ≤ Λ → ∀ f : C(IConf G, ℝ), μ Λ (γ Λ' f) = μ Λ f) :
    ∃ (P : MeasureTheory.Measure (IConf G)) (ν : State (IConf G)),
      MeasureTheory.IsProbabilityMeasure P ∧
      (∀ f : C(IConf G, ℝ), ∫ U, f U ∂P = ν f) ∧ IsDLR γ ν := by
  obtain ⟨_u, ν, _hle, _htend, hdlr⟩ := exists_dlr_state γ μ hcons
  exact ⟨gibbsMeasure ν, ν, instIsProbabilityMeasure ν, integral_gibbsMeasure ν, hdlr⟩

#print axioms exists_infinite_volume_gibbs_measure

end MassGap.DLRLimit
