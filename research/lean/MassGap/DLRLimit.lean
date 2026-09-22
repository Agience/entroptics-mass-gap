import Mathlib

/-!
# MassGap.DLRLimit — existence of the infinite-volume (DLR) state

The Yang–Mills development has no infinite-volume Gibbs measure, and the Clay rows that speak about
one (A5, A6, B1, B5, B6) all run through the object this file builds: a state on the continuous
functions of the FULL lattice configuration space `IConf G = ILink → G`, obtained as a limit of
finite-volume states and inheriting their consistency relation.

## Why this is compactness and not analysis

`IConf G` is a product of copies of a compact group, so it is compact by Tychonoff
(`compactSpace_iconf`, which is `Pi.compactSpace` and nothing else). On a compact space the states
on `C(X, ℝ)` — positive normalised linear functionals — are uniformly bounded, `|ν f| ≤ ‖f‖`
(`State.abs_le_norm`), by positivity alone. So each coordinate `ν ↦ ν f` of the finite-volume family
lives in the fixed compact interval `[−‖f‖, ‖f‖]`, an ultrafilter converges in every one of them at
once, and the limit is again a state because linearity, positivity and normalisation are each
preserved by `tendsto_nhds_unique` or `ge_of_tendsto`. That is the whole existence argument.

## Which of the two Mathlib routes, and why

Two formulations were available in Mathlib v4.31.

* **States on `C(X, ℝ)`** — the route taken. The compactness used here is
  `isCompact_Icc.ultrafilter_le_nhds`, ONE interval per observable, which is the Banach–Alaoglu
  argument specialised to the case where the bound is uniform by positivity. It needs no normed-dual
  API at all, and it is the same move `InfiniteVolume.exists_filter_tendsto_all_lags` already makes
  one level down (there the coordinates are lags, here they are observables). The measure is then
  recovered by Riesz–Markov–Kakutani, for which this tree already carries a worked instance:
  `MomentMeasure.stateCc` / `MomentMeasure.spectralMeasure` build `RealRMK.rieszMeasure` out of a
  `C_c(·, ℝ) →ₚ[ℝ] ℝ`, and `gibbsMeasure` below reuses that pattern verbatim.
* **`MeasureTheory.ProbabilityMeasure X` with the weak topology.** Not taken. Mathlib has the type
  and the portmanteau lemmas, but the statement this file needs — that the space of probability
  measures on a compact space is itself compact — is the conclusion of Prokhorov's theorem, whose
  Mathlib development is partial: what is available is tightness ⇒ relative compactness for the
  finite-measure space, and the identification of weak convergence with convergence of integrals of
  bounded continuous functions. Going that way would have meant proving the compactness statement
  anyway, and proving it the same way — through `C(X, ℝ)`. So the functional route is not merely
  cheaper here, it is a strict prefix of the measure route.

## What is proved

* `State` — a positive normalised linear functional on `C(X, ℝ)`, `X` compact, with the elementary
  consequences `State.mono`, `State.abs_le_norm`, `State.mem_Icc`.
* `exists_limit_state` — for ANY `NeBot` filter `l` on ANY index type and ANY family of states, an
  ultrafilter `u ≤ l` and a state `ν` with `μ i f → ν f` along `u`, SIMULTANEOUSLY for every
  observable `f`. This is the existence theorem; everything after it is inheritance.
* `isDLR_of_tendsto` — the consistency relation is closed under such limits. Stated for an abstract
  specification `γ : κ → C(X, ℝ) → C(X, ℝ)` acting on observables, because that is the shape a
  finite-volume kernel with boundary conditions takes once it is applied to a function: the Feller
  property (a kernel sends continuous functions to continuous functions) is carried by the TYPE of
  `γ` and is therefore a hypothesis on whoever supplies it.
* `exists_dlr_state` — the assembly, over a directed index: finite-volume states consistent for every
  smaller volume have a limit state consistent for EVERY volume.
* `exists_infinite_volume_gibbs_state` — the same statement with the index specialised to
  `Finset ILink` and the space to `IConf G`. This is the infinite-volume object.
* `gibbsMeasure` — the limit state as a genuine `MeasureTheory.Measure`, a probability measure whose
  integral against every continuous observable is the state's value.
* `exists_infinite_volume_gibbs_measure` — the same at `IConf G`. This spends the countability of
  `ILink`: the Borel structure of the product topology and the product σ-algebra coincide only over a
  countable index, so `SecondCountableTopology G` is a hypothesis here and not in the state version.
* `not_isPointMass_of_variance_pos`, `variance_ge_of_eventually` — the non-degeneracy check.

## What is NOT proved

Uniqueness, translation invariance, and any connection to the Wilson action. `γ` here is abstract;
nothing in this file says the finite-volume states are the Wilson–Gibbs states or that `γ` is their
kernel. The limit is subsequential in the same sense `InfiniteVolume` is: an ultrafilter refining
`atTop` exists, nothing shows the net itself converges.

Non-degeneracy beyond normalisation. `ν 1 = 1` is a field of `State` and is re-exported in the
conclusions below for readability, not as evidence: it rules out the ZERO functional and nothing
else. Ruling out a POINT MASS is strictly stronger and is proved here only CONDITIONALLY, on a
variance floor `c ≤ μ_Λ(f₀²) − μ_Λ(f₀)²` holding uniformly in the volume. ⛔ THIS PARAGRAPH IS STALE — `InfiniteVolume.exists_uniform_contact_floor` supplies such a floor, as this file's own Part 6 prose records. What follows was written before it and is kept only for the distinction it draws:
 `GibbsPositive.corrNum_plaqObs_pos` bounds a finite-volume correlation below at a FIXED
volume, with no statement that the bound survives the volume growing, and a variance is not a
correlation. Supplying it is open work, and until it is supplied the infinite-volume state here is
not known to be spread out.

DERIVED: `4` is the problem's dimension. `1` is the unit of `C(X, ℝ)` and the normalisation of a
probability state. No constant is chosen here and none is fitted.

Build: `python research/code/lean_build.py build MassGap.DLRLimit`.
-/

namespace MassGap.DLRLimit

open Filter
open scoped Topology CompactlySupported

/-! ## Part 0 — the shared skeleton

Written here rather than imported so that this file stands alone. The four declarations are the
skeleton agreed for `MassGap.InfiniteLattice`; being `abbrev`s they are reducible, so the two copies
are interchangeable wherever both are in scope. -/

/-- A site of the infinite four-dimensional lattice.

DERIVED: `4` is the number of spacetime directions — the dimension of the Clay statement, the same
`d` that `WilsonHypercubic` is instantiated at for the Clay instance (`bd (d := 4)` in `AreaLaw`).
It is an index range, not an extent: the coordinate in each of the four directions is all of `ℤ`. -/
abbrev ISite : Type := Fin 4 → ℤ

#print axioms ISite

/-- An oriented link: a direction and the site it leaves.

DERIVED: `4` is the dimension again — a link's direction ranges over the four spacetime directions,
so `Fin 4` is the direction index and nothing else. Same constant as in `ISite`, not a second one. -/
abbrev ILink : Type := Fin 4 × ISite

#print axioms ILink

/-- A plaquette: a plane and the site at its corner.

DERIVED: both `4`s are the dimension, written twice because a plane in `d` dimensions is spanned by
an ORDERED PAIR of directions (`WilsonHypercubic.Plaq` carries the same pair for the same reason).
The pair is the dimension used twice, not a separate constant. -/
abbrev IPlaq : Type := (Fin 4 × Fin 4) × ISite

#print axioms IPlaq

/-- A configuration of the infinite lattice: one group element per link. -/
abbrev IConf (G : Type) : Type := ILink → G

#print axioms IConf

/-- **Tychonoff.** The configuration space of the INFINITE lattice is compact whenever the gauge
group is. Nothing is proved here that `Pi.compactSpace` does not already say; the point is that the
instance fires at this type, which is what makes every compactness argument below available at
`IConf G`. -/
theorem compactSpace_iconf (G : Type) [TopologicalSpace G] [CompactSpace G] :
    CompactSpace (IConf G) := inferInstance

#print axioms compactSpace_iconf

/-! ## Part 1 — states

A state is a positive normalised linear functional on the continuous functions. On a compact space
that is exactly a probability measure (Part 6), but the functional is the object the limit argument
moves, so it is the primitive here. -/

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **A state on `C(X, ℝ)`**: linear, positive, normalised. -/
structure State (X : Type*) [TopologicalSpace X] [CompactSpace X] where
  /-- The underlying functional. -/
  toFun : C(X, ℝ) → ℝ
  /-- Additivity. -/
  map_add' : ∀ f g : C(X, ℝ), toFun (f + g) = toFun f + toFun g
  /-- Homogeneity. -/
  map_smul' : ∀ (c : ℝ) (f : C(X, ℝ)), toFun (c • f) = c * toFun f
  /-- Positivity: a pointwise nonnegative observable has a nonnegative value. -/
  nonneg' : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ toFun f
  /-- Normalisation. -/
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

/-- **A state is monotone.** Positivity applied to the difference. -/
theorem State.mono (ν : State X) {f g : C(X, ℝ)} (h : ∀ x, f x ≤ g x) : ν f ≤ ν g := by
  have h0 : 0 ≤ ν (g - f) := ν.nonneg _ (fun x => by simpa using sub_nonneg.mpr (h x))
  rw [ν.map_sub] at h0
  linarith

#print axioms State.mono

/-- **A state is bounded above by the sup norm** — no continuity hypothesis is needed, positivity
and normalisation give it. This is the uniform bound the compactness argument runs on. -/
theorem State.le_norm (ν : State X) (f : C(X, ℝ)) : ν f ≤ ‖f‖ := by
  have hle : ∀ x, f x ≤ ((‖f‖ : ℝ) • (1 : C(X, ℝ))) x := by
    intro x
    have h1 : ‖f x‖ ≤ ‖f‖ := f.norm_coe_le_norm x
    have h2 : f x ≤ ‖f‖ := le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at h1)
    simpa using h2
  have h3 := ν.mono hle
  rwa [ν.map_smul, ν.map_one, mul_one] at h3

#print axioms State.le_norm

/-- **A state is bounded by the sup norm**, both signs. -/
theorem State.abs_le_norm (ν : State X) (f : C(X, ℝ)) : |ν f| ≤ ‖f‖ := by
  refine abs_le.mpr ⟨?_, ν.le_norm f⟩
  have h := ν.le_norm (-f)
  rw [ν.map_neg, norm_neg] at h
  linarith

#print axioms State.abs_le_norm

/-- Every state's value at `f` lies in ONE compact interval, fixed by `f` alone and independent of
the state. This is the whole input to the compactness step. -/
theorem State.mem_Icc (ν : State X) (f : C(X, ℝ)) : ν f ∈ Set.Icc (-‖f‖) ‖f‖ :=
  Set.mem_Icc.mpr (abs_le.mp (ν.abs_le_norm f))

#print axioms State.mem_Icc


/-- **A STATE IS 1-LIPSCHITZ.** `|ν f - ν g| = |ν (f - g)| ≤ ‖f - g‖`, which is `State.map_sub`
followed by `State.abs_le_norm`.

DERIVED: the `1` is the Lipschitz constant, and it is forced — a state is unital and positive, so
it cannot expand the sup norm. -/
theorem State.abs_sub_le (ν : State X) (f g : C(X, ℝ)) : |ν f - ν g| ≤ ‖f - g‖ := by
  rw [← ν.map_sub]
  exact ν.abs_le_norm (f - g)

#print axioms State.abs_sub_le

/-- **So it is continuous as a function of the observable.**

DERIVED: no numeral. -/
theorem State.continuous (ν : State X) : Continuous (fun f : C(X, ℝ) => ν f) := by
  refine Metric.continuous_iff.mpr (fun f ε hε => ⟨ε, hε, fun g hg => ?_⟩)
  have h := ν.abs_sub_le g f
  rw [Real.dist_eq]
  have hgf : ‖g - f‖ < ε := by rwa [dist_eq_norm] at hg
  exact lt_of_le_of_lt h hgf

#print axioms State.continuous

/-- **⭐⭐ AND TWO STATES AGREEING ON A DENSE SET ARE EQUAL.**

This is the half of DLR uniqueness that does not depend on the model. Uniqueness splits in two:
a DLR state is pinned on LOCAL observables by the specification, and a state is determined by its
values on a dense set. The first is Wilson-specific; **this is the second, and it is general**.

The local observables are a subalgebra (`InfiniteLattice.quasiLocalAlg`); that they are DENSE is a
Stone–Weierstrass statement and is not proved in this tree.

DERIVED: no numeral. -/
theorem State.eq_of_eqOn_dense {ν₁ ν₂ : State X} {s : Set C(X, ℝ)} (hs : Dense s)
    (h : ∀ f ∈ s, ν₁ f = ν₂ f) : ∀ f : C(X, ℝ), ν₁ f = ν₂ f := by
  have := Continuous.ext_on hs ν₁.continuous ν₂.continuous h
  exact fun f => congrFun this f

#print axioms State.eq_of_eqOn_dense

/-- **⭐ A STATE IS DETERMINED BY A POINT-SEPARATING SUBALGEBRA.**

The density hypothesis of `State.eq_of_eqOn_dense` is replaced by the one a model can check: that
the subalgebra tells points apart. Stone–Weierstrass
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`) turns separation into
density on a compact space, and a state is continuous, so agreement propagates from the subalgebra
to everything.

DERIVED: no numeral. -/
theorem State.eq_of_eqOn_subalgebra {ν₁ ν₂ : State X} (A : Subalgebra ℝ C(X, ℝ))
    (hsep : A.SeparatesPoints) (h : ∀ f ∈ A, ν₁ f = ν₂ f) : ∀ f : C(X, ℝ), ν₁ f = ν₂ f := by
  have htop : A.topologicalClosure = ⊤ :=
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hdense : Dense (A : Set C(X, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, htop]
    simp
  exact State.eq_of_eqOn_dense hdense h

#print axioms State.eq_of_eqOn_subalgebra

/-- **A STATE FORCES ITS SPACE TO BE INHABITED.** On an empty space the constant-one observable IS
the zero observable, so `ν 1 = 1` and `ν 0 = 0` collide. Anything that needs a base configuration
can take one from the state itself.

DERIVED: the `1` and `0` are the two values a state takes on the unit and the zero observable,
`State.map_one` and `State.map_zero`. -/
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

/-- **A STATE IS ITS FUNCTIONAL.** The other four fields are Props, so they are equal by proof
irrelevance once the functionals are. This is what `tendsto_of_unique_dlr` needs: it asks for
equality of STATES, and a uniqueness argument delivers agreement at every observable.

DERIVED: no numeral. -/
theorem State.eq_of_apply_eq {ν₁ ν₂ : State X} (h : ∀ f : C(X, ℝ), ν₁ f = ν₂ f) : ν₁ = ν₂ := by
  obtain ⟨t₁, _, _, _, _⟩ := ν₁
  obtain ⟨t₂, _, _, _, _⟩ := ν₂
  have ht : t₁ = t₂ := funext (fun f => h f)
  subst ht
  rfl

#print axioms State.eq_of_apply_eq



section LocalObservables

variable {G : Type} [TopologicalSpace G] [CompactSpace G]

/-- A BUNDLED continuous observable is LOCAL on `S` when it does not move as the links outside `S`
move. The unbundled twin is `InfiniteLattice.IsLocalOn`; the only difference is that continuity is
carried by the bundling here rather than by a conjunct.

DERIVED: no numeral. -/
def IsLocalOnC (S : Finset ILink) (F : C(IConf G, ℝ)) : Prop :=
  ∀ U V : IConf G, (∀ l ∈ S, U l = V l) → F U = F V

#print axioms IsLocalOnC

/-- **THE LOCAL OBSERVABLES AS A SUBALGEBRA OF `C(IConf G, ℝ)`.** A product of two observables
reading disjoint finite link sets reads their union, which is again finite; that is the whole
closure argument, and it is the same one `InfiniteLattice.quasiLocalAlg` makes one coercion away.

DERIVED: no numeral. -/
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

/-- Membership in `localObsAlg` is exactly locality on SOME finite link set. Mirrors
`InfiniteLattice.mem_quasiLocalAlg`, one coercion away.

DERIVED: no numeral. -/
theorem mem_localObsAlg {F : C(IConf G, ℝ)} :
    F ∈ localObsAlg G ↔ ∃ S : Finset ILink, IsLocalOnC S F := Iff.rfl

#print axioms mem_localObsAlg


/-- **THE LOCAL OBSERVABLES SEPARATE CONFIGURATIONS**, as soon as the gauge group's continuous
functions separate its elements. Two configurations that differ do so at some LINK, and a function
of that one link is local on the singleton `{l}` — so the separating observable is as local as an
observable can be.

DERIVED: no numeral. -/
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

/-- **AND A COMPACT HAUSDORFF GROUP DISCHARGES THAT HYPOTHESIS**, by Urysohn. Two distinct points
of a compact Hausdorff space are two disjoint closed singletons, and
`exists_continuous_zero_one_of_isClosed` produces a continuous real function vanishing on one and
equal to one on the other.

DERIVED: the `0` and `1` are the two values Urysohn's lemma produces, not a threshold; any two
distinct reals would do and Mathlib's statement fixes these. -/
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

/-- **⭐⭐ TWO STATES AGREEING ON THE LOCAL OBSERVABLES ARE EQUAL.**

Obligation II's general half, carrying NO density hypothesis and NO separation hypothesis: on a
compact Hausdorff gauge group both are discharged above. What remains of II is exactly the
Wilson-specific half — that the specification pins a DLR state on the LOCAL observables. Once that
lands, this theorem takes it to equality of states, and `tendsto_of_unique_dlr` takes uniqueness to
the infinite-volume limit.

DERIVED: no numeral. -/
theorem State.eq_of_eqOn_localObs {G : Type} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    {ν₁ ν₂ : State (IConf G)} (h : ∀ F ∈ localObsAlg G, ν₁ F = ν₂ F) :
    ∀ F : C(IConf G, ℝ), ν₁ F = ν₂ F :=
  State.eq_of_eqOn_subalgebra _
    (localObsAlg_separatesPoints (fun a b hab => continuousMap_separatesPoints_of_t2 G a b hab)) h

#print axioms State.eq_of_eqOn_localObs

end LocalObservables



/-! ## Part 2 — the limit

The ultrafilter-plus-compactness move of `InfiniteVolume.exists_filter_tendsto_all_lags`, one level
up: there the coordinates were lags and the compact set was `[−4, 4]`; here the coordinates are
observables and the compact set is `[−‖f‖, ‖f‖]`. The limit functional is then assembled coordinate
by coordinate, each of its four defining properties transported by uniqueness of limits. -/

/-- **THE EXISTENCE THEOREM.** Any family of states, along any `NeBot` filter on the index, has a
limit state along an ultrafilter refining that filter — simultaneously at EVERY observable.

No structure on the index is used: not directedness, not countability. The hypotheses are exactly
`l.NeBot` and that each `μ i` is a state. -/
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

/-! ## Part 3 — the DLR property passes to the limit

A specification is carried here by its action on OBSERVABLES: `γ k : C(X, ℝ) → C(X, ℝ)`. That the
finite-volume kernel with boundary conditions sends continuous functions to continuous functions —
the Feller property — is therefore a hypothesis on whoever supplies `γ`, recorded in its type rather
than proved here. The DLR equation is then the equality of two numbers, so it is closed and passes to
limits by uniqueness of limits. -/

/-- **The DLR (consistency) property**: the state is unmoved by every kernel of the specification. -/
def IsDLR {κ : Type*} (γ : κ → C(X, ℝ) → C(X, ℝ)) (ν : State X) : Prop :=
  ∀ (k : κ) (f : C(X, ℝ)), ν (γ k f) = ν f

#print axioms IsDLR

/-- **Consistency is a closed condition.** If the finite-volume states satisfy the DLR equation for
`k` EVENTUALLY along the filter, the limit state satisfies it outright.

`ge_of_tendsto`-style: nothing here is an inequality, but the shape is the same — an eventual
relation between two convergent quantities forces the relation between the limits. -/
theorem isDLR_of_tendsto {ι κ : Type*} {l : Filter ι} [l.NeBot] {γ : κ → C(X, ℝ) → C(X, ℝ)}
    (μ : ι → State X) (ν : State X)
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (hev : ∀ (k : κ) (f : C(X, ℝ)),
      (fun i => μ i (γ k f)) =ᶠ[l] (fun i => μ i f)) :
    IsDLR γ ν := by
  intro k f
  exact tendsto_nhds_unique ((htend (γ k f)).congr' (hev k f)) (htend f)

#print axioms isDLR_of_tendsto


/-- **⭐⭐⭐ UNIQUENESS OF THE DLR STATE UPGRADES COMPACTNESS TO CONVERGENCE.**

Compactness gives a limit along SOME ultrafilter; `ReflectionHalfSpace`'s `htend` needs one along
`atTop`. This is the step between them, and it is the classical one: if the DLR state is unique,
every ultrafilter limit is the same state, and a filter converges exactly when every refining
ultrafilter does.

**THIS IS WHAT `mixCube_ultrafilter_sees_one_parity` POINTS AT.** That theorem shows an ultrafilter
sees only one parity class of the interleaved family, and its docstring says the two parity limits
would agree if the DLR state were unique. This supplies that implication.

`hev` is the finite-volume DLR consistency, holding eventually along `l` — the same hypothesis
`isDLR_of_tendsto` takes. `huniq` is the uniqueness itself, and it is the real content. At coupling
ZERO `WilsonDLR.dlr_unique_at_zero_eq` proves it for the Wilson specification, the kernel
there not seeing the boundary at all; at general coupling it is open.

DERIVED: no numeral. -/
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


/-- **THE INFINITE-VOLUME STATE, abstractly.** A directed family of finite-volume states, each
consistent with the specification at every SMALLER index, has a limit state consistent at EVERY
index.

`hcons` is the hypothesis a Gibbs specification supplies: the finite-volume state in volume `i`
satisfies the DLR equation for every sub-volume `j ≤ i`. Directedness of the index is what turns
"for every `j ≤ i`" into "eventually in `i`", and is the only structure the index needs. -/
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

/-! ## Part 4 — the limit is not vacuous

`GibbsPositive.corrNum_plaqObs_pos` exists because a state satisfying every field of the interface
vacuously — the zero functional, or a point mass — was a live worry at finite volume. The same worry
applies to a limit.

The zero functional is excluded for free: `ν 1 = 1` is a field of `State`, so it is true of the limit
by construction and is not evidence of anything else. A POINT MASS is not excluded, and cannot be
without more input, because a limit of point masses is a point mass. What suffices is a uniform
second-moment gap — one observable whose variance is bounded below along the family, uniformly in the
volume — and everything below is CONDITIONAL on being handed one. Such a floor IS supplied:
`InfiniteVolume.exists_uniform_contact_floor` fixes one `δ₀ > 0` BEFORE the aperture with
`exp(−128β)·δ₀ ≤ wilsonCorrAt N β 0` at every aperture and every `β ≥ 0`, and
`PlaqVariance.corrClay_zero_eq` makes that contact value a plaquette VARIANCE, so it is both a
variance and uniform in the volume. `ClayNontriviality.clay_nontriviality_of_wilson_variance`
composes it with the theorem below. What remains open is the BRIDGE between the aperture indexing
that floor is stated in and the `Finset ILink` indexing used here. -/

/-- **A state is a point mass** when it is evaluation at a single configuration. -/
def IsPointMass (ν : State X) : Prop := ∃ x : X, ∀ f : C(X, ℝ), ν f = f x

#print axioms IsPointMass

/-- **A point mass has zero variance at every observable.** -/
theorem variance_eq_zero_of_isPointMass {ν : State X} (h : IsPointMass ν) (f : C(X, ℝ)) :
    ν (f * f) - (ν f) ^ 2 = 0 := by
  obtain ⟨x, hx⟩ := h
  simp only [hx, ContinuousMap.mul_apply]
  ring

#print axioms variance_eq_zero_of_isPointMass

/-- **A strictly positive variance rules the point masses out.** This is the check that the limit is
a genuinely spread-out state and not the vacuous witness. -/
theorem not_isPointMass_of_variance_pos {ν : State X} {f : C(X, ℝ)}
    (h : 0 < ν (f * f) - (ν f) ^ 2) : ¬ IsPointMass ν := by
  intro hp
  rw [variance_eq_zero_of_isPointMass hp f] at h
  exact lt_irrefl _ h

#print axioms not_isPointMass_of_variance_pos

/-- **A uniform lower bound passes to the limit.** If the finite-volume values of an observable are
eventually at least `c`, so is the limit value. `ge_of_tendsto`, nothing more. -/
theorem le_of_eventually_le {ι : Type*} {l : Filter ι} [l.NeBot] {μ : ι → State X} {ν : State X}
    (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (f : C(X, ℝ)) (c : ℝ) (h : ∀ᶠ i in l, c ≤ μ i f) : c ≤ ν f :=
  ge_of_tendsto (htend f) h

#print axioms le_of_eventually_le

/-- **A uniform VARIANCE floor passes to the limit.** The variance is a continuous function of the
two moments, so an eventual bound on the finite-volume variances bounds the limit variance. -/
theorem variance_ge_of_eventually {ι : Type*} {l : Filter ι} [l.NeBot] {μ : ι → State X}
    {ν : State X} (htend : ∀ f : C(X, ℝ), Tendsto (fun i => μ i f) l (𝓝 (ν f)))
    (f : C(X, ℝ)) (c : ℝ) (h : ∀ᶠ i in l, c ≤ μ i (f * f) - (μ i f) ^ 2) :
    c ≤ ν (f * f) - (ν f) ^ 2 :=
  ge_of_tendsto ((htend (f * f)).sub ((htend f).pow 2)) h

#print axioms variance_ge_of_eventually

/-- **The limit is a genuine, spread-out state.** A single observable carrying a variance floor that
does not depend on the volume forces the limit to be neither the zero functional (it is normalised by
construction) nor a point mass. -/
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

Riesz–Markov–Kakutani, following `MomentMeasure.stateCc` / `MomentMeasure.spectralMeasure`: on a
compact space every continuous function is compactly supported, so a state is a positive linear map
on `C_c(X, ℝ)` and `RealRMK.rieszMeasure` represents it. The measure is a PROBABILITY measure because
the state is normalised, which is the `f = 1` case of the representation. -/

section Measure

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The state as the positive linear map on compactly supported functions that Riesz–Markov–
Kakutani consumes.

DERIVED: the only numeral here is the `0` of `ℝ` in the monotonicity obligation — `0 ≤ ν (g − f)`,
which is the additive identity of the ordered field and the definition of "nonnegative". Nothing
about the state, the space or the measure is set by a number. -/
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

/-- **The infinite-volume Gibbs measure of a state**: its Riesz–Markov–Kakutani representative. -/
noncomputable def gibbsMeasure (ν : State X) : MeasureTheory.Measure X :=
  RealRMK.rieszMeasure (stateCc ν)

#print axioms gibbsMeasure

instance instIsFiniteMeasure (ν : State X) : MeasureTheory.IsFiniteMeasure (gibbsMeasure ν) :=
  inferInstanceAs (MeasureTheory.IsFiniteMeasure (RealRMK.rieszMeasure (stateCc ν)))

#print axioms instIsFiniteMeasure

/-- **The measure represents the state**: every continuous observable integrates to its value. -/
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

/-- The total mass is the value of the state at `1`, which is `1`.

`(1 : C(X, ℝ)) x` is `(1 : ℝ)` definitionally, so `h1` is the `f = 1` case of
`integral_gibbsMeasure` with no rewriting, and `Measure.real` is `ENNReal.toReal` of the measure by
the same token (`ContactFloor.measureReal_univ_one` makes the same identification). -/
theorem gibbsMeasure_univ_toReal (ν : State X) : (gibbsMeasure ν Set.univ).toReal = 1 := by
  have h := integral_gibbsMeasure ν 1
  rw [ν.map_one] at h
  have h1 : (∫ _x : X, (1 : ℝ) ∂(gibbsMeasure ν)) = 1 := h
  rw [MeasureTheory.integral_const, smul_eq_mul, mul_one] at h1
  exact h1

#print axioms gibbsMeasure_univ_toReal

/-- **The Gibbs measure is a probability measure.** Normalisation of the state, transported. -/
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

/-! ## Part 6 — the infinite lattice

The instantiation. `Finset ILink` is the index of finite volumes; it is a `SemilatticeSup` with a
bottom element, so `atTop` is `NeBot` and the directedness hypothesis of `exists_dlr_state` is
discharged by the lattice structure of finite sets. `IConf G` is compact by Part 0. -/

/-- **THE INFINITE-VOLUME GIBBS STATE.** Given a gauge group that is compact, an abstract
specification indexed by finite volumes, and finite-volume states consistent with it on every
sub-volume, there EXISTS a state on the full infinite-lattice configuration space which is the limit
of the finite-volume states and satisfies the DLR equation for EVERY finite volume.

Every hypothesis is named: `γ` is Agent 2's specification once its kernels are applied to
observables, `μ` is Agent 2's family of finite-volume states with boundary conditions, and `hcons` is
its DLR consistency. Nothing about the Wilson action enters. -/
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

/-- **The same statement with the non-degeneracy attached.** A uniform variance floor at ONE
observable, holding AT EVERY FINITE VOLUME (the eventual form is `not_isPointMass_of_uniform_variance`'s), gives an infinite-volume DLR state that is normalised and
provably not a point mass. This is the form Clay row A6 needs: an infinite-volume object that is not
the vacuous witness. -/
theorem exists_infinite_volume_gibbs_state_nondegenerate (G : Type) [TopologicalSpace G]
    [CompactSpace G]
    (γ : Finset ILink → C(IConf G, ℝ) → C(IConf G, ℝ))
    (μ : Finset ILink → State (IConf G))
    (hcons : ∀ Λ Λ' : Finset ILink, Λ' ≤ Λ → ∀ f : C(IConf G, ℝ), μ Λ (γ Λ' f) = μ Λ f)
    (f₀ : C(IConf G, ℝ)) (c : ℝ) (hc : 0 < c)
    -- CONDITIONAL: this floor is an input, not a result. See the module header.
    (hvar : ∀ Λ : Finset ILink, c ≤ μ Λ (f₀ * f₀) - (μ Λ f₀) ^ 2) :
    ∃ ν : State (IConf G), IsDLR γ ν ∧ ν 1 = 1 ∧ ¬ IsPointMass ν := by
  classical
  obtain ⟨u, ν, _hle, htend, hdlr⟩ := exists_dlr_state γ μ hcons
  haveI hub : (u : Filter (Finset ILink)).NeBot := u.neBot'
  obtain ⟨hone, hpm⟩ :=
    not_isPointMass_of_uniform_variance htend f₀ c hc (Filter.Eventually.of_forall hvar)
  exact ⟨ν, hdlr, hone, hpm⟩

#print axioms exists_infinite_volume_gibbs_state_nondegenerate

/-! ### The infinite-volume state as a measure

`gibbsMeasure` needs the Borel structure of `IConf G` to BE its product σ-algebra, and over an
infinite index those agree only when the index is countable and the factor is second countable.
`ILink = Fin 4 × (Fin 4 → ℤ)` is countable, so the hypothesis lands on the gauge group. -/

/-- **The product σ-algebra on configurations is the Borel one.** Where the countability of `ILink`
is spent; without it `gibbsMeasure` below would name a measure on a strictly smaller σ-algebra than
the topology's. -/
theorem borelSpace_iconf (G : Type) [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] : BorelSpace (IConf G) := inferInstance

#print axioms borelSpace_iconf

/-- **THE INFINITE-VOLUME GIBBS MEASURE.** The same limit, delivered as a probability measure on the
configuration space of the infinite lattice whose integral against every continuous observable is the
limit state, and whose state satisfies the DLR equation at every finite volume.

This is the object Clay row A6 asks for: not a sequence of finite-volume numbers with a limit, but a
single measure on the FULL lattice. What it does not yet carry is any tie to the Wilson action —
`γ` and `μ` are hypotheses. -/
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
