import Mathlib
import MassGap.InfiniteLattice

/-!
# MassGap.InfiniteShift — the lattice translation acting on the quasi-local algebra

The unit translation in a direction `μ : Fin 4`, built up from links to observables on the infinite
lattice `ISite = Fin 4 → ℤ` of `MassGap.InfiniteLattice`, and three properties of it.

## The maps

`ishiftLink` moves a link's base site by one step in direction `μ`, keeping its direction.
`ishiftPlaq` does the same for a plaquette, keeping the plane — a translation does not transpose it,
so the loop is not reversed. `ishiftConf` pulls a configuration back along `ishiftLink`, and
`ishiftObs` precomposes an observable with `ishiftConf`.

`wilsonHol_ishiftPlaq` records the consequence for the Wilson holonomy: it is equal on the two
sides, not merely conjugate. The plaquette's boundary word is the same word at a moved base, so no
hypothesis on the plaquette density is needed — unlike a reflection, where the word is rotated and
the ordered product is conjugated (`LatticeReflection.ihol_ireflConf`).

## The three properties

* `ishiftObs_mem_quasiLocalAlg` — `ishiftObs μ` maps `InfiniteLattice.quasiLocalAlg` into itself. The
  support of an observable local on `S` moves to `S.image (ishiftLink μ)`, which is again finite;
  `isLocalOn_ishiftObs` is that step, and `continuous_ishiftConf` supplies continuity.
* `ishiftObs_infinite_order` — for every `k > 0`, `(ishiftObs μ)^[k]` is not the identity on the
  witness observable `linkObs l f`. `ishift_iterate` is where `ℤ` enters: `k` steps add `k` to a
  coordinate, and on `ℤ` that is never zero for `k > 0`, whereas on `Fin n` it wraps.
* `ishiftObs_ne_id_of_separating` — the case `k = 1` of the previous statement.

## Scope

The two non-triviality statements take a separating pair: `f g₀ ≠ f g₁` for a real-valued `f` on the
gauge group. Without it the conclusion is false — on a group whose continuous real functions are all
constant, every observable is fixed by every translation, which is a property of the group rather
than of the translation.

Nothing here constructs a reflection form, a positivity statement, or a `Transfer.TransferData`. The
declarations below concern the translation map alone; `IConf` carries no measure or state in this
file, and `G` is only a topological space (a group structure is assumed for
`wilsonHol_ishiftPlaq` alone).
-/

namespace MassGap.InfiniteShift

open MassGap.InfiniteLattice

section Shift

variable {G : Type} [TopologicalSpace G]

/-! ## 1. The shift, on links, configurations and observables -/

/-- A link translated one step in direction `μ`: the direction component is unchanged, the base site
is moved by `InfiniteLattice.ishift`.

DERIVED: `4` is the spacetime dimension, the range of the direction index `μ : Fin 4`. It is the only
numeral in the statement; the unit step lives inside `ishift`. -/
def ishiftLink (μ : Fin 4) (l : ILink) : ILink := (l.1, ishift μ l.2)

/-- Translations in any two directions commute: `ishift μ (ishift ν x) = ishift ν (ishift μ x)`.

Each touches one coordinate, and when `μ = ν` both add the same step to the same coordinate. No
hypothesis relates `μ` and `ν`.

DERIVED: `4` is the spacetime dimension, the range of both direction indices. It is the only numeral
in the statement; the unit step lives inside `ishift`. -/
theorem ishift_comm (μ ν : Fin 4) (x : ISite) :
    ishift μ (ishift ν x) = ishift ν (ishift μ x) := by
  by_cases h : μ = ν
  · subst h; rfl
  · funext j
    by_cases hμ : j = μ
    · subst hμ
      simp [ishift, Function.update_apply, h, Ne.symm h]
    · by_cases hν : j = ν
      · subst hν
        simp [ishift, Function.update_apply, h, Ne.symm h, hμ]
      · simp [ishift, Function.update_apply, hμ, hν]

#print axioms ishift_comm

/-- A plaquette translated one step in direction `μ`: the plane is unchanged, the base site is moved
by `ishift`.

The plane is not transposed, so the boundary loop keeps its orientation — which is what separates a
translation from the reflection of `LatticeReflection`.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement. -/
def ishiftPlaq (μ : Fin 4) (q : IPlaq) : IPlaq := (q.1, ishift μ q.2)

/-- A configuration translated by pullback along `ishiftLink μ`: the value at `l` becomes the old
value at `ishiftLink μ l`.

DERIVED: `4` is the spacetime dimension, the constant `InfiniteLattice.ISite` and `ILink` are built
on and the range of the direction index. It is the only numeral in the statement, and it is an index
range, not a size. -/
def ishiftConf (μ : Fin 4) (U : IConf G) : IConf G := fun l => U (ishiftLink μ l)

/-- An observable translated by precomposition with `ishiftConf μ`. This is the map the endomorphism
statement below is about.

DERIVED: `4` is the spacetime dimension, as in `ishiftConf`. It is the only numeral in the
statement. -/
def ishiftObs (μ : Fin 4) (F : IConf G → ℝ) : IConf G → ℝ := fun U => F (ishiftConf μ U)

/-! ## 2. The shift moves every site, and keeps moving -/

/-- The Wilson holonomy of a translated plaquette equals the holonomy of the original plaquette on
the translated configuration: `wilsonHol ibd (ishiftPlaq μ q) U = wilsonHol ibd q (ishiftConf μ U)`.

Equality, not conjugacy. The boundary word is the same word at a moved base, since `ishift_comm`
lets the translation pass through each of the four link lookups. A reflection instead rotates the
word and conjugates the ordered product (`LatticeReflection.ihol_ireflConf`), which is why that case
needs the plaquette density to be a class function and this one needs no hypothesis on it.

Scope: `G` is required to be a `Group` here, unlike the rest of the section.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement. -/
theorem wilsonHol_ishiftPlaq {G : Type} [Group G] (μ : Fin 4) (q : IPlaq) (U : IConf G) :
    MassGap.WilsonLattice.wilsonHol ibd (ishiftPlaq μ q) U
      = MassGap.WilsonLattice.wilsonHol ibd q (ishiftConf μ U) := by
  rw [wilsonHol_ibd, wilsonHol_ibd]
  simp only [ishiftPlaq, ishiftConf, ishiftLink]
  rw [ishift_comm μ q.1.1 q.2, ishift_comm μ q.1.2 q.2]

#print axioms wilsonHol_ishiftPlaq

/-- Iterating the translation `k` times adds `k` to the `μ` coordinate:
`((ishift μ)^[k] x) μ = x μ + k`.

The coordinate lives in `ℤ`, so the sum is taken there and does not wrap; on `Fin n` the
corresponding statement would reduce mod `n`. Stated for every `k : ℕ`, including `0`.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement; the unit step lives inside `ishift`. -/

theorem ishift_iterate (μ : Fin 4) (k : ℕ) (x : ISite) :
    ((ishift μ)^[k] x) μ = x μ + k := by
  induction k with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ishift, Function.update_self, ih]
      push_cast
      ring

#print axioms MassGap.InfiniteShift.ishift_iterate

/-- No positive number of translations fixes a site: `(ishift μ)^[k] x ≠ x` whenever `k > 0`.

From `ishift_iterate`, since `x μ + k = x μ` fails in `ℤ` for positive `k`. The hypothesis `0 < k` is
required — at `k = 0` the iterate is the identity.

DERIVED: `4` is the spacetime dimension, the range of the direction index. `0` is the excluded step
count in `hk : 0 < k`. -/
theorem ishift_iterate_ne (μ : Fin 4) {k : ℕ} (hk : 0 < k) (x : ISite) :
    (ishift μ)^[k] x ≠ x := by
  intro h
  have hcoord : ((ishift μ)^[k] x) μ = x μ := congrFun h μ
  rw [ishift_iterate] at hcoord
  omega

#print axioms MassGap.InfiniteShift.ishift_iterate_ne

/-- Iterating the link translation moves the base site and leaves the direction alone:
`(ishiftLink μ)^[k] l = (l.1, (ishift μ)^[k] l.2)`, for every `k : ℕ`.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement — `l.1` and `l.2` are projections. -/
theorem ishiftLink_iterate (μ : Fin 4) (k : ℕ) (l : ILink) :
    (ishiftLink μ)^[k] l = (l.1, (ishift μ)^[k] l.2) := by
  induction k with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, ishiftLink, Function.iterate_succ_apply']

#print axioms MassGap.InfiniteShift.ishiftLink_iterate

/-- No positive number of translations fixes a link: `(ishiftLink μ)^[k] l ≠ l` whenever `k > 0`.

The direction component is fixed by the translation, so the difference is in the base site, where
`ishift_iterate_ne` applies.

DERIVED: `4` is the spacetime dimension, the range of the direction index. `0` is the excluded step
count in `hk : 0 < k`. -/
theorem ishiftLink_iterate_ne (μ : Fin 4) {k : ℕ} (hk : 0 < k) (l : ILink) :
    (ishiftLink μ)^[k] l ≠ l := by
  have hfst : ∀ j : ℕ, ((ishiftLink μ)^[j] l) = (l.1, (ishift μ)^[j] l.2) := by
    intro j
    induction j with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, ishiftLink, Function.iterate_succ_apply']
  intro h
  rw [hfst k] at h
  exact ishift_iterate_ne μ hk l.2 (congrArg Prod.snd h)

#print axioms MassGap.InfiniteShift.ishiftLink_iterate_ne

/-! ## 3. Iterating the shift on configurations and observables -/

omit [TopologicalSpace G] in
theorem ishiftConf_iterate (μ : Fin 4) (k : ℕ) (U : IConf G) :
    (ishiftConf μ)^[k] U = fun l => U ((ishiftLink μ)^[k] l) := by
  induction k with
  | zero => simp
  | succ j ih =>
      funext l
      rw [Function.iterate_succ_apply']
      show ((ishiftConf μ)^[j] U) (ishiftLink μ l) = _
      rw [ih]
      show U ((ishiftLink μ)^[j] (ishiftLink μ l)) = _
      rw [Function.iterate_succ_apply]

omit [TopologicalSpace G] in
theorem ishiftObs_iterate (μ : Fin 4) (k : ℕ) (F : IConf G → ℝ) :
    (ishiftObs μ)^[k] F = fun U => F ((ishiftConf μ)^[k] U) := by
  induction k with
  | zero => simp
  | succ j ih =>
      funext U
      rw [Function.iterate_succ_apply']
      show ((ishiftObs μ)^[j] F) (ishiftConf μ U) = _
      rw [ih]
      show F ((ishiftConf μ)^[j] (ishiftConf μ U)) = _
      rw [Function.iterate_succ_apply]

/-! ## 4. It is an endomorphism of the quasi-local algebra -/

/-- `ishiftConf μ` is continuous on `IConf G` with the product topology: each output coordinate is
one of the input coordinates, so the map is a projection composed with a relabelling.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement. -/
theorem continuous_ishiftConf (μ : Fin 4) :
    Continuous (ishiftConf (G := G) μ) :=
  continuous_pi fun l => continuous_apply (ishiftLink μ l)

#print axioms MassGap.InfiniteShift.continuous_ishiftConf

omit [TopologicalSpace G] in
/-- An observable local on a finite link set `S` becomes local on `S.image (ishiftLink μ)` after
translation.

The support is not preserved; it is carried to its image, which is again finite. `S` is an arbitrary
`Finset ILink` and no relation between `S` and its image is required.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement. -/
theorem isLocalOn_ishiftObs (μ : Fin 4) {S : Finset ILink} {F : IConf G → ℝ}
    (hF : IsLocalOn S F) :
    IsLocalOn (S.image (ishiftLink μ)) (ishiftObs μ F) := by
  classical
  intro U V h
  refine hF _ _ (fun l hl => ?_)
  exact h (ishiftLink μ l) (Finset.mem_image_of_mem _ hl)

#print axioms MassGap.InfiniteShift.isLocalOn_ishiftObs

/-- `ishiftObs μ` maps `InfiniteLattice.quasiLocalAlg` into itself.

Membership of that algebra asks for continuity and locality on some finite link set. Continuity
composes (`continuous_ishiftConf`), and the witnessing set moves to its image under `ishiftLink μ`
(`isLocalOn_ishiftObs`), which is again finite. No fixed block is required to contain the support.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement. -/
theorem ishiftObs_mem_quasiLocalAlg (μ : Fin 4) {F : IConf G → ℝ}
    (hF : F ∈ quasiLocalAlg (G := G)) :
    ishiftObs μ F ∈ quasiLocalAlg (G := G) := by
  classical
  obtain ⟨hFc, S, hFl⟩ := hF
  exact ⟨hFc.comp (continuous_ishiftConf μ), S.image (ishiftLink μ), isLocalOn_ishiftObs μ hFl⟩

#print axioms MassGap.InfiniteShift.ishiftObs_mem_quasiLocalAlg

/-! ## 5. And it is non-trivial, at every power -/

/-- The observable reading one link through a real-valued function: `linkObs l f U = f (U l)`.

DERIVED: the statement carries no numeral — the link, the function and the configuration are all
parameters. -/
def linkObs (l : ILink) (f : G → ℝ) : IConf G → ℝ := fun U => f (U l)

theorem linkObs_mem_quasiLocalAlg {l : ILink} {f : G → ℝ} (hf : Continuous f) :
    linkObs (G := G) l f ∈ quasiLocalAlg (G := G) := by
  classical
  refine ⟨hf.comp (continuous_coord l), {l}, fun U V h => ?_⟩
  show f (U l) = f (V l)
  rw [h l (Finset.mem_singleton_self l)]

#print axioms MassGap.InfiniteShift.linkObs_mem_quasiLocalAlg

omit [TopologicalSpace G] in
/-- For every `k > 0`, `(ishiftObs μ)^[k] (linkObs l f) ≠ linkObs l f`, given a separating pair
`hf : f g₀ ≠ f g₁`.

The witness configuration is `g₁` at `l` and `g₀` elsewhere. `ishiftLink_iterate_ne` puts
`(ishiftLink μ)^[k] l` away from `l`, so the translated observable reads `g₀` where the original
reads `g₁`.

Scope. The separating pair is a hypothesis and the conclusion fails without it: on a gauge group
whose real-valued functions are all constant, every observable is fixed by every translation, which
is a fact about the group rather than about the map. The statement is about this one observable
family, not about every element of the algebra, and it says nothing about a spectrum or a gap.

DERIVED: `4` is the spacetime dimension, the range of the direction index. `0` is the excluded step
count in `hk : 0 < k`. The subscripts on `g₀` and `g₁` are part of their names, not numerals. -/
theorem ishiftObs_infinite_order (μ : Fin 4) {k : ℕ} (hk : 0 < k) (l : ILink)
    {f : G → ℝ} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) :
    (ishiftObs (G := G) μ)^[k] (linkObs l f) ≠ linkObs l f := by
  classical
  intro h
  have hmoved : (ishiftLink μ)^[k] l ≠ l := ishiftLink_iterate_ne μ hk l
  have hval := congrFun h (fun j : ILink => if j = l then g₁ else g₀)
  rw [ishiftObs_iterate] at hval
  simp only [linkObs, ishiftConf_iterate, if_neg hmoved] at hval
  exact hf hval

#print axioms MassGap.InfiniteShift.ishiftObs_infinite_order

/-- `ishiftObs μ (linkObs l f) ≠ linkObs l f`, given a separating pair `hf : f g₀ ≠ f g₁`.

`ishiftObs_infinite_order` at a single step, with `Function.iterate_one` removing the iterate. The
separating pair is required for the same reason as there.

DERIVED: `4` is the spacetime dimension, the range of the direction index. It is the only numeral in
the statement; the single step appears in the proof, not in the type. -/
theorem ishiftObs_ne_id_of_separating (μ : Fin 4) (l : ILink)
    {f : G → ℝ} {g₀ g₁ : G} (hf : f g₀ ≠ f g₁) :
    ishiftObs (G := G) μ (linkObs l f) ≠ linkObs l f := by
  have h := ishiftObs_infinite_order μ Nat.one_pos l hf
  rwa [Function.iterate_one] at h

#print axioms MassGap.InfiniteShift.ishiftObs_ne_id_of_separating

end Shift

end MassGap.InfiniteShift
