import Mathlib
import MassGap.HalfSpaceAlgebra
import MassGap.ReflectionShift
import MassGap.WilsonTransferReduction
import MassGap.CrossingIntegration
import MassGap.ActionSplit
import MassGap.GibbsSpec
import MassGap.HaarVariance

/-!
# MassGap.ReflectionHalfSpace — pairing a reflection with a half-space

`HalfSpaceAlgebra.posHalf τ p = {l | p ≤ l.2 τ}` indexes the half-space by the plane `p`.
`LatticeReflection.ireflSite τ c x` sends `x_τ` to `c − x_τ`, so `c` is the reflection constant and
the plane it fixes sits at `c/2`. The reflection about `c` carries `{x_τ ≥ p}` into `{x_τ ≤ c − p}`,
which is the complementary half at

    c = 2p.

`reflection_exchanges_halves` states that case: at `c = 2p` the image of `posHalf τ p` lies in
`negHalf τ p`. `image_half_is_c_sub_p` gives the image coordinate exactly, for a link whose
direction
is not `τ`.

Both are containments, not equalities. At `c = 2p` a `τ`-link reflects about `c − 1` and lands at
`≤ p − 1`, so the `τ`-link based at `p` is outside the image, and the image meets `posHalf τ p` at
`x_τ = p`. At `c = 2p − 1` the image lies in `{x_τ ≤ p − 1}`, its `τ` part reaching only `≤ p − 2`,
and is disjoint from `posHalf τ p`.

The algebra is indexed by the integer `p` and the reflection by the constant, and the two indices
need not agree: `reflPositive_of_tendsto_halfSpaceAlg_odd` states reflection positivity on
`halfSpaceAlg τ p` at the odd constant `2p − 1`.
-/

namespace MassGap.ReflectionHalfSpace

open MassGap.InfiniteLattice MassGap.LatticeReflection MassGap.HalfSpaceAlgebra

/-! ## 1. The negative half -/

/-- The half-space of links at or below the plane `p` in the `τ` coordinate, `{l | l.2 τ ≤ p}`. A
link is
placed by its base site, so a `τ`-link spanning `[x_τ, x_τ+1]` is placed by the end nearer the
plane.
Complementary to `HalfSpaceAlgebra.posHalf τ p`.

DERIVED: `4` is the spacetime dimension carried by `Fin 4`; `p` is the caller's plane. -/
def negHalf (τ : Fin 4) (p : ℤ) : Set ILink := {l | l.2 τ ≤ p}

/-! ## 2. The pairing -/

/-- At reflection constant `c = 2 * p`, every link of `posHalf τ p` lands in `negHalf τ p`. A
`τ`-link
reflects about `2p - 1` and lands at `2p - 1 - x_τ ≤ p - 1`; a link in any other direction reflects
about `2p` and lands at `2p - x_τ ≤ p`. This is the containment Osterwalder–Schrader positivity is
stated against: `θ` carries the positive half-space algebra into the negative one.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`, forced by `ireflSite`'s own
parametrisation; the `1` is `ireflLink`'s link length; `4` is the dimension. -/
theorem reflection_exchanges_halves (τ : Fin 4) (p : ℤ) {l : ILink} (hl : l ∈ posHalf τ p) :
    ireflLink τ (2 * p) l ∈ negHalf τ p := by
  have hp : p ≤ l.2 τ := hl
  show (ireflLink τ (2 * p) l).2 τ ≤ p
  by_cases h : l.1 = τ
  · simp only [ireflLink, if_pos h, ireflSite_axis]
    omega
  · simp only [ireflLink, if_neg h, ireflSite_axis]
    omega

#print axioms reflection_exchanges_halves

/-- The image coordinate at an arbitrary reflection constant: for a link whose direction is not `τ`,
`(ireflLink τ c l).2 τ = c - l.2 τ`, an equality rather than a bound, because `ireflLink`'s base
shift applies to `τ`-links only. It places the image of the plane-`p` half-space in `{x_τ ≤ c - p}`,
which is the complementary half exactly when `c - p = p`.

DERIVED: `4` is the dimension; `c` is the caller's reflection constant. -/
theorem image_half_is_c_sub_p (τ : Fin 4) (c : ℤ) {l : ILink} (h : l.1 ≠ τ) :
    (ireflLink τ c l).2 τ = c - l.2 τ := by
  simp only [ireflLink, if_neg h, ireflSite_axis]

#print axioms image_half_is_c_sub_p

/-- A witness that pairing the reflection at `c` with the half-space indexed by the same `c` does
not
exchange the halves. At `c = -1` the link `(μ, fun _ => -1)` with `μ ≠ τ` reflects to `τ`-coordinate
`0`, which still satisfies `-1 ≤ x`, so the image has not left the positive half. Negative control
for `reflection_exchanges_halves`.

CHOSEN: `-1` for both the reflection constant and the base coordinate is the smallest witness with a
negative plane, and the hypothesis `μ ≠ τ` avoids `ireflLink`'s base shift; neither carries another
role. DERIVED: `4` is the dimension. -/
theorem mismatched_pairing_stays_positive {τ μ : Fin 4} (hμ : μ ≠ τ) :
    (ireflLink τ (-1) (μ, fun _ => (-1 : ℤ))).2 τ ∈ {x : ℤ | (-1 : ℤ) ≤ x} := by
  have h := image_half_is_c_sub_p τ (-1) (l := (μ, fun _ => (-1 : ℤ))) hμ
  show (-1 : ℤ) ≤ (ireflLink τ (-1) (μ, fun _ => (-1 : ℤ))).2 τ
  rw [h]
  norm_num

#print axioms mismatched_pairing_stays_positive

/-! ## 3. The reflection as a permutation, and its fixed set -/

/-- The reflection packaged as `Equiv.Perm ILink`, built from
`LatticeReflection.ireflLink_involutive`. `ActionSplit.pairing_nonneg_of_shared_block` takes its `θ`
as a permutation, so the involution has to be presented in that form.

DERIVED: `4` is the dimension carried by `Fin 4`; `c` is the caller's reflection constant. -/
def ireflPerm (τ : Fin 4) (c : ℤ) : Equiv.Perm ILink :=
  (MassGap.LatticeReflection.ireflLink_involutive τ c).toPerm _

@[simp] theorem ireflPerm_apply (τ : Fin 4) (c : ℤ) (l : ILink) :
    ireflPerm τ c l = MassGap.LatticeReflection.ireflLink τ c l := rfl

#print axioms ireflPerm

/-- At the even constant `2 * p` no `τ`-link is fixed: a `τ`-link reflects about `2p - 1`, so being
fixed
would need `2 * x_τ = 2p - 1`, which has no solution over `ℤ`. The plane therefore carries no
`τ`-link, and the `τ`-direction links split between the two halves without remainder.

DERIVED: the `2` is the plane-to-constant conversion, the `1` is `ireflLink`'s link length, and `4`
is the dimension. -/
theorem no_tau_link_fixed (τ : Fin 4) (p : ℤ) {l : ILink} (hτ : l.1 = τ) :
    MassGap.LatticeReflection.ireflLink τ (2 * p) l ≠ l := by
  intro h
  have hax : (MassGap.LatticeReflection.ireflLink τ (2 * p) l).2 τ = l.2 τ := by rw [h]
  simp only [MassGap.LatticeReflection.ireflLink, if_pos hτ,
    MassGap.LatticeReflection.ireflSite_axis] at hax
  omega

#print axioms no_tau_link_fixed

/-- At `2 * p`, a link whose direction is not `τ` is fixed exactly when its base sits on the plane:
`2p - x_τ = x_τ` iff `x_τ = p`. With `no_tau_link_fixed` this identifies the shared block `R` of the
Osterwalder–Seiler split as the transverse links based on the plane, and nothing else.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem nonTau_fixed_iff (τ : Fin 4) (p : ℤ) {l : ILink} (hτ : l.1 ≠ τ) :
    MassGap.LatticeReflection.ireflLink τ (2 * p) l = l ↔ l.2 τ = p := by
  constructor
  · intro h
    have hax : (MassGap.LatticeReflection.ireflLink τ (2 * p) l).2 τ = l.2 τ := by rw [h]
    simp only [MassGap.LatticeReflection.ireflLink, if_neg hτ,
      MassGap.LatticeReflection.ireflSite_axis] at hax
    omega
  · intro h
    have : MassGap.LatticeReflection.ireflSite τ (2 * p) l.2 = l.2 := by
      funext j
      by_cases hj : j = τ
      · subst hj
        rw [MassGap.LatticeReflection.ireflSite_axis, h]
        omega
      · simp [MassGap.LatticeReflection.ireflSite, hj]
    simp only [MassGap.LatticeReflection.ireflLink, if_neg hτ, this]

#print axioms nonTau_fixed_iff

/-! ## 3b. The dagger, and the reflection as a twist -/

section Twist

variable {G : Type} [Group G]

/-- The coordinate twist attached to the reflection on `ℤ⁴`: invert the group element on a `τ`-link,
leave it alone in every other direction. The infinite-lattice counterpart of
`ActionSplit.axisDagger`.

DERIVED: `4` is the dimension carried by `Fin 4`; `τ` is the caller's reflected direction. -/
def ilinkDagger (τ : Fin 4) : ILink → G → G :=
  fun l u => if l.1 = τ then u⁻¹ else u

/-- `LatticeReflection.ireflConf τ c` is `ActionSplit.twist (ireflPerm τ c) (ilinkDagger τ)`, by
`rfl`.
`ActionSplit.twist e σ U i = σ i (U (e i))`, and `ireflConf` moves the base by `ireflLink` and
inverts precisely on `τ`-links, so the two sides are the same function. Stated for a compact
topological group with continuous inversion.

DERIVED: `4` is the dimension carried by `Fin 4`; `c` is the caller's reflection constant. -/
theorem ireflConf_eq_twist [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
    (τ : Fin 4) (c : ℤ) (U : MassGap.InfiniteLattice.IConf G) :
    MassGap.LatticeReflection.ireflConf τ c U
      = MassGap.ActionSplit.twist (ireflPerm τ c) (ilinkDagger (G := G) τ) U := rfl

#print axioms ireflConf_eq_twist

/-- `ilinkDagger τ l u = u` whenever `l.1 ≠ τ` — `ActionSplit`'s `hσR`. By `no_tau_link_fixed` the
shared
block carries no `τ`-link, so the twist acts as the identity there.

DERIVED: `4` is the dimension carried by `Fin 4`. -/
theorem ilinkDagger_eq_self_of_ne (τ : Fin 4) {l : ILink} (h : l.1 ≠ τ) (u : G) :
    ilinkDagger τ l u = u := by
  simp [ilinkDagger, h]

#print axioms ilinkDagger
#print axioms ilinkDagger_eq_self_of_ne

end Twist

section DaggerMeasure

open MeasureTheory MassGap.CompactGauge

/-- The twist preserves `probHaar (SU N)` on every link — `ActionSplit`'s `hσ`. On a `τ`-link it is
group
inversion and Haar on a compact group is inversion-invariant (`Measure.measurePreserving_inv`);
elsewhere it is the identity. Holds for every `N : ℕ`, with no hypothesis on `N`. The argument is
`ActionSplit.axisDagger_measurePreserving`'s and does not read which lattice the link came from.

DERIVED: `4` is the dimension carried by `Fin 4`. -/
theorem ilinkDagger_measurePreserving {N : ℕ} (τ : Fin 4) (l : ILink) :
    MeasurePreserving (ilinkDagger (G := MassGap.SUN.SU N) τ l)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
  by_cases h : l.1 = τ
  · have hf : ilinkDagger (G := MassGap.SUN.SU N) τ l = fun u => u⁻¹ := by
      funext u; simp [ilinkDagger, h]
    rw [hf]
    exact Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
  · have hf : ilinkDagger (G := MassGap.SUN.SU N) τ l = id := by
      funext u; simp [ilinkDagger, h]
    rw [hf]
    exact MeasurePreserving.id (probHaar (MassGap.SUN.SU N))

#print axioms ilinkDagger_measurePreserving

end DaggerMeasure

/-! ## 3c. The blocks `ActionSplit.pairing_nonneg_of_local` consumes -/

section Blocks

open MassGap.LatticeReflection

variable (τ : Fin 4) (p : ℤ) (Λ : Finset ILink)

/-- The positive half of a finite link set `Λ`: the links whose `τ` coordinate the reflection at `2
* p`
moves down. Classifying by the reflection's own action rather than by an inequality on the base is
what makes the three blocks disjoint by trichotomy, with no case split on the link's direction.

DERIVED: `τ`, `p` and `Λ` come from the `variable` line above, so the signature writes no numeral of
its own; in the body the `2` is the plane-to-constant conversion `c = 2 * p` and `4` is the
dimension carried by `ILink`. -/
def iblkS : Finset ILink :=
  Λ.filter (fun l => (ireflLink τ (2 * p) l).2 τ < l.2 τ)

/-- The negative half: the links whose `τ` coordinate the reflection at `2 * p` moves up.

DERIVED: as `iblkS` — the `2` is the plane-to-constant conversion and `4` the dimension, both in the
body rather than in the signature. -/
def iblkT : Finset ILink :=
  Λ.filter (fun l => l.2 τ < (ireflLink τ (2 * p) l).2 τ)

/-- The shared block: the links whose `τ` coordinate the reflection at `2 * p` leaves fixed.

DERIVED: as `iblkS` — the `2` is the plane-to-constant conversion and `4` the dimension, both in the
body rather than in the signature. -/
def iblkR : Finset ILink :=
  Λ.filter (fun l => (ireflLink τ (2 * p) l).2 τ = l.2 τ)

#print axioms iblkS

/-- The three blocks are pairwise disjoint, by trichotomy on `ℤ`. `iblkS_disjoint_iblkR` and
`iblkT_disjoint_iblkR` are the other two pairs.

DERIVED: `τ`, `p` and `Λ` come from the `variable` line above, so the signature writes no numeral.
-/
theorem iblkS_disjoint_iblkT : Disjoint (iblkS τ p Λ) (iblkT τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hT => ?_
  simp only [iblkS, iblkT, Finset.mem_filter] at hS hT
  omega

theorem iblkS_disjoint_iblkR : Disjoint (iblkS τ p Λ) (iblkR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hR => ?_
  simp only [iblkS, iblkR, Finset.mem_filter] at hS hR
  omega

theorem iblkT_disjoint_iblkR : Disjoint (iblkT τ p Λ) (iblkR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hT hR => ?_
  simp only [iblkT, iblkR, Finset.mem_filter] at hT hR
  omega

#print axioms iblkS_disjoint_iblkT

/-- The reflection at `2 * p` fixes each link of `iblkR` as a link, not only in its `τ` coordinate —
`ActionSplit`'s `hθR`. The `τ`-link case is vacuous, since a fixed `τ` coordinate would need
`2 * x_τ = 2p - 1`; the transverse case is `nonTau_fixed_iff`. Classifying by the `τ` coordinate
alone therefore already forces the whole link fixed.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; `τ`, `p` and `Λ` come from the
`variable` line above. -/
theorem irefl_eq_self_of_mem_iblkR {l : ILink} (hl : l ∈ iblkR τ p Λ) :
    ireflLink τ (2 * p) l = l := by
  simp only [iblkR, Finset.mem_filter] at hl
  by_cases hτ : l.1 = τ
  · exfalso
    have := hl.2
    simp only [ireflLink, if_pos hτ, ireflSite_axis] at this
    omega
  · refine (nonTau_fixed_iff τ p hτ).2 ?_
    have := hl.2
    simp only [ireflLink, if_neg hτ, ireflSite_axis] at this
    omega

#print axioms irefl_eq_self_of_mem_iblkR

/-- Given a link set stable under the reflection, the reflection at `2 * p` carries `iblkS` into
`iblkT`
— `ActionSplit`'s `hθST`. The inequality flips because `ireflLink` is an involution, so the image of
the image is the original link.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`. -/
theorem irefl_mem_iblkT_of_mem_iblkS
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) {l : ILink} (hl : l ∈ iblkS τ p Λ) :
    ireflLink τ (2 * p) l ∈ iblkT τ p Λ := by
  simp only [iblkS, Finset.mem_filter] at hl
  simp only [iblkT, Finset.mem_filter]
  refine ⟨hΛ l hl.1, ?_⟩
  rw [ireflLink_involutive τ (2 * p) l]
  exact hl.2

#print axioms irefl_mem_iblkT_of_mem_iblkS

end Blocks

/-! ## 3d. Transport to the box — the index `ActionSplit` takes -/

section Box

open MassGap.LatticeReflection

variable {τ : Fin 4} {p : ℤ} {Λ : Finset ILink}

/-- The reflection as a map of a reflection-stable box `↥Λ`. `ActionSplit.cvol` carries `[Fintype
ι]`, so
the index has to be the box as a subtype rather than the infinite `ILink`. The hypothesis
`hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ` is what makes the map well defined.

DERIVED: the signature writes no numeral of its own; `c` is the caller's reflection constant and is
not pinned to an even `2 * p` here, and `4` is the dimension carried by `ILink`. -/
def ireflBox {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) : ↥Λ → ↥Λ :=
  fun l => ⟨ireflLink τ c l.1, hΛ l.1 l.2⟩

theorem ireflBox_involutive {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) :
    Function.Involutive (ireflBox (τ := τ) (c := c) hΛ) := by
  intro l
  refine Subtype.ext ?_
  simpa [ireflBox] using ireflLink_involutive τ c l.1

/-- The box reflection as `Equiv.Perm ↥Λ`, from `ireflBox_involutive` — the `θ` at the index
`ActionSplit` takes.

DERIVED: the signature writes no numeral. -/
def ireflBoxPerm {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) : Equiv.Perm ↥Λ :=
  (ireflBox_involutive hΛ).toPerm _

@[simp] theorem ireflBoxPerm_coe {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (l : ↥Λ) :
    ((ireflBoxPerm hΛ l : ↥Λ) : ILink) = ireflLink τ c l.1 := rfl

#print axioms ireflBoxPerm

/-- `Λ ∪ Λ.image (ireflLink τ c)`: a finite link set closed under the reflection at `c`, built from
any
starting set. The lemmas of this file carry `hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ`, and
`reflClosure_closed` discharges that hypothesis for this set, so a witness box can be specified by
the plaquettes it must contain rather than link by link.

DERIVED: `4` is the dimension carried by `ILink`; `c` is the caller's reflection constant. -/
def reflClosure (τ : Fin 4) (c : ℤ) (Λ : Finset ILink) : Finset ILink :=
  Λ ∪ Λ.image (ireflLink τ c)

#print axioms reflClosure

theorem subset_reflClosure (τ : Fin 4) (c : ℤ) (Λ : Finset ILink) : Λ ⊆ reflClosure τ c Λ :=
  Finset.subset_union_left

#print axioms subset_reflClosure

/-- `reflClosure τ c Λ` is closed under `ireflLink τ c`. A link of `Λ` reflects into the image part;
a
link of the image reflects back into `Λ`, because `ireflLink` is an involution. No case split on the
link's direction and no arithmetic.

DERIVED: `4` is the dimension carried by `ILink`; `c` is the caller's reflection constant. -/
theorem reflClosure_closed (τ : Fin 4) (c : ℤ) (Λ : Finset ILink) :
    ∀ l ∈ reflClosure τ c Λ, ireflLink τ c l ∈ reflClosure τ c Λ := by
  intro l hl
  rcases Finset.mem_union.mp hl with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    refine Finset.mem_union_left _ ?_
    rw [ireflLink_involutive τ c m]
    exact hm

#print axioms reflClosure_closed

/-- The positive half at the box index: the elements of `↥Λ` whose `τ` coordinate the reflection at
`2 * p` moves down. The same classification as `iblkS`, over the subtype.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
def boxS (τ : Fin 4) (p : ℤ) (Λ : Finset ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ (2 * p) l.1).2 τ < l.1.2 τ)

/-- The negative half at the box index: moved up in the `τ` coordinate.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
def boxT (τ : Fin 4) (p : ℤ) (Λ : Finset ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => l.1.2 τ < (ireflLink τ (2 * p) l.1).2 τ)

/-- The shared block at the box index: not moved in the `τ` coordinate.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
def boxR (τ : Fin 4) (p : ℤ) (Λ : Finset ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ (2 * p) l.1).2 τ = l.1.2 τ)

theorem boxS_disjoint_boxT : Disjoint (boxS τ p Λ) (boxT τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hT => ?_
  simp only [boxS, boxT, Finset.mem_filter] at hS hT
  omega

theorem boxS_disjoint_boxR : Disjoint (boxS τ p Λ) (boxR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hS hR => ?_
  simp only [boxS, boxR, Finset.mem_filter] at hS hR
  omega

theorem boxT_disjoint_boxR : Disjoint (boxT τ p Λ) (boxR τ p Λ) := by
  refine Finset.disjoint_left.2 fun l hT hR => ?_
  simp only [boxT, boxR, Finset.mem_filter] at hT hR
  omega

/-- `hθR` at the box index: `ireflBoxPerm hΛ l = l` for `l ∈ boxR τ p Λ`. The same argument as
`irefl_eq_self_of_mem_iblkR`, transported by `Subtype.ext`. The stability hypothesis is taken at the
even constant `2 * p`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`. -/
theorem ireflBoxPerm_eq_self_of_mem_boxR (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {l : ↥Λ} (hl : l ∈ boxR τ p Λ) : ireflBoxPerm hΛ l = l := by
  simp only [boxR, Finset.mem_filter] at hl
  refine Subtype.ext ?_
  rw [ireflBoxPerm_coe]
  by_cases hτ : l.1.1 = τ
  · exfalso
    have := hl.2
    simp only [ireflLink, if_pos hτ, ireflSite_axis] at this
    omega
  · refine (nonTau_fixed_iff τ p hτ).2 ?_
    have := hl.2
    simp only [ireflLink, if_neg hτ, ireflSite_axis] at this
    omega

/-- `hθST` at the box index: `ireflBoxPerm hΛ` carries `boxS τ p Λ` into `boxT τ p Λ`. The stability
hypothesis is taken at the even constant `2 * p`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`. -/
theorem ireflBoxPerm_mem_boxT_of_mem_boxS (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {l : ↥Λ} (hl : l ∈ boxS τ p Λ) : ireflBoxPerm hΛ l ∈ boxT τ p Λ := by
  simp only [boxS, Finset.mem_filter] at hl
  simp only [boxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ireflBoxPerm_coe, ireflLink_involutive τ (2 * p) l.1]
  exact hl.2

#print axioms ireflBoxPerm_eq_self_of_mem_boxR
#print axioms ireflBoxPerm_mem_boxT_of_mem_boxS

/-- No element of `boxR τ p Λ` is a `τ`-link — `no_tau_link_fixed` transported to the box index, and
what makes `ilinkDagger` the identity on the shared block.

DERIVED: the signature writes no numeral; `τ`, `p` and `Λ` are the caller's. -/
theorem boxR_ne_tau {l : ↥Λ} (hl : l ∈ boxR τ p Λ) : l.1.1 ≠ τ := by
  simp only [boxR, Finset.mem_filter] at hl
  intro hτ
  have := hl.2
  simp only [ireflLink, if_pos hτ, ireflSite_axis] at this
  omega

#print axioms boxR_ne_tau

/-- A `τ`-link based on the plane moves down: from `x_τ = p` it reflects to `p - 1`, so it lies in
`boxS`
and not in the shared block. With `nonTau_link_at_plane_fixed` this places a plaquette in a `(τ, ν)`
plane based on the plane inside `S ∪ R`, which is what `hOloc` asks of the half-action.

DERIVED: the `2` is the plane-to-constant conversion and the `1` is `ireflLink`'s link length; `4`
is
the dimension. -/
theorem tau_link_at_plane_moves_down {l : ILink} (hτ : l.1 = τ) (hp : l.2 τ = p) :
    (ireflLink τ (2 * p) l).2 τ < l.2 τ := by
  simp only [ireflLink, if_pos hτ, ireflSite_axis]
  omega

#print axioms tau_link_at_plane_moves_down

/-- A link based on the plane whose direction is not `τ` keeps its `τ` coordinate under the
reflection at
`2 * p`, so it lies in the shared block. Companion to `tau_link_at_plane_moves_down`: the plane
carries transverse links only, and the `τ`-direction links at the plane belong to the positive half.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. -/
theorem nonTau_link_at_plane_fixed {l : ILink} (hτ : l.1 ≠ τ) (hp : l.2 τ = p) :
    (ireflLink τ (2 * p) l).2 τ = l.2 τ := by
  simp only [ireflLink, if_neg hτ, ireflSite_axis]
  omega

#print axioms nonTau_link_at_plane_fixed

end Box

/-! ## 3d′. Every plaquette lies on one side of the plane -/

section Plaquette

open MassGap.LatticeReflection

/-- The `τ` coordinate of `GibbsSpec.ishift μ x`: `x τ + 1` when `μ = τ`, and `x τ` otherwise.

DERIVED: the `1` is `ishift`'s lattice step; `4` is the dimension. -/
theorem ishift_coord (μ τ : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    (MassGap.GibbsSpec.ishift μ x) τ = if μ = τ then x τ + 1 else x τ := by
  by_cases h : μ = τ
  · subst h; simp [MassGap.GibbsSpec.ishift]
  · simp [MassGap.GibbsSpec.ishift, Ne.symm h, h]

/-- The reflected `τ` coordinate in closed form: `2 * p - 1 - l.2 τ` for a `τ`-link, which reflects
about
`2p - 1` because the link occupies the segment `[x, x + e_τ]`, and `2 * p - l.2 τ` for every other
direction. Shared by the two directed plaquette lemmas below.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`, the `1` is `ireflLink`'s link
length, and `4` is the dimension. -/
theorem irefl_coord (τ : Fin 4) (p : ℤ) (l : MassGap.InfiniteLattice.ILink) :
    (ireflLink τ (2 * p) l).2 τ = if l.1 = τ then 2 * p - 1 - l.2 τ else 2 * p - l.2 τ := by
  by_cases h : l.1 = τ
  · simp [ireflLink, if_pos h, ireflSite_axis]
  · simp [ireflLink, if_neg h, ireflSite_axis]

/-- Every link of a plaquette based at or above the plane satisfies `(irefl l).2 τ ≤ l.2 τ` — moved
down
or fixed, that is, lying in `S ∪ R`. The directed form: which side a plaquette belongs to is decided
by its base's `τ` coordinate against the plane.

The tight case is a `τ`-link, which reflects about `2p - 1`: it moves down exactly when `x_τ ≥ p`,
because `2 * x_τ ≥ 2p - 1` leaves no room between the integers.

This side takes no non-degeneracy hypothesis and holds for `q.1.1 = q.1.2` too. A `τ`-link at `a ≥
p`
reflects to `2p - 1 - a ≤ a`; a transverse link of a plaquette based at `a` sits at `a` or `a + 1`,
both `≥ p`, and reflects to `2p - b ≤ b`. `plaq_links_ge_of_lt`, the statement for the other side,
does take one.

DERIVED: the `2` is the plane-to-constant conversion, the `1`s are `ireflLink`'s link length and
`ishift`'s step, and `4` is the dimension. -/
theorem plaq_links_le_of_le (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hq : p ≤ q.2 τ) :
    ∀ l ∈ MassGap.GibbsSpec.ilinks q, (ireflLink τ (2 * p) l).2 τ ≤ l.2 τ := by
  intro l hl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  by_cases h1 : q.1.1 = τ <;> by_cases h2 : q.1.2 = τ <;>
    rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [irefl_coord, ishift_coord, h1, h2, if_true, if_false] <;>
    omega

#print axioms plaq_links_le_of_le

/-- Every link of a non-degenerate plaquette based strictly below the plane satisfies
`l.2 τ ≤ (irefl l).2 τ` — moved up or fixed, that is, lying in `T ∪ R`.

`hne : q.1.1 ≠ q.1.2` is required on this side. At `μ = ν = τ` with `x_τ = p - 1` the conclusion
fails: `(τ, x)` sits at `p - 1` and moves up to `p`, while `(τ, x + e_τ)` sits at `p` and moves down
to `p - 1`, so that plaquette has links strictly on both sides. `hne` never appears in the tactic
script; `omega` reads it from the context.

DERIVED: the `2` is the plane-to-constant conversion, the `1` is `ireflLink`'s link length, and `4`
is the dimension, as in `plaq_links_le_of_le`. -/
theorem plaq_links_ge_of_lt (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hne : q.1.1 ≠ q.1.2) (hq : q.2 τ < p) :
    ∀ l ∈ MassGap.GibbsSpec.ilinks q, l.2 τ ≤ (ireflLink τ (2 * p) l).2 τ := by
  intro l hl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  by_cases h1 : q.1.1 = τ <;> by_cases h2 : q.1.2 = τ <;>
    rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [irefl_coord, ishift_coord, h1, h2, if_true, if_false] <;>
    omega

#print axioms plaq_links_ge_of_lt

/-- Every non-degenerate plaquette lies on one side of the plane together with the plane: either all
of
its links are moved down or fixed, or all are moved up or fixed, so none has links strictly on both
sides. The undirected corollary of the two lemmas above, and the form `ActionSplit`'s `hOloc` and
`hWloc` take of the action's two halves.

DERIVED: the `2` is the plane-to-constant conversion, the `1` is `ireflLink`'s link length, and `4`
is the dimension, as in `plaq_links_le_of_le`. -/
theorem plaq_links_one_side (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hne : q.1.1 ≠ q.1.2) :
    -- `hne` is consumed by the second disjunct's branch only; see `plaq_links_ge_of_lt`.
    (∀ l ∈ MassGap.GibbsSpec.ilinks q, (ireflLink τ (2 * p) l).2 τ ≤ l.2 τ) ∨
      (∀ l ∈ MassGap.GibbsSpec.ilinks q, l.2 τ ≤ (ireflLink τ (2 * p) l).2 τ) := by
  by_cases hq : q.2 τ < p
  · exact Or.inr (plaq_links_ge_of_lt τ p q hne hq)
  · exact Or.inl (plaq_links_le_of_le τ p q (not_lt.mp hq))

#print axioms plaq_links_one_side

end Plaquette

/-! ## 3d″. The plaquettes of the positive half, and the links they read -/

section HalfPlaq

open MassGap.LatticeReflection

/-- The plane plaquettes at a box: non-degenerate, transverse to `τ` in both directions, and based
exactly on the plane. Every link of such a plaquette is fixed by the reflection at `2 * p`, since
`2p - p = p`, so they lie in the shared block `R` and the reflection does not carry them from one
half to the other. `ActionSplit.plqZero` is the corresponding set on the torus.

DERIVED: the signature writes no numeral; `τ`, `p` and `Λ` are the caller's, and `4` is the
dimension carried by `ILink` and `IPlaq`. -/
def iplqZero (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter
    (fun q => q.1.1 ≠ q.1.2 ∧ q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p)

/-- The plaquettes the action sums over at this box: those inside `Λ` by `GibbsSpec.plaqsIn`, and
non-degenerate. The three groups defined below partition exactly this set.

DERIVED: the signature writes no numeral; `Λ` is the caller's and `4` is the dimension carried by
`ILink` and `IPlaq`. -/
def iplqAll (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter (fun q => q.1.1 ≠ q.1.2)

/-- Membership in `iplqAll`, unfolded: a plaquette is in it exactly when it lies in
`GibbsSpec.plaqsIn Λ` and is non-degenerate.

DERIVED: the signature writes no numeral. -/
theorem mem_iplqAll {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqAll Λ ↔ q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 := by
  simp only [iplqAll, Finset.mem_filter]

/-- The boundary word of a plaquette restricted to the box: `GibbsSpec.ibd q` read as a list of `↥Λ`
paired with orientations. `StrongCoupling`'s cluster expansion is stated over abstract
`{Lk Pq : Type}` with `Fintype`, `DecidableEq` and `bd : Pq → List (Lk × Bool)`, and this presents a
`ℤ⁴` box in that form.

The restriction is total because `GibbsSpec.mem_plaqsIn` puts every link of a plaquette of
`plaqsIn Λ` in `Λ`, and `iplqAll Λ` is a subset of `plaqsIn Λ`; so `List.pmap` needs no default and
no truncation. `ibd` is a separate constant in `GibbsSpec` and in `InfiniteLattice`, so the
namespace
is written out here, and `gibbs_ihol_eq` below relates the two.

DERIVED: the signature writes no numeral; `Λ` is the caller's and `4` is the dimension carried by
`ILink` and `IPlaq`, as in `iplqAll`. -/
def boxBd (Λ : Finset MassGap.InfiniteLattice.ILink) (q : ↥(iplqAll Λ)) :
    List (↥Λ × Bool) :=
  List.pmap (fun lb (h : lb.1 ∈ Λ) => ((⟨lb.1, h⟩ : ↥Λ), lb.2))
    (MassGap.GibbsSpec.ibd (q : MassGap.GibbsSpec.IPlaq))
    (fun lb hlb => by
      have hq : (q : MassGap.GibbsSpec.IPlaq) ∈ MassGap.GibbsSpec.plaqsIn Λ :=
        (mem_iplqAll.mp q.2).1
      exact MassGap.GibbsSpec.mem_plaqsIn.mp hq lb.1 (List.mem_map.mpr ⟨lb, hlb, rfl⟩))

#print axioms boxBd

/-- The box word lists the plaquette's own four links, in order: mapping the first component back to
`ILink` gives `GibbsSpec.ilinks q`. The `Bool` orientations are not this statement's subject;
`wilsonHol_boxBd` is what checks those.

DERIVED: the signature writes no numeral; `Λ` is the caller's and `4` is the dimension carried by
`ILink` and `IPlaq`, as in `iplqAll`. -/
theorem boxBd_map_fst (Λ : Finset MassGap.InfiniteLattice.ILink) (q : ↥(iplqAll Λ)) :
    (boxBd Λ q).map (fun lb => (lb.1 : MassGap.InfiniteLattice.ILink))
      = MassGap.GibbsSpec.ilinks (q : MassGap.GibbsSpec.IPlaq) := by
  simp [boxBd, MassGap.GibbsSpec.ilinks, MassGap.GibbsSpec.ibd]

#print axioms boxBd_map_fst

/-- `WilsonLattice.wilsonHol (boxBd Λ) q u` equals `GibbsSpec.ihol q (GibbsSpec.splice Λ u ω)`: the
holonomy of the restricted word against the box's own variables is the lattice holonomy of the
spliced configuration. The boundary configuration `ω` is free on the right and absent on the left.

This is one plaquette. `wtFree` sums over `iplqAll Λ`, and `wtFree_congr_right` is what carries this
equality to that sum.

DERIVED: the signature writes no numeral; `Λ` is the caller's and `4` is the dimension carried by
`ILink` and `IPlaq`, as in `iplqAll`. -/
theorem wilsonHol_boxBd {G : Type} [Group G] (Λ : Finset MassGap.InfiniteLattice.ILink)
    (q : ↥(iplqAll Λ)) (u : MassGap.GibbsSpec.VConf G Λ)
    (ω : MassGap.GibbsSpec.IConf G) :
    MassGap.WilsonLattice.wilsonHol (boxBd Λ) q u
      = MassGap.GibbsSpec.ihol (q : MassGap.GibbsSpec.IPlaq)
          (MassGap.GibbsSpec.splice Λ u ω) := by
  have hq : (q : MassGap.GibbsSpec.IPlaq) ∈ MassGap.GibbsSpec.plaqsIn Λ :=
    (mem_iplqAll.mp q.2).1
  have hmem : ∀ l ∈ MassGap.GibbsSpec.ilinks (q : MassGap.GibbsSpec.IPlaq), l ∈ Λ :=
    MassGap.GibbsSpec.mem_plaqsIn.mp hq
  have e1 : ((q : MassGap.GibbsSpec.IPlaq).1.1, (q : MassGap.GibbsSpec.IPlaq).2) ∈ Λ :=
    hmem _ (by rw [MassGap.GibbsSpec.ilinks_eq]; simp)
  have e2 : ((q : MassGap.GibbsSpec.IPlaq).1.2,
      MassGap.GibbsSpec.ishift (q : MassGap.GibbsSpec.IPlaq).1.1
        (q : MassGap.GibbsSpec.IPlaq).2) ∈ Λ :=
    hmem _ (by rw [MassGap.GibbsSpec.ilinks_eq]; simp)
  have e3 : ((q : MassGap.GibbsSpec.IPlaq).1.1,
      MassGap.GibbsSpec.ishift (q : MassGap.GibbsSpec.IPlaq).1.2
        (q : MassGap.GibbsSpec.IPlaq).2) ∈ Λ :=
    hmem _ (by rw [MassGap.GibbsSpec.ilinks_eq]; simp)
  have e4 : ((q : MassGap.GibbsSpec.IPlaq).1.2, (q : MassGap.GibbsSpec.IPlaq).2) ∈ Λ :=
    hmem _ (by rw [MassGap.GibbsSpec.ilinks_eq]; simp)
  simp [MassGap.WilsonLattice.wilsonHol, boxBd, MassGap.GibbsSpec.ihol,
    MassGap.GibbsSpec.ibd, List.pmap, MassGap.GibbsSpec.splice_mem e1,
    MassGap.GibbsSpec.splice_mem e2, MassGap.GibbsSpec.splice_mem e3,
    MassGap.GibbsSpec.splice_mem e4]

#print axioms wilsonHol_boxBd

/-- At most sixteen plaquettes read a given link: `(GibbsSpec.touching l).card ≤ 16`.
`GibbsSpec.touching` enumerates four directions against four placements and `GibbsSpec.mem_touching`
puts every plaquette reading the link inside it. The statement is a bound and not a count — the set
of readers is strictly smaller, since at `ν = l.1` the first two entries coincide — and a bound is
what a `touchDeg` estimate consumes.

DERIVED: `16` is four placements against the `4` directions, `4 * dim` at `dim = 4`, the same count
`StrongCoupling.linkMult_bd_le` derives. The four placements are two pair-positions against two base
sites and do not scale with the dimension, so this is not the dimension twice over; the two readings
agree only at `dim = 4`. `4` is the dimension. -/
theorem card_touching_le (l : MassGap.InfiniteLattice.ILink) :
    (MassGap.GibbsSpec.touching l).card ≤ 16 := by
  classical
  have hcard4 : ∀ a b c d : MassGap.GibbsSpec.IPlaq,
      ({a, b, c, d} : Finset MassGap.GibbsSpec.IPlaq).card ≤ 4 := by
    intro a b c d
    have h1 := Finset.card_insert_le a ({b, c, d} : Finset MassGap.GibbsSpec.IPlaq)
    have h2 := Finset.card_insert_le b ({c, d} : Finset MassGap.GibbsSpec.IPlaq)
    have h3 := Finset.card_insert_le c ({d} : Finset MassGap.GibbsSpec.IPlaq)
    have h4 : ({d} : Finset MassGap.GibbsSpec.IPlaq).card = 1 := Finset.card_singleton d
    omega
  unfold MassGap.GibbsSpec.touching
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum (fun ν _ => hcard4 _ _ _ _)) ?_
  simp

#print axioms card_touching_le

/-- The box word supports at most four links: `(StrongCoupling.linkSupp (boxBd Λ) q).card ≤ 4`. The
`ℤ⁴`
mirror of `InfiniteLattice.linksOf_card_le`, repackaged for the subtype `↥Λ` that `boxBd` reads.
`iplqAll` excludes the degenerate plane, so on this domain the four links are distinct; `≤` is the
form `StrongCoupling.touchDeg_bd_le`'s argument consumes.

DERIVED: `4` is the number of links in a plaquette boundary word, as in `GibbsSpec.ibd`, and also
the dimension carried by `ILink` and `IPlaq` as in `iplqAll`. -/
theorem linkSupp_boxBd_card_le (Λ : Finset MassGap.InfiniteLattice.ILink)
    (q : ↥(iplqAll Λ)) :
    (MassGap.StrongCoupling.linkSupp (boxBd Λ) q).card ≤ 4 := by
  classical
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.length_map]
  simp [boxBd, MassGap.GibbsSpec.ibd]

#print axioms linkSupp_boxBd_card_le

/-- A link in the support of the box word is a link of the plaquette: `boxBd_map_fst` read through
`linkSupp`'s `toFinset`. Every argument about the box's touch graph starts here.

DERIVED: the signature writes no numeral; `Λ` is the caller's and `4` is the dimension carried by
`ILink` and `IPlaq`, as in `iplqAll`. -/
theorem mem_ilinks_of_mem_linkSupp_boxBd (Λ : Finset MassGap.InfiniteLattice.ILink)
    (q : ↥(iplqAll Λ)) (l : ↥Λ)
    (hl : l ∈ MassGap.StrongCoupling.linkSupp (boxBd Λ) q) :
    (l : MassGap.InfiniteLattice.ILink)
      ∈ MassGap.GibbsSpec.ilinks (q : MassGap.GibbsSpec.IPlaq) := by
  classical
  have h1 : l ∈ (boxBd Λ q).map Prod.fst := List.mem_toFinset.mp hl
  have h2 : (l : MassGap.InfiniteLattice.ILink)
      ∈ (boxBd Λ q).map (fun lb => (lb.1 : MassGap.InfiniteLattice.ILink)) := by
    obtain ⟨lb, hlb, hlb2⟩ := List.mem_map.mp h1
    exact List.mem_map.mpr ⟨lb, hlb, by rw [hlb2]⟩
  rwa [boxBd_map_fst] at h2

#print axioms mem_ilinks_of_mem_linkSupp_boxBd

/-- Each link of the box is read by at most sixteen of its plaquettes:
`StrongCoupling.linkMult (boxBd Λ) l ≤ 16`. `boxBd_map_fst` carries a link of the box word back to
`GibbsSpec.ilinks`, `GibbsSpec.mem_touching` puts the plaquette in `touching`, and `Subtype.val` is
injective, so `card_touching_le` bounds the count. The `ℤ⁴` analogue of
`StrongCoupling.linkMult_bd_le`.

DERIVED: `16` is four placements against the `4` directions, `4 * dim` at `dim = 4`, as in
`card_touching_le`; `4` is the dimension carried by `ILink` as in `iplqAll`. -/
theorem linkMult_boxBd_le (Λ : Finset MassGap.InfiniteLattice.ILink) (l : ↥Λ) :
    MassGap.StrongCoupling.linkMult (boxBd Λ) l ≤ 16 := by
  classical
  refine le_trans ?_ (card_touching_le (l : MassGap.InfiniteLattice.ILink))
  refine Finset.card_le_card_of_injOn (fun q => (q : MassGap.GibbsSpec.IPlaq)) ?_ ?_
  · intro q hq
    exact MassGap.GibbsSpec.mem_touching
      (mem_ilinks_of_mem_linkSupp_boxBd Λ q l (Finset.mem_filter.mp hq).2)
  · intro a _ b _ h
    exact Subtype.ext h

#print axioms linkMult_boxBd_le

/-- `StrongCoupling.touchDeg (boxBd Λ) ≤ 16 * 4`, with no dependence on the box: `Λ` does not occur
on
the right.

`StrongCoupling.touchNbrs_card_le` is carrier-free and bounds the touch count by
`∑ l ∈ linkSupp bd p, linkMult bd l`; the two factors are `linkSupp_boxBd_card_le` and
`linkMult_boxBd_le`. The assembly is the one `StrongCoupling.touchDeg_bd_le` performs on the
periodic
lattice.

DERIVED: `16` is four placements against the `4` directions, as in `card_touching_le`; `4` is the
number of links in a plaquette boundary word and the dimension, as in `linkSupp_boxBd_card_le`. The
product `16 * 4` equals `StrongCoupling.touchDeg_bd_le`'s `16 * dim` at `dim = 4`, but the
factorisations are transposed — here `linkMult` against `linkSupp`, there `linkSupp` against word
slots and the dimension. -/
theorem touchDeg_boxBd_le (Λ : Finset MassGap.InfiniteLattice.ILink) :
    MassGap.StrongCoupling.touchDeg (boxBd Λ) ≤ 16 * 4 := by
  classical
  refine Finset.sup_le (fun p _ => ?_)
  refine le_trans (MassGap.StrongCoupling.touchNbrs_card_le (boxBd Λ) p) ?_
  calc ∑ l ∈ MassGap.StrongCoupling.linkSupp (boxBd Λ) p,
        MassGap.StrongCoupling.linkMult (boxBd Λ) l
      ≤ ∑ _l ∈ MassGap.StrongCoupling.linkSupp (boxBd Λ) p, 16 :=
        Finset.sum_le_sum (fun l _ => linkMult_boxBd_le Λ l)
    _ = (MassGap.StrongCoupling.linkSupp (boxBd Λ) p).card * 16 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * 16 := Nat.mul_le_mul_right _ (linkSupp_boxBd_card_le Λ p)
    _ = 16 * 4 := by ring

#print axioms touchDeg_boxBd_le

/-- **The strong-coupling bound, at the box carrier.**

`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le` is carrier-free over abstract
link and plaquette types, and `touchDeg_boxBd_le` supplies its combinatorial input for a finite box
of `ℤ⁴` **with no dependence on the box**. So the connected correlator of two plaquette observables in
the free-boundary box state decays geometrically in the boundary-word distance, at a rate and
constant that do not grow with the box.

**Why the box carrier and not the periodic one.** `stateFree_eq_expect_boxBd` identifies `stateFree`
with the `wilsonSystem (boxBd Λ)` expectation this bounds, and `stateFree` along `mixCube` is what
`wilson_positiveTransfer_of_mixCube_limit`'s `htend` converges to — so this bounds correlators of the
very state the transfer data is built from. Routing through the periodic lattice instead would need
the periodic and free-boundary limits to agree, which is boundary-condition independence and is
available here only at zero coupling.

`touchDeg_boxBd_le` had no consumers before this.

Scope: this is a bound on a correlator of two SINGLE plaquettes at boundary-word separation `k`. The
gap obligation is about pairings of general invariant observables under a reflection, so this is an
entry bound and not yet an entry of `GaugeInvariantAlgebra.gapEntry`.

DERIVED: `16 * 4` is `touchDeg_boxBd_le`'s bound, transcribed — `16` the link multiplicity of a box
word and `4` the links in one, so the product is the combinatorial degree and not a chosen constant;
`0` is the lower end of the coupling range, which the cluster expansion requires; `1` is
`coreRate`'s own convergence threshold in `hr`, the condition under which the expansion sums,
and not a chosen bound. -/
theorem wilsonCorrConn_boxBd_abs_le (hN : N ≠ 0)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (p₀ pd : ↥(iplqAll Λ)) {β : ℝ} (hβ : 0 ≤ β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (k : ℕ) (hk : pd ∉ MassGap.StrongCoupling.ball (boxBd Λ) p₀ k) :
    |MassGap.WilsonBridge.wilsonCorrConn (Nc := N) (boxBd Λ) p₀ β pd|
      ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
        * MassGap.StrongCoupling.coreRate (16 * 4) β ^ k :=
  MassGap.StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le hN
    (boxBd Λ) p₀ pd hβ (16 * 4) (touchDeg_boxBd_le Λ) hr k hk

#print axioms wilsonCorrConn_boxBd_abs_le

/-- Along any axis `τ`, every link of a plaquette sits at the plaquette's own coordinate or one
above it:
`l.2 τ = q.2 τ ∨ l.2 τ = q.2 τ + 1`. `GibbsSpec.ibd` names the sites `x`, `ishift a x` and
`ishift b x` and no others, and `ishift_coord` says a shift raises one coordinate by one.

The offsets lie in `{0, +1}` rather than `{-1, 0, +1}`, which is why two plaquettes sharing a link
differ by at most one step along `τ`. The `ℤ⁴` form of `StrongCoupling.link_site_coord`, without the
circle.

DERIVED: `1` is the one lattice step `ishift` takes; `4` is the dimension. -/
theorem ilink_site_coord (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq)
    (l : MassGap.InfiniteLattice.ILink)
    (hl : l ∈ MassGap.GibbsSpec.ilinks q) :
    l.2 τ = q.2 τ ∨ l.2 τ = q.2 τ + 1 := by
  have hup : ∀ ν : Fin 4, (MassGap.GibbsSpec.ishift ν q.2) τ = q.2 τ
      ∨ (MassGap.GibbsSpec.ishift ν q.2) τ = q.2 τ + 1 := by
    intro ν
    rw [ishift_coord]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact hup _
  · exact hup _
  · exact Or.inl rfl

#print axioms ilink_site_coord

/-- Displacement along `τ` from a base site, `(q.2 τ - x₀ τ).natAbs` — the level a radius argument
measures on `ℤ⁴`. The counterpart of `StrongCoupling.axisLvl`; with no circle it is the absolute
value of an integer difference rather than a distance on `Fin n`.

DERIVED: the signature writes no numeral; `τ` and `x₀` are the caller's and `4` is the dimension. -/
def axisLvlBox (τ : Fin 4) (x₀ : MassGap.GibbsSpec.ISite)
    (q : MassGap.GibbsSpec.IPlaq) : ℕ := (q.2 τ - x₀ τ).natAbs

/-- One touch-step moves `axisLvlBox` by at most one:
`axisLvlBox τ x₀ q ≤ axisLvlBox τ x₀ p + 1` whenever `p` and `q` touch in the box word. Two touching
plaquettes share a link, and by `ilink_site_coord` that link sits at each one's own `τ` coordinate
or
one above it; both offsets lie in `{0, +1}`, so the four cases put the two base sites within one
step.

DERIVED: `1` is the one lattice step a touch can cross, read off `ilink_site_coord` and not chosen;
`4` is the dimension. -/
theorem axisLvlBox_lipschitz (Λ : Finset MassGap.InfiniteLattice.ILink) (τ : Fin 4)
    (x₀ : MassGap.GibbsSpec.ISite) (p q : ↥(iplqAll Λ))
    (h : MassGap.StrongCoupling.Touch (boxBd Λ) p q) :
    axisLvlBox τ x₀ (q : MassGap.GibbsSpec.IPlaq)
      ≤ axisLvlBox τ x₀ (p : MassGap.GibbsSpec.IPlaq) + 1 := by
  obtain ⟨l, hp, hq⟩ := h
  have hP := ilink_site_coord τ (p : MassGap.GibbsSpec.IPlaq) _
    (mem_ilinks_of_mem_linkSupp_boxBd Λ p l hp)
  have hQ := ilink_site_coord τ (q : MassGap.GibbsSpec.IPlaq) _
    (mem_ilinks_of_mem_linkSupp_boxBd Λ q l hq)
  simp only [axisLvlBox]
  rcases hP with hP | hP <;> rcases hQ with hQ | hQ <;> omega

#print axioms axisLvlBox_lipschitz

/-- A plaquette displaced more than `k` steps along `τ` from `p₀` lies outside the `k`-step
touch-ball of
`p₀`: `q ∉ StrongCoupling.ball (boxBd Λ) p₀ k`. This is the shape of the hypothesis `hk` that
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` takes, supplied for `boxBd` from a
`ℤ⁴`
separation.

`StrongCoupling.lvl_le_of_mem_ball` is carrier-free and does the work: `axisLvlBox` is zero at `p₀`
and rises by at most one per touch, so a ball of radius `k` reaches no level above `k`.

The index is the plain displacement. On the torus the index has to be `Moment.circLag` rather than
the raw lag, because the lattice wraps and `StrongCoupling.raw_lag_radius_refuted` exhibits a
plaquette the raw index would place outside a ball it is inside. `ℤ⁴` does not wrap.

DERIVED: `4` is the dimension; the comparison is against the caller's `k` and carries no constant.
-/
theorem not_mem_ball_of_axis_gt (Λ : Finset MassGap.InfiniteLattice.ILink) (τ : Fin 4)
    (p₀ q : ↥(iplqAll Λ)) (k : ℕ)
    (hk : k < ((q : MassGap.GibbsSpec.IPlaq).2 τ
      - (p₀ : MassGap.GibbsSpec.IPlaq).2 τ).natAbs) :
    q ∉ MassGap.StrongCoupling.ball (boxBd Λ) p₀ k := by
  classical
  intro hmem
  have hlvl := MassGap.StrongCoupling.lvl_le_of_mem_ball (boxBd Λ) p₀
    (fun r => axisLvlBox τ ((p₀ : MassGap.GibbsSpec.IPlaq).2) (r : MassGap.GibbsSpec.IPlaq))
    (by simp [axisLvlBox])
    (fun p r ht => axisLvlBox_lipschitz Λ τ _ p r ht) k q hmem
  simp only [axisLvlBox] at hlvl
  omega

#print axioms not_mem_ball_of_axis_gt

/-- **Translating a plaquette moves its base site along the axis.** `ishiftPlaq` leaves the plane
directions alone and shifts the corner, so iterating it iterates `ishift` on the corner.

DERIVED: `4` is the spacetime dimension, indexing the translation's direction; `m` is the
caller's. -/
theorem ishiftPlaq_iterate (μ : Fin 4) (m : ℕ) (q : MassGap.GibbsSpec.IPlaq) :
    (MassGap.InfiniteShift.ishiftPlaq μ)^[m] q
      = (q.1, (MassGap.InfiniteLattice.ishift μ)^[m] q.2) := by
  induction m with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl

#print axioms ishiftPlaq_iterate

/-- The axis coordinate of an `m`-fold translate is `m` above the original.

DERIVED: `4` is the spacetime dimension, indexing the translation's direction; `m` is the
caller's. -/
theorem ishiftPlaq_iterate_axis (μ : Fin 4) (m : ℕ) (q : MassGap.GibbsSpec.IPlaq) :
    ((MassGap.InfiniteShift.ishiftPlaq μ)^[m] q).2 μ = q.2 μ + m := by
  rw [ishiftPlaq_iterate]
  exact MassGap.InfiniteShift.ishift_iterate μ m q.2

#print axioms ishiftPlaq_iterate_axis

/-- **The reflected plaquette's axis coordinate**, in either of `ireflPlaq`'s branches. The two
branches differ by one, because a plaquette spanning the reflection direction has its corner moved
to the far end of the link.

DERIVED: `1` is `ireflPlaq`'s own offset on the branches where a plane direction is `τ`, transcribed
rather than chosen; `4` is the spacetime dimension. -/
theorem ireflPlaq_axis (τ : Fin 4) (c : ℤ) (q : MassGap.GibbsSpec.IPlaq) :
    (MassGap.LatticeReflection.ireflPlaq τ c q).2 τ = c - q.2 τ
      ∨ (MassGap.LatticeReflection.ireflPlaq τ c q).2 τ = c - 1 - q.2 τ := by
  unfold MassGap.LatticeReflection.ireflPlaq
  split_ifs
  · right; simp [MassGap.LatticeReflection.ireflSite_axis]
  · right; simp [MassGap.LatticeReflection.ireflSite_axis]
  · left; simp [MassGap.LatticeReflection.ireflSite_axis]

#print axioms ireflPlaq_axis

/-- **The separation between a plaquette's reflection and its translate grows with the
translation.** For a plaquette whose base site lies at or above the reflection plane, the axis
distance from `ireflPlaq τ (2 * p) q` to the `m`-fold translate of `q` is at least `m`.

Both branches of `ireflPlaq_axis` give `2 * q.2 τ - 2 * p + m` or one more, and `p ≤ q.2 τ` makes
the leading part non-negative.

**This is what lets a correlation estimate be applied to an observable against its own translate.**
The estimates in `StrongCoupling` are indexed by a ball radius around one plaquette; this supplies
the radius, growing with the translation, when the second plaquette is a translate of the first and
the first is reflected.

DERIVED: `2` is the reflection plane's spacing in lattice units — the plane through `2 * p` sends
`h` to `2 * p - h`, so the separation carries the factor; `4` is the spacetime dimension. -/
theorem axis_sep_irefl_shift (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hq : p ≤ q.2 τ) (m : ℕ) :
    m ≤ (((MassGap.InfiniteShift.ishiftPlaq τ)^[m] q).2 τ
      - (MassGap.LatticeReflection.ireflPlaq τ (2 * p) q).2 τ).natAbs := by
  rw [ishiftPlaq_iterate_axis]
  rcases ireflPlaq_axis τ (2 * p) q with h | h <;> rw [h] <;> omega

#print axioms axis_sep_irefl_shift

/-- **The translate lies outside every ball around the reflection of radius below the
translation.** `not_mem_ball_of_axis_gt` fed by `axis_sep_irefl_shift`.

DERIVED: `2` is the reflection plane's spacing, carried from `axis_sep_irefl_shift`; `4` is the
spacetime dimension. -/
theorem not_mem_ball_of_irefl_shift (Λ : Finset MassGap.InfiniteLattice.ILink) (τ : Fin 4)
    (p : ℤ) (q : MassGap.GibbsSpec.IPlaq) (hq : p ≤ q.2 τ) (m k : ℕ) (hk : k < m)
    (hrefl : MassGap.LatticeReflection.ireflPlaq τ (2 * p) q ∈ iplqAll Λ)
    (hshift : (MassGap.InfiniteShift.ishiftPlaq τ)^[m] q ∈ iplqAll Λ) :
    (⟨(MassGap.InfiniteShift.ishiftPlaq τ)^[m] q, hshift⟩ : ↥(iplqAll Λ))
      ∉ MassGap.StrongCoupling.ball (boxBd Λ)
          ⟨MassGap.LatticeReflection.ireflPlaq τ (2 * p) q, hrefl⟩ k :=
  not_mem_ball_of_axis_gt Λ τ ⟨_, hrefl⟩ ⟨_, hshift⟩ k
    (lt_of_lt_of_le hk (axis_sep_irefl_shift τ p q hq m))

#print axioms not_mem_ball_of_irefl_shift

/-- The plaquettes the positive half-action sums over: inside the box by `GibbsSpec.plaqsIn`,
non-degenerate, not in the plane, and based at or above it. The `ℤ⁴` counterpart of
`ActionSplit.plqPlus`.

Degenerate plaquettes are filtered out rather than assumed away, because a `Finset IPlaq` carries no
`μ < ν` side condition and `plaq_links_ge_of_lt` is false without one. The whole diagonal `μ = ν` is
dropped, not only `μ = ν = τ`: its holonomy is the identity
(`InfiniteLattice.ibd_diag_hol_one`), so for the Wilson density it contributes `wilsonDensity 1 = 0`
and dropping it changes the sum by nothing. For a general `φ` it would shift the action by a
constant
per diagonal plaquette.

DERIVED: the signature writes no numeral; `τ`, `p` and `Λ` are the caller's, and `4` is the
dimension. -/
def iplqPlus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter
    (fun q => q.1.1 ≠ q.1.2 ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ p ≤ q.2 τ)

/-- The mirror set: the plaquettes the negative half-action sums over, based strictly below the
plane,
with the same non-degeneracy and off-plane filters as `iplqPlus`.

DERIVED: the signature writes no numeral; `τ`, `p` and `Λ` are the caller's, and `4` is the
dimension. -/
def iplqMinus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (MassGap.GibbsSpec.plaqsIn Λ).filter
    (fun q => q.1.1 ≠ q.1.2 ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ q.2 τ < p)

theorem mem_iplqPlus {τ : Fin 4} {p : ℤ} {Λ : Finset MassGap.InfiniteLattice.ILink}
    {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqPlus τ p Λ ↔
      q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 ∧
        ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ p ≤ q.2 τ := by
  simp only [iplqPlus, Finset.mem_filter]

theorem mem_iplqMinus {τ : Fin 4} {p : ℤ} {Λ : Finset MassGap.InfiniteLattice.ILink}
    {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqMinus τ p Λ ↔
      q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 ∧
        ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) ∧ q.2 τ < p := by
  simp only [iplqMinus, Finset.mem_filter]

#print axioms mem_iplqPlus

theorem iplqPlus_disjoint_iplqMinus (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (iplqPlus τ p Λ) (iplqMinus τ p Λ) := by
  refine Finset.disjoint_left.2 fun q hP hM => ?_
  exact absurd (mem_iplqMinus.mp hM).2.2.2 (not_lt.mpr (mem_iplqPlus.mp hP).2.2.2)

#print axioms iplqPlus_disjoint_iplqMinus

/-- The reflection at `2 * p` carries `iplqPlus τ p Λ` into `iplqMinus τ p Λ`, given that the image
plaquette is in `plaqsIn Λ`. The `ℤ⁴` counterpart of `ActionSplit.reflPlaq_plus_mem_minus`.

Three branches on whether `μ` or `ν` equals `τ`. In the transverse branch the image base sits at
`2p - x_τ`, which is `< p` only when `x_τ > p`; at `x_τ = p` the plaquette is its own image, which
is
`iplqZero` and is excluded from `iplqPlus`.

The `plaqsIn` half is taken as the hypothesis `hmem` rather than proved: it holds whenever `Λ` is
stable under the link reflection, which is the same `hΛ` that `irefl_box_pairing_nonneg` takes.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`, the `1` is `ireflPlaq`'s
link-length offset, and `4` is the dimension. -/
theorem ireflPlaq_mem_iplqMinus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqPlus τ p Λ)
    (hmem : ireflPlaq τ (2 * p) q ∈ MassGap.GibbsSpec.plaqsIn Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqMinus τ p Λ := by
  obtain ⟨_, hne, hnz, hge⟩ := mem_iplqPlus.mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hne hnz hge
  rw [mem_iplqMinus]
  by_cases hμ : μ = τ
  · subst hμ
    refine ⟨hmem, ?_, ?_, ?_⟩
    · simpa [ireflPlaq] using fun h => hne h.symm
    · simp [ireflPlaq]
    · simp only [ireflPlaq, ireflSite_axis, reduceIte]
      omega
  · by_cases hν : ν = τ
    · subst hν
      refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ] using fun h => hμ h.symm
      · simp [ireflPlaq, hμ]
      · simp only [ireflPlaq, if_neg hμ, ireflSite_axis, reduceIte]
        omega
    · have hxp : x τ ≠ p := fun h => hnz ⟨hμ, hν, h⟩
      refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ, hν] using hne
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        rintro ⟨-, -, hz⟩
        omega
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        omega

#print axioms ireflPlaq_mem_iplqMinus

/-- `GibbsSpec.ishift` and `InfiniteLattice.ishift` are the same function, by `rfl`. The two
namespaces
are import-isolated and each defines `ISite` and `ishift` for itself with identical bodies, so they
are distinct constants: a rewrite stated on one does not fire on the other, and both print as
`ishift` in a goal. This equation is what lets the reflection lemmas reach a goal produced by
`GibbsSpec.ilinks_eq`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem gibbs_ishift_eq :
    (MassGap.GibbsSpec.ishift : Fin 4 → MassGap.GibbsSpec.ISite → MassGap.GibbsSpec.ISite)
      = MassGap.InfiniteLattice.ishift := rfl

#print axioms gibbs_ishift_eq

/-- `GibbsSpec.iunshift` and `ReflectionShift.iunshift` are the same map, by `rfl` — the same
situation
as `gibbs_ishift_eq`: identical bodies in two isolated namespaces are still two constants, both
printing as `iunshift`, and a lemma proved about one is inert on the other.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem gibbs_iunshift_eq :
    (MassGap.GibbsSpec.iunshift : Fin 4 → MassGap.GibbsSpec.ISite → MassGap.GibbsSpec.ISite)
      = MassGap.ReflectionShift.iunshift := rfl

#print axioms gibbs_iunshift_eq

/-- Every link of the image plaquette is a reflected link of the original, stated as: reflecting a
link
of `ilinks (ireflPlaq τ c q)` again lands it back in `ilinks q`. By involutivity this is the same
fact, and it is the form the box transport consumes.

The order of the links differs — the mirror reverses the loop, which is what `ihol_ireflConf` reads
as conjugacy rather than equality. `plaqsIn` asks only that every link lie in the box, so order does
not enter here.

`hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)` is required. For `q = ((τ, τ), x)` the links sit at `x_τ` and
`x_τ + 1`, covering `[x, x + 2e_τ]`; their reflections cover `[c - 2 - x_τ, c - x_τ]`, based at
`c - 2 - x_τ`, while `ireflPlaq` puts the image base at `c - 1 - x_τ`, so the image's links are not
the reflections of the original's. The open goal in that case is
`ireflSite τ (c-1) (ishift τ (ireflSite τ (c-1) x))` against `ishift τ x`, reducing to `x_τ - 1`
against `x_τ + 1`.

That case is excluded where `ireflPlaq` is used: `ihol_ireflConf` holds for a degenerate plaquette
anyway with `g = 1`, since a degenerate loop retraces itself and both holonomies are the identity.
The torus has the same feature, which is why `ActionSplit.plqDeg` is a separate group excluded from
the action split. This hypothesis is `plqDeg`'s complement, and `iplqPlus` excludes the whole
diagonal, so it costs nothing at the call site.

DERIVED: the `1` is `ireflPlaq`'s link-length offset, the `2` appears in the description of the
excluded degenerate case rather than in the signature, and `4` is the dimension. -/
theorem ireflLink_mem_ilinks (τ : Fin 4) (c : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (ireflPlaq τ c q)) :
    ireflLink τ c l ∈ MassGap.GibbsSpec.ilinks q := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  rw [MassGap.GibbsSpec.ilinks_eq] at hl ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
  by_cases hμ : μ = τ <;> by_cases hν : ν = τ
  · exact absurd ⟨hμ, hν⟩ hdeg
  all_goals
    simp only [ireflPlaq, hμ, hν, reduceIte] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [ireflLink, hμ, hν, gibbs_ishift_eq, ireflSite_ireflSite, ireflSite_ireflSite_pred,
        ireflSite_ishift_of_ne, ishift_ireflSite_axis]

#print axioms ireflLink_mem_ilinks

/-- A box stable under the link reflection contains the image plaquette. This discharges the `hmem`
hypothesis of `ireflPlaq_mem_iplqMinus` from the same `hΛ` that `irefl_box_pairing_nonneg` takes, so
no new assumption enters. Carries `ireflLink_mem_ilinks`'s non-degeneracy hypothesis `hdeg`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem ireflPlaq_mem_plaqsIn (τ : Fin 4) (c : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) (hq : q ∈ MassGap.GibbsSpec.plaqsIn Λ) :
    ireflPlaq τ c q ∈ MassGap.GibbsSpec.plaqsIn Λ := by
  rw [MassGap.GibbsSpec.mem_plaqsIn]
  intro l hl
  have h1 : ireflLink τ c l ∈ Λ :=
    MassGap.GibbsSpec.mem_plaqsIn.mp hq _ (ireflLink_mem_ilinks τ c q hdeg hl)
  have h2 := hΛ _ h1
  rwa [ireflLink_involutive τ c l] at h2

#print axioms ireflPlaq_mem_plaqsIn

/-- The reflection at `2 * p` maps `iplqPlus τ p Λ` into `iplqMinus τ p Λ` with no leftover
hypothesis —
`ireflPlaq_mem_iplqMinus` composed with `ireflPlaq_mem_plaqsIn`.
`ActionSplit.reflPlaq_plus_mem_minus`
on `ℤ⁴`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; `4` is the dimension. -/
theorem ireflPlaq_maps_plus_to_minus (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqPlus τ p Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqMinus τ p Λ :=
  ireflPlaq_mem_iplqMinus τ p Λ hq
    (ireflPlaq_mem_plaqsIn τ (2 * p) hΛ
      (fun h => (mem_iplqPlus.mp hq).2.1 (h.1.trans h.2.symm)) (mem_iplqPlus.mp hq).1)

#print axioms ireflPlaq_maps_plus_to_minus

/-- Every link of a positive-half plaquette lies in `boxS τ p Λ ∪ boxR τ p Λ`, given that the link
is in
the box. The `ℤ⁴` form of the step `ReflectionStrong.actPlus_local` consumes on the torus
(`plaq_links_le`): it makes the positive half-action an observable of the positive half, which is
what lets the half Boltzmann factor be absorbed into the observable.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iplqPlus_links_mem (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqPlus τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) (h : l ∈ Λ) :
    (⟨l, h⟩ : ↥Λ) ∈ boxS τ p Λ ∪ boxR τ p Λ := by
  obtain ⟨_, _, _, hge⟩ := mem_iplqPlus.mp hq
  have hle := plaq_links_le_of_le τ p q hge l hl
  simp only [Finset.mem_union, boxS, boxR, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

#print axioms iplqPlus_links_mem

/-- The links of a positive-half plaquette lie in the box — the side condition `iplqPlus_links_mem`
asks for, read off the `plaqsIn` filter inside `iplqPlus`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iplqPlus_link_mem_box (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqPlus τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) : l ∈ Λ :=
  MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqPlus.mp hq).1 l hl

#print axioms iplqPlus_link_mem_box

/-- A link based on the plane whose direction is not `τ` lies in `boxR`: `ν ≠ τ` and `x τ = p` give
`(ireflLink τ (2 * p) (ν, x)).2 τ = 2p - p = p = x τ`, which is `boxR`'s filter.

DERIVED: the signature writes no numeral of its own — the `2` of the reflection constant sits inside
`boxR`; `4` is the dimension. -/
theorem transverse_link_mem_boxR (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ)
    (x : MassGap.GibbsSpec.ISite) (hx : x τ = p)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (h : ((ν, x) : MassGap.InfiniteLattice.ILink) ∈ Λ) :
    (⟨(ν, x), h⟩ : ↥Λ) ∈ boxR τ p Λ := by
  simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and, ireflLink, if_neg hν,
    ireflSite_axis, hx]
  omega

#print axioms transverse_link_mem_boxR

/-- The plaquette `((τ, ν), x)` with `x τ = p` is in `iplqPlus τ p Λ`, given that its links are in
`Λ`.
Its first direction is `τ`, so the transverse-at-the-plane exclusion in `mem_iplqPlus` does not
fire,
and `p ≤ x τ` holds with equality.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iplqPlus_mem_of_tau_base (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ)
    (x : MassGap.GibbsSpec.ISite) (hx : x τ = p)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (hΛ : ∀ l ∈ MassGap.GibbsSpec.ilinks (((τ, ν), x) : MassGap.GibbsSpec.IPlaq), l ∈ Λ) :
    (((τ, ν), x) : MassGap.GibbsSpec.IPlaq) ∈ iplqPlus τ p Λ := by
  refine mem_iplqPlus.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr hΛ, Ne.symm hν, ?_, le_of_eq hx.symm⟩
  rintro ⟨hne, -, -⟩
  exact hne rfl

#print axioms iplqPlus_mem_of_tau_base

/-- An `iplqPlus` plaquette that has a link in `boxR`: `((τ, ν), x)` with `x τ = p` is in `iplqPlus
τ p Λ`
and its transverse link `(ν, x)` lies in the shared block. `iplqPlus_links_mem` bounds the
half-action's links by `boxS ∪ boxR`, and a half-action reading only `boxS` would satisfy that
bound; this exhibits the other case. The statement is about which links a plaquette reads, not about
how `iactPlus` varies with them.

DERIVED: the signature writes no numeral; the `2` of the reflection constant sits inside `boxR`, and
`4` is the dimension. -/
theorem iplqPlus_has_link_in_boxR (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ)
    (x : MassGap.GibbsSpec.ISite) (hx : x τ = p)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (hΛ : ∀ l ∈ MassGap.GibbsSpec.ilinks (((τ, ν), x) : MassGap.GibbsSpec.IPlaq), l ∈ Λ) :
    (((τ, ν), x) : MassGap.GibbsSpec.IPlaq) ∈ iplqPlus τ p Λ ∧
      ∃ l : ↥Λ, l ∈ boxR τ p Λ ∧
        l.1 ∈ MassGap.GibbsSpec.ilinks (((τ, ν), x) : MassGap.GibbsSpec.IPlaq) := by
  have hmem : ((ν, x) : MassGap.InfiniteLattice.ILink) ∈
      MassGap.GibbsSpec.ilinks (((τ, ν), x) : MassGap.GibbsSpec.IPlaq) := by
    rw [MassGap.GibbsSpec.ilinks_eq]
    simp
  exact ⟨iplqPlus_mem_of_tau_base τ ν hν p x hx Λ hΛ,
    ⟨(ν, x), hΛ _ hmem⟩, transverse_link_mem_boxR τ ν hν p x hx Λ (hΛ _ hmem), hmem⟩

#print axioms iplqPlus_has_link_in_boxR

/-- Shifts in distinct directions send a site to distinct sites.

DERIVED: the signature writes no numeral; `1` is `ishift`'s step, inside `ishift_coord`; `4` is the
dimension. -/
theorem ishift_ne_ishift {μ ν : Fin 4} (h : μ ≠ ν) (x : MassGap.GibbsSpec.ISite) :
    MassGap.GibbsSpec.ishift μ x ≠ MassGap.GibbsSpec.ishift ν x := by
  intro he
  have hc := congrFun he μ
  rw [ishift_coord, ishift_coord, if_pos rfl, if_neg (Ne.symm h)] at hc
  omega

#print axioms ishift_ne_ishift

/-- A shift moves the site: `GibbsSpec.ishift μ x ≠ x`.

DERIVED: the signature writes no numeral; `1` is `ishift`'s step, inside `ishift_coord`; `4` is the
dimension. -/
theorem ishift_ne_self (μ : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    MassGap.GibbsSpec.ishift μ x ≠ x := by
  intro he
  have hc := congrFun he μ
  rw [ishift_coord, if_pos rfl] at hc
  omega

#print axioms ishift_ne_self

/-- The four links of the plaquette at `x` spanned by `τ` and `ν`, as a `Finset ILink` in its own
right —
the one-plaquette carrier the lemmas below run on.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def quadLinks (τ ν : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    Finset MassGap.InfiniteLattice.ILink :=
  {(τ, x), (ν, MassGap.GibbsSpec.ishift τ x), (τ, MassGap.GibbsSpec.ishift ν x), (ν, x)}

/-- Every link of `((τ, ν), x)` lies in `quadLinks τ ν x`. A containment, not an equality of lists.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem quadLinks_ilinks (τ ν : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    ∀ l ∈ MassGap.GibbsSpec.ilinks (((τ, ν), x) : MassGap.GibbsSpec.IPlaq),
      l ∈ quadLinks τ ν x := by
  intro l hl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [quadLinks, List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

#print axioms quadLinks_ilinks

/-- The same for the reversed orientation `((ν, τ), x)`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem quadLinks_ilinks_swap (τ ν : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    ∀ l ∈ MassGap.GibbsSpec.ilinks (((ν, τ), x) : MassGap.GibbsSpec.IPlaq),
      l ∈ quadLinks τ ν x := by
  intro l hl
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  simp only [quadLinks, Finset.mem_insert, Finset.mem_singleton]
  tauto

#print axioms quadLinks_ilinks_swap

/-- If two links of `quadLinks τ ν x` share a base `y` and have distinct directions, then `y = x`.
In
`quadLinks`, `x` is the only base carrying two directions; `ishift τ x` and `ishift ν x` carry one
each and are distinct by `ishift_ne_ishift`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem quad_two_dirs (τ ν : Fin 4) (hν : ν ≠ τ) (x y : MassGap.GibbsSpec.ISite)
    {a b : Fin 4} (hab : a ≠ b)
    (ha : ((a, y) : MassGap.InfiniteLattice.ILink) ∈ quadLinks τ ν x)
    (hb : ((b, y) : MassGap.InfiniteLattice.ILink) ∈ quadLinks τ ν x) :
    y = x := by
  simp only [quadLinks, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at ha hb
  rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
  · exact ha2
  · rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · exact hb2
    · exact absurd (ha1.trans hb1.symm) hab
    · exact absurd (ha2.symm.trans hb2) (ishift_ne_ishift (Ne.symm hν) x)
    · exact hb2
  · rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · exact hb2
    · exact absurd (ha2.symm.trans hb2) (ishift_ne_ishift hν x)
    · exact absurd (ha1.trans hb1.symm) hab
    · exact hb2
  · exact ha2

#print axioms quad_two_dirs

/-- A link of `quadLinks τ ν x` based at `x` has direction `τ` or `ν`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem quad_dirs (τ ν : Fin 4) (x : MassGap.GibbsSpec.ISite) {a : Fin 4}
    (ha : ((a, x) : MassGap.InfiniteLattice.ILink) ∈ quadLinks τ ν x) : a = τ ∨ a = ν := by
  simp only [quadLinks, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at ha
  tauto

#print axioms quad_dirs

/-- On the one-plaquette carrier, `iplqPlus τ p (quadLinks τ ν x)` is exactly the two orientations
`{((τ, ν), x), ((ν, τ), x)}`, for `x τ = p` and `ν ≠ τ`. The half-action on this carrier is
therefore
a two-term sum.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iplqPlus_quad_eq (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ)
    (x : MassGap.GibbsSpec.ISite) (hx : x τ = p) :
    iplqPlus τ p (quadLinks τ ν x)
      = {(((τ, ν), x) : MassGap.GibbsSpec.IPlaq), (((ν, τ), x) : MassGap.GibbsSpec.IPlaq)} := by
  ext q
  obtain ⟨⟨a, b⟩, y⟩ := q
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro hq
    obtain ⟨hin, hne, -, -⟩ := mem_iplqPlus.mp hq
    have hml := MassGap.GibbsSpec.mem_plaqsIn.mp hin
    have hA : ((a, y) : MassGap.InfiniteLattice.ILink) ∈ quadLinks τ ν x := by
      refine hml _ ?_
      rw [MassGap.GibbsSpec.ilinks_eq]
      simp
    have hB : ((b, y) : MassGap.InfiniteLattice.ILink) ∈ quadLinks τ ν x := by
      refine hml _ ?_
      rw [MassGap.GibbsSpec.ilinks_eq]
      simp
    have hy : y = x := quad_two_dirs τ ν hν x y hne hA hB
    subst hy
    rcases quad_dirs τ ν y hA with ha | ha <;> rcases quad_dirs τ ν y hB with hb | hb
    · exact absurd (ha.trans hb.symm) hne
    · exact Or.inl ⟨⟨ha, hb⟩, rfl⟩
    · exact Or.inr ⟨⟨ha, hb⟩, rfl⟩
    · exact absurd (ha.trans hb.symm) hne
  · intro h
    refine mem_iplqPlus.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr ?_, ?_, ?_, ?_⟩
    · rcases h with ⟨⟨ha, hb⟩, hy⟩ | ⟨⟨ha, hb⟩, hy⟩ <;> subst ha <;> subst hb <;> subst hy
      · exact quadLinks_ilinks _ _ _
      · exact quadLinks_ilinks_swap _ _ _
    · rcases h with ⟨⟨ha, hb⟩, -⟩ | ⟨⟨ha, hb⟩, -⟩ <;> subst ha <;> subst hb
      · exact Ne.symm hν
      · exact hν
    · rcases h with ⟨⟨ha, hb⟩, -⟩ | ⟨⟨ha, hb⟩, -⟩ <;> subst ha <;> subst hb
      · rintro ⟨hc, -, -⟩
        exact hc rfl
      · rintro ⟨-, hc, -⟩
        exact hc rfl
    · rcases h with ⟨-, hy⟩ | ⟨-, hy⟩ <;> subst hy <;> exact le_of_eq hx.symm

#print axioms iplqPlus_quad_eq

end HalfPlaq

/-! ## 3d″a. The three groups partition the box -/

section Partition

open MassGap.LatticeReflection

theorem mem_iplqZero {τ : Fin 4} {p : ℤ} {Λ : Finset MassGap.InfiniteLattice.ILink}
    {q : MassGap.GibbsSpec.IPlaq} :
    q ∈ iplqZero τ p Λ ↔
      q ∈ MassGap.GibbsSpec.plaqsIn Λ ∧ q.1.1 ≠ q.1.2 ∧
        (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p) := by
  simp only [iplqZero, Finset.mem_filter]

#print axioms mem_iplqZero

theorem iplqZero_disjoint_iplqPlus (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (iplqZero τ p Λ) (iplqPlus τ p Λ) := by
  refine Finset.disjoint_left.2 fun q hZ hP => ?_
  exact (mem_iplqPlus.mp hP).2.2.1 (mem_iplqZero.mp hZ).2.2

theorem iplqZero_disjoint_iplqMinus (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (iplqZero τ p Λ) (iplqMinus τ p Λ) := by
  refine Finset.disjoint_left.2 fun q hZ hM => ?_
  exact (mem_iplqMinus.mp hM).2.2.1 (mem_iplqZero.mp hZ).2.2

/-- The three groups partition the box's plaquettes:
`iplqZero ∪ iplqPlus ∪ iplqMinus = iplqAll`. Every non-degenerate plaquette of the box is in the
plane, above it, or below it, and in exactly one of the three — disjointness is
`iplqZero_disjoint_iplqPlus`, `iplqZero_disjoint_iplqMinus` and `iplqPlus_disjoint_iplqMinus`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iplq_union (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    iplqZero τ p Λ ∪ iplqPlus τ p Λ ∪ iplqMinus τ p Λ = iplqAll Λ := by
  ext q
  simp only [Finset.mem_union, mem_iplqZero, mem_iplqPlus, mem_iplqMinus, mem_iplqAll]
  constructor
  · rintro ((⟨h, hne, -⟩ | ⟨h, hne, -⟩) | ⟨h, hne, -⟩) <;> exact ⟨h, hne⟩
  · rintro ⟨h, hne⟩
    by_cases hz : q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ q.2 τ = p
    · exact Or.inl (Or.inl ⟨h, hne, hz⟩)
    · by_cases hge : p ≤ q.2 τ
      · exact Or.inl (Or.inr ⟨h, hne, hz, hge⟩)
      · exact Or.inr ⟨h, hne, hz, not_le.mp hge⟩

#print axioms iplq_union

/-- The action over `iplqAll Λ` splits into a plane part and the two halves:
`actionOn φ (iplqAll Λ) U = actionOn φ (iplqZero τ p Λ) U + actionOn φ (iplqPlus τ p Λ) U
+ actionOn φ (iplqMinus τ p Λ) U`, by `iplq_union` and the disjointness lemmas. With
`action_iplqPlus_ireflConf` this gives
`exp(-βS) = exp(-βA₀) · exp(-βA₊(U)) · exp(-βA₊(ΘU))`: a weight reading the shared block only, times
an observable times its own reflection, which is the shape
`ActionSplit.pairing_nonneg_of_local` consumes. Holds for any `φ : G → ℝ`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem actionOn_split_three {G : Type} [Group G] (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U
      = MassGap.GibbsSpec.actionOn φ (iplqZero τ p Λ) U
        + MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ) U
        + MassGap.GibbsSpec.actionOn φ (iplqMinus τ p Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  rw [← iplq_union τ p Λ,
    Finset.sum_union (Finset.disjoint_union_left.2
      ⟨iplqZero_disjoint_iplqMinus τ p Λ, iplqPlus_disjoint_iplqMinus τ p Λ⟩),
    Finset.sum_union (iplqZero_disjoint_iplqPlus τ p Λ)]

#print axioms actionOn_split_three

end Partition

/-! ## 3d‴a. The reflection is a bijection between the two halves -/

section Bijection

open MassGap.LatticeReflection

/-- The mirror of `ireflPlaq_mem_iplqMinus`: the reflection at `2 * p` carries `iplqMinus τ p Λ`
into
`iplqPlus τ p Λ`, given the image is in `plaqsIn Λ`. The action identity reindexes a sum, which
needs
a bijection rather than a map in one direction.

The transverse branch needs no off-plane hypothesis here: below the plane `x_τ < p` already forces
`2p - x_τ > p`, so the image cannot land on the plane.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`, the `1` is `ireflPlaq`'s
link-length offset, and `4` is the dimension. -/
theorem ireflPlaq_mem_iplqPlus (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqMinus τ p Λ)
    (hmem : ireflPlaq τ (2 * p) q ∈ MassGap.GibbsSpec.plaqsIn Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqPlus τ p Λ := by
  obtain ⟨_, hne, _, hlt⟩ := mem_iplqMinus.mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hne hlt
  rw [mem_iplqPlus]
  by_cases hμ : μ = τ
  · subst hμ
    refine ⟨hmem, ?_, ?_, ?_⟩
    · simpa [ireflPlaq] using fun h => hne h.symm
    · simp [ireflPlaq]
    · simp only [ireflPlaq, ireflSite_axis, reduceIte]
      omega
  · by_cases hν : ν = τ
    · subst hν
      refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ] using fun h => hμ h.symm
      · simp [ireflPlaq, hμ]
      · simp only [ireflPlaq, if_neg hμ, ireflSite_axis, reduceIte]
        omega
    · refine ⟨hmem, ?_, ?_, ?_⟩
      · simpa [ireflPlaq, hμ, hν] using hne
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        rintro ⟨-, -, hz⟩
        omega
      · simp only [ireflPlaq, if_neg hμ, if_neg hν, ireflSite_axis]
        omega

#print axioms ireflPlaq_mem_iplqPlus

/-- The negative half maps back into the positive one with no leftover hypothesis, on the same `hΛ`
as
`ireflPlaq_maps_plus_to_minus`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; `4` is the dimension. -/
theorem ireflPlaq_maps_minus_to_plus (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqMinus τ p Λ) :
    ireflPlaq τ (2 * p) q ∈ iplqPlus τ p Λ :=
  ireflPlaq_mem_iplqPlus τ p Λ hq
    (ireflPlaq_mem_plaqsIn τ (2 * p) hΛ
      (fun h => (mem_iplqMinus.mp hq).2.1 (h.1.trans h.2.symm)) (mem_iplqMinus.mp hq).1)

#print axioms ireflPlaq_maps_minus_to_plus

end Bijection

/-! ## 3d‴b. The reflected positive half-action is the negative half-action -/

section Covariance

open MassGap.LatticeReflection MassGap.WilsonLattice

variable {G : Type} [Group G]

/-- `GibbsSpec.ihol q U` is `WilsonLattice.wilsonHol InfiniteLattice.ibd q U`, by `rfl`, so
`GibbsSpec.ihol` is the holonomy `ihol_ireflConf` speaks about. The same import-isolation bridge as
`gibbs_ishift_eq`: identical bodies in two isolated namespaces are still two constants.

DERIVED: the signature writes no numeral; `4` is the dimension carried by `IPlaq` and `IConf`. -/
theorem gibbs_ihol_eq (q : MassGap.GibbsSpec.IPlaq) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.ihol q U = wilsonHol MassGap.InfiniteLattice.ibd q U := rfl

#print axioms gibbs_ihol_eq

/-- The positive half-action at the reflected configuration equals the negative half-action at the
original: `actionOn φ (iplqPlus τ p Λ) (ireflConf τ (2 * p) U) = actionOn φ (iplqMinus τ p Λ) U`.
With `actionOn_split_three` this makes `exp(-βS)` factor as `w(U|R) · h(U) · h(ΘU)`, the shape
`ActionSplit.pairing_nonneg_of_local` consumes; the `ℤ⁴` counterpart of
`ActionSplit.sum_plqMinus_eq_plus_refl`.

It does not go through a `LatticeGauge.Symmetry`: the mirrored holonomy is only conjugate to the
image plaquette's, which is what `ihol_ireflConf` gives. The sum is carried by the hypothesis `hφ`
that `φ` is a class function — true of the Wilson density by `WilsonAction.wilsonDensity_conj` —
together with `ireflPlaq` being a bijection `iplqPlus ↔ iplqMinus` on a reflection-stable box.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; `4` is the dimension. -/
theorem action_iplqPlus_ireflConf (φ : G → ℝ) (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h)
    (τ : Fin 4) (p : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ) (ireflConf τ (2 * p) U)
      = MassGap.GibbsSpec.actionOn φ (iplqMinus τ p Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ (2 * p) q)
    (j := fun q => ireflPlaq τ (2 * p) q)
    (fun a ha => ireflPlaq_maps_plus_to_minus τ p hΛ ha)
    (fun b hb => ireflPlaq_maps_minus_to_plus τ p hΛ hb)
    (fun a _ => ireflPlaq_involutive τ (2 * p) a)
    (fun b _ => ireflPlaq_involutive τ (2 * p) b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ (2 * p) a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms action_iplqPlus_ireflConf

/-- The reflection preserves non-degeneracy, so it maps `iplqAll Λ` into itself on a stable box. At
`μ = τ` the image plane is `(ν, τ)` with `ν ≠ τ`; at `ν = τ` it is `(τ, μ)` with `μ ≠ τ`; otherwise
it is `(μ, ν)` unchanged. Stated at an arbitrary constant `c`.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. -/
theorem ireflPlaq_mem_iplqAll (τ : Fin 4) (c : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) : ireflPlaq τ c q ∈ iplqAll Λ := by
  obtain ⟨hin, hne⟩ := mem_iplqAll.mp hq
  refine mem_iplqAll.mpr ⟨ireflPlaq_mem_plaqsIn τ c hΛ
    (fun h => hne (h.1.trans h.2.symm)) hin, ?_⟩
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hne
  by_cases hμ : μ = τ
  · subst hμ
    simpa [ireflPlaq] using fun h => hne h.symm
  · by_cases hν : ν = τ
    · subst hν
      simpa [ireflPlaq, hμ] using fun h => hμ h.symm
    · simpa [ireflPlaq, hμ, hν] using hne

#print axioms ireflPlaq_mem_iplqAll

/-- The full action over `iplqAll Λ` is invariant under the reflection at any constant `c`, for a
class
function `φ` on a reflection-stable box. The same three ingredients as
`action_iplqPlus_ireflConf` — `ihol_ireflConf`, `hφ`, and `ireflPlaq` a bijection of the index set,
which here it is of `iplqAll` with itself by `ireflPlaq_mem_iplqAll` and involutivity.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. -/
theorem action_iplqAll_ireflConf (φ : G → ℝ) (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h)
    (τ : Fin 4) (c : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_mem_iplqAll τ c hΛ ha)
    (fun b hb => ireflPlaq_mem_iplqAll τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms action_iplqAll_ireflConf

end Covariance

/-! ## 3d‴. The half-action at a box, and its Boltzmann factor -/

section HalfAction

open MassGap.LatticeReflection

variable {G : Type} [Group G]

/-- The positive half-action at a box: the action `φ` summed over `iplqPlus τ p Λ`, read off a
finite-volume configuration `u` spliced into a background `ω`.

The background is inert — every plaquette summed over has all four links inside `Λ` by
`iplqPlus_link_mem_box`, so `splice` never consults `ω`. It is carried rather than fixed because
`GibbsSpec.actionOn` is stated on `IConf G` while the finite-volume configuration lives on `↥Λ`.

DERIVED: the signature writes no numeral; `φ`, `τ`, `p`, `Λ` and `ω` are the caller's, and `4` is
the dimension. -/
noncomputable def iactPlus (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ) (MassGap.GibbsSpec.splice Λ u ω)

/-- `iactPlus` depends on the configuration only through `boxS ∪ boxR`: two configurations agreeing
on
`boxS` and on `boxR` give the same value. The `ℤ⁴` counterpart of `ReflectionStrong.actPlus_local`,
and what lets the half Boltzmann factor be absorbed into the observable.

The two hypotheses are kept apart rather than merged over the union because this is the shape of
`hOloc` in `ActionSplit.pairing_nonneg_of_local`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iactPlus_local (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ)
    (hS : ∀ l ∈ boxS τ p Λ, u l = v l) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    iactPlus φ τ p Λ ω u = iactPlus φ τ p Λ ω v := by
  refine MassGap.GibbsSpec.actionOn_congr φ _ _ _ (fun q hq l hl => ?_)
  have hlΛ : l ∈ Λ := iplqPlus_link_mem_box τ p Λ hq hl
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
  rcases Finset.mem_union.mp (iplqPlus_links_mem τ p Λ hq hl hlΛ) with h | h
  · exact hS _ h
  · exact hR _ h

#print axioms iactPlus_local

/-- On the one-plaquette carrier `quadLinks τ ν x` with `x τ = p`, the half-action is the two-term
sum
over the orientations `((τ, ν), x)` and `((ν, τ), x)` — `iplqPlus_quad_eq` summed by
`Finset.sum_pair`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iactPlus_quad (φ : G → ℝ) (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ)
    (x : MassGap.GibbsSpec.ISite) (hx : x τ = p)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G (quadLinks τ ν x)) :
    iactPlus φ τ p (quadLinks τ ν x) ω u
      = φ (MassGap.GibbsSpec.ihol (((τ, ν), x) : MassGap.GibbsSpec.IPlaq)
            (MassGap.GibbsSpec.splice (quadLinks τ ν x) u ω))
        + φ (MassGap.GibbsSpec.ihol (((ν, τ), x) : MassGap.GibbsSpec.IPlaq)
            (MassGap.GibbsSpec.splice (quadLinks τ ν x) u ω)) := by
  have hne2 : (((τ, ν), x) : MassGap.GibbsSpec.IPlaq)
      ≠ (((ν, τ), x) : MassGap.GibbsSpec.IPlaq) := by
    intro h
    exact (Ne.symm hν) (congrArg (fun q : MassGap.GibbsSpec.IPlaq => q.1.1) h)
  unfold iactPlus MassGap.GibbsSpec.actionOn
  rw [iplqPlus_quad_eq τ ν hν p x hx, Finset.sum_pair hne2]

#print axioms iactPlus_quad

/-- On the one-plaquette carrier there are two configurations agreeing off `boxR` at which
`iactPlus`
differs. `iplqPlus_has_link_in_boxR` shows the half-action reads `boxR`; this shows it varies with
it. On `quadLinks τ ν x` the only `boxR` link is `(ν, x)`; the two orientations give `g⁻¹` and `g`,
and the all-identity configuration gives `1` and `1`.

Scope: `hsep : φ g + φ g⁻¹ ≠ 2 * φ 1` is unsatisfiable in the trivial group, so it carries a
non-triviality assumption on `G`, and with it excludes `SU 0` and `SU 1`. The carrier is a single
plaquette and is not closed under the reflection.

DERIVED: the `2` is the two orientations, one per term of `iactPlus_quad`; the `1`s are the identity
configuration and its two holonomies; `4` is the dimension. -/
theorem iactPlus_depends_on_boxR (φ : G → ℝ) (τ ν : Fin 4) (hν : ν ≠ τ)
    (p : ℤ) (x : MassGap.GibbsSpec.ISite) (hx : x τ = p)
    (ω : MassGap.GibbsSpec.IConf G) (g : G) (hsep : φ g + φ g⁻¹ ≠ 2 * φ 1) :
    ∃ u u' : MassGap.GibbsSpec.VConf G (quadLinks τ ν x),
      (∀ l : ↥(quadLinks τ ν x), l ∉ boxR τ p (quadLinks τ ν x) → u l = u' l) ∧
        iactPlus φ τ p (quadLinks τ ν x) ω u
          ≠ iactPlus φ τ p (quadLinks τ ν x) ω u' := by
  classical
  have m1 : ((τ, x) : MassGap.InfiniteLattice.ILink) ∈ quadLinks τ ν x := by simp [quadLinks]
  have m2 : ((ν, MassGap.GibbsSpec.ishift τ x) : MassGap.InfiniteLattice.ILink)
      ∈ quadLinks τ ν x := by simp [quadLinks]
  have m3 : ((τ, MassGap.GibbsSpec.ishift ν x) : MassGap.InfiniteLattice.ILink)
      ∈ quadLinks τ ν x := by simp [quadLinks]
  have m4 : ((ν, x) : MassGap.InfiniteLattice.ILink) ∈ quadLinks τ ν x := by simp [quadLinks]
  refine ⟨fun l => if (l : MassGap.InfiniteLattice.ILink) = ((ν, x) : _) then g else 1,
    fun _ => 1, ?_, ?_⟩
  · intro l hl
    by_cases he : (l : MassGap.InfiniteLattice.ILink) = ((ν, x) : _)
    · exfalso
      apply hl
      have hle : l = (⟨(ν, x), m4⟩ : ↥(quadLinks τ ν x)) := Subtype.ext he
      rw [hle]
      exact transverse_link_mem_boxR τ ν hν p x hx _ m4
    · simp [he]
  · rw [iactPlus_quad φ τ ν hν p x hx ω, iactPlus_quad φ τ ν hν p x hx ω]
    simp [MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd,
      MassGap.GibbsSpec.splice_mem m1, MassGap.GibbsSpec.splice_mem m2,
      MassGap.GibbsSpec.splice_mem m3, MassGap.GibbsSpec.splice_mem m4,
      Ne.symm hν, ishift_ne_self τ x, ishift_ne_self ν x]
    intro h
    apply hsep
    linarith

#print axioms iactPlus_depends_on_boxR

/-- The half-space Boltzmann factor at a box, `exp (-β * iactPlus φ τ p Λ ω u)` —
`ReflectionStrong.halfBoltz` on `ℤ⁴`.

DERIVED: the sign is the Gibbs convention `e^{-β S}` and `β` is the caller's; `4` is the dimension.
-/
noncomputable def ihalfBoltz (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  Real.exp (-β * iactPlus φ τ p Λ ω u)

/-- The half Boltzmann factor depends on the configuration only through `boxS ∪ boxR`: `exp` of
`iactPlus_local`. Again in `hOloc`'s shape, with the two blocks as separate hypotheses.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem ihalfBoltz_local (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ)
    (hS : ∀ l ∈ boxS τ p Λ, u l = v l) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    ihalfBoltz φ β τ p Λ ω u = ihalfBoltz φ β τ p Λ ω v := by
  simp only [ihalfBoltz, iactPlus_local φ τ p Λ ω u v hS hR]

#print axioms ihalfBoltz_local

/-- The half Boltzmann factor is strictly positive, at every `φ`, `β`, box and configuration — it is
an
exponential. This is what keeps the dressing from collapsing an observable to zero, and is `hWnn`
for a plane weight built the same way.

DERIVED: the `0` is the lower bound of the strict inequality; `4` is the dimension. -/
theorem ihalfBoltz_pos (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    0 < ihalfBoltz φ β τ p Λ ω u :=
  Real.exp_pos _

#print axioms ihalfBoltz_pos

/-- `|iactPlus φ τ p Λ ω u| ≤ (iplqPlus τ p Λ).card * Cφ` for any uniform bound `Cφ` on `|φ|`: the
plaquette count times the density bound. The bound depends on the box through the cardinality.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem abs_iactPlus_le (φ : G → ℝ) {Cφ : ℝ} (hφ : ∀ g, |φ g| ≤ Cφ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    |iactPlus φ τ p Λ ω u| ≤ (iplqPlus τ p Λ).card * Cφ := by
  unfold iactPlus MassGap.GibbsSpec.actionOn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun q _ => hφ _)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

#print axioms abs_iactPlus_le

/-- A lower bound on the dressing that does not depend on the configuration:
`exp (-(|β| * ((iplqPlus τ p Λ).card * Cφ))) ≤ ihalfBoltz φ β τ p Λ ω u`, from `abs_iactPlus_le`.
`ActionSplit.le_halfIntegral` requires a constant of this kind; `ihalfBoltz_pos` is pointwise and
supplies none.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem ihalfBoltz_lower_bound (φ : G → ℝ) {Cφ : ℝ} (hφ : ∀ g, |φ g| ≤ Cφ) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    Real.exp (-(|β| * ((iplqPlus τ p Λ).card * Cφ))) ≤ ihalfBoltz φ β τ p Λ ω u := by
  have hC : (0 : ℝ) ≤ Cφ := le_trans (abs_nonneg _) (hφ 1)
  have hcard : (0 : ℝ) ≤ (iplqPlus τ p Λ).card * Cφ :=
    mul_nonneg (Nat.cast_nonneg _) hC
  have hA := abs_iactPlus_le φ hφ τ p Λ ω u
  have hb : β * iactPlus φ τ p Λ ω u ≤ |β| * ((iplqPlus τ p Λ).card * Cφ) := by
    refine le_trans (le_abs_self _) ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hA (abs_nonneg β)
  unfold ihalfBoltz
  exact Real.exp_le_exp.mpr (by linarith)

#print axioms ihalfBoltz_lower_bound

/-- The matching upper bound, `|ihalfBoltz φ β τ p Λ ω u| ≤ exp (|β| * ((iplqPlus τ p Λ).card *
Cφ))`,
also from `abs_iactPlus_le`, and also required by `ActionSplit.le_halfIntegral`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem ihalfBoltz_upper_bound (φ : G → ℝ) {Cφ : ℝ} (hφ : ∀ g, |φ g| ≤ Cφ) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    |ihalfBoltz φ β τ p Λ ω u| ≤ Real.exp (|β| * ((iplqPlus τ p Λ).card * Cφ)) := by
  have hA := abs_iactPlus_le φ hφ τ p Λ ω u
  have hb : -β * iactPlus φ τ p Λ ω u ≤ |β| * ((iplqPlus τ p Λ).card * Cφ) := by
    refine le_trans (le_abs_self _) ?_
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hA (abs_nonneg β)
  rw [abs_of_pos (ihalfBoltz_pos φ β τ p Λ ω u)]
  unfold ihalfBoltz
  exact Real.exp_le_exp.mpr hb

#print axioms ihalfBoltz_upper_bound

/-- The dressed observable, `fun u => F u * ihalfBoltz φ β τ p Λ ω u` — the map that carries the
Gibbs
pairing to the split pairing on `ℤ⁴`, as `ReflectionStrong.dressed` does on the torus.

DERIVED: the signature writes no numeral; the product is the dressing and `4` is the dimension. -/
noncomputable def idressed (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (F : MassGap.GibbsSpec.VConf G Λ → ℝ) : MassGap.GibbsSpec.VConf G Λ → ℝ :=
  fun u => F u * ihalfBoltz φ β τ p Λ ω u

/-- The dressed observable reads `boxS ∪ boxR` whenever the bare one does — `hOloc` for `idressed`
given
`hOloc` for `F`. The locality half of `ReflectionStrong.dressed_mem`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem idressed_local (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    {F : MassGap.GibbsSpec.VConf G Λ → ℝ}
    (hF : ∀ u v : MassGap.GibbsSpec.VConf G Λ, (∀ l ∈ boxS τ p Λ, u l = v l) →
      (∀ l ∈ boxR τ p Λ, u l = v l) → F u = F v)
    (u v : MassGap.GibbsSpec.VConf G Λ)
    (hS : ∀ l ∈ boxS τ p Λ, u l = v l) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    idressed φ β τ p Λ ω F u = idressed φ β τ p Λ ω F v := by
  simp only [idressed, hF u v hS hR, ihalfBoltz_local φ β τ p Λ ω u v hS hR]

#print axioms idressed_local

/-- At every non-zero coupling the half Boltzmann factor also varies with `boxR`, on the
one-plaquette
carrier: `exp` is injective and the factor `-β` cancels, so `iactPlus_depends_on_boxR` transfers.

DERIVED: the `0` is the coupling excluded by `hβ`; the `2` and the `1`s are `hsep`'s, as in
`iactPlus_depends_on_boxR`; `4` is the dimension. -/
theorem ihalfBoltz_depends_on_boxR (φ : G → ℝ) (β : ℝ) (hβ : β ≠ 0) (τ ν : Fin 4) (hν : ν ≠ τ)
    (p : ℤ) (x : MassGap.GibbsSpec.ISite) (hx : x τ = p)
    (ω : MassGap.GibbsSpec.IConf G) (g : G) (hsep : φ g + φ g⁻¹ ≠ 2 * φ 1) :
    ∃ u u' : MassGap.GibbsSpec.VConf G (quadLinks τ ν x),
      (∀ l : ↥(quadLinks τ ν x), l ∉ boxR τ p (quadLinks τ ν x) → u l = u' l) ∧
        ihalfBoltz φ β τ p (quadLinks τ ν x) ω u
          ≠ ihalfBoltz φ β τ p (quadLinks τ ν x) ω u' := by
  obtain ⟨u, u', hagree, hne⟩ := iactPlus_depends_on_boxR φ τ ν hν p x hx ω g hsep
  refine ⟨u, u', hagree, ?_⟩
  intro h
  simp only [ihalfBoltz] at h
  exact hne (mul_left_cancel₀ (neg_ne_zero.mpr hβ) (Real.exp_eq_exp.mp h))

#print axioms ihalfBoltz_depends_on_boxR

/-- With the constant bare observable `F ≡ 1` the dressed observable varies with `boxR`, at every
non-zero coupling, on the one-plaquette carrier. `ActionSplit.pairing_eq_zero_of_indep_R`'s `hOS`
asks the observable not to depend on the shared block, and the dressing alone breaks that: the
dressed observable is then the half Boltzmann factor, which differs at two configurations agreeing
off `boxR`.

Scope: the carrier `quadLinks τ ν x` is a single plaquette and is not closed under the reflection.

DERIVED: the `1` is the constant bare observable; the `0` is the coupling excluded by `hβ`; the `2`
and the remaining `1`s are `hsep`'s; `4` is the dimension. -/
theorem idressed_depends_on_boxR (φ : G → ℝ) (β : ℝ) (hβ : β ≠ 0) (τ ν : Fin 4) (hν : ν ≠ τ)
    (p : ℤ) (x : MassGap.GibbsSpec.ISite) (hx : x τ = p)
    (ω : MassGap.GibbsSpec.IConf G) (g : G) (hsep : φ g + φ g⁻¹ ≠ 2 * φ 1) :
    ∃ u u' : MassGap.GibbsSpec.VConf G (quadLinks τ ν x),
      (∀ l : ↥(quadLinks τ ν x), l ∉ boxR τ p (quadLinks τ ν x) → u l = u' l) ∧
        idressed φ β τ p (quadLinks τ ν x) ω (fun _ => 1) u
          ≠ idressed φ β τ p (quadLinks τ ν x) ω (fun _ => 1) u' := by
  obtain ⟨u, u', hagree, hne⟩ := ihalfBoltz_depends_on_boxR φ β hβ τ ν hν p x hx ω g hsep
  refine ⟨u, u', hagree, ?_⟩
  simpa [idressed] using hne

#print axioms idressed_depends_on_boxR

end HalfAction

/-! ## 3d‴c. The plane weight, which reads the shared block only -/

section PlaneWeight

open MassGap.LatticeReflection

/-- The links of a plane plaquette lie in the box, read off the `plaqsIn` filter inside `iplqZero`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iplqZero_link_mem_box (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqZero τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) : l ∈ Λ :=
  MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqZero.mp hq).1 l hl

/-- Every link of a plane plaquette lies in `boxR τ p Λ`, so the whole group sits in the shared
block —
what makes the plane weight a `hWloc` weight. Both spanning directions are transverse to `τ`, so no
link points along `τ` and neither `ishift μ` nor `ishift ν` moves the `τ` coordinate; all four links
therefore sit at the plane, where a transverse link is fixed.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`, inside `boxR`; `4` is the
dimension. -/
theorem iplqZero_links_mem (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    {q : MassGap.GibbsSpec.IPlaq} (hq : q ∈ iplqZero τ p Λ)
    {l : MassGap.InfiniteLattice.ILink} (hl : l ∈ MassGap.GibbsSpec.ilinks q) (h : l ∈ Λ) :
    (⟨l, h⟩ : ↥Λ) ∈ boxR τ p Λ := by
  obtain ⟨_, _, hμ, hν, hx⟩ := mem_iplqZero.mp hq
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  simp only at hμ hν hx
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [irefl_coord, ishift_coord, hμ, hν, if_false] <;> omega

#print axioms iplqZero_links_mem

variable {G : Type} [Group G]

/-- The plane action at a box: `φ` summed over `iplqZero τ p Λ` alone, at the spliced configuration.

DERIVED: the signature writes no numeral; `φ`, `τ`, `p`, `Λ` and `ω` are the caller's, and `4` is
the dimension. -/
noncomputable def iactZero (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  MassGap.GibbsSpec.actionOn φ (iplqZero τ p Λ) (MassGap.GibbsSpec.splice Λ u ω)

/-- The plane action depends on the configuration only through `boxR` — one hypothesis, over the
shared
block and nothing else, which is `hWloc`'s shape.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iactZero_local (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    iactZero φ τ p Λ ω u = iactZero φ τ p Λ ω v := by
  refine MassGap.GibbsSpec.actionOn_congr φ _ _ _ (fun q hq l hl => ?_)
  have hlΛ : l ∈ Λ := iplqZero_link_mem_box τ p Λ hq hl
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
  exact hR _ (iplqZero_links_mem τ p Λ hq hl hlΛ)

#print axioms iactZero_local

/-- The plane weight, `exp (-β * iactZero φ τ p Λ ω u)` — the `W` of
`ActionSplit.pairing_nonneg_of_local` on `ℤ⁴`.

DERIVED: the sign is the Gibbs convention `e^{-β S}` and `β` is the caller's; `4` is the dimension.
-/
noncomputable def iplaneWeight (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  Real.exp (-β * iactZero φ τ p Λ ω u)

/-- `hWloc` for the plane weight: it depends on the configuration only through `boxR`, by `exp` of
`iactZero_local`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem iplaneWeight_local (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u v : MassGap.GibbsSpec.VConf G Λ) (hR : ∀ l ∈ boxR τ p Λ, u l = v l) :
    iplaneWeight φ β τ p Λ ω u = iplaneWeight φ β τ p Λ ω v := by
  simp only [iplaneWeight, iactZero_local φ τ p Λ ω u v hR]

/-- `hWnn` for the plane weight: `0 ≤ iplaneWeight φ β τ p Λ ω u`, since it is an exponential.

DERIVED: the `0` is the lower bound asserted; `4` is the dimension. -/
theorem iplaneWeight_nonneg (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    0 ≤ iplaneWeight φ β τ p Λ ω u :=
  (Real.exp_pos _).le

#print axioms iplaneWeight_local

#print axioms iplaneWeight_nonneg

/-- The plane weight is strictly positive, being an exponential. `iplaneWeight_nonneg` is the weak
form;
`ActionSplit.pairing_pos_iff_half_ne_const` needs this one, because it divides the weight out of
`W·x² = 0`.

DERIVED: the `0` is the strict lower bound, which is the whole statement; `β`, `τ`, `p`, `Λ` and `ω`
are the caller's, and `4` is the dimension. -/
theorem iplaneWeight_pos {G : Type} [Group G] (φ : G → ℝ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : 0 < iplaneWeight φ β τ p Λ ω u :=
  Real.exp_pos _

#print axioms iplaneWeight_pos

/-- At `β = 0` the half-weight is `1`: `ihalfBoltz` is `exp (-β * iactPlus)` and `exp 0 = 1`.

DERIVED: the `0` is the coupling this is evaluated at; the `1` is `exp 0`; `4` is the dimension. -/
theorem ihalfBoltz_at_zero_coupling {G : Type} [Group G] (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ihalfBoltz φ 0 τ p Λ ω u = 1 := by
  unfold ihalfBoltz
  simp

#print axioms ihalfBoltz_at_zero_coupling

/-- `GibbsSpec.splice Λ · ω` is continuous in the inner configuration, for any topological group.
`WilsonDLR.continuous_splice_right` is the statement for the outer one.

DERIVED: the signature writes no numeral. -/
theorem continuous_splice_left {G : Type} [TopologicalSpace G]
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Continuous (fun u : MassGap.GibbsSpec.VConf G Λ => MassGap.GibbsSpec.splice Λ u ω) := by
  refine continuous_pi (fun l => ?_)
  by_cases hl : l ∈ Λ
  · have he : (fun u : MassGap.GibbsSpec.VConf G Λ => MassGap.GibbsSpec.splice Λ u ω l)
        = fun u => u ⟨l, hl⟩ := funext fun u => MassGap.GibbsSpec.splice_mem hl
    rw [he]; exact continuous_apply _
  · have he : (fun u : MassGap.GibbsSpec.VConf G Λ => MassGap.GibbsSpec.splice Λ u ω l)
        = fun _ => ω l := funext fun u => MassGap.GibbsSpec.splice_not_mem hl
    rw [he]; exact continuous_const

#print axioms continuous_splice_left

/-- The spliced holonomy `fun u => GibbsSpec.ihol q (splice Λ u ω)` is continuous in the inner
configuration — `PlaqVariance.continuous_wilsonHol` composed with `continuous_splice_left`.

DERIVED: the signature writes no numeral. -/
theorem continuous_ihol_splice {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (q : MassGap.GibbsSpec.IPlaq) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) :
    Continuous (fun u : MassGap.GibbsSpec.VConf G Λ =>
      MassGap.GibbsSpec.ihol q (MassGap.GibbsSpec.splice Λ u ω)) :=
  (MassGap.PlaqVariance.continuous_wilsonHol MassGap.GibbsSpec.ibd q).comp
    (continuous_splice_left Λ ω)

#print axioms continuous_ihol_splice

/-- The positive half-action is continuous in the inner configuration, for a continuous density `φ`:
a
finite sum of `continuous_ihol_splice` terms over `iplqPlus τ p Λ`.

DERIVED: the signature writes no numeral of its own; `4` is the dimension carried by `Fin 4` and
`ILink`. -/
theorem continuous_iactPlus {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℝ} (hφc : Continuous φ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Continuous (iactPlus φ τ p Λ ω) := by
  unfold iactPlus MassGap.GibbsSpec.actionOn
  exact continuous_finset_sum _ (fun q _ => hφc.comp (continuous_ihol_splice q Λ ω))

#print axioms continuous_iactPlus

/-- The half-weight is continuous in the inner configuration — `Real.exp` composed with
`continuous_iactPlus`.

DERIVED: the signature writes no numeral of its own; `4` is the dimension carried by `Fin 4` and
`ILink`. -/
theorem continuous_ihalfBoltz {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℝ} (hφc : Continuous φ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Continuous (ihalfBoltz φ β τ p Λ ω) := by
  unfold ihalfBoltz
  exact Real.continuous_exp.comp ((continuous_iactPlus hφc τ p Λ ω).const_smul (-β)
    |>.congr (fun u => by simp [smul_eq_mul]))

#print axioms continuous_ihalfBoltz

/-- At `β = 0` the dressed observable is the bare one: `idressed φ 0 τ p Λ ω F = F`, since the
exponential is `1` there by `ihalfBoltz_at_zero_coupling`. The observable the three-block machinery
sees at zero coupling is `F` itself.

At `β ≠ 0` the dressing does vary with `boxR`; `idressed_depends_on_boxR` exhibits that on the
one-plaquette carrier.

DERIVED: the `0` is the coupling; `4` is the dimension. -/
theorem idressed_at_zero_coupling {G : Type} [Group G] (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (F : MassGap.GibbsSpec.VConf G Λ → ℝ) :
    idressed φ 0 τ p Λ ω F = F := by
  funext u
  unfold idressed
  rw [ihalfBoltz_at_zero_coupling φ τ p Λ ω u, mul_one]

#print axioms idressed_at_zero_coupling

/-- At `β = 0` the plane weight is `1` as well.

DERIVED: the `0` is the coupling; the `1` is `exp 0`; `4` is the dimension. -/
theorem iplaneWeight_at_zero_coupling {G : Type} [Group G] (φ : G → ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : iplaneWeight φ 0 τ p Λ ω u = 1 := by
  unfold iplaneWeight
  simp

#print axioms iplaneWeight_at_zero_coupling

end PlaneWeight

/-! ## 3d‴d. The bound `C`, and measurability -/

section Bounds

open MassGap.LatticeReflection

/-- `|exp (-β * actionOn φ S U)| ≤ exp (|β| * (S.card * 2))` for a density with `0 ≤ φ ≤ 2`, over
any
finite plaquette set `S`. The `ℤ⁴` counterpart of `ActionSplit.abs_exp_actSum_le`.

DERIVED: the `2` is the range of the Wilson density (`WilsonAction.wilsonDensity_le_two` and
`wilsonDensity_nonneg`), carried in as `hφ2`, and the `0` is its sign hypothesis `hφ0`; the
cardinality is the plaquette set's own. -/
theorem abs_exp_neg_actionOn_le {G : Type} [Group G] {φ : G → ℝ}
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (S : Finset MassGap.GibbsSpec.IPlaq) (U : MassGap.GibbsSpec.IConf G) :
    |Real.exp (-β * MassGap.GibbsSpec.actionOn φ S U)| ≤ Real.exp (|β| * ((S.card : ℝ) * 2)) := by
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc -β * MassGap.GibbsSpec.actionOn φ S U
      ≤ |(-β) * MassGap.GibbsSpec.actionOn φ S U| := le_abs_self _
    _ = |β| * |MassGap.GibbsSpec.actionOn φ S U| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * ((S.card : ℝ) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_of_nonneg (MassGap.GibbsSpec.actionOn_nonneg hφ0 S U)]
        exact MassGap.GibbsSpec.actionOn_le hφ2 S U

#print axioms abs_exp_neg_actionOn_le

/-- The matching floor, `exp (-(|β| * (S.card * 2))) ≤ exp (-β * actionOn φ S U)`, by the same
route.
`Real.exp_pos` is pointwise and supplies no constant.

DERIVED: the `2` is the range of the density and the `0` its sign hypothesis, as in
`abs_exp_neg_actionOn_le`. No dimension parameter enters this signature. -/
theorem exp_neg_actionOn_ge {G : Type} [Group G] {φ : G → ℝ}
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (S : Finset MassGap.GibbsSpec.IPlaq) (U : MassGap.GibbsSpec.IConf G) :
    Real.exp (-(|β| * ((S.card : ℝ) * 2)))
      ≤ Real.exp (-β * MassGap.GibbsSpec.actionOn φ S U) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : |(-β) * MassGap.GibbsSpec.actionOn φ S U| ≤ |β| * ((S.card : ℝ) * 2) := by
    rw [abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (MassGap.GibbsSpec.actionOn_nonneg hφ0 S U)]
    exact MassGap.GibbsSpec.actionOn_le hφ2 S U
  have h2 := neg_abs_le ((-β) * MassGap.GibbsSpec.actionOn φ S U)
  linarith

#print axioms exp_neg_actionOn_ge

variable {G : Type} [Group G]

/-- The half Boltzmann factor is bounded by `exp (|β| * ((iplqPlus τ p Λ).card * 2))` —
`abs_exp_neg_actionOn_le` at the positive-half plaquette set.

DERIVED: the `2` is the range of the density and the `0` its sign hypothesis, as in
`abs_exp_neg_actionOn_le`; `4` is the dimension. -/
theorem ihalfBoltz_abs_le {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    |ihalfBoltz φ β τ p Λ ω u| ≤ Real.exp (|β| * (((iplqPlus τ p Λ).card : ℝ) * 2)) :=
  abs_exp_neg_actionOn_le hφ0 hφ2 β _ _

/-- The plane weight is bounded by `exp (|β| * ((iplqZero τ p Λ).card * 2))` — the same lemma at the
plane plaquette set.

DERIVED: the `2` is the range of the density and the `0` its sign hypothesis, as in
`abs_exp_neg_actionOn_le`; `4` is the dimension. -/
theorem iplaneWeight_abs_le {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    |iplaneWeight φ β τ p Λ ω u| ≤ Real.exp (|β| * (((iplqZero τ p Λ).card : ℝ) * 2)) :=
  abs_exp_neg_actionOn_le hφ0 hφ2 β _ _

/-- A floor for the plane weight, `exp (-(|β| * ((iplqZero τ p Λ).card * 2))) ≤ iplaneWeight ...`,
which
`irefl_box_pairing_ge_variance` passes as `Wmin`. `iplaneWeight_pos` is pointwise and supplies no
constant.

DERIVED: the `2` is the range of the density; the `0` is the density's sign hypothesis; `4` is the
dimension. -/
theorem iplaneWeight_lower_bound {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    Real.exp (-(|β| * (((iplqZero τ p Λ).card : ℝ) * 2)))
      ≤ iplaneWeight φ β τ p Λ ω u :=
  exp_neg_actionOn_ge hφ0 hφ2 β _ _

#print axioms iplaneWeight_lower_bound

/-- A dressed observable is bounded when the bare one is:
`|idressed φ β τ p Λ ω F u| ≤ CF * exp (|β| * ((iplqPlus τ p Λ).card * 2))`, from `hF` and
`ihalfBoltz_abs_le`.

DERIVED: the `2` is the range of the density and the `0` its sign hypothesis, as in
`abs_exp_neg_actionOn_le`; `4` is the dimension. -/
theorem idressed_abs_le {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (τ : Fin 4) (p : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf G) {F : MassGap.GibbsSpec.VConf G Λ → ℝ} {CF : ℝ}
    (hF : ∀ u, |F u| ≤ CF) (u : MassGap.GibbsSpec.VConf G Λ) :
    |idressed φ β τ p Λ ω F u| ≤ CF * Real.exp (|β| * (((iplqPlus τ p Λ).card : ℝ) * 2)) := by
  rw [idressed, abs_mul]
  exact mul_le_mul (hF u) (ihalfBoltz_abs_le hφ0 hφ2 β τ p Λ ω u) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hF u))

#print axioms idressed_abs_le

/-- `|W u * O u * O (f u)| ≤ CW * CO * CO` for any bounded `W` and `O` and any map `f` — the shape
of the
`hC` hypothesis the split lemmas take. The reflection enters only as `f`, so nothing about it is
used. Stated over an arbitrary type `α`.

DERIVED: the signature writes no numeral; the bound is the product of the caller's two. -/
theorem abs_weight_obs_obs_le {α : Type} {W O : α → ℝ} {CW CO : ℝ}
    (hW : ∀ u, |W u| ≤ CW) (hO : ∀ u, |O u| ≤ CO) (f : α → α) (u : α) :
    |W u * O u * O (f u)| ≤ CW * CO * CO := by
  rw [abs_mul, abs_mul]
  refine mul_le_mul ?_ (hO (f u)) (abs_nonneg _) ?_
  · exact mul_le_mul (hW u) (hO u) (abs_nonneg _) (le_trans (abs_nonneg _) (hW u))
  · exact mul_nonneg (le_trans (abs_nonneg _) (hW u)) (le_trans (abs_nonneg _) (hO u))

#print axioms abs_weight_obs_obs_le

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- The positive half-action is measurable in the finite-volume configuration —
`GibbsSpec.measurable_actionOn` composed with `GibbsSpec.measurable_splice_left`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem measurable_iactPlus {φ : G → ℝ} (hφ : Measurable φ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (iactPlus φ τ p Λ ω) :=
  (MassGap.GibbsSpec.measurable_actionOn hφ _).comp
    (MassGap.GibbsSpec.measurable_splice_left Λ ω)

/-- The plane action is measurable in the finite-volume configuration, by the same composition.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem measurable_iactZero {φ : G → ℝ} (hφ : Measurable φ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (iactZero φ τ p Λ ω) :=
  (MassGap.GibbsSpec.measurable_actionOn hφ _).comp
    (MassGap.GibbsSpec.measurable_splice_left Λ ω)

theorem measurable_ihalfBoltz {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (ihalfBoltz φ β τ p Λ ω) :=
  Real.measurable_exp.comp ((measurable_iactPlus hφ τ p Λ ω).const_mul _)

theorem measurable_iplaneWeight {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (iplaneWeight φ β τ p Λ ω) :=
  Real.measurable_exp.comp ((measurable_iactZero hφ τ p Λ ω).const_mul _)

theorem measurable_idressed {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    {F : MassGap.GibbsSpec.VConf G Λ → ℝ} (hF : Measurable F) :
    Measurable (idressed φ β τ p Λ ω F) :=
  hF.mul (measurable_ihalfBoltz hφ β τ p Λ ω)

#print axioms measurable_idressed

#print axioms measurable_iplaneWeight

end Bounds

/-! ## 3e. The Osterwalder–Seiler split on `ℤ⁴`, at a box -/

section Split

open MeasureTheory MassGap.CompactGauge MassGap.LatticeReflection

variable {N : ℕ} {τ : Fin 4} {p : ℤ} {Λ : Finset ILink}

/-- The Osterwalder–Seiler split on `ℤ⁴`: `0 ≤ ∫ W · O · (O ∘ Θ)` over `ActionSplit.cvol ↥Λ` with
Haar
on `SU N`, at a box stable under the reflection at `2 * p`. Instantiates
`ActionSplit.pairing_nonneg_of_local`.

The structural inputs are supplied here from the pieces above: the blocks `boxS`, `boxT`, `boxR` and
their disjointness, `θ = ireflBoxPerm`, `hθR` from `ireflBoxPerm_eq_self_of_mem_boxR`, `hθST` from
`ireflBoxPerm_mem_boxT_of_mem_boxS`, the dagger as `σ`, `hσR` from `boxR_ne_tau` (the shared block
carries no `τ`-link, so the twist is trivial there), and `hσ` from
`ilinkDagger_measurePreserving`.

What the caller supplies is Wilson-specific and stays as hypotheses: `hOloc`, that the observable
reads only `S ∪ R`; `hWloc` and `hWnn`, that the weight reads only `R` and is nonnegative; and `hC`,
that the integrand is bounded. For the Wilson measure those come from dressing — absorbing the half
Boltzmann weight into the observable, as `ReflectionStrong.dressed_mem` does on the torus.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; the `0`s are the lower bound
concluded and the weight's sign in `hWnn`; `N`, `τ`, `p` and `Λ` come from the `variable` line, so
the dimension does not appear in this signature. -/
theorem irefl_box_pairing_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (O : (↥Λ → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → O U = O V)
    (W : (↥Λ → MassGap.SUN.SU N) → ℝ) (hWm : Measurable W) (hWnn : ∀ U, 0 ≤ W U)
    (hWloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxR τ p Λ, U i = V i) → W U = W V)
    (C : ℝ)
    (hC : ∀ U, |W U * O U *
      O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)| ≤ C) :
    0 ≤ ∫ U, W U * O U *
      O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
  MassGap.ActionSplit.pairing_nonneg_of_local
    (probHaar (MassGap.SUN.SU N))
    (boxS τ p Λ) (boxT τ p Λ) (boxR τ p Λ)
    boxS_disjoint_boxT boxS_disjoint_boxR boxT_disjoint_boxR
    (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1)
    (fun l => ilinkDagger_measurePreserving τ l.1)
    (fun _ hi => ireflBoxPerm_eq_self_of_mem_boxR hΛ hi)
    (fun _ hi u => ilinkDagger_eq_self_of_ne τ (boxR_ne_tau hi) u)
    (fun _ hi => ireflBoxPerm_mem_boxT_of_mem_boxS hΛ hi)
    (fun _ => 1)
    O hOm hOloc W hWm hWnn hWloc C hC

#print axioms irefl_box_pairing_nonneg

/-- When the box's reflection form vanishes. `irefl_box_pairing_nonneg` gives `0 ≤`; this gives the
equivalence at the same instantiation of the same three blocks, from
`ActionSplit.pairing_eq_zero_iff_local`. The form is zero exactly when the weight times the square
of
the observable's conditional half-integral — the integral over the positive block with the shared
block held fixed — vanishes almost everywhere.

The right-hand side constrains the conditional half-integral, not `O` itself: an observable can vary
while that half-integral vanishes. `ActionSplit.glue_base_congr` shows the right-hand side does not
depend on the `base` the instantiation picks, so the criterion is a property of `O` and `W` alone.

Stated at one finite box.

DERIVED: the `2` in `2 * p` is the even reflection constant, as in `irefl_box_pairing_nonneg`; the
`2` in `^ 2` is the square of `ActionSplit.pairing_eq_weighted_square`; the `0`s are the vanishing
asserted on each side and the weight's sign; the `1` is the all-identity `base`; `4` is the
dimension. -/
theorem irefl_box_pairing_eq_zero_iff
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (O : (↥Λ → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (↥Λ → MassGap.SUN.SU N) → ℝ) (hWm : Measurable W) (hWnn : ∀ U, 0 ≤ W U)
    (hWloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxR τ p Λ, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) :
    (∫ U, W U * O U *
        O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
        ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) = 0
      ↔ (fun U => W U * (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
            (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
            (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
              (fun _ => 1) v w)) U) ^ 2)
          =ᵐ[MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))] 0 :=
  MassGap.ActionSplit.pairing_eq_zero_iff_local
    (probHaar (MassGap.SUN.SU N))
    (boxS τ p Λ) (boxT τ p Λ) (boxR τ p Λ)
    boxS_disjoint_boxT boxS_disjoint_boxR boxT_disjoint_boxR
    (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1)
    (fun l => ilinkDagger_measurePreserving τ l.1)
    (fun _ hi => ireflBoxPerm_eq_self_of_mem_boxR hΛ hi)
    (fun _ hi u => ilinkDagger_eq_self_of_ne τ (boxR_ne_tau hi) u)
    (fun _ hi => ireflBoxPerm_mem_boxT_of_mem_boxS hΛ hi)
    (fun _ => 1)
    O hOm hOloc Ch hOb W hWm hWnn hWloc Cw hWb

#print axioms irefl_box_pairing_eq_zero_iff

/-- When the box's reflection form is strictly positive. The companion to
`irefl_box_pairing_eq_zero_iff`, from `ActionSplit.pairing_pos_iff_half_ne_const`: the
`k`-subtracted form is strictly positive exactly when the observable's conditional half-integral is
not almost everywhere `k`. Takes `hWpos : ∀ U, 0 < W U` where the vanishing criterion takes only
`hWnn`.

The criterion is about the half-integral as a function of the shared block. In the Wilson
instantiation the observable carried here is the dressed one, `idressed = F · e^{-βA₊}`, and
`idressed_depends_on_boxR` exhibits two configurations agreeing off `boxR` at which the integrand
differs — the half-integral integrates over the `S`-block, so that is a statement about the
integrand.

With `0 < W` the two sides are `irefl_box_pairing_eq_zero_iff` negated and signed. What the form
adds is the criterion written as a statement about a function of the plane variables, which is the
shape `HaarVariance.variance_pos_of_two_values` takes — available at this instantiation, unlike in
`ActionSplit`'s abstract section, because `SU N` carries a topology and Haar is open-positive.

DERIVED: the `2` is the even reflection constant, as in `irefl_box_pairing_eq_zero_iff`; the `0`s
are the positivity asserted, the weight's sign in `hWpos`, and the a.e. vanishing denied; the `1` is
the all-identity `base`, which `ActionSplit.glue_base_congr` shows the statement does not depend on;
`4` is the dimension. -/
theorem irefl_box_pairing_pos_iff
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (O : (↥Λ → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (↥Λ → MassGap.SUN.SU N) → ℝ) (hWm : Measurable W) (hWpos : ∀ U, 0 < W U)
    (hWloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxR τ p Λ, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) (k : ℝ) :
    0 < (∫ U, W U * (O U - k) *
        (O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U) - k)
        ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
      ↔ ¬ ((fun U => MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
            (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
            (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
              (fun _ => 1) v w)) U - k)
          =ᵐ[MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))] 0) :=
  MassGap.ActionSplit.pairing_pos_iff_half_ne_const
    (probHaar (MassGap.SUN.SU N))
    (boxS τ p Λ) (boxT τ p Λ) (boxR τ p Λ)
    boxS_disjoint_boxT boxS_disjoint_boxR boxT_disjoint_boxR
    (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1)
    (fun l => ilinkDagger_measurePreserving τ l.1)
    (fun _ hi => ireflBoxPerm_eq_self_of_mem_boxR hΛ hi)
    (fun _ hi u => ilinkDagger_eq_self_of_ne τ (boxR_ne_tau hi) u)
    (fun _ hi => ireflBoxPerm_mem_boxT_of_mem_boxS hΛ hi)
    (fun _ => 1)
    O hOm hOloc Ch hOb W hWm hWpos hWloc Cw hWb k

#print axioms irefl_box_pairing_pos_iff

/-- The box's reflection form is strictly positive for an observable of the form
`O U = f(plane part of U) · K U`, at every `k`.

The plane factor pulls out of the half-integral (`ActionSplit.halfIntegral_mul_R_left`), what is
left
is the `S`-integral of `K`, and the uniform lower bound `hKc : c ≤ K` with `hc0 : 0 < c` makes that
strictly positive (`ActionSplit.le_halfIntegral`). So `ha : f a = 0` and `hb : 0 < f b` give the
half-integral two values, which is `ActionSplit.pairing_pos_of_half_two_values`'s hypothesis.

The bare factor `f` reads the plane alone but the product does not, so
`ActionSplit.pairing_pos_iff_ne_const_of_indep_S` does not apply; this is the mixed case. Both `hKc`
and the bound `hKb` are used, through `le_halfIntegral`: without a bound the Bochner integral of a
non-integrable function is `0` by convention and the floor would not carry the conclusion.

`K` is where the dressing goes; `irefl_box_pairing_pos_of_plane_factor_dressed` discharges every
hypothesis on `K` for `ihalfBoltz`. The conclusion is a strict sign, not a quantitative lower bound.

DERIVED: the `2` is the even reflection constant `2 * p`, as in `irefl_box_pairing_pos_iff`; the
`0`s are `c`'s sign, `f`'s value at `a`, the sign of `f`'s value at `b`, the weight's sign, and the
positivity concluded; the `1` is the all-identity `base`; `4` is the dimension. -/
theorem irefl_box_pairing_pos_of_plane_factor
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (f : (↥(boxR τ p Λ) → MassGap.SUN.SU N) → ℝ) (hfc : Continuous f)
    {Cf : ℝ} (hfb : ∀ w, |f w| ≤ Cf)
    (K : (↥Λ → MassGap.SUN.SU N) → ℝ) (hKm : Measurable K)
    (hKloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → K U = K V)
    {Ck : ℝ} (hKb : ∀ U, |K U| ≤ Ck) {c : ℝ} (hc0 : 0 < c) (hKc : ∀ U, c ≤ K U)
    (hKcj : Continuous (fun q : ((↥(boxS τ p Λ) → MassGap.SUN.SU N) ×
        (↥(boxR τ p Λ) → MassGap.SUN.SU N)) =>
      K (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ) (fun _ => 1) q.1 q.2)))
    (W : (↥Λ → MassGap.SUN.SU N) → ℝ) (hWm : Measurable W) (hWpos : ∀ U, 0 < W U)
    (hWloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxR τ p Λ, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) (k : ℝ)
    {a b : ↥Λ → MassGap.SUN.SU N}
    (ha : f (fun i : ↥(boxR τ p Λ) => a (i : ↥Λ)) = 0)
    (hb : 0 < f (fun i : ↥(boxR τ p Λ) => b (i : ↥Λ))) :
    0 < (∫ U, W U
        * (f (fun i : ↥(boxR τ p Λ) => U (i : ↥Λ)) * K U - k)
        * (f (fun i : ↥(boxR τ p Λ) => MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U (i : ↥Λ))
            * K (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U) - k)
        ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) := by
  classical
  have hres : ∀ (v : ↥(boxS τ p Λ) → MassGap.SUN.SU N)
      (w : ↥(boxR τ p Λ) → MassGap.SUN.SU N),
      (fun i : ↥(boxR τ p Λ) => MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
        (fun _ => 1) v w (i : ↥Λ)) = w :=
    fun v w => MassGap.ActionSplit.glue_restrict_R _ _ boxS_disjoint_boxR _ v w
  refine MassGap.ActionSplit.pairing_pos_of_half_two_values
    (probHaar (MassGap.SUN.SU N))
    (boxS τ p Λ) (boxT τ p Λ) (boxR τ p Λ)
    boxS_disjoint_boxT boxS_disjoint_boxR boxT_disjoint_boxR
    (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1)
    (fun l => ilinkDagger_measurePreserving τ l.1)
    (fun _ hi => ireflBoxPerm_eq_self_of_mem_boxR hΛ hi)
    (fun _ hi u => ilinkDagger_eq_self_of_ne τ (boxR_ne_tau hi) u)
    (fun _ hi => ireflBoxPerm_mem_boxT_of_mem_boxS hΛ hi)
    (fun _ => 1)
    (fun U => f (fun i : ↥(boxR τ p Λ) => U (i : ↥Λ)) * K U) ?_ ?_ (Cf * Ck) ?_ ?_
    W hWm hWpos hWloc Cw hWb k (a := a) (b := b) ?_
  · have hrm : Measurable (fun U : ↥Λ → MassGap.SUN.SU N =>
        (fun i : ↥(boxR τ p Λ) => U (i : ↥Λ))) :=
      measurable_pi_lambda _ (fun i : ↥(boxR τ p Λ) => measurable_pi_apply (i : ↥Λ))
    exact (hfc.measurable.comp hrm).mul hKm
  · intro U V hS hR
    have h1 : (fun i : ↥(boxR τ p Λ) => U (i : ↥Λ))
        = (fun i : ↥(boxR τ p Λ) => V (i : ↥Λ)) := funext (fun i => hR _ i.2)
    rw [h1, hKloc U V hS hR]
  · intro U
    have hCf : (0 : ℝ) ≤ Cf :=
      le_trans (abs_nonneg _) (hfb (fun i : ↥(boxR τ p Λ) => U (i : ↥Λ)))
    rw [abs_mul]
    exact mul_le_mul (hfb _) (hKb U) (abs_nonneg _) hCf
  · simp only [hres]
    exact (hfc.comp continuous_snd).mul hKcj
  · have key := MassGap.ActionSplit.halfIntegral_two_values_of_R_factor
      (probHaar (MassGap.SUN.SU N)) (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR f
      (fun v w => K (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ) (fun _ => 1) v w))
      (hKm.comp (MassGap.ActionSplit.measurable_glue _ _ _))
      (fun _ _ => hKb _) hc0 (fun _ _ => hKc _) ha hb
    simpa only [hres] using key

#print axioms irefl_box_pairing_pos_of_plane_factor

/-- The same statement with `ihalfBoltz φ β τ p Λ ω` in place of `K`. Every hypothesis on `K` is
discharged here: `measurable_ihalfBoltz`, `ihalfBoltz_local`, `ihalfBoltz_upper_bound`,
`ihalfBoltz_lower_bound`, and `continuous_ihalfBoltz` composed with `ActionSplit.continuous_glue`.

`f` remains a hypothesis, with `ha` and `hb` asking for a plane function that vanishes at one
configuration and is positive at another, and `hΛ` asks for a `Λ` closed under the reflection, which
`quadLinks` is not. The conclusion is a strict sign, not a quantitative lower bound.

DERIVED: the `2` is the even reflection constant `2 * p`, as in `irefl_box_pairing_pos_iff`; the
`0`s are `f`'s value at `a`, the sign of `f`'s value at `b`, the weight's sign, and the positivity
concluded; `4` is the dimension. -/
theorem irefl_box_pairing_pos_of_plane_factor_dressed
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (φ : MassGap.SUN.SU N → ℝ) (hφm : Measurable φ) (hφc : Continuous φ)
    {Cφ : ℝ} (hφb : ∀ g, |φ g| ≤ Cφ) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : (↥(boxR τ p Λ) → MassGap.SUN.SU N) → ℝ) (hfc : Continuous f)
    {Cf : ℝ} (hfb : ∀ w, |f w| ≤ Cf)
    (W : (↥Λ → MassGap.SUN.SU N) → ℝ) (hWm : Measurable W) (hWpos : ∀ U, 0 < W U)
    (hWloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxR τ p Λ, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) (k : ℝ)
    {a b : ↥Λ → MassGap.SUN.SU N}
    (ha : f (fun i : ↥(boxR τ p Λ) => a (i : ↥Λ)) = 0)
    (hb : 0 < f (fun i : ↥(boxR τ p Λ) => b (i : ↥Λ))) :
    0 < (∫ U, W U
        * (f (fun i : ↥(boxR τ p Λ) => U (i : ↥Λ))
            * ihalfBoltz (G := MassGap.SUN.SU N) φ β τ p Λ ω U - k)
        * (f (fun i : ↥(boxR τ p Λ) => MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U (i : ↥Λ))
            * ihalfBoltz (G := MassGap.SUN.SU N) φ β τ p Λ ω
              (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
                (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U) - k)
        ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) :=
  irefl_box_pairing_pos_of_plane_factor hΛ f hfc hfb
    (ihalfBoltz (G := MassGap.SUN.SU N) φ β τ p Λ ω)
    (measurable_ihalfBoltz hφm β τ p Λ ω)
    (ihalfBoltz_local φ β τ p Λ ω)
    (hKb := ihalfBoltz_upper_bound φ hφb β τ p Λ ω)
    (hc0 := Real.exp_pos _)
    (hKc := ihalfBoltz_lower_bound φ hφb β τ p Λ ω)
    (hKcj := (continuous_ihalfBoltz hφc β τ p Λ ω).comp
      (MassGap.ActionSplit.continuous_glue (boxS τ p Λ) (boxR τ p Λ) (fun _ => 1)))
    W hWm hWpos hWloc Cw hWb k ha hb

#print axioms irefl_box_pairing_pos_of_plane_factor_dressed

/-- The box's reflection form is bounded below by the half-integral's variance, at every `k`:
`ActionSplit.pairing_ge_variance_of_local` instantiated with the box's own plane weight —
`measurable_iplaneWeight`, `iplaneWeight_local`, `iplaneWeight_abs_le` for the ceiling and
`iplaneWeight_lower_bound` for the floor. The floor is `exp(-|β| · card (iplqZero τ p Λ) · 2)`,
strictly positive at every `β`.

Both sides are integrals. The bound improves on `irefl_box_pairing_nonneg` where the variance is
positive, which by `ActionSplit.variance_pos_of_not_ae_const` needs the half-integral not to be
almost everywhere its own mean; where that fails the bound reads `0 ≤`. The pairing here is the
`k`-subtracted one, which agrees with the raw pairing at `k = 0`.

DERIVED: the `2` in `2 * p` is the even reflection constant; the `2` multiplying the plaquette count
is the range of the density, as in `iplaneWeight_abs_le`; the `2`s in `^ 2` are the squares of the
variance; the `0` is the density's lower sign hypothesis; the `1` is the all-identity `base`; `4` is
the dimension. -/
theorem irefl_box_pairing_ge_variance
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (φ : MassGap.SUN.SU N → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (O : (↥Λ → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch) (k : ℝ) :
    Real.exp (-(|β| * (((iplqZero τ p Λ).card : ℝ) * 2)))
        * ((∫ U, (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
                (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
                (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
                  (fun _ => 1) v w)) U) ^ 2
              ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
            - (∫ U, MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
                (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
                (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
                  (fun _ => 1) v w)) U
              ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) ^ 2)
      ≤ ∫ U, iplaneWeight φ β τ p Λ ω U * (O U - k)
          * (O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U) - k)
          ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
  MassGap.ActionSplit.pairing_ge_variance_of_local
    (probHaar (MassGap.SUN.SU N))
    (boxS τ p Λ) (boxT τ p Λ) (boxR τ p Λ)
    boxS_disjoint_boxT boxS_disjoint_boxR boxT_disjoint_boxR
    (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1)
    (fun l => ilinkDagger_measurePreserving τ l.1)
    (fun _ hi => ireflBoxPerm_eq_self_of_mem_boxR hΛ hi)
    (fun _ hi u => ilinkDagger_eq_self_of_ne τ (boxR_ne_tau hi) u)
    (fun _ hi => ireflBoxPerm_mem_boxT_of_mem_boxS hΛ hi)
    (fun _ => 1)
    O hOm hOloc Ch hOb
    (iplaneWeight φ β τ p Λ ω)
    (measurable_iplaneWeight hφm β τ p Λ ω)
    (fun U V hR => iplaneWeight_local φ β τ p Λ ω U V hR)
    (Real.exp (|β| * (((iplqZero τ p Λ).card : ℝ) * 2)))
    (iplaneWeight_abs_le hφ0 hφ2 β τ p Λ ω)
    (hWmin0 := (Real.exp_pos _).le)
    (hWmin := iplaneWeight_lower_bound hφ0 hφ2 β τ p Λ ω)
    k

#print axioms irefl_box_pairing_ge_variance

/-- The lower bound of `irefl_box_pairing_ge_variance` is itself strictly positive when the
half-integral
takes two values — the hypothesis `hab`, that it differs at `a` and at `b`.
`ActionSplit.continuous_halfIntegral` makes the half-integral continuous,
`ActionSplit.not_ae_eq_const_of_two_values` makes it not a.e. its own mean against the open-positive
`cvol`, and `ActionSplit.variance_pos_of_not_ae_const` turns that into a positive variance. The
weight's floor is positive at every coupling.

The quantity shown positive is an integral expression, not a number.

DERIVED: the `2` multiplying the plaquette count is the range of the density; the `2`s in `^ 2` are
the squares of the variance; the `0`s are the density's lower sign hypothesis, its upper bound being
`2`, and the positivity concluded; the `1` is the all-identity `base`; `4` is the dimension. -/
theorem irefl_box_pairing_ge_variance_pos
    (φ : MassGap.SUN.SU N → ℝ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (O : (↥Λ → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (hcj : Continuous (fun q : ((↥(boxS τ p Λ) → MassGap.SUN.SU N) ×
        (↥(boxR τ p Λ) → MassGap.SUN.SU N)) =>
      O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ) (fun _ => 1) q.1 q.2)))
    {a b : ↥Λ → MassGap.SUN.SU N}
    (hab : MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) a ≠ MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) b) :
    0 < Real.exp (-(|β| * (((iplqZero τ p Λ).card : ℝ) * 2)))
        * ((∫ U, (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U) ^ 2
              ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
            - (∫ U, MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U
              ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) ^ 2) := by
  classical
  have hmj : Measurable (fun q : ((↥(boxS τ p Λ) → MassGap.SUN.SU N) ×
      (↥(boxR τ p Λ) → MassGap.SUN.SU N)) =>
      O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ) (fun _ => 1) q.1 q.2)) :=
    hOm.comp (MassGap.ActionSplit.measurable_glue _ _ _)
  have hcont : Continuous (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w))) :=
    MassGap.ActionSplit.continuous_halfIntegral _ _ _ _ _ hmj hcj (fun _ _ => hOb _)
  have hbd : ∀ U, |MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U| ≤ Ch :=
    fun U => MassGap.ActionSplit.abs_halfIntegral_le _ _ _ _ _ (fun _ _ => hOb _) U
  have hCh0 : (0 : ℝ) ≤ Ch := le_trans (abs_nonneg _) (hOb (fun _ => 1))
  have hgi : Integrable (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)))
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
    MassGap.ActionSplit.integrable_of_bounded _ hcont.measurable hbd
  have hg2i : Integrable (fun U => (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U) ^ 2)
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) := by
    refine MassGap.ActionSplit.integrable_of_bounded _ (hcont.measurable.pow_const 2)
      (C := Ch ^ 2) (fun U => ?_)
    rw [abs_pow]
    nlinarith [abs_nonneg (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U), hbd U]
  refine mul_pos (Real.exp_pos _) ?_
  refine MassGap.ActionSplit.variance_pos_of_not_ae_const
    (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) _ hgi hg2i ?_
  intro hae
  refine MassGap.ActionSplit.not_ae_eq_const_of_two_values
    (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) hcont
    (∫ y, MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) y ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) hab ?_
  filter_upwards [hae] with U hU
  simp only [Pi.zero_apply]
  rw [hU]
  ring

#print axioms irefl_box_pairing_ge_variance_pos

/-- The two halves joined: the variance expression is strictly positive
(`irefl_box_pairing_ge_variance_pos`) and it lies below the box's Wilson reflection form at every
`k`
(`irefl_box_pairing_ge_variance`). So the form is strictly positive, and the quantity it exceeds is
named.

The floor is an integral expression rather than a number.

DERIVED: the `2` in `2 * p` is the even reflection constant; the `2` multiplying the plaquette count
is the range of the density; the `2`s in `^ 2` are the squares of the variance; the `0`s are the
density's lower sign hypothesis and the positivity concluded; the `1` is the all-identity `base`;
`4` is the dimension. -/
theorem irefl_box_pairing_pos_and_floor
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (φ : MassGap.SUN.SU N → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (O : (↥Λ → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (hcj : Continuous (fun q : ((↥(boxS τ p Λ) → MassGap.SUN.SU N) ×
        (↥(boxR τ p Λ) → MassGap.SUN.SU N)) =>
      O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ) (fun _ => 1) q.1 q.2)))
    {a b : ↥Λ → MassGap.SUN.SU N}
    (hab : MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) a ≠ MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) b)
    (k : ℝ) :
    0 < Real.exp (-(|β| * (((iplqZero τ p Λ).card : ℝ) * 2)))
        * ((∫ U, (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U) ^ 2
              ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
            - (∫ U, MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U
              ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) ^ 2)
      ∧ Real.exp (-(|β| * (((iplqZero τ p Λ).card : ℝ) * 2)))
          * ((∫ U, (MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U) ^ 2
                ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
              - (∫ U, MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
          (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
          (fun v w => O (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
            (fun _ => 1) v w)) U
                ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) ^ 2)
        ≤ ∫ U, iplaneWeight φ β τ p Λ ω U * (O U - k)
            * (O (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
                (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U) - k)
            ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
  ⟨irefl_box_pairing_ge_variance_pos φ hφ0 hφ2 β O hOm Ch hOb hcj hab,
    irefl_box_pairing_ge_variance hΛ φ hφm hφ0 hφ2 β ω O hOm hOloc Ch hOb k⟩

#print axioms irefl_box_pairing_pos_and_floor

/-- At the literal weight `1` and the bare observable `F`, the box's `k`-subtracted reflection form
is
exactly `0` for every `F` reading the positive block alone — `hFS` asks agreement on `boxS` only.
`ActionSplit.pairing_eq_zero_of_indep_R` applies directly: subtract the constant the half-integral
takes and the pairing vanishes.

Scope: the weight is the constant `1`, not the box's `wtFree`. `wtFree_at_zero_coupling` is the
bridge between them and is not used here, so a caller holding the `β`-parametrised pairing rewrites
through it first. Nothing is asserted at `β ≠ 0`, where `hOS` can fail —
`idressed_depends_on_boxR` exhibits a dressed observable that depends on `boxR` at every non-zero
coupling. The statement is at one box, not at a limit state.

DERIVED: the only `0` in the statement is the pairing's value — `β` does not occur, the coupling
being carried by the literal weight; the `2` is the even reflection constant `2 * p`, as in
`irefl_box_pairing_nonneg`; the `1`s are the weight, the all-identity `base`, and the point each
half-integral is evaluated at; `4` is the dimension. -/
theorem irefl_box_pairing_eq_zero_at_zero_coupling
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    (F : (↥Λ → MassGap.SUN.SU N) → ℝ) (hFm : Measurable F)
    (hFS : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → F U = F V)
    (Ch : ℝ) (hFb : ∀ U, |F U| ≤ Ch) :
    (∫ U, (1 : ℝ)
        * (F U - MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
            (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
            (fun v w => F (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
              (fun _ => 1) v w)) (fun _ => 1))
        * (F (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
            - MassGap.ActionSplit.halfIntegral (probHaar (MassGap.SUN.SU N))
              (boxS τ p Λ) (boxR τ p Λ) boxS_disjoint_boxR
              (fun v w => F (MassGap.ActionSplit.glue (boxS τ p Λ) (boxR τ p Λ)
                (fun _ => 1) v w)) (fun _ => 1))
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))) = 0 :=
  MassGap.ActionSplit.pairing_eq_zero_of_indep_R
    (probHaar (MassGap.SUN.SU N))
    (boxS τ p Λ) (boxT τ p Λ) (boxR τ p Λ)
    boxS_disjoint_boxT boxS_disjoint_boxR boxT_disjoint_boxR
    (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1)
    (fun l => ilinkDagger_measurePreserving τ l.1)
    (fun _ hi => ireflBoxPerm_eq_self_of_mem_boxR hΛ hi)
    (fun _ hi u => ilinkDagger_eq_self_of_ne τ (boxR_ne_tau hi) u)
    (fun _ hi => ireflBoxPerm_mem_boxT_of_mem_boxS hΛ hi)
    (fun _ => 1)
    F hFm hFS Ch hFb
    (fun _ => (1 : ℝ)) measurable_const (fun _ => zero_le_one)
    (fun _ _ _ => rfl) 1 (fun _ => by norm_num)

#print axioms irefl_box_pairing_eq_zero_at_zero_coupling

/-- The abstract twist and the concrete reflection agree inside the box: splicing
`ActionSplit.twist (ireflBoxPerm hΛ) (ilinkDagger τ ·) u` into `ω` gives, at a link `l ∈ Λ`, the
same
group element as `ireflConf τ c (splice Λ u ω) l`. `ActionSplit` relabels and maps fibres on the
index type; the lattice relabels and inverts on configurations.

Stated for `l ∈ Λ` only; the two need not agree outside the box. Every plaquette the action sums
over has all four links in `Λ`, so nothing outside is read.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. -/
theorem splice_twist_eq_ireflConf {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ)
    {l : ILink} (hl : l ∈ Λ) :
    MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω l
      = ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω) l := by
  have himg : ireflLink τ c l ∈ Λ := hΛ l hl
  rw [MassGap.GibbsSpec.splice_mem hl]
  have hperm : (ireflBoxPerm hΛ ⟨l, hl⟩ : ↥Λ) = ⟨ireflLink τ c l, himg⟩ :=
    Subtype.ext (ireflBoxPerm_coe hΛ ⟨l, hl⟩)
  simp only [MassGap.ActionSplit.twist, hperm, ireflConf, ilinkDagger,
    MassGap.GibbsSpec.splice_mem himg]

#print axioms splice_twist_eq_ireflConf

/-- The half-action at the twisted configuration is the negative half-action at the original:
`iactPlus φ τ p Λ ω (twist ... u) = actionOn φ (iplqMinus τ p Λ) (splice Λ u ω)`.
`splice_twist_eq_ireflConf` moves the twist to `ireflConf`, and `action_iplqPlus_ireflConf` does the
rest; `hφ` asks `φ` to be a class function.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; `4` is the dimension. -/
theorem iactPlus_twist (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφ : ∀ g h, φ (g * h * g⁻¹) = φ h)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    iactPlus φ τ p Λ ω
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)
      = MassGap.GibbsSpec.actionOn φ (iplqMinus τ p Λ) (MassGap.GibbsSpec.splice Λ u ω) := by
  have h1 : iactPlus φ τ p Λ ω
      (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)
      = MassGap.GibbsSpec.actionOn φ (iplqPlus τ p Λ)
          (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω)) :=
    MassGap.GibbsSpec.actionOn_congr φ _ _ _
      (fun q hq l hl => splice_twist_eq_ireflConf hΛ ω u (iplqPlus_link_mem_box τ p Λ hq hl))
  rw [h1]
  exact action_iplqPlus_ireflConf φ hφ τ p hΛ _

#print axioms iactPlus_twist

/-- The Gibbs weight of the box factors as a plane weight times an observable times that observable
at
the twisted configuration:
`exp (-β * actionOn φ (iplqAll Λ) (splice Λ u ω)) = iplaneWeight · ihalfBoltz(u) · ihalfBoltz(Θu)`.
This is the shape `ActionSplit.pairing_nonneg_of_local` consumes.

It is `actionOn_split_three` — the action splits into three groups — together with `iactPlus_twist`,
which carries the positive group onto the negative one and needs `hφ`, `φ` a class function, because
the mirrored holonomy is only conjugate to the image plaquette's.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` in `hΛ`; the sign is the Gibbs
convention; `4` is the dimension. -/
theorem gibbs_weight_factors (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφ : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    Real.exp (-β * MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (MassGap.GibbsSpec.splice Λ u ω))
      = iplaneWeight φ β τ p Λ ω u * ihalfBoltz φ β τ p Λ ω u
        * ihalfBoltz φ β τ p Λ ω
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) := by
  rw [actionOn_split_three φ τ p Λ]
  simp only [iplaneWeight, ihalfBoltz]
  rw [iactPlus_twist hΛ hφ ω u]
  simp only [iactZero, iactPlus]
  rw [mul_add, mul_add, Real.exp_add, Real.exp_add]

#print axioms gibbs_weight_factors

/-- Reflection positivity of the Wilson pairing on `ℤ⁴` at a reflection-stable box:
`0 ≤ ∫ iplaneWeight · idressed F · (idressed F ∘ Θ)`. Every hypothesis of
`irefl_box_pairing_nonneg` is discharged here from the plane weight and the dressing.

What the caller supplies:

* `φ` measurable with `0 ≤ φ ≤ 2` — the Wilson density's own range
  (`WilsonAction.wilsonDensity_nonneg`, `wilsonDensity_le_two`);
* `F` measurable, bounded, and reading `S ∪ R`;
* `hΛ`, that the box is stable under the link reflection at `2 * p`.

The blocks, the dagger, the plane weight, the dressing and the bound are proved here. Note that this
statement is about `iplaneWeight` times the dressed observable, not about `wtFree`;
`wtFree_refl_pairing_nonneg` is the statement in the free-boundary weight.

DERIVED: the `2`s are the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling
in `hφ2`; the `0`s are the density's sign hypothesis and the lower bound concluded; `4` is the
dimension. -/
theorem irefl_box_wilson_pairing_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    (hFloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → F U = F V)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    0 ≤ ∫ U, iplaneWeight φ β τ p Λ ω U * idressed φ β τ p Λ ω F U
        * idressed φ β τ p Λ ω F
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
  irefl_box_pairing_nonneg hΛ
    (idressed φ β τ p Λ ω F) (measurable_idressed hφm β τ p Λ ω hFm)
    (fun U V hS hR => idressed_local φ β τ p Λ ω hFloc U V hS hR)
    (iplaneWeight φ β τ p Λ ω) (measurable_iplaneWeight hφm β τ p Λ ω)
    (iplaneWeight_nonneg φ β τ p Λ ω)
    (fun U V hR => iplaneWeight_local φ β τ p Λ ω U V hR)
    _
    (fun U => abs_weight_obs_obs_le
      (iplaneWeight_abs_le hφ0 hφ2 β τ p Λ ω)
      (idressed_abs_le hφ0 hφ2 β τ p Λ ω hFb) _ U)

#print axioms irefl_box_wilson_pairing_nonneg

/-- The free-boundary weight of a box: `exp (-β * actionOn φ (iplqAll Λ) (splice Λ u ω))`, summing
over
the plaquettes with every link inside `Λ`.

This is not `GibbsSpec.wt`, which sums over `boundaryPlaqs Λ` — every plaquette with some link in
`Λ`. Those straddling the edge read the boundary condition `ω` outside the box, and a plaquette with
links on both sides of the box edge belongs to neither half of the reflection. The
Osterwalder–Seiler argument is about the free-boundary measure, which sums over `iplqAll Λ`.

`ω` is carried and inert: every plaquette of `iplqAll` has all four links in `Λ`, so `splice` never
consults it. `wtFree_congr_right` is that statement.

DERIVED: the signature writes no numeral; the sign is the Gibbs convention and `4` is the
dimension. -/
noncomputable def wtFree {G : Type} [Group G] (φ : G → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : ℝ :=
  Real.exp (-β * MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (MassGap.GibbsSpec.splice Λ u ω))

/-- **The reassembled configuration is the box configuration updated on the region.**

The crux identity of the assembly. `ActionSplit.integral_cvol_split_iterated_symm` runs its inner
integral over the region's block with the outer block fixed; for a fixed outer part, the reassembly
agrees with ANY box configuration `u₀` extending that outer part, except on the region, where it
takes the inner variable. That is exactly `GibbsSpec.updateOn`.

So the inner integral is an integral over `updateOn hVΛ u₀ ·`, which `GibbsSpec.splice_updateOn`
turns into what `GibbsSpec.num` and `GibbsSpec.part` at the region read — and
`GibbsSpec.spec_splice_off` says the kernel there does not depend on which `u₀` was chosen.

DERIVED: no numeral occurs; `V`, `Λ`, `x`, `y` and `u₀` are the caller's. -/
theorem symm_eq_updateOn {G : Type} [Group G] [MeasurableSpace G]
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (x : {i : ↥Λ // (i : MassGap.InfiniteLattice.ILink) ∈ V} → G)
    (y : {i : ↥Λ // ¬ ((i : MassGap.InfiniteLattice.ILink) ∈ V)} → G)
    (u₀ : MassGap.GibbsSpec.VConf G Λ)
    (hu₀ : ∀ (i : ↥Λ) (h : ¬ ((i : MassGap.InfiniteLattice.ILink) ∈ V)), u₀ i = y ⟨i, h⟩) :
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ↥Λ => G)
        (fun i : ↥Λ => (i : MassGap.InfiniteLattice.ILink) ∈ V)).symm (x, y)
      = MassGap.GibbsSpec.updateOn hVΛ u₀
          (fun w : ↥V => x ⟨⟨(w : MassGap.InfiniteLattice.ILink), hVΛ w.2⟩, w.2⟩) := by
  funext i
  rw [MassGap.ActionSplit.piSubtypeProd_symm_apply]
  by_cases h : (i : MassGap.InfiniteLattice.ILink) ∈ V
  · rw [dif_pos h]
    simp only [MassGap.GibbsSpec.updateOn, dif_pos h]
  · rw [dif_neg h]
    simp only [MassGap.GibbsSpec.updateOn, dif_neg h]
    exact (hu₀ i h).symm

/-- **The free weight factors at a region.** The part of the free action carried by plaquettes
touching `V`, times the rest.

The split is taken at `iplqAll Λ ∩ GibbsSpec.boundaryPlaqs V`, not at `boundaryPlaqs V` itself.
`boundaryPlaqs` contains DEGENERATE plaquettes — `GibbsSpec.touching` ranges over every direction,
including the plaquette's own — and `iplqAll` filters those out, so `boundaryPlaqs V ⊆ iplqAll Λ`
is false in general and the split would not typecheck. The intersection lies inside `iplqAll Λ` for
free, so this carries no hypothesis at all.

DERIVED: no numeral occurs; `Λ`, `V`, `ω` and `u` are the caller's. -/
theorem wtFree_factor {G : Type} [Group G] (φ : G → ℝ) (β : ℝ)
    (Λ V : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    wtFree φ β Λ ω u
      = Real.exp (-β * MassGap.GibbsSpec.actionOn φ
            (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V)
            (MassGap.GibbsSpec.splice Λ u ω))
        * Real.exp (-β * MassGap.GibbsSpec.actionOn φ
            (iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V))
            (MassGap.GibbsSpec.splice Λ u ω)) := by
  unfold wtFree
  rw [MassGap.GibbsSpec.actionOn_sdiff φ Finset.inter_subset_left, mul_add, Real.exp_add]

#print axioms wtFree_factor

/-- **The outer factor does not read the `V`-links.** Changing the configuration only on `V` leaves
the part of the free action carried by plaquettes away from `V` unchanged.

A plaquette in `iplqAll Λ \ (iplqAll Λ ∩ boundaryPlaqs V)` lies in `iplqAll Λ` but not in
`boundaryPlaqs V`, so by `GibbsSpec.not_mem_boundaryPlaqs_links` none of its links is in `V`, and
`GibbsSpec.actionOn_indep_of_avoid` applies. Links outside `Λ` are untouched because both splices
read `ω` there.

**This is the factorisation the free-boundary DLR consistency turns on**: with the weight split by
`wtFree_factor`, integrating out the `V`-links leaves the outer factor as a constant, so the
conditional is the ordinary fixed-boundary kernel at `V`.

DERIVED: no numeral occurs; `Λ`, `V` and `ω` are the caller's. -/
theorem wtFree_outer_congr {G : Type} [Group G] (φ : G → ℝ) (β : ℝ)
    (Λ V : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u u' : MassGap.GibbsSpec.VConf G Λ)
    (h : ∀ x : ↥Λ, (x : MassGap.InfiniteLattice.ILink) ∉ V → u x = u' x) :
    MassGap.GibbsSpec.actionOn φ
        (iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V))
        (MassGap.GibbsSpec.splice Λ u ω)
      = MassGap.GibbsSpec.actionOn φ
          (iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V))
          (MassGap.GibbsSpec.splice Λ u' ω) := by
  refine MassGap.GibbsSpec.actionOn_indep_of_avoid φ _ V ?_ _ _ ?_
  · intro q hq hb
    obtain ⟨hqin, hqout⟩ := Finset.mem_sdiff.mp hq
    exact hqout (Finset.mem_inter.mpr ⟨hqin, hb⟩)
  · intro l hl
    by_cases hlΛ : l ∈ Λ
    · rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
      exact h ⟨l, hlΛ⟩ hl
    · rw [MassGap.GibbsSpec.splice_not_mem hlΛ, MassGap.GibbsSpec.splice_not_mem hlΛ]

#print axioms symm_eq_updateOn

#print axioms wtFree_outer_congr

/-- **The free weight at an updated configuration is the region's own weight times a constant.**

The heart of the factorisation. `wtFree_factor` splits the free weight at
`iplqAll Λ ∩ boundaryPlaqs V`; `GibbsSpec.splice_updateOn` turns the updated configuration into the
region spliced over the box; `GibbsSpec.actionOn_drop_degenerate` closes the gap between that
plaquette set and `boundaryPlaqs V` — the difference being degenerate, given `hside` — so the first
factor is exactly `GibbsSpec.wt` at `V`; and `GibbsSpec.actionOn_indep_of_avoid` shows the second
factor does not read the region at all, so it is constant in the update.

**This is what makes the inner integral the region's own numerator and partition function.** Without
it the inner integral would carry a weight that merely resembles the kernel's.

`hside` is the "`V` well inside `Λ`" condition: every NON-degenerate plaquette touching `V` lies in
the box. For fixed `V` it holds at all large boxes. `hφ1` is supplied for the Wilson density by
`WilsonAction.wilsonDensity_one`.

DERIVED: `1` is the identity at which the density vanishes; `0` is the value it takes there. -/
theorem wtFree_updateOn_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (φ : G → ℝ) (hφ1 : φ 1 = 0) (β : ℝ)
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (hside : ∀ q ∈ MassGap.GibbsSpec.boundaryPlaqs V, q.1.1 ≠ q.1.2 → q ∈ iplqAll Λ)
    (u₀ : MassGap.GibbsSpec.VConf G Λ) (v : MassGap.GibbsSpec.VConf G V)
    (ω : MassGap.GibbsSpec.IConf G) :
    wtFree φ β Λ ω (MassGap.GibbsSpec.updateOn hVΛ u₀ v)
      = MassGap.GibbsSpec.wt φ β V v (MassGap.GibbsSpec.splice Λ u₀ ω)
        * Real.exp (-β * MassGap.GibbsSpec.actionOn φ
            (iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V))
            (MassGap.GibbsSpec.splice Λ u₀ ω)) := by
  have hdeg : ∀ q ∈ MassGap.GibbsSpec.boundaryPlaqs V \
      (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V), q.1.1 = q.1.2 := by
    intro q hq
    obtain ⟨hqB, hqn⟩ := Finset.mem_sdiff.mp hq
    by_contra hne
    exact hqn (Finset.mem_inter.mpr ⟨hside q hqB hne, hqB⟩)
  have h1 : MassGap.GibbsSpec.actionOn φ (MassGap.GibbsSpec.boundaryPlaqs V)
        (MassGap.GibbsSpec.splice V v (MassGap.GibbsSpec.splice Λ u₀ ω))
      = MassGap.GibbsSpec.actionOn φ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V)
        (MassGap.GibbsSpec.splice V v (MassGap.GibbsSpec.splice Λ u₀ ω)) :=
    MassGap.GibbsSpec.actionOn_drop_degenerate hφ1 Finset.inter_subset_right hdeg _
  have hS : ∀ q ∈ iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V),
      q ∉ MassGap.GibbsSpec.boundaryPlaqs V := by
    intro q hq hb
    obtain ⟨hqin, hqout⟩ := Finset.mem_sdiff.mp hq
    exact hqout (Finset.mem_inter.mpr ⟨hqin, hb⟩)
  have h2 : MassGap.GibbsSpec.actionOn φ
        (iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V))
        (MassGap.GibbsSpec.splice V v (MassGap.GibbsSpec.splice Λ u₀ ω))
      = MassGap.GibbsSpec.actionOn φ
        (iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V))
        (MassGap.GibbsSpec.splice Λ u₀ ω) :=
    MassGap.GibbsSpec.actionOn_indep_of_avoid φ _ V hS _ _
      (fun l hl => MassGap.GibbsSpec.splice_not_mem hl)
  rw [wtFree_factor φ β Λ V ω (MassGap.GibbsSpec.updateOn hVΛ u₀ v),
    MassGap.GibbsSpec.splice_updateOn hVΛ u₀ v ω, ← h1, h2]
  rfl

#print axioms wtFree_updateOn_eq

/-- **The split's inner block, reindexed to the region's own configuration space.**

`ActionSplit.integral_cvol_split_iterated_symm` leaves the inner integral over
`{i : ↥Λ // (i : ILink) ∈ V} → G`, a subtype of the BOX's links. `GibbsSpec.num` and
`GibbsSpec.part` at `V` integrate over `GibbsSpec.VConf G V`, that is over `GibbsSpec.vol`. This is
the change of variables between them: `GibbsSpec.linkSubEquiv` is the index equivalence and
`ActionSplit.integral_cvol_reindex` transports the measure, with Mathlib's
`piCongrLeft_apply_apply` collapsing the round trip.

**This is the last structural gap in the free-boundary DLR consistency.** With it the inner integral
is literally the region's numerator or partition function, not a reindexed lookalike.

DERIVED: no numeral occurs; `V`, `Λ` and `F` are the caller's. -/
theorem integral_vblock {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (μ : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure μ]
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (F : MassGap.GibbsSpec.VConf G V → ℝ) :
    ∫ x : ({i : ↥Λ // (i : MassGap.InfiniteLattice.ILink) ∈ V} → G),
        F (fun w : ↥V => x ((MassGap.GibbsSpec.linkSubEquiv hVΛ).symm w))
        ∂(MassGap.ActionSplit.cvol
          {i : ↥Λ // (i : MassGap.InfiniteLattice.ILink) ∈ V} μ)
      = ∫ v : MassGap.GibbsSpec.VConf G V, F v ∂(MassGap.GibbsSpec.vol μ V) := by
  rw [MassGap.ActionSplit.integral_cvol_reindex μ (MassGap.GibbsSpec.linkSubEquiv hVΛ).symm
    (fun x => F (fun w : ↥V => x ((MassGap.GibbsSpec.linkSubEquiv hVΛ).symm w)))]
  congr 1

#print axioms integral_vblock

/-- **The inner-integral identity — the analytic core of the free-boundary DLR consistency.**

Hold the configuration fixed off the region and integrate over the region's own links. The kernel at
the region does not read those links (`GibbsSpec.spec_splice_off`), so it comes out as a constant;
the free weight becomes the region's fixed-boundary weight times a factor that also does not read
them (`wtFree_updateOn_eq`). So the left side is kernel × constant × partition function and the
right side is constant × numerator — and the kernel is numerator over partition function, which
`GibbsSpec.part_pos` makes a legitimate division.

No split machinery appears here. This is the analytic step on its own; the splitting and reindexing
lemmas only put the integrals into this form.

DERIVED: `1` is the identity at which the density vanishes, in `hφ1`; `0` and `2` are the density's
range, needed by `GibbsSpec.part_pos` for the division. -/
theorem inner_spec_wtFree_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (φ : G → ℝ) (hφm : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (hφ1 : φ 1 = 0) (β : ℝ)
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (hside : ∀ q ∈ MassGap.GibbsSpec.boundaryPlaqs V, q.1.1 ≠ q.1.2 → q ∈ iplqAll Λ)
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
    (f : MassGap.GibbsSpec.IConf G → ℝ) (ω : MassGap.GibbsSpec.IConf G)
    (u₀ : MassGap.GibbsSpec.VConf G Λ) :
    ∫ v, MassGap.GibbsSpec.spec φ β V μ f
          (MassGap.GibbsSpec.splice Λ (MassGap.GibbsSpec.updateOn hVΛ u₀ v) ω)
        * wtFree φ β Λ ω (MassGap.GibbsSpec.updateOn hVΛ u₀ v)
        ∂(MassGap.GibbsSpec.vol μ V)
      = ∫ v, f (MassGap.GibbsSpec.splice Λ (MassGap.GibbsSpec.updateOn hVΛ u₀ v) ω)
        * wtFree φ β Λ ω (MassGap.GibbsSpec.updateOn hVΛ u₀ v)
        ∂(MassGap.GibbsSpec.vol μ V) := by
  set X := MassGap.GibbsSpec.splice Λ u₀ ω with hX
  set E := Real.exp (-β * MassGap.GibbsSpec.actionOn φ
      (iplqAll Λ \ (iplqAll Λ ∩ MassGap.GibbsSpec.boundaryPlaqs V)) X) with hE
  have hL : ∀ v : MassGap.GibbsSpec.VConf G V,
      MassGap.GibbsSpec.spec φ β V μ f
          (MassGap.GibbsSpec.splice Λ (MassGap.GibbsSpec.updateOn hVΛ u₀ v) ω)
        = MassGap.GibbsSpec.spec φ β V μ f X :=
    fun v => MassGap.GibbsSpec.spec_splice_off φ β V Λ μ f
      (MassGap.GibbsSpec.updateOn hVΛ u₀ v) u₀ ω
      (fun i hi => MassGap.GibbsSpec.updateOn_eq_off hVΛ u₀ v i hi)
  have hW : ∀ v : MassGap.GibbsSpec.VConf G V,
      wtFree φ β Λ ω (MassGap.GibbsSpec.updateOn hVΛ u₀ v)
        = MassGap.GibbsSpec.wt φ β V v X * E :=
    fun v => wtFree_updateOn_eq φ hφ1 β hVΛ hside u₀ v ω
  have hF : ∀ v : MassGap.GibbsSpec.VConf G V,
      f (MassGap.GibbsSpec.splice Λ (MassGap.GibbsSpec.updateOn hVΛ u₀ v) ω)
        = f (MassGap.GibbsSpec.splice V v X) :=
    fun v => congrArg f (MassGap.GibbsSpec.splice_updateOn hVΛ u₀ v ω)
  simp only [hL, hW, hF]
  have hA : ∀ v : MassGap.GibbsSpec.VConf G V,
      MassGap.GibbsSpec.spec φ β V μ f X * (MassGap.GibbsSpec.wt φ β V v X * E)
        = (MassGap.GibbsSpec.spec φ β V μ f X * E) * MassGap.GibbsSpec.wt φ β V v X :=
    fun v => by ring
  have hB : ∀ v : MassGap.GibbsSpec.VConf G V,
      f (MassGap.GibbsSpec.splice V v X) * (MassGap.GibbsSpec.wt φ β V v X * E)
        = E * (f (MassGap.GibbsSpec.splice V v X) * MassGap.GibbsSpec.wt φ β V v X) :=
    fun v => by ring
  simp only [hA, hB]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hpart : (0 : ℝ) < MassGap.GibbsSpec.part φ β V μ X :=
    MassGap.GibbsSpec.part_pos hφm hφ0 hφ2 β V μ X
  show MassGap.GibbsSpec.spec φ β V μ f X * E * MassGap.GibbsSpec.part φ β V μ X
      = E * MassGap.GibbsSpec.num φ β V μ f X
  unfold MassGap.GibbsSpec.spec
  field_simp

#print axioms inner_spec_wtFree_eq

/-- **The free state's numerator is unchanged by inserting the kernel at an interior region.**

The assembly. `ActionSplit.integral_cvol_split_iterated_symm` cuts the box's links at "lies in `V`",
putting the region on the inside; `symm_eq_updateOn` rewrites the reassembly as an update of a fixed
configuration; `integral_vblock` reindexes the inner block to the region's own configuration space;
and `inner_spec_wtFree_eq` is the identity for each fixed outer configuration.

Dividing both sides by `partFree` gives the free-boundary DLR consistency,
`stateFree Λ (spec V f) = stateFree Λ f`, which is the `hev` hypothesis that
`DLRLimit.isDLR_of_tendsto` and `limits_eq_of_unique_dlr` take and that nothing else in the tree
supplies for the FREE-boundary family.

`hside` is the "`V` well inside `Λ`" condition — every non-degenerate plaquette touching `V` lies in
the box — which holds for fixed `V` at all large boxes. Measurability and boundedness of the two
integrands are hypotheses rather than obligations discharged here: they are a separate concern from
the identity, and `ActionSplit.integrable_split_of_bounded` turns them into what the split needs.

DERIVED: `1` is the identity at which the density vanishes; `0` and `2` are the density's range,
carried in for `GibbsSpec.part_pos`. -/
theorem num_free_spec_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (φ : G → ℝ) (hφm : Measurable φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ2 : ∀ g, φ g ≤ 2) (hφ1 : φ 1 = 0) (β : ℝ)
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (hside : ∀ q ∈ MassGap.GibbsSpec.boundaryPlaqs V, q.1.1 ≠ q.1.2 → q ∈ iplqAll Λ)
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsProbabilityMeasure μ]
    (f : MassGap.GibbsSpec.IConf G → ℝ) (ω : MassGap.GibbsSpec.IConf G) {C : ℝ}
    (hm1 : Measurable fun u : MassGap.GibbsSpec.VConf G Λ =>
      MassGap.GibbsSpec.spec φ β V μ f (MassGap.GibbsSpec.splice Λ u ω)
        * wtFree φ β Λ ω u)
    (hb1 : ∀ u, |MassGap.GibbsSpec.spec φ β V μ f (MassGap.GibbsSpec.splice Λ u ω)
        * wtFree φ β Λ ω u| ≤ C)
    (hm2 : Measurable fun u : MassGap.GibbsSpec.VConf G Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω) * wtFree φ β Λ ω u)
    (hb2 : ∀ u, |f (MassGap.GibbsSpec.splice Λ u ω) * wtFree φ β Λ ω u| ≤ C) :
    ∫ u, MassGap.GibbsSpec.spec φ β V μ f (MassGap.GibbsSpec.splice Λ u ω)
        * wtFree φ β Λ ω u ∂(MassGap.ActionSplit.cvol ↥Λ μ)
      = ∫ u, f (MassGap.GibbsSpec.splice Λ u ω) * wtFree φ β Λ ω u
        ∂(MassGap.ActionSplit.cvol ↥Λ μ) := by
  classical
  rw [MassGap.ActionSplit.integral_cvol_split_iterated_symm μ
      (fun i : ↥Λ => (i : MassGap.InfiniteLattice.ILink) ∈ V) _
      (MassGap.ActionSplit.integrable_split_of_bounded μ _ _ hm1 hb1),
    MassGap.ActionSplit.integral_cvol_split_iterated_symm μ
      (fun i : ↥Λ => (i : MassGap.InfiniteLattice.ILink) ∈ V) _
      (MassGap.ActionSplit.integrable_split_of_bounded μ _ _ hm2 hb2)]
  congr 1
  funext y
  set u₀ : MassGap.GibbsSpec.VConf G Λ :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ↥Λ => G)
      (fun i : ↥Λ => (i : MassGap.InfiniteLattice.ILink) ∈ V)).symm (fun _ => (1 : G), y)
    with hu₀def
  have hu₀ : ∀ (i : ↥Λ) (h : ¬ ((i : MassGap.InfiniteLattice.ILink) ∈ V)),
      u₀ i = y ⟨i, h⟩ := by
    intro i h
    rw [hu₀def, MassGap.ActionSplit.piSubtypeProd_symm_apply, dif_neg h]
  have hre : ∀ x : {i : ↥Λ // (i : MassGap.InfiniteLattice.ILink) ∈ V} → G,
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ↥Λ => G)
        (fun i : ↥Λ => (i : MassGap.InfiniteLattice.ILink) ∈ V)).symm (x, y)
        = MassGap.GibbsSpec.updateOn hVΛ u₀
            (fun w : ↥V => x ((MassGap.GibbsSpec.linkSubEquiv hVΛ).symm w)) :=
    fun x => symm_eq_updateOn hVΛ x y u₀ hu₀
  simp only [hre]
  rw [integral_vblock μ hVΛ (fun v => MassGap.GibbsSpec.spec φ β V μ f
      (MassGap.GibbsSpec.splice Λ (MassGap.GibbsSpec.updateOn hVΛ u₀ v) ω)
        * wtFree φ β Λ ω (MassGap.GibbsSpec.updateOn hVΛ u₀ v)),
    integral_vblock μ hVΛ (fun v => f
      (MassGap.GibbsSpec.splice Λ (MassGap.GibbsSpec.updateOn hVΛ u₀ v) ω)
        * wtFree φ β Λ ω (MassGap.GibbsSpec.updateOn hVΛ u₀ v))]
  exact inner_spec_wtFree_eq φ hφm hφ0 hφ2 hφ1 β hVΛ hside μ f ω u₀

#print axioms num_free_spec_eq


/-- The free-boundary weight is strictly positive, being an exponential.

DERIVED: the `0` is the strict lower bound asserted. -/
theorem wtFree_pos {G : Type} [Group G] (φ : G → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : 0 < wtFree φ β Λ ω u := Real.exp_pos _

/-- The box weight does not see the boundary configuration: `wtFree φ β Λ ω u = wtFree φ β Λ ω' u`
for
any two backgrounds. Every plaquette of `iplqAll Λ` has all four links inside `Λ` by
`GibbsSpec.mem_plaqsIn`, so `splice` returns the box's own variable at each of them.

This is what lets `boxBd` present the box as a finite Wilson system with no boundary data;
`wilsonHol_boxBd` is the same fact at one plaquette.

DERIVED: the signature writes no numeral; `Λ` is the caller's and `4` is the dimension carried by
`ILink` and `IPlaq`, as in `iplqAll`. -/
theorem wtFree_congr_right {G : Type} [Group G] (φ : G → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω ω' : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : wtFree φ β Λ ω u = wtFree φ β Λ ω' u := by
  unfold wtFree MassGap.GibbsSpec.actionOn
  refine congrArg (fun z => Real.exp (-β * z)) (Finset.sum_congr rfl (fun q hq => ?_))
  refine congrArg φ (MassGap.GibbsSpec.ihol_congr q _ _ (fun l hl => ?_))
  have hmem : l ∈ Λ :=
    MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hq).1 l hl
  rw [MassGap.GibbsSpec.splice_mem hmem, MassGap.GibbsSpec.splice_mem hmem]

#print axioms wtFree_congr_right

/-- At `β = 0` the box weight is `1`, `wtFree` being `exp (-β * actionOn …)`.

DERIVED: the `0` is the coupling; the `1` is `exp 0`; `4` is the dimension. -/
theorem wtFree_at_zero_coupling {G : Type} [Group G] (φ : G → ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) : wtFree φ 0 Λ ω u = 1 := by
  unfold wtFree
  simp

#print axioms wtFree_at_zero_coupling

#print axioms wtFree_pos

/-- Reflection positivity in the free-boundary measure:
`0 ≤ ∫ F(U) · F(ΘU) · wtFree φ β Λ ω U`, with the Gibbs weight itself rather than a weight already
split by hand. This is the form the Osterwalder–Schrader reconstruction takes.

The rearrangement is `gibbs_weight_factors`:
`F(U) · F(ΘU) · e^{-βA(U)} = iplaneWeight(U) · (F·h)(U) · (F·h)(ΘU)`, and `F·h` is `idressed`.
`hφc` asks `φ` to be a class function, which `irefl_box_wilson_pairing_nonneg` does not need but
`gibbs_weight_factors` does.

DERIVED: the `2`s are the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling
in `hφ2`; the `0`s are the density's sign hypothesis and the lower bound concluded; `4` is the
dimension. -/
theorem wtFree_refl_pairing_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    (hFloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → F U = F V)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    0 ≤ ∫ U, F U *
        F (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
            (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
        * wtFree φ β Λ ω U
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) := by
  have hfun : (fun U : ↥Λ → MassGap.SUN.SU N => F U *
      F (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U)
      * wtFree φ β Λ ω U)
      = fun U => iplaneWeight φ β τ p Λ ω U * idressed φ β τ p Λ ω F U
          * idressed φ β τ p Λ ω F
              (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
                (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) U) := by
    funext U
    rw [wtFree, gibbs_weight_factors hΛ hφc β ω U]
    simp only [idressed]
    ring
  rw [hfun]
  exact irefl_box_wilson_pairing_nonneg hΛ hφm hφ0 hφ2 β ω hFm hFloc hFb

#print axioms wtFree_refl_pairing_nonneg

/-- The free weight is bounded: `|wtFree φ β Λ ω u| ≤ exp (|β| * ((iplqAll Λ).card * 2))`. The same
argument as `GibbsSpec.wt_le`, over a smaller plaquette set.

DERIVED: the `2` is the Wilson density's ceiling, carried in as `hφ2`, and the `0` is its sign
hypothesis `hφ0`; the cardinality is the plaquette set's own. -/
theorem wtFree_le {G : Type} [Group G] {φ : G → ℝ} (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (β : ℝ) (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G)
    (u : MassGap.GibbsSpec.VConf G Λ) :
    |wtFree φ β Λ ω u| ≤ Real.exp (|β| * (((iplqAll Λ).card : ℝ) * 2)) :=
  abs_exp_neg_actionOn_le hφ0 hφ2 β _ _

theorem measurable_wtFree {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] {φ : G → ℝ} (hφ : Measurable φ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (ω : MassGap.GibbsSpec.IConf G) :
    Measurable (wtFree φ β Λ ω) :=
  Real.measurable_exp.comp
    (((MassGap.GibbsSpec.measurable_actionOn hφ (iplqAll Λ)).comp
      (MassGap.GibbsSpec.measurable_splice_left Λ ω)).const_mul (-β))

#print axioms measurable_wtFree

/-- The free-boundary partition function of a box: `wtFree` integrated against product Haar over the
box's links, `ActionSplit.cvol ↥Λ (probHaar (SU N))`.

DERIVED: the signature writes no numeral; the measure is product Haar over the box's links. -/
noncomputable def partFree {φ : MassGap.SUN.SU N → ℝ} (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) : ℝ :=
  ∫ u, wtFree φ β Λ ω u ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))

/-- The partition function is strictly positive, so the normalisation in `specFree` is legitimate.
`GibbsSpec.part_pos`'s argument over the free plaquette set: the integrand is strictly positive
everywhere, so its support is the whole space, to which the probability measure gives measure one.
Integrability comes from `wtFree_le`.

DERIVED: the `2` is the Wilson density's ceiling in `hφ2` and the `0`s are its sign hypothesis and
the strict lower bound concluded; `4` is the dimension. -/
theorem partFree_pos {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    0 < partFree (φ := φ) β Λ ω := by
  unfold partFree
  rw [integral_pos_iff_support_of_nonneg (fun u => (wtFree_pos φ β Λ ω u).le)
    (MassGap.GibbsSpec.integrable_of_bounded _ (measurable_wtFree hφm β Λ ω)
      (wtFree_le hφ0 hφ2 β Λ ω))]
  have hsupp : Function.support (wtFree φ β Λ ω) = Set.univ :=
    Set.eq_univ_of_forall (fun u => Function.mem_support.mpr (wtFree_pos φ β Λ ω u).ne')
  rw [hsupp, measure_univ]
  exact one_pos

#print axioms partFree_pos

/-- The free-boundary expectation of a box: `∫ f · wtFree` divided by `partFree`, the normalised
state
whose limit the statements at the end of this file take.

DERIVED: the signature writes no numeral. -/
noncomputable def specFree {φ : MassGap.SUN.SU N → ℝ} (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ) : ℝ :=
  (∫ u, f u * wtFree φ β Λ ω u ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
    / partFree (φ := φ) β Λ ω

/-- The box's action is the finite Wilson system's action: `(wilsonSystem (boxBd Λ) φ).action u`
equals
`GibbsSpec.actionOn φ (iplqAll Λ) (splice Λ u ω)`. `System.action` sums `φ ∘ hol` over the plaquette
type and `actionOn` sums `φ ∘ ihol` over the `Finset`; at `Plaq := ↥(iplqAll Λ)` those are the same
sum by `Finset.sum_coe_sort`, with `wilsonHol_boxBd` matching the summands one plaquette at a time.

DERIVED: the signature writes no numeral; `Λ` and `ω` are the caller's and `4` is the dimension
carried by `ILink` and `IPlaq`, as in `iplqAll`. -/
theorem action_boxBd (φ : MassGap.SUN.SU N → ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    (MassGap.WilsonLattice.wilsonSystem (boxBd Λ) φ).action u
      = MassGap.GibbsSpec.actionOn φ (iplqAll Λ) (MassGap.GibbsSpec.splice Λ u ω) := by
  classical
  show ∑ p : ↥(iplqAll Λ), φ (MassGap.WilsonLattice.wilsonHol (boxBd Λ) p u)
      = ∑ q ∈ iplqAll Λ, φ (MassGap.GibbsSpec.ihol q (MassGap.GibbsSpec.splice Λ u ω))
  rw [← Finset.sum_coe_sort (iplqAll Λ)
    (fun q => φ (MassGap.GibbsSpec.ihol q (MassGap.GibbsSpec.splice Λ u ω)))]
  exact Finset.sum_congr rfl (fun q _ => by rw [wilsonHol_boxBd])

#print axioms action_boxBd

/-- The finite Wilson system's Boltzmann weight over `↥Λ` is `wtFree`, at every boundary
configuration —
`ω` occurs on the right and nowhere on the left, which is what `wtFree_congr_right` states on its
own.

DERIVED: the signature writes no numeral; `β`, `Λ` and `ω` are the caller's and `4` is the dimension
carried by `ILink` and `IPlaq`, as in `iplqAll`. -/
theorem boltz_boxBd (φ : MassGap.SUN.SU N → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    (MassGap.WilsonLattice.wilsonSystem (boxBd Λ) φ).boltz β u = wtFree φ β Λ ω u := by
  unfold MassGap.LatticeGauge.System.boltz wtFree
  rw [action_boxBd φ Λ ω u]

#print axioms boltz_boxBd

/-- The two partition functions agree: the finite Wilson system's over `↥Λ` and the box's
`partFree`.
Immediate from `boltz_boxBd` under the integral, the two measures being the same `Measure.pi`.

DERIVED: the signature writes no numeral; `β`, `Λ` and `ω` are the caller's and `4` is the dimension
carried by `ILink` and `IPlaq`, as in `iplqAll`. -/
theorem partition_boxBd (φ : MassGap.SUN.SU N → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    (MassGap.WilsonLattice.wilsonSystem (boxBd Λ) φ).partition
        (probHaar (MassGap.SUN.SU N)) β
      = partFree (φ := φ) β Λ ω := by
  unfold MassGap.LatticeGauge.System.partition partFree
  exact integral_congr_ae (Filter.Eventually.of_forall (fun u => boltz_boxBd φ β Λ ω u))

#print axioms partition_boxBd

/-- The free-boundary state of a box is a finite Wilson system's Gibbs expectation:
`(wilsonSystem (boxBd Λ) φ).expect (probHaar (SU N)) β O = specFree β Λ ω O`. The numerators agree
by
`boltz_boxBd` under the integral, the denominators by `partition_boxBd`, and the two measures are
the same `Measure.pi`.

With `touchDeg_boxBd_le` and `not_mem_ball_of_axis_gt`, this supplies the third of the inputs that
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow_of_le` reads off the carrier; `hN`,
`0 ≤ β` and `hr` stay with the caller, and that theorem's conclusion is about `wilsonCorrConn`, a
connected correlation of plaquette observables.

`LatticeGauge.Config` and `GibbsSpec.VConf` are definitionally equal but not syntactically so,
`wilsonSystem` being a plain `def`, so `rw` and `simp` at reducible transparency do not cross them —
which is why `action_boxBd` needs a `show`, and a caller rewriting between them needs the same.

`GibbsSpec.spec`, `part` and `num` sit on `GibbsSpec.vol` rather than on `ActionSplit.cvol`; this is
the free-boundary variant of the same correspondence, stated as a term.

The statement is an identification of two definitions.

DERIVED: the signature writes no numeral; `β`, `Λ` and `ω` are the caller's and `4` is the dimension
carried by `ILink` and `IPlaq`, as in `iplqAll`. -/
theorem expect_boxBd (φ : MassGap.SUN.SU N → ℝ) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (O : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ) :
    (MassGap.WilsonLattice.wilsonSystem (boxBd Λ) φ).expect
        (probHaar (MassGap.SUN.SU N)) β O
      = specFree (φ := φ) β Λ ω O := by
  unfold MassGap.LatticeGauge.System.expect MassGap.LatticeGauge.System.corrNum specFree
  rw [partition_boxBd φ β Λ ω]
  refine congrArg (fun z => z / partFree (φ := φ) β Λ ω) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  show O u * (MassGap.WilsonLattice.wilsonSystem (boxBd Λ) φ).boltz β u
      = O u * wtFree φ β Λ ω u
  rw [boltz_boxBd φ β Λ ω u]

#print axioms expect_boxBd

/-- `WilsonBridge.wilsonCorrConn` for `boxBd Λ` written in the box's free-boundary state: the
`specFree`
expectation of the product of the two `wilsonPlaqObs` minus the product of their separate `specFree`
expectations. `wilsonCorr` is `.expect` of the product observable and the subtraction is a product
of
two single-observable `.expect`s, so all three terms are instances of `expect_boxBd`. The density is
`WilsonAction.wilsonDensity` and the observables are the one-plaquette `WilsonReal.wilsonPlaqObs`.

The statement is an identification of two expressions; nothing here is an estimate.

DERIVED: the signature writes no numeral; `β`, `Λ`, `ω`, `p₀` and `p` are the caller's and `4` is
the dimension carried by `ILink` and `IPlaq`, as in `iplqAll`. -/
theorem wilsonCorrConn_boxBd (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (p₀ p : ↥(iplqAll Λ)) :
    MassGap.WilsonBridge.wilsonCorrConn (Nc := N) (boxBd Λ) p₀ β p
      = specFree (φ := MassGap.WilsonAction.wilsonDensity) β Λ ω
          (fun u => MassGap.WilsonReal.wilsonPlaqObs (N := N) (boxBd Λ) p₀ u
            * MassGap.WilsonReal.wilsonPlaqObs (N := N) (boxBd Λ) p u)
        - specFree (φ := MassGap.WilsonAction.wilsonDensity) β Λ ω
            (fun u => MassGap.WilsonReal.wilsonPlaqObs (N := N) (boxBd Λ) p₀ u)
          * specFree (φ := MassGap.WilsonAction.wilsonDensity) β Λ ω
            (fun u => MassGap.WilsonReal.wilsonPlaqObs (N := N) (boxBd Λ) p u) := by
  unfold MassGap.WilsonBridge.wilsonCorrConn MassGap.WilsonBridge.wilsonCorr
  rw [expect_boxBd (ω := ω), expect_boxBd (ω := ω), expect_boxBd (ω := ω)]
  rfl

#print axioms wilsonCorrConn_boxBd

/-- Reflection positivity of the box's free-boundary state: `0 ≤ specFree β Λ ω (F · (F ∘ Θ))`, with
`Θ`
the abstract twist. The numerator is `wtFree_refl_pairing_nonneg` and the denominator is
`partFree_pos`. This is `InfiniteReflection.ReflPositiveOn`'s content at one finite volume.

DERIVED: the `2`s are the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling
in `hφ2`; the `0`s are the density's sign hypothesis and the lower bound concluded; `4` is the
dimension. -/
theorem specFree_refl_nonneg
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    (hFloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) → F U = F V)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    0 ≤ specFree (φ := φ) β Λ ω
      (fun u => F u * F (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
        (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)) := by
  refine div_nonneg ?_ (partFree_pos hφm hφ0 hφ2 β Λ ω).le
  exact wtFree_refl_pairing_nonneg hΛ hφm hφ0 hφ2 hφc β ω hFm hFloc hFb

#print axioms specFree_refl_nonneg

/-- The same with `f` a function of the whole lattice configuration and `Θ` the concrete lattice
reflection `ireflConf τ (2 * p)`, which is the form `InfiniteReflection.ReflPositiveOn` asks for.

`hfΛ`, locality to the box, is load-bearing: `splice_twist_eq_ireflConf` identifies the abstract
twist with `ireflConf` on `Λ` and says nothing off it, so an `f` that read outside the box would
distinguish the two. `InfiniteReflection.reflPositive_of_tendsto` holds its submodule `A` fixed
across the volumes for the same reason: `A` is observables local to one fixed finite region of the
positive half, and every large enough box contains that region.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling in
`hφ2`; the `0`s are the density's sign hypothesis and the lower bound concluded; `4` is the
dimension. -/
theorem specFree_refl_nonneg_of_local
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ}
    (hfm : Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω)))
    (hfΛ : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ l ∈ Λ, U l = V l) → f U = f V)
    (hfloc : ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) →
      f (MassGap.GibbsSpec.splice Λ U ω) = f (MassGap.GibbsSpec.splice Λ V ω))
    {CF : ℝ} (hfb : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      |f (MassGap.GibbsSpec.splice Λ u ω)| ≤ CF) :
    0 ≤ specFree (φ := φ) β Λ ω
      (fun u => f (MassGap.GibbsSpec.splice Λ u ω)
        * f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω))) := by
  have hkey : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      f (ireflConf τ (2 * p) (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω) := by
    intro u
    exact (hfΛ _ _ (fun l hl => splice_twist_eq_ireflConf hΛ ω u hl)).symm
  simp only [hkey]
  exact specFree_refl_nonneg hΛ hφm hφ0 hφ2 hφc β ω hfm hfloc hfb

#print axioms specFree_refl_nonneg_of_local

/-! ## 3g. The free-boundary expectation is a state -/

section StateAlgebra

open MeasureTheory MassGap.CompactGauge MassGap.LatticeReflection

/-- A bounded measurable observable against the free weight is integrable — bounded times bounded on
a
probability space, with `wtFree_le` supplying the weight's bound.

DERIVED: the `2` is the Wilson density's ceiling in `hφ2` and the `0` is its sign hypothesis `hφ0`;
the cardinality is the plaquette set's own. -/
theorem integrable_numFree {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hFm : Measurable F)
    {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF) :
    Integrable (fun u => F u * wtFree φ β Λ ω u)
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) := by
  refine MassGap.GibbsSpec.integrable_of_bounded _ (hFm.mul (measurable_wtFree hφm β Λ ω))
    (C := CF * Real.exp (|β| * (((iplqAll Λ).card : ℝ) * 2))) (fun u => ?_)
  rw [abs_mul]
  exact mul_le_mul (hFb u) (wtFree_le hφ0 hφ2 β Λ ω u) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hFb u))

#print axioms integrable_numFree

/-- `specFree` is additive on bounded measurable observables. Boundedness and measurability enter
through `integrable_numFree`, which `integral_add` requires.

DERIVED: the `2` is the Wilson density's ceiling in `hφ2` and the `0` is its sign hypothesis `hφ0`;
both are carried only to reach `partFree` and `integrable_numFree`. -/
theorem specFree_add {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F G : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ}
    (hFm : Measurable F) {CF : ℝ} (hFb : ∀ u, |F u| ≤ CF)
    (hGm : Measurable G) {CG : ℝ} (hGb : ∀ u, |G u| ≤ CG) :
    specFree (φ := φ) β Λ ω (fun u => F u + G u)
      = specFree (φ := φ) β Λ ω F + specFree (φ := φ) β Λ ω G := by
  unfold specFree
  rw [← add_div]
  congr 1
  rw [← integral_add (integrable_numFree hφm hφ0 hφ2 β Λ ω hFm hFb)
    (integrable_numFree hφm hφ0 hφ2 β Λ ω hGm hGb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))

#print axioms specFree_add

/-- `specFree` is homogeneous: a scalar pulls out of both the numerator and the quotient. No
integrability hypothesis is needed, so `φ` carries no range assumption here.

DERIVED: the signature writes no numeral. -/
theorem specFree_smul {φ : MassGap.SUN.SU N → ℝ} (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (c : ℝ)
    (F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ) :
    specFree (φ := φ) β Λ ω (fun u => c * F u) = c * specFree (φ := φ) β Λ ω F := by
  unfold specFree
  rw [← mul_div_assoc]
  congr 1
  simp only [mul_assoc]
  rw [integral_const_mul]

#print axioms specFree_smul

/-- `specFree` is normalised: the constant observable `1` gives `1`, the partition function divided
by
itself, which `partFree_pos` makes legitimate.

DERIVED: the `1`s are the constant observable's value and the normalised result; the `2` is the
Wilson density's ceiling in `hφ2` and the `0` is its sign hypothesis `hφ0`, both carried to reach
`partFree_pos`. -/
theorem specFree_one {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    specFree (φ := φ) β Λ ω (fun _ => 1) = 1 := by
  unfold specFree
  have h : (∫ u, (1 : ℝ) * wtFree φ β Λ ω u
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
      = partFree (φ := φ) β Λ ω := by
    unfold partFree
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => one_mul _))
  rw [h]
  exact div_self (partFree_pos hφm hφ0 hφ2 β Λ ω).ne'

#print axioms specFree_one

/-- `specFree` is positive: a pointwise nonnegative observable has a nonnegative value, since
`wtFree` is
strictly positive everywhere and the denominator is positive by `partFree_pos`.

DERIVED: the `0`s are the observable's sign hypothesis `hF`, the density's sign hypothesis `hφ0`,
and the sign concluded; the `2` is the Wilson density's ceiling in `hφ2`. -/
theorem specFree_nonneg {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {F : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ} (hF : ∀ u, 0 ≤ F u) :
    0 ≤ specFree (φ := φ) β Λ ω F := by
  refine div_nonneg ?_ (partFree_pos hφm hφ0 hφ2 β Λ ω).le
  exact integral_nonneg (fun u => mul_nonneg (hF u) (wtFree_pos φ β Λ ω u).le)

#print axioms specFree_nonneg

/-- The observable a continuous lattice function induces on the box is measurable —
`f.continuous.measurable` composed with `GibbsSpec.measurable_splice_left`.

DERIVED: the signature writes no numeral. -/
theorem boxObs_measurable {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω)) :=
  f.continuous.measurable.comp (MassGap.GibbsSpec.measurable_splice_left Λ ω)

/-- And it is bounded, because the configuration space is compact:
`InfiniteLattice.bounded_of_continuous` supplies the constant, which is stated as an existential
rather than computed.

DERIVED: the signature writes no numeral. -/
theorem boxObs_bounded {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    ∃ C : ℝ, ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      |f (MassGap.GibbsSpec.splice Λ u ω)| ≤ C := by
  obtain ⟨C, hC⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  exact ⟨C, fun u => hC _⟩

#print axioms boxObs_bounded

/-- The box's free-boundary state as a `DLRLimit.State` on `C(IConf (SU N), ℝ)` — the type
`InfiniteReflection.reflPositive_of_tendsto` consumes.

All four fields come from the section above: `map_add'` from `specFree_add`, `map_smul'` from
`specFree_smul`, `nonneg'` from `specFree_nonneg`, and `one'` from `specFree_one`. The bounds the
first and third need come from `boxObs_bounded` and `boxObs_measurable`.

DERIVED: the `2` in the hypotheses is the Wilson density's ceiling and the `0` its sign hypothesis,
both carried through to `partFree_pos`. -/
noncomputable def stateFree {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) where
  toFun := fun f => specFree (φ := φ) β Λ ω (fun u => f (MassGap.GibbsSpec.splice Λ u ω))
  map_add' := by
    intro f g
    obtain ⟨CF, hCF⟩ := boxObs_bounded (Λ := Λ) ω f
    obtain ⟨CG, hCG⟩ := boxObs_bounded (Λ := Λ) ω g
    exact specFree_add hφm hφ0 hφ2 β Λ ω (boxObs_measurable ω f) hCF
      (boxObs_measurable ω g) hCG
  map_smul' := by
    intro c f
    exact specFree_smul β Λ ω c (fun u => f (MassGap.GibbsSpec.splice Λ u ω))
  nonneg' := by
    intro f hf
    exact specFree_nonneg hφm hφ0 hφ2 β Λ ω (fun u => hf _)
  one' := specFree_one hφm hφ0 hφ2 β Λ ω

#print axioms stateFree

@[simp] theorem stateFree_apply {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    stateFree hφm hφ0 hφ2 β Λ ω f
      = specFree (φ := φ) β Λ ω (fun u => f (MassGap.GibbsSpec.splice Λ u ω)) := rfl

/-- `stateFree` at a box, applied to a continuous observable, is that observable read through
`splice`
and expected against `wilsonSystem (boxBd Λ) φ` — the finite Wilson system `StrongCoupling`'s
cluster expansion is stated over. `stateFree_apply` is the first half and is definitional;
`expect_boxBd` is the second and is not.

This converts between the two coordinate systems in this file: the carrier construction concludes
about `specFree`, and `gapAt_of_finite_volume_connected`'s `hfin` is about `stateFree`. The
statement is an equality of two expectations, not a bound.

DERIVED: the `0` and the `2` are `wilsonDensity`'s range, carried in as `hφ0` and `hφ2` exactly as
`stateFree` takes them; `β`, `Λ`, `ω` and `f` are the caller's. -/
theorem stateFree_eq_expect_boxBd {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (β : ℝ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    stateFree hφm hφ0 hφ2 β Λ ω f
      = (MassGap.WilsonLattice.wilsonSystem (boxBd Λ) φ).expect
          (probHaar (MassGap.SUN.SU N)) β
          (fun u => f (MassGap.GibbsSpec.splice Λ u ω)) := by
  rw [expect_boxBd φ β Λ ω]
  rfl

/-- At `β = 0` the free-boundary partition function is `1`: the weight is `1` by
`wtFree_at_zero_coupling` and `cvol` is a probability measure.

DERIVED: the `0` is the coupling; the `1` is the total mass of a probability measure. -/
theorem partFree_at_zero_coupling {φ : MassGap.SUN.SU N → ℝ}
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    partFree (φ := φ) 0 Λ ω = 1 := by
  unfold partFree
  simp [wtFree_at_zero_coupling]

#print axioms partFree_at_zero_coupling

/-- At `β = 0` the free-boundary kernel is the plain Haar integral: the weight is `1` and the
partition function is `1`, so nothing of the box's geometry survives.

DERIVED: the `0` is the coupling; the `1`s are the weight and the partition function. -/
theorem specFree_at_zero_coupling {φ : MassGap.SUN.SU N → ℝ}
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ → ℝ) :
    specFree (φ := φ) 0 Λ ω f
      = ∫ u, f u ∂(MassGap.ActionSplit.cvol ↑Λ (probHaar (MassGap.SUN.SU N))) := by
  unfold specFree
  rw [partFree_at_zero_coupling (φ := φ) Λ ω, div_one]
  simp [wtFree_at_zero_coupling]

#print axioms specFree_at_zero_coupling


#print axioms stateFree_eq_expect_boxBd

/-- **The free-boundary DLR consistency, at the level of the state.**

`num_free_spec_eq` equates the two numerators and `specFree` divides both by the same `partFree`, so
the states agree:

    stateFree Λ ω (kernel at V applied to f) = stateFree Λ ω f

**This is the `hev` hypothesis that `DLRLimit.isDLR_of_tendsto`, `tendsto_of_unique_dlr` and
`limits_eq_of_unique_dlr` all take**, and which the tree supplies for the FIXED-boundary family
through `GibbsSpec.wilson_dlr_consistent` but has not supplied for the FREE-boundary family — the one
the transfer construction actually consumes, and the one reflection positivity is proved for.

The kernel enters as `hg`, any continuous map agreeing with it pointwise, rather than as
`WilsonDLR.specCM`; that keeps this file's imports unchanged and lets the caller instantiate.

`hside` is the "`V` well inside `Λ`" condition, true for fixed `V` at all large boxes.

DERIVED: `1` is the identity at which the density vanishes; `0` and `2` are the density's range. -/
theorem stateFree_spec_eq {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (hφ1 : φ 1 = 0) (β : ℝ)
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (hside : ∀ q ∈ MassGap.GibbsSpec.boundaryPlaqs V, q.1.1 ≠ q.1.2 → q ∈ iplqAll Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hg : ∀ ω', g ω' = MassGap.GibbsSpec.spec φ β V (probHaar (MassGap.SUN.SU N)) (⇑f) ω')
    {C : ℝ}
    (hm1 : Measurable fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      MassGap.GibbsSpec.spec φ β V (probHaar (MassGap.SUN.SU N)) (⇑f)
        (MassGap.GibbsSpec.splice Λ u ω) * wtFree φ β Λ ω u)
    (hb1 : ∀ u, |MassGap.GibbsSpec.spec φ β V (probHaar (MassGap.SUN.SU N)) (⇑f)
        (MassGap.GibbsSpec.splice Λ u ω) * wtFree φ β Λ ω u| ≤ C)
    (hm2 : Measurable fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω) * wtFree φ β Λ ω u)
    (hb2 : ∀ u, |f (MassGap.GibbsSpec.splice Λ u ω) * wtFree φ β Λ ω u| ≤ C) :
    stateFree hφm hφ0 hφ2 β Λ ω g = stateFree hφm hφ0 hφ2 β Λ ω f := by
  show specFree (φ := φ) β Λ ω (fun u => g (MassGap.GibbsSpec.splice Λ u ω))
      = specFree (φ := φ) β Λ ω (fun u => f (MassGap.GibbsSpec.splice Λ u ω))
  unfold specFree
  congr 1
  have hgu : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      g (MassGap.GibbsSpec.splice Λ u ω)
        = MassGap.GibbsSpec.spec φ β V (probHaar (MassGap.SUN.SU N)) (⇑f)
          (MassGap.GibbsSpec.splice Λ u ω) := fun u => hg _
  simp only [hgu]
  exact num_free_spec_eq φ hφm hφ0 hφ2 hφ1 β hVΛ hside (probHaar (MassGap.SUN.SU N)) (⇑f) ω
    hm1 hb1 hm2 hb2

#print axioms stateFree_spec_eq

/-- **The free-boundary DLR consistency, with its side hypotheses discharged.**

`stateFree_spec_eq` takes measurability and boundedness of the two integrands; for a bounded
observable they are automatic. `GibbsSpec.abs_spec_le` puts the kernel in `[-1, 1]` and
`wtFree_le` bounds the weight, so both products are bounded by the weight's own ceiling;
measurability is `boxObs_measurable` for one integrand and `GibbsSpec.measurable_spec_right`
composed with `GibbsSpec.measurable_splice_left` for the other, each multiplied by
`measurable_wtFree`.

**This is the free-boundary `hev` in usable form.** The bound is arbitrary rather than fixed at one,
which matters: `DLRLimit.IsDLR` quantifies over ALL of `C(IConf G, ℝ)`, and specialising to `|f| ≤ 1`
would need the kernel's linearity in the observable to rescale — a lemma the tree does not have.
Every continuous observable on this compact configuration space is bounded, by
`InfiniteLattice.bounded_of_continuous`.

DERIVED: `1` is the identity at which the density vanishes and the bound assumed on the observable;
`0` and `2` are the density's range; the `2` in the weight's ceiling is `actionOn`'s own, from
`wtFree_le`. -/
theorem stateFree_spec_eq_of_bounded {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (hφ1 : φ 1 = 0) (β : ℝ)
    {V Λ : Finset MassGap.InfiniteLattice.ILink} (hVΛ : V ⊆ Λ)
    (hside : ∀ q ∈ MassGap.GibbsSpec.boundaryPlaqs V, q.1.1 ≠ q.1.2 → q ∈ iplqAll Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hg : ∀ ω', g ω' = MassGap.GibbsSpec.spec φ β V (probHaar (MassGap.SUN.SU N)) (⇑f) ω')
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hfb : ∀ U, |f U| ≤ C₀) :
    stateFree hφm hφ0 hφ2 β Λ ω g = stateFree hφm hφ0 hφ2 β Λ ω f := by
  have hfm : Measurable (⇑f) := f.continuous.measurable
  have hwm := measurable_wtFree hφm β Λ ω
  have hspecm : Measurable fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      MassGap.GibbsSpec.spec φ β V (probHaar (MassGap.SUN.SU N)) (⇑f)
        (MassGap.GibbsSpec.splice Λ u ω) :=
    (MassGap.GibbsSpec.measurable_spec_right hφm β V (probHaar (MassGap.SUN.SU N)) hfm).comp
      (MassGap.GibbsSpec.measurable_splice_left Λ ω)
  refine stateFree_spec_eq hφm hφ0 hφ2 hφ1 β hVΛ hside ω f g hg
    (C := C₀ * Real.exp (|β| * (((iplqAll Λ).card : ℝ) * 2)))
    (hspecm.mul hwm) ?_ ((boxObs_measurable ω f).mul hwm) ?_
  · intro u
    rw [abs_mul]
    exact mul_le_mul
      (MassGap.GibbsSpec.abs_spec_le hφm hφ0 hφ2 β V (probHaar (MassGap.SUN.SU N)) hfm hfb _)
      (wtFree_le hφ0 hφ2 β Λ ω u) (abs_nonneg _) hC₀
  · intro u
    rw [abs_mul]
    exact mul_le_mul (hfb _) (wtFree_le hφ0 hφ2 β Λ ω u) (abs_nonneg _) hC₀

#print axioms stateFree_spec_eq_of_bounded

/-- Reflection positivity of the finite-volume state in `InfiniteReflection`'s own form:
`ReflPositiveOn (latticeReflection τ (2 * p)) A (stateFree …)`. Built from
`specFree_refl_nonneg_of_local`, with `heq` turning `θ f * f` into the product this file's lemmas
carry.

`A` is a parameter. `InfiniteReflection.reflPositive_of_tendsto` requires `A` held fixed across the
volumes, so the caller that chooses the exhausting sequence of boxes chooses `A` too, and `A` must
be observables local to one fixed finite region of the positive half; constructing it here would pin
it to a single `Λ`.

`hAloc` is locality to the box, needed because the abstract twist and `ireflConf` agree only on `Λ`,
and `hAhalf` is the half-space reading `ActionSplit`'s `hOloc` asks for.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling in
`hφ2`; the `0`s are the density's sign hypothesis and the sign asserted; `4` is the dimension. -/
theorem reflPositiveOn_stateFree
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (A : Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hAloc : ∀ f ∈ A, ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ l ∈ Λ, U l = V l) → f U = f V)
    (hAhalf : ∀ f ∈ A, ∀ U V : ↥Λ → MassGap.SUN.SU N,
      (∀ i ∈ boxS τ p Λ, U i = V i) → (∀ i ∈ boxR τ p Λ, U i = V i) →
      f (MassGap.GibbsSpec.splice Λ U ω) = f (MassGap.GibbsSpec.splice Λ V ω)) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) A
      (stateFree hφm hφ0 hφ2 β Λ ω) := by
  intro f hf
  obtain ⟨CF, hCF⟩ := boxObs_bounded (Λ := Λ) ω f
  have hkey := specFree_refl_nonneg_of_local hΛ hφm hφ0 hφ2 hφc β ω
    (boxObs_measurable ω f) (hAloc f hf) (hAhalf f hf) hCF
  show (0 : ℝ) ≤ specFree (φ := φ) β Λ ω
    (fun u => ((MassGap.LatticeReflection.latticeReflection τ (2 * p)).θ f * f)
      (MassGap.GibbsSpec.splice Λ u ω))
  have heq : (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      ((MassGap.LatticeReflection.latticeReflection τ (2 * p)).θ f * f)
        (MassGap.GibbsSpec.splice Λ u ω))
      = fun u => f (MassGap.GibbsSpec.splice Λ u ω)
          * f (MassGap.LatticeReflection.ireflConf τ (2 * p)
                (MassGap.GibbsSpec.splice Λ u ω)) := by
    funext u
    exact mul_comm _ _
  rw [heq]
  exact hkey

#print axioms reflPositiveOn_stateFree

/-- Reflection positivity of an infinite-volume state `ν`, from a family of reflection-stable boxes
`box : ι → Finset ILink` whose free-boundary states converge to `ν` along a `NeBot` filter.
`InfiniteReflection.reflPositive_of_tendsto` applied to `reflPositiveOn_stateFree` at each box.

The convergence is the hypothesis `htend`; this does not construct the limit state and does not
show any sequence converges. Apart from `htend` the hypotheses are `hbox`, the density's range and
class-function property, and the two locality conditions on `A`; there is no second positivity
assumption and no condition on the filter beyond `NeBot`.

`A` is held fixed across the volumes, which is why `hAloc` is quantified over the family:
observables local to one fixed finite region of the positive half are local to every box containing
it.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling in
`hφ2`; the `0` is the density's sign hypothesis `hφ0`; `4` is the dimension. -/
theorem reflPositive_limit_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (A : Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hAloc : ∀ i, ∀ f ∈ A, ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ box i, U lk = V lk) → f U = f V)
    (hAhalf : ∀ i, ∀ f ∈ A, ∀ U V : ↥(box i) → MassGap.SUN.SU N,
      (∀ j ∈ boxS τ p (box i), U j = V j) → (∀ j ∈ boxR τ p (box i), U j = V j) →
      f (MassGap.GibbsSpec.splice (box i) U ω) = f (MassGap.GibbsSpec.splice (box i) V ω))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) A ν :=
  MassGap.InfiniteReflection.reflPositive_of_tendsto htend _ A
    (Filter.Eventually.of_forall (fun i =>
      reflPositiveOn_stateFree (hbox i) hφm hφ0 hφ2 hφc β ω A (hAloc i) (hAhalf i)))

#print axioms reflPositive_limit_of_tendsto

/-- Reflection positivity of an infinite-volume state of the Wilson measure on `ℤ⁴`, with no
convergence
hypothesis. `DLRLimit.exists_limit_state` supplies, for any `NeBot` filter and any family of states,
an ultrafilter refining it together with a state to which every observable converges — one compact
interval per observable. So the limit is produced here rather than assumed, and
`reflPositive_limit_of_tendsto` is applied to it.

The caller supplies a family of boxes each stable under the link reflection at `2 * p`, and a fixed
submodule `A` of observables local to the boxes and reading the positive half. The Wilson density
satisfies `hφm`, `hφ0`, `hφ2` and `hφc`.

Scope: the limit is along an ultrafilter refining `l`, so it is subsequential; it is not claimed to
be the DLR state nor to be translation invariant. What is concluded is `ReflPositiveOn` for the
limit, on `A`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling in
`hφ2`; the `0` is the density's sign hypothesis `hφ0`; `4` is the dimension. -/
theorem reflPositive_limit_exists
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (A : Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hAloc : ∀ i, ∀ f ∈ A, ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ box i, U lk = V lk) → f U = f V)
    (hAhalf : ∀ i, ∀ f ∈ A, ∀ U V : ↥(box i) → MassGap.SUN.SU N,
      (∀ j ∈ boxS τ p (box i), U j = V j) → (∀ j ∈ boxR τ p (box i), U j = V j) →
      f (MassGap.GibbsSpec.splice (box i) U ω) = f (MassGap.GibbsSpec.splice (box i) V ω)) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) A ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state l (fun i => stateFree hφm hφ0 hφ2 β (box i) ω)
  haveI : (u : Filter ι).NeBot := u.neBot'
  exact ⟨u, ν, hle, htend,
    reflPositive_limit_of_tendsto τ p box hbox hφm hφ0 hφ2 hφc β ω A hAloc hAhalf ν htend⟩

#print axioms reflPositive_limit_exists

/-- The observables depending on a fixed finite region `R₀` only, as a `Submodule ℝ C(X, ℝ)` — the
type
`InfiniteReflection.ReflPositiveOn` asks for. `InfiniteLattice.localAlg` is the same notion as a
`Subalgebra ℝ (IConf G → ℝ)` over raw functions, which is the wrong type here.

At `R₀ = ∅` the carrier reads `∀ U V, f U = f V`, so the submodule is exactly the constants.

DERIVED: the signature writes no numeral; `R₀` is the caller's fixed region and `4` is the
dimension. -/
def localSubmodule (R₀ : Finset MassGap.InfiniteLattice.ILink) :
    Submodule ℝ C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ) where
  carrier := {f | ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
    (∀ lk ∈ R₀, U lk = V lk) → f U = f V}
  add_mem' := by
    intro f g hf hg U V h
    show f U + g U = f V + g V
    rw [hf U V h, hg U V h]
  zero_mem' := by intro U V _; rfl
  smul_mem' := by
    intro c f hf U V h
    show c * f U = c * f V
    rw [hf U V h]

theorem mem_localSubmodule {R₀ : Finset MassGap.InfiniteLattice.ILink}
    {f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)} :
    f ∈ localSubmodule R₀ ↔ ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ R₀, U lk = V lk) → f U = f V := Iff.rfl

#print axioms localSubmodule

/-- `reflPositive_limit_exists` with the submodule supplied rather than assumed, so the conclusion
is
not satisfiable by `⊥`. The caller fixes a finite region `R₀` of links lying at or above the plane
(`hR₀`) and a family of reflection-stable boxes each containing it (`hsub`, `hbox`).

`R₀` is fixed first and every box contains it, which is what `reflPositive_of_tendsto` needs of a
submodule held fixed across volumes, and it is why the two locality hypotheses of
`reflPositive_limit_exists` are discharged here: locality to the box because `R₀` is inside it, and
the half-space reading because every link of `R₀` lands in `boxS ∪ boxR`.

Scope: `localSubmodule R₀` is one fixed finite support, where `HalfSpaceAlgebra.halfSpaceAlg τ p` is
a directed union over all finite supports in the positive half; positivity on the former is weaker.
`reflPositive_limit_on_halfSpaceAlg` below states the union, trading the `∀ i` quantifier for an
eventual one (`InfiniteReflection.reflPositive_of_eventually_pointwise`) and choosing the fixed
region per observable, in exchange for an exhaustion hypothesis on the box family that this
statement does not take. At `R₀ = ∅` the submodule is the constants and every hypothesis holds
vacuously, so the content rests on `R₀` and on the convergence clause, which is what ties `ν` to the
Wilson measure. `HalfSpaceAlgebra.halfLinkObs_mem` puts `halfLinkObs l f` in `halfSpaceAlg` for
every link `l` of the half-space and every `f : C(G, ℝ)`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling in
`hφ2`; the `0` is the density's sign hypothesis `hφ0`; `4` is the dimension. -/
theorem reflPositive_limit_on_half_space
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (R₀ : Finset MassGap.InfiniteLattice.ILink)
    (hR₀ : ∀ lk ∈ R₀, (ireflLink τ (2 * p) lk).2 τ ≤ lk.2 τ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hsub : ∀ i, R₀ ⊆ box i)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) (localSubmodule R₀) ν := by
  obtain ⟨u, ν, hle, htend, hrp⟩ :=
    reflPositive_limit_exists l τ p box hbox hφm hφ0 hφ2 hφc β ω (localSubmodule R₀)
      (fun i f hf U V h => hf U V (fun lk hlk => h lk (hsub i hlk)))
      (fun i f hf U V hS hR => by
        refine hf _ _ (fun lk hlk => ?_)
        have hlΛ : lk ∈ box i := hsub i hlk
        rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
        rcases lt_or_eq_of_le (hR₀ lk hlk) with hlt | heq
        · exact hS _ (by simp only [boxS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt)
        · exact hR _ (by simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]; exact heq))
  exact ⟨u, ν, hle, htend, hrp⟩

#print axioms reflPositive_limit_on_half_space

/-! ## 6′. B3 on the directed union -/

/-- A link of `posHalf τ p` reflects to or below itself in the `τ` coordinate:
`reflection_exchanges_halves` puts the image at or below the plane and membership puts the link at
or
above it. This is the `hR₀` that `reflPositive_limit_on_half_space` takes as a hypothesis; for a
half-space support it is a theorem.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; `4` is the dimension. -/
theorem irefl_le_self_of_posHalf (τ : Fin 4) (p : ℤ) {lk : ILink} (hlk : lk ∈ posHalf τ p) :
    (ireflLink τ (2 * p) lk).2 τ ≤ lk.2 τ := by
  have h1 : (ireflLink τ (2 * p) lk).2 τ ≤ p := reflection_exchanges_halves τ p hlk
  have h2 : p ≤ lk.2 τ := hlk
  omega

#print axioms irefl_le_self_of_posHalf

/-- Reflection positivity of the finite-volume state at one observable of the directed union:
`0 ≤ stateFree … ((latticeReflection τ (2 * p)).θ f * f)` for an `f` whose finite support `S` lies
in
`posHalf τ p` and inside the box.

`reflPositiveOn_stateFree` needs a submodule every member of which is local to the box, and
`halfSpaceAlg` is not one. A member of `halfSpaceAlg` carries its own finite support, so the fixed
region that fits it is `localSubmodule S`, chosen per observable rather than once for the algebra.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling in
`hφ2`; the `0`s are the density's sign hypothesis and the sign asserted; `4` is the dimension. -/
theorem stateFree_refl_nonneg_of_halfSpace_support
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p) l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (S : Finset ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    0 ≤ stateFree hφm hφ0 hφ2 β Λ ω
      ((MassGap.LatticeReflection.latticeReflection τ (2 * p)).θ f * f) :=
  reflPositiveOn_stateFree hΛ hφm hφ0 hφ2 hφc β ω (localSubmodule S)
    (fun g hg U V h => hg U V (fun lk hlk => h lk (hSΛ hlk)))
    (fun g hg U V hSb hRb => by
      refine hg _ _ (fun lk hlk => ?_)
      have hlΛ : lk ∈ Λ := hSΛ hlk
      rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
      rcases lt_or_eq_of_le
          (irefl_le_self_of_posHalf τ p (hS (Finset.mem_coe.mpr hlk))) with hlt | heq
      · exact hSb _ (by simp only [boxS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt)
      · exact hRb _ (by simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]; exact heq))
    f hf

#print axioms stateFree_refl_nonneg_of_halfSpace_support

/-- The all-identity configuration is fixed by `ireflConf τ c` at every constant `c`: the map
inverts on
`τ`-links and does nothing elsewhere, and `1⁻¹ = 1`. So one boundary condition serves two box
families with different mirrors.

DERIVED: the `1` is the group identity; `4` is the dimension. -/
theorem ireflConf_one (τ : Fin 4) (c : ℤ) :
    MassGap.LatticeReflection.ireflConf τ c
        (1 : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) = 1 := by
  funext l
  by_cases h : l.1 = τ <;>
    simp [MassGap.LatticeReflection.ireflConf, h]

#print axioms ireflConf_one

/-- `Re tr` as a bundled `C(SU N, ℝ)`, at every rank. `HaarVariance.reTr` is the function and
`HaarVariance.continuous_reTr` its continuity; this bundles them because
`HalfSpaceAlgebra.halfLinkObs` takes a `C(G, ℝ)`.

DERIVED: the signature writes no numeral; `N` is the caller's rank. -/
noncomputable def reTrCM (N : ℕ) : C(MassGap.SUN.SU N, ℝ) :=
  ⟨MassGap.HaarVariance.reTr, MassGap.HaarVariance.continuous_reTr⟩

#print axioms reTrCM

/-- `reTrCM` separates `HaarVariance.flipEl m` from `1` in `SU (m + 2)`, which is the hypothesis
`HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` takes.
`HaarVariance.reTr_flipEl_ne_reTr_one` is the content: `Re tr` reads `m + 2` at the identity and
`m - 2` at `flipEl m`.

The rank is written `m + 2` rather than `N` with a side condition, because at `SU 0` and `SU 1` the
group is a singleton and no two elements exist to separate.

DERIVED: the `2` is the least matrix dimension at which two group elements exist to separate; the
`1` is the identity, the element `flipEl` is separated from; `m` is the caller's. -/
theorem reTrCM_separating (m : ℕ) :
    reTrCM (m + 2) (MassGap.HaarVariance.flipEl m) ≠ reTrCM (m + 2) 1 :=
  MassGap.HaarVariance.reTr_flipEl_ne_reTr_one m

#print axioms reTrCM_separating

/-- `HalfSpaceAlgebra.halfSpaceAlg τ p` contains a non-constant observable at every `SU (m + 2)`:
the
witness is `halfLinkObs l₀ (reTrCM (m + 2))` at a link `l₀` based on the plane, and the two
configurations separating it are the constant `flipEl m` and the constant `1`.

`HalfSpaceAlgebra.halfLinkObs_mem` alone does not give this: it is quantified over an arbitrary
`f : C(G, ℝ)`, and a constant `f` gives a constant member. The separating function is `reTrCM` and
the separated pair is `reTrCM_separating`, which is `HaarVariance.reTr_flipEl_ne_reTr_one`.

Scope: false at `SU 0` and `SU 1`, where the group is a singleton, every observable is constant and
the carrier is the constants. That is why the rank is written `m + 2`.

DERIVED: the `2` is the least rank at which two group elements exist to separate; `m` is the
caller's; the `-1` reached in the proof is `HaarVariance.reTr_flipEl`'s computed value; `4` is the
spacetime dimension. -/
theorem halfSpaceAlg_has_nonconstant_of_rank_two (m : ℕ) (τ : Fin 4) (p : ℤ) :
    ∃ F ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU (m + 2)) τ p,
      ∃ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU (m + 2)), F U ≠ F V := by
  classical
  set l₀ : MassGap.InfiniteLattice.ILink := ((0 : Fin 4), fun _ => p) with hl₀
  have hmem : l₀ ∈ MassGap.HalfSpaceAlgebra.posHalf τ p := le_refl p
  exact ⟨MassGap.HalfSpaceAlgebra.halfLinkObs l₀ (reTrCM (m + 2)),
    MassGap.HalfSpaceAlgebra.halfLinkObs_mem τ p hmem (reTrCM (m + 2)),
    (fun _ => MassGap.HaarVariance.flipEl m), 1, reTrCM_separating m⟩

#print axioms halfSpaceAlg_has_nonconstant_of_rank_two

/-- The same at `SU 3`, which is `m = 1` in `halfSpaceAlg_has_nonconstant_of_rank_two`. At `SU 3`,
`CrossingIntegration.trace_gNeg` computes `Re tr gNeg = -1` against `Re tr 1 = 3` for such a pair.

DERIVED: `3` is the matrix dimension of `SU 3` — its rank is `2`; `1` is the `m` that gives it; `4`
is the spacetime dimension. -/
theorem halfSpaceAlg_has_nonconstant (τ : Fin 4) (p : ℤ) :
    ∃ F ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU 3) τ p,
      ∃ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3), F U ≠ F V :=
  halfSpaceAlg_has_nonconstant_of_rank_two 1 τ p

#print axioms halfSpaceAlg_has_nonconstant

/-- No non-empty finite box is stable under two adjacent mirrors: `h0` at `a` and `h1` at `a + 1`
force
`Λ = ∅`.

Three steps. `ReflectionShift.ireflLink_comp_succ` composes the two mirrors into one link shift, so
a doubly stable box is shift-stable; the shift orbit of any member stays inside it; and the orbit is
injective because `InfiniteShift.ishift_iterate` moves the `τ` coordinate by the step count. An
infinite injective image inside a `Finset` is the contradiction.

Scope: this is about a finite-volume box carrying both invariances. It says nothing about the
infinite-volume state.

DERIVED: the `1` is the mirror separation, which is what makes the composite a single lattice step;
`4` is the dimension. -/
theorem eq_empty_of_stable_two_mirrors (τ : Fin 4) (a : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (h0 : ∀ l ∈ Λ, ireflLink τ a l ∈ Λ)
    (h1 : ∀ l ∈ Λ, ireflLink τ (a + 1) l ∈ Λ) :
    Λ = ∅ := by
  by_contra hne
  obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hshift : ∀ m ∈ Λ, MassGap.InfiniteShift.ishiftLink τ m ∈ Λ := by
    intro m hm
    rw [← MassGap.ReflectionShift.ireflLink_comp_succ τ a m]
    exact h1 _ (h0 m hm)
  have horb : ∀ k : ℕ, (MassGap.InfiniteShift.ishiftLink τ)^[k] l ∈ Λ := by
    intro k
    induction k with
    | zero => simpa using hl
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact hshift _ ih
  have hinj : Function.Injective
      (fun k : ℕ => (MassGap.InfiniteShift.ishiftLink τ)^[k] l) := by
    intro k m hkm
    have h := congrArg (fun q : MassGap.InfiniteLattice.ILink => q.2 τ) hkm
    simp only [MassGap.InfiniteShift.ishiftLink_iterate,
      MassGap.InfiniteShift.ishift_iterate] at h
    omega
  have hsub : Set.range (fun k : ℕ => (MassGap.InfiniteShift.ishiftLink τ)^[k] l)
      ⊆ (Λ : Set MassGap.InfiniteLattice.ILink) := by
    rintro x ⟨k, rfl⟩
    exact horb k
  exact (Set.infinite_range_of_injective hinj) (Λ.finite_toSet.subset hsub)

#print axioms eq_empty_of_stable_two_mirrors

/-- Mirrors two apart compose to a double shift:
`ireflLink τ (a + 2) ∘ ireflLink τ a = ishiftLink τ ∘ ishiftLink τ`.
`ReflectionShift.ireflLink_comp_succ` composes adjacent mirrors into one shift, and inserting
`ireflLink_involutive` at the midpoint `a + 1` applies it twice.

DERIVED: the `2` is the mirror separation this composes; the `1` is the midpoint the involution is
inserted at; `4` is the dimension. -/
theorem ireflLink_comp_add_two (τ : Fin 4) (a : ℤ) (l : MassGap.InfiniteLattice.ILink) :
    ireflLink τ (a + 2) (ireflLink τ a l)
      = MassGap.InfiniteShift.ishiftLink τ (MassGap.InfiniteShift.ishiftLink τ l) := by
  have hmid : ireflLink τ (a + 1) (ireflLink τ (a + 1) (ireflLink τ a l))
      = ireflLink τ a l := MassGap.LatticeReflection.ireflLink_involutive τ (a + 1) _
  have ha2 : a + 2 = a + 1 + 1 := by ring
  calc ireflLink τ (a + 2) (ireflLink τ a l)
      = ireflLink τ (a + 1 + 1)
          (ireflLink τ (a + 1) (ireflLink τ (a + 1) (ireflLink τ a l))) := by
        rw [hmid, ha2]
    _ = ireflLink τ (a + 1 + 1)
          (ireflLink τ (a + 1) (MassGap.InfiniteShift.ishiftLink τ l)) := by
        rw [MassGap.ReflectionShift.ireflLink_comp_succ τ a l]
    _ = MassGap.InfiniteShift.ishiftLink τ (MassGap.InfiniteShift.ishiftLink τ l) :=
        MassGap.ReflectionShift.ireflLink_comp_succ τ (a + 1) _

#print axioms ireflLink_comp_add_two

/-- No non-empty finite box is stable under two mirrors two apart either: `h0` at `a` and `h2` at
`a + 2` force `Λ = ∅`. `ireflLink_comp_add_two` makes the composite a double shift, and the rest is
`eq_empty_of_stable_two_mirrors`'s argument on the doubled orbit.

`eq_empty_of_stable_two_mirrors` covers the adjacent pair `(a, a + 1)`, which at `a = 2p - 1` is the
reflection-positivity pair `(2p - 1, 2p)`. `gapAt_of_finite_volume_connected` compares the constants
`2p - 2` and `2p`, which is the separation this statement covers.

Scope: this is about a finite-volume box carrying both invariances. A box stable under the `2p`
mirror alone is what the reflection-positivity construction uses, and `symCube` provides one.

DERIVED: the `2` is the mirror separation; `4` is the dimension. -/
theorem eq_empty_of_stable_two_mirrors_step_two (τ : Fin 4) (a : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (h0 : ∀ l ∈ Λ, ireflLink τ a l ∈ Λ)
    (h2 : ∀ l ∈ Λ, ireflLink τ (a + 2) l ∈ Λ) :
    Λ = ∅ := by
  by_contra hne
  obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hshift : ∀ m ∈ Λ, (MassGap.InfiniteShift.ishiftLink τ)^[2] m ∈ Λ := by
    intro m hm
    have : (MassGap.InfiniteShift.ishiftLink τ)^[2] m
        = ireflLink τ (a + 2) (ireflLink τ a m) := by
      rw [ireflLink_comp_add_two τ a m]
      simp [Function.iterate_succ_apply']
    rw [this]
    exact h2 _ (h0 m hm)
  have horb : ∀ k : ℕ, (MassGap.InfiniteShift.ishiftLink τ)^[2 * k] l ∈ Λ := by
    intro k
    induction k with
    | zero => simpa using hl
    | succ i ih =>
        have hstep : 2 * (i + 1) = 2 + 2 * i := by ring
        rw [hstep, Function.iterate_add_apply]
        exact hshift _ ih
  have hinj : Function.Injective
      (fun k : ℕ => (MassGap.InfiniteShift.ishiftLink τ)^[2 * k] l) := by
    intro k m hkm
    have h := congrArg (fun q : MassGap.InfiniteLattice.ILink => q.2 τ) hkm
    simp only [MassGap.InfiniteShift.ishiftLink_iterate,
      MassGap.InfiniteShift.ishift_iterate] at h
    omega
  have hsub : Set.range (fun k : ℕ => (MassGap.InfiniteShift.ishiftLink τ)^[2 * k] l)
      ⊆ (Λ : Set MassGap.InfiniteLattice.ILink) := by
    rintro x ⟨k, rfl⟩
    exact horb k
  exact (Set.infinite_range_of_injective hinj) (Λ.finite_toSet.subset hsub)

#print axioms eq_empty_of_stable_two_mirrors_step_two

/-! ### The odd constant's block structure — the even one with the fixed set flipped -/

/-- The positive half of `Λ` at an arbitrary reflection constant `c`: the links the reflection moves
down in the `τ` coordinate. `iblkS` is this at `c = 2 * p`.

Classifying by the reflection's own action makes the three blocks disjoint by trichotomy, with no
case split on the link's direction, and that argument does not read the parity of `c`.

Parity does enter membership. A `τ`-link reflects about `c - 1` and a transverse one about `c`, so
they enter `ioblkS` at `2 x_τ > c - 1` and at `2 x_τ > c`; those thresholds coincide only when
`2 x_τ ≠ c` can be assumed, that is at odd `c`. At even `c` a plaquette of `ioplqPlus` can have a
boundary link in `ioblkR`, which is why the even chain's `iplqPlus_links_mem` concludes
`boxS ∪ boxR` rather than `boxS`. A locality statement built on these blocks carries `c` odd.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioblkS (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.InfiniteLattice.ILink :=
  Λ.filter (fun l => (ireflLink τ c l).2 τ < l.2 τ)

/-- The negative half at an arbitrary constant: moved up in the `τ` coordinate.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioblkT (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.InfiniteLattice.ILink :=
  Λ.filter (fun l => l.2 τ < (ireflLink τ c l).2 τ)

/-- The shared block at an arbitrary constant: not moved in the `τ` coordinate.

Its content depends on the parity of `c`. At an even constant it holds the transverse links lying in
the plane, and the twist does not invert them; at an odd one it holds the axis links straddling the
mirror, and the twist does invert them (`odd_tau_fixed_iff`,
`LatticeReflection.ireflConf_inverts_fixed_axis_link`). The definition is the same either way.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioblkR (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.InfiniteLattice.ILink :=
  Λ.filter (fun l => (ireflLink τ c l).2 τ = l.2 τ)

#print axioms ioblkS

/-- The three blocks are pairwise disjoint, by trichotomy on `ℤ`, at any constant.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioblk_disjoint (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (ioblkS τ c Λ) (ioblkT τ c Λ)
      ∧ Disjoint (ioblkS τ c Λ) (ioblkR τ c Λ)
      ∧ Disjoint (ioblkT τ c Λ) (ioblkR τ c Λ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine Finset.disjoint_left.2 fun l h1 h2 => ?_ <;>
      simp only [ioblkS, ioblkT, ioblkR, Finset.mem_filter] at h1 h2 <;>
        omega

#print axioms ioblk_disjoint

/-- And they exhaust the box: `ioblkS ∪ ioblkT ∪ ioblkR = Λ`, again by trichotomy.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioblk_union (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    ioblkS τ c Λ ∪ ioblkT τ c Λ ∪ ioblkR τ c Λ = Λ := by
  classical
  ext l
  simp only [Finset.mem_union, ioblkS, ioblkT, ioblkR, Finset.mem_filter]
  constructor
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  · intro hl
    rcases lt_trichotomy ((ireflLink τ c l).2 τ) (l.2 τ) with h | h | h
    · exact Or.inl (Or.inl ⟨hl, h⟩)
    · exact Or.inr ⟨hl, h⟩
    · exact Or.inl (Or.inr ⟨hl, h⟩)

#print axioms ioblk_union

/-- The reflection carries `ioblkS` into `ioblkT` at any constant: `ireflLink` is an involution, so
a
link moved down has an image moved up. Takes the box's stability `hΛ`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflLink_ioblkS_mem_ioblkT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkS τ c Λ) : ireflLink τ c l ∈ ioblkT τ c Λ := by
  simp only [ioblkS, Finset.mem_filter] at hl
  simp only [ioblkT, Finset.mem_filter]
  refine ⟨hΛ l hl.1, ?_⟩
  rw [ireflLink_involutive τ c l]
  exact hl.2

#print axioms ireflLink_ioblkS_mem_ioblkT

/-- And back: `ioblkT` into `ioblkS`. `Finset.sum_nbij'` needs the map in both directions, and the
 lemma above supplies one.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflLink_ioblkT_mem_ioblkS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkT τ c Λ) : ireflLink τ c l ∈ ioblkS τ c Λ := by
  simp only [ioblkT, Finset.mem_filter] at hl
  simp only [ioblkS, Finset.mem_filter]
  refine ⟨hΛ l hl.1, ?_⟩
  rw [ireflLink_involutive τ c l]
  exact hl.2

#print axioms ireflLink_ioblkT_mem_ioblkS

/-- A link whose `τ` coordinate the reflection leaves fixed is fixed outright, at every constant:
`ireflSite` touches the `τ` coordinate and nothing else. Parity enters nowhere.

This is the `hθR` the downstream pairing lemmas take —
`ActionSplit.pairing_nonneg_of_local` needs the reflection to fix the shared block pointwise before
it integrates over it.

DERIVED: the `1` is `ireflLink`'s link-length offset; `c` is the caller's constant; `4` is the
dimension. -/
theorem irefl_eq_self_of_coord_eq (τ : Fin 4) (c : ℤ)
    {l : MassGap.InfiniteLattice.ILink}
    (hcoord : (ireflLink τ c l).2 τ = l.2 τ) : ireflLink τ c l = l := by
  refine Prod.ext rfl ?_
  by_cases h : l.1 = τ
  · show (if l.1 = τ then ireflSite τ (c - 1) l.2 else ireflSite τ c l.2) = l.2
    rw [if_pos h]
    simp only [ireflLink, if_pos h, ireflSite_axis] at hcoord
    funext j
    by_cases hj : j = τ
    · subst hj
      simp only [ireflSite, Function.update_self]
      omega
    · simp [ireflSite, Function.update_of_ne hj]
  · show (if l.1 = τ then ireflSite τ (c - 1) l.2 else ireflSite τ c l.2) = l.2
    rw [if_neg h]
    simp only [ireflLink, if_neg h, ireflSite_axis] at hcoord
    funext j
    by_cases hj : j = τ
    · subst hj
      simp only [ireflSite, Function.update_self]
      omega
    · simp [ireflSite, Function.update_of_ne hj]

#print axioms irefl_eq_self_of_coord_eq

/-- The block form of `irefl_eq_self_of_coord_eq`, which is how a caller usually has it.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem irefl_eq_self_of_mem_ioblkR (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkR τ c Λ) : ireflLink τ c l = l :=
  irefl_eq_self_of_coord_eq τ c (Finset.mem_filter.mp hl).2

#print axioms irefl_eq_self_of_mem_ioblkR

/-! ### The same three blocks at the box-subtype index -/

/-- The positive half at the box-subtype index. `ioblkS` is over `ILink`, and every locality
hypothesis
downstream is over `↥Λ`, so both indexings are carried. `boxS` is this at `c = 2 * p`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def oboxS (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ c l.1).2 τ < l.1.2 τ)

/-- The negative half at the box-subtype index.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def oboxT (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => l.1.2 τ < (ireflLink τ c l.1).2 τ)

/-- The shared block at the box-subtype index.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def oboxR (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) : Finset ↥Λ :=
  Finset.univ.filter (fun l : ↥Λ => (ireflLink τ c l.1).2 τ = l.1.2 τ)

#print axioms oboxS

/-- The two indexings of the positive block agree: `ioblkS` filters `Λ` and `oboxS` filters the
subtype
with the same predicate.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem mem_oboxS_of_mem_ioblkS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ ioblkS τ c Λ) :
    (⟨l, (Finset.mem_filter.mp hl).1⟩ : ↥Λ) ∈ oboxS τ c Λ :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩

#print axioms mem_oboxS_of_mem_ioblkS

/-- `hθR` at the box-subtype index: `ireflBoxPerm hΛ` fixes every element of `oboxR τ c Λ`, from
`irefl_eq_self_of_coord_eq` by `Subtype.ext`. Holds at any constant.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflBoxPerm_eq_self_of_mem_oboxR (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : ↥Λ} (hl : l ∈ oboxR τ c Λ) :
    ireflBoxPerm hΛ l = l := by
  refine Subtype.ext ?_
  rw [ireflBoxPerm_coe]
  exact irefl_eq_self_of_coord_eq τ c
    (by simpa only [oboxR, Finset.mem_filter, Finset.mem_univ, true_and] using hl)

#print axioms ireflBoxPerm_eq_self_of_mem_oboxR

/-- The box permutation carries `oboxS` into `oboxT` — the `hSmap` the pairing lemmas take, at any
constant.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflBoxPerm_mem_oboxT_of_mem_oboxS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : ↥Λ} (hl : l ∈ oboxS τ c Λ) :
    ireflBoxPerm hΛ l ∈ oboxT τ c Λ := by
  simp only [oboxS, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  simp only [oboxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ireflBoxPerm_coe, ireflLink_involutive τ c l.1]
  exact hl

#print axioms ireflBoxPerm_mem_oboxT_of_mem_oboxS

/-- And back, `oboxT` into `oboxS`, which the mirror bijection needs for its inverse.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflBoxPerm_mem_oboxS_of_mem_oboxT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {l : ↥Λ} (hl : l ∈ oboxT τ c Λ) :
    ireflBoxPerm hΛ l ∈ oboxS τ c Λ := by
  simp only [oboxT, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  simp only [oboxS, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ireflBoxPerm_coe, ireflLink_involutive τ c l.1]
  exact hl

#print axioms ireflBoxPerm_mem_oboxS_of_mem_oboxT

/-- The bijection `↥(oboxT τ c Λ) ≃ ↥(oboxS τ c Λ)` given by the reflection. `ireflBoxPerm` is an
`Equiv.Perm` built from an involution, so the two directions are each other's inverse with no
computation. The `ℤ⁴` counterpart of `OddLagSplit.mirrorEquivTS`.

This is the relabelling of indices only. Transporting configurations carries the dagger as well,
since the reflection inverts on `τ`-links; `omirrorT` is that map and
`measurePreserving_omirrorT` is where inversion-invariance of Haar is used.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def omirrorEquivTS (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) :
    ↥(oboxT τ c Λ) ≃ ↥(oboxS τ c Λ) where
  toFun := fun l => ⟨ireflBoxPerm hΛ l.1, ireflBoxPerm_mem_oboxS_of_mem_oboxT τ c hΛ l.2⟩
  invFun := fun l => ⟨ireflBoxPerm hΛ l.1, ireflBoxPerm_mem_oboxT_of_mem_oboxS τ c hΛ l.2⟩
  left_inv := fun l => Subtype.ext (ireflBox_involutive hΛ l.1)
  right_inv := fun l => Subtype.ext (ireflBox_involutive hΛ l.1)

#print axioms omirrorEquivTS

/-- The mirror block's variable written as a variable of the positive half: relabel by
`omirrorEquivTS` and invert on `τ`-links, which is the same `σ` that `ireflConf` carries restricted
to the mirror block. The `ℤ⁴` counterpart of `OddLagSplit.mirrorT`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
noncomputable def omirrorT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (y : ↥(oboxS τ c Λ) → MassGap.SUN.SU N) : ↥(oboxT τ c Λ) → MassGap.SUN.SU N :=
  fun l => if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ
    then (y (omirrorEquivTS τ c hΛ l))⁻¹
    else y (omirrorEquivTS τ c hΛ l)

#print axioms omirrorT

/-- `omirrorT` preserves product Haar: relabelling by a bijection of index sets and inverting on
some
coordinates. Haar on a compact group is inversion-invariant, so every coordinate map preserves its
factor, and `OddLagSplit.measurePreserving_relabel_twist` — abstract in both index types —
assembles them. The inversion-invariance is what lets the negative half be moved onto the positive
one, turning the odd pairing into two evaluations of one function of the half.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem measurePreserving_omirrorT (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) :
    MeasureTheory.MeasurePreserving (omirrorT (N := N) τ c hΛ)
      (MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N)))
      (MassGap.ActionSplit.cvol ↥(oboxT τ c Λ) (probHaar (MassGap.SUN.SU N))) := by
  have hσ : ∀ l : ↥(oboxT τ c Λ), MeasureTheory.MeasurePreserving
      (fun u : MassGap.SUN.SU N =>
        if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ then u⁻¹ else u)
      (probHaar (MassGap.SUN.SU N)) (probHaar (MassGap.SUN.SU N)) := by
    intro l
    by_cases h : ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ
    · simpa [h] using
        MeasureTheory.Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
    · have hid : (fun u : MassGap.SUN.SU N =>
          if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ then u⁻¹ else u) = id := by
        funext u
        simp [h]
      rw [hid]
      exact MeasureTheory.MeasurePreserving.id _
  exact MassGap.OddLagSplit.measurePreserving_relabel_twist
    (probHaar (MassGap.SUN.SU N)) (omirrorEquivTS τ c hΛ)
    (fun l u => if ((l : ↥Λ) : MassGap.InfiniteLattice.ILink).1 = τ then u⁻¹ else u) hσ

#print axioms measurePreserving_omirrorT


/-- The three box-subtype blocks are pairwise disjoint, by trichotomy on `ℤ`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem obox_disjoint (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (oboxR τ c Λ) (oboxS τ c Λ)
      ∧ Disjoint (oboxR τ c Λ) (oboxT τ c Λ)
      ∧ Disjoint (oboxS τ c Λ) (oboxT τ c Λ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine Finset.disjoint_left.2 fun l h1 h2 => ?_ <;>
      simp only [oboxS, oboxT, oboxR, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 <;>
        omega

#print axioms obox_disjoint

/-- And they cover the box, stated over the subtype `↥Λ`. `OddLagSplit.integral_three_block`'s cover
hypothesis is over the whole index type, which on `ℤ⁴` can only be `↥Λ`: `ILink` is infinite and no
finite family covers it. This is why the box-subtype blocks exist beside `ioblkS`, `ioblkT` and
`ioblkR`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem obox_cover (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (i : ↥Λ) : i ∈ oboxR τ c Λ ∨ i ∈ oboxS τ c Λ ∨ i ∈ oboxT τ c Λ := by
  simp only [oboxR, oboxS, oboxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy ((ireflLink τ c i.1).2 τ) (i.1.2 τ) with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

#print axioms obox_cover

/-- The box integral written as three nested integrals — over the shared block's variables, the
positive
half's, and the negative half's — with the integrand still free to couple all three. This is not a
product factorisation, which matters for the straddling term: it reads all three blocks at once, so
no factor of it is a function of one block alone.

`OddLagSplit.integral_three_block` is abstract in the index type and the fibre and does the work;
this supplies the instance. Its combinatorial inputs are `obox_disjoint` and `obox_cover`, and its
index has to be the box subtype because the cover hypothesis quantifies over the whole index type
and `ILink` is infinite. The `ℤ⁴` counterpart of `OddLagSplit.integral_oblk_three_block`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem integral_obox_three_block (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (F : (↥Λ → MassGap.SUN.SU N) → ℝ) (hFm : Measurable F) {C : ℝ}
    (hC : ∀ U, |F U| ≤ C) :
    (∫ U, F U ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
      = ∫ g, (∫ x, (∫ y, F (MassGap.OddLagSplit.join3
                (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
                (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
                (obox_cover τ c Λ) g x y)
              ∂(MassGap.ActionSplit.cvol ↥(oboxT τ c Λ) (probHaar (MassGap.SUN.SU N))))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxR τ c Λ) (probHaar (MassGap.SUN.SU N))) :=
  MassGap.OddLagSplit.integral_three_block (probHaar (MassGap.SUN.SU N))
    (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) F hFm hC

#print axioms integral_obox_three_block

/-- Measurability of `OddLagSplit.join3` in its third slot, with the first two held fixed.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem measurable_obox_join3_right (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N)
    (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N) :
    Measurable (fun y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N =>
      MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
        (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
        (obox_cover τ c Λ) g x y) :=
  (MassGap.OddLagSplit.measurable_join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
      (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
      (obox_cover τ c Λ)).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

#print axioms measurable_obox_join3_right

/-- Measurability of `OddLagSplit.join3` in its second slot, the one the positive half occupies,
with
the first and third held fixed — the sibling of `measurable_obox_join3_right`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem measurable_obox_join3_mid (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) :
    Measurable (fun x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N =>
      MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
        (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
        (obox_cover τ c Λ) g x y) :=
  (MassGap.OddLagSplit.measurable_join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
      (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
      (obox_cover τ c Λ)).comp
    (measurable_const.prodMk (measurable_id.prodMk measurable_const))

#print axioms measurable_obox_join3_mid

/-- The iterated integral with both half-variables on the positive block: `∫` over the box equals
`∫_R ∫_S ∫_S`. The innermost integral has been moved from the negative block to the positive one by
`measurePreserving_omirrorT`, so the two half-variables are independent draws from the same space.

This is the shape `CrossingIntegration.wilson_crossing_pairing_nonneg` takes: one integral over the
shared block and two over the same half, which is what turns the pairing into two evaluations of one
function of the half rather than a coupling of two different spaces. The `ℤ⁴` counterpart of
`OddLagSplit.integral_oblk_mirror`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem integral_obox_mirror (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (F : (↥Λ → MassGap.SUN.SU N) → ℝ) (hFm : Measurable F) {C : ℝ}
    (hC : ∀ U, |F U| ≤ C) :
    (∫ U, F U ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))))
      = ∫ g, (∫ x, (∫ y, F (MassGap.OddLagSplit.join3
                (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
                (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
                (obox_cover τ c Λ) g x (omirrorT τ c hΛ y))
              ∂(MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N))))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ c Λ) (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxR τ c Λ) (probHaar (MassGap.SUN.SU N))) := by
  rw [integral_obox_three_block τ c Λ F hFm hC]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact (MassGap.ActionSplit.integral_comp_of_mp (measurePreserving_omirrorT τ c hΛ)
    (hFm.comp (measurable_obox_join3_right τ c Λ g x))).symm

#print axioms integral_obox_mirror

/-- The plaquettes of `iplqAll Λ` whose base the reflection at `c` moves down in the `τ` coordinate.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioplqPlus (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (iplqAll Λ).filter (fun q => (ireflPlaq τ c q).2 τ < q.2 τ)

/-- Their mirror: base moved up.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioplqMinus (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (iplqAll Λ).filter (fun q => q.2 τ < (ireflPlaq τ c q).2 τ)

/-- The plaquettes whose base is not moved in the `τ` coordinate.

The geometry depends on the parity of `c`. At an even constant this is the plane plaquettes, all
four of whose links lie in the shared block. At an odd constant there is no plane, and the set is
the axis plaquettes based one step below the mirror, which cross it. The definition is the same
either way.

It is the only one of the three classes in which the shared block appears, and at an odd constant
the shared block is axis links the twist inverts (`odd_tau_fixed_iff`,
`LatticeReflection.ireflConf_inverts_fixed_axis_link`). `OddLagSplit.actCrossO` is the periodic
counterpart.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
def ioplqCross (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Finset MassGap.GibbsSpec.IPlaq :=
  (iplqAll Λ).filter (fun q => (ireflPlaq τ c q).2 τ = q.2 τ)

#print axioms ioplqPlus

/-- The three plaquette classes are pairwise disjoint, by trichotomy on `ℤ`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplq_disjoint (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    Disjoint (ioplqPlus τ c Λ) (ioplqMinus τ c Λ)
      ∧ Disjoint (ioplqPlus τ c Λ) (ioplqCross τ c Λ)
      ∧ Disjoint (ioplqMinus τ c Λ) (ioplqCross τ c Λ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine Finset.disjoint_left.2 fun q h1 h2 => ?_ <;>
      simp only [ioplqPlus, ioplqMinus, ioplqCross, Finset.mem_filter] at h1 h2 <;>
        omega

#print axioms ioplq_disjoint

/-- And they exhaust `iplqAll Λ`, the plaquette set of `wtFree`.

Scope: `iplqAll` is the free-boundary plaquette set, not `GibbsSpec.wt`'s, which sums over
`boundaryPlaqs` and for which `plaqsIn` is provably not local
(`GibbsSpec.plaqsIn_split_not_local`). `iplqAll` also drops the diagonal `μ = ν`; that is inert for
the Wilson density, whose degenerate holonomy is the identity, and for a general `φ` it shifts the
action by `φ 1` per diagonal plaquette.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplq_union (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink) :
    ioplqPlus τ c Λ ∪ ioplqMinus τ c Λ ∪ ioplqCross τ c Λ = iplqAll Λ := by
  classical
  ext q
  simp only [Finset.mem_union, ioplqPlus, ioplqMinus, ioplqCross, Finset.mem_filter]
  constructor
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  · intro hq
    rcases lt_trichotomy ((ireflPlaq τ c q).2 τ) (q.2 τ) with h | h | h
    · exact Or.inl (Or.inl ⟨hq, h⟩)
    · exact Or.inr ⟨hq, h⟩
    · exact Or.inl (Or.inr ⟨hq, h⟩)

#print axioms ioplq_union

/-- At the odd constant `2 * p - 1` every straddling plaquette has a `τ` direction. A transverse
plaquette reflects about `c` itself, so its base is unmoved only when `2 x_τ = c`, which is
impossible for odd `c`; only axis plaquettes, reflecting about `c - 1`, can straddle.

This is what makes the crossing word well defined: a cross plaquette with a `τ` direction has
exactly one boundary link in the positive half — the transverse link one step up — so the word can
be indexed by the cross plaquettes themselves, one block each. At an even constant the set is the
plane plaquettes, whose links all lie in the shared block, and no such indexing exists.

DERIVED: the `2` and the `1` make the constant odd, which is the content; `4` is the dimension. -/
theorem ioplqCross_axis (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : q.1.1 = τ ∨ q.1.2 = τ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [ioplqCross, Finset.mem_filter] at hq
  have h := hq.2
  simp only [ireflPlaq, if_neg h1, if_neg h2, ireflSite_axis] at h
  omega

#print axioms ioplqCross_axis

/-- The action over the box's non-degenerate plaquettes splits as `A = A₊ + A₋ + A_cross`, at any
constant `c` and any `φ`, from `ioplq_union` and `ioplq_disjoint`.

At an even constant the analogous decomposition `actionOn_split_three` has a plane part reading the
shared block only, on which the twist acts trivially, and the Gibbs weight factors as
`W · h(U) · h(ΘU)`. At an odd constant the shared block is axis links the twist inverts, so
`A_cross` does not factor that way and its exponential is integrated against the crossing kernel
(`CrossingIntegration.wilson_crossing_pairing_nonneg`), which is where `0 ≤ β` is used.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplq_actionOn_split {G : Type} [Group G] (φ : G → ℝ) (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) U
        + MassGap.GibbsSpec.actionOn φ (ioplqMinus τ c Λ) U
        + MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  rw [← ioplq_union τ c Λ,
    Finset.sum_union (Finset.disjoint_union_left.2
      ⟨(ioplq_disjoint τ c Λ).2.1, (ioplq_disjoint τ c Λ).2.2⟩),
    Finset.sum_union (ioplq_disjoint τ c Λ).1]

#print axioms ioplq_actionOn_split

/-- At the odd constant `2 * p - 1`, a link of the box based at height `p` or above is in `ioblkS` —
for a `τ`-link and a transverse link alike.

The parity is load-bearing: a `τ`-link needs `2 x_τ > c - 1 = 2p - 2` and a transverse one
`2 x_τ > c = 2p - 1`, and between `2p - 2` and `2p - 1` there is no even number, so both read
`x_τ ≥ p`. At an even constant the two conditions separate and no single height serves, which is why
the even chain's `iplqPlus_links_mem` lands in `boxS ∪ boxR`.

DERIVED: the `2` is the plane-to-constant conversion and the `1` the half-step, together making the
constant odd, which is the content; `4` is the dimension. -/
theorem ioblkS_of_le_coord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ Λ) (hp : p ≤ l.2 τ) : l ∈ ioblkS τ (2 * p - 1) Λ := by
  simp only [ioblkS, Finset.mem_filter]
  refine ⟨hl, ?_⟩
  by_cases h : l.1 = τ
  · simp only [ireflLink, if_pos h, ireflSite_axis]
    omega
  · simp only [ireflLink, if_neg h, ireflSite_axis]
    omega

#print axioms ioblkS_of_le_coord

/-- A plaquette of `ioplqPlus τ (2 * p - 1) Λ` is based at height `p` or above, in all three
branches of
`ireflPlaq`: the axis branches use the `c - 1` offset and the transverse branch uses `c`, and at an
odd constant both reduce to the same cut.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ioplqPlus_base_ge (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqPlus τ (2 * p - 1) Λ) : p ≤ q.2 τ := by
  simp only [ioplqPlus, Finset.mem_filter] at hq
  have h := hq.2
  by_cases h1 : q.1.1 = τ
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis] at h
    omega
  · by_cases h2 : q.1.2 = τ
    · simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis] at h
      omega
    · simp only [ireflPlaq, if_neg h1, if_neg h2, ireflSite_axis] at h
      omega

#print axioms ioplqPlus_base_ge

/-- Every boundary link of a plaquette in `ioplqPlus τ (2 * p - 1) Λ` lies in `ioblkS τ (2 * p - 1)
Λ`,
not merely in `ioblkS ∪ ioblkR` as the even chain's `iplqPlus_links_mem` concludes. The shared block
does not appear in the positive action at an odd constant.

`GibbsSpec.ilinks_eq` puts the four boundary links at `x`, `ishift μ x`, `ishift ν x` and `x`, and
only a shift along `τ` moves the `τ` coordinate, so they sit at height `x_τ` or `x_τ + 1`;
`ioplqPlus_base_ge` puts `x_τ` at `p` or above.

Odd constant only: `ioblkS_of_le_coord` is where the parity is used. The `ℤ⁴` counterpart of
`OddLagSplit.oplaq_links_plus`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ioplqPlus_links_mem (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqPlus τ (2 * p - 1) Λ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks q) : l ∈ ioblkS τ (2 * p - 1) Λ := by
  have hbase : p ≤ q.2 τ := ioplqPlus_base_ge τ p hq
  have hqall : q ∈ iplqAll Λ := (Finset.mem_filter.mp hq).1
  have hin : l ∈ Λ :=
    (MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hqall).1) l hl
  refine ioblkS_of_le_coord τ p hin ?_
  have hshift : ∀ μ : Fin 4, p ≤ (MassGap.InfiniteLattice.ishift μ q.2) τ := by
    intro μ
    by_cases hm : τ = μ
    · subst hm
      simp only [MassGap.InfiniteLattice.ishift, Function.update_self]
      omega
    · simp only [MassGap.InfiniteLattice.ishift, Function.update_of_ne hm]
      exact hbase
  rw [MassGap.GibbsSpec.ilinks_eq] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact hbase
  · exact hshift q.1.1
  · exact hshift q.1.2
  · exact hbase

#print axioms ioplqPlus_links_mem

/-- A straddling plaquette at `c = 2 * p - 1` is based at `p - 1`, one step below the mirror, which
sits
at `p - 1/2`.

DERIVED: the `2` and the `1`s are the odd constant and `ireflPlaq`'s axis offset; `4` is the
dimension. -/
theorem ioplqCross_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : q.2 τ = p - 1 := by
  simp only [ioplqCross, Finset.mem_filter] at hq
  have h := hq.2
  rcases ioplqCross_axis τ p (Finset.mem_filter.mpr hq) with h1 | h2
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis] at h
    omega
  · by_cases h1 : q.1.1 = τ
    · simp only [ireflPlaq, if_pos h1, ireflSite_axis] at h
      omega
    · simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis] at h
      omega

#print axioms ioplqCross_base

/-- The positive half's link at a straddling plaquette: the transverse link one step above the base.
The
other three boundary links are the two `τ`-links at the base, which the mirror fixes, and the
transverse link at the base, which it sends below. `ioplqCross_axis` is what guarantees a `τ`
direction exists to step along.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def osLinkOf (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : MassGap.InfiniteLattice.ILink :=
  if q.1.1 = τ then (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
  else (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2)

#print axioms osLinkOf

/-- `osLinkOf τ q` lies in `ioblkS τ (2 * p - 1) Λ` for a straddling plaquette `q`: the plaquette is
based at `p - 1` by `ioplqCross_base`, so stepping once along `τ` lands at `p`, which
`ioblkS_of_le_coord` accepts. Exactly one of the four boundary links is in `ioblkS`, which is what
lets the crossing word carry one block per straddling plaquette.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_mem_ioblkS (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    osLinkOf τ q ∈ ioblkS τ (2 * p - 1) Λ := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hqall : q ∈ iplqAll Λ := (Finset.mem_filter.mp hq).1
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hqall).1
  have hstep : ∀ μ : Fin 4, μ = τ →
      (MassGap.GibbsSpec.ishift μ q.2) τ = p := by
    intro μ hμ
    subst hμ
    simp only [MassGap.GibbsSpec.ishift, Function.update_self]
    omega
  by_cases h1 : q.1.1 = τ
  · have hmem : osLinkOf τ q ∈ MassGap.GibbsSpec.ilinks q := by
      rw [MassGap.GibbsSpec.ilinks_eq]
      simp only [osLinkOf, if_pos h1]
      simp
    refine ioblkS_of_le_coord τ p (hlinks _ hmem) ?_
    simp only [osLinkOf, if_pos h1]
    rw [hstep q.1.1 h1]
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    have hmem : osLinkOf τ q ∈ MassGap.GibbsSpec.ilinks q := by
      rw [MassGap.GibbsSpec.ilinks_eq]
      simp only [osLinkOf, if_neg h1]
      simp
    refine ioblkS_of_le_coord τ p (hlinks _ hmem) ?_
    simp only [osLinkOf, if_neg h1]
    rw [hstep q.1.2 h2]

#print axioms osLinkOf_mem_ioblkS

/-- The half-link is in the box: `ioblkS` is a filter of `Λ`, so this is the first component of
`osLinkOf_mem_ioblkS`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_mem_box (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : osLinkOf τ q ∈ Λ :=
  (Finset.mem_filter.mp (osLinkOf_mem_ioblkS τ p hq)).1

#print axioms osLinkOf_mem_box

/-- And it is in the positive block at the box-subtype index — the same inequality as in `ioblkS`,
carried to the subtype the mirror factorisation's integrals run over.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_mem_oboxS (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨osLinkOf τ q, osLinkOf_mem_box τ p hq⟩ : ↥Λ) ∈ oboxS τ (2 * p - 1) Λ :=
  mem_oboxS_of_mem_ioblkS τ (2 * p - 1) (osLinkOf_mem_ioblkS τ p hq)

#print axioms osLinkOf_mem_oboxS

/-- The map the crossing word is built along: each straddling plaquette contributes exactly one
block,
the half's variable at its own `osLinkOf`. `ioplqCross_axis` and `osLinkOf_mem_ioblkS` are what make
it well defined; at an even constant there is no such map, since a plane plaquette has no link in
the positive half. The `ℤ⁴` counterpart of `OddLagSplit.sIdx`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
def osIdx (τ : Fin 4) (p : ℤ) {Λ : Finset MassGap.InfiniteLattice.ILink}
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) : ↥(oboxS τ (2 * p - 1) Λ) :=
  ⟨⟨osLinkOf τ k.1, osLinkOf_mem_box τ p k.2⟩, osLinkOf_mem_oboxS τ p k.2⟩

#print axioms osIdx

/-- The word the crossing integration reads: the block-diagonal sum, over the straddling plaquettes,
of
the positive half's link at each, relabelled to a `Fin` index because that is the type
`CrossingIntegration.wilson_crossing_pairing_nonneg` takes for its word `X`. One block per
straddling plaquette, with `osIdx` supplying the indexing. The `ℤ⁴` counterpart of
`OddLagSplit.crossWord`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension; the matrix size is
`Fintype.card (Fin N × ioplqCross)`, a count. -/
noncomputable def ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    Matrix (Fin (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))))
      (Fin (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ)))) ℂ :=
  (Matrix.blockDiagonal (fun k : ↥(ioplqCross τ (2 * p - 1) Λ) =>
      ((u (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))).submatrix
    (Fintype.equivFin (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))).symm
    (Fintype.equivFin (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))).symm

#print axioms ocrossWord

/-- The word's cross form is the sum of the per-block cross forms over the straddling plaquettes.
`OddLagSplit.hsRe_blockDiagonal_fin` is abstract in the block index and the matrix size, so the
relabelling to `Fin` is invisible to the cross form.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem hsRe_ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (u v : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.CharacterExpansion.hsRe (ocrossWord τ p u) (ocrossWord τ p v)
      = ∑ k : ↥(ioplqCross τ (2 * p - 1) Λ),
          MassGap.CharacterExpansion.hsRe
            ((u (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
            ((v (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) :=
  MassGap.OddLagSplit.hsRe_blockDiagonal_fin _ _

#print axioms hsRe_ocrossWord

/-- The word's cross form is unchanged by `OddLagSplit.planeAct`, which conjugates each half-link by
its
own pair of shared-block variables. `hsRe_ocrossWord` reduces the cross form to a sum of per-block
cross forms and `CrossingIntegration.hsRe_conj` absorbs the conjugation one block at a time. This is
the hypothesis `CrossingIntegration.wilson_crossing_pairing_nonneg` calls `hXinv`.

Scope: it holds for any `A` and `B`, because the invariance is a property of conjugation and not of
which straddling links the assignment picks. What the assignment has to get right is the sum
identity, where the actual straddling links appear.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem hsRe_ocrossWord_planeAct (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (A B : ↥(oboxS τ (2 * p - 1) Λ) → ↥(oboxR τ (2 * p - 1) Λ))
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (u v : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.CharacterExpansion.hsRe
        (ocrossWord τ p (MassGap.OddLagSplit.planeAct A B g u))
        (ocrossWord τ p (MassGap.OddLagSplit.planeAct A B g v))
      = MassGap.CharacterExpansion.hsRe (ocrossWord τ p u) (ocrossWord τ p v) := by
  rw [hsRe_ocrossWord, hsRe_ocrossWord]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact MassGap.CrossingIntegration.hsRe_conj
    (g (A (osIdx τ p k))) (g (B (osIdx τ p k))) (u (osIdx τ p k)) (v (osIdx τ p k))

#print axioms hsRe_ocrossWord_planeAct

/-- A straddling plaquette's base `τ`-link is in the box. It is a boundary link in both orientations
of
the plane — first in the list when the plane leads with `τ`, fourth when it trails — so
`GibbsSpec.mem_plaqsIn` places it in `Λ`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem baseTauLink_mem_box (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    ((τ, q.2) : MassGap.InfiniteLattice.ILink) ∈ Λ := by
  have hqall : q ∈ iplqAll Λ := (Finset.mem_filter.mp hq).1
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hqall).1
  refine hlinks _ ?_
  rw [MassGap.GibbsSpec.ilinks_eq]
  rcases ioplqCross_axis τ p hq with h1 | h2
  · rw [← h1]
    simp
  · rw [← h2]
    simp

#print axioms baseTauLink_mem_box

/-- At the odd constant `2 * p - 1`, every `τ`-link based at `p - 1` is in the shared block: it
reflects
to `(2p - 1) - 1 - (p - 1) = p - 1`, so the mirror at `p - 1/2` leaves it where it is.

This is one inclusion. That the shared block contains nothing else is a separate statement, not
proved here; `odd_nonTau_not_fixed` is the nearest statement to it and is about `ireflLink l ≠ l`
rather than about `oboxR`.

DERIVED: the `2` and the `1`s are the odd constant and `ireflLink`'s link-length offset; `4` is the
dimension. -/
theorem tauLink_mem_oboxR (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {x : MassGap.GibbsSpec.ISite}
    (hx : x τ = p - 1) (hmem : ((τ, x) : MassGap.InfiniteLattice.ILink) ∈ Λ) :
    (⟨(τ, x), hmem⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ := by
  have hval : (ireflLink τ (2 * p - 1) ((τ, x) : MassGap.InfiniteLattice.ILink)).2 τ
      = 2 * p - 1 - 1 - x τ := by
    simp [ireflLink]
  simp only [oboxR, Finset.mem_filter, Finset.mem_univ, true_and, hval]
  omega

#print axioms tauLink_mem_oboxR

/-- And so a straddling plaquette's base `τ`-link is in the shared block, since `ioplqCross_base`
puts
it at `p - 1`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem baseTauLink_mem_oboxR (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨(τ, q.2), baseTauLink_mem_box τ p hq⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ :=
  tauLink_mem_oboxR τ p (ioplqCross_base τ p hq) (baseTauLink_mem_box τ p hq)

#print axioms baseTauLink_mem_oboxR

/-- The transverse direction of a plaquette: the plane direction that is not `τ`. `ioplqCross_axis`
says
one of the two plane directions of a straddling plaquette is `τ`, and this picks the other. The `ℤ⁴`
counterpart of `OddLagSplit.cDir`.

DERIVED: `4` is the dimension; the projections are structure fields. -/
def ocDir (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : Fin 4 :=
  if q.1.1 = τ then q.1.2 else q.1.1

#print axioms ocDir

/-- `ocDir τ q ≠ τ` for a non-degenerate plaquette. If the first direction is `τ` the second differs
from it by `hnd`, and otherwise the first is not `τ` by the case.

Non-degeneracy is the whole hypothesis: no box, no constant and no reflection enter, and the
plaquette need not lie in any `Λ`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem ocDir_ne (τ : Fin 4) {q : MassGap.GibbsSpec.IPlaq} (hnd : q.1.1 ≠ q.1.2) :
    ocDir τ q ≠ τ := by
  show (if q.1.1 = τ then q.1.2 else q.1.1) ≠ τ
  by_cases h1 : q.1.1 = τ
  · rw [if_pos h1]
    exact fun hc => hnd (h1.trans hc.symm)
  · rw [if_neg h1]
    exact h1

#print axioms ocDir_ne

/-- A plaquette's second `τ`-link, one transverse step along from the base one. Together with `(τ,
q.2)`
these are the two links the mirror fixes, and they are the plane gauge acting on the half. The `ℤ⁴`
counterpart of `OddLagSplit.bLinkOf`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def obLinkOf (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : MassGap.InfiniteLattice.ILink :=
  (τ, MassGap.GibbsSpec.ishift (ocDir τ q) q.2)

#print axioms obLinkOf

/-- The mirror's transverse link: the one at the base, which the reflection sends to height `p`. The
`ℤ⁴` counterpart of `OddLagSplit.tLinkOf`.

It tests nothing about which plane the plaquette sits at. On the torus `tLinkOf` does, because the
two fixed planes exchange the roles of the two transverse links; `ℤ⁴` has one mirror, and the only
case split left is `ocDir`'s.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def otLinkOf (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) : MassGap.InfiniteLattice.ILink :=
  (ocDir τ q, q.2)

#print axioms otLinkOf

/-- The second `τ`-link is in the box. It is a boundary link in both orientations of the plane —
third
in the list when the plane leads with `τ`, second when it trails — so `GibbsSpec.mem_plaqsIn` places
it in `Λ`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem obLinkOf_mem_box (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) : obLinkOf τ q ∈ Λ := by
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp
    (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).1
  refine hlinks _ ?_
  rw [MassGap.GibbsSpec.ilinks_eq]
  by_cases h1 : q.1.1 = τ
  · simp only [obLinkOf, ocDir, if_pos h1]
    rw [← h1]
    simp
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    simp only [obLinkOf, ocDir, if_neg h1]
    rw [← h2]
    simp

#print axioms obLinkOf_mem_box

/-- And the second `τ`-link is in the shared block too. Its base is one transverse step from `q.2`,
which `ishift_coord` leaves at `p - 1`, so it reflects exactly as the base `τ`-link does.

DERIVED: the `2` and the `1`s are the odd constant and `ireflLink`'s link-length offset; `4` is the
dimension. -/
theorem obLinkOf_mem_oboxR (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨obLinkOf τ q, obLinkOf_mem_box τ p hq⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hstep : (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ = q.2 τ := by
    rw [ishift_coord, if_neg (ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2)]
  have hval : (ireflLink τ (2 * p - 1) (obLinkOf τ q)).2 τ
      = 2 * p - 1 - 1 - (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ := by
    simp [obLinkOf, ireflLink]
  simp only [oboxR, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hval]
  show 2 * p - 1 - 1 - (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ
      = (MassGap.GibbsSpec.ishift (ocDir τ q) q.2) τ
  rw [hstep]
  omega

#print axioms obLinkOf_mem_oboxR

/-- The mirror's transverse link is in the box, by the same boundary-word argument — fourth in the
boundary word when `q.1.1 = τ`, first otherwise.

Like `ocDir_ne` this needs no reflection, and the branch is on `q.1.1 = τ` rather than on which
direction is the axis: at a general plaquette of `iplqAll` neither need be `τ`, and both branches
land on a boundary link. `iplqAll` membership is the whole hypothesis.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem otLinkOf_mem_box (τ : Fin 4)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) : otLinkOf τ q ∈ Λ := by
  have hlinks := MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hq).1
  refine hlinks _ ?_
  rw [MassGap.GibbsSpec.ilinks_eq]
  by_cases h1 : q.1.1 = τ
  · simp only [otLinkOf, ocDir, if_pos h1]
    simp
  · simp only [otLinkOf, ocDir, if_neg h1]
    simp

#print axioms otLinkOf_mem_box

/-- And it is in the negative block: a transverse link reflects about `c` rather than `c - 1`, so
its
image sits at `(2p - 1) - (p - 1) = p`, strictly above its own height `p - 1`.

With the memberships above, a straddling plaquette has one link in `S`, one in `T` and two in `R`,
and `ocross_links_distinct` shows the four are distinct. Its contribution is therefore a cross term
between the two halves rather than a square, which is what the even constant gives.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem otLinkOf_mem_oboxT (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (⟨otLinkOf τ q, otLinkOf_mem_box τ (Finset.mem_filter.mp hq).1⟩ : ↥Λ) ∈ oboxT τ (2 * p - 1) Λ := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hne : (otLinkOf τ q).1 ≠ τ := ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2
  have hval : (ireflLink τ (2 * p - 1) (otLinkOf τ q)).2 τ = 2 * p - 1 - (otLinkOf τ q).2 τ :=
    image_half_is_c_sub_p τ (2 * p - 1) hne
  simp only [oboxT, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hval]
  show q.2 τ < 2 * p - 1 - q.2 τ
  omega

#print axioms otLinkOf_mem_oboxT

/-- One formula for every straddling plaquette: its `Re tr` is the cross form of its `τ`-links
acting on
the positive half's link, against the mirror's link,

    Re tr (hol q U) = hsRe (U(A) · U(S) · U(B)⁻¹) (U(T))

with `A = (τ, q.2)`, `B = obLinkOf τ q`, `S = osLinkOf τ q`, `T = otLinkOf τ q`. This is the
identification `CrossingIntegration`'s `hsRe (X (act g x)) (X y)` reads, with `act` the gauge action
of the two `τ`-links.

The right-hand side is the same in both orientations of the plane by construction of `ocDir`; only
the word's direction differs, and `Re tr` does not see inversion. The second branch's `group`
followed by `OddLagSplit.re_trace_inv` is `OddLagSplit.re_tr_hol_swap`'s argument inlined. `invLink`
is not needed here: on the torus it existed to put two mirror planes into one handedness, and there
is one mirror on `ℤ⁴`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem re_tr_hol_ocross (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ)
    (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    (Matrix.trace ((MassGap.GibbsSpec.ihol q U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = MassGap.CharacterExpansion.hsRe
          (((U (τ, q.2) * U (osLinkOf τ q) * (U (obLinkOf τ q))⁻¹ : MassGap.SUN.SU N)
            : Matrix (Fin N) (Fin N) ℂ))
          ((U (otLinkOf τ q) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [gibbs_ihol_eq, MassGap.InfiniteLattice.wilsonHol_ibd,
    MassGap.CrossingIntegration.hsRe_coe_eq, ← gibbs_ishift_eq]
  by_cases h1 : q.1.1 = τ
  · have hos : osLinkOf τ q = (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2) := if_pos h1
    have hob : obLinkOf τ q = (τ, MassGap.GibbsSpec.ishift q.1.2 q.2) := by
      simp only [obLinkOf, ocDir, if_pos h1]
    have hot : otLinkOf τ q = (q.1.2, q.2) := by
      simp only [otLinkOf, ocDir, if_pos h1]
    rw [hos, hob, hot, ← h1]
    have hw : (U (q.1.1, q.2) * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
          * ((U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹))
        : MassGap.SUN.SU N)
        = U (q.1.1, q.2) * U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
            * (U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹ := by
      group
    rw [hw]
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    have hos : osLinkOf τ q = (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2) := if_neg h1
    have hob : obLinkOf τ q = (τ, MassGap.GibbsSpec.ishift q.1.1 q.2) := by
      simp only [obLinkOf, ocDir, if_neg h1]
    have hot : otLinkOf τ q = (q.1.1, q.2) := by
      simp only [otLinkOf, ocDir, if_neg h1]
    rw [hos, hob, hot, ← h2]
    have hw : (U (q.1.1, q.2) * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2)
          * ((U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2))⁻¹ * (U (q.1.2, q.2))⁻¹))
        : MassGap.SUN.SU N)
        = (U (q.1.2, q.2) * U (q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2)
            * (U (q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2))⁻¹
            * (U (q.1.1, q.2))⁻¹)⁻¹ := by
      group
    rw [hw, MassGap.OddLagSplit.re_trace_inv]

#print axioms re_tr_hol_ocross

/-- The half-link's direction is the plaquette's transverse one, in both orientations, because
`ocDir`
and `osLinkOf` split on the same condition into matching branches. No hypothesis is needed.

DERIVED: `4` is the dimension. -/
theorem osLinkOf_dir (τ : Fin 4) (q : MassGap.GibbsSpec.IPlaq) :
    (osLinkOf τ q).1 = ocDir τ q := by
  by_cases h1 : q.1.1 = τ
  · simp only [osLinkOf, ocDir, if_pos h1]
  · simp only [osLinkOf, ocDir, if_neg h1]

#print axioms osLinkOf_dir

/-- And its base is one `τ` step up from the plaquette's. The orientation matters here: the shifted
direction is `q.1.1` in one branch and `q.1.2` in the other, and `ioplqCross_axis` says whichever it
is equals `τ`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem osLinkOf_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    (osLinkOf τ q).2 = MassGap.GibbsSpec.ishift τ q.2 := by
  unfold osLinkOf
  by_cases h1 : q.1.1 = τ
  · rw [if_pos h1, h1]
  · have h2 : q.1.2 = τ := (ioplqCross_axis τ p hq).resolve_left h1
    rw [if_neg h1, h2]

#print axioms osLinkOf_base

/-- The four roles at a straddling plaquette are four distinct links, so "one link in `S`, one in
`T`,
two in `R`" is a count. Two mechanisms cover all six pairs: `ocDir_ne` separates the two `τ`-links
from the two transverse ones by direction, and a one-step shift separates within each pair by base —
the `τ`-links at `q.2` and `ishift (ocDir τ q) q.2`, the transverse ones at `q.2` and `ishift τ
q.2`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. The one-step shift that
separates each pair lives in `osLinkOf` and `obLinkOf`, not in this signature. -/
theorem ocross_links_distinct (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    ((τ, q.2) : MassGap.InfiniteLattice.ILink) ≠ obLinkOf τ q ∧
      ((τ, q.2) : MassGap.InfiniteLattice.ILink) ≠ osLinkOf τ q ∧
      ((τ, q.2) : MassGap.InfiniteLattice.ILink) ≠ otLinkOf τ q ∧
      obLinkOf τ q ≠ osLinkOf τ q ∧
      obLinkOf τ q ≠ otLinkOf τ q ∧
      osLinkOf τ q ≠ otLinkOf τ q := by
  have hdir : ocDir τ q ≠ τ := ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2
  have hos1 : (osLinkOf τ q).1 = ocDir τ q := osLinkOf_dir τ q
  have hos2 : (osLinkOf τ q).2 = MassGap.GibbsSpec.ishift τ q.2 := osLinkOf_base τ p hq
  have hself : ∀ (μ : Fin 4) (x : MassGap.GibbsSpec.ISite),
      (MassGap.GibbsSpec.ishift μ x) μ = x μ + 1 := by
    intro μ x
    simp only [MassGap.GibbsSpec.ishift, Function.update_self]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 : q.2 = MassGap.GibbsSpec.ishift (ocDir τ q) q.2 := congrArg Prod.snd h
    have h3 := congrFun h2 (ocDir τ q)
    rw [hself] at h3
    omega
  · intro h
    exact hdir ((congrArg Prod.fst h).trans hos1).symm
  · intro h
    have h1 : τ = ocDir τ q := congrArg Prod.fst h
    exact hdir h1.symm
  · intro h
    exact hdir ((congrArg Prod.fst h).trans hos1).symm
  · intro h
    have h1 : τ = ocDir τ q := congrArg Prod.fst h
    exact hdir h1.symm
  · intro h
    have h2 : (osLinkOf τ q).2 = q.2 := congrArg Prod.snd h
    rw [hos2] at h2
    have h3 := congrFun h2 τ
    rw [hself] at h3
    omega

#print axioms ocross_links_distinct

/-- The converse of `ioplqCross_base`: a plaquette of `iplqAll Λ` with a `τ` direction, based one
step
below the mirror, is straddling. With `ioplqCross_base` and `ioplqCross_axis` this characterises the
straddling set at an odd constant as the plaquettes with a `τ` direction based at `p - 1`.

Both orientations of the plane are covered, which matters because `ioplqCross` contains both copies
of every geometric plaquette and `sum_re_tr_ioplqCross` sums over them.

DERIVED: the `2` and the `1`s are the odd constant and `ireflPlaq`'s axis offset; `4` is the
dimension. -/
theorem mem_ioplqCross_of_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) (hax : q.1.1 = τ ∨ q.1.2 = τ) (hbase : q.2 τ = p - 1) :
    q ∈ ioplqCross τ (2 * p - 1) Λ := by
  refine Finset.mem_filter.mpr ⟨hq, ?_⟩
  show (ireflPlaq τ (2 * p - 1) q).2 τ = q.2 τ
  by_cases h1 : q.1.1 = τ
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis]
    omega
  · have h2 : q.1.2 = τ := hax.resolve_left h1
    simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis]
    omega

#print axioms mem_ioplqCross_of_base

/-- The converse of `ioplqPlus_base_ge`: a plaquette of `iplqAll Λ` based at or above the plane is
positive, in all three branches of `ireflPlaq` and with no hypothesis on direction. The axis
branches reflect about `c - 1` and the transverse one about `c`; at an odd constant `p ≤ x_τ` clears
both, the same collapse `ioblkS_of_le_coord` performs on links.

DERIVED: the `2` and the `1` make the constant odd, which is what lets one cut serve all three
branches; `4` is the dimension. -/
theorem mem_ioplqPlus_of_base (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ iplqAll Λ) (hbase : p ≤ q.2 τ) :
    q ∈ ioplqPlus τ (2 * p - 1) Λ := by
  refine Finset.mem_filter.mpr ⟨hq, ?_⟩
  show (ireflPlaq τ (2 * p - 1) q).2 τ < q.2 τ
  by_cases h1 : q.1.1 = τ
  · simp only [ireflPlaq, if_pos h1, ireflSite_axis]
    omega
  · by_cases h2 : q.1.2 = τ
    · simp only [ireflPlaq, if_neg h1, if_pos h2, ireflSite_axis]
      omega
    · simp only [ireflPlaq, if_neg h1, if_neg h2, ireflSite_axis]
      omega

#print axioms mem_ioplqPlus_of_base

/-- The base site of the witness box's straddling plaquette, one `τ` step below the mirror at
`p - 1/2`.

CHOSEN: all four coordinates are set to `p - 1`. Only the `τ` one is forced — `ioplqCross_base`
fixes it at `p - 1` and nothing constrains the other three, so they are set equal. `4` is the
dimension. -/
def ocrossSite (p : ℤ) : MassGap.GibbsSpec.ISite := fun _ => p - 1

#print axioms ocrossSite

/-- The witness box's straddling plaquette: the `(τ, ν)` plane based at `ocrossSite p`, one step
below
the mirror.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def ocrossPlaq (τ ν : Fin 4) (p : ℤ) : MassGap.GibbsSpec.IPlaq := ((τ, ν), ocrossSite p)

/-- And its positive companion: the same plane, one `τ` step up, based at `p`. A box holding only a
straddling plaquette has `ioplqPlus` empty, and every statement about the positive half-action would
hold vacuously there.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def oplusPlaq (τ ν : Fin 4) (p : ℤ) : MassGap.GibbsSpec.IPlaq :=
  ((τ, ν), MassGap.GibbsSpec.ishift τ (ocrossSite p))

#print axioms ocrossPlaq
#print axioms oplusPlaq

/-- The witness box: the boundary links of one straddling plaquette and one positive plaquette,
closed
under the reflection at `2 * p - 1`. `reflClosure` supplies the closure, so the box is specified by
the plaquettes it must carry rather than by the links it happens to have.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
def ocrossBox (τ ν : Fin 4) (p : ℤ) : Finset MassGap.InfiniteLattice.ILink :=
  reflClosure τ (2 * p - 1)
    ((MassGap.GibbsSpec.ilinks (ocrossPlaq τ ν p)).toFinset ∪
      (MassGap.GibbsSpec.ilinks (oplusPlaq τ ν p)).toFinset)

#print axioms ocrossBox

/-- The witness box is closed under the reflection at `2 * p - 1` — the `hΛ` every lemma of the odd
chain carries. One application of `reflClosure_closed`, with no case split on direction and no
arithmetic.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_refl_closed (τ ν : Fin 4) (p : ℤ) :
    ∀ l ∈ ocrossBox τ ν p, ireflLink τ (2 * p - 1) l ∈ ocrossBox τ ν p :=
  reflClosure_closed τ (2 * p - 1) _

#print axioms ocrossBox_refl_closed

/-- Every boundary link of `ocrossPlaq τ ν p` is in the witness box, by `subset_reflClosure`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossPlaq_links_mem (τ ν : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (ocrossPlaq τ ν p)) : l ∈ ocrossBox τ ν p :=
  subset_reflClosure τ (2 * p - 1) _
    (Finset.mem_union_left _ (List.mem_toFinset.mpr hl))

/-- And every boundary link of `oplusPlaq τ ν p` is too.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem oplusPlaq_links_mem (τ ν : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (hl : l ∈ MassGap.GibbsSpec.ilinks (oplusPlaq τ ν p)) : l ∈ ocrossBox τ ν p :=
  subset_reflClosure τ (2 * p - 1) _
    (Finset.mem_union_right _ (List.mem_toFinset.mpr hl))

#print axioms ocrossPlaq_links_mem
#print axioms oplusPlaq_links_mem

/-- `ioplqCross τ (2 * p - 1) (ocrossBox τ ν p)` contains `ocrossPlaq τ ν p`, so the straddling set
is
not always empty. `sum_re_tr_ioplqCross`, `hsRe_ocrossWord_planeAct`, `ocrossWord` and the
memberships above are statements about `ioplqCross`, and each holds vacuously when that set is
empty.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_cross_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    ocrossPlaq τ ν p ∈ ioplqCross τ (2 * p - 1) (ocrossBox τ ν p) :=
  mem_ioplqCross_of_base τ p
    (mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr
      (fun l hl => ocrossPlaq_links_mem τ ν p hl), fun h => hν h.symm⟩)
    (Or.inl rfl) rfl

#print axioms ocrossBox_cross_nonempty

/-- And `ioplqPlus τ (2 * p - 1) (ocrossBox τ ν p)` contains `oplusPlaq τ ν p`. With only a
straddling
plaquette in the box, `ioplqPlus` is empty, `actionOn_ioplqPlus_ojoin` reads `0 = 0` and two of
`wtFree_odd_paired`'s three factors read `exp 0 = 1`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_plus_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    oplusPlaq τ ν p ∈ ioplqPlus τ (2 * p - 1) (ocrossBox τ ν p) := by
  refine mem_ioplqPlus_of_base τ p
    (mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr
      (fun l hl => oplusPlaq_links_mem τ ν p hl), fun h => hν h.symm⟩) ?_
  show p ≤ (MassGap.GibbsSpec.ishift τ (ocrossSite p)) τ
  simp only [MassGap.GibbsSpec.ishift, Function.update_self]
  show p ≤ (p - 1) + 1
  omega

#print axioms ocrossBox_plus_nonempty

/-- The witness box's shared block is inhabited, the straddling plaquette's base `τ`-link supplying
the
witness — `baseTauLink_mem_oboxR` read as an existence claim.

`sum_re_tr_ioplqCross` and `re_tr_hol_oblock` each take a default `dflt : ↥(oboxR τ (2p-1) Λ)` as an
explicit parameter, so a box with an empty shared block admits no application of either.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_oboxR_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    (oboxR τ (2 * p - 1) (ocrossBox τ ν p)).Nonempty :=
  ⟨⟨(τ, (ocrossPlaq τ ν p).2), baseTauLink_mem_box τ p (ocrossBox_cross_nonempty τ ν hν p)⟩,
    baseTauLink_mem_oboxR τ p (ocrossBox_cross_nonempty τ ν hν p)⟩

#print axioms ocrossBox_oboxR_nonempty

/-- And its positive block is inhabited, which is the space the crossing integration integrates over
and
the domain of both half-variables. Were it empty, `x` and `y` would both be the unique empty
function, `oddHalfA` a constant, and `integrand_odd_eq` an identity between two fixed reals.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ocrossBox_oboxS_nonempty (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    (oboxS τ (2 * p - 1) (ocrossBox τ ν p)).Nonempty :=
  ⟨⟨osLinkOf τ (ocrossPlaq τ ν p),
      osLinkOf_mem_box τ p (ocrossBox_cross_nonempty τ ν hν p)⟩,
    osLinkOf_mem_oboxS τ p (ocrossBox_cross_nonempty τ ν hν p)⟩

#print axioms ocrossBox_oboxS_nonempty

/-- A nonempty half-space support inside the witness box: the straddling plaquette's own half-link,
and
nothing else.

`integrand_odd_eq` takes a support `S` with `↑S ⊆ posHalf τ p` and `S ⊆ Λ`; at `S = ∅` its
hypothesis `hf` reads `∀ U V, f U = f V`, so `f` is constant, `obs_ojoin_local` and
`obs_ireflConf_ojoin` both read `c = c`, and only the weight half of the identity carries content.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def ocrossSupp (τ ν : Fin 4) (p : ℤ) : Finset MassGap.InfiniteLattice.ILink :=
  {osLinkOf τ (ocrossPlaq τ ν p)}

#print axioms ocrossSupp

/-- And it is nonempty, being a singleton.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem ocrossSupp_nonempty (τ ν : Fin 4) (p : ℤ) : (ocrossSupp τ ν p).Nonempty :=
  Finset.singleton_nonempty _

#print axioms ocrossSupp_nonempty

/-- It lies in the positive half, at height exactly `p`, since `osLinkOf` steps one `τ` up from a
base
at `p - 1`.

DERIVED: the signature writes no numeral of its own — the odd constant enters only through the
proof's appeal to `osLinkOf_base`; `4` is the dimension. -/
theorem ocrossSupp_subset_posHalf (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    ↑(ocrossSupp τ ν p) ⊆ posHalf τ p := by
  intro l hl
  rw [Finset.mem_coe, ocrossSupp, Finset.mem_singleton] at hl
  subst hl
  show p ≤ (osLinkOf τ (ocrossPlaq τ ν p)).2 τ
  rw [osLinkOf_base τ p (ocrossBox_cross_nonempty τ ν hν p)]
  show p ≤ (MassGap.GibbsSpec.ishift τ (ocrossSite p)) τ
  simp only [MassGap.GibbsSpec.ishift, Function.update_self]
  show p ≤ (p - 1) + 1
  omega

#print axioms ocrossSupp_subset_posHalf

/-- And it lies in the witness box, being a boundary link of a plaquette the box was built around.

DERIVED: the signature writes no numeral of its own — the odd constant enters only through the
proof; `4` is the dimension. -/
theorem ocrossSupp_subset_box (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) :
    ocrossSupp τ ν p ⊆ ocrossBox τ ν p := by
  intro l hl
  rw [ocrossSupp, Finset.mem_singleton] at hl
  subst hl
  exact osLinkOf_mem_box τ p (ocrossBox_cross_nonempty τ ν hν p)

#print axioms ocrossSupp_subset_box


/-- The plane assignment run backwards, first `τ`-link: a half-link at height `p` is the far
transverse
link of the plaquette based one `τ` step down, whose first `τ`-link sits at that base.

No case split. `OddLagSplit.planeARaw` tests which of the torus's two straddling levels the link
sits at; `ℤ⁴` has one mirror. A link this map is wrong about — a `τ`-link, or one no straddling
plaquette of `Λ` owns — is caught by `oplanePick` rather than by a test here.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def oplaneARaw (τ : Fin 4) (l : MassGap.InfiniteLattice.ILink) :
    MassGap.InfiniteLattice.ILink :=
  (τ, MassGap.GibbsSpec.iunshift τ l.2)

#print axioms oplaneARaw

/-- The second one: one transverse step along, in the half-link's own direction.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def oplaneBRaw (τ : Fin 4) (l : MassGap.InfiniteLattice.ILink) :
    MassGap.InfiniteLattice.ILink :=
  (τ, MassGap.GibbsSpec.ishift l.1 (MassGap.GibbsSpec.iunshift τ l.2))

#print axioms oplaneBRaw

/-- The membership gate. `oboxR` is a filter of `Λ` rather than of the whole lattice, so a backward
assignment has to return a link that `Λ` contains and the mirror fixes; this returns the raw link
when both hold and the caller's default `dflt` otherwise.

`oplaneA_osIdx` and `oplaneB_osIdx` show the raw link passes the gate at every half-link the
crossing word reads. Elsewhere the gauge acts by conjugation on a variable the word does not read.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oplanePick (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (m : MassGap.InfiniteLattice.ILink) : ↥(oboxR τ (2 * p - 1) Λ) :=
  if h : m ∈ Λ then
    (if h2 : (⟨m, h⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ then ⟨⟨m, h⟩, h2⟩ else dflt)
  else dflt

#print axioms oplanePick

/-- When the gate passes, the pick is the raw link.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem oplanePick_of_mem (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    {m : MassGap.InfiniteLattice.ILink} (h : m ∈ Λ)
    (h2 : (⟨m, h⟩ : ↥Λ) ∈ oboxR τ (2 * p - 1) Λ) :
    (oplanePick τ p dflt m).1.1 = m := by
  simp only [oplanePick, dif_pos h, dif_pos h2]

#print axioms oplanePick_of_mem

/-- The plane assignment in the types `OddLagSplit.planeAct` takes: a map from the positive half's
index
set to the shared block's, given by `oplaneARaw` through the gate.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oplaneA (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (l : ↥(oboxS τ (2 * p - 1) Λ)) : ↥(oboxR τ (2 * p - 1) Λ) :=
  oplanePick τ p dflt (oplaneARaw τ l.1.1)

#print axioms oplaneA

/-- The second assignment, from `oplaneBRaw` through the same gate.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oplaneB (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (l : ↥(oboxS τ (2 * p - 1) Λ)) : ↥(oboxR τ (2 * p - 1) Λ) :=
  oplanePick τ p dflt (oplaneBRaw τ l.1.1)

#print axioms oplaneB

/-- At the half-link of a straddling plaquette the backward map returns that plaquette's own base
`τ`-link: `GibbsSpec.iunshift` undoes the `τ` step `osLinkOf` took, and `baseTauLink_mem_oboxR`
clears the gate.

`hsRe_ocrossWord_planeAct` holds for any `A` and `B`, so it does not constrain the assignment; this
 lemma and the sum identity do.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem oplaneA_osIdx (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    (oplaneA τ p dflt (osIdx τ p k)).1.1
      = ((τ, (k : MassGap.GibbsSpec.IPlaq).2) : MassGap.InfiniteLattice.ILink) := by
  have hraw : oplaneARaw τ (osIdx τ p k).1.1
      = ((τ, (k : MassGap.GibbsSpec.IPlaq).2) : MassGap.InfiniteLattice.ILink) := by
    show ((τ, MassGap.GibbsSpec.iunshift τ (osLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).2)
      : MassGap.InfiniteLattice.ILink) = (τ, (k : MassGap.GibbsSpec.IPlaq).2)
    rw [osLinkOf_base τ p k.2, MassGap.GibbsSpec.iunshift_ishift]
  show (oplanePick τ p dflt (oplaneARaw τ (osIdx τ p k).1.1)).1.1 = _
  rw [hraw]
  exact oplanePick_of_mem τ p dflt (baseTauLink_mem_box τ p k.2)
    (baseTauLink_mem_oboxR τ p k.2)

#print axioms oplaneA_osIdx

/-- And the second returns `obLinkOf`. The transverse step is taken in the half-link's own
direction,
which `osLinkOf_dir` identifies with the plaquette's `ocDir`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem oplaneB_osIdx (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    (oplaneB τ p dflt (osIdx τ p k)).1.1 = obLinkOf τ (k : MassGap.GibbsSpec.IPlaq) := by
  have hraw : oplaneBRaw τ (osIdx τ p k).1.1 = obLinkOf τ (k : MassGap.GibbsSpec.IPlaq) := by
    show ((τ, MassGap.GibbsSpec.ishift (osLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).1
        (MassGap.GibbsSpec.iunshift τ (osLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).2))
      : MassGap.InfiniteLattice.ILink)
      = (τ, MassGap.GibbsSpec.ishift (ocDir τ (k : MassGap.GibbsSpec.IPlaq))
          (k : MassGap.GibbsSpec.IPlaq).2)
    rw [osLinkOf_dir, osLinkOf_base τ p k.2, MassGap.GibbsSpec.iunshift_ishift]
  show (oplanePick τ p dflt (oplaneBRaw τ (osIdx τ p k).1.1)).1.1 = _
  rw [hraw]
  exact oplanePick_of_mem τ p dflt (obLinkOf_mem_box τ p k.2)
    (obLinkOf_mem_oboxR τ p k.2)

#print axioms oplaneB_osIdx

/-- The mirror carries a straddling plaquette's negative link onto its positive one:
`ireflLink τ (2 * p - 1) (otLinkOf τ q) = osLinkOf τ q`. Both are transverse links in the same
direction, based one `τ` step apart at `p - 1` and `p`, and the reflection about `p - 1/2` exchanges
those two heights. The bases differ, and `iunshift`/`ishift` is by how much. The `ℤ⁴` counterpart of
`OddLagSplit.reflLink_tLinkOf`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ireflLink_otLinkOf (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink} {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ (2 * p - 1) Λ) :
    ireflLink τ (2 * p - 1) (otLinkOf τ q) = osLinkOf τ q := by
  have hbase : q.2 τ = p - 1 := ioplqCross_base τ p hq
  have hsite : ireflSite τ (2 * p - 1) q.2 = MassGap.GibbsSpec.ishift τ q.2 := by
    show Function.update q.2 τ (2 * p - 1 - q.2 τ) = Function.update q.2 τ (q.2 τ + 1)
    have harith : 2 * p - 1 - q.2 τ = q.2 τ + 1 := by omega
    rw [harith]
  have hos : osLinkOf τ q = (ocDir τ q, MassGap.GibbsSpec.ishift τ q.2) := by
    rw [← osLinkOf_dir τ q, ← osLinkOf_base τ p hq]
  rw [hos]
  show ((ocDir τ q, if ocDir τ q = τ then ireflSite τ (2 * p - 1 - 1) q.2
      else ireflSite τ (2 * p - 1) q.2) : MassGap.InfiniteLattice.ILink)
    = (ocDir τ q, MassGap.GibbsSpec.ishift τ q.2)
  rw [if_neg (ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp hq).1).2), hsite]

#print axioms ireflLink_otLinkOf

/-- The three-block configuration, named. `integral_obox_mirror` integrates against exactly this;
naming it lets the straddling sum be stated without repeating the three disjointness proofs and the
cover.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
noncomputable def ojoin (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) : ↥Λ → MassGap.SUN.SU N :=
  MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y

#print axioms ojoin

/-- `ojoin` folded, for rewriting under a binder. `integral_obox_mirror` states its integrand with
`OddLagSplit.join3` spelled out, and `rw` cannot refold that under the three integral binders
because the block variables are bound there, so `simp only` does it with this.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ojoin_def (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) :
    MassGap.OddLagSplit.join3 (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
        (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
        (obox_cover τ c Λ) g x y
      = ojoin τ c Λ g x y := rfl

#print axioms ojoin_def

/-- On the shared block, `ojoin` returns the shared block's variable.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ojoin_mem_R (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) {l : ↥Λ} (hl : l ∈ oboxR τ c Λ) :
    ojoin τ c Λ g x y l = g ⟨l, hl⟩ :=
  MassGap.OddLagSplit.join3_mem_R (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y hl

/-- On the positive block, it returns the positive half's variable.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ojoin_mem_S (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) {l : ↥Λ} (hl : l ∈ oboxS τ c Λ) :
    ojoin τ c Λ g x y l = x ⟨l, hl⟩ :=
  MassGap.OddLagSplit.join3_mem_S (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y hl

/-- And on the negative block, the negative half's.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ojoin_mem_T (τ : Fin 4) (c : ℤ) (Λ : Finset MassGap.InfiniteLattice.ILink)
    (g : ↥(oboxR τ c Λ) → MassGap.SUN.SU N) (x : ↥(oboxS τ c Λ) → MassGap.SUN.SU N)
    (y : ↥(oboxT τ c Λ) → MassGap.SUN.SU N) {l : ↥Λ} (hl : l ∈ oboxT τ c Λ) :
    ojoin τ c Λ g x y l = y ⟨l, hl⟩ :=
  MassGap.OddLagSplit.join3_mem_T (oboxR τ c Λ) (oboxS τ c Λ) (oboxT τ c Λ)
    (obox_disjoint τ c Λ).1 (obox_disjoint τ c Λ).2.1 (obox_disjoint τ c Λ).2.2
    (obox_cover τ c Λ) g x y hl

#print axioms ojoin_mem_R
#print axioms ojoin_mem_S
#print axioms ojoin_mem_T

/-- At a straddling plaquette's negative link, the mirror's variable is the second half-variable
untwisted. That link is transverse, so the dagger branch of `omirrorT` is not taken — the reflection
inverts only on `τ`-links.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem omirrorT_otLinkOf (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    omirrorT τ (2 * p - 1) hΛ y
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩
      = y (osIdx τ p k) := by
  have hne : (otLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).1 ≠ τ :=
    ocDir_ne τ (mem_iplqAll.mp (Finset.mem_filter.mp k.2).1).2
  have heq : omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩
      = osIdx τ p k :=
    Subtype.ext (Subtype.ext (ireflLink_otLinkOf τ p k.2))
  show (if (otLinkOf τ (k : MassGap.GibbsSpec.IPlaq)).1 = τ
      then (y (omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩))⁻¹
      else y (omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨otLinkOf τ (k : MassGap.GibbsSpec.IPlaq), otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1⟩,
          otLinkOf_mem_oboxT τ p k.2⟩)) = y (osIdx τ p k)
  rw [if_neg hne, heq]

#print axioms omirrorT_otLinkOf

/-- One straddling plaquette's contribution in the crossing integration's variables: at the
configuration assembled from the three block variables, the plaquette reads the cross form of the
gauge-acted positive-half variable against the mirror's, and the mirror's transported variable is
the second half-variable.

All four links pass through `GibbsSpec.splice`. On the torus the blocks filter the whole lattice and
the join is already a configuration; here they filter `Λ`, so the holonomy sees the join against a
boundary condition. All four are inside `Λ` — `baseTauLink_mem_box`, `obLinkOf_mem_box`,
`osLinkOf_mem_box`, `otLinkOf_mem_box` — so `ω` is never read and the identity does not depend on
it.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem re_tr_hol_oblock (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (k : ↥(ioplqCross τ (2 * p - 1) Λ)) :
    (Matrix.trace ((MassGap.GibbsSpec.ihol (k : MassGap.GibbsSpec.IPlaq)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
        : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re
      = MassGap.CharacterExpansion.hsRe
          ((MassGap.OddLagSplit.planeAct (oplaneA τ p dflt) (oplaneB τ p dflt) g x
              (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          ((y (osIdx τ p k) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [re_tr_hol_ocross τ p k.2,
    MassGap.GibbsSpec.splice_mem (baseTauLink_mem_box τ p k.2),
    MassGap.GibbsSpec.splice_mem (osLinkOf_mem_box τ p k.2),
    MassGap.GibbsSpec.splice_mem (obLinkOf_mem_box τ p k.2),
    MassGap.GibbsSpec.splice_mem (otLinkOf_mem_box τ (Finset.mem_filter.mp k.2).1),
    ojoin_mem_R τ (2 * p - 1) Λ g x _ (baseTauLink_mem_oboxR τ p k.2),
    ojoin_mem_S τ (2 * p - 1) Λ g x _ (osLinkOf_mem_oboxS τ p k.2),
    ojoin_mem_R τ (2 * p - 1) Λ g x _ (obLinkOf_mem_oboxR τ p k.2),
    ojoin_mem_T τ (2 * p - 1) Λ g x _ (otLinkOf_mem_oboxT τ p k.2),
    omirrorT_otLinkOf τ p hΛ y k]
  have hA : (⟨⟨((τ, (k : MassGap.GibbsSpec.IPlaq).2) : MassGap.InfiniteLattice.ILink),
        baseTauLink_mem_box τ p k.2⟩, baseTauLink_mem_oboxR τ p k.2⟩
        : ↥(oboxR τ (2 * p - 1) Λ))
      = oplaneA τ p dflt (osIdx τ p k) :=
    Subtype.ext (Subtype.ext (oplaneA_osIdx τ p dflt k).symm)
  have hB : (⟨⟨obLinkOf τ (k : MassGap.GibbsSpec.IPlaq), obLinkOf_mem_box τ p k.2⟩,
        obLinkOf_mem_oboxR τ p k.2⟩ : ↥(oboxR τ (2 * p - 1) Λ))
      = oplaneB τ p dflt (osIdx τ p k) :=
    Subtype.ext (Subtype.ext (oplaneB_osIdx τ p dflt k).symm)
  rw [hA, hB]
  rfl

#print axioms re_tr_hol_oblock

/-- The whole straddling sum is one cross form. `ioplqCross` indexes the blocks directly, so the sum
over the `Finset` is the sum over the block index, and `hsRe_ocrossWord` folds it into a single
`hsRe`. Both orientations of every geometric plaquette appear and carry the same number; the direct
sum holds the block twice.

This is where `oplaneA` and `oplaneB` have to be the plaquette's own `τ`-links:
`hsRe_ocrossWord_planeAct` holds for any assignment, and this identity does not.

With `integral_obox_mirror` it puts the odd-constant pairing in the shape
`CrossingIntegration.wilson_crossing_pairing_nonneg` takes.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem sum_re_tr_ioplqCross (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    (∑ q ∈ ioplqCross τ (2 * p - 1) Λ,
        (Matrix.trace ((MassGap.GibbsSpec.ihol q
          (MassGap.GibbsSpec.splice Λ
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
          : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re)
      = MassGap.CharacterExpansion.hsRe
          (ocrossWord τ p (MassGap.OddLagSplit.planeAct
            (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
          (ocrossWord τ p y) := by
  rw [← Finset.sum_coe_sort (ioplqCross τ (2 * p - 1) Λ)
    (fun q => (Matrix.trace ((MassGap.GibbsSpec.ihol q
      (MassGap.GibbsSpec.splice Λ
        (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
      : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)).re), hsRe_ocrossWord]
  exact Finset.sum_congr rfl
    (fun k _ => re_tr_hol_oblock τ p hΛ dflt ω g x y k)

#print axioms sum_re_tr_ioplqCross

/-- Every coordinate of the word is bounded by `1` — the `hXb` the crossing kernel takes. Each is a
unitary entry on a diagonal block or `0` off one, and
`OddLagSplit.entry_blockDiagonal_fin_norm_le_one` is abstract in the block index.

DERIVED: `1` is the bound a unitary entry carries (`SUN.unitary_entry_norm_le_one`), not a chosen
cut; the `2` and the `1` in the constant make it odd. `4` is the dimension. -/
theorem abs_coord_ocrossWord_le_one (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (c : MassGap.CharacterExpansion.Coord
      (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ))))
    (u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    |MassGap.CharacterExpansion.coord c (ocrossWord τ p u)| ≤ 1 :=
  MassGap.OddLagSplit.abs_coord_le_one_of_entries
    (fun i j => MassGap.OddLagSplit.entry_blockDiagonal_fin_norm_le_one
      (fun k => u (osIdx τ p k)) i j) c

#print axioms abs_coord_ocrossWord_le_one

/-- Every entry of the word is measurable in the half-variable, by the same abstract lemma
(`OddLagSplit.measurable_entry_blockDiagonal_fin`).

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem measurable_entry_ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (i j : Fin (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ)))) :
    Measurable (fun u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N =>
      ocrossWord τ p u i j) :=
  MassGap.OddLagSplit.measurable_entry_blockDiagonal_fin
    (fun (u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
      (k : ↥(ioplqCross τ (2 * p - 1) Λ)) => u (osIdx τ p k))
    (fun _ => measurable_pi_apply _) i j

#print axioms measurable_entry_ocrossWord

/-- And so is every coordinate — the `hXm` the crossing kernel takes.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem measurable_coord_ocrossWord (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (c : MassGap.CharacterExpansion.Coord
      (Fintype.card (Fin N × ↥(ioplqCross τ (2 * p - 1) Λ)))) :
    Measurable (fun u : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N =>
      MassGap.CharacterExpansion.coord c (ocrossWord τ p u)) :=
  MassGap.OddLagSplit.measurable_coord_of_entries _ (measurable_entry_ocrossWord τ p) c

#print axioms measurable_coord_ocrossWord

/-- The straddling part of the Wilson action in the crossing engine's variables: since
`wilsonDensity W = 1 - (1/N) · Re tr W`, it is the cardinality of `ioplqCross τ c Λ` minus `1/N`
times the sum of the words' real traces. `sum_re_tr_ioplqCross` turns that sum into one cross form.

An algebraic identity, carrying no `β`. The trace enters negatively, so
`e^{-β·S_cross} = e^{-β·card} · e^{(β/N)·(cross form)}` and the exponent reaching the kernel is
`β/N`, which is how `0 ≤ β` becomes
`CrossingIntegration.wilson_crossing_pairing_nonneg`'s `hβ`; that hypothesis is stated where it is
used, and `CrossingIntegration.NegControl.su3_kernel_nonneg_iff` shows the Wilson cross kernel is
not positive-semidefinite at negative coupling. The `ℤ⁴` counterpart of
`OddLagSplit.actCrossO_eq_trace_sum`.

DERIVED: `1` is the value of `wilsonDensity` at zero trace and the numerator of `1/N`; `N` is the
rank. Both come from `WilsonAction.wilsonDensity`, not from here. `4` is the dimension. -/
theorem iactCross_eq_trace_sum (τ : Fin 4) (c : ℤ)
    (Λ : Finset MassGap.InfiniteLattice.ILink)
    (U : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity (ioplqCross τ c Λ) U
      = ((ioplqCross τ c Λ).card : ℝ)
        - (1 / (N : ℝ)) * ∑ q ∈ ioplqCross τ c Λ,
            (Matrix.trace ((MassGap.GibbsSpec.ihol q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := by
  unfold MassGap.GibbsSpec.actionOn
  have hterm : ∀ q ∈ ioplqCross τ c Λ,
      MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q U)
        = 1 - (1 / (N : ℝ))
          * (Matrix.trace ((MassGap.GibbsSpec.ihol q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := fun q _ => rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one, Finset.mul_sum]

#print axioms iactCross_eq_trace_sum

/-! ### The odd crossing structure on `ℤ⁴`, and how it differs from the torus

The geometric inputs `CrossingIntegration.wilson_crossing_pairing_nonneg` reads are the four link
roles (`(τ, q.2)`, `obLinkOf`, `osLinkOf`, `otLinkOf`), the per-plaquette identity
`re_tr_hol_ocross`, the assignment `oplaneA`/`oplaneB` with `oplaneA_osIdx`/`oplaneB_osIdx`, the
word `ocrossWord` with its `hXinv` (`hsRe_ocrossWord_planeAct`), and the sum identity
`sum_re_tr_ioplqCross`. `OddLagSplit.planeAct_measurePreserving` and
`OddLagSplit.measurable_uncurry_planeAct` are abstract in `{ι κ}` and apply at these index types
unchanged.

`OddLagSplit.planeARaw` tests two straddling levels, `1` and `m`, because a periodic lattice has two
mirror planes; they are disjoint only when `1 ≠ m`, which is that development's `2 ≤ m` hypothesis,
and at `m = 1` a single link is owned by two plaquettes with different plane links. `ℤ⁴` has one
mirror: a transverse link at height `p` is the far link of the plaquette based at `p - 1`,
`oplaneARaw` carries no case split, and no analogue of `2 ≤ m` appears. The same collapse removes
`OddLagSplit.invLink` and `OddLagSplit.uplane`, which put the torus's two planes into one
handedness. The orientation reconciliation does not collapse: `re_tr_hol_ocross` inlines it in its
second branch, where `OddLagSplit.re_tr_hol_swap`'s `group` and `OddLagSplit.re_trace_inv` reappear.

The periodic blocks filter the whole lattice, so an assignment there may return any fixed default
and its membership in `OddLagSplit.oblkR` is automatic. `oboxR` filters `Λ`, so a default has to lie
in `Λ`, and for a half-link that is the `osLinkOf` of no straddling plaquette of `Λ` the owning
plaquette's `τ`-links need not be in `Λ` either. Hence `oplanePick`, which decides membership, and a
default carried as an explicit parameter, so the requirement sits in the signature rather than in a
nonemptiness assumption. The same layer appears in `re_tr_hol_oblock`, where the joined
configuration reaches the holonomy through `GibbsSpec.splice`. -/

/-! ### Two hypotheses of the even pairing lemma at an odd constant

`ActionSplit.pairing_nonneg_of_local` is the lemma the even chain instantiates. Two of its
hypotheses read differently at an odd constant.

`hσR : ∀ i ∈ R, ∀ u, σ i u = u` asks the twist to act trivially on the shared block. `σ` on a
`τ`-link is `ilinkDagger τ`, which is inversion, and at an odd constant the shared block is the
`τ`-links straddling the mirror (`odd_tau_fixed_iff`), where
`LatticeReflection.ireflConf_inverts_fixed_axis_link` says it inverts. Inversion is the identity
only on elements with `g = g⁻¹`.

`hWloc : ∀ U V, (∀ i ∈ R, U i = V i) → W U = W V` asks the weight to read `R` alone. At an odd
constant `W = e^{-βA_cross}` reads the straddling plaquettes, and those touch all three blocks: a
cross plaquette `((τ, ν), x)` based at `x_τ = p - 1` reads two links in `ioblkR`, one in `ioblkS` at
height `p`, and one in `ioblkT` at height `p - 1`.

`CrossingIntegration.wilson_crossing_pairing_nonneg` takes neither hypothesis: it integrates the
shared block out against a positive-semidefinite kernel rather than factoring it out as a constant,
and that is where `0 ≤ β` enters. `OddLagSplit` is arranged the same way. -/

/-- The reflection carries the positive plaquettes into the negative ones, by involutivity, as for
the
links: a plaquette whose base it moves down has an image whose base it moves up. Holds at any
constant, given the box's stability.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflPlaq_ioplqPlus_mem_ioplqMinus (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqPlus τ c Λ) : ireflPlaq τ c q ∈ ioplqMinus τ c Λ := by
  simp only [ioplqPlus, Finset.mem_filter] at hq
  simp only [ioplqMinus, Finset.mem_filter]
  refine ⟨ireflPlaq_mem_iplqAll τ c hΛ hq.1, ?_⟩
  rw [ireflPlaq_involutive τ c q]
  exact hq.2

#print axioms ireflPlaq_ioplqPlus_mem_ioplqMinus

/-- And back, which is what the bijection in the covariance proof needs on both sides.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflPlaq_ioplqMinus_mem_ioplqPlus (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqMinus τ c Λ) : ireflPlaq τ c q ∈ ioplqPlus τ c Λ := by
  simp only [ioplqMinus, Finset.mem_filter] at hq
  simp only [ioplqPlus, Finset.mem_filter]
  refine ⟨ireflPlaq_mem_iplqAll τ c hΛ hq.1, ?_⟩
  rw [ireflPlaq_involutive τ c q]
  exact hq.2

#print axioms ireflPlaq_ioplqMinus_mem_ioplqPlus

/-- The odd covariance `A₊(ΘU) = A₋(U)`, at a free constant `c` and for a class function `φ`. The
reflection is a bijection from the positive plaquettes to the negative ones, and on each the
mirrored holonomy is conjugate to the image's, which `hφ` does not see —
`action_iplqPlus_ireflConf`'s
argument with the constant left free.

The straddling term has no partner block: the reflection maps it to itself, and
`ioplqCross_actionOn_ireflConf` states `A_cross(ΘU) = A_cross(U)`. That, with the twist inverting
the axis links it reads, is why the odd case carries `0 ≤ β` where the even case does not.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplqPlus_actionOn_ireflConf {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (ioplqMinus τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_ioplqPlus_mem_ioplqMinus τ c hΛ ha)
    (fun b hb => ireflPlaq_ioplqMinus_mem_ioplqPlus τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms ioplqPlus_actionOn_ireflConf

/-- The reflection maps the straddling plaquettes to themselves: a base it does not move stays
unmoved
under the image, by involutivity.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ireflPlaq_ioplqCross_mem_ioplqCross (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) {q : MassGap.GibbsSpec.IPlaq}
    (hq : q ∈ ioplqCross τ c Λ) : ireflPlaq τ c q ∈ ioplqCross τ c Λ := by
  simp only [ioplqCross, Finset.mem_filter] at hq
  simp only [ioplqCross, Finset.mem_filter]
  refine ⟨ireflPlaq_mem_iplqAll τ c hΛ hq.1, ?_⟩
  rw [ireflPlaq_involutive τ c q]
  exact hq.2.symm

#print axioms ireflPlaq_ioplqCross_mem_ioplqCross

/-- The straddling action is invariant under the reflection: `A_cross(ΘU) = A_cross(U)`, for a class
function `φ`. The same bijection argument as the covariance, with `ioplqCross` mapped to itself
instead of to a mirror partner.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplqCross_actionOn_ireflConf {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_ioplqCross_mem_ioplqCross τ c hΛ ha)
    (fun b hb => ireflPlaq_ioplqCross_mem_ioplqCross τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms ioplqCross_actionOn_ireflConf

/-- The mirror statement, `A₋(ΘU) = A₊(U)`: the same bijection with the two block memberships
swapped.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem ioplqMinus_actionOn_ireflConf {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (ioplqMinus τ c Λ) (ireflConf τ c U)
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) U := by
  unfold MassGap.GibbsSpec.actionOn
  refine Finset.sum_nbij' (i := fun q => ireflPlaq τ c q)
    (j := fun q => ireflPlaq τ c q)
    (fun a ha => ireflPlaq_ioplqMinus_mem_ioplqPlus τ c hΛ ha)
    (fun b hb => ireflPlaq_ioplqPlus_mem_ioplqMinus τ c hΛ hb)
    (fun a _ => ireflPlaq_involutive τ c a)
    (fun b _ => ireflPlaq_involutive τ c b)
    (fun a _ => ?_)
  obtain ⟨g, hg⟩ := ihol_ireflConf τ c a U
  rw [gibbs_ihol_eq, gibbs_ihol_eq, hg, hφ]

#print axioms ioplqMinus_actionOn_ireflConf

/-- The odd split in paired form,

    A(U) = A₊(U) + A₊(ΘU) + A_cross(U),

with the same `A₊` on both of the first two summands, which is what exponentiates to
`e^{-βA(U)} = h(U) · h(ΘU) · W(U)` with `h = e^{-βA₊}` and `W = e^{-βA_cross}`. From
`ioplq_actionOn_split` and `ioplqPlus_actionOn_ireflConf`; the paired shape comes from the latter,
which invariance of the whole action (`action_iplqAll_ireflConf`) does not give. The `ℤ⁴`
counterpart of `OddLagSplit.action_eq_split_odd`.

DERIVED: `c` is the caller's reflection constant; `4` is the dimension. -/
theorem iodd_action_paired {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ) (U : MassGap.GibbsSpec.IConf G) :
    MassGap.GibbsSpec.actionOn φ (iplqAll Λ) U
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) U
        + MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ) (ireflConf τ c U)
        + MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ) U := by
  rw [ioplq_actionOn_split φ τ c Λ U, ioplqPlus_actionOn_ireflConf φ hφ τ c hΛ U]

#print axioms iodd_action_paired

/-- The free-boundary Boltzmann weight in paired form,
`wtFree = h(u) · h(Θu) · W_cross(u)` with `h = e^{-βA₊}` and `W_cross = e^{-βA_cross}`:
`iodd_action_paired` exponentiated. This is the shape
`CrossingIntegration.wilson_crossing_pairing_nonneg` consumes.

At an even constant the third factor reads the shared block alone, so it comes out of both inner
integrals and the pairing is a square. At an odd constant `A_cross` sums over plaquettes touching
all three blocks (`otLinkOf_mem_oboxT` beside `osLinkOf_mem_oboxS`), so `W_cross` does not factor
out and the pairing is an integral against a kernel, which is where `0 ≤ β` enters. The `ℤ⁴`
counterpart of `OddLagSplit.boltz_eq_paired_cross`.

DERIVED: the signature writes no numeral; `c` is the caller's reflection constant and `4` is the
dimension. -/
theorem wtFree_odd_paired {G : Type} [Group G] (φ : G → ℝ)
    (hφ : ∀ g h : G, φ (g * h * g⁻¹) = φ h) (τ : Fin 4) (c : ℤ) (β : ℝ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf G) (u : MassGap.GibbsSpec.VConf G Λ) :
    wtFree φ β Λ ω u
      = Real.exp (-β * MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ)
            (MassGap.GibbsSpec.splice Λ u ω))
        * Real.exp (-β * MassGap.GibbsSpec.actionOn φ (ioplqPlus τ c Λ)
            (MassGap.LatticeReflection.ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)))
        * Real.exp (-β * MassGap.GibbsSpec.actionOn φ (ioplqCross τ c Λ)
            (MassGap.GibbsSpec.splice Λ u ω)) := by
  have hsum : ∀ a b d : ℝ, -β * (a + b + d) = -β * a + -β * b + -β * d := by
    intro a b d
    ring
  show Real.exp (-β * MassGap.GibbsSpec.actionOn φ (iplqAll Λ)
      (MassGap.GibbsSpec.splice Λ u ω)) = _
  rw [iodd_action_paired φ hφ τ c hΛ (MassGap.GibbsSpec.splice Λ u ω), hsum,
    Real.exp_add, Real.exp_add]

#print axioms wtFree_odd_paired

/-- The positive half-action at an odd constant is a function of the positive half alone: changing
the
shared block variable `g` and the mirror block variable `y` does not move it. `ioplqPlus_links_mem`
is what carries it — every boundary link of a positive plaquette is in `ioblkS`, `S` only rather
than `S ∪ R`, which is where the odd constant differs from the even one.

This is what lets `h(U) = e^{-βA₊(U)}` in `wtFree_odd_paired` be the `a : Ω → ℝ` that
`CrossingIntegration.wilson_crossing_pairing_nonneg` takes: a function of the half, not of the whole
configuration. The `ℤ⁴` counterpart of `OddLagSplit.actPlusO_local`.

DERIVED: the `2` and the `1` make the constant odd, which is what collapses the two locality
thresholds into one; `4` is the dimension. -/
theorem actionOn_ioplqPlus_ojoin (φ : MassGap.SUN.SU N → ℝ) (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g x y) ω)
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' x y') ω) := by
  refine MassGap.GibbsSpec.actionOn_congr φ _ _ _ (fun q hq l hl => ?_)
  have hS : l ∈ ioblkS τ (2 * p - 1) Λ := ioplqPlus_links_mem τ p hq hl
  have hlΛ : l ∈ Λ := (Finset.mem_filter.mp hS).1
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ,
    ojoin_mem_S τ (2 * p - 1) Λ g x y (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hS),
    ojoin_mem_S τ (2 * p - 1) Λ g' x y' (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hS)]

#print axioms actionOn_ioplqPlus_ojoin

/-- On the positive block, the reflected configuration assembled with the mirror transport reads the
second half-variable outright: `ireflConf τ (2p-1) (splice Λ (ojoin g x (omirrorT y)) ω) l` equals
`splice Λ (ojoin g' y y') ω l` for `l ∈ ioblkS τ (2p-1) Λ`.

The two daggers cancel. `ireflConf` inverts on `τ`-links and `omirrorT` carries the same dagger, so
on the positive block the composition is `inv_inv`, with no appeal to conjugation invariance of `φ`
and no trace identity; off the `τ`-links neither inverts and the two agree directly.

Both inner integrals therefore run over `oboxS` against the same measure and read the same
`a : Ω → ℝ`, which is the shape
`CrossingIntegration.wilson_crossing_pairing_nonneg` consumes.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem ireflConf_ojoin_eq_on_ioblkS (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    {l : MassGap.InfiniteLattice.ILink} (hS : l ∈ ioblkS τ (2 * p - 1) Λ) :
    MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω) l
      = MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' y y') ω l := by
  have hlΛ : l ∈ Λ := (Finset.mem_filter.mp hS).1
  have hlS : (⟨l, hlΛ⟩ : ↥Λ) ∈ oboxS τ (2 * p - 1) Λ :=
    mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hS
  have hrΛ : ireflLink τ (2 * p - 1) l ∈ Λ := hΛ l hlΛ
  have hrT : (⟨ireflLink τ (2 * p - 1) l, hrΛ⟩ : ↥Λ) ∈ oboxT τ (2 * p - 1) Λ :=
    ireflBoxPerm_mem_oboxT_of_mem_oboxS τ (2 * p - 1) hΛ hlS
  have heq : omirrorEquivTS τ (2 * p - 1) hΛ
        ⟨⟨ireflLink τ (2 * p - 1) l, hrΛ⟩, hrT⟩
      = ⟨⟨l, hlΛ⟩, hlS⟩ :=
    Subtype.ext (Subtype.ext (MassGap.LatticeReflection.ireflLink_involutive τ (2 * p - 1) l))
  have hmir : omirrorT τ (2 * p - 1) hΛ y ⟨⟨ireflLink τ (2 * p - 1) l, hrΛ⟩, hrT⟩
      = if l.1 = τ then (y ⟨⟨l, hlΛ⟩, hlS⟩)⁻¹ else y ⟨⟨l, hlΛ⟩, hlS⟩ := by
    simp only [omirrorT, MassGap.LatticeReflection.ireflLink_fst, heq]
  simp only [MassGap.LatticeReflection.ireflConf]
  rw [MassGap.GibbsSpec.splice_mem hlΛ,
    ojoin_mem_S τ (2 * p - 1) Λ g' y y' hlS,
    MassGap.GibbsSpec.splice_mem hrΛ,
    ojoin_mem_T τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y) hrT,
    hmir]
  by_cases hτ : l.1 = τ
  · rw [if_pos hτ, if_pos hτ, inv_inv]
  · rw [if_neg hτ, if_neg hτ]

#print axioms ireflConf_ojoin_eq_on_ioblkS

/-- And so the mirror factor of the action is the same function at the second half-variable:
`GibbsSpec.actionOn_congr` with `ioplqPlus_links_mem`, since a positive plaquette reads only links
of `ioblkS` and `ireflConf_ojoin_eq_on_ioblkS` covers those.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem actionOn_ioplqPlus_ireflConf_ojoin (φ : MassGap.SUN.SU N → ℝ) (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
          (MassGap.GibbsSpec.splice Λ
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      = MassGap.GibbsSpec.actionOn φ (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' y y') ω) :=
  MassGap.GibbsSpec.actionOn_congr φ _ _ _
    (fun q hq l hl => ireflConf_ojoin_eq_on_ioblkS τ p hΛ ω g g' x y y'
      (ioplqPlus_links_mem τ p hq hl))

#print axioms actionOn_ioplqPlus_ireflConf_ojoin

/-- An observable whose support `S` lies in `posHalf τ p` and inside `Λ` is a function of the
positive
half alone: changing the shared block variable and the mirror block variable does not move it.

`ioblkS_of_le_coord` sends any link of `Λ` at height `≥ p` into the positive block — `τ`-link or
transverse — because a `τ`-link needs `2x > 2p - 2`, a transverse one `2x > 2p - 1`, and no even
number lies between. At an even constant the two thresholds separate and a half-space-supported
observable can reach the shared block, so the statement is specific to the odd constant.

DERIVED: the `2` and the `1` make the constant odd, which is what collapses the two thresholds; `4`
is the dimension. -/
theorem obs_ojoin_local (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g x y) ω)
      = f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' x y') ω) := by
  refine hf _ _ (fun lk hlk => ?_)
  have hlΛ : lk ∈ Λ := hSΛ hlk
  have hSb : lk ∈ ioblkS τ (2 * p - 1) Λ :=
    ioblkS_of_le_coord τ p hlΛ (hS (Finset.mem_coe.mpr hlk))
  rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ,
    ojoin_mem_S τ (2 * p - 1) Λ g x y (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hSb),
    ojoin_mem_S τ (2 * p - 1) Λ g' x y' (mem_oboxS_of_mem_ioblkS τ (2 * p - 1) hSb)]

#print axioms obs_ojoin_local

/-- And its reflection is the same observable at the second half-variable — the statement
`actionOn_ioplqPlus_ireflConf_ojoin` makes for the action, from the same pointwise lemma
`ireflConf_ojoin_eq_on_ioblkS`, because both read only links of `ioblkS`.

With `obs_ojoin_local` this turns `ν(ΘF · F)` into an integral of `a(x) · a(y)` against a kernel in
`x` and `y`: two independent draws from one space, read by one function.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem obs_ireflConf_ojoin (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (g g' : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (y' : ↥(oboxT τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    f (MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      = f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ g' y y') ω) :=
  hf _ _ (fun lk hlk => ireflConf_ojoin_eq_on_ioblkS τ p hΛ ω g g' x y y'
    (ioblkS_of_le_coord τ p (hSΛ hlk) (hS (Finset.mem_coe.mpr hlk))))

#print axioms obs_ireflConf_ojoin

/-- The straddling factor is a constant times the crossing kernel,

    e^{-β·A_cross} = e^{-β·card} · e^{(β/N)·hsRe(X(g·x), X(y))}.

`iactCross_eq_trace_sum` turns the straddling action into its cardinality minus `1/N` times a sum of
real traces, and `sum_re_tr_ioplqCross` turns that sum into one cross form of the crossing word.
What is left is the kernel `CrossingIntegration.wilson_crossing_pairing_nonneg` integrates.

An identity at every real `β`, asserting no nonnegativity. It fixes the sign: `wilsonDensity` enters
the action with a minus on the trace, so `e^{-βA_cross}` carries `+β/N` on the cross form, and the
exponent reaching the kernel is `β/N`. `0 ≤ β` is stated where the kernel is applied, and
`CrossingIntegration.NegControl.su3_kernel_nonneg_iff` shows the Wilson cross kernel is not
positive-semidefinite below zero.

DERIVED: the `2` and the `1` make the constant odd; `N` is the rank, from
`WilsonAction.wilsonDensity` and not chosen here; `4` is the dimension. -/
theorem exp_cross_ojoin (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    Real.exp (-β * MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity
        (ioplqCross τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
            (ocrossWord τ p (MassGap.OddLagSplit.planeAct
              (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
            (ocrossWord τ p y)) := by
  rw [iactCross_eq_trace_sum τ (2 * p - 1) Λ
      (MassGap.GibbsSpec.splice Λ
        (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω),
    sum_re_tr_ioplqCross τ p hΛ dflt ω g x y]
  have harith : ∀ C H : ℝ, -β * (C - (1 / (N : ℝ)) * H)
      = -β * C + (β / (N : ℝ)) * H := by
    intro C H
    ring
  rw [harith, Real.exp_add]

#print axioms exp_cross_ojoin

/-- The observable the crossing integration takes as its `a : Ω → ℝ`: the observable `f` times the
positive half-weight, read at the configuration assembled with the constant-one gauge on the shared
and mirror blocks. No inhabitant of `oboxR` or `oboxT` is needed, `1` being `Pi.one`.

The two factors ignore those reference values for different reasons. The weight factor ignores them
unconditionally, by `actionOn_ioplqPlus_ojoin`, which carries no hypothesis because
`ioplqPlus_links_mem` puts every link a positive plaquette reads in `ioblkS`. The observable factor
ignores them when `f` has half-space support, which is `obs_ojoin_local`'s hypothesis and which this
definition does not require: `f` here is arbitrary, so at a general `f` the value depends on the
choice. A caller that needs the choice to be immaterial supplies that support.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. The `1`s in the body are
the group identity. -/
noncomputable def oddHalfA (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) : ℝ :=
  f (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ 1 x 1) ω)
    * Real.exp (-β * MassGap.GibbsSpec.actionOn MassGap.WilsonAction.wilsonDensity
        (ioplqPlus τ (2 * p - 1) Λ)
        (MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ 1 x 1) ω))

#print axioms oddHalfA

/-- The configuration `oddHalfA` reads is a measurable function of the half-variable —
`GibbsSpec.measurable_splice_left` composed with `measurable_obox_join3_mid`.

DERIVED: the `2` and the `1` of the constant make it odd; the two other `1`s are the group identity,
the constant-one gauge on the shared and mirror blocks; `4` is the dimension. -/
theorem measurable_oddHalfA_conf (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    Measurable (fun x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N =>
      MassGap.GibbsSpec.splice Λ (ojoin τ (2 * p - 1) Λ 1 x 1) ω) :=
  (MassGap.GibbsSpec.measurable_splice_left Λ ω).comp
    (measurable_obox_join3_mid τ (2 * p - 1) Λ 1 1)

#print axioms measurable_oddHalfA_conf

/-- `oddHalfA` is measurable — the `ham` the crossing kernel takes — given that `f` is.
Measurability of
`f` is a hypothesis because `oddHalfA` takes an arbitrary `f`; the torus twin gets it from `aObs`'s
concrete definition (`OddLagSplit.measurable_aHalf`).

DERIVED: the signature writes no numeral of its own — the odd constant reaches this only through
`oddHalfA`'s body; `4` is the dimension. -/
theorem measurable_oddHalfA (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} (hfm : Measurable f) :
    Measurable (oddHalfA (Λ := Λ) τ p ω β f) :=
  (hfm.comp (measurable_oddHalfA_conf τ p ω)).mul
    ((((MassGap.GibbsSpec.measurable_actionOn
        MassGap.WilsonAction.measurable_wilsonDensity
        (ioplqPlus τ (2 * p - 1) Λ)).comp
      (measurable_oddHalfA_conf τ p ω)).const_mul (-β)).exp)

#print axioms measurable_oddHalfA

/-- `oddHalfA` is bounded — the `hab` the crossing kernel takes — given that `f` is. The positive
half-weight is bounded because the Wilson density lies in `[0, 2]` (`abs_exp_neg_actionOn_le`), so
the bound is the observable's own times a factor set by the number of positive plaquettes and the
coupling, both the caller's.

DERIVED: the `2` is the range of the Wilson density (`WilsonAction.wilsonDensity_le_two`), the
cardinality is the positive plaquette set's own, and the `2` and `1` of the constant make it odd;
`4` is the dimension. The `0`s are the one in `N ≠ 0` and the sign in `0 ≤ CF`. -/
theorem abs_oddHalfA_le (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ) (hN : N ≠ 0)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hfb : ∀ U, |f U| ≤ CF)
    (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    |oddHalfA τ p ω β f x|
      ≤ CF * Real.exp (|β| * (((ioplqPlus τ (2 * p - 1) Λ).card : ℝ) * 2)) := by
  rw [oddHalfA, abs_mul]
  refine mul_le_mul (hfb _) ?_ (abs_nonneg _) hCF
  exact abs_exp_neg_actionOn_le (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) β _ _

#print axioms abs_oddHalfA_le


/-- The pairing integrand in the crossing integration's variables:

    f(ΘU) · f(U) · W(U)  =  const · (a(x) · a(y) · e^{(β/N)·hsRe(X(g·x), X(y))})

pointwise, at the configuration assembled from the three block variables with the mirror transport.
The factors come from `obs_ireflConf_ojoin` and `obs_ojoin_local` for the observable,
`actionOn_ioplqPlus_ireflConf_ojoin` and `actionOn_ioplqPlus_ojoin` for the two half-weights, and
`exp_cross_ojoin` for the straddling factor.

`CrossingIntegration.wilson_crossing_pairing_nonneg` takes `a x * a y * exp (β * hsRe …)`, with no
constant factor and `β` multiplying `hsRe` directly, so it is instantiated at `β' = β/N` and the
constant is pulled out first. The parenthesisation here puts the constant outermost and leftmost for
that reason, matching `OddLagSplit.oddIntegrand_join`, so `integral_const_mul` fires with no
reassociation.

`a` appears once at `x` and once at `y` — one function of one space, which is what `omirrorT`'s
dagger provides.

DERIVED: the `2` and the `1` make the constant odd; `N` is the rank; `4` is the dimension. -/
theorem integrand_odd_eq (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V)
    (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
    (x y : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N) :
    f (MassGap.LatticeReflection.ireflConf τ (2 * p - 1)
        (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω))
      * f (MassGap.GibbsSpec.splice Λ
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)) ω)
      * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
          * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
              (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
              (ocrossWord τ p y))) := by
  rw [wtFree_odd_paired MassGap.WilsonAction.wilsonDensity
      (fun a b => MassGap.WilsonAction.wilsonDensity_conj a b) τ (2 * p - 1) β hΛ ω
      (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y)),
    obs_ireflConf_ojoin τ p hΛ ω g 1 x y 1 S hS hSΛ f hf,
    obs_ojoin_local τ p ω g 1 x (omirrorT τ (2 * p - 1) hΛ y) 1 S hS hSΛ f hf,
    actionOn_ioplqPlus_ojoin MassGap.WilsonAction.wilsonDensity τ p ω g 1 x
      (omirrorT τ (2 * p - 1) hΛ y) 1,
    actionOn_ioplqPlus_ireflConf_ojoin MassGap.WilsonAction.wilsonDensity τ p hΛ ω g 1 x y 1,
    exp_cross_ojoin τ p hΛ dflt ω β g x y]
  unfold oddHalfA
  ring

#print axioms integrand_odd_eq

/-- The pairing integrand on the box: `f(ΘU) · f(U)` against the free-boundary Wilson weight, with
`Θ`
the reflection at the odd constant `2 * p - 1`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
noncomputable def oddPairIntegrand (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ)
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) : ℝ :=
  f (MassGap.LatticeReflection.ireflConf τ (2 * p - 1) (MassGap.GibbsSpec.splice Λ u ω))
    * f (MassGap.GibbsSpec.splice Λ u ω)
    * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω u

#print axioms oddPairIntegrand

/-- The pairing integrand is measurable, given that `f` is. The reflection is continuous
(`LatticeReflection.continuous_ireflConf`), so the reflected factor costs only a composition.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem measurable_oddPairIntegrand (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} (hfm : Measurable f) :
    Measurable (oddPairIntegrand (Λ := Λ) τ p ω β f) :=
  ((hfm.comp (((MassGap.LatticeReflection.continuous_ireflConf τ
        (2 * p - 1)).measurable).comp
      (MassGap.GibbsSpec.measurable_splice_left Λ ω))).mul
    (hfm.comp (MassGap.GibbsSpec.measurable_splice_left Λ ω))).mul
    (measurable_wtFree MassGap.WilsonAction.measurable_wilsonDensity β Λ ω)

#print axioms measurable_oddPairIntegrand

/-- The pairing integrand is bounded by two copies of the observable's bound times the weight's,
which
is `wtFree_le` and rests on the Wilson density lying in `[0, 2]`.

DERIVED: the `2` is the range of the Wilson density (`WilsonAction.wilsonDensity_le_two`) and the
cardinality is the box's own plaquette set; the `0` is the sign in `N ≠ 0` and in `0 ≤ CF`; `4` is
the dimension. -/
theorem abs_oddPairIntegrand_le (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) (β : ℝ) (hN : N ≠ 0)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hfb : ∀ U, |f U| ≤ CF)
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    |oddPairIntegrand τ p ω β f u|
      ≤ CF * CF * Real.exp (|β| * (((iplqAll Λ).card : ℝ) * 2)) := by
  rw [oddPairIntegrand, abs_mul, abs_mul]
  refine mul_le_mul (mul_le_mul (hfb _) (hfb _) (abs_nonneg _) hCF) ?_ (abs_nonneg _)
    (by positivity)
  exact wtFree_le (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω u

#print axioms abs_oddPairIntegrand_le

/-- `0 ≤ ∫ f(ΘU) · f(U) · W(U)` over the box, for `f` supported in the positive half-space and
`0 ≤ β`, at the odd constant `2 * p - 1` — Osterwalder–Seiler reflection positivity at a link
reflection on `ℤ⁴`, the mirror at `p - 1/2` that cuts `τ`-links.

`integral_obox_mirror` puts both half-variables on `oboxS`, `integrand_odd_eq` identifies the
integrand, `integral_const_mul` takes the constant out through all three integrals, and
`CrossingIntegration.wilson_crossing_pairing_nonneg` — abstract in the group, the space and the word
— closes it. The same argument as `OddLagSplit.odd_crossing_integral_nonneg`, re-derived because
that lemma is the torus statement and carries `hm : n = 2 * m` and `2 ≤ m`.

`0 ≤ β` is used once, at the end, as `0 ≤ β/N`; everything before is an identity.
`CrossingIntegration.NegControl.su3_kernel_nonneg_iff` shows the Wilson cross kernel is not
positive-semidefinite below zero.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign asserted and the one in
`N ≠ 0`; `N` is the rank, from `wilsonDensity`; `4` is the dimension. -/
theorem odd_pairing_integral_nonneg (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ} (hfm : Measurable f)
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V)
    {CF : ℝ} (hCF : 0 ≤ CF) (hfb : ∀ U, |f U| ≤ CF) :
    0 ≤ ∫ u, oddPairIntegrand τ p ω β f u
      ∂(MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) := by
  rw [integral_obox_mirror τ (2 * p - 1) hΛ (oddPairIntegrand τ p ω β f)
    (measurable_oddPairIntegrand τ p ω β hfm)
    (abs_oddPairIntegrand_le τ p ω β hN hCF hfb)]
  simp only [ojoin_def]
  have hy : ∀ (g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N)
      (x : ↥(oboxS τ (2 * p - 1) Λ) → MassGap.SUN.SU N),
      (∫ y, oddPairIntegrand τ p ω β f
          (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
        ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
          (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * ∫ y, (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
            * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
                (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                  (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
                (ocrossWord τ p y)))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))) := by
    intro g x
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun y => integrand_odd_eq τ p hΛ dflt ω β S hS hSΛ f hf g x y))
  have hx : ∀ g : ↥(oboxR τ (2 * p - 1) Λ) → MassGap.SUN.SU N,
      (∫ x, (∫ y, oddPairIntegrand τ p ω β f
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))))
        ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
          (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * ∫ x, (∫ y, (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
              * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
                  (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                    (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
                  (ocrossWord τ p y)))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
              (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))) := by
    intro g
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hy g x))
  have hstep : (∫ g, (∫ x, (∫ y, oddPairIntegrand τ p ω β f
            (ojoin τ (2 * p - 1) Λ g x (omirrorT τ (2 * p - 1) hΛ y))
          ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))))
        ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
          (probHaar (MassGap.SUN.SU N))))
      ∂(MassGap.ActionSplit.cvol ↥(oboxR τ (2 * p - 1) Λ)
        (probHaar (MassGap.SUN.SU N))))
      = Real.exp (-β * ((ioplqCross τ (2 * p - 1) Λ).card : ℝ))
        * ∫ g, (∫ x, (∫ y, (oddHalfA τ p ω β f x * oddHalfA τ p ω β f y
                * Real.exp ((β / (N : ℝ)) * MassGap.CharacterExpansion.hsRe
                    (ocrossWord τ p (MassGap.OddLagSplit.planeAct
                      (oplaneA τ p dflt) (oplaneB τ p dflt) g x))
                    (ocrossWord τ p y)))
              ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
                (probHaar (MassGap.SUN.SU N))))
            ∂(MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ)
              (probHaar (MassGap.SUN.SU N))))
          ∂(MassGap.ActionSplit.cvol ↥(oboxR τ (2 * p - 1) Λ)
            (probHaar (MassGap.SUN.SU N))) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun g => hx g))
  rw [hstep]
  refine mul_nonneg (Real.exp_nonneg _) ?_
  exact MassGap.CrossingIntegration.wilson_crossing_pairing_nonneg
    (MassGap.ActionSplit.cvol ↥(oboxR τ (2 * p - 1) Λ) (probHaar (MassGap.SUN.SU N)))
    (MassGap.ActionSplit.cvol ↥(oboxS τ (2 * p - 1) Λ) (probHaar (MassGap.SUN.SU N)))
    (MassGap.OddLagSplit.measurable_uncurry_planeAct
      (oplaneA τ p dflt) (oplaneB τ p dflt))
    (fun g => MassGap.OddLagSplit.planeAct_measurePreserving
      (oplaneA τ p dflt) (oplaneB τ p dflt) g)
    (fun g h u => MassGap.OddLagSplit.planeAct_mul
      (oplaneA τ p dflt) (oplaneB τ p dflt) g h u)
    (ocrossWord τ p)
    (measurable_coord_ocrossWord τ p)
    (fun c v => abs_coord_ocrossWord_le_one τ p c v)
    (fun g u v => hsRe_ocrossWord_planeAct τ p
      (oplaneA τ p dflt) (oplaneB τ p dflt) g u v)
    (measurable_oddHalfA τ p ω β hfm) (by positivity)
    (fun x => abs_oddHalfA_le τ p ω β hN hCF hfb x)
    (by positivity)

#print axioms odd_pairing_integral_nonneg

/-- `0 ≤ stateFree … ((latticeReflection τ (2 * p - 1)).θ f * f)` for a continuous `f` supported in
the
positive half-space — `InfiniteReflection.ReflPositiveOn`'s content at one finite volume, at the
mirror `p - 1/2` that cuts `τ`-links. `odd_pairing_integral_nonneg` is the numerator and
`partFree_pos` the denominator; the observable's bound comes from
`InfiniteLattice.bounded_of_continuous`, `IConf` being a product of compact groups.

Three hypotheses distinguish it from the even counterpart
`stateFree_refl_nonneg_of_halfSpace_support`, which is general in `φ` under `hφm`, `hφ0`, `hφ2` and
`hφc`, takes no condition on `N`, and asks nothing of the box beyond reflection-closure. This one:

* takes `dflt : ↥(oboxR τ (2p-1) Λ)`, so the box's shared block must be nonempty. At an odd constant
  that block is the `τ`-links based at `p - 1`, and a reflection-closed box built from transverse
  links alone satisfies `hΛ` with `oboxR = ∅`, where this statement cannot be formed;
* fixes `φ` to `WilsonAction.wilsonDensity`, the crossing kernel being the Wilson one;
* takes `hN : N ≠ 0`.

When `oboxR` is empty, `ioplqCross` is empty too and the residual weight is `1`, so
`ActionSplit.pairing_nonneg_of_local`'s `hσR` and `hWloc` hold vacuously there; when it is nonempty
both fail at an odd constant, by
`LatticeReflection.ireflConf_inverts_fixed_axis_link` and by `osLinkOf_mem_oboxS` beside
`otLinkOf_mem_oboxT`. Neither direction is formalised here; `eq_empty_of_stable_two_mirrors` is the
proved no-go in this file.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign asserted and the one in
`N ≠ 0`; `4` is the dimension. -/
theorem stateFree_odd_refl_nonneg (τ : Fin 4) (p : ℤ)
    {Λ : Finset MassGap.InfiniteLattice.ILink}
    (hΛ : ∀ l ∈ Λ, ireflLink τ (2 * p - 1) l ∈ Λ)
    (dflt : ↥(oboxR τ (2 * p - 1) Λ))
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (S : Finset MassGap.InfiniteLattice.ILink) (hS : ↑S ⊆ posHalf τ p) (hSΛ : S ⊆ Λ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hf : ∀ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
      (∀ lk ∈ S, U lk = V lk) → f U = f V) :
    0 ≤ stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω
        ((MassGap.LatticeReflection.latticeReflection τ (2 * p - 1)).θ f * f) := by
  obtain ⟨CF, hCF⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  have hCF0 : 0 ≤ CF := le_trans (abs_nonneg _) (hCF 1)
  rw [stateFree_apply]
  unfold specFree
  refine div_nonneg ?_ (partFree_pos MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) β Λ ω).le
  have hrw : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      ((MassGap.LatticeReflection.latticeReflection τ (2 * p - 1)).θ f * f)
          (MassGap.GibbsSpec.splice Λ u ω)
        * wtFree MassGap.WilsonAction.wilsonDensity β Λ ω u
      = oddPairIntegrand τ p ω β f u := fun _ => rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact odd_pairing_integral_nonneg τ p hΛ dflt ω hβ hN S hS hSΛ
    f.continuous.measurable hf hCF0 hCF

#print axioms stateFree_odd_refl_nonneg

/-- `Re tr` at the witness box's own half-link, as a `C(IConf (SU 3), ℝ)` — an observable supported
exactly on `ocrossSupp`, built with `HalfSpaceAlgebra.halfLinkObs`.

CHOSEN: `3` is `SU 3`'s matrix dimension. Nothing in this definition forces it, since `Re tr` reads
any `SU N`, but `ocrossObs_nonconstant` uses `CrossingIntegration.trace_gNeg`, which is stated at
`3`. `4` is the dimension. -/
noncomputable def ocrossObs (τ ν : Fin 4) (p : ℤ) :
    C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3), ℝ) :=
  MassGap.HalfSpaceAlgebra.halfLinkObs (osLinkOf τ (ocrossPlaq τ ν p))
    ⟨fun g => (Matrix.trace (g : Matrix (Fin 3) (Fin 3) ℂ)).re,
      Complex.continuous_re.comp continuous_subtype_val.matrix_trace⟩

#print axioms ocrossObs

/-- `ocrossObs` reads its own link and nothing else — the `hf` that `odd_pairing_integral_nonneg`
takes.

CHOSEN: `3` is inherited from `ocrossObs` and is not forced here. `4` is the dimension. -/
theorem ocrossObs_local (τ ν : Fin 4) (p : ℤ)
    (U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3))
    (h : ∀ lk ∈ ocrossSupp τ ν p, U lk = V lk) :
    ocrossObs τ ν p U = ocrossObs τ ν p V := by
  have hmem : osLinkOf τ (ocrossPlaq τ ν p) ∈ ocrossSupp τ ν p :=
    Finset.mem_singleton_self _
  show (Matrix.trace ((U (osLinkOf τ (ocrossPlaq τ ν p)) : MassGap.SUN.SU 3)
      : Matrix (Fin 3) (Fin 3) ℂ)).re
    = (Matrix.trace ((V (osLinkOf τ (ocrossPlaq τ ν p)) : MassGap.SUN.SU 3)
      : Matrix (Fin 3) (Fin 3) ℂ)).re
  rw [h _ hmem]

#print axioms ocrossObs_local

/-- `ocrossObs` is not constant at `SU 3`: it reads `3` at the identity configuration and `-1` at
the
constant `CrossingIntegration.gNeg` configuration.

`odd_pairing_integral_nonneg` assumes only `N ≠ 0`, and at `N = 1` the group `SU 1` is a singleton,
so `IConf` is a singleton, every observable is constant and the conclusion holds with `0 ≤ β` never
used. This exhibits a case where the integrand varies with the half-variable.

DERIVED: `3` is `SU 3`'s matrix dimension, and here it is forced — `trace_gNeg` is what separates
the two configurations and is stated at `3`. `4` is the dimension. The `1` and `-1` of the proof are
the trace of the identity and `trace_gNeg`'s computed value; neither is in the statement. -/
theorem ocrossObs_nonconstant (τ ν : Fin 4) (p : ℤ) :
    ∃ U V : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3),
      ocrossObs τ ν p U ≠ ocrossObs τ ν p V := by
  refine ⟨1, (fun _ => MassGap.CrossingIntegration.gNeg), ?_⟩
  have h1 : ocrossObs τ ν p 1 = 3 := by
    show (Matrix.trace (((1 : MassGap.SUN.SU 3) : Matrix (Fin 3) (Fin 3) ℂ))).re = 3
    simp
  have h2 : ocrossObs τ ν p (fun _ => MassGap.CrossingIntegration.gNeg) = -1 :=
    MassGap.CrossingIntegration.trace_gNeg
  rw [h1, h2]
  norm_num

#print axioms ocrossObs_nonconstant

/-- `odd_pairing_integral_nonneg` at the witness box and the witness observable, leaving only `0 ≤
β`
and `ν ≠ τ` on the caller. Each hypothesis is discharged here:

* `hΛ` — `ocrossBox_refl_closed`;
* `dflt` — `ocrossBox_oboxR_nonempty`, so the shared block is inhabited and the statement can be
  formed;
* `S`, `hS`, `hSΛ` — `ocrossSupp` with `ocrossSupp_subset_posHalf` and `ocrossSupp_subset_box`;
* `f`, `hfm`, `hf`, `hfb` — `ocrossObs`, continuous hence measurable, local by `ocrossObs_local`,
  bounded by `InfiniteLattice.bounded_of_continuous`.

`ocrossBox_cross_nonempty`, `ocrossBox_plus_nonempty`, `ocrossBox_oboxS_nonempty` and
`ocrossObs_nonconstant` say the conclusion is not vacuous at this data: straddling plaquettes exist,
positive plaquettes exist, the integration space is not a point, and the observable is not constant.

CHOSEN: `3` is inherited from `ocrossObs`; `odd_pairing_integral_nonneg` is general in `N` under
`N ≠ 0` and every other input here is `N`-free, so this instance is narrower than what it proves —
it is pinned at `3` so that `ocrossObs_nonconstant` applies to the same observable.
DERIVED: the first `0` is the sign of the coupling and the second the sign asserted; `4` is the
dimension. -/
theorem ocrossBox_odd_pairing_nonneg (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU 3)) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ ∫ u, oddPairIntegrand (N := 3) τ p ω β (ocrossObs τ ν p) u
      ∂(MassGap.ActionSplit.cvol ↥(ocrossBox τ ν p) (probHaar (MassGap.SUN.SU 3))) := by
  obtain ⟨d, hd⟩ := ocrossBox_oboxR_nonempty τ ν hν p
  obtain ⟨CF, hCF⟩ :=
    MassGap.InfiniteLattice.bounded_of_continuous (ocrossObs τ ν p).continuous
  exact odd_pairing_integral_nonneg (N := 3) τ p (ocrossBox_refl_closed τ ν p)
    ⟨d, hd⟩ ω hβ (by norm_num) (ocrossSupp τ ν p)
    (ocrossSupp_subset_posHalf τ ν hν p) (ocrossSupp_subset_box τ ν hν p)
    (ocrossObs τ ν p).continuous.measurable (ocrossObs_local τ ν p)
    (le_trans (abs_nonneg _) (hCF 1)) hCF

#print axioms ocrossBox_odd_pairing_nonneg

/-- The limit of the free-boundary states over a reflection-stable family of boxes is reflection
positive at the mirror `p - 1/2`, on the whole of `HalfSpaceAlgebra.halfSpaceAlg τ p`.

`InfiniteReflection.reflPositive_of_eventually_pointwise` does the transport: a member of
`halfSpaceAlg` carries its own finite support `S`, `hexh` puts `S` inside the box eventually, and
`stateFree_odd_refl_nonneg` gives the sign at each such box. The support is chosen per observable
rather than once for the algebra, `halfSpaceAlg` being a directed union local to no single box.

Against `reflPositive_of_tendsto_halfSpaceAlg`, the even statement, this adds `hR`, adds `0 ≤ β`,
adds `hN : N ≠ 0`, and fixes `φ` to `WilsonAction.wilsonDensity` — which excludes `φ = 0`, the free
theory — because the crossing kernel is the Wilson one. It drops `hφc`, which the odd route does not
use. `HalfSpaceReflPositive`, the even statement this file calls `B3`, is not instantiated by it.

`hR` asks the box to have a nonempty shared block, since `stateFree_odd_refl_nonneg` takes an
inhabitant of it. At an odd constant that block contains the `τ`-links based at `p - 1`
(`tauLink_mem_oboxR`; that it contains nothing else is not proved here, though
`odd_nonTau_not_fixed` is most of it), so a family built only from transverse links satisfies `hbox`
and fails `hR`.

`hR` is eventual rather than universal because a cube of radius `n` centred on the constant contains
no site at height `p - 1` until `n ≥ |p|`; at `p = 0` that holds at every `n`.
`symCube_oboxR_nonempty` discharges it.

At `N ≤ 1` the conclusion is empty: `SU 1` is a singleton, so `halfSpaceAlg` is the constants and
`ReflPositiveOn` says nothing. `halfSpaceAlg_has_nonconstant` is a witness at `SU 3`.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign of the coupling and the one
in `N ≠ 0`; `4` is the dimension. -/
theorem reflPositive_of_tendsto_halfSpaceAlg_odd
    {ι : Type*} {l : Filter ι} [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p - 1) lk ∈ box i)
    (hR : ∀ᶠ i in l, (oboxR τ (2 * p - 1) (box i)).Nonempty)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun i => stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box i) ω f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  refine MassGap.InfiniteReflection.reflPositive_of_eventually_pointwise htend _ _ ?_
  intro f hf
  obtain ⟨S, hS, hfloc⟩ := MassGap.HalfSpaceAlgebra.mem_halfSpaceAlg.mp hf
  refine ((hexh S).and hR).mono (fun i hi => ?_)
  obtain ⟨d, hd⟩ := hi.2
  exact stateFree_odd_refl_nonneg (Λ := box i) τ p (hbox i) ⟨d, hd⟩ ω hβ hN S hS hi.1 f hfloc

#print axioms reflPositive_of_tendsto_halfSpaceAlg_odd



/-- At the odd constant `2 * p - 1` no transverse link is fixed: a non-`τ` link reflects about `c`
itself, so fixing it needs `2 x_τ = c`, which an odd `c` cannot satisfy. The mirror of
`no_tau_link_fixed`, which says the same of `τ`-links at an even constant.

DERIVED: the `2` is the plane-to-constant conversion and the `1` the half-step, together making the
constant odd, which is the content; `4` is the dimension. -/
theorem odd_nonTau_not_fixed (τ : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (h : l.1 ≠ τ) : ireflLink τ (2 * p - 1) l ≠ l := by
  intro heq
  have hcoord : (ireflLink τ (2 * p - 1) l).2 τ = l.2 τ := by rw [heq]
  rw [image_half_is_c_sub_p τ (2 * p - 1) h] at hcoord
  omega

#print axioms odd_nonTau_not_fixed

/-- An axis link is fixed at the odd constant exactly when it straddles the mirror: a `τ`-link
reflects
about `c - 1 = 2p - 2`, so it is fixed exactly at base `p - 1` — the link spanning `[p-1, p]`, which
is the one the mirror at `p - 1/2` cuts.

`ireflConf` inverts on `τ`-links, so the twist does not act trivially on the shared block as it does
in the even case. That is why the odd pairing is an integral against a kernel rather than a square,
and why it carries `0 ≤ β`.

DERIVED: the `2` is the plane-to-constant conversion, the `1`s are the half-step and `ireflLink`'s
link length; `4` is the dimension. -/
theorem odd_tau_fixed_iff (τ : Fin 4) (p : ℤ) {l : MassGap.InfiniteLattice.ILink}
    (h : l.1 = τ) : ireflLink τ (2 * p - 1) l = l ↔ l.2 τ = p - 1 := by
  constructor
  · intro heq
    have hcoord : (ireflLink τ (2 * p - 1) l).2 τ = l.2 τ := by rw [heq]
    simp only [ireflLink, if_pos h, ireflSite_axis] at hcoord
    omega
  · intro hx
    refine Prod.ext rfl ?_
    show (if l.1 = τ then ireflSite τ (2 * p - 1 - 1) l.2 else ireflSite τ (2 * p - 1) l.2) = l.2
    rw [if_pos h]
    funext j
    by_cases hj : j = τ
    · subst hj
      simp only [ireflSite, Function.update_self]
      omega
    · simp [ireflSite, Function.update_of_ne hj]

#print axioms odd_tau_fixed_iff

/-! ### A box family that is reflection-stable and exhausting -/

/-- The coordinate cube of radius `n` centred at the reflection constant `c` in every coordinate.
`c` is
the constant, not the plane — the mirror it names sits at `c / 2`. Centring on `c` rather than on
the plane is what makes `symCube` stable without further argument.

DERIVED: the signature writes no numeral; `c` and `n` are the caller's constant and radius, and `4`
is the dimension carried by `ILink` inside the body. The pair `(direction, site)` a link is comes
from `×ˢ`. -/
noncomputable def coordCube (c : ℤ) (n : ℕ) : Finset MassGap.InfiniteLattice.ILink :=
  Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (c - n) (c + n))

/-- The symmetrised cube: `coordCube c n` together with its image under `ireflLink τ c`. Finite, and
stable by construction.

DERIVED: `c` is the caller's reflection constant; `n` is the caller's radius; `4` is the dimension.
-/
noncomputable def symCube (τ : Fin 4) (c : ℤ) (n : ℕ) : Finset MassGap.InfiniteLattice.ILink :=
  coordCube c n ∪ (coordCube c n).image (ireflLink τ c)

/-- `symCube τ c n = reflClosure τ c (coordCube c n)`, by `rfl`: `reflClosure` unions a set with its
reflected image, which is what `symCube` does to `coordCube`.

DERIVED: `c` is the caller's reflection constant; `n` is the radius; `4` is the dimension. -/
theorem symCube_eq_reflClosure (τ : Fin 4) (c : ℤ) (n : ℕ) :
    symCube τ c n = reflClosure τ c (coordCube c n) := rfl

#print axioms symCube_eq_reflClosure

/-- The symmetrised cube is closed under the reflection — the `hbox` the limit statements take. One
application of `reflClosure_closed` at the plain cube: a member reflects into the image part, and a
member of the image part reflects back by involutivity. Holds at any constant.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. -/
theorem symCube_refl_stable (τ : Fin 4) (c : ℤ) (n : ℕ) :
    ∀ lk ∈ symCube τ c n, ireflLink τ c lk ∈ symCube τ c n :=
  reflClosure_closed τ c (coordCube c n)

#print axioms symCube_refl_stable

/-- The plane link: direction `ν`, every coordinate `p`.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
def planeLink (ν : Fin 4) (p : ℤ) : MassGap.InfiniteLattice.ILink := (ν, fun _ => p)

/-- `planeLink ν p` is in `symCube τ (2 * p) n` once the radius reaches `|p|`, which is what `hlo`
and
`hhi` ask.

DERIVED: the `2` is the even reflection constant `2 * p`; `4` is the dimension. -/
theorem planeLink_mem_symCube (τ ν : Fin 4) (p : ℤ) {n : ℕ}
    (hlo : -(n : ℤ) ≤ p) (hhi : p ≤ (n : ℤ)) :
    planeLink ν p ∈ symCube τ (2 * p) n := by
  refine Finset.mem_union_left _ ?_
  simp only [coordCube, planeLink, Finset.mem_product, Finset.mem_univ, true_and,
    Fintype.mem_piFinset, Finset.mem_Icc]
  intro _
  omega

#print axioms planeLink_mem_symCube

/-- And it is in the shared block, by `transverse_link_mem_boxR`, so the cube's plane is not empty.

DERIVED: the `2` is the even reflection constant `2 * p`; `4` is the dimension. -/
theorem planeLink_mem_boxR (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) {n : ℕ}
    (hlo : -(n : ℤ) ≤ p) (hhi : p ≤ (n : ℤ)) :
    (⟨planeLink ν p, planeLink_mem_symCube τ ν p hlo hhi⟩ : ↥(symCube τ (2 * p) n))
      ∈ boxR τ p (symCube τ (2 * p) n) :=
  transverse_link_mem_boxR τ ν hν p (fun _ => p) rfl _ _

#print axioms planeLink_mem_boxR

/-- A plane function with a zero: it reads one shared-block link through `HaarVariance.reTr` and is
squashed by `1 - exp (-(·)^2)`, so it lies in `[0, 1)` and needs no bound on the trace.

DERIVED: the leading `1` is `exp`'s value at `0`, so the probe vanishes where `Re tr` reads `m + 2`;
the `2` in `m + 2` is the least matrix dimension at which two group elements exist; the exponent `2`
makes the argument of `exp` nonpositive whatever the sign of the difference; `4` is the dimension.
-/
noncomputable def planeProbe (m : ℕ) {τ : Fin 4} {p : ℤ}
    {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥(boxR τ p Λ))
    (w : ↥(boxR τ p Λ) → MassGap.SUN.SU (m + 2)) : ℝ :=
  1 - Real.exp (-(MassGap.HaarVariance.reTr (w ℓ) - ((m : ℝ) + 2)) ^ 2)

/-- `planeProbe m ℓ` is continuous, `HaarVariance.continuous_reTr` composed with the squashing.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem continuous_planeProbe (m : ℕ) {τ : Fin 4} {p : ℤ}
    {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥(boxR τ p Λ)) :
    Continuous (planeProbe m ℓ) := by
  unfold planeProbe
  exact continuous_const.sub (Real.continuous_exp.comp
    (((MassGap.HaarVariance.continuous_reTr.comp (continuous_apply ℓ)).sub
      continuous_const).pow 2).neg)

#print axioms continuous_planeProbe

/-- And bounded by `1`, with no bound on the trace: the subtracted exponential lies in `(0, 1]`.

DERIVED: the `1` is the bound, which is `exp`'s value at `0`; the `2` in `m + 2` is the least matrix
dimension carrying two group elements; `4` is the dimension. -/
theorem planeProbe_abs_le_one (m : ℕ) {τ : Fin 4} {p : ℤ}
    {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥(boxR τ p Λ))
    (w : ↥(boxR τ p Λ) → MassGap.SUN.SU (m + 2)) : |planeProbe m ℓ w| ≤ 1 := by
  unfold planeProbe
  have h1 : 0 < Real.exp (-(MassGap.HaarVariance.reTr (w ℓ) - ((m : ℝ) + 2)) ^ 2) :=
    Real.exp_pos _
  have h2 : Real.exp (-(MassGap.HaarVariance.reTr (w ℓ) - ((m : ℝ) + 2)) ^ 2) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have := sq_nonneg (MassGap.HaarVariance.reTr (w ℓ) - ((m : ℝ) + 2))
    linarith
  rw [abs_le]
  constructor <;> linarith

#print axioms planeProbe_abs_le_one

/-- It vanishes where `Re tr` reads `m + 2` — at the identity, by `HaarVariance.reTr_one`.

DERIVED: the `0` is the value; the `1` is the identity `w` takes at `ℓ`; the `2` in `m + 2` is the
least matrix dimension carrying two group elements; `4` is the dimension. -/
theorem planeProbe_eq_zero (m : ℕ) {τ : Fin 4} {p : ℤ}
    {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥(boxR τ p Λ))
    (w : ↥(boxR τ p Λ) → MassGap.SUN.SU (m + 2))
    (hw : w ℓ = 1) : planeProbe m ℓ w = 0 := by
  unfold planeProbe
  rw [hw, MassGap.HaarVariance.reTr_one]
  push_cast
  simp

#print axioms planeProbe_eq_zero

/-- And is positive where it does not — at `HaarVariance.flipEl`, which reads `m - 2`.

DERIVED: the `0` is the bound; the `2` in `m + 2` is `reTr`'s value at the identity; `4` is the
dimension. -/
theorem planeProbe_pos (m : ℕ) {τ : Fin 4} {p : ℤ}
    {Λ : Finset MassGap.InfiniteLattice.ILink} (ℓ : ↥(boxR τ p Λ))
    (w : ↥(boxR τ p Λ) → MassGap.SUN.SU (m + 2))
    (hw : MassGap.HaarVariance.reTr (w ℓ) ≠ (m : ℝ) + 2) : 0 < planeProbe m ℓ w := by
  unfold planeProbe
  have ht : MassGap.HaarVariance.reTr (w ℓ) - ((m : ℝ) + 2) ≠ 0 := sub_ne_zero.mpr hw
  have ht2 : 0 < (MassGap.HaarVariance.reTr (w ℓ) - ((m : ℝ) + 2)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ht))
  have he : Real.exp (-(MassGap.HaarVariance.reTr (w ℓ) - ((m : ℝ) + 2)) ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  linarith

#print axioms planeProbe_pos

/-- An observable at which the box's Wilson reflection form is strictly positive, at every `k`. Each
hypothesis of `irefl_box_pairing_pos_of_plane_factor_dressed` is discharged at concrete data: the
carrier `symCube τ (2 * p) n` is reflection-closed (`symCube_refl_stable`), the density is
`WilsonAction.wilsonDensity` bounded in `[0, 2]`, the weight is the box's own `iplaneWeight`, and
the
observable is `planeProbe` times the dressing. The two configurations are the constants `1` and
`HaarVariance.flipEl m`, separated by `Re tr`.

Scope: the matrix dimension is written `m + 2` because at `SU 0` and `SU 1` the group is a singleton
and no separating pair exists. The conclusion is a strict sign at one box, not a quantitative bound
and not a statement about a limit state.

DERIVED: the `2` in `2 * p` is the even reflection constant; the `2` in `m + 2` is the least matrix
dimension carrying two group elements; the `0` is the positivity concluded; `4` is the dimension.
The identity configuration and `flipEl m` are bound in the proof and appear in no literal here. -/
theorem irefl_box_pairing_pos_witness (m : ℕ) (τ ν : Fin 4) (hν : ν ≠ τ) (p : ℤ) {n : ℕ}
    (hlo : -(n : ℤ) ≤ p) (hhi : p ≤ (n : ℤ)) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU (m + 2))) (k : ℝ) :
    ∃ O : (↥(symCube τ (2 * p) n) → MassGap.SUN.SU (m + 2)) → ℝ,
      0 < (∫ U, iplaneWeight MassGap.WilsonAction.wilsonDensity β τ p
              (symCube τ (2 * p) n) ω U
          * (O U - k)
          * (O (MassGap.ActionSplit.twist (ireflBoxPerm (symCube_refl_stable τ (2 * p) n))
                (fun l : ↥(symCube τ (2 * p) n) =>
                  ilinkDagger (G := MassGap.SUN.SU (m + 2)) τ l.1) U) - k)
          ∂(MassGap.ActionSplit.cvol ↥(symCube τ (2 * p) n)
              (probHaar (MassGap.SUN.SU (m + 2))))) := by
  classical
  have hN : (m + 2 : ℕ) ≠ 0 := by omega
  have hφ0 : ∀ g : MassGap.SUN.SU (m + 2), 0 ≤ MassGap.WilsonAction.wilsonDensity g :=
    fun g => MassGap.WilsonAction.wilsonDensity_nonneg hN g
  have hφ2 : ∀ g : MassGap.SUN.SU (m + 2), MassGap.WilsonAction.wilsonDensity g ≤ 2 :=
    fun g => MassGap.WilsonAction.wilsonDensity_le_two hN g
  have hφb : ∀ g : MassGap.SUN.SU (m + 2), |MassGap.WilsonAction.wilsonDensity g| ≤ 2 := by
    intro g
    rw [abs_of_nonneg (hφ0 g)]
    exact hφ2 g
  refine ⟨fun U => planeProbe m
      ⟨⟨planeLink ν p, planeLink_mem_symCube τ ν p hlo hhi⟩,
        planeLink_mem_boxR τ ν hν p hlo hhi⟩
      (fun i => U (i : ↥(symCube τ (2 * p) n)))
      * ihalfBoltz MassGap.WilsonAction.wilsonDensity β τ p (symCube τ (2 * p) n) ω U, ?_⟩
  refine irefl_box_pairing_pos_of_plane_factor_dressed
    (symCube_refl_stable τ (2 * p) n)
    MassGap.WilsonAction.wilsonDensity MassGap.WilsonAction.measurable_wilsonDensity
    MassGap.WilsonAction.continuous_wilsonDensity hφb β ω
    (planeProbe m ⟨⟨planeLink ν p, planeLink_mem_symCube τ ν p hlo hhi⟩,
      planeLink_mem_boxR τ ν hν p hlo hhi⟩)
    (continuous_planeProbe m _)
    (hfb := planeProbe_abs_le_one m _)
    (iplaneWeight MassGap.WilsonAction.wilsonDensity β τ p (symCube τ (2 * p) n) ω)
    (measurable_iplaneWeight MassGap.WilsonAction.measurable_wilsonDensity β τ p _ ω)
    (iplaneWeight_pos MassGap.WilsonAction.wilsonDensity β τ p _ ω)
    (fun U V hR => iplaneWeight_local MassGap.WilsonAction.wilsonDensity β τ p _ ω U V hR)
    _ (iplaneWeight_abs_le hφ0 hφ2 β τ p _ ω) k
    (a := fun _ => 1) (b := fun _ => MassGap.HaarVariance.flipEl m) ?_ ?_
  · exact planeProbe_eq_zero m _ _ rfl
  · refine planeProbe_pos m _ _ ?_
    rw [MassGap.HaarVariance.reTr_flipEl]
    intro h
    linarith

#print axioms irefl_box_pairing_pos_witness

/-- The cube family exhausts — the `hexh` the limit statements take. A `Finset` of links has
finitely
many coordinates, so they are bounded, so it sits inside every large enough cube.

DERIVED: `n` is the radius; `4` is the dimension. -/
theorem symCube_exhausts (τ : Fin 4) (c : ℤ) (S : Finset MassGap.InfiniteLattice.ILink) :
    ∀ᶠ n : ℕ in Filter.atTop, S ⊆ symCube τ c n := by
  classical
  set M : ℕ := S.sup (fun lk => Finset.univ.sup (fun j : Fin 4 => (lk.2 j).natAbs)) with hM
  refine Filter.eventually_atTop.2 ⟨M + c.natAbs, fun n hn lk hlk => ?_⟩
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_product.2 ⟨Finset.mem_univ _, Fintype.mem_piFinset.2 (fun j => ?_)⟩
  have hin : (lk.2 j).natAbs
      ≤ Finset.univ.sup (fun k : Fin 4 => (lk.2 k).natAbs) :=
    Finset.le_sup (f := fun k : Fin 4 => (lk.2 k).natAbs) (Finset.mem_univ j)
  have houter : Finset.univ.sup (fun k : Fin 4 => (lk.2 k).natAbs) ≤ M := by
    rw [hM]
    exact Finset.le_sup
      (f := fun m : MassGap.InfiniteLattice.ILink =>
        Finset.univ.sup (fun k : Fin 4 => (m.2 k).natAbs)) hlk
  have h1 : (lk.2 j).natAbs ≤ M := le_trans hin houter
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

#print axioms symCube_exhausts

/-- The cube family meets `hR`: eventually the cube reaches height `p - 1`, and then its `τ`-link
there
is in the shared block by `tauLink_mem_oboxR`. `ocrossSite p` is the site all of whose coordinates
are `p - 1`; only its `τ` one is used.

Eventual rather than universal: `coordCube` admits sites with every coordinate in `Icc (c-n) (c+n)`
at `c = 2p - 1`, so height `p - 1` is in range exactly when `n ≥ |p|`. At `p = 0` that holds at
every `n`, including `n = 0`.

DERIVED: the `2` and the `1` make the constant odd; `4` is the dimension. -/
theorem symCube_oboxR_nonempty (τ : Fin 4) (p : ℤ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (oboxR τ (2 * p - 1) (symCube τ (2 * p - 1) n)).Nonempty := by
  refine (symCube_exhausts τ (2 * p - 1)
    {((τ, ocrossSite p) : MassGap.InfiniteLattice.ILink)}).mono (fun n hn => ?_)
  have hmem : ((τ, ocrossSite p) : MassGap.InfiniteLattice.ILink) ∈ symCube τ (2 * p - 1) n :=
    hn (Finset.mem_singleton_self _)
  exact ⟨⟨_, hmem⟩, tauLink_mem_oboxR τ p rfl hmem⟩

#print axioms symCube_oboxR_nonempty

/-- `reflPositive_of_tendsto_halfSpaceAlg_odd` at the cube family `symCube τ (2 * p - 1)`, along any
filter refining `atTop`: `symCube_refl_stable` is `hbox`, `symCube_oboxR_nonempty` is `hR` and
`symCube_exhausts` is `hexh`, both transported by `Filter.Eventually.filter_mono`.

DERIVED: the `2` and the `1` make the constant odd; the two `0`s are the sign of the coupling and
the one in `N ≠ 0`; `4` is the dimension. -/
theorem wilson_reflPositive_odd_of_tendsto (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (l : Filter ℕ) [l.NeBot] (hl : l ≤ Filter.atTop)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
        l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  reflPositive_of_tendsto_halfSpaceAlg_odd τ p (symCube τ (2 * p - 1))
    (fun n => symCube_refl_stable τ (2 * p - 1) n)
    (Filter.Eventually.filter_mono hl (symCube_oboxR_nonempty τ p))
    (fun S => Filter.Eventually.filter_mono hl (symCube_exhausts τ (2 * p - 1) S))
    hβ hN ω ν htend

#print axioms wilson_reflPositive_odd_of_tendsto

/-- The same at `atTop` itself: reflection positivity at the odd constant on `halfSpaceAlg τ p`,
given
convergence of the odd cube family's free-boundary states along `atTop`. The remaining hypotheses
are that convergence and the sign of the coupling.

`DLRLimit.exists_limit_state` gives convergence along a refining ultrafilter rather than along
`atTop`, so `wilson_reflPositive_limit_exists_odd` is the form that takes no convergence hypothesis;
this one is for a caller who has an `atTop` limit. At `N ≤ 1` the conclusion is empty, as for the
abstract form.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign of the coupling and the one
in `N ≠ 0`; `4` is the dimension. -/
theorem reflPositive_symCube_odd (τ : Fin 4) (p : ℤ)
    {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n : ℕ => stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
        Filter.atTop (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  wilson_reflPositive_odd_of_tendsto τ p hN hβ ω ν Filter.atTop le_rfl htend

#print axioms reflPositive_symCube_odd

/-- A limit state with odd reflection positivity exists, with no convergence hypothesis.
`DLRLimit.exists_limit_state` gives a refining ultrafilter along which the free-boundary states
converge, and `reflPositive_of_tendsto_halfSpaceAlg_odd` is filter-generic, so `hR` and `hexh`
transport by `Filter.Eventually.filter_mono`. The `ℤ⁴` odd counterpart of
`wilson_reflPositive_limit_exists`.

The convergence is along an ultrafilter, not along `atTop`. At `N ≤ 1` the conclusion is empty:
`SU 1` is a singleton, so `halfSpaceAlg` is the constants; `halfSpaceAlg_has_nonconstant` is a
witness at `SU 3`.

DERIVED: the `2` and the `1` make the constant odd; the `0` is the sign of the coupling and the one
in `N ≠ 0`; `4` is the dimension. -/
theorem wilson_reflPositive_limit_exists_odd (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β) (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ℕ) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
          (u : Filter ℕ) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state Filter.atTop
      (fun n : ℕ => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
        MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω)
  haveI : (u : Filter ℕ).NeBot := u.neBot'
  refine ⟨u, ν, htend, ?_⟩
  exact reflPositive_of_tendsto_halfSpaceAlg_odd τ p (symCube τ (2 * p - 1))
    (fun n => symCube_refl_stable τ (2 * p - 1) n)
    (Filter.Eventually.filter_mono hle (symCube_oboxR_nonempty τ p))
    (fun S => Filter.Eventually.filter_mono hle (symCube_exhausts τ (2 * p - 1) S))
    hβ hN ω ν htend

#print axioms wilson_reflPositive_limit_exists_odd

/-- `GNSHilbert.PositiveTransfer` for the transfer data assembled from the state facts.
`WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive` is an equivalence — that data is a
positive transfer exactly when the state is reflection positive at the odd constant on the same
algebra — and `reflPositive_symCube_odd` supplies that side.

`hpos` and `htend` are about different families: `hpos` is reflection positivity at `2 * p`, which
the even chain gets from `symCube τ (2 * p)`, while `htend` here is convergence of
`symCube τ (2 * p - 1)`. `eq_empty_of_stable_two_mirrors` shows no nonempty box is stable under both
mirrors, so no single family discharges both, and sharing `ν` between them is an assumption this
statement leaves implicit. `wilson_transferData_of_common_limit` makes that assumption explicit,
`wilson_transferData_of_thermodynamic_limit` discharges it by interleaving the two shapes into
`mixCube`, `wilson_positiveTransfer_of_mixCube_limit` is this theorem in that form, and
`wilson_positiveTransfer_of_common_subsequential_limit` asks only that the two families share a
state along filters that need not agree.

At `N ≤ 1` the conclusion is empty: `hN : N ≠ 0` leaves `N = 1`, where `SU 1` is a singleton, so
`IConf` is, `halfSpaceAlg` is the constants and `PositiveTransfer` holds of a one-dimensional space.
`halfSpaceAlg_has_nonconstant` is a witness at `SU 3`.

DERIVED: the `2` and the `1` make the odd constant; the `2` alone is the plane-to-constant
conversion `c = 2 * p`; the `0` is the sign of the coupling and the one in `N ≠ 0`; `4` is the
dimension. -/
theorem wilson_positiveTransfer_of_odd_limit (τ : Fin 4) (p : ℤ)
    {β : ℝ} (hβ : 0 ≤ β) (hN : N ≠ 0)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n : ℕ => stateFree MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) ω f)
        Filter.atTop (nhds (ν f))) :
    MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu) :=
  (MassGap.WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive τ p ν hinv hpos hnu).mpr
    (reflPositive_symCube_odd τ p hβ hN ω ν htend)

#print axioms wilson_positiveTransfer_of_odd_limit

/-- Reflection positivity at the even constant `2 * p` on `halfSpaceAlg τ p`, given convergence of
the
free-boundary states along `l`. The observable's own support picks the fixed region, `hexh` puts
that support inside the box eventually, and
`InfiniteReflection.reflPositive_of_eventually_pointwise` accepts an eventual hypothesis in place of
a uniform one. The sign at each box is `stateFree_refl_nonneg_of_halfSpace_support`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the Wilson density's ceiling in
`hφ2`; the `0` is the sign in `hφ0`; `4` is the dimension. -/
theorem reflPositive_of_tendsto_halfSpaceAlg
    {ι : Type*} {l : Filter ι} [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  refine MassGap.InfiniteReflection.reflPositive_of_eventually_pointwise htend _ _ ?_
  intro f hf
  obtain ⟨S, hS, hfloc⟩ := MassGap.HalfSpaceAlgebra.mem_halfSpaceAlg.mp hf
  refine (hexh S).mono (fun i hi => ?_)
  exact stateFree_refl_nonneg_of_halfSpace_support (Λ := box i) (hbox i)
    hφm hφ0 hφ2 hφc β ω S hS hi f hfloc

#print axioms reflPositive_of_tendsto_halfSpaceAlg

/-- Reflection positivity at the even constant from convergence of the even cube family along any
filter
refining `atTop`; a subsequential limit suffices, because `hexh` transports by
`Filter.Eventually.filter_mono`. The density is `WilsonAction.wilsonDensity`, whose class-function
property is `wilsonDensity_conj`.

DERIVED: the `2` is the plane-to-constant conversion and the Wilson density's ceiling; the `0` is
the one in `N ≠ 0`; `4` is the dimension. -/
theorem wilson_reflPositive_even_of_tendsto (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (l : Filter ℕ) [l.NeBot] (hl : l ≤ Filter.atTop)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) ω f)
        l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  reflPositive_of_tendsto_halfSpaceAlg τ p (symCube τ (2 * p))
    (fun n => symCube_refl_stable τ (2 * p) n)
    (fun S => Filter.Eventually.filter_mono hl (symCube_exhausts τ (2 * p) S))
    MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN)
    (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β ω ν htend

#print axioms wilson_reflPositive_even_of_tendsto

/-- `ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg τ p) ν` for a limit state produced
here,
on the directed union rather than on one fixed finite region. The submodule is supplied rather than
assumed, so `⊥` does not satisfy it: it contains the constants
(`HalfSpaceAlgebra.one_mem_halfSpaceAlg`) and every `halfLinkObs` of a link in the positive half
(`HalfSpaceAlgebra.halfLinkObs_mem`).

`halfLinkObs_mem` alone does not make it more than the constants, being quantified over an arbitrary
`f : C(G, ℝ)`; a separating `f` is needed, which is what
`HalfSpaceAlgebra.shift_moves_halfLinkObs` takes as a hypothesis and what
`halfSpaceAlg_has_nonconstant` supplies at `SU 3`, by `Re tr` against
`CrossingIntegration.trace_gNeg`. At `N ≤ 1` the algebra is the constants, since `SU 0` and `SU 1`
are singletons; no statement in this file carries `2 ≤ N`.

`hexh` is a property of the box family alone — every finite set of links eventually lies inside the
box — satisfiable by any increasing exhaustion of `ℤ⁴`. It replaces the fixed region `R₀` of
`reflPositive_limit_on_half_space`.

The limit is along an ultrafilter refining `l`, and translation invariance is not asserted;
`ReflectionShift.nu_T_of_reflection_invariant` relates it to reflection invariance, one translation
being the composite of the reflections at `2p` and `2p - 1`.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the density's ceiling in
`hφ2`; the `0` is the sign in `hφ0`; `4` is the dimension. -/
theorem reflPositive_limit_on_halfSpaceAlg
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state l (fun i => stateFree hφm hφ0 hφ2 β (box i) ω)
  haveI : (u : Filter ι).NeBot := u.neBot'
  exact ⟨u, ν, hle, htend,
    reflPositive_of_tendsto_halfSpaceAlg τ p box hbox
      (fun S => ((hexh S).filter_mono hle)) hφm hφ0 hφ2 hφc β ω ν htend⟩

#print axioms reflPositive_limit_on_halfSpaceAlg

/-- The free weight is invariant under the abstract twist, for a class function `φ`: the action over
`iplqAll` sees only links inside the box, where `splice_twist_eq_ireflConf` identifies the twist
with
`ireflConf`, and `action_iplqAll_ireflConf` says the action does not see that.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. -/
theorem wtFree_twist {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    wtFree φ β Λ ω
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u)
      = wtFree φ β Λ ω u := by
  unfold wtFree
  congr 2
  have h1 : MassGap.GibbsSpec.actionOn φ (iplqAll Λ)
      (MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω)
      = MassGap.GibbsSpec.actionOn φ (iplqAll Λ)
          (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)) :=
    MassGap.GibbsSpec.actionOn_congr φ _ _ _
      (fun q hq l hl => splice_twist_eq_ireflConf hΛ ω u
        (MassGap.GibbsSpec.mem_plaqsIn.mp (mem_iplqAll.mp hq).1 l hl))
  rw [h1, action_iplqAll_ireflConf φ hφc τ c hΛ]

#print axioms wtFree_twist

/-- The free-boundary state does not see the reflection: `specFree` of `f ∘ ireflConf τ c` equals
`specFree` of `f`. Change of variables along the measure-preserving twist
(`ActionSplit.twist_measurePreserving` with `ilinkDagger_measurePreserving`), with the weight
invariant by `wtFree_twist`.

This is `IsReflectionInvariant` at one box, which
`InfiniteReflection.isReflectionInvariant_of_tendsto` transports to the limit. Unlike positivity it
is stated for all observables. `hagree` carries the box-locality of `f`, for the same reason as
elsewhere: the twist and `ireflConf` agree only on `Λ`.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. -/
theorem specFree_reflection_invariant {c : ℤ}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    {f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ}
    (hfm : Measurable (fun u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ =>
      f (MassGap.GibbsSpec.splice Λ u ω)))
    (hagree : ∀ u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ,
      f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ
            (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
              (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω)) :
    specFree (φ := φ) β Λ ω
        (fun u => f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)))
      = specFree (φ := φ) β Λ ω (fun u => f (MassGap.GibbsSpec.splice Λ u ω)) := by
  unfold specFree
  congr 1
  set θ := MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
    (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) with hθ
  have hmp : MeasureTheory.MeasurePreserving θ
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N)))
      (MassGap.ActionSplit.cvol ↥Λ (probHaar (MassGap.SUN.SU N))) :=
    MassGap.ActionSplit.twist_measurePreserving _ _ _
      (fun l => ilinkDagger_measurePreserving τ l.1)
  have hw : ∀ v, wtFree φ β Λ ω (θ v) = wtFree φ β Λ ω v :=
    fun v => wtFree_twist hΛ hφc β ω v
  have hrw : (fun u => f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω))
      * wtFree φ β Λ ω u)
      = fun u => (fun v => f (MassGap.GibbsSpec.splice Λ v ω) * wtFree φ β Λ ω v) (θ u) := by
    funext u
    have h1 : f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω))
        = f (MassGap.GibbsSpec.splice Λ (θ u) ω) := hagree u
    show f (ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω)) * wtFree φ β Λ ω u
      = f (MassGap.GibbsSpec.splice Λ (θ u) ω) * wtFree φ β Λ ω (θ u)
    rw [h1, hw u]
  rw [hrw]
  exact MassGap.GibbsSpec.integral_comp_of_mp hmp (hfm.mul (measurable_wtFree hφm β Λ ω))

#print axioms specFree_reflection_invariant

/-- A reflection-stable box has a reflection-stable complement, by involutivity.

DERIVED: the signature writes no numeral; `c` is the caller's reflection constant. -/
theorem not_mem_of_not_mem_box {c : ℤ} (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {l : ILink} (hl : l ∉ Λ) : ireflLink τ c l ∉ Λ := by
  intro hmem
  exact hl (by simpa [ireflLink_involutive τ c l] using hΛ _ hmem)

/-- With a reflection-symmetric boundary condition `hω : ireflConf τ c ω = ω`, the spliced twist and
`ireflConf` agree at every link, not only inside the box — which is what `IsReflectionInvariant`
needs, since it quantifies over all observables.

Inside the box this is `splice_twist_eq_ireflConf`. Outside it, the complement is stable by
`not_mem_of_not_mem_box`, so the splice reads `ω` on both sides and `hω` closes it.

`hω` is satisfiable: the identity configuration is reflection-symmetric, because the dagger sends
`1` to `1`.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. -/
theorem splice_twist_eq_ireflConf_everywhere {c : ℤ}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : ireflConf τ c ω = ω)
    (u : MassGap.GibbsSpec.VConf (MassGap.SUN.SU N) Λ) :
    MassGap.GibbsSpec.splice Λ
        (MassGap.ActionSplit.twist (ireflBoxPerm hΛ)
          (fun l : ↥Λ => ilinkDagger (G := MassGap.SUN.SU N) τ l.1) u) ω
      = ireflConf τ c (MassGap.GibbsSpec.splice Λ u ω) := by
  funext l
  by_cases hl : l ∈ Λ
  · exact splice_twist_eq_ireflConf hΛ ω u hl
  · have himg : ireflLink τ c l ∉ Λ := not_mem_of_not_mem_box hΛ hl
    rw [MassGap.GibbsSpec.splice_not_mem hl]
    show ω l = _
    simp only [ireflConf, MassGap.GibbsSpec.splice_not_mem himg]
    conv_lhs => rw [← hω]
    simp only [ireflConf]

#print axioms splice_twist_eq_ireflConf_everywhere

/-- The free-boundary state at a box is invariant under the reflection, on all observables —
`InfiniteReflection.IsReflectionInvariant`, which
`InfiniteReflection.isReflectionInvariant_of_tendsto` transports to a limit. It is stated for every
observable, which is why the boundary condition has to satisfy `hω : ireflConf τ c ω = ω`;
`splice_twist_eq_ireflConf_everywhere` is where that is used.

DERIVED: `c` is the caller's reflection constant and is not pinned to an even `2 * p` here; `4` is
the dimension. The `0` is the sign in `hφ0` and the `2` the ceiling in `hφ2`. -/
theorem stateFree_reflection_invariant {c : ℤ}
    (hΛ : ∀ l ∈ Λ, ireflLink τ c l ∈ Λ)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : ireflConf τ c ω = ω) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ c)
      (stateFree hφm hφ0 hφ2 β Λ ω) := by
  intro f
  exact specFree_reflection_invariant hΛ hφm hφc β ω (boxObs_measurable ω f)
    (fun u => congrArg f (splice_twist_eq_ireflConf_everywhere hΛ hω u).symm)

#print axioms stateFree_reflection_invariant

/-- **Reflection invariance holds at every symmetric cube, with no hypothesis but the boundary
condition's own symmetry.**

`stateFree_reflection_invariant` carries three hypotheses and all three have suppliers here:
`symCube_refl_stable` makes the box closed under the reflection, `WilsonAction.wilsonDensity_conj`
makes the Wilson density a class function — with no condition on `N` — and `hω` is the caller's
choice of a reflection-symmetric boundary configuration.

So the `hinv` input that `WilsonTransferReduction` and `GaugeInvariantAlgebra` read off the state is
not an open assumption at finite volume: it is discharged at each cube, and
`InfiniteReflection.isReflectionInvariant_of_tendsto` carries it to a limit.

DERIVED: `4` is the spacetime dimension; `0` and `2` are `wilsonDensity`'s range, supplied by
`wilsonDensity_nonneg` and `wilsonDensity_le_two`. -/
theorem stateFree_symCube_reflection_invariant (hN : N ≠ 0) (τ : Fin 4) (c : ℤ) (n : ℕ) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : MassGap.LatticeReflection.ireflConf τ c ω = ω) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ c)
      (stateFree (Λ := symCube τ c n) MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β ω) :=
  stateFree_reflection_invariant (symCube_refl_stable τ c n)
    MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN)
    (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β hω

#print axioms stateFree_symCube_reflection_invariant

/-- `IsReflectionInvariant` and `ReflPositiveOn` for the same limit state, along the same
ultrafilter.
Invariance comes from `stateFree_reflection_invariant` at each box through
`InfiniteReflection.isReflectionInvariant_of_tendsto`; positivity is
`reflPositive_limit_exists` on `localSubmodule R₀`.

These are two of the three facts `WilsonTransferReduction` reads off the infinite-volume state:

    hinv : IsReflectionInvariant (latticeReflection τ (2*p)) ν      ← here
    hpos : ReflPositiveOn (latticeReflection τ (2*p)) A ν           ← here
    hnu  : ∀ f, ν (ishiftObsL τ f) = ν f                            ← not here

The third is translation invariance and is not asserted; the finite-volume free state does not have
it, the box breaking it.

The caller supplies a finite region at or above the plane, reflection-stable boxes containing it, a
reflection-symmetric boundary condition (the identity configuration is one, by `ireflConf_one`), and
the density's four properties.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the ceiling in `hφ2`; `4` is
the dimension. The `0` is the sign in `hφ0`. -/
theorem reflection_facts_of_limit
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (R₀ : Finset MassGap.InfiniteLattice.ILink)
    (hR₀ : ∀ lk ∈ R₀, (ireflLink τ (2 * p) lk).2 τ ≤ lk.2 τ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hsub : ∀ i, R₀ ⊆ box i)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : MassGap.LatticeReflection.ireflConf τ (2 * p) ω = ω) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.IsReflectionInvariant
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) (localSubmodule R₀) ν := by
  obtain ⟨u, ν, hle, htend, hrp⟩ :=
    reflPositive_limit_exists l τ p box hbox hφm hφ0 hφ2 hφc β ω (localSubmodule R₀)
      (fun i f hf U V h => hf U V (fun lk hlk => h lk (hsub i hlk)))
      (fun i f hf U V hS hR => by
        refine hf _ _ (fun lk hlk => ?_)
        have hlΛ : lk ∈ box i := hsub i hlk
        rw [MassGap.GibbsSpec.splice_mem hlΛ, MassGap.GibbsSpec.splice_mem hlΛ]
        rcases lt_or_eq_of_le (hR₀ lk hlk) with hlt | heq
        · exact hS _ (by simp only [boxS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hlt)
        · exact hR _ (by simp only [boxR, Finset.mem_filter, Finset.mem_univ, true_and]; exact heq))
  haveI : (u : Filter ι).NeBot := u.neBot'
  refine ⟨u, ν, hle, htend, ?_, hrp⟩
  exact MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun i =>
      stateFree_reflection_invariant (hbox i) hφm hφ0 hφ2 hφc β hω))

#print axioms reflection_facts_of_limit

/-- `reflPositive_limit_on_halfSpaceAlg` run once with no abstract parameters: `φ` is
`WilsonAction.wilsonDensity` and the boxes are `symCube τ (2 * p)`, so the hypotheses left are the
coupling `β`, the boundary configuration `ω` and `N ≠ 0`.

The four density properties are `WilsonAction.measurable_wilsonDensity`, `wilsonDensity_nonneg`,
`wilsonDensity_le_two` and `wilsonDensity_conj`; the middle two take `N ≠ 0` and the others take
nothing.

Scope: `N ≠ 0` leaves `N = 1`, where the group is a singleton, `IConf (SU 1)` is a singleton and
`halfSpaceAlg` is the constants, so the statement holds there with no content. The limit is along an
ultrafilter refining `atTop`, from `DLRLimit.exists_limit_state`; no sequence is shown to converge.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p`; `4` is the dimension. The `0` is
the one in `N ≠ 0`. -/
theorem wilson_reflPositive_limit_exists (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ℕ) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) ω f)
          (u : Filter ℕ) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, -, htend, hpos⟩ :=
    reflPositive_limit_on_halfSpaceAlg (ι := ℕ) Filter.atTop τ p (symCube τ (2 * p))
      (fun n => symCube_refl_stable τ (2 * p) n) (fun S => symCube_exhausts τ (2 * p) S)
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN)
      (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β ω
  exact ⟨u, ν, htend, hpos⟩

#print axioms wilson_reflPositive_limit_exists

/-! ## 6″. The reflection facts the operator side reads -/



/-- `reflection_facts_of_limit` with positivity on `halfSpaceAlg τ p` rather than on one fixed
finite
region — the form `WilsonTransferReduction` consumes. Invariance is unchanged,
`InfiniteReflection.isReflectionInvariant_of_tendsto` over `stateFree_reflection_invariant`, which
is why `hω` asks the boundary condition to be reflection symmetric.

DERIVED: the `2` is the plane-to-constant conversion `c = 2 * p` and the ceiling in `hφ2`; `4` is
the dimension. The `0` is the sign in `hφ0`. -/
theorem reflection_facts_on_halfSpaceAlg
    {ι : Type*} (l : Filter ι) [l.NeBot] (τ : Fin 4) (p : ℤ)
    (box : ι → Finset MassGap.InfiniteLattice.ILink)
    (hbox : ∀ i, ∀ lk ∈ box i, ireflLink τ (2 * p) lk ∈ box i)
    (hexh : ∀ S : Finset MassGap.InfiniteLattice.ILink, ∀ᶠ i in l, S ⊆ box i)
    {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2)
    (hφc : ∀ g h, φ (g * h * g⁻¹) = φ h) (β : ℝ)
    {ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)}
    (hω : MassGap.LatticeReflection.ireflConf τ (2 * p) ω = ω) :
    ∃ (u : Ultrafilter ι) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ι) ≤ l ∧
      (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun i => stateFree hφm hφ0 hφ2 β (box i) ω f)
          (u : Filter ι) (nhds (ν f))) ∧
      MassGap.InfiniteReflection.IsReflectionInvariant
        (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν ∧
      MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν := by
  obtain ⟨u, ν, hle, htend⟩ :=
    MassGap.DLRLimit.exists_limit_state l (fun i => stateFree hφm hφ0 hφ2 β (box i) ω)
  haveI : (u : Filter ι).NeBot := u.neBot'
  refine ⟨u, ν, hle, htend, ?_,
    reflPositive_of_tendsto_halfSpaceAlg τ p box hbox
      (fun S => ((hexh S).filter_mono hle)) hφm hφ0 hφ2 hφc β ω ν htend⟩
  exact MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun i =>
      stateFree_reflection_invariant (hbox i) hφm hφ0 hφ2 hφc β hω))

#print axioms reflection_facts_on_halfSpaceAlg

/-- `WilsonTransferReduction.transferData_of_state_facts` with its third input derived: it takes
`hinv`,
`hpos` and `hnu`, and `ReflectionShift.nu_T_of_reflection_invariant` produces `hnu` from reflection
invariance at two adjacent constants, one translation being two reflections. So the inputs here are
`hinv` at `2 * p`, `hinvOdd` at `2 * p - 1`, and `hpos`.

`ReflectionShift.reflection_invariant_succ_iff_nu_T` shows that, given `hinv`, `hinvOdd` and `hnu`
imply each other, so this changes the kind of the remaining hypothesis rather than removing one.
`hinvOdd` has the shape `stateFree_reflection_invariant` proves at finite volume at every constant,
where `hnu` has no finite-volume counterpart; it is an equality, so the `0 ≤ β` restriction that
separates the odd reflection for `ReflPositiveOn`
(`CharacterExpansion.NegControl.su3_kernel_nonneg_iff`) does not enter it, and it transports to a
limit by `InfiniteReflection.isReflectionInvariant_of_tendsto`.

`eq_empty_of_stable_two_mirrors` shows one box family cannot supply both invariances, so two
families are needed and something has to identify their limits.
`wilson_transferData_of_thermodynamic_limit` states that as a single convergence hypothesis.

`ν` is a free parameter here, so the result can be rank one: evaluation at the all-identity
configuration satisfies all three hypotheses at every constant, even and odd, since `ireflConf`
inverts only on `τ`-links and `1⁻¹ = 1`. Its form is `F ↦ F(1)·H(1)`, whose GNS space is `ℝ` and
whose transfer operator is the identity, and `TransferData`'s only non-degeneracy field, `vac_norm`,
holds there. The object is produced; its spectrum is `TransferGap.GapAt` and is carried separately.
`reflection_facts_on_halfSpaceAlg`'s conjoined `Tendsto` clause is what ties `ν` to the Wilson
measure, and this definition does not carry it.

DERIVED: the `2` and the `1` are the plane-to-constant conversion and the mirror separation; `4` is
the dimension. -/
noncomputable def transferData_of_reflection_facts (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hinvOdd : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν) :
    MassGap.Transfer.TransferData
      ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) :=
  MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos
    (fun f => MassGap.ReflectionShift.nu_T_of_reflection_invariant τ (2 * p - 1) ν hinvOdd
      (by rw [sub_add_cancel]; exact hinv) f)

#print axioms transferData_of_reflection_facts

/-- `transferData_of_reflection_facts` with every structural hypothesis discharged: `φ` is the
Wilson
density, the boundary condition is the all-identity configuration (symmetric about every mirror by
`ireflConf_one`), and the boxes are `symCube` at each of the two constants — reflection-stable by
`symCube_refl_stable` and exhausting by `symCube_exhausts`. Positivity comes from
`reflPositive_of_tendsto_halfSpaceAlg`, invariance at each constant from
`stateFree_reflection_invariant` there, and translation invariance from
`ReflectionShift.nu_T_of_reflection_invariant`.

What is assumed is that the two families converge to the same state: `hEven` and `hOdd` name the
same `ν`. `eq_empty_of_stable_two_mirrors` shows a finite box stable under the mirrors at `2 * p`
and `2 * p - 1` is empty, so two families are needed whenever the odd invariance comes from a
finite-volume box statement. The two also differ by a diagonal translation of their centre, since
`coordCube c n` is centred at `c` in every coordinate.

Convergence is along `atTop` rather than along a refining ultrafilter:
`DLRLimit.exists_limit_state` gives the latter for one family but not a common limit for two.

`TransferData` carries no spectral content; the gap is `TransferGap.GapAt`. At `N ≤ 1` the carrier
is the constants.

DERIVED: the `2` and the `1` are the plane-to-constant conversion and the mirror separation; `4` is
the dimension. The `0` is the one in `N ≠ 0`. -/
noncomputable def wilson_transferData_of_common_limit (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hEven : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        Filter.atTop (nhds (ν f)))
    (hOdd : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.Transfer.TransferData
      ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) :=
  transferData_of_reflection_facts τ p ν
    (MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto hEven _
      (Filter.Eventually.of_forall (fun n =>
        stateFree_reflection_invariant (symCube_refl_stable τ (2 * p) n)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN)
          (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β
          (ireflConf_one τ (2 * p)))))
    (MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto hOdd _
      (Filter.Eventually.of_forall (fun n =>
        stateFree_reflection_invariant (symCube_refl_stable τ (2 * p - 1) n)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN)
          (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β
          (ireflConf_one τ (2 * p - 1)))))
    (reflPositive_of_tendsto_halfSpaceAlg τ p (symCube τ (2 * p))
      (fun n => symCube_refl_stable τ (2 * p) n)
      (fun S => symCube_exhausts τ (2 * p) S)
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN)
      (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β 1 ν hEven)

#print axioms wilson_transferData_of_common_limit

/-- The two box shapes interleaved into one sequence: even steps carry the mirror at `2 * p`, odd
steps
the mirror at `2 * p - 1`, each at half the step index so both shapes grow without bound.

DERIVED: the `2`s are the plane-to-constant conversion, the interleaving period and the halved
index; the `1` is the mirror separation; the `0` is the parity test `n % 2 = 0`; `4` is the
dimension. -/
noncomputable def mixCube (τ : Fin 4) (p : ℤ) (n : ℕ) : Finset MassGap.InfiniteLattice.ILink :=
  if n % 2 = 0 then symCube τ (2 * p) (n / 2) else symCube τ (2 * p - 1) (n / 2)

/-- At an even index, `mixCube` is the even cube family: `mixCube τ p (2 * k) = symCube τ (2 * p)
k`.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period; `4` is the
dimension. -/
theorem mixCube_even (τ : Fin 4) (p : ℤ) (k : ℕ) :
    mixCube τ p (2 * k) = symCube τ (2 * p) k := by
  have h1 : (2 * k) % 2 = 0 := by omega
  have h2 : (2 * k) / 2 = k := by omega
  simp [mixCube, h1, h2]

#print axioms mixCube_even

/-- At an odd index it is the odd one: `mixCube τ p (2 * k + 1) = symCube τ (2 * p - 1) k`.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period, and the `1`s are
the odd index and the mirror separation; `4` is the dimension. -/
theorem mixCube_odd (τ : Fin 4) (p : ℤ) (k : ℕ) :
    mixCube τ p (2 * k + 1) = symCube τ (2 * p - 1) k := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [mixCube, h1, h2]

#print axioms mixCube_odd

/-- The even subsequence of `mixCube` is `symCube τ (2 * p)`, so one convergence hypothesis about
`mixCube` gives convergence of the even cube family to the same state. Stated as a lemma rather than
derived inside a proof because the results below need it in a statement.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period; the `0` is the
one in `N ≠ 0`; the `1` is the all-identity boundary condition; `4` is the dimension. -/
theorem tendsto_symCube_even_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        Filter.atTop (nhds (ν f)) := by
  have hdouble : Filter.Tendsto (fun k : ℕ => 2 * k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  intro f
  have h := (htend f).comp hdouble
  simp only [Function.comp_def, mixCube_even] at h
  exact h

#print axioms tendsto_symCube_even_of_mixCube

/-- And the odd subsequence is `symCube τ (2 * p - 1)`, giving convergence of the odd cube family to
the
same state.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period, the `1` the
mirror separation; the `0` is the one in `N ≠ 0`; the other `1` is the all-identity boundary
condition; `4` is the dimension. -/
theorem tendsto_symCube_odd_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        Filter.atTop (nhds (ν f)) := by
  have hdoubleSucc : Filter.Tendsto (fun k : ℕ => 2 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  intro f
  have h := (htend f).comp hdoubleSucc
  simp only [Function.comp_def, mixCube_odd] at h
  exact h

#print axioms tendsto_symCube_odd_of_mixCube

/-- **`mixCube` exhausts.** Every finite link set is eventually inside it.

`mixCube` interleaves two box families at two different reflection planes, so it is not monotone and
exhaustion does not follow from a single `symCube_exhausts`. It follows from both: past the larger
of the two thresholds, whichever branch the parity selects has already swallowed `S`.

DERIVED: `4` is the spacetime dimension, the `Fin 4` the lattice direction ranges over; `2` is the
interleaving period and the plane-to-constant conversion; `1` is the offset that puts the index past
both thresholds on either branch. -/
theorem mixCube_exhausts (τ : Fin 4) (p : ℤ) (S : Finset MassGap.InfiniteLattice.ILink) :
    ∀ᶠ n : ℕ in Filter.atTop, S ⊆ mixCube τ p n := by
  have he := symCube_exhausts τ (2 * p) S
  have ho := symCube_exhausts τ (2 * p - 1) S
  rw [Filter.eventually_atTop] at he ho ⊢
  obtain ⟨Ne, hNe⟩ := he
  obtain ⟨No, hNo⟩ := ho
  refine ⟨2 * (max Ne No) + 1, fun n hn => ?_⟩
  have hdiv : max Ne No ≤ n / 2 := by omega
  unfold mixCube
  split
  · exact hNe _ (le_trans (le_max_left _ _) hdiv)
  · exact hNo _ (le_trans (le_max_right _ _) hdiv)

#print axioms mixCube_exhausts

/-- `mixCube` is cofinal: it tends to `atTop` in the finite link sets.

This is what lets a limit taken along ALL finite regions be read along the interleaved box sequence.
`WilsonDLR.tendsto_specState_at_zero` gives the first shape and
`wilson_positiveTransfer_of_mixCube_limit` wants the second.

DERIVED: `4` is the spacetime dimension, the `Fin 4` the lattice direction ranges over. No other
numeral occurs. -/
theorem tendsto_mixCube (τ : Fin 4) (p : ℤ) :
    Filter.Tendsto (mixCube τ p) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro S
  simpa [Finset.le_iff_subset] using mixCube_exhausts τ p S

#print axioms tendsto_mixCube

/-- **The reflected plaquette is non-degenerate.** `ireflPlaq` either transposes the plane with the
reflection direction or leaves it alone; in the transposing branches the direction that becomes new
is the one the hypothesis says differs from `τ`.

DERIVED: `4` is the spacetime dimension, the range of the plane and reflection directions. -/
theorem ireflPlaq_nondeg (τ : Fin 4) (c : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hq : q.1.1 ≠ q.1.2) :
    (MassGap.LatticeReflection.ireflPlaq τ c q).1.1
      ≠ (MassGap.LatticeReflection.ireflPlaq τ c q).1.2 := by
  unfold MassGap.LatticeReflection.ireflPlaq
  split_ifs with h1 h2
  · intro h; exact hq (h1.trans h.symm)
  · intro h; exact h1 h.symm
  · exact hq

#print axioms ireflPlaq_nondeg

/-- **A translate is non-degenerate.** `ishiftPlaq` moves the corner and leaves the plane alone, so
the plane directions are unchanged.

DERIVED: `4` is the spacetime dimension; `m` is the caller's. -/
theorem ishiftPlaq_iterate_nondeg (τ : Fin 4) (m : ℕ) (q : MassGap.GibbsSpec.IPlaq)
    (hq : q.1.1 ≠ q.1.2) :
    ((MassGap.InfiniteShift.ishiftPlaq τ)^[m] q).1.1
      ≠ ((MassGap.InfiniteShift.ishiftPlaq τ)^[m] q).1.2 := by
  rw [ishiftPlaq_iterate]
  exact hq

#print axioms ishiftPlaq_iterate_nondeg

/-- **A non-degenerate plaquette eventually lies in the box.** `mixCube_exhausts` at the plaquette's
own four links, through `GibbsSpec.mem_plaqsIn`.

DERIVED: `4` is the spacetime dimension. -/
theorem eventually_mem_iplqAll (τ : Fin 4) (p : ℤ) (q : MassGap.GibbsSpec.IPlaq)
    (hq : q.1.1 ≠ q.1.2) :
    ∀ᶠ n : ℕ in Filter.atTop, q ∈ iplqAll (mixCube τ p n) := by
  filter_upwards [mixCube_exhausts τ p (MassGap.GibbsSpec.ilinks q).toFinset] with n hn
  refine mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr (fun l hl => ?_), hq⟩
  exact hn (List.mem_toFinset.mpr hl)

#print axioms eventually_mem_iplqAll

/-- **A plaquette, its reflection and its translate all eventually lie in the box.**

This supplies the box-membership side conditions of
`GaugeInvariantAlgebra.stateFree_pairing_shift_abs_le` for all large boxes, which is what the
box-to-limit assembly needs before `DLRLimit.abs_le_of_eventually_abs_le` can be applied: the
estimate's constants `coreConst` and `coreRate` are already box-free, since `touchDeg_boxBd_le`
carries no box dependence, so membership was the only remaining obstacle to an eventual hypothesis.

DERIVED: `2` is the reflection plane's spacing in lattice units; `4` is the spacetime dimension;
`m` is the caller's. -/
theorem eventually_mem_iplqAll_refl_shift (τ : Fin 4) (p : ℤ)
    (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) (m : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      q ∈ iplqAll (mixCube τ p n)
        ∧ MassGap.LatticeReflection.ireflPlaq τ (2 * p) q ∈ iplqAll (mixCube τ p n)
        ∧ (MassGap.InfiniteShift.ishiftPlaq τ)^[m] q ∈ iplqAll (mixCube τ p n) := by
  filter_upwards [eventually_mem_iplqAll τ p q hq,
    eventually_mem_iplqAll τ p (MassGap.LatticeReflection.ireflPlaq τ (2 * p) q)
      (ireflPlaq_nondeg τ (2 * p) q hq),
    eventually_mem_iplqAll τ p ((MassGap.InfiniteShift.ishiftPlaq τ)^[m] q)
      (ishiftPlaq_iterate_nondeg τ m q hq)] with n h1 h2 h3
  exact ⟨h1, h2, h3⟩

#print axioms eventually_mem_iplqAll_refl_shift

/-- **The interiority side condition holds at all large boxes.**

`stateFree_spec_eq_of_bounded` asks that every NON-degenerate plaquette touching `V` lie in the box.
For fixed `V` that is a finite set of plaquettes, each with finitely many links, so
`mixCube_exhausts` puts them all inside eventually.

DERIVED: `4` is the spacetime dimension, indexing the reflection's direction. -/
theorem eventually_hside (τ : Fin 4) (p : ℤ) (V : Finset MassGap.InfiniteLattice.ILink) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ q ∈ MassGap.GibbsSpec.boundaryPlaqs V,
      q.1.1 ≠ q.1.2 → q ∈ iplqAll (mixCube τ p n) := by
  filter_upwards [mixCube_exhausts τ p ((MassGap.GibbsSpec.boundaryPlaqs V).biUnion
    (fun q => (MassGap.GibbsSpec.ilinks q).toFinset))] with n hn q hq hne
  refine mem_iplqAll.mpr ⟨MassGap.GibbsSpec.mem_plaqsIn.mpr (fun l hl => ?_), hne⟩
  exact hn (Finset.mem_biUnion.mpr ⟨q, hq, List.mem_toFinset.mpr hl⟩)

#print axioms eventually_hside

/-- **The free-boundary DLR consistency, eventually along the exhausting cube family.**

Both side conditions — the region inside the box, and every non-degenerate plaquette touching it
inside the box — hold at all large boxes, by `mixCube_exhausts` and `eventually_hside`. So the
consistency holds eventually, which is exactly the `hev` shape `DLRLimit.isDLR_of_tendsto`,
`tendsto_of_unique_dlr` and `limits_eq_of_unique_dlr` consume.

**This completes the free-boundary side of the DLR theory.** `GibbsSpec.wilson_dlr_consistent`
supplies the same for the FIXED-boundary family at every coupling; the free-boundary family is what
the transfer construction consumes and what reflection positivity is proved for, and it had no such
supply until now.

What it does NOT supply is uniqueness of the DLR state, which is what
`limits_eq_of_unique_dlr` additionally requires and what fails at a phase transition.

DERIVED: `4` is the spacetime dimension; `1` is the identity at which the density vanishes and the
bound on the observable; `0` and `2` are the density's range. -/
theorem eventually_stateFree_spec_eq {φ : MassGap.SUN.SU N → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ g, 0 ≤ φ g) (hφ2 : ∀ g, φ g ≤ 2) (hφ1 : φ 1 = 0) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (V : Finset MassGap.InfiniteLattice.ILink)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (f g : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hg : ∀ ω', g ω' = MassGap.GibbsSpec.spec φ β V (probHaar (MassGap.SUN.SU N)) (⇑f) ω')
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hfb : ∀ U, |f U| ≤ C₀) :
    ∀ᶠ n : ℕ in Filter.atTop,
      stateFree hφm hφ0 hφ2 β (mixCube τ p n) ω g
        = stateFree hφm hφ0 hφ2 β (mixCube τ p n) ω f := by
  filter_upwards [mixCube_exhausts τ p V, eventually_hside τ p V] with n hsub hs
  exact stateFree_spec_eq_of_bounded hφm hφ0 hφ2 hφ1 β hsub hs ω f g hg hC₀ hfb

#print axioms eventually_stateFree_spec_eq

/-- Reflection positivity at the even constant from one convergence hypothesis about the interleaved
family: the even subsequence of `mixCube` is `symCube τ (2 * p)`
(`tendsto_symCube_even_of_mixCube`), and `wilson_reflPositive_even_of_tendsto` takes it from there.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period; `4` is the
dimension. The `0` is the one in `N ≠ 0` and the `1` is the all-identity boundary condition. -/
theorem wilson_reflPositive_even_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
    (tendsto_symCube_even_of_mixCube τ p hN β ν htend)

#print axioms wilson_reflPositive_even_of_mixCube

/-- And reflection positivity at the odd constant from the same hypothesis, the odd subsequence
being
`symCube τ (2 * p - 1)`. Takes `0 ≤ β`, which the even statement does not.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period, the `1` the
mirror separation; the `0` is the sign of the coupling; `4` is the dimension. -/
theorem wilson_reflPositive_odd_of_mixCube (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  wilson_reflPositive_odd_of_tendsto τ p hN hβ 1 ν Filter.atTop le_rfl
    (tendsto_symCube_odd_of_mixCube τ p hN β ν htend)

#print axioms wilson_reflPositive_odd_of_mixCube


/-- Along any ultrafilter, `mixCube` is eventually equal to one of the two box shapes, so an
ultrafilter
limit of the interleaved sequence is a limit of a single shape and carries a single reflection
constant. The `∨` is `Ultrafilter.mem_or_compl_mem`, the "at least one" half; exclusivity is neither
stated nor used.

Scope: this is about ultrafilter limits of `mixCube`. `wilson_reflPositive_limit_exists` and
`wilson_reflPositive_limit_exists_odd` each produce a limit state without mentioning `mixCube`, and
nothing here relates those two states. `atTop` meets both parity classes cofinally, which is what
`wilson_positiveTransfer_of_mixCube_limit` uses.

DERIVED: the `2`s are the plane-to-constant conversion, the interleaving period and the halved
index, the `1` the mirror separation; `4` is the dimension. The `0` of the parity test is in the
proof, not in the signature. -/
theorem mixCube_ultrafilter_sees_one_parity (τ : Fin 4) (p : ℤ) (u : Ultrafilter ℕ) :
    (∀ᶠ n in (u : Filter ℕ), mixCube τ p n = symCube τ (2 * p) (n / 2))
      ∨ (∀ᶠ n in (u : Filter ℕ), mixCube τ p n = symCube τ (2 * p - 1) (n / 2)) := by
  rcases u.mem_or_compl_mem {n : ℕ | n % 2 = 0} with h | h
  · refine Or.inl (Filter.Eventually.mono h (fun n hn => ?_))
    have hn' : n % 2 = 0 := hn
    show (if n % 2 = 0 then symCube τ (2 * p) (n / 2) else symCube τ (2 * p - 1) (n / 2))
      = symCube τ (2 * p) (n / 2)
    rw [if_pos hn']
  · refine Or.inr (Filter.Eventually.mono h (fun n hn => ?_))
    have hn' : ¬ (n % 2 = 0) := hn
    show (if n % 2 = 0 then symCube τ (2 * p) (n / 2) else symCube τ (2 * p - 1) (n / 2))
      = symCube τ (2 * p - 1) (n / 2)
    rw [if_neg hn']

#print axioms mixCube_ultrafilter_sees_one_parity



/-- The limit state is invariant under the reflection at whatever constant the family is closed
under.
Each finite-volume state is invariant because the all-identity boundary condition is fixed by every
mirror (`ireflConf_one`) and the Wilson density is conjugation-invariant
(`wilsonDensity_conj`), and `InfiniteReflection.isReflectionInvariant_of_tendsto` passes that to the
limit. Generic in `c`, so it serves both `2 * p` and `2 * p - 1`.

DERIVED: `c` is the caller's reflection constant; the `0` is the one in `N ≠ 0`; the `1` is the
all-identity boundary condition; `4` is the dimension. -/
theorem wilson_reflInvariant_of_tendsto (τ : Fin 4) (c : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (l : Filter ℕ) [l.NeBot]
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ c n) 1 f)
        l (nhds (ν f))) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ c) ν :=
  MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun n =>
      stateFree_reflection_invariant (symCube_refl_stable τ c n)
        MassGap.WilsonAction.measurable_wilsonDensity
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN)
        (fun g h => MassGap.WilsonAction.wilsonDensity_conj g h) β (ireflConf_one τ c)))

#print axioms wilson_reflInvariant_of_tendsto

/-- The limit state is translation invariant — the `hnu` that
`WilsonTransferReduction.transferData_of_state_facts` takes — from invariance at the two adjacent
constants. `ReflectionShift.nu_T_of_reflection_invariant` composes the mirrors at `a` and `a + 1`
into one translation; here `a = 2 * p - 1`, so the two mirrors are the odd and the even one and each
family supplies its own.

The two convergence hypotheses are separate because `eq_empty_of_stable_two_mirrors` shows no single
family is stable under both mirrors. The filters `lE` and `lO` need not agree.

DERIVED: the `2` is the plane-to-constant conversion and the `1` the mirror separation; the `0` is
the one in `N ≠ 0`; the other `1` is the all-identity boundary condition; `4` is the dimension. -/
theorem wilson_nu_T_of_tendsto (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (lE lO : Filter ℕ) [lE.NeBot] [lO.NeBot]
    (hEven : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        lE (nhds (ν f)))
    (hOdd : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        lO (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f := by
  have hEvenInv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 1 + 1)) ν := by
    rw [show (2 * p - 1 + 1 : ℤ) = 2 * p from by ring]
    exact wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven
  exact MassGap.ReflectionShift.nu_T_of_reflection_invariant τ (2 * p - 1) ν
    (wilson_reflInvariant_of_tendsto τ (2 * p - 1) hN β ν lO hOdd) hEvenInv

#print axioms wilson_nu_T_of_tendsto

/-- `GNSHilbert.PositiveTransfer` for the assembled transfer data, from two convergence facts. The
two
cube families need share only one state `ν`, and may reach it along different filters; each filter
refines `atTop` so that `hexh` and `hR` transport, and nothing else about it is used. Reflection
invariance comes from `wilson_reflInvariant_of_tendsto` at each constant and translation invariance
from `wilson_nu_T_of_tendsto`, so what the caller supplies is the two limits, the two filter
refinements, `0 ≤ β` and `N ≠ 0`.

That the two limits can be chosen equal is a hypothesis. Compactness gives each family its own
subsequential limit — `wilson_reflPositive_limit_exists` unconditionally,
`wilson_reflPositive_limit_exists_odd` under `0 ≤ β` — and nothing here identifies the two states;
`eq_empty_of_stable_two_mirrors` shows no single family carries both constants. Convergence along
`atTop` is one sufficient condition (`wilson_positiveTransfer_of_mixCube_limit`).

At `N ≤ 1` the carrier is one-dimensional; `halfSpaceAlg_has_nonconstant` is a witness at `SU 3`.

DERIVED: the `2` is the plane-to-constant conversion and the `1` the mirror separation; the `0` is
the sign of the coupling and the one in `N ≠ 0`; the other `1` is the all-identity boundary
condition; `4` is the dimension. -/
theorem wilson_positiveTransfer_of_common_subsequential_limit (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (lE lO : Filter ℕ) [lE.NeBot] [lO.NeBot]
    (hlE : lE ≤ Filter.atTop) (hlO : lO ≤ Filter.atTop)
    (hEven : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
        lE (nhds (ν f)))
    (hOdd : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p - 1) n) 1 f)
        lO (nhds (ν f))) :
    MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν
        (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
        (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE hEven)
        (wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)) :=
  (MassGap.WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive τ p ν
      (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
      (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE hEven)
      (wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)).mpr
    (wilson_reflPositive_odd_of_tendsto τ p hN hβ 1 ν lO hlO hOdd)

#print axioms wilson_positiveTransfer_of_common_subsequential_limit

/-- `HalfSpaceAlgebra.ishiftObsCM` and `ReflectionShift.ishiftObsL` are the same map, by `rfl`:
identical bodies — precomposition with `InfiniteShift.ishiftConf` — in two namespaces, so a lemma
proved about one is inert on the other and a goal display does not tell them apart. The same bridge
`gibbs_ishift_eq` records for `ishift`.

Nothing in this file consumes it: `HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` is about
the first, `TransferData.T` is built by `TransferAssembly.restrictT` from the second, and
`transferData_of_state_facts_T_ne_id` closes by definitional unfolding without citing this.
`InfiniteShift.ishiftObs` is a third, unbundled copy of the same map, carrying its own motion
theorems (`InfiniteShift.ishiftObs_infinite_order`,
`InfiniteShift.ishiftObs_ne_id_of_separating`); this records one of the three pairs.

DERIVED: the signature writes no numeral; `4` is the dimension. -/
theorem ishiftObsCM_eq_ishiftObsL (τ : Fin 4) :
    (MassGap.HalfSpaceAlgebra.ishiftObsCM (G := MassGap.SUN.SU N) τ)
      = MassGap.ReflectionShift.ishiftObsL τ := rfl

#print axioms ishiftObsCM_eq_ishiftObsL

/-- The assembled data's `T` is not the identity on `halfSpaceAlg`, given a function separating two
group elements. `HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` at `k = 1` supplies a
member the shift moves, and `TransferAssembly.restrictT_coe` carries it through the restriction.

So `GNSHilbert.positiveTransfer_of_T_eq_id`, which discharges `PositiveTransfer` for the other
`TransferData`s in this tree, does not apply to this carrier; positivity here is
`wilson_positiveTransfer_of_common_subsequential_limit`'s to supply.

This is motion in the algebra, not in the GNS quotient: `opT [F] = [F]` whenever `T F - F` lies in
the null space of the form, and nothing here rules that out.
`HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg` carries the same caveat. The separating
hypothesis `hf` is real: at `SU 0` and `SU 1` the group is a singleton and no separating function
exists, while `CrossingIntegration.trace_gNeg` supplies one at `SU 3`.

DERIVED: the `2` is the plane-to-constant conversion; the `1` is the single shift step; `4` is the
dimension. -/
theorem transferData_of_state_facts_T_ne_id (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    {f : C(MassGap.SUN.SU N, ℝ)} {g₀ g₁ : MassGap.SUN.SU N} (hf : f g₀ ≠ f g₁) :
    ∃ F : ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p),
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu).T F
        ≠ F := by
  obtain ⟨F, hFmem, hFne⟩ :=
    MassGap.HalfSpaceAlgebra.shift_no_finite_order_on_halfSpaceAlg τ p hf (k := 1) one_pos
  refine ⟨⟨F, hFmem⟩, fun h => hFne ?_⟩
  rw [Function.iterate_one]
  exact congrArg Subtype.val h

#print axioms transferData_of_state_facts_T_ne_id

/-- `transferData_of_state_facts_T_ne_id` with the separating premise discharged by
`reTrCM_separating`: the assembled transfer operator is not the identity on the half-space algebra
at every `SU (m + 2)`.

`hinv`, `hpos` and `hnu` remain hypotheses, and the conclusion is about
`WilsonTransferReduction.transferData_of_state_facts` applied to them. At `SU 0` and `SU 1` no
separating function exists, which is why the matrix dimension is written `m + 2`. This is motion in
the algebra, not in the GNS quotient; `ClayAssembly.transferMovesSomething_of_pairing_ne` is a
sufficient condition for the latter.

DERIVED: the `2`s are the plane-to-constant conversion and the least matrix dimension at which two
group elements exist; `m` is the caller's; `4` is the dimension. -/
theorem transferData_T_ne_id_of_rank_two (τ : Fin 4) (p : ℤ) (m : ℕ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU (m + 2))))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU (m + 2)) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU (m + 2)), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) :
    ∃ F : ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU (m + 2)) τ p),
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu).T F
        ≠ F :=
  transferData_of_state_facts_T_ne_id (N := m + 2) τ p ν hinv hpos hnu (reTrCM_separating m)

#print axioms transferData_T_ne_id_of_rank_two

/-- `wilson_positiveTransfer_of_common_subsequential_limit` at `lE = lO = atTop`, with the two
convergence facts read off the interleaved family's even and odd subsequences, so both reflection
constants come from one hypothesis.

`eq_empty_of_stable_two_mirrors` shows no nonempty box is stable under two adjacent mirrors, so
`symCube τ (2 * p)` and `symCube τ (2 * p - 1)` are different families; subsequences of one
convergent sequence share a limit, but only along a filter meeting both parity classes cofinally,
which `mixCube_ultrafilter_sees_one_parity` shows an ultrafilter need not do.

At `N ≤ 1` the carrier is one-dimensional; `halfSpaceAlg_has_nonconstant` is a witness at `SU 3`.

DERIVED: the `2`s are the plane-to-constant conversion and the interleaving period, the `1` the
mirror separation; the `0` is the sign of the coupling and the one in `N ≠ 0`; the other `1` is the
all-identity boundary condition; `4` is the dimension. -/
theorem wilson_positiveTransfer_of_mixCube_limit (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν
        (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
        (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
        (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop (tendsto_symCube_even_of_mixCube τ p hN β ν htend) (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))) :=
  wilson_positiveTransfer_of_common_subsequential_limit τ p hN hβ ν
    Filter.atTop Filter.atTop le_rfl le_rfl (tendsto_symCube_even_of_mixCube τ p hN β ν htend) (tendsto_symCube_odd_of_mixCube τ p hN β ν htend)

#print axioms wilson_positiveTransfer_of_mixCube_limit

/-- `wilson_transferData_of_common_limit` with the two convergence hypotheses read off one:
interleaving
the two box shapes into `mixCube` makes the sharing automatic, since the even and odd subsequences
of a convergent sequence converge to its limit.

What the caller supplies is convergence along one exhausting family of boxes with the all-identity
boundary condition, along `atTop`. `DLRLimit.exists_limit_state` gives convergence along a refining
ultrafilter instead, and that difference is what this hypothesis covers.

`TransferData` carries no spectral content. At `N ≤ 1` the carrier is the constants.

DERIVED: the `2` is the plane-to-constant conversion; `4` is the dimension. The `0` is the one in
`N ≠ 0` and the `1` is the all-identity boundary condition. -/
noncomputable def wilson_transferData_of_thermodynamic_limit
    (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.Transfer.TransferData
      ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) := by
  have hdouble : Filter.Tendsto (fun k : ℕ => 2 * k) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have hdoubleSucc : Filter.Tendsto (fun k : ℕ => 2 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  refine wilson_transferData_of_common_limit τ p hN β ν (fun f => ?_) (fun f => ?_)
  · have h := (htend f).comp hdouble
    simp only [Function.comp_def, mixCube_even] at h
    exact h
  · have h := (htend f).comp hdoubleSucc
    simp only [Function.comp_def, mixCube_odd] at h
    exact h

#print axioms wilson_transferData_of_thermodynamic_limit

/-- `TransferGap.GapAt` for the infinite-volume transfer data at `r`, from a finite-volume
inequality.
The hypothesis `hfin` asks that for every `F` in the half-space algebra, eventually along the box
family and with each box subtracting its own mean,

    ⟨θ_{2p-2} F · F⟩ₙ - ⟨F⟩ₙ⟨θ_{2p-2} F⟩ₙ  ≤  r² · ( ⟨θ_{2p} F · F⟩ₙ - ⟨F⟩ₙ⟨θ_{2p} F⟩ₙ ),

where `⟨·⟩ₙ` is `stateFree` at `box n` with the all-identity boundary condition. The other
hypotheses are the state's three reflection facts `hinv`, `hpos`, `hnu` and the convergence `htend`.

`hfin` itself names no limit state: both sides are connected two-point functions of one explicit
finite integral, `stateFree` being `specFree` normalised and `specFree` a ratio of two Bochner
integrals of `wtFree` over the box's product Haar measure.
`InfiniteReflection.state_pairing_subtracted` identifies the vacuum-subtracted pairing with the
connected correlator, so each box's connected pairing converges to the limit state's term by term,
and `InfiniteReflection.connected_pairing_le_of_eventually` carries the inequality across.

The subtraction is part of the statement rather than a premise: at `F = 1` both sides are `0`, so
the collapse that makes an unsubtracted decay hypothesis contradictory — `1 ≤ r²`, whence
`TransferGap.gapAt_of_one_le_sq` gives the conclusion — does not arise. What `hfin` asserts is that
the connected two-step reflection pairing decays by `r²` against the connected zero-step one,
uniformly in the volume.

DERIVED: the `2`s are the plane-to-constant conversion and the two-step separation, the `1` is the
all-identity boundary condition; `4` is the dimension. The `0` is the one in `N ≠ 0`. -/
theorem gapAt_of_finite_volume_connected (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) (r : ℝ)
    (box : ℕ → Finset MassGap.InfiniteLattice.ILink)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 f) Filter.atTop (nhds (ν f)))
    (hfin : ∀ F ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p,
      ∀ᶠ n in Filter.atTop,
        stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) F * F)
            - stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 F * stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) F)
          ≤ r ^ 2 * (stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p) F * F)
            - stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 F * stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) β (box n) 1 (MassGap.LatticeReflection.ireflObs τ (2 * p) F))) :
    MassGap.TransferGap.GapAt
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu) r :=
  (MassGap.WilsonTransferReduction.gapAt_iff_subtracted_pairing τ p ν hinv hpos hnu r).mpr
    (MassGap.InfiniteReflection.connected_pairing_le_of_eventually htend
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.LatticeReflection.latticeReflection τ (2 * p - 2))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) r hfin)

#print axioms gapAt_of_finite_volume_connected

end StateAlgebra

end Split

/-! ## 4. The obligation, as a named proposition -/

section Obligation

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- `ReflPositiveOn (latticeReflection τ (2 * p)) (halfSpaceAlg τ p) ν` as a named proposition: the
reflection constant is twice the plane, which is the pairing `reflection_exchanges_halves`
establishes. This declaration names the statement; it does not supply it.

Stated for a compact topological group with continuous inversion, not only for `SU N`.

DERIVED: the `2` is `reflection_exchanges_halves`'s plane-to-constant conversion; `4` is the
dimension. -/
def HalfSpaceReflPositive (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (IConf G)) : Prop :=
  MassGap.InfiniteReflection.ReflPositiveOn
    (MassGap.LatticeReflection.latticeReflection τ (2 * p))
    (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p) ν

end Obligation

end MassGap.ReflectionHalfSpace
