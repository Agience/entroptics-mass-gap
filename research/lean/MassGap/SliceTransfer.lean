import MassGap.OddLagSplit

/-!
# MassGap.SliceTransfer — the Wilson action split by time slice, and the slice-to-slice kernel

The kernel this file builds is a slice-to-slice kernel `T(V, W)` acting on functions of the spatial
links of one time slice. Parts 0 to 2 build the geometry the lattice supplies to it, Part 3 the
identity that ties it to plaquette energies, and Part 4 the kernel itself.

## Parts 0 to 2 — the split

`plaqSum_eq_slice_sum` and `action_eq_slice_sum`: for any choice of time direction `τ : Fin d`,

    S(U) = ∑_{t : Fin n} ( intraSliceAction τ t U + interSliceAction τ t U ),

a `Finset` partition of `WilsonHypercubic.Plaq d n` by the `τ`-coordinate of a plaquette's base site
and by whether its direction pair contains `τ`. The inputs are `Finset.sum_filter`,
`Finset.sum_comm` and `Finset.sum_filter_add_sum_filter_not`, the first two collected in
`sum_by_fibre`.

Which links each block reads is read off `WilsonHypercubic.bd`:

* `intra_links_mem` — every link of a spatial plaquette at time `t` lies in `sliceLinks τ t`;
* `inter_links_mem` — every link of a temporal plaquette at time `t` whose two directions differ
  lies in `sliceLinks τ t ∪ sliceLinks τ (t + 1) ∪ axisLinks τ t`.

The `t + 1` is `Fin n` addition and wraps, so the slabs are strung cyclically around the periodic
direction. `inter_links_diag_not_mem` is the control on the hypothesis: for the degenerate pair
`(τ, τ)` that conclusion fails, which is why `inter_links_mem` carries `q.1.1 ≠ q.1.2` and why
`interSliceAction_eq_nondeg` removes the diagonal.

`sliceLinks_axisLinks_cover` and `slab_pairwise_disjoint` give the matching partition of the link
set: the links are the union over `t : Fin n` of the pairwise disjoint blocks
`sliceLinks τ t ∪ axisLinks τ t`. `boltz_eq_slab_prod` factorises the Boltzmann weight, at a fixed
configuration, into a product over `t` of a slice factor and a slab factor.

## Part 3 — the temporal plaquette energy as the Wilson cross form

Under the hypothesis `hg : ∀ y, U (τ, y) = 1`, `hol_temporal_gauge_right` and `_left` collapse the
temporal plaquette holonomy to `V * W⁻¹` with `V` a spatial link of slice `t` and `W` the same
spatial link of slice `t + 1`, and `trace_hol_temporal_gauge_right` / `_left` identify its `Re tr`
with `CharacterExpansion.hsRe V W` through `CrossingIntegration.hsRe_coe_eq`. `hsRe` is the argument
`CharacterExpansion.wilson_kernel_nonneg` takes. Temporal gauge appears only as that explicit
hypothesis; no statement here derives it.

## Part 4 — the kernel

`transferKernel b s V W` is a real-valued kernel on the configurations of one slice, carrying a
diagonal factor `e^{-s/2}` at each argument and the aggregated cross form in between.
`transferKernel_symm` and `transferKernel_psd` give symmetry and positive semidefiniteness for
`0 ≤ b`, collected in `transferKernel_selfAdjoint_psd`; `transferKernel_pos` records pointwise
strict positivity. Because a slab weight is a product over all the spatial links of a slice,
`aggregate_kernel_nonneg` first transports `wilson_kernel_nonneg` to a whole finite family of
matrices through `OddLagSplit.hsRe_blockDiagonal_fin`.
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` shows `0 ≤ b` cannot be dropped.

The kernel is defined over an arbitrary finite index type `ι`, which the lattice supplies as
`sliceLinks τ t`, and the diagonal weight `s` is an arbitrary function of a slice configuration. No
statement in this file mentions an eigenvalue or a partition function.

Foundational footprint only (`#print axioms` throughout).
Build: `python code/lean_build.py build MassGap.SliceTransfer`.
-/

namespace MassGap.SliceTransfer

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.WilsonHypercubic MassGap.CharacterExpansion

/-! ## Part 0 — summing a finite type by the fibres of a map

The one combinatorial fact the decomposition runs on, proved from `Finset.sum_filter` and
`Finset.sum_comm`. -/

/-- Summing over the fibres of a map and then over the target recovers the sum over the source: for
`g : ι → κ` between finite types and `f : ι → M` into an additive commutative monoid,
`∑ k : κ, ∑ i ∈ univ.filter (fun i => g i = k), f i = ∑ i, f i`. `κ` carries `DecidableEq`, which is
what the filter needs.

DERIVED: no numeral appears in the statement. -/
theorem sum_by_fibre {ι κ M : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [AddCommMonoid M]
    (g : ι → κ) (f : ι → M) :
    ∑ k : κ, ∑ i ∈ Finset.univ.filter (fun i => g i = k), f i = ∑ i, f i := by
  classical
  calc ∑ k : κ, ∑ i ∈ Finset.univ.filter (fun i => g i = k), f i
      = ∑ k : κ, ∑ i : ι, (if g i = k then f i else 0) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_filter _ _)
    _ = ∑ i : ι, ∑ k : κ, (if g i = k then f i else 0) := Finset.sum_comm
    _ = ∑ i : ι, f i := Finset.sum_congr rfl (fun i _ => by simp)

/-! ## Part 1 — the time-slice geometry of the hypercubic lattice

A time direction is a choice `τ : Fin d` of one of the axes, and every definition below is relative
to it. No axis is privileged by the definitions themselves. -/

section Geometry

variable {d n : ℕ}

/-- A plaquette is temporal for the time direction `τ` when one of the two directions spanning its
plane is `τ`. Otherwise both directions are spatial and the plaquette lies inside one slice. This is
a `Prop`; `decidableIsTemporal` supplies the decidability the filters below need.

DERIVED: the `1` and `2` are anonymous-projection indices of `WilsonHypercubic.Plaq` — `q.1` is the
direction pair, `q.1.1` and `q.1.2` its first and second component. -/
def IsTemporal (τ : Fin d) (q : Plaq d n) : Prop := q.1.1 = τ ∨ q.1.2 = τ

instance decidableIsTemporal (τ : Fin d) (q : Plaq d n) : Decidable (IsTemporal τ q) := by
  unfold IsTemporal; infer_instance

/-- The spatial links of the slice at time `t`: direction other than `τ`, base site with
`τ`-coordinate `t`. These are the variables a slice-to-slice kernel acts on.

DERIVED: the `1` and `2` are projection indices of `LatticeGauge.Link` — `l.1` is the direction and
`l.2` the base site. -/
def sliceLinks (τ : Fin d) (t : Fin n) : Finset (Link d n) :=
  Finset.univ.filter (fun l => l.1 ≠ τ ∧ l.2 τ = t)

/-- The links leaving the slice at time `t` along the time direction: direction `τ`, base site
with `τ`-coordinate `t`. These are the links the temporal-gauge hypothesis of Part 3 sets to the
identity.

DERIVED: the `1` and `2` are projection indices of `LatticeGauge.Link` — `l.1` is the direction and
`l.2` the base site. -/
def axisLinks (τ : Fin d) (t : Fin n) : Finset (Link d n) :=
  Finset.univ.filter (fun l => l.1 = τ ∧ l.2 τ = t)

/-- The spatial plaquettes at time `t`: neither direction is `τ`, base site with `τ`-coordinate `t`.

DERIVED: the `2` is the projection index of `WilsonHypercubic.Plaq` — `q.2` is the base site. -/
def intraPlaq (τ : Fin d) (t : Fin n) : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => ¬ IsTemporal τ q ∧ q.2 τ = t)

/-- The temporal plaquettes of the slab based at time `t`: one direction is `τ`, base site with
`τ`-coordinate `t`. By `inter_links_mem` the ones whose two directions differ read slices `t` and
`t + 1`.

DERIVED: the `2` is the projection index of `WilsonHypercubic.Plaq` — `q.2` is the base site. The
filter is on `q.2 τ = t` and carries no other numeral. -/
def interPlaq (τ : Fin d) (t : Fin n) : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => IsTemporal τ q ∧ q.2 τ = t)

theorem mem_sliceLinks {τ : Fin d} {t : Fin n} {l : Link d n} :
    l ∈ sliceLinks τ t ↔ l.1 ≠ τ ∧ l.2 τ = t := by
  simp [sliceLinks]

theorem mem_axisLinks {τ : Fin d} {t : Fin n} {l : Link d n} :
    l ∈ axisLinks τ t ↔ l.1 = τ ∧ l.2 τ = t := by
  simp [axisLinks]

theorem mem_intraPlaq {τ : Fin d} {t : Fin n} {q : Plaq d n} :
    q ∈ intraPlaq τ t ↔ ¬ IsTemporal τ q ∧ q.2 τ = t := by
  simp [intraPlaq]

theorem mem_interPlaq {τ : Fin d} {t : Fin n} {q : Plaq d n} :
    q ∈ interPlaq τ t ↔ IsTemporal τ q ∧ q.2 τ = t := by
  simp [interPlaq]

/-- The spatial and the time-direction links of a slice are disjoint: `sliceLinks` requires a link's
direction to differ from `τ` and `axisLinks` requires it to equal `τ`.

DERIVED: no numeral appears in the statement. -/
theorem sliceLinks_disjoint_axisLinks (τ : Fin d) (t : Fin n) :
    Disjoint (sliceLinks τ t) (axisLinks τ t) := by
  rw [Finset.disjoint_left]
  intro l hl hl'
  exact (mem_sliceLinks.mp hl).1 (mem_axisLinks.mp hl').1

/-- The spatial and temporal plaquettes at a given time are disjoint, by the same argument on
`IsTemporal`.

DERIVED: no numeral appears in the statement. -/
theorem intraPlaq_disjoint_interPlaq (τ : Fin d) (t : Fin n) :
    Disjoint (intraPlaq τ t) (interPlaq τ t) := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  exact (mem_intraPlaq.mp hq).1 (mem_interPlaq.mp hq').1

/-! ### The link set partitions by slice

Every link of the lattice belongs to exactly one block `sliceLinks τ t ∪ axisLinks τ t`, indexed by
`t : Fin n`. -/

/-- The blocks cover the link set: the `biUnion` over `t : Fin n` of
`sliceLinks τ t ∪ axisLinks τ t` is `Finset.univ`. A link lands in the block at the `τ`-coordinate
of its own base site.

DERIVED: no numeral appears in the statement. -/
theorem sliceLinks_axisLinks_cover (τ : Fin d) :
    (Finset.univ : Finset (Fin n)).biUnion (fun t => sliceLinks τ t ∪ axisLinks τ t)
      = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun l => ?_)
  refine Finset.mem_biUnion.mpr ⟨l.2 τ, Finset.mem_univ _, ?_⟩
  by_cases h : l.1 = τ
  · exact Finset.mem_union_right _ (mem_axisLinks.mpr ⟨h, rfl⟩)
  · exact Finset.mem_union_left _ (mem_sliceLinks.mpr ⟨h, rfl⟩)

/-- Blocks at different times share no link, because a link's block is fixed by the `τ`-coordinate
of its base site. Stated for one pair `t ≠ t'` at a time, not as a `Set.PairwiseDisjoint`.

DERIVED: no numeral appears in the statement. -/
theorem slab_pairwise_disjoint (τ : Fin d) {t t' : Fin n} (h : t ≠ t') :
    Disjoint (sliceLinks τ t ∪ axisLinks τ t) (sliceLinks τ t' ∪ axisLinks τ t') := by
  rw [Finset.disjoint_left]
  intro l hl hl'
  have e : l.2 τ = t := by
    rcases Finset.mem_union.mp hl with h1 | h1
    · exact (mem_sliceLinks.mp h1).2
    · exact (mem_axisLinks.mp h1).2
  have e' : l.2 τ = t' := by
    rcases Finset.mem_union.mp hl' with h1 | h1
    · exact (mem_sliceLinks.mp h1).2
    · exact (mem_axisLinks.mp h1).2
  exact h (e ▸ e')

/-! ### The two shift facts

`shift μ x = Function.update x μ (x μ + 1)`. A step in a direction other than `τ` leaves the time
coordinate alone, and a step along `τ` advances it by one, cyclically, since `Fin n` addition wraps.
That wrap is what makes the slab structure a cycle rather than a chain.

Both lemmas below are stated for a general dimension `d`. `PowerTail.shift_apply_of_ne` is the
`d = 4` form of the first, and `ActionSplit.lv_shift_of_ne` states it wrapped in the level
function. -/

/-- A step in direction `μ` leaves every coordinate other than `μ` alone. Requires `NeZero n`, as
`shift` does.

DERIVED: no numeral appears in the statement. -/
theorem shift_apply_of_ne [NeZero n] {μ ν : Fin d} (h : ν ≠ μ) (x : Site d n) :
    shift μ x ν = x ν := by
  simp [shift, Function.update_of_ne h]

/-- A step in direction `μ` advances the `μ` coordinate by one. The addition is in `Fin n`, so it
wraps.

DERIVED: the `1` is one lattice step, added to the `μ` coordinate in `Fin n`. -/
theorem shift_apply_self [NeZero n] (μ : Fin d) (x : Site d n) :
    shift μ x μ = x μ + 1 := by
  simp [shift]

/-! ### Locality: which links each block of the split reads -/

/-- Every link of a plaquette whose direction pair avoids `τ` and whose base site sits at time `t`
is a spatial link at time `t`. Case analysis on the four letters of `WilsonHypercubic.bd q`, with
`shift_apply_of_ne` handling the two shifted letters.

This is what makes `intraSliceAction` an action of a slice rather than a label on a subsum.

DERIVED: the `1` is the projection index selecting the link out of the `(link, orientation)` pair
`lo`. -/
theorem intra_links_mem [NeZero n] {τ : Fin d} {t : Fin n} {q : Plaq d n}
    (hq : q ∈ intraPlaq τ t) (lo : Link d n × Bool) (hlo : lo ∈ bd q) :
    lo.1 ∈ sliceLinks τ t := by
  obtain ⟨hT, ht⟩ := mem_intraPlaq.mp hq
  have hμ : q.1.1 ≠ τ := fun h => hT (Or.inl h)
  have hν : q.1.2 ≠ τ := fun h => hT (Or.inr h)
  simp only [bd, List.mem_cons, List.not_mem_nil, or_false] at hlo
  rcases hlo with rfl | rfl | rfl | rfl
  · exact mem_sliceLinks.mpr ⟨hμ, ht⟩
  · refine mem_sliceLinks.mpr ⟨hν, ?_⟩
    show shift q.1.1 q.2 τ = t
    rw [shift_apply_of_ne (Ne.symm hμ)]; exact ht
  · refine mem_sliceLinks.mpr ⟨hμ, ?_⟩
    show shift q.1.2 q.2 τ = t
    rw [shift_apply_of_ne (Ne.symm hν)]; exact ht
  · exact mem_sliceLinks.mpr ⟨hν, ht⟩

/-- Every link of a plaquette with one direction `τ`, the other different from it, and base site at
time `t`, lies in `sliceLinks τ t ∪ sliceLinks τ (t + 1) ∪ axisLinks τ t`. Case analysis on the four
letters of `bd q` in each of the two orientations, using `shift_apply_self` and `shift_apply_of_ne`.

The `t + 1` is `Fin n` addition and therefore wraps, so the blocks are strung around the periodic
time direction.

The hypothesis `q.1.1 ≠ q.1.2` cannot be dropped: `inter_links_diag_not_mem` refutes the conclusion
for the degenerate pair.

DERIVED: the `1`s and the `2` in `q.1.1 ≠ q.1.2` and in `lo.1` are projection indices — the two
components of the plaquette's direction pair, and the link component of `lo`. The `1` in `t + 1` is
one time step in `Fin n`. -/
theorem inter_links_mem [NeZero n] {τ : Fin d} {t : Fin n} {q : Plaq d n}
    (hq : q ∈ interPlaq τ t) (hnd : q.1.1 ≠ q.1.2)
    (lo : Link d n × Bool) (hlo : lo ∈ bd q) :
    lo.1 ∈ sliceLinks τ t ∪ sliceLinks τ (t + 1) ∪ axisLinks τ t := by
  obtain ⟨hT, ht⟩ := mem_interPlaq.mp hq
  simp only [bd, List.mem_cons, List.not_mem_nil, or_false] at hlo
  rcases hT with hfst | hsnd
  · -- the first direction is `τ`; the second is spatial
    have hν : q.1.2 ≠ τ := fun h => hnd (by rw [hfst, h])
    rcases hlo with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hfst, ht⟩)
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ (mem_sliceLinks.mpr ⟨hν, ?_⟩))
      show shift q.1.1 q.2 τ = t + 1
      rw [hfst, shift_apply_self, ht]
    · refine Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hfst, ?_⟩)
      show shift q.1.2 q.2 τ = t
      rw [shift_apply_of_ne (Ne.symm hν)]; exact ht
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_sliceLinks.mpr ⟨hν, ht⟩))
  · -- the second direction is `τ`; the first is spatial
    have hμ : q.1.1 ≠ τ := fun h => hnd (by rw [h, hsnd])
    rcases hlo with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_sliceLinks.mpr ⟨hμ, ht⟩))
    · refine Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hsnd, ?_⟩)
      show shift q.1.1 q.2 τ = t
      rw [shift_apply_of_ne (Ne.symm hμ)]; exact ht
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ (mem_sliceLinks.mpr ⟨hμ, ?_⟩))
      show shift q.1.2 q.2 τ = t + 1
      rw [hsnd, shift_apply_self, ht]
    · exact Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hsnd, ht⟩)

/-- For the degenerate direction pair `(τ, τ)` the conclusion of `inter_links_mem` fails: at a base
site with `x τ = t`, the link `(τ, shift τ x)` is a time-direction link at time `t + 1` and lies in
none of the three blocks. The hypothesis `hne : t + 1 ≠ t` is explicit because it fails at extent
one.

The degenerate plaquette contributes nothing to the action (`ActionSplit.hol_diag_one`), which is
what `interSliceAction_eq_nondeg` uses to remove it.

DERIVED: both `1`s are one time step in `Fin n`, in `t + 1`. -/
theorem inter_links_diag_not_mem [NeZero n] {τ : Fin d} {t : Fin n} (x : Site d n)
    (hx : x τ = t) (hne : t + 1 ≠ t) :
    ((τ, shift τ x) : Link d n) ∉
      sliceLinks τ t ∪ sliceLinks τ (t + 1) ∪ axisLinks τ t := by
  intro h
  have hts : shift τ x τ = t + 1 := by rw [shift_apply_self, hx]
  rcases Finset.mem_union.mp h with h' | h'
  · rcases Finset.mem_union.mp h' with h'' | h''
    · exact (mem_sliceLinks.mp h'').1 rfl
    · exact (mem_sliceLinks.mp h'').1 rfl
  · have h2 : shift τ x τ = t := (mem_axisLinks.mp h').2
    rw [hts] at h2
    exact hne h2

/-- The degenerate plaquette `((τ, τ), x)` does lie in the temporal block at its own time:
`interPlaq` filters on `IsTemporal`, which `(τ, τ)` satisfies. So the split does not drop it.

DERIVED: no numeral appears in the statement. -/
theorem diag_mem_interPlaq (τ : Fin d) (x : Site d n) :
    (((τ, τ), x) : Plaq d n) ∈ interPlaq τ (x τ) :=
  mem_interPlaq.mpr ⟨Or.inl rfl, rfl⟩

/-- Whenever some direction `μ` differs from `τ`, the temporal block at time `x τ` contains a
plaquette whose two directions differ; the witness is `((μ, τ), x)`. So the hypothesis of
`inter_links_mem` is satisfiable.

DERIVED: the `1`s and the `2` in `q.1.1 ≠ q.1.2` are projection indices, the two components of the
plaquette's direction pair. -/
theorem exists_nondeg_interPlaq {τ μ : Fin d} (hμ : μ ≠ τ) (x : Site d n) :
    ∃ q ∈ interPlaq τ (x τ), q.1.1 ≠ q.1.2 :=
  ⟨((μ, τ), x), mem_interPlaq.mpr ⟨Or.inr rfl, rfl⟩, hμ⟩

/-- At dimension one the only direction is `τ`, so every plaquette is temporal and `intraPlaq` is
empty: the split degenerates to the temporal block alone.

DERIVED: the `1` in `Fin 1` and the `1` in `d := 1` are the same lattice dimension, fixed to one for
this statement. -/
theorem intraPlaq_eq_empty_of_dim_one (τ : Fin 1) (t : Fin n) :
    intraPlaq (d := 1) (n := n) τ t = ∅ := by
  ext q
  constructor
  · intro hq
    exact absurd (Or.inl (Subsingleton.elim q.1.1 τ) : IsTemporal τ q) (mem_intraPlaq.mp hq).1
  · intro hq
    exact absurd hq (Finset.notMem_empty q)

end Geometry

/-! ## Part 2 — the action decomposition -/

section Decomposition

variable {d n : ℕ}

theorem filter_time_filter_temporal (τ : Fin d) (t : Fin n) :
    (Finset.univ.filter (fun q : Plaq d n => q.2 τ = t)).filter (IsTemporal τ)
      = interPlaq τ t := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, interPlaq]
  exact and_comm

theorem filter_time_filter_not_temporal (τ : Fin d) (t : Fin n) :
    (Finset.univ.filter (fun q : Plaq d n => q.2 τ = t)).filter (fun q => ¬ IsTemporal τ q)
      = intraPlaq τ t := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, intraPlaq]
  exact and_comm

/-- The plaquette set splits by time slice: for any real-valued plaquette weight `f`,

    ∑_q f q = ∑_t ( ∑_{q ∈ intraPlaq τ t} f q + ∑_{q ∈ interPlaq τ t} f q ).

Every plaquette is counted once — its time is the `τ`-coordinate of its base site, and it is
temporal or spatial according to its direction pair. From `sum_by_fibre` along `fun q => q.2 τ`
together with `Finset.sum_filter_add_sum_filter_not` and the two `filter_time_filter_*` lemmas. The
weight is valued in `ℝ`; nothing about the Wilson action enters yet.

DERIVED: no numeral appears in the statement. -/
theorem plaqSum_eq_slice_sum (τ : Fin d) (f : Plaq d n → ℝ) :
    ∑ q : Plaq d n, f q
      = ∑ t : Fin n, ((∑ q ∈ intraPlaq τ t, f q) + ∑ q ∈ interPlaq τ t, f q) := by
  have h1 : ∀ t : Fin n,
      (∑ q ∈ intraPlaq τ t, f q) + ∑ q ∈ interPlaq τ t, f q
        = ∑ q ∈ Finset.univ.filter (fun q : Plaq d n => q.2 τ = t), f q := by
    intro t
    rw [← filter_time_filter_temporal τ t, ← filter_time_filter_not_temporal τ t, add_comm]
    exact Finset.sum_filter_add_sum_filter_not _ _ f
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => h1 t)]
  exact (sum_by_fibre (fun q : Plaq d n => q.2 τ) f).symm

variable {N : ℕ}

/-- The intra-slice action at time `t`: the Wilson energy summed over the plaquettes lying inside
the slice. By `intra_links_mem` it reads only the links in `sliceLinks τ t`.

DERIVED: no numeral appears in the statement. -/
noncomputable def intraSliceAction [NeZero n] (τ : Fin d) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ intraPlaq τ t, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- The inter-slice action of the slab based at time `t`: the Wilson energy summed over
`interPlaq τ t`, the plaquettes with one direction along `τ` and base site at time `t`. By
`inter_links_mem` the part with distinct directions reads only slices `t` and `t + 1` and the
time-direction links between them.

DERIVED: no numeral appears in the statement. -/
noncomputable def interSliceAction [NeZero n] (τ : Fin d) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ interPlaq τ t, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- The `action` field of `WilsonHypercubic.sysWilson N d n` is the plaquette sum of the Wilson
density of the ordered loop holonomy, by `rfl`. Stated separately so the decomposition below does
not unfold `System` inline.

DERIVED: no numeral appears in the statement. -/
theorem sysWilson_action (N d n : ℕ) [NeZero n] (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := rfl

/-- The Wilson action of the periodic hypercubic lattice splits by time slice:

    (sysWilson N d n).action U = ∑ t : Fin n, (intraSliceAction τ t U + interSliceAction τ t U).

`sysWilson_action` followed by `plaqSum_eq_slice_sum`. The time direction `τ` is the caller's, and
the index set is `Fin n`, the lattice's own extent in that direction.

DERIVED: no numeral appears in the statement. -/
theorem action_eq_slice_sum [NeZero n] (τ : Fin d) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = ∑ t : Fin n, (intraSliceAction τ t U + interSliceAction τ t U) := by
  rw [sysWilson_action]
  simp only [intraSliceAction, interSliceAction]
  exact plaqSum_eq_slice_sum τ _

/-- The Boltzmann weight factorises over slices: `Real.exp (-β * S U)` is the product over
`t : Fin n` of `Real.exp (-β * intraSliceAction τ t U) * Real.exp (-β * interSliceAction τ t U)`.
From `action_eq_slice_sum`, `Finset.mul_sum` and `Real.exp_sum`.

This is an identity of real numbers at a fixed configuration; it does not regroup the product
measure over links.

DERIVED: no numeral appears in the statement. -/
theorem boltz_eq_slab_prod [NeZero n] (τ : Fin d) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    Real.exp (-β * (sysWilson N d n).action U)
      = ∏ t : Fin n, (Real.exp (-β * intraSliceAction τ t U)
          * Real.exp (-β * interSliceAction τ t U)) := by
  rw [action_eq_slice_sum τ, Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_congr rfl (fun t _ => by rw [mul_add, Real.exp_add])

/-- The inter-slice action may be summed over the temporal plaquettes whose two directions differ
alone: a degenerate plaquette has identity holonomy (`ActionSplit.hol_diag_one`) and so contributes
`wilsonDensity 1`, which is zero by `wilsonDensity_one` — the step that needs `N ≠ 0`. By
`inter_links_mem` the remaining terms read only slices `t`, `t + 1` and the time-direction links
between them.

DERIVED: the `0` is the rank condition `N ≠ 0`; the `1`s and the `2` in `q.1.1 ≠ q.1.2` are
projection indices, the two components of the plaquette's direction pair. -/
theorem interSliceAction_eq_nondeg [NeZero n] (hN : N ≠ 0) (τ : Fin d) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) :
    interSliceAction τ t U
      = ∑ q ∈ (interPlaq τ t).filter (fun q => q.1.1 ≠ q.1.2),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by
  unfold interSliceAction
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro q hq hq'
  obtain ⟨⟨a, b⟩, x⟩ := q
  have hd : a = b := by
    by_contra h
    exact hq' (Finset.mem_filter.mpr ⟨hq, h⟩)
  subst hd
  rw [ActionSplit.hol_diag_one, wilsonDensity_one hN]

end Decomposition

/-! ## Part 3 — the temporal plaquette energy as the Wilson cross form

With the links along `τ` set to the identity, a temporal plaquette's ordered loop collapses to
`V * W⁻¹`, with `V` a spatial link of slice `t` and `W` the same spatial link of slice `t + 1`. Its
`Re tr` is `hsRe V W` by `CrossingIntegration.hsRe_coe_eq`, and `hsRe` is the argument
`CharacterExpansion.wilson_kernel_nonneg` takes.

Temporal gauge appears in every statement below as the explicit hypothesis
`hg : ∀ y, U (τ, y) = 1`. Nothing here states that the Gibbs measure may be computed in that
gauge. -/

section TemporalGauge

variable {d n N : ℕ}

/-- The Wilson density of `V * W⁻¹` in terms of the cross form:
`wilsonDensity (V * W⁻¹) = 1 - (1 / N) * hsRe V W`, by `CrossingIntegration.hsRe_coe_eq`.

DERIVED: the first `1` is the value the normalised trace is subtracted from; the second is the
numerator of the character normalisation `1 / N`. -/
theorem wilsonDensity_mul_inv (V W : MassGap.SUN.SU N) :
    wilsonDensity (V * W⁻¹)
      = 1 - (1 / (N : ℝ)) * hsRe (V : Matrix (Fin N) (Fin N) ℂ)
          (W : Matrix (Fin N) (Fin N) ℂ) := by
  unfold wilsonDensity
  rw [CrossingIntegration.hsRe_coe_eq]

/-- With every `τ`-link at the identity, the holonomy of the plaquette `((μ, τ), x)` is
`U (μ, x) * (U (μ, shift τ x))⁻¹`: `Reflect.hol_bd` expands the ordered loop and the two `τ` factors
drop out.

DERIVED: the `1` is the group identity, the value the hypothesis `hg` assigns to every `τ`-link. -/
theorem hol_temporal_gauge_right [NeZero n] {τ μ : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    wilsonHol (bd (d := d) (n := n)) ((μ, τ), x) U = U (μ, x) * (U (μ, shift τ x))⁻¹ := by
  rw [Reflect.hol_bd]
  simp [hg]

/-- The same for the plane orientation `((τ, ν), x)`: the holonomy is
`U (ν, shift τ x) * (U (ν, x))⁻¹`, the same two spatial links in the opposite order.

DERIVED: the `1` is the group identity, the value the hypothesis `hg` assigns to every `τ`-link. -/
theorem hol_temporal_gauge_left [NeZero n] {τ ν : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    wilsonHol (bd (d := d) (n := n)) ((τ, ν), x) U = U (ν, shift τ x) * (U (ν, x))⁻¹ := by
  rw [Reflect.hol_bd]
  simp [hg]

/-- Under the same hypothesis, the real part of the trace of a temporal plaquette holonomy is the
cross form between a spatial link of slice `t` and the same spatial link one step along `τ`:

    Re tr (hol ((μ, τ), x) U) = hsRe (U (μ, x)) (U (μ, shift τ x)).

`hol_temporal_gauge_right` followed by `CrossingIntegration.hsRe_coe_eq`. `hsRe` is the argument
`CharacterExpansion.wilson_kernel_nonneg` takes.

DERIVED: the `1` is the group identity in the hypothesis `hg`; the conclusion carries no
numeral. -/
theorem trace_hol_temporal_gauge_right [NeZero n] {τ μ : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) ((μ, τ), x) U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe ((U (μ, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          ((U (μ, shift τ x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hol_temporal_gauge_right x U hg, CrossingIntegration.hsRe_coe_eq]

/-- The same for the opposite plane orientation: the two arguments of `hsRe` swap, and `hsRe_comm`
says the value does not. An ordered-pair plaquette type therefore counts each plane twice with the
same energy, which is `WilsonHypercubic.Plaq`'s convention rather than anything this file imposes.

DERIVED: the `1` is the group identity in the hypothesis `hg`; the conclusion carries no
numeral. -/
theorem trace_hol_temporal_gauge_left [NeZero n] {τ ν : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) ((τ, ν), x) U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe ((U (ν, shift τ x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          ((U (ν, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hol_temporal_gauge_left x U hg, CrossingIntegration.hsRe_coe_eq]

/-- The slab energy with the trace separated out: the plaquette count `(interPlaq τ t).card` minus
`1 / N` times the summed `Re tr` over that block. Unfolding `wilsonDensity` and collecting the
constant term. No gauge hypothesis is needed.

DERIVED: the `1` is the numerator of the character normalisation `1 / N`. -/
theorem interSliceAction_eq_card_sub [NeZero n] (τ : Fin d) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) :
    interSliceAction τ t U
      = ((interPlaq τ t).card : ℝ)
        - (1 / (N : ℝ)) * ∑ q ∈ interPlaq τ t,
            (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := by
  unfold interSliceAction wilsonDensity
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]

/-- The slab Boltzmann factor is a configuration-independent constant times an exponential of the
aggregated trace:

    Real.exp (-β * interSliceAction τ t U)
      = Real.exp (-β * (interPlaq τ t).card) * Real.exp ((β / N) * ∑_q Re tr (hol q U)).

From `interSliceAction_eq_card_sub` and `Real.exp_add`. Under the temporal-gauge hypothesis the sum
in the second exponent is a sum of cross forms between consecutive slices, by
`trace_hol_temporal_gauge_right`; that hypothesis is not required for this identity.

DERIVED: no numeral appears in the statement. The coefficient in the second exponent is `β / N`, the
coupling over the rank; the `1 / N` of `wilsonDensity` has already been absorbed into it by
`interSliceAction_eq_card_sub`. -/
theorem boltz_inter_eq [NeZero n] (τ : Fin d) (t : Fin n) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    Real.exp (-β * interSliceAction τ t U)
      = Real.exp (-β * ((interPlaq τ t).card : ℝ))
        * Real.exp ((β / (N : ℝ)) * ∑ q ∈ interPlaq τ t,
            (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re) := by
  rw [interSliceAction_eq_card_sub, ← Real.exp_add]
  congr 1
  ring

end TemporalGauge

/-! ## Part 4 — the slice-to-slice transfer kernel

A slice configuration is a group element on each of the slice's spatial links — `ι → SU N` for a
finite index type `ι`, which the lattice supplies as `sliceLinks τ t`. The kernel carries a diagonal
factor `e^{-s/2}` at each of its two arguments, which is what makes it symmetric, and the aggregated
cross form in between.

`s` is an arbitrary function of a slice configuration. On the lattice it is `intraSliceAction τ t`,
which by `intra_links_mem` reads only the slice; no statement below assumes that. -/

section Kernel

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `hsRe` is symmetric in its two matrix arguments, from `hsRe_eq_sum`, which presents it as a sum
of products of real coordinates.

DERIVED: no numeral appears in the statement. -/
theorem hsRe_comm (A B : Matrix (Fin N) (Fin N) ℂ) : hsRe A B = hsRe B A := by
  rw [hsRe_eq_sum, hsRe_eq_sum]
  exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)

/-- The aggregated Wilson cross form between two slice configurations: the sum over the index type
of `hsRe` between a link's value in one configuration and in the other. By
`trace_hol_temporal_gauge_right` this is what a slab energy is built from.

DERIVED: no numeral appears in the statement. -/
noncomputable def sliceForm (V W : ι → MassGap.SUN.SU N) : ℝ :=
  ∑ l : ι, hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((W l : Matrix (Fin N) (Fin N) ℂ))

omit [DecidableEq ι] in
theorem sliceForm_comm (V W : ι → MassGap.SUN.SU N) : sliceForm V W = sliceForm W V :=
  Finset.sum_congr rfl (fun _ _ => hsRe_comm _ _)

/-- The slice-to-slice transfer kernel

    T(V, W) = e^{-s(V)/2} * e^{b * sliceForm V W} * e^{-s(W)/2}

on the configurations of one slice, valued in `ℝ`. Both `b` and `s` are the caller's: on the lattice
`b` is `β / N` and `s` is the intra-slice action. The diagonal factor is split evenly between the
two arguments, which is what `transferKernel_symm` and `transferKernel_psd` use.

DERIVED: both `2`s are the divisor splitting `s` evenly between the kernel's two arguments. -/
noncomputable def transferKernel (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) : ℝ :=
  Real.exp (-(s V) / 2) * Real.exp (b * sliceForm V W) * Real.exp (-(s W) / 2)

omit [DecidableEq ι] in
/-- `T(V, W) = T(W, V)`, for every `b` and every `s`. From `sliceForm_comm` and the even split of
the diagonal factor.

DERIVED: no numeral appears in the statement. -/
theorem transferKernel_symm (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) :
    transferKernel b s V W = transferKernel b s W V := by
  unfold transferKernel
  rw [sliceForm_comm]
  ring

omit [DecidableEq ι] in
/-- `0 < T(V, W)` at every pair of slice configurations, for every `b` and every `s`: the kernel is
a product of exponentials. This is positivity of the values, a different statement from the positive
semidefiniteness of `transferKernel_psd`.

DERIVED: the `0` is the lower bound in the conclusion. -/
theorem transferKernel_pos (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) :
    0 < transferKernel b s V W := by
  unfold transferKernel
  positivity

/-- The aggregated Wilson weight is a positive-semidefinite kernel for `0 ≤ b`, over a whole finite
family of matrices at once rather than over one matrix:

    0 ≤ ∑ᵢ ∑ⱼ zᵢ zⱼ exp (b * ∑_l hsRe (A i l) (A j l)).

`CharacterExpansion.wilson_kernel_nonneg` applied at the block diagonal over `Fin N × ι`,
transported by `OddLagSplit.hsRe_blockDiagonal_fin`, which says `hsRe` of a direct sum is the sum of
the `hsRe`s. The family is indexed by `Fin m` and the weights `z` are real. This is the step that
carries a slab weight, which is a product over the slice's links rather than a single plaquette.

`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` shows `0 ≤ b` cannot be dropped: it is already
sharp for a single link, hence for a family containing one.

DERIVED: the first `0` is the sign condition `0 ≤ b` on the coupling; the second is the lower bound
in the conclusion, which is positive semidefiniteness. -/
theorem aggregate_kernel_nonneg {b : ℝ} (hb : 0 ≤ b) {m : ℕ}
    (A : Fin m → ι → Matrix (Fin N) (Fin N) ℂ) (z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * Real.exp (b * ∑ l : ι, hsRe (A i l) (A j l)) := by
  have h := wilson_kernel_nonneg hb
    (fun i => (Matrix.blockDiagonal (A i)).submatrix
      (Fintype.equivFin (Fin N × ι)).symm (Fintype.equivFin (Fin N × ι)).symm) z
  simpa only [OddLagSplit.hsRe_blockDiagonal_fin] using h

/-- The transfer kernel is positive-semidefinite for `0 ≤ b`:

    0 ≤ ∑ᵢ ∑ⱼ zᵢ zⱼ T(Vᵢ, Vⱼ)

for every finite family `V : Fin m → (ι → SU N)` of slice configurations and every real weight
vector `z`. `aggregate_kernel_nonneg` with the diagonal factor `e^{-s/2}` absorbed into the weights,
which is why it had to be split evenly between the two arguments. The only hypothesis is the sign of
`b`; `s` is unrestricted.

DERIVED: the first `0` is the sign condition `0 ≤ b`; the second is the lower bound in the
conclusion. -/
theorem transferKernel_psd {b : ℝ} (hb : 0 ≤ b) (s : (ι → MassGap.SUN.SU N) → ℝ) {m : ℕ}
    (V : Fin m → (ι → MassGap.SUN.SU N)) (z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j) := by
  have hrw : ∀ i j : Fin m, z i * z j * transferKernel b s (V i) (V j)
      = (z i * Real.exp (-(s (V i)) / 2)) * (z j * Real.exp (-(s (V j)) / 2))
        * Real.exp (b * ∑ l : ι, hsRe ((V i l : Matrix (Fin N) (Fin N) ℂ))
            ((V j l : Matrix (Fin N) (Fin N) ℂ))) := by
    intro i j
    unfold transferKernel sliceForm
    ring
  calc (0 : ℝ)
      ≤ ∑ i, ∑ j, (z i * Real.exp (-(s (V i)) / 2)) * (z j * Real.exp (-(s (V j)) / 2))
          * Real.exp (b * ∑ l : ι, hsRe ((V i l : Matrix (Fin N) (Fin N) ℂ))
              ((V j l : Matrix (Fin N) (Fin N) ℂ))) :=
        aggregate_kernel_nonneg hb
          (fun i l => ((V i l : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ))
          (fun i => z i * Real.exp (-(s (V i)) / 2))
    _ = ∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => (hrw i j).symm))

/-- The two properties as one conjunction: for `0 ≤ b` and any `s`, `T` is symmetric in its two
arguments and positive-semidefinite on every finite family of slice configurations. Packaged from
`transferKernel_symm` and `transferKernel_psd`.

DERIVED: the first `0` is the sign condition `0 ≤ b`; the second is the lower bound in the second
conjunct. -/
theorem transferKernel_selfAdjoint_psd {b : ℝ} (hb : 0 ≤ b) (s : (ι → MassGap.SUN.SU N) → ℝ) :
    (∀ V W : ι → MassGap.SUN.SU N, transferKernel b s V W = transferKernel b s W V)
      ∧ (∀ (m : ℕ) (V : Fin m → (ι → MassGap.SUN.SU N)) (z : Fin m → ℝ),
          0 ≤ ∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j)) :=
  ⟨transferKernel_symm b s, fun _ V z => transferKernel_psd hb s V z⟩

end Kernel

/-! ## Axiom footprints -/

#print axioms sum_by_fibre
#print axioms IsTemporal
#print axioms decidableIsTemporal
#print axioms sliceLinks
#print axioms axisLinks
#print axioms intraPlaq
#print axioms interPlaq
#print axioms mem_sliceLinks
#print axioms mem_axisLinks
#print axioms mem_intraPlaq
#print axioms mem_interPlaq
#print axioms sliceLinks_disjoint_axisLinks
#print axioms intraPlaq_disjoint_interPlaq
#print axioms sliceLinks_axisLinks_cover
#print axioms slab_pairwise_disjoint
#print axioms shift_apply_of_ne
#print axioms shift_apply_self
#print axioms intra_links_mem
#print axioms inter_links_mem
#print axioms inter_links_diag_not_mem
#print axioms diag_mem_interPlaq
#print axioms exists_nondeg_interPlaq
#print axioms intraPlaq_eq_empty_of_dim_one
#print axioms filter_time_filter_temporal
#print axioms filter_time_filter_not_temporal
#print axioms plaqSum_eq_slice_sum
#print axioms intraSliceAction
#print axioms interSliceAction
#print axioms sysWilson_action
#print axioms action_eq_slice_sum
#print axioms boltz_eq_slab_prod
#print axioms interSliceAction_eq_nondeg
#print axioms wilsonDensity_mul_inv
#print axioms hol_temporal_gauge_right
#print axioms hol_temporal_gauge_left
#print axioms trace_hol_temporal_gauge_right
#print axioms trace_hol_temporal_gauge_left
#print axioms interSliceAction_eq_card_sub
#print axioms boltz_inter_eq
#print axioms hsRe_comm
#print axioms sliceForm
#print axioms sliceForm_comm
#print axioms transferKernel
#print axioms transferKernel_symm
#print axioms transferKernel_pos
#print axioms aggregate_kernel_nonneg
#print axioms transferKernel_psd
#print axioms transferKernel_selfAdjoint_psd

end MassGap.SliceTransfer
