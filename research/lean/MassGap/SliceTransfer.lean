import MassGap.OddLagSplit

/-!
# MassGap.SliceTransfer — the Wilson action split by time slice, and the slice-to-slice kernel

`HalfLineTransfer` closes the route that reads the lattice SHIFT as a transfer operator: the shift
has finite order (`shiftObs_pow_period`), so any `TransferData` built on it has a zero vacuum
complement and can never deliver a subdominant eigenvalue below one. `WilsonTransfer`'s
`shift_not_stable_on_slab` says the same thing from the other side — one lattice step carries an axis
link out of the slab, so the slab algebra is not shift-stable and `TransferData.T_contract` is not
available there.

The operator the Osterwalder–Seiler construction actually uses is a different object on a different
space: a SLICE-TO-SLICE KERNEL `T(V, W)` acting on functions of the spatial links of ONE time slice.
This file builds the geometry and the kernel. It does not extract a spectrum.

## What is proved here

**The Wilson action splits by time slice, on the real lattice.** `plaqSum_eq_slice_sum` /
`action_eq_slice_sum`: for any choice of time direction `τ`,

    S(U) = ∑_{t : Fin n} ( intraSliceAction τ t U + interSliceAction τ t U ),

a `Finset` partition of `WilsonHypercubic.Plaq` by the `τ`-coordinate of a plaquette's base site and
by whether its direction pair contains `τ`. It is bookkeeping and it is written as bookkeeping: the
only inputs are `Finset.sum_filter`, `Finset.sum_comm` and `Finset.sum_filter_add_sum_filter_not`.

`ActionSplit` and `OddLagSplit` already split the plaquette set — by position relative to a
REFLECTION PLANE (`blkS`/`blkT`/`blkR`, `oplqCross`/`oplqPlus`/`oplqMinus`). That is a two-sided cut
for reflection positivity, not a per-slice decomposition, and the block whose links two consecutive
slices share is not among its pieces. Nothing in the tree decomposed the action by time slice.

**The split really is by time — the locality lemmas.** A partition of a sum carries nothing on its
own; what makes it a slice decomposition is WHICH LINKS each block reads, and that is read off `bd`:

* `intra_links_mem` — every link of a spatial plaquette at time `t` lies in `sliceLinks τ t`;
* `inter_links_mem` — every link of a NON-DEGENERATE temporal plaquette at time `t` lies in
  `sliceLinks τ t ∪ sliceLinks τ (t+1) ∪ axisLinks τ t`.

The `t+1` is `Fin n` addition, so it wraps: the slabs are strung around the periodic direction, and
that cycle is the combinatorial shape of "`Z` is a trace". `inter_links_diag_not_mem` is the control
on the hypothesis: for the degenerate pair `(τ, τ)` the claim is FALSE — that plaquette reads an axis
link at time `t+1` — which is why `inter_links_mem` carries `q.1.1 ≠ q.1.2` and why
`interSliceAction_eq_nondeg` removes the diagonal before the slab is a two-slice object.
`OddLagSplit.odd_degenerate_axis_plaquette_straddles` is the same obstruction at a reflection plane.

**The link set partitions by slice.** `sliceLinks_axisLinks_cover` and `slab_pairwise_disjoint`: the
links of the lattice are the disjoint union over `t : Fin n` of `sliceLinks τ t ∪ axisLinks τ t`.
That is the index partition the missing Fubini step would consume.

**The temporal plaquette energy IS the Wilson cross form.** `trace_hol_temporal_gauge_right` /
`_left`: in temporal gauge the holonomy of a plaquette spanning `(μ, τ)` collapses to
`V_μ(x) · W_μ(x)⁻¹` with `V` on slice `t` and `W` on slice `t+1`, and its `Re tr` is exactly
`CharacterExpansion.hsRe V W` (via `CrossingIntegration.hsRe_coe_eq`). That identity is what points
the kernel positivity at the lattice rather than at a formal object of the right shape: `hsRe` is the
argument `wilson_kernel_nonneg` takes.

**The aggregated kernel is symmetric and positive-semidefinite.** The slab weight is a product over
ALL the spatial links of a slice, so the single-matrix kernel does not reach it directly.
`OddLagSplit.hsRe_blockDiagonal_fin` is the step that closes the gap — `hsRe` of a direct sum is the
sum of the `hsRe`s — so the aggregated weight `exp (b · ∑_l hsRe (V l) (W l))` IS a single-matrix
Wilson weight, at the direct sum, and `wilson_kernel_nonneg` applies verbatim
(`aggregate_kernel_nonneg`). `transferKernel_symm` and `transferKernel_psd` are the two properties
that make `T` a transfer matrix rather than a formal object; `transferKernel_pos` records that it is
also pointwise strictly positive.

## What is NOT proved here, named exactly

**`Z = Tr(Tⁿ)` is not proved.** Three ingredients, in three states:

* the CYCLE structure — the slabs are indexed by `Fin n` and the `t`-th couples slices `t` and `t+1`
  — is proved (`inter_links_mem`, `plaqSum_eq_slice_sum`);
* the FACTORISATION of the Boltzmann weight into a product of slice and slab weights is proved
  (`boltz_eq_slab_prod`);
* the FUBINI step — regrouping `Measure.pi` over `Link d n` as an iterated integral along the
  partition `sliceLinks_axisLinks_cover`, so the product of slab weights becomes an iterated kernel
  composition — is NOT. `ActionSplit.join3`/`integral_three_block` do this for a THREE-block split;
  the `n`-block version indexed by `Fin n` is not in the tree and is not here.

Until that step exists, `T` is a symmetric positive kernel on slice configurations and nothing
identifies its powers with the finite-volume partition function.

**Temporal gauge is a HYPOTHESIS, not a theorem.** Every statement about the collapsed temporal
holonomy carries `hg : ∀ y, U (τ, y) = 1` explicitly. That the Gibbs measure may be computed in that
gauge is a change of variables on the axis links, and it is not proved here. The tree has no
temporal-gauge statement of any kind.

**No spectrum.** Nothing here bounds an eigenvalue, and in particular nothing here approaches the
`λ_max < 0.13647` that B5 asks for.

Foundational footprint only (`#print axioms` throughout).
Build: `python code/lean_build.py build MassGap.SliceTransfer`.
-/

namespace MassGap.SliceTransfer

open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.WilsonHypercubic MassGap.CharacterExpansion

/-! ## Part 0 — summing a finite type by the fibres of a map

The one combinatorial fact the decomposition runs on, proved from `Finset.sum_filter` and
`Finset.sum_comm`. -/

/-- **Summing by fibres.** For any map `g` into a finite type, summing over the fibres of `g` and
then over the target recovers the sum over the source.

DERIVED: no numeral. -/
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

A time direction `τ` is a choice of one of the `d` axes. Everything below is relative to it: nothing
privileges a particular axis, and `LatticeGauge.expect_invariant` is what says the choice does not
move a correlation. -/

section Geometry

variable {d n : ℕ}

/-- A plaquette is **temporal** for the time direction `τ` when one of the two directions spanning
its plane is `τ`. Otherwise both directions are spatial and the plaquette lies inside one slice.

DERIVED: the `2` directions of a plane are `WilsonHypercubic.Plaq`'s, not a choice here. -/
def IsTemporal (τ : Fin d) (q : Plaq d n) : Prop := q.1.1 = τ ∨ q.1.2 = τ

instance decidableIsTemporal (τ : Fin d) (q : Plaq d n) : Decidable (IsTemporal τ q) := by
  unfold IsTemporal; infer_instance

/-- The **spatial links of the slice at time `t`**: direction not `τ`, base site at `τ`-coordinate
`t`. These are the variables a slice-to-slice kernel acts on. -/
def sliceLinks (τ : Fin d) (t : Fin n) : Finset (Link d n) :=
  Finset.univ.filter (fun l => l.1 ≠ τ ∧ l.2 τ = t)

/-- The **temporal links leaving the slice at time `t`**: direction `τ`, base site at time `t`.
These are the links temporal gauge sets to the identity. -/
def axisLinks (τ : Fin d) (t : Fin n) : Finset (Link d n) :=
  Finset.univ.filter (fun l => l.1 = τ ∧ l.2 τ = t)

/-- The **spatial plaquettes at time `t`**: neither direction is `τ`, base site at time `t`. -/
def intraPlaq (τ : Fin d) (t : Fin n) : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => ¬ IsTemporal τ q ∧ q.2 τ = t)

/-- The **temporal plaquettes of the slab from `t` to `t+1`**: one direction is `τ`, base site at
time `t`. -/
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

/-- Spatial and temporal links of a slice are disjoint — a link has one direction. -/
theorem sliceLinks_disjoint_axisLinks (τ : Fin d) (t : Fin n) :
    Disjoint (sliceLinks τ t) (axisLinks τ t) := by
  rw [Finset.disjoint_left]
  intro l hl hl'
  exact (mem_sliceLinks.mp hl).1 (mem_axisLinks.mp hl').1

/-- Spatial and temporal plaquettes at a given time are disjoint. -/
theorem intraPlaq_disjoint_interPlaq (τ : Fin d) (t : Fin n) :
    Disjoint (intraPlaq τ t) (interPlaq τ t) := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  exact (mem_intraPlaq.mp hq).1 (mem_interPlaq.mp hq').1

/-! ### The link set partitions by slice

This is the index partition the missing Fubini step would consume: every link of the lattice belongs
to exactly one `sliceLinks τ t ∪ axisLinks τ t`, indexed by `t : Fin n`. -/

/-- **THE SLABS COVER THE LINKS.** Every link lies in the slice-or-axis block at its own time. -/
theorem sliceLinks_axisLinks_cover (τ : Fin d) :
    (Finset.univ : Finset (Fin n)).biUnion (fun t => sliceLinks τ t ∪ axisLinks τ t)
      = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun l => ?_)
  refine Finset.mem_biUnion.mpr ⟨l.2 τ, Finset.mem_univ _, ?_⟩
  by_cases h : l.1 = τ
  · exact Finset.mem_union_right _ (mem_axisLinks.mpr ⟨h, rfl⟩)
  · exact Finset.mem_union_left _ (mem_sliceLinks.mpr ⟨h, rfl⟩)

/-- **THE SLABS ARE DISJOINT.** Blocks at different times share no link, because a link's block is
fixed by the `τ`-coordinate of its base site. -/
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

`shift μ x = Function.update x μ (x μ + 1)`. A step in a direction other than `τ` does not move the
time coordinate, and a step in `τ` advances it by one — cyclically, because `Fin n` addition wraps.
That wrap is what makes the slab structure a CYCLE rather than a chain.

`PowerTail.shift_apply_of_ne` states the first of these for `d = 4` only, and
`ActionSplit.lv_shift_of_ne` states it wrapped in the level function. The raw dimension-general form
is not in the tree. -/

/-- A step in direction `μ` leaves every other coordinate alone. -/
theorem shift_apply_of_ne [NeZero n] {μ ν : Fin d} (h : ν ≠ μ) (x : Site d n) :
    shift μ x ν = x ν := by
  simp [shift, Function.update_of_ne h]

/-- A step in direction `μ` advances the `μ` coordinate by one, cyclically. -/
theorem shift_apply_self [NeZero n] (μ : Fin d) (x : Site d n) :
    shift μ x μ = x μ + 1 := by
  simp [shift]

/-! ### Locality: which links each block of the split reads -/

/-- **A SPATIAL PLAQUETTE READS ONE SLICE.** Every link of a plaquette whose direction pair avoids
`τ` and whose base site sits at time `t` is a spatial link at time `t`.

This is what makes `intraSliceAction` an action OF A SLICE rather than a label on a subsum. -/
theorem intra_links_mem [NeZero n] {τ : Fin d} {t : Fin n} {q : Plaq d n}
    (hq : q ∈ intraPlaq τ t) (lo : Link d n × Bool) (hlo : lo ∈ bd q) :
    lo.1 ∈ sliceLinks τ t := by
  obtain ⟨hT, ht⟩ := mem_intraPlaq.mp hq
  have hμ : q.1.1 ≠ τ := fun h => hT (Or.inl h)
  have hν : q.1.2 ≠ τ := fun h => hT (Or.inr h)
  simp only [bd, List.mem_cons, List.not_mem_nil, or_false] at hlo
  rcases hlo with rfl | rfl | rfl | rfl
  · exact mem_sliceLinks.mpr ⟨hμ, ht⟩
  · exact mem_sliceLinks.mpr ⟨hν, by rw [shift_apply_of_ne (Ne.symm hμ)]; exact ht⟩
  · exact mem_sliceLinks.mpr ⟨hμ, by rw [shift_apply_of_ne (Ne.symm hν)]; exact ht⟩
  · exact mem_sliceLinks.mpr ⟨hν, ht⟩

/-- **A NON-DEGENERATE TEMPORAL PLAQUETTE READS EXACTLY TWO SLICES AND THE AXIS LINKS BETWEEN
THEM.** Every link of a plaquette with one direction `τ`, the other different, and base site at time
`t`, lies in `sliceLinks τ t ∪ sliceLinks τ (t+1) ∪ axisLinks τ t`.

The `t + 1` is `Fin n` addition and therefore wraps at `t = n-1`: the slabs are strung around the
periodic time direction, which is the combinatorial shape of `Tr(Tⁿ)`.

The hypothesis `q.1.1 ≠ q.1.2` is load-bearing — see `inter_links_diag_not_mem`. -/
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
      rw [hfst, shift_apply_self, ht]
    · refine Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hfst, ?_⟩)
      rw [shift_apply_of_ne (Ne.symm hν)]; exact ht
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_sliceLinks.mpr ⟨hν, ht⟩))
  · -- the second direction is `τ`; the first is spatial
    have hμ : q.1.1 ≠ τ := fun h => hnd (by rw [h, hsnd])
    rcases hlo with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_sliceLinks.mpr ⟨hμ, ht⟩))
    · refine Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hsnd, ?_⟩)
      rw [shift_apply_of_ne (Ne.symm hμ)]; exact ht
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ (mem_sliceLinks.mpr ⟨hμ, ?_⟩))
      rw [hsnd, shift_apply_self, ht]
    · exact Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hsnd, ht⟩)

/-- **CONTROL ON THE NON-DEGENERACY HYPOTHESIS.** For the degenerate pair `(τ, τ)` the locality
claim fails: that plaquette's second link is `(τ, shift τ x)`, an axis link at time `t + 1`, which
lies in none of the three blocks as soon as `t + 1 ≠ t`.

So `inter_links_mem`'s `q.1.1 ≠ q.1.2` is doing work rather than decorating, and the diagonal has to
be removed before a slab is a two-slice object. It contributes nothing to the action
(`ActionSplit.hol_diag_one`), which is why removing it is free. `OddLagSplit` meets the same
obstruction at a reflection plane and excludes `oplqDeg` for the same reason. -/
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

/-- The degenerate plaquette really is in the temporal block at its own time — the split does not
quietly drop it. -/
theorem diag_mem_interPlaq (τ : Fin d) (x : Site d n) :
    (((τ, τ), x) : Plaq d n) ∈ interPlaq τ (x τ) :=
  mem_interPlaq.mpr ⟨Or.inl rfl, rfl⟩

/-- **THE SPLIT IS NOT VACUOUS.** Whenever some direction differs from `τ`, the temporal block
carries a non-degenerate plaquette. -/
theorem exists_nondeg_interPlaq {τ μ : Fin d} (hμ : μ ≠ τ) (x : Site d n) :
    ∃ q ∈ interPlaq τ (x τ), q.1.1 ≠ q.1.2 :=
  ⟨((μ, τ), x), mem_interPlaq.mpr ⟨Or.inr rfl, rfl⟩, hμ⟩

/-- **IN ONE DIMENSION THERE IS NO SPATIAL BLOCK.** With `d = 1` the only direction is `τ`, so
`intraPlaq` is empty and the split degenerates to the temporal block alone — the split reads the
geometry rather than imposing a shape on it. -/
theorem intraPlaq_eq_empty_of_dim_one (τ : Fin 1) (t : Fin n) :
    intraPlaq (d := 1) (n := n) τ t = ∅ := by
  refine Finset.eq_empty_of_forall_not_mem (fun q hq => ?_)
  have hT : IsTemporal τ q := Or.inl (Subsingleton.elim q.1.1 τ)
  exact (mem_intraPlaq.mp hq).1 hT

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

/-- **THE PLAQUETTE SET SPLITS BY TIME SLICE.** For any real-valued plaquette weight,

    ∑_q f q = ∑_{t} ( ∑_{q spatial at t} f q + ∑_{q temporal at t} f q ).

Every plaquette of the periodic hypercubic lattice is counted exactly once: its time is the
`τ`-coordinate of its base site, and it is temporal or spatial according to its direction pair.

DERIVED: nothing numeric. -/
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

/-- The **intra-slice (spatial) action at time `t`**: the Wilson energy of the plaquettes lying
inside the slice. By `intra_links_mem` it reads only `sliceLinks τ t`. -/
noncomputable def intraSliceAction [NeZero n] (τ : Fin d) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ intraPlaq τ t, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- The **inter-slice action of the slab from `t` to `t+1`**: the Wilson energy of the plaquettes
with one direction along `τ` and base site at time `t`. By `inter_links_mem` its non-degenerate part
reads only slices `t` and `t+1` and the axis links between them. -/
noncomputable def interSliceAction [NeZero n] (τ : Fin d) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ interPlaq τ t, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- The system's `action` really is the plaquette sum of the Wilson density on the ordered loop —
stated separately so the decomposition does not depend on unfolding `System` inline. -/
theorem sysWilson_action (N d n : ℕ) [NeZero n] (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := rfl

/-- **THE WILSON ACTION OF THE PERIODIC HYPERCUBIC LATTICE SPLITS BY TIME SLICE.**

    S(U) = ∑_{t : Fin n} ( intraSliceAction τ t U + interSliceAction τ t U ).

The shape a transfer-matrix reading needs: per-slice terms and per-slab terms, with the slabs strung
cyclically around the time direction.

DERIVED: nothing numeric; the index set is `Fin n`, the lattice's own time extent. -/
theorem action_eq_slice_sum [NeZero n] (τ : Fin d) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = ∑ t : Fin n, (intraSliceAction τ t U + interSliceAction τ t U) := by
  rw [sysWilson_action]
  simp only [intraSliceAction, interSliceAction]
  exact plaqSum_eq_slice_sum τ _

/-- **THE BOLTZMANN WEIGHT FACTORISES INTO SLICE AND SLAB WEIGHTS.**

This is the second of the three ingredients `Z = Tr(Tⁿ)` needs — the first being the cycle structure
of `inter_links_mem`, the third the Fubini regrouping of the link product measure, which is not here.

DERIVED: nothing numeric. -/
theorem boltz_eq_slab_prod [NeZero n] (τ : Fin d) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    Real.exp (-β * (sysWilson N d n).action U)
      = ∏ t : Fin n, (Real.exp (-β * intraSliceAction τ t U)
          * Real.exp (-β * interSliceAction τ t U)) := by
  rw [action_eq_slice_sum τ, Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_congr rfl (fun t _ => by rw [mul_add, Real.exp_add])

/-- **THE SLAB IS A TWO-SLICE OBJECT.** The inter-slice action may be summed over the
NON-DEGENERATE temporal plaquettes alone, which by `inter_links_mem` read only slices `t`, `t+1` and
the axis links between them. The diagonal drops out because its holonomy is the identity
(`ActionSplit.hol_diag_one`).

DERIVED: nothing numeric. -/
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

/-! ## Part 3 — the temporal plaquette energy IS the Wilson cross form

In temporal gauge the axis links are the identity and the temporal plaquette's ordered loop collapses
to `V · W⁻¹` with `V` a spatial link of slice `t` and `W` the same spatial link of slice `t+1`. Its
`Re tr` is `hsRe V W` on the nose (`CrossingIntegration.hsRe_coe_eq`), which is the argument
`CharacterExpansion.wilson_kernel_nonneg` takes. This is the step that makes the kernel below the
LATTICE's kernel rather than a formal object of the right shape.

Temporal gauge appears only as an explicit hypothesis `hg`; nothing here proves the Gibbs measure may
be computed in it, and the tree has no temporal-gauge statement at all. -/

section TemporalGauge

variable {d n N : ℕ}

/-- The Wilson density of `V W⁻¹` in terms of the cross form. -/
theorem wilsonDensity_mul_inv (V W : MassGap.SUN.SU N) :
    wilsonDensity (V * W⁻¹)
      = 1 - (1 / (N : ℝ)) * hsRe (V : Matrix (Fin N) (Fin N) ℂ)
          (W : Matrix (Fin N) (Fin N) ℂ) := by
  unfold wilsonDensity
  rw [CrossingIntegration.hsRe_coe_eq]

/-- **THE TEMPORAL HOLONOMY COLLAPSES, ORIENTATION `(μ, τ)`.** In temporal gauge the loop
`U_μ(x) · U_τ(x+μ̂) · U_μ(x+τ̂)⁻¹ · U_τ(x)⁻¹` loses its two axis factors. -/
theorem hol_temporal_gauge_right [NeZero n] {τ μ : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    wilsonHol (bd (d := d) (n := n)) ((μ, τ), x) U = U (μ, x) * (U (μ, shift τ x))⁻¹ := by
  rw [Reflect.hol_bd]
  simp [hg]

/-- **THE TEMPORAL HOLONOMY COLLAPSES, ORIENTATION `(τ, ν)`.** The opposite plane orientation gives
the same pair of spatial links in the opposite order. -/
theorem hol_temporal_gauge_left [NeZero n] {τ ν : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    wilsonHol (bd (d := d) (n := n)) ((τ, ν), x) U = U (ν, shift τ x) * (U (ν, x))⁻¹ := by
  rw [Reflect.hol_bd]
  simp [hg]

/-- **THE BRIDGE.** In temporal gauge the energy of a temporal plaquette based at time `t` is the
Wilson cross form between a spatial link of slice `t` and the SAME spatial link of slice `t+1`:

    Re tr (hol ((μ,τ),x) U) = hsRe (U_μ(x)) (U_μ(x + τ̂)).

`hsRe` is exactly the argument `CharacterExpansion.wilson_kernel_nonneg` takes, so this identity is
what points the kernel positivity at the lattice.

DERIVED: nothing numeric. -/
theorem trace_hol_temporal_gauge_right [NeZero n] {τ μ : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) ((μ, τ), x) U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe ((U (μ, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          ((U (μ, shift τ x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hol_temporal_gauge_right x U hg, CrossingIntegration.hsRe_coe_eq]

/-- The same for the opposite plane orientation: the two arguments swap, and `hsRe_comm` says the
value does not. An ordered-pair plaquette type therefore counts each plane twice with the same
energy — a feature of `WilsonHypercubic.Plaq`'s convention, not of this file. -/
theorem trace_hol_temporal_gauge_left [NeZero n] {τ ν : Fin d} (x : Site d n)
    (U : Link d n → MassGap.SUN.SU N) (hg : ∀ y : Site d n, U (τ, y) = 1) :
    (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) ((τ, ν), x) U : MassGap.SUN.SU N)
        : Matrix (Fin N) (Fin N) ℂ)).re
      = hsRe ((U (ν, shift τ x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
          ((U (ν, x) : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ) := by
  rw [hol_temporal_gauge_left x U hg, CrossingIntegration.hsRe_coe_eq]

/-- The slab energy, written so the coupling to the cross form is visible: the plaquette count minus
`1/N` times the aggregated `Re tr`. -/
theorem interSliceAction_eq_card_sub [NeZero n] (τ : Fin d) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) :
    interSliceAction τ t U
      = ((interPlaq τ t).card : ℝ)
        - (1 / (N : ℝ)) * ∑ q ∈ interPlaq τ t,
            (Matrix.trace ((wilsonHol (bd (d := d) (n := n)) q U : MassGap.SUN.SU N)
              : Matrix (Fin N) (Fin N) ℂ)).re := by
  unfold interSliceAction wilsonDensity
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]

/-- **THE SLAB WEIGHT IS A CONSTANT TIMES THE AGGREGATED WILSON WEIGHT.** With `b = β/N` the
Boltzmann factor of a slab is `e^{-β·(plaquette count)}` times `exp (b · ∑ Re tr)`, and by
`trace_hol_temporal_gauge_right` the sum in the exponent is a sum of cross forms between consecutive
slices. That is the shape `aggregate_kernel_nonneg` consumes.

DERIVED: the `1/N` is the Wilson density's own normalisation, not a chosen constant. -/
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
finite index `ι`, which the lattice supplies as `sliceLinks τ t`. The kernel carries a diagonal
factor `e^{-s/2}` from the intra-slice action, split evenly between the two slices (which is what
makes it symmetric), and an off-diagonal factor from the slab.

`s` is left as an arbitrary function of a slice configuration: on the lattice it is
`intraSliceAction τ t`, and by `intra_links_mem` that reads only the slice. -/

section Kernel

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `hsRe` is symmetric — immediate from `hsRe_eq_sum`, which presents it as a Euclidean inner
product on the real coordinates. Not in the tree before; `OddLagSplit.trace_su_mul_comm` is a
different statement. -/
theorem hsRe_comm (A B : Matrix (Fin N) (Fin N) ℂ) : hsRe A B = hsRe B A := by
  rw [hsRe_eq_sum, hsRe_eq_sum]
  exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)

/-- The **aggregated Wilson cross form** between two slice configurations: the sum over the slice's
spatial links of the cross form between the link's value on one slice and on the other. By
`trace_hol_temporal_gauge_right` this is what the slab energy is made of. -/
noncomputable def sliceForm (V W : ι → MassGap.SUN.SU N) : ℝ :=
  ∑ l : ι, hsRe ((V l : Matrix (Fin N) (Fin N) ℂ)) ((W l : Matrix (Fin N) (Fin N) ℂ))

theorem sliceForm_comm (V W : ι → MassGap.SUN.SU N) : sliceForm V W = sliceForm W V :=
  Finset.sum_congr rfl (fun l _ => hsRe_comm _ _)

/-- **THE SLICE-TO-SLICE TRANSFER KERNEL.**

    T(V, W) = e^{-s(V)/2} · e^{b · ∑_l hsRe (V l) (W l)} · e^{-s(W)/2}

with `b = β/N` the Wilson coupling over the density's normalisation. The intra-slice action is split
evenly between the two arguments, which is what makes `T` symmetric; the slab supplies the coupling.

This is a kernel on ONE slice's configurations. It is not the lattice shift, and
`HalfLineTransfer.shiftObs_pow_period` does not apply to it: nothing here has finite order.

DERIVED: the `2` is the two arguments the diagonal factor is split between, not a chosen constant.
`b` is the caller's. -/
noncomputable def transferKernel (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) : ℝ :=
  Real.exp (-(s V) / 2) * Real.exp (b * sliceForm V W) * Real.exp (-(s W) / 2)

/-- **THE KERNEL IS SYMMETRIC** — `T(V,W) = T(W,V)`. The cross form is symmetric and the diagonal
factor is split evenly. This is self-adjointness of the operator, before any spectral theory. -/
theorem transferKernel_symm (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) :
    transferKernel b s V W = transferKernel b s W V := by
  unfold transferKernel
  rw [sliceForm_comm]
  ring

/-- **THE KERNEL IS POINTWISE STRICTLY POSITIVE** — a product of exponentials. Distinct from
positive-semidefiniteness, which is the next theorem. -/
theorem transferKernel_pos (b : ℝ) (s : (ι → MassGap.SUN.SU N) → ℝ)
    (V W : ι → MassGap.SUN.SU N) :
    0 < transferKernel b s V W := by
  unfold transferKernel
  positivity

/-- **THE AGGREGATED WILSON WEIGHT IS A POSITIVE-SEMIDEFINITE KERNEL**, for `b ≥ 0` — over a whole
finite family of matrices at once, not one matrix:

    0 ≤ ∑ᵢⱼ zᵢ zⱼ exp (b · ∑_l Re tr (A_{i,l} A_{j,l}ᴴ)).

`CharacterExpansion.wilson_kernel_nonneg` at the direct sum, transported by
`OddLagSplit.hsRe_blockDiagonal_fin`. This is the step that carries the SLAB weight, which is a
product over the slice's links rather than a single plaquette.

`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` shows `0 ≤ b` cannot be dropped: it is already
sharp for one link, hence for a family containing one.

DERIVED: the only numeral is the `0` of `0 ≤ ·`, which IS positive semidefiniteness. -/
theorem aggregate_kernel_nonneg {b : ℝ} (hb : 0 ≤ b) {m : ℕ}
    (A : Fin m → ι → Matrix (Fin N) (Fin N) ℂ) (z : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * Real.exp (b * ∑ l : ι, hsRe (A i l) (A j l)) := by
  have h := wilson_kernel_nonneg hb
    (fun i => (Matrix.blockDiagonal (A i)).submatrix
      (Fintype.equivFin (Fin N × ι)).symm (Fintype.equivFin (Fin N × ι)).symm) z
  simpa only [OddLagSplit.hsRe_blockDiagonal_fin] using h

/-- **THE TRANSFER KERNEL IS POSITIVE-SEMIDEFINITE**, for `b ≥ 0`:

    0 ≤ ∑ᵢⱼ zᵢ zⱼ T(Vᵢ, Vⱼ)   for every finite family of slice configurations and real weights.

Together with `transferKernel_symm` this says `T` is a self-adjoint positive kernel — the object the
Osterwalder–Seiler construction diagonalises. The diagonal factor `e^{-s/2}` is absorbed into the
weights, which is exactly why it had to be split evenly between the two arguments.

The hypothesis `0 ≤ b` is the sign of the Wilson coupling and nothing else.

DERIVED: the only numeral is the `0` of `0 ≤ ·`. -/
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

/-- **THE OBJECT, NAMED.** `T` is symmetric and positive-semidefinite on slice configurations, at
every nonnegative coupling. That is a self-adjoint positive kernel, and it is where this file stops:
extracting its spectrum and bounding the subdominant eigenvalue is a separate obligation, and nothing
here approaches it. -/
theorem transferKernel_selfAdjoint_psd {b : ℝ} (hb : 0 ≤ b) (s : (ι → MassGap.SUN.SU N) → ℝ) :
    (∀ V W : ι → MassGap.SUN.SU N, transferKernel b s V W = transferKernel b s W V)
      ∧ (∀ (m : ℕ) (V : Fin m → (ι → MassGap.SUN.SU N)) (z : Fin m → ℝ),
          0 ≤ ∑ i, ∑ j, z i * z j * transferKernel b s (V i) (V j)) :=
  ⟨transferKernel_symm b s, fun m V z => transferKernel_psd hb s V z⟩

end Kernel

/-! ## Axiom footprints -/

#print axioms sum_by_fibre
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
