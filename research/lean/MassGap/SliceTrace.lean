import MassGap.SliceTransfer

/-!
# MassGap.SliceTrace — the finite-volume partition function as a cyclic kernel integral

Regroups `Measure.pi` over `Link d n` along the slab partition, so that the product of slab weights
becomes a cyclic product of kernels, and draws two consequences.

## What is proved

**A block regrouping of a finite product measure** (`measurePreserving_confEquiv`). For any map
`c : ι → κ` out of a finite index type, the product measure over `ι` is the image of the product,
over `t : κ`, of the product measures over the fibres `Block c t = {i // c i = t}`. The transporting
map is `regroup c W i = W (c i) ⟨i, rfl⟩`, and it is a measurable equivalence, so it moves integrals
in both directions (`MeasurePreserving.integral_comp'`).

The Mathlib pin (v4.31.0) has `measurePreserving_piCongrLeft`,
`measurePreserving_piEquivPiSubtypeProd` and `MeasurableEquiv.piCurry`, but no
`measurePreserving_piCurry` for `Measure.pi`; the currying step is proved here from `Measure.pi_eq`
and `Finset.prod_sigma'` (`measurePreserving_sigmaUncurry`).
`ProbabilityTheory.infinitePi_map_piCurry` is the same statement for the Ionescu–Tulcea product and
does not apply to `Measure.pi`.

**The Wilson partition function as a cyclic integral of slab kernels**
(`partition_eq_cycleIntegral`):

    Z(β) = ∫ ∏_{t : Fin n} K_t (W t, W (t+1))  dW,

over `W : ∀ t : Fin n, SlabIdx τ t → SU N` against the product of Haar measures. The `t+1` is `Fin n`
addition, so the product closes around the periodic direction.

**The correlator as a ratio of two such integrals** (`expect_eq_cycleRatio`, `twoSlab_expect`). For
an observable reading the slabs at two times `t₀` and `t₁`,

    ⟨Φ(t₀) Ψ(t₁)⟩ = ( ∫ Φ(W t₀) Ψ(W t₁) ∏_t K_t(W t, W (t+1)) ) / ( ∫ ∏_t K_t(W t, W (t+1)) ).

`cycle_kernel_prod_split` splits the cyclic product into two sub-products.

## The form of the trace

The cyclic integral is taken over the product of the slab configuration spaces, not as a
`LinearMap.trace` or `Matrix.trace`. A slab configuration is a point of `SlabIdx τ t → SU N`, a
compact group of positive dimension for `N ≥ 2`, so there is no index type for `Matrix.trace`;
`LinearMap.trace` typechecks for any module but is a `dite` on the existence of a finite basis and
returns `0` when there is none. Mathlib v4.31.0 carries no Schatten, Hilbert–Schmidt or trace-class
machinery.

The slab index types `SlabIdx τ t` differ with `t` — they are the links at time `t` — so the periodic
lattice gives a cycle of kernels between isomorphic but distinct spaces.

## Scope

* `K_t` is not `SliceTransfer.transferKernel`, and no statement identifies them. Three differences:
  `K_t` still reads the axis links of its own slab, where `transferKernel` acts on the spatial links
  of a slice alone; `K_t` carries the whole intra-slice weight of slice `t`, where `transferKernel`
  carries `e^{-s/2}` at each argument, which is what makes it symmetric; and `K_t` carries the
  constant `e^{-β·(interPlaq τ t).card}` that `SliceTransfer.boltz_inter_eq` separates out, reaching
  `slabWeight`'s filtered sum through `SliceTransfer.interSliceAction_eq_nondeg`, which is why
  `hN : N ≠ 0` is carried, with its plaquette sum over the ordered pair type, counting each plane
  twice (`PlaqCount.boltz_eq_std`). The symmetry and positive-semidefiniteness `SliceTransfer` proves
  of `transferKernel` are therefore not available for `K_t`; `slabKernel_pos` gives strict
  positivity, immediate from the exponentials.
* The locality of `slabWeight_local` is vacuous at small `n`. `slabSupport τ t` is the links at times
  `t` and `t+1`, which is every link when `n ≤ 2`; `slabSupport_eq_univ_iff` is sharp in both
  directions, so locality begins at `n ≥ 3` (`slabSupport_ne_univ`). At `n = 1` the cycle has one
  factor and `slabKernel` ignores its second argument, since `patch` takes the first.
* No statement says `K_t` couples its two arguments. Strict positivity and the regrouping bijection
  are consistent with a kernel constant in its second argument;
  `SliceTransfer.exists_nondeg_interPlaq` is the nearest non-degeneracy statement and is not applied
  here.
* No spectrum appears, and no bound on `λ_max`.
* No composition is performed. `cycle_kernel_prod_split` exhibits the cut between two arcs; no
  statement in this file is about an operator power, so no `T^d` appears anywhere.
  `Transfer.TransferData.periodicCorr` records why a ratio of this shape is not
  `Spectral.PeriodicSpectralForm`'s: expanding each arc in an eigenbasis gives one spectral index per
  arc, so the ratio would be a double sum `∑_{i,j} λ_i^d λ_j^{n−d}` weighted by matrix elements,
  rather than `∑_i w_i λ_i^d`.
* No gauge fixing is used. `SliceTransfer`'s temporal gauge is a hypothesis there (`hg`) and is not
  discharged.
* `β` is `sysWilson`'s coupling. `PlaqCount.boltz_eq_std` records that the ordered-`Plaq` sum counts
  each plane twice, so it is half the coupling of a formulation summing each plane once.

Build: `python code/lean_build.py build MassGap.SliceTrace`.
-/

namespace MassGap.SliceTrace

open MeasureTheory
open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.WilsonHypercubic MassGap.CompactGauge MassGap.SliceTransfer

/-! ## Part 0 — regrouping a finite product measure along the fibres of a block map

This is the step `SliceTransfer` named as missing. It is stated for an arbitrary finite index type
and an arbitrary block map, because nothing about it is about the lattice. -/

section Regroup

/-- The **block at `t`**: the fibre of the block map `c` over `t`, as a subtype of the index.

DERIVED: no numeral. -/
abbrev Block {ι κ : Type} (c : ι → κ) (t : κ) : Type := {i : ι // c i = t}

/-- Assembling a flat configuration from per-block configurations. Each index `i` is served by
its own block `c i`, where it sits as `⟨i, rfl⟩`.

DERIVED: no numeral. -/
def regroup {ι κ Ω : Type} (c : ι → κ) (W : ∀ t : κ, Block c t → Ω) : ι → Ω :=
  fun i => W (c i) ⟨i, rfl⟩

/-- Reading a regrouped configuration at a known block. If `i` is known to lie in block `t`, the
value is the block-`t` configuration at `i`. The proof carried by the subtype is irrelevant.

DERIVED: no numeral. -/
theorem regroup_apply {ι κ Ω : Type} (c : ι → κ) (W : ∀ t : κ, Block c t → Ω) {t : κ}
    (i : ι) (h : c i = t) : regroup c W i = W t ⟨i, h⟩ := by
  subst h; rfl

/-- Restricting a regrouped configuration to one block returns that block's configuration. This
is what makes an observable reading one time slice a function of one integration variable.

DERIVED: no numeral. -/
theorem regroup_restrict {ι κ Ω : Type} (c : ι → κ) (W : ∀ t : κ, Block c t → Ω) (t : κ) :
    (fun i : Block c t => regroup c W i.val) = W t := by
  funext i
  exact regroup_apply c W i.val i.property

/-- The currying step, which Mathlib does not have for `Measure.pi`.

`Sigma.uncurry` carries the product over `t : κ` of the product measures over the fibres `B t` to the
flat product measure over `Σ t, B t`. Mathlib v4.31.0 has `MeasurableEquiv.piCurry` (the equivalence)
and `ProbabilityTheory.infinitePi_map_piCurry` (the same statement for the Ionescu–Tulcea product),
but nothing for `Measure.pi`. Proved from `Measure.pi_eq` on rectangles: the preimage of a rectangle
under `Sigma.uncurry` is a rectangle of rectangles, and `Finset.prod_sigma'` matches the two
products.

DERIVED: no numeral. -/
theorem measurePreserving_sigmaUncurry {κ : Type} [Fintype κ] [DecidableEq κ]
    {B : κ → Type} [∀ t, Fintype (B t)] {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun W : (∀ t : κ, B t → Ω) => (Sigma.uncurry W : (Σ t : κ, B t) → Ω))
      (Measure.pi fun t : κ => Measure.pi fun _ : B t => μ)
      (Measure.pi fun _ : (Σ t : κ, B t) => μ) := by
  refine ⟨measurable_sigmaUncurry, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_sigmaUncurry (MeasurableSet.univ_pi hs)]
  have hpre : (fun W : (∀ t : κ, B t → Ω) => (Sigma.uncurry W : (Σ t : κ, B t) → Ω))
        ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun t : κ => Set.univ.pi (fun j : B t => s ⟨t, j⟩)) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, Sigma.uncurry]
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Finset.prod_sigma' (Finset.univ : Finset κ) (fun _ => Finset.univ)
    (fun (t : κ) (j : B t) => μ (s ⟨t, j⟩)), Finset.univ_sigma_univ]

variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω]

/-- `regroup` as a measurable equivalence. Currying, then relabelling the sigma type of fibres by
`Equiv.sigmaFiberEquiv` back to the index type. Being an equivalence rather than merely a map is what
lets `MeasurePreserving.integral_comp'` move an integral in either direction.

DERIVED: no numeral. -/
def confEquiv (c : ι → κ) : (∀ t : κ, Block c t → Ω) ≃ᵐ (ι → Ω) :=
  (MeasurableEquiv.piCurry (fun (t : κ) (_ : Block c t) => Ω)).symm.trans
    (MeasurableEquiv.arrowCongr' (Equiv.sigmaFiberEquiv c) (MeasurableEquiv.refl Ω))

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- The equivalence is the assembly map — nothing is hidden in the coercion, and it is `rfl`.

DERIVED: no numeral. -/
theorem coe_confEquiv (c : ι → κ) : ⇑(confEquiv (Ω := Ω) c) = regroup c := rfl

/-- The Fubini step `SliceTransfer` named as missing. The product measure over the index type is
the image, under assembly, of the product over blocks of the product measures within each block.

`OddLagSplit.join3` / `OddLagSplit.integral_three_block` are this for a three-block split; this is
the version indexed by an arbitrary finite `κ`, which is what a `Fin n`-indexed slab decomposition
needs. (`SliceTransfer`'s module docstring attributes those two to `ActionSplit`; they are in
`OddLagSplit`.)

DERIVED: no numeral. -/
theorem measurePreserving_confEquiv (c : ι → κ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (confEquiv (Ω := Ω) c)
      (Measure.pi fun t : κ => Measure.pi fun _ : Block c t => μ)
      (Measure.pi fun _ : ι => μ) := by
  have h1 := measurePreserving_sigmaUncurry (B := fun t : κ => Block c t) (Ω := Ω) μ
  have h2 := measurePreserving_arrowCongr' (fun _ : (Σ t : κ, Block c t) => μ) (fun _ : ι => μ)
    (Equiv.sigmaFiberEquiv c) (MeasurableEquiv.refl Ω) (fun _ => MeasurePreserving.id μ)
  exact h2.comp h1

/-- The integral of anything, regrouped. The working form of the previous theorem.

DERIVED: no numeral. -/
theorem integral_regroup (c : ι → κ) (μ : Measure Ω) [IsProbabilityMeasure μ] (f : (ι → Ω) → ℝ) :
    ∫ U, f U ∂(Measure.pi fun _ : ι => μ)
      = ∫ W, f (regroup c W) ∂(Measure.pi fun t : κ => Measure.pi fun _ : Block c t => μ) :=
  ((measurePreserving_confEquiv c μ).integral_comp' f).symm

end Regroup

/-! ## Part 1 — the slab decomposition of the Wilson lattice

The block map is the time coordinate of a link. `mem_slab_iff`, below, is what identifies its fibres
with `SliceTransfer`'s slabs; `SliceTransfer.sliceLinks_axisLinks_cover` and `slab_pairwise_disjoint`
are the corresponding cover and disjointness there. -/

section Slab

variable {d n N : ℕ} [NeZero n]

/-- The **time of a link**: the `τ`-coordinate of its base site. This is the block map.

DERIVED: no numeral. -/
def timeOf (τ : Fin d) (l : Link d n) : Fin n := l.2 τ

/-- The **slab index at time `t`**: the links of the lattice whose base site sits at time `t`.
`mem_slab_iff` below is what says these are exactly the spatial links of slice `t` together with the
axis links leaving it; `SliceTransfer.sliceLinks_axisLinks_cover` says the slabs cover the link set
and `slab_pairwise_disjoint` that they are disjoint, which is a different statement from the fibre
identification.

DERIVED: no numeral. -/
abbrev SlabIdx (τ : Fin d) (t : Fin n) : Type := Block (timeOf (d := d) (n := n) τ) t

omit [NeZero n] in
/-- The slab index type really is the slice-and-axis block of `SliceTransfer`, so this file's blocks
are that file's partition and not a second one.

DERIVED: no numeral. -/
theorem mem_slab_iff (τ : Fin d) (t : Fin n) (l : Link d n) :
    l ∈ sliceLinks τ t ∪ axisLinks τ t ↔ timeOf τ l = t := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h' | h'
    · exact (mem_sliceLinks.mp h').2
    · exact (mem_axisLinks.mp h').2
  · intro h
    by_cases hd : l.1 = τ
    · exact Finset.mem_union_right _ (mem_axisLinks.mpr ⟨hd, h⟩)
    · exact Finset.mem_union_left _ (mem_sliceLinks.mpr ⟨hd, h⟩)

/-- The **support of the slab based at `t`**: the links at time `t` together with those at time
`t+1`. `intra_support` and `inter_support` below are what say the slab's plaquettes read only this
set, via `SliceTransfer.intra_links_mem` and `inter_links_mem`. Note the restriction:
`inter_links_mem` carries `q.1.1 ≠ q.1.2`, so it says nothing about the degenerate plaquette
`((τ,τ),x)`, and
`inter_support` is correspondingly stated on the filtered set only. `slabWeight` sums over that same
filtered set, so nothing here relies on a claim about the diagonal.

DERIVED: the `1` is one time step — the next slice, `Fin n` addition, which wraps. It is an index
step, not a spacing, and it is `SliceTransfer.interPlaq`'s own step, inherited rather than chosen
here. -/
def slabSupport (τ : Fin d) (t : Fin n) : Finset (Link d n) :=
  Finset.univ.filter (fun l : Link d n => timeOf τ l = t ∨ timeOf τ l = t + 1)

/-- Membership in the slab support unfolded.

DERIVED: the `1` is `slabSupport`'s own time step — one slice on, `Fin n` addition. -/
theorem mem_slabSupport {τ : Fin d} {t : Fin n} {l : Link d n} :
    l ∈ slabSupport τ t ↔ (timeOf τ l = t ∨ timeOf τ l = t + 1) := by
  simp [slabSupport]

/-- The support is the union of two of `SliceTransfer`'s slabs, written in that file's own
`Finset`s. This is what makes `mem_slab_iff` load-bearing: the blocks this file integrates over are
that file's partition of the link set and not a second decomposition alongside it.

DERIVED: the `1` is `slabSupport`'s time step. -/
theorem slabSupport_eq (τ : Fin d) (t : Fin n) :
    slabSupport τ t
      = (sliceLinks τ t ∪ axisLinks τ t) ∪ (sliceLinks τ (t + 1) ∪ axisLinks τ (t + 1)) := by
  ext l
  rw [mem_slabSupport, Finset.mem_union, mem_slab_iff, mem_slab_iff]

/-- Control: a full support forces a short torus. If the slab support is the whole link set then
`Fin n` has at most two elements, so `slabWeight_local`'s hypothesis degenerates to `U = V`
everywhere and the locality claim carries nothing. The converse is `slabSupport_eq_univ_of_le_two`;
this theorem proves only this direction.

The proof reads a link straight off a time: `(τ, fun _ => c)` sits at time `c`, so a full support
forces every `c : Fin n` into `{t, t+1}`.

DERIVED: the `2` is the cardinality of `{t, t+1}` and the `1` is `slabSupport`'s time step; neither
is chosen. -/
theorem card_le_two_of_slabSupport_univ (τ : Fin d) (t : Fin n)
    (h : slabSupport τ t = Finset.univ) : n ≤ 2 := by
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {t, t + 1} := by
    intro c _
    have hc : ((τ, fun _ => c) : Link d n) ∈ slabSupport τ t := h ▸ Finset.mem_univ _
    rcases mem_slabSupport.mp hc with h' | h'
    · exact Finset.mem_insert.mpr (Or.inl h')
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h'))
  have hcard := Finset.card_le_card hsub
  have h2 : ({t, t + 1} : Finset (Fin n)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  simpa using le_trans hcard h2

/-- On a two-element cycle every element is one of any chosen pair `{b, b+1}`. Four cases, by
`decide`; the statement is what makes the `n ≤ 2` half of `slabSupport_eq_univ_iff` true.

DERIVED: the `2` is `Fin 2`'s own extent and the `1` is the cycle's step; neither is chosen. -/
theorem fin_two_eq_or_eq_succ : ∀ a b : Fin 2, a = b ∨ a = b + 1 := by decide

/-- Control: at `n ≤ 2` the support is every link. The converse of
`card_le_two_of_slabSupport_univ`, so the two together make `n ≤ 2` the exact condition under which
`slabWeight_local` says nothing. At `n = 1` the times are a subsingleton; at `n = 2` every time is
`t` or `t+1`.

DERIVED: the `2` is `card_le_two_of_slabSupport_univ`'s bound, read back; the `1` is
`slabSupport`'s time step. -/
theorem slabSupport_eq_univ_of_le_two (h2 : n ≤ 2) (τ : Fin d) (t : Fin n) :
    slabSupport τ t = Finset.univ := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : n = 1 ∨ n = 2 := by omega
  refine Finset.eq_univ_of_forall (fun l => mem_slabSupport.mpr ?_)
  rcases hn with rfl | rfl
  · exact Or.inl (Subsingleton.elim _ _)
  · exact fin_two_eq_or_eq_succ (timeOf τ l) t

/-- The sharp condition. The slab support is the whole link set exactly when the time extent is
at most two. Below that threshold `slabWeight_local` is the tautology `U = V → ⋯`; from `n ≥ 3` it is
a locality statement.

DERIVED: the `2` is the two times `{t, t+1}` a slab spans. -/
theorem slabSupport_eq_univ_iff (τ : Fin d) (t : Fin n) :
    slabSupport τ t = Finset.univ ↔ n ≤ 2 :=
  ⟨card_le_two_of_slabSupport_univ τ t, fun h => slabSupport_eq_univ_of_le_two h τ t⟩

/-- Control: from `n ≥ 3` the support is a proper subset. The contrapositive of the previous
theorem, and the statement that `slabWeight_local` is a real locality claim rather than a tautology.

DERIVED: the `3` is `2 + 1`, the first extent at which a third time exists; it is read off
`card_le_two_of_slabSupport_univ` and is not chosen. -/
theorem slabSupport_ne_univ (h3 : 3 ≤ n) (τ : Fin d) (t : Fin n) :
    slabSupport τ t ≠ Finset.univ := by
  intro h
  have := card_le_two_of_slabSupport_univ τ t h
  omega

/-- The spatial plaquettes of slice `t` read the slab support. `intra_links_mem` in the shape
`ReflectionPositivity.action_on_congr_of_support` consumes.

DERIVED: no numeral. -/
theorem intra_support (τ : Fin d) (t : Fin n) :
    ∀ q ∈ intraPlaq (d := d) (n := n) τ t, ∀ l ∈ (bd q).map Prod.fst, l ∈ slabSupport τ t := by
  intro q hq l hl
  obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hl
  exact mem_slabSupport.mpr (Or.inl (mem_sliceLinks.mp (intra_links_mem hq lo hlo)).2)

/-- The non-degenerate temporal plaquettes of the slab read the slab support. `inter_links_mem`
in the same shape. The degenerate pair `(τ, τ)` is excluded, as it must be
(`inter_links_diag_not_mem`), and `interSliceAction_eq_nondeg` is what says excluding it is free.

DERIVED: no numeral of its own; the `t + 1` is `slabSupport`'s. -/
theorem inter_support (τ : Fin d) (t : Fin n) :
    ∀ q ∈ (interPlaq (d := d) (n := n) τ t).filter (fun q => q.1.1 ≠ q.1.2),
      ∀ l ∈ (bd q).map Prod.fst, l ∈ slabSupport τ t := by
  intro q hq l hl
  obtain ⟨hqmem, hnd⟩ := Finset.mem_filter.mp hq
  obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hl
  have h := inter_links_mem hqmem hnd lo hlo
  refine mem_slabSupport.mpr ?_
  rcases Finset.mem_union.mp h with h' | h'
  · rcases Finset.mem_union.mp h' with h'' | h''
    · exact Or.inl (mem_sliceLinks.mp h'').2
    · exact Or.inr (mem_sliceLinks.mp h'').2
  · exact Or.inl (mem_axisLinks.mp h').2

/-- The weight of the slab based at time `t`, as a function of a full configuration: the slice
weight of `t` times the slab weight coupling `t` to `t+1`, the latter summed over the non-degenerate
temporal plaquettes only.

`SliceTransfer.boltz_eq_slab_prod` factorises the Boltzmann weight into these, and
`interSliceAction_eq_nondeg` says dropping the diagonal costs nothing. The intra-slice factor is not
split evenly between the two slices here — that symmetrisation is `transferKernel`'s, and it is a
choice about how to present the kernel, not about what `Z` is.

DERIVED: no numeral; `β` is the caller's coupling and the sum is over a `Finset`. -/
noncomputable def slabWeight (τ : Fin d) (β : ℝ) (t : Fin n)
    (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  Real.exp (-β * intraSliceAction τ t U)
    * Real.exp (-β * ∑ q ∈ (interPlaq τ t).filter (fun q => q.1.1 ≠ q.1.2),
        wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U))

/-- The Boltzmann weight, written on the link type. `LatticeGauge.System.boltz` takes a
`sys.Config`, which is `Link d n → SU N` only after `sysWilson` unfolds — a semireducible `def`, so
`rw` cannot see through it and every rewrite that mentions a configuration fails on transparency.
This is the same weight with the argument typed as what it is. `sysWilson_boltz` is the bridge and it
is `rfl`.

DERIVED: no numeral; the sum is over the plaquette type. -/
noncomputable def latticeBoltz (β : ℝ) (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  Real.exp (-β * ∑ q : Plaq d n, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U))

/-- The rewritten weight is the system's own.

DERIVED: no numeral. -/
theorem sysWilson_boltz (β : ℝ) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).boltz β U = latticeBoltz β U := rfl

/-- The partition function is the integral of that weight.

DERIVED: no numeral. -/
theorem partition_eq_integral_latticeBoltz (β : ℝ) :
    (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β
      = ∫ U : Link d n → MassGap.SUN.SU N, latticeBoltz β U
          ∂(Measure.pi fun _ : Link d n => probHaar (MassGap.SUN.SU N)) := rfl

/-- The correlation numerator is the integral of the observable against that weight.

DERIVED: no numeral. -/
theorem corrNum_eq_integral (β : ℝ) (O : (Link d n → MassGap.SUN.SU N) → ℝ) :
    (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β O
      = ∫ U : Link d n → MassGap.SUN.SU N, O U * latticeBoltz β U
          ∂(Measure.pi fun _ : Link d n => probHaar (MassGap.SUN.SU N)) := rfl

/-- The Boltzmann weight is the cyclic product of slab weights.
`SliceTransfer.boltz_eq_slab_prod` with the diagonal removed slab by slab.

DERIVED: the only numeral is the `0` of `hN : N ≠ 0`, which excludes the empty gauge group so that
`wilsonDensity_one` applies to the dropped diagonal. It is not a chosen constant. -/
theorem latticeBoltz_eq_prod_slabWeight (hN : N ≠ 0) (τ : Fin d) (β : ℝ)
    (U : Link d n → MassGap.SUN.SU N) :
    latticeBoltz β U = ∏ t : Fin n, slabWeight τ β t U := by
  show Real.exp (-β * (sysWilson N d n).action U) = _
  rw [boltz_eq_slab_prod τ β U]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  unfold slabWeight
  rw [interSliceAction_eq_nondeg hN τ t U]

/-- The slab weight reads only its own support. Two configurations agreeing on the links at times
`t` and `t+1` give it the same value. This is what makes the slab weight a kernel rather than a
labelled factor, and it is `ReflectionPositivity.action_on_congr_of_support` applied twice — to the
spatial plaquettes of slice `t` and to the non-degenerate temporal plaquettes of the slab.

The hypothesis is a real restriction only from `n ≥ 3`: `slabSupport_eq_univ_iff` says the support is
every link exactly when `n ≤ 2`, and there this theorem says nothing.

DERIVED: no numeral. -/
theorem slabWeight_local (τ : Fin d) (β : ℝ) (t : Fin n) (U V : Link d n → MassGap.SUN.SU N)
    (h : ∀ l ∈ slabSupport τ t, U l = V l) :
    slabWeight (N := N) τ β t U = slabWeight τ β t V := by
  unfold slabWeight intraSliceAction
  rw [MassGap.ReflectionPositivity.action_on_congr_of_support (bd (d := d) (n := n))
      (wilsonDensity (N := N)) (intraPlaq τ t) (slabSupport τ t) (intra_support τ t) U V h,
    MassGap.ReflectionPositivity.action_on_congr_of_support (bd (d := d) (n := n))
      (wilsonDensity (N := N)) ((interPlaq τ t).filter (fun q => q.1.1 ≠ q.1.2))
      (slabSupport τ t) (inter_support τ t) U V h]

end Slab

/-! ## Part 2 — the slab kernel and the trace formula -/

section Kernel

variable {d n N : ℕ} [NeZero n]

/-- A two-slab configuration, extended by the identity. Given configurations `A` of slab `t` and
`B` of slab `t+1`, the configuration that is `A` on slab `t`, `B` on slab `t+1`, and the identity
element everywhere else. Only the two named slabs are ever read, by `slabWeight_local`.

The order of the two tests matters only when `t + 1 = t`, i.e. `n = 1`; there the two slabs are the
same slab and `A` wins, which is consistent because a one-slice torus has `W 0 = W (0+1)`.

DERIVED: the `1` chosen as the filler value is the group identity, and it is never read — any element
would do, and `slabWeight_local` is what says so. The `t + 1` is `SliceTransfer.interPlaq`'s time
step. -/
def patch (τ : Fin d) {t : Fin n}
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    ∀ s : Fin n, SlabIdx (d := d) (n := n) τ s → MassGap.SUN.SU N :=
  fun s l =>
    if h : s = t then A ⟨l.val, by rw [l.property]; exact h⟩
    else if h' : s = t + 1 then B ⟨l.val, by rw [l.property]; exact h'⟩
    else 1

/-- The patch agrees with the original on the slab support. On every link at time `t` or `t+1`,
the assembled patched configuration reads the same value as the assembled original.

The degenerate case `t + 1 = t` cannot arise in the second branch: a link there has time `t+1` and
not `t`, so `t + 1 ≠ t` is DERIVED rather than assumed.

DERIVED: the `1` is `slabSupport`'s time step. -/
theorem regroup_patch_eq (τ : Fin d) (t : Fin n)
    (W : ∀ s : Fin n, SlabIdx (d := d) (n := n) τ s → MassGap.SUN.SU N)
    (l : Link d n) (hl : l ∈ slabSupport τ t) :
    regroup (timeOf τ) (patch (N := N) τ (W t) (W (t + 1))) l = regroup (timeOf τ) W l := by
  by_cases h1 : timeOf τ l = t
  · rw [regroup_apply (timeOf τ) (patch (N := N) τ (W t) (W (t + 1))) l h1,
      regroup_apply (timeOf τ) W l h1]
    simp [patch]
  · have h2 : timeOf τ l = t + 1 := (mem_slabSupport.mp hl).resolve_left h1
    have hne : t + 1 ≠ t := fun hc => h1 (h2.trans hc)
    rw [regroup_apply (timeOf τ) (patch (N := N) τ (W t) (W (t + 1))) l h2,
      regroup_apply (timeOf τ) W l h2]
    simp [patch, hne]

/-- The slab kernel. `K_t (A, B)` is the weight of the slab from `t` to `t+1` evaluated on any
configuration that restricts to `A` on slab `t` and `B` on slab `t+1`; `slabWeight_local` says the
value does not depend on which one, and `patch` supplies a concrete choice.

This is a kernel between the configuration space of slab `t` and that of slab `t+1`. It still carries
the axis links of slab `t` — the links temporal gauge would set to the identity — the whole
intra-slice weight of slice `t` rather than `transferKernel`'s symmetric half at each argument, and
the plaquette-count constant `SliceTransfer.boltz_inter_eq` separates out. It is therefore not
`SliceTransfer.transferKernel`, and the gap between them is three steps, not one; the module
docstring lists them.

At `n = 1` this ignores `B` entirely, because `patch` resolves `s = t` first and `t + 1 = t` there.
Nothing in this file proves it depends on `B` at any `n`.

DERIVED: the `1` is `SliceTransfer.interPlaq`'s time step. -/
noncomputable def slabKernel (τ : Fin d) (β : ℝ) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) : ℝ :=
  slabWeight τ β t (regroup (timeOf τ) (patch (N := N) τ A B))

/-- The slab weight of an assembled configuration is the kernel at its two slabs. This is the
whole content of "the transfer matrix": a factor of the Boltzmann weight that depends on the global
configuration only through two consecutive slabs.

DERIVED: the `1` is `SliceTransfer.interPlaq`'s time step. -/
theorem slabWeight_regroup_eq_kernel (τ : Fin d) (β : ℝ) (t : Fin n)
    (W : ∀ s : Fin n, SlabIdx (d := d) (n := n) τ s → MassGap.SUN.SU N) :
    slabWeight τ β t (regroup (timeOf τ) W) = slabKernel (N := N) τ β t (W t) (W (t + 1)) :=
  (slabWeight_local τ β t _ _ (fun l hl => regroup_patch_eq τ t W l hl)).symm

/-- The **product of Haar measures over the slab configuration spaces** — the measure the cyclic
integral is taken against. Each slab carries the product Haar measure over its own links.

DERIVED: no numeral. -/
noncomputable def slabVol (τ : Fin d) :
    Measure (∀ t : Fin n, SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) :=
  Measure.pi fun t : Fin n =>
    Measure.pi fun _ : SlabIdx (d := d) (n := n) τ t => probHaar (MassGap.SUN.SU N)

/-- The partition function is a cyclic integral of slab kernels, on the real Wilson lattice.

    Z(β) = ∫ ∏_{t : Fin n} K_t (W t, W (t+1)) dW

This is the integral form of `Z = Tr(Tⁿ)` and is not that equation: the `K_t` are `n` distinct
kernels between `n` distinct spaces, the product is pointwise, and no composition and no single `T`
appears in the statement.

over `W : ∀ t, SlabIdx τ t → SU N`, against the product of Haar measures. The `t+1` is `Fin n`
addition, so the product closes around the periodic time direction: the last factor couples slab
`n−1` back to slab `0`, which is the trace and is why this is not a chain.

The three ingredients, now all present: the cycle structure (`SliceTransfer.inter_links_mem`), the
factorisation of the Boltzmann weight (`SliceTransfer.boltz_eq_slab_prod` via
`latticeBoltz_eq_prod_slabWeight`), and the Fubini regrouping (`measurePreserving_confEquiv`), which
is what was missing.

No gauge fixing is used. `K_t` carries the axis links of its own slab; see `slabKernel`.

DERIVED: `β` is the caller's coupling, `n` the lattice's own time extent, the `t + 1` is one time
step of `Fin n` addition, and the `0` of `hN : N ≠ 0` excludes the empty gauge group. None is
chosen. -/
theorem partition_eq_cycleIntegral (hN : N ≠ 0) (τ : Fin d) (β : ℝ) :
    (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β
      = ∫ W, ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
          ∂(slabVol (d := d) (n := n) (N := N) τ) := by
  rw [partition_eq_integral_latticeBoltz (N := N) (d := d) (n := n) β,
    integral_regroup (timeOf (d := d) (n := n) τ) (probHaar (MassGap.SUN.SU N))
      (fun U => latticeBoltz β U)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
  show latticeBoltz β (regroup (timeOf τ) W)
      = ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
  rw [latticeBoltz_eq_prod_slabWeight hN τ β]
  exact Finset.prod_congr rfl (fun t _ => slabWeight_regroup_eq_kernel τ β t W)

/-- The Gibbs expectation, written on the link type. Same reason as `latticeBoltz`:
`System.expect` takes a `sys.Config` observable, and no rewrite can see through `sysWilson`.
`latticeExpect_eq` is the bridge and it is `rfl`.

DERIVED: no numeral. -/
noncomputable def latticeExpect (β : ℝ) (O : (Link d n → MassGap.SUN.SU N) → ℝ) : ℝ :=
  (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O

/-- The rewritten expectation is the system's own.

DERIVED: no numeral. -/
theorem latticeExpect_eq (β : ℝ) (O : (Link d n → MassGap.SUN.SU N) → ℝ) :
    latticeExpect β O = (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β O := rfl

/-- Every correlator is a ratio of cyclic integrals. The Gibbs expectation of an arbitrary
observable, with no locality assumed of it, is the cyclic integral with `O` in the integrand over the
cyclic integral without it.

Not written as `Tr(O Tⁿ) / Tr(Tⁿ)`: that presupposes `O` is an operator inserted at one point of the
cycle, and the `O` here is a function of all `n` slabs at once, for which there is no such operator.
`twoSlab_expect` is the case where `O` does sit at two points.

DERIVED: the `t + 1` is `SliceTransfer.interPlaq`'s time step, one slice on and `Fin n` addition,
inherited from `slabKernel`; the `0` of `hN : N ≠ 0` excludes the empty gauge group. Neither is
chosen. -/
theorem expect_eq_cycleRatio (hN : N ≠ 0) (τ : Fin d) (β : ℝ)
    (O : (Link d n → MassGap.SUN.SU N) → ℝ) :
    latticeExpect β O
      = (∫ W, O (regroup (timeOf τ) W) * ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
            ∂(slabVol (d := d) (n := n) (N := N) τ))
        / ∫ W, ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
            ∂(slabVol (d := d) (n := n) (N := N) τ) := by
  show (sysWilson N d n).corrNum (probHaar (MassGap.SUN.SU N)) β O
      / (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β = _
  rw [partition_eq_cycleIntegral hN τ β, corrNum_eq_integral β O,
    integral_regroup (timeOf (d := d) (n := n) τ) (probHaar (MassGap.SUN.SU N))
      (fun U => O U * latticeBoltz β U)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
  show O (regroup (timeOf τ) W) * latticeBoltz β (regroup (timeOf τ) W)
      = O (regroup (timeOf τ) W) * ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
  rw [latticeBoltz_eq_prod_slabWeight hN τ β]
  exact congrArg _ (Finset.prod_congr rfl (fun t _ => slabWeight_regroup_eq_kernel τ β t W))

/-- The two-slab correlator as a cyclic integral with two insertions.

For observables `Φ` and `Ψ` that read the slabs at times `t₀` and `t₁` and nothing else, the Gibbs
expectation of their product is the cyclic integral with those two insertions, divided by the cyclic
integral without them.

This is the integral form of `Tr(Φ T^{d} Ψ T^{n−d}) / Tr(Tⁿ)` and is not that expression: no
composition happens, so no operator power appears. `cycle_kernel_prod_split` cuts the product into
the two sub-products a composition would turn into the two powers.

Two things the statement does not require. `t₀` and `t₁` may be equal, in which case there is no
two-point anything and this reduces to a single insertion. And `Φ` and `Ψ` read a whole slab — the
spatial links of their slice together with the axis links leaving it — not a gauge-invariant slice
observable; a slice observable in the Osterwalder–Seiler sense is a special case of this and is not
singled out.

The shape is what `Transfer.TransferData.periodicCorr`'s docstring names as the exact finite-volume
thermal
correlator and distinguishes from `Spectral.PeriodicSpectralForm`: expanding each arc in an
eigenbasis gives one spectral index per arc, hence a double sum `∑_{i,j} Φ_{ij} Ψ_{ji} λ_i^{d}
λ_j^{n−d}`, not the single-index `∑_i w_i λ_i^{d}`. `periodicCorr` is the `j = vacuum` row of that
sum, symmetrised. Nothing here narrows that gap; it states the object the gap is about.

DERIVED: `t₀` and `t₁` are the caller's times; the `t + 1` is `SliceTransfer.interPlaq`'s time step,
inherited from `slabKernel`; the `0` of `hN : N ≠ 0` excludes the empty gauge group. None is
chosen. -/
theorem twoSlab_expect (hN : N ≠ 0) (τ : Fin d) (β : ℝ) (t₀ t₁ : Fin n)
    (Φ : (SlabIdx (d := d) (n := n) τ t₀ → MassGap.SUN.SU N) → ℝ)
    (Ψ : (SlabIdx (d := d) (n := n) τ t₁ → MassGap.SUN.SU N) → ℝ) :
    latticeExpect β
        (fun U => Φ (fun l : SlabIdx (d := d) (n := n) τ t₀ => U l.val)
          * Ψ (fun l : SlabIdx (d := d) (n := n) τ t₁ => U l.val))
      = (∫ W, Φ (W t₀) * Ψ (W t₁) * ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
            ∂(slabVol (d := d) (n := n) (N := N) τ))
        / ∫ W, ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
            ∂(slabVol (d := d) (n := n) (N := N) τ) := by
  rw [expect_eq_cycleRatio hN τ β]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
  show Φ (fun l : SlabIdx (d := d) (n := n) τ t₀ => regroup (timeOf τ) W l.val)
      * Ψ (fun l : SlabIdx (d := d) (n := n) τ t₁ => regroup (timeOf τ) W l.val)
      * ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
    = Φ (W t₀) * Ψ (W t₁) * ∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1))
  rw [regroup_restrict (timeOf (d := d) (n := n) τ) W t₀,
    regroup_restrict (timeOf (d := d) (n := n) τ) W t₁]

omit [NeZero n] in
/-- A product over `Fin n` splits at `k` into the factors below `k` and the rest. A plain `Finset`
fact about an arbitrary real function, stated so that the kernel version below is one line.

DERIVED: no numeral; `k` is the caller's cut and the comparison is on `Fin n`'s own value. -/
theorem prod_split_at (f : Fin n → ℝ) (k : Fin n) :
    ∏ t : Fin n, f t
      = (∏ t ∈ Finset.univ.filter (fun t : Fin n => (t : ℕ) < (k : ℕ)), f t)
        * ∏ t ∈ Finset.univ.filter (fun t : Fin n => ¬ ((t : ℕ) < (k : ℕ))), f t :=
  (Finset.prod_filter_mul_prod_filter_not Finset.univ _ f).symm

/-- The cyclic kernel product cuts into two arcs at any time. The integrand of
`partition_eq_cycleIntegral` and `twoSlab_expect`, split at `k` into the factors before `k` and the
factors from `k` on.

Read the statement for what it gives: two sub-products of kernels, not two operator powers. With an
insertion at time `0` and another at `k`, these are the two arcs a composition would turn into
`T^{k}` and `T^{n−k}` — and that composition needs one Fubini per intermediate variable and is not
done here or anywhere in the tree. This lemma is the whole of what "the correlator has two arcs" is
backed by. It is not applied in any proof in this file; `twoSlab_expect` does not use it, and the cut
point `k` is unrelated to that theorem's insertion times unless a caller chooses it so.

DERIVED: `k` is the caller's cut, the comparison is on `Fin n`'s own value, and the `t + 1` is
`slabKernel`'s time step. -/
theorem cycle_kernel_prod_split (τ : Fin d) (β : ℝ)
    (W : ∀ t : Fin n, SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) (k : Fin n) :
    (∏ t : Fin n, slabKernel (N := N) τ β t (W t) (W (t + 1)))
      = (∏ t ∈ Finset.univ.filter (fun t : Fin n => (t : ℕ) < (k : ℕ)),
            slabKernel (N := N) τ β t (W t) (W (t + 1)))
        * ∏ t ∈ Finset.univ.filter (fun t : Fin n => ¬ ((t : ℕ) < (k : ℕ))),
            slabKernel (N := N) τ β t (W t) (W (t + 1)) :=
  prod_split_at _ k

end Kernel

/-! ## Part 3 — controls

Two facts about the regrouping and the kernel. Neither says the kernel couples its two arguments;
that control does not exist here and is named in the module docstring. The locality control is
`slabSupport_ne_univ`, up in Part 1 with the object it is about. -/

section Controls

variable {d n N : ℕ} [NeZero n]

omit [NeZero n] in
/-- The regrouping is a bijection, so nothing is lost or counted twice. Every lattice
configuration is the assembly of exactly one family of slab configurations.

This is a restatement, not an independent check: it falls out of `confEquiv` being built from two
Mathlib equivalences, and `measurePreserving_confEquiv` already has it. What it adds is the
identification — via `coe_confEquiv`, which is `rfl` — that the bijection is `regroup` and not some
other map that happens to be measure-preserving.

DERIVED: no numeral. -/
theorem regroup_bijective (τ : Fin d) :
    Function.Bijective (regroup (Ω := MassGap.SUN.SU N) (timeOf (d := d) (n := n) τ)) :=
  (confEquiv (Ω := MassGap.SUN.SU N) (timeOf (d := d) (n := n) τ)).toEquiv.bijective

/-- The kernel is strictly positive. A product of two exponentials, so the cyclic integrand never
vanishes and the denominator of `twoSlab_expect` is an integral of a positive function.

DERIVED: the `0` of `0 < ·` is positivity itself; the `t + 1` is `slabKernel`'s time step. -/
theorem slabKernel_pos (τ : Fin d) (β : ℝ) (t : Fin n)
    (A : SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N)
    (B : SlabIdx (d := d) (n := n) τ (t + 1) → MassGap.SUN.SU N) :
    0 < slabKernel (N := N) τ β t A B := by
  unfold slabKernel slabWeight
  positivity

end Controls

/-! ## Axiom footprints -/

#print axioms Block
#print axioms regroup
#print axioms regroup_apply
#print axioms regroup_restrict
#print axioms measurePreserving_sigmaUncurry
#print axioms confEquiv
#print axioms coe_confEquiv
#print axioms measurePreserving_confEquiv
#print axioms integral_regroup
#print axioms timeOf
#print axioms SlabIdx
#print axioms mem_slab_iff
#print axioms slabSupport
#print axioms mem_slabSupport
#print axioms slabSupport_eq
#print axioms card_le_two_of_slabSupport_univ
#print axioms fin_two_eq_or_eq_succ
#print axioms slabSupport_eq_univ_of_le_two
#print axioms slabSupport_eq_univ_iff
#print axioms slabSupport_ne_univ
#print axioms intra_support
#print axioms inter_support
#print axioms slabWeight
#print axioms latticeBoltz
#print axioms sysWilson_boltz
#print axioms partition_eq_integral_latticeBoltz
#print axioms corrNum_eq_integral
#print axioms latticeBoltz_eq_prod_slabWeight
#print axioms slabWeight_local
#print axioms patch
#print axioms regroup_patch_eq
#print axioms slabKernel
#print axioms slabWeight_regroup_eq_kernel
#print axioms slabVol
#print axioms partition_eq_cycleIntegral
#print axioms latticeExpect
#print axioms latticeExpect_eq
#print axioms expect_eq_cycleRatio
#print axioms twoSlab_expect
#print axioms prod_split_at
#print axioms cycle_kernel_prod_split
#print axioms regroup_bijective
#print axioms slabKernel_pos

end MassGap.SliceTrace
