import MassGap.CompactGauge
import MassGap.SUN
import MassGap.WilsonAction
import MassGap.WilsonHypercubic

/-!
# MassGap.SliceTrace — regrouping the link measure along the slab partition

Regroups `Measure.pi` over `Link d n` along the slab partition, and records the slab support and the
Wilson weight written on the link type.

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

**The slab support** (`slabSupport`): the links at times `t` and `t+1`. It is every link when
`n ≤ 2`, and `slabSupport_eq_univ_iff` is sharp in both directions, so the support is a proper subset
exactly from `n ≥ 3` (`slabSupport_ne_univ`).

**The Wilson weight on the link type** (`latticeBoltz`, `partition_eq_integral_latticeBoltz`,
`corrNum_eq_integral`, `latticeExpect`), and `prod_split_at`, which splits a product over `Fin n` at a
cut `k`.

## Scope

* No kernel is defined here and no cyclic integral is formed.
* No spectrum appears, and no bound on `λ_max`.
* No gauge fixing is used.
* `β` is `sysWilson`'s coupling. The ordered-`Plaq` sum counts each plane twice, so it is half the
  coupling of a formulation summing each plane once.

Build: `python code/lean_build.py build MassGap.SliceTrace`.
-/

namespace MassGap.SliceTrace

open MeasureTheory
open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.WilsonHypercubic MassGap.CompactGauge

/-! ## Part 0 — regrouping a finite product measure along the fibres of a block map

This is stated for an arbitrary finite index type and an arbitrary block map, because nothing about
it is about the lattice. -/

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

/-- The Fubini step. The product measure over the index type is the image, under assembly, of the
product over blocks of the product measures within each block.

`OddLagSplit.join3` / `OddLagSplit.integral_three_block` are this for a three-block split; this is
the version indexed by an arbitrary finite `κ`, which is what a `Fin n`-indexed slab decomposition
needs.

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

The block map is the time coordinate of a link. -/

section Slab

variable {d n N : ℕ} [NeZero n]

/-- The **time of a link**: the `τ`-coordinate of its base site. This is the block map.

DERIVED: no numeral. -/
def timeOf (τ : Fin d) (l : Link d n) : Fin n := l.2 τ

/-- The **slab index at time `t`**: the links of the lattice whose base site sits at time `t`.
These are the spatial links of slice `t` together with the axis links leaving it.

DERIVED: no numeral. -/
abbrev SlabIdx (τ : Fin d) (t : Fin n) : Type := Block (timeOf (d := d) (n := n) τ) t

omit [NeZero n] in

/-- The **support of the slab based at `t`**: the links at time `t` together with those at time
`t+1`.

DERIVED: the `1` is one time step — the next slice, `Fin n` addition, which wraps. It is an index
step, not a spacing. -/
def slabSupport (τ : Fin d) (t : Fin n) : Finset (Link d n) :=
  Finset.univ.filter (fun l : Link d n => timeOf τ l = t ∨ timeOf τ l = t + 1)

/-- Membership in the slab support unfolded.

DERIVED: the `1` is `slabSupport`'s own time step — one slice on, `Fin n` addition. -/
theorem mem_slabSupport {τ : Fin d} {t : Fin n} {l : Link d n} :
    l ∈ slabSupport τ t ↔ (timeOf τ l = t ∨ timeOf τ l = t + 1) := by
  simp [slabSupport]

/-- Control: a full support forces a short torus. If the slab support is the whole link set then
`Fin n` has at most two elements, so a locality claim on the support degenerates to `U = V`
everywhere and carries nothing. The converse is `slabSupport_eq_univ_of_le_two`;
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
a locality claim on the support says nothing. At `n = 1` the times are a subsingleton; at `n = 2` every time is
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
at most two. Below that threshold a locality claim on the support is the tautology `U = V → ⋯`; from
`n ≥ 3` it is a locality statement.

DERIVED: the `2` is the two times `{t, t+1}` a slab spans. -/
theorem slabSupport_eq_univ_iff (τ : Fin d) (t : Fin n) :
    slabSupport τ t = Finset.univ ↔ n ≤ 2 :=
  ⟨card_le_two_of_slabSupport_univ τ t, fun h => slabSupport_eq_univ_of_le_two h τ t⟩

/-- Control: from `n ≥ 3` the support is a proper subset. The contrapositive of the previous
theorem, and the statement that a locality claim on the support is real rather than a tautology.

DERIVED: the `3` is `2 + 1`, the first extent at which a third time exists; it is read off
`card_le_two_of_slabSupport_univ` and is not chosen. -/
theorem slabSupport_ne_univ (h3 : 3 ≤ n) (τ : Fin d) (t : Fin n) :
    slabSupport τ t ≠ Finset.univ := by
  intro h
  have := card_le_two_of_slabSupport_univ τ t h
  omega

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

end Slab

/-! ## Part 2 — the two-slab patch, the slab volume and the product split -/

section Kernel

variable {d n N : ℕ} [NeZero n]

/-- A two-slab configuration, extended by the identity. Given configurations `A` of slab `t` and
`B` of slab `t+1`, the configuration that is `A` on slab `t`, `B` on slab `t+1`, and the identity
element everywhere else. Only the two named slabs are read on the slab support
(`regroup_patch_eq`).

The order of the two tests matters only when `t + 1 = t`, i.e. `n = 1`; there the two slabs are the
same slab and `A` wins, which is consistent because a one-slice torus has `W 0 = W (0+1)`.

DERIVED: the `1` chosen as the filler value is the group identity, and it is never read — any element
would do. The `t + 1` is `slabSupport`'s time step. -/
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

/-- The **product of Haar measures over the slab configuration spaces**. Each slab carries the product Haar measure over its own links.

DERIVED: no numeral. -/
noncomputable def slabVol (τ : Fin d) :
    Measure (∀ t : Fin n, SlabIdx (d := d) (n := n) τ t → MassGap.SUN.SU N) :=
  Measure.pi fun t : Fin n =>
    Measure.pi fun _ : SlabIdx (d := d) (n := n) τ t => probHaar (MassGap.SUN.SU N)

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

omit [NeZero n] in
/-- A product over `Fin n` splits at `k` into the factors below `k` and the rest. A plain `Finset`
fact about an arbitrary real function.

DERIVED: no numeral; `k` is the caller's cut and the comparison is on `Fin n`'s own value. -/
theorem prod_split_at (f : Fin n → ℝ) (k : Fin n) :
    ∏ t : Fin n, f t
      = (∏ t ∈ Finset.univ.filter (fun t : Fin n => (t : ℕ) < (k : ℕ)), f t)
        * ∏ t ∈ Finset.univ.filter (fun t : Fin n => ¬ ((t : ℕ) < (k : ℕ))), f t :=
  (Finset.prod_filter_mul_prod_filter_not Finset.univ _ f).symm

end Kernel

/-! ## Part 3 — controls

A fact about the regrouping. The locality control is `slabSupport_ne_univ`, up in Part 1 with the
object it is about. -/

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
#print axioms slabSupport
#print axioms mem_slabSupport
#print axioms card_le_two_of_slabSupport_univ
#print axioms fin_two_eq_or_eq_succ
#print axioms slabSupport_eq_univ_of_le_two
#print axioms slabSupport_eq_univ_iff
#print axioms slabSupport_ne_univ
#print axioms latticeBoltz
#print axioms sysWilson_boltz
#print axioms partition_eq_integral_latticeBoltz
#print axioms corrNum_eq_integral
#print axioms patch
#print axioms regroup_patch_eq
#print axioms slabVol
#print axioms latticeExpect
#print axioms latticeExpect_eq
#print axioms prod_split_at
#print axioms regroup_bijective

end MassGap.SliceTrace
