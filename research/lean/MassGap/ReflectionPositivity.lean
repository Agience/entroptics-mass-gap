import Mathlib
import MassGap.WilsonReal

/-!
# MassGap.ReflectionPositivity — the MECHANISM of reflection positivity, proved

`Complete.wilson_reflection_positive_at` is an axiom, cited to Osterwalder–Seiler (*Gauge field
theories on a lattice*, Ann. Phys. **110** (1978) 440). A citation is a fine thing to stand on, but
it is worth knowing which half of the cited theorem is doing the work, because the two halves are of
very different difficulty and only one of them is hard.

WHAT REFLECTION POSITIVITY IS, MECHANICALLY. Split the links into a POSITIVE half `S` and a NEGATIVE
half `T`, disjoint, exchanged by a reflection `θ`. Reflection positivity says that an observable
paired with its own reflection has nonnegative expectation. The reason is not analytic: it is that
such a pairing is a SQUARE. If everything supported on the positive half integrates to some number,
the reflected copy integrates to the same number (the measure does not know which side is which), and
the two sides are independent (they read disjoint coordinates), so the product integrates to that
number squared.

That is `pairing_with_reflection_nonneg` below, and it is proved here with no axiom. What it needs
from the caller is exactly one thing: the observable-times-weight has to be WRITTEN in the paired
form `h(U|_S) · h((U∘θ)|_S)`.

SO WHAT IS ACTUALLY CITED. Putting the Wilson Boltzmann weight into that form is the cited content.
The action splits as `S₊ + S₋ + S_cross`, and the cross term — the plaquettes straddling the
reflection plane — does not factorise on its own; Osterwalder–Seiler expand `e^{-β S_cross}` into a
convergent sum of products, each term of the paired form, and conclude by summing nonnegatives. The
expansion is the theorem. The pairing-is-a-square step, which is what the expansion is FOR, is below.

WHY THIS DISTINCTION IS WORTH DRAWING. `entroptics-positivity` makes the same separation in a
different setting and finds it decisive there. It has two routes to its pairing identity: a
similarity `S K S⁻¹ = −K`, which leaves the weights REAL and does carry positivity, and an
ANTI-similarity `S K S⁻¹ = −conj(K)`, which restores the identity on an odd cycle and leaves a phase
behind. On an odd cycle only the second is available, so there the identity can be restored and the
positivity cannot — measured, the identity goes to `8e-14` while the sign deficit gets nine times
WORSE. Reading that back here: "the measure is invariant under the reflection" is the easy half and
is not by itself reflection positivity. The content is whether the weight can be written as a
pairing at all.

AT ZERO COUPLING there is no cross term, so the hypothesis is discharged outright and reflection
positivity is a theorem with nothing cited (`reflection_positive_at_zero`). That is the free case,
and it is the base the expansion perturbs around.

Foundational footprint only (`#print axioms` at the end). Build: `lake build MassGap.ReflectionPositivity`.
-/

namespace MassGap.ReflectionPositivity

open MeasureTheory MassGap.WilsonReal MassGap.CompactGauge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The product Haar measure on link configurations valued in `SU N`. -/
noncomputable abbrev vol (ι : Type) [Fintype ι] (N : ℕ) : Measure (ι → MassGap.SUN.SU N) :=
  Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))

/-- Relabelling links by a permutation, as a measurable equivalence of configurations.

The same construction as `LatticeGauge.reindex`, stated directly on `ι → SU N` so that this module
does not have to carry a `System` to talk about a reflection. -/
noncomputable def relabel (e : Equiv.Perm ι) :
    (ι → MassGap.SUN.SU N) ≃ᵐ (ι → MassGap.SUN.SU N) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι => MassGap.SUN.SU N) e).symm

@[simp] theorem relabel_apply (e : Equiv.Perm ι) (U : ι → MassGap.SUN.SU N) (l : ι) :
    relabel (N := N) e U l = U (e l) := rfl

/-- **Relabelling links preserves the product Haar measure.** Identical factors, so a permutation of
the index set is a symmetry of the product — the same fact `LatticeGauge.reindex_measurePreserving`
records, on the bare configuration type. -/
theorem relabel_measurePreserving (e : Equiv.Perm ι) :
    MeasurePreserving (relabel (N := N) e) (vol ι N) (vol ι N) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => MassGap.SUN.SU N) e) (vol ι N) (vol ι N) := by
    simpa using
      measurePreserving_piCongrLeft (μ := fun _ : ι => probHaar (MassGap.SUN.SU N)) e
  exact h.symm _

#print axioms relabel_measurePreserving

/-- **THE MECHANISM: a positive-half function paired with its own reflection integrates to a square.**

`h` is anything supported on the positive half `S` — in the application, an observable multiplied by
whatever part of the Boltzmann weight is supported there. `e : S ≃ T` is the reflection restricted to
that half, `hθ` saying it agrees with the global permutation `θ`. The conclusion is that the pairing

    ∫ h(U|_S) · h((U ∘ θ)|_S)  dvol

equals `(∫ h(U|_S))²`, hence is nonnegative — REFLECTION POSITIVITY, for any weight already written
in paired form.

Two facts carry it and neither is analytic: the two halves read disjoint coordinates, so the integral
factorises (`WilsonReal.block_integral_factor`); and the measure does not distinguish the halves, so
the two factors are equal (`relabel_measurePreserving`).

DERIVED: no numeric content whatsoever. The `0` in the conclusion is the statement. -/
theorem pairing_with_reflection_nonneg
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (e : S ≃ T)
    (hθ : ∀ i : S, ((e i : ι)) = θ (i : ι))
    (h : (S → MassGap.SUN.SU N) → ℝ) (hm : Measurable h) :
    (∫ U, h (fun i : S => U (i : ι)) * h (fun i : S => U (θ (i : ι))) ∂(vol ι N))
      = (∫ U, h (fun i : S => U (i : ι)) ∂(vol ι N)) ^ 2 := by
  -- the reflected copy, as a function of the NEGATIVE half alone
  set ψ : (T → MassGap.SUN.SU N) → ℝ := fun v => h (fun i : S => v (e i)) with hψ
  have hψm : Measurable ψ := hm.comp (measurable_pi_lambda _ fun i => measurable_pi_apply (e i))
  have hrw : ∀ U : ι → MassGap.SUN.SU N,
      h (fun i : S => U (θ (i : ι))) = ψ (fun i : T => U (i : ι)) := by
    intro U
    simp only [hψ]
    exact congrArg h (funext fun i => by rw [hθ i])
  have hfac := block_integral_factor (N := N) S T hST h ψ hm hψm
  have hmirror : (∫ U, ψ (fun i : T => U (i : ι)) ∂(vol ι N))
      = ∫ U, h (fun i : S => U (i : ι)) ∂(vol ι N) := by
    have hmp := relabel_measurePreserving (N := N) θ
    have := hmp.integral_comp' (fun U : ι → MassGap.SUN.SU N => h (fun i : S => U (i : ι)))
    calc (∫ U, ψ (fun i : T => U (i : ι)) ∂(vol ι N))
        = ∫ U, h (fun i : S => U (θ (i : ι))) ∂(vol ι N) := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun U => (hrw U).symm)
      _ = ∫ U, h (fun i : S => (relabel (N := N) θ U) (i : ι)) ∂(vol ι N) := by
          simp only [relabel_apply]
      _ = ∫ U, h (fun i : S => U (i : ι)) ∂(vol ι N) := this
  calc (∫ U, h (fun i : S => U (i : ι)) * h (fun i : S => U (θ (i : ι))) ∂(vol ι N))
      = ∫ U, h (fun i : S => U (i : ι)) * ψ (fun i : T => U (i : ι)) ∂(vol ι N) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun U => by simp only [hrw U])
    _ = (∫ U, h (fun i : S => U (i : ι)) ∂(vol ι N))
          * (∫ U, ψ (fun i : T => U (i : ι)) ∂(vol ι N)) := hfac
    _ = (∫ U, h (fun i : S => U (i : ι)) ∂(vol ι N)) ^ 2 := by rw [hmirror]; ring

#print axioms pairing_with_reflection_nonneg

/-- **Reflection positivity, in the form it is used: the pairing is nonnegative.** -/
theorem reflection_positive_of_paired
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (e : S ≃ T)
    (hθ : ∀ i : S, ((e i : ι)) = θ (i : ι))
    (h : (S → MassGap.SUN.SU N) → ℝ) (hm : Measurable h) :
    0 ≤ ∫ U, h (fun i : S => U (i : ι)) * h (fun i : S => U (θ (i : ι))) ∂(vol ι N) := by
  rw [pairing_with_reflection_nonneg S T hST θ e hθ h hm]
  exact sq_nonneg _

#print axioms reflection_positive_of_paired

/-- **A SUM of paired products is nonnegative, given nonnegative coefficients.**

This is the shape the cited expansion produces, and adding it narrows what is cited. Osterwalder-Seiler
expand `exp(-beta S_cross)` over the straddling plaquettes into a convergent sum

    sum_k  c_k * g_k(U|_+) * g_k((U . theta)|_+)

and conclude by summing nonnegatives. The summing is here, proved: each term is a nonnegative multiple
of a square by `pairing_with_reflection_nonneg`, and a finite sum of nonnegatives is nonnegative.

What that leaves cited is no longer "reflection positivity holds" but the narrower and far more
checkable "the expansion exists with nonnegative coefficients". The difference matters because the
second is a statement about characters of a compact group, where the coefficients are known, and the
first is a statement about the theory.

Stated for a FINITE index set. The cited expansion is an infinite convergent sum; a finite truncation
of it is what a lattice with finitely many straddling plaquettes and a convergent character expansion
produces at each order, and the limit is the analytic half that remains outside. -/
theorem reflection_positive_of_expansion
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (e : S ≃ T)
    (hθ : ∀ i : S, ((e i : ι)) = θ (i : ι))
    {K : Type} [Fintype K] (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (g : K → (S → MassGap.SUN.SU N) → ℝ) (hg : ∀ k, Measurable (g k))
    (hint : ∀ k, Integrable
      (fun U => g k (fun i : S => U (i : ι)) * g k (fun i : S => U (θ (i : ι)))) (vol ι N))
    (F : (ι → MassGap.SUN.SU N) → ℝ)
    (hF : ∀ U, F U = ∑ k, c k *
      (g k (fun i : S => U (i : ι)) * g k (fun i : S => U (θ (i : ι))))) :
    0 ≤ ∫ U, F U ∂(vol ι N) := by
  have hrw : (∫ U, F U ∂(vol ι N))
      = ∑ k, c k * ∫ U, g k (fun i : S => U (i : ι)) * g k (fun i : S => U (θ (i : ι)))
          ∂(vol ι N) := by
    simp_rw [hF]
    rw [integral_finset_sum _ (fun k _ => (hint k).const_mul (c k))]
    exact Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
  rw [hrw]
  refine Finset.sum_nonneg (fun k _ => mul_nonneg (hc k) ?_)
  rw [pairing_with_reflection_nonneg S T hST θ e hθ (g k) (hg k)]
  exact sq_nonneg _

#print axioms reflection_positive_of_expansion

/-- **At zero coupling it is unconditional.**

With `β = 0` the Boltzmann weight is `1`, so there is no cross term to expand and the observable
alone is the paired function: any observable of the positive half, paired with its own reflection, has
nonnegative expectation under the bare product Haar measure. Nothing is cited here.

This is the base the Osterwalder–Seiler expansion perturbs around, and it says the axiom's SHAPE is
right: the quantity asserted nonnegative really is nonnegative in the case where the hard half is
absent. -/
theorem reflection_positive_at_zero
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (e : S ≃ T)
    (hθ : ∀ i : S, ((e i : ι)) = θ (i : ι))
    (O : (S → MassGap.SUN.SU N) → ℝ) (hO : Measurable O) :
    0 ≤ ∫ U, O (fun i : S => U (i : ι)) * O (fun i : S => U (θ (i : ι))) ∂(vol ι N) :=
  reflection_positive_of_paired S T hST θ e hθ O hO

#print axioms reflection_positive_at_zero

/-! ## What the cited expansion has to handle: the action splits, and the cross term is what is left

`pairing_with_reflection_nonneg` needs the observable-times-weight WRITTEN in paired form. Getting the
Wilson weight there is the cited content, and it is worth making precise what "there" means, because
the first two thirds of it are elementary and only the last third is Osterwalder--Seiler.

Split the plaquettes by where their boundary words live. A plaquette entirely inside the positive
half contributes a term that depends only on the positive links; one entirely inside the negative
half, only on the negative; and the rest -- those straddling the reflection plane -- are the CROSS
term. So

    S(U) = S_+(U|_+) + S_-(U|_-) + S_cross(U)

and `exp(-beta S)` factorises into `g(U|_+) * g'(U|_-) * exp(-beta S_cross)`. The first two factors
are already of the paired shape. The cross term is not, and expanding `exp(-beta S_cross)` into a
convergent sum of paired products is the theorem that is cited.

THE SUBSTANTIVE STEP HERE IS LOCALITY, not the partition. Splitting a finite sum by a partition is
`Finset.sum_filter_add_sum_filter_not` and says nothing. What has content is that a plaquette's
holonomy READS ONLY THE LINKS IN ITS OWN BOUNDARY WORD -- `hol_congr_on_support` -- so a term indexed
by a plaquette supported in the positive half really is a function of the positive links alone, and
not merely written next to them.
-/

/-- **A plaquette's holonomy reads only the links in its own boundary word.**

The locality on which every splitting argument rests. Two configurations agreeing on the links the
word names have the same holonomy, whatever they do elsewhere.

DERIVED: nothing numeric. This is congruence of an ordered product under pointwise equality of its
factors. -/
theorem hol_congr_on_support {L P : Type} [MeasurableSpace (MassGap.SUN.SU N)]
    (bd : P → List (L × Bool)) (p : P) (U V : L → MassGap.SUN.SU N)
    (h : ∀ l ∈ (bd p).map Prod.fst, U l = V l) :
    MassGap.WilsonLattice.wilsonHol bd p U = MassGap.WilsonLattice.wilsonHol bd p V := by
  unfold MassGap.WilsonLattice.wilsonHol
  congr 1
  refine List.map_congr_left ?_
  intro lo hlo
  have : U lo.1 = V lo.1 := h lo.1 (List.mem_map_of_mem hlo)
  rw [this]

#print axioms hol_congr_on_support

/-- **So the action splits by any partition of the plaquettes**, and each piece is a function of the
links its own plaquettes read.

Stated as the plain sum split; the content is `hol_congr_on_support` above, which is what makes the
`A`-indexed piece a function of `U` restricted to the links `A` names rather than merely a sum
written over `A`. -/
theorem action_split {L P : Type} [Fintype L] [Fintype P] [DecidableEq P]
    (bd : P → List (L × Bool)) (φ : MassGap.SUN.SU N → ℝ) (A : Finset P)
    (U : L → MassGap.SUN.SU N) :
    ∑ p, φ (MassGap.WilsonLattice.wilsonHol bd p U)
      = (∑ p ∈ Finset.univ.filter (fun p => p ∈ A), φ (MassGap.WilsonLattice.wilsonHol bd p U))
        + ∑ p ∈ Finset.univ.filter (fun p => p ∉ A), φ (MassGap.WilsonLattice.wilsonHol bd p U) :=
  (Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ A) _).symm

#print axioms action_split

/-- **The half-action is a function of its half's links alone.**

`hol_congr_on_support` lifted from one plaquette to a set of them: if every plaquette in `A` draws its
boundary word from `S`, then `A`'s contribution to the action is unchanged by anything outside `S`.
This is the statement "`S_+` depends only on `U|_+`" that the splitting picture assumes and that makes
`exp(-beta S_+)` a candidate for the `h` of `pairing_with_reflection_nonneg`. -/
theorem action_on_congr_of_support {L P : Type} [Fintype L] [Fintype P]
    (bd : P → List (L × Bool)) (φ : MassGap.SUN.SU N → ℝ) (A : Finset P) (S : Finset L)
    (hsupp : ∀ p ∈ A, ∀ l ∈ (bd p).map Prod.fst, l ∈ S)
    (U V : L → MassGap.SUN.SU N) (h : ∀ l ∈ S, U l = V l) :
    (∑ p ∈ A, φ (MassGap.WilsonLattice.wilsonHol bd p U))
      = ∑ p ∈ A, φ (MassGap.WilsonLattice.wilsonHol bd p V) :=
  Finset.sum_congr rfl fun p hp => by
    rw [hol_congr_on_support bd p U V (fun l hl => h l (hsupp p hp l hl))]

#print axioms action_on_congr_of_support

end MassGap.ReflectionPositivity
