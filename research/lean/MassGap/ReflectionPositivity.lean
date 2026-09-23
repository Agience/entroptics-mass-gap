import Mathlib
import MassGap.WilsonReal

/-!
# MassGap.ReflectionPositivity — paired integrals over product Haar, and the locality that feeds them

Everything here is stated over `vol ι N`, the product Haar measure on configurations
`ι → MassGap.SUN.SU N` for a finite link index `ι`. A reflection is a permutation `θ : Equiv.Perm ι`
together with two disjoint `Finset`s `S`, `T` and an equivalence `e : S ≃ T` agreeing with `θ` on
`S`.

`pairing_with_reflection_nonneg` is the core identity: for a measurable `h` on the `S`-coordinates,

    ∫ h(U|_S) · h((U ∘ θ)|_S) dvol = (∫ h(U|_S) dvol)²

Two inputs carry it. `WilsonReal.block_integral_factor` factorises the integral because the two
halves read disjoint coordinates, and `relabel_measurePreserving` — the permutation invariance of a
product of identical factors — makes the two resulting integrals equal.
`reflection_positive_of_paired` reads off `0 ≤` that integral, `reflection_positive_at_zero` restates
it with the function named `O`, and `reflection_positive_of_expansion` extends it to a finite sum
`∑ k, c k * (g k (U|_S) * g k ((U ∘ θ)|_S))` with nonnegative coefficients.

The remaining three theorems are the locality facts a splitting argument rests on.
`hol_congr_on_support`: a plaquette's holonomy depends only on the links its boundary word names.
`action_split`: the total action splits over a `Finset` of plaquettes and its complement, by
`Finset.sum_filter_add_sum_filter_not`. `action_on_congr_of_support`: if every plaquette of `A` draws
its boundary word from `S`, then `A`'s contribution is unchanged by configurations outside `S`.

Scope: the hypothesis of `pairing_with_reflection_nonneg` is that the integrand is already written in
the paired form `h(U|_S) · h((U ∘ θ)|_S)`; no statement here puts a Wilson Boltzmann weight into that
form, and no coupling `β` appears anywhere in this file. `reflection_positive_of_expansion` is stated
for a `Fintype` index `K`, so it covers finite sums only. `Complete.wilson_reflection_positive_at`,
the axiom cited to Osterwalder–Seiler (Ann. Phys. 110 (1978) 440), is not used or discharged here.
Axiom footprint is recorded by the `#print axioms` line after each declaration.
-/

namespace MassGap.ReflectionPositivity

open MeasureTheory MassGap.WilsonReal MassGap.CompactGauge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The product Haar measure on configurations `ι → MassGap.SUN.SU N`, as
`Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))` over a finite index type `ι`. Every factor
is the same normalised Haar measure, which is what makes index permutations measure-preserving.

DERIVED: no numeral appears in the statement. -/
noncomputable abbrev vol (ι : Type) [Fintype ι] (N : ℕ) : Measure (ι → MassGap.SUN.SU N) :=
  Measure.pi (fun _ : ι => probHaar (MassGap.SUN.SU N))

/-- The measurable equivalence of configurations induced by a permutation `e : Equiv.Perm ι`, as
`(MeasurableEquiv.piCongrLeft _ e).symm`. By `relabel_apply` it acts as `relabel e U l = U (e l)`.

This is the same construction as `LatticeGauge.reindex`, stated directly on `ι → MassGap.SUN.SU N`
so the module needs no `System` to speak of a reflection.

DERIVED: no numeral appears in the statement. -/
noncomputable def relabel (e : Equiv.Perm ι) :
    (ι → MassGap.SUN.SU N) ≃ᵐ (ι → MassGap.SUN.SU N) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι => MassGap.SUN.SU N) e).symm

@[simp] theorem relabel_apply (e : Equiv.Perm ι) (U : ι → MassGap.SUN.SU N) (l : ι) :
    relabel (N := N) e U l = U (e l) := rfl

/-- `relabel e` is measure-preserving from `vol ι N` to itself, for every `e : Equiv.Perm ι`. The
factors of the product are identical copies of `probHaar`, so `measurePreserving_piCongrLeft`
applies and `MeasurePreserving.symm` transports it to the inverse equivalence.

Scope: this is permutation invariance of the product measure. It uses no property of
`MassGap.SUN.SU N` beyond carrying `probHaar`, and is the same fact
`LatticeGauge.reindex_measurePreserving` records on a `System`.

DERIVED: no numeral appears in the statement. -/
theorem relabel_measurePreserving (e : Equiv.Perm ι) :
    MeasurePreserving (relabel (N := N) e) (vol ι N) (vol ι N) := by
  have h : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : ι => MassGap.SUN.SU N) e) (vol ι N) (vol ι N) := by
    simpa using
      measurePreserving_piCongrLeft (μ := fun _ : ι => probHaar (MassGap.SUN.SU N)) e
  exact h.symm _

#print axioms relabel_measurePreserving

/-- For disjoint `Finset`s `S`, `T`, a permutation `θ : Equiv.Perm ι`, an equivalence `e : S ≃ T`
agreeing with `θ` on `S`, and a measurable `h : (S → MassGap.SUN.SU N) → ℝ`,

    ∫ U, h (U|_S) * h ((U ∘ θ)|_S) ∂(vol ι N)  =  (∫ U, h (U|_S) ∂(vol ι N)) ^ 2

The proof defines `ψ v := h (fun i : S => v (e i))` on the `T`-coordinates, rewrites the second
factor as `ψ (U|_T)` using `hθ`, factorises with `WilsonReal.block_integral_factor` on the disjoint
blocks, and identifies `∫ ψ (U|_T)` with `∫ h (U|_S)` through `relabel_measurePreserving` at `θ`.

Scope: the conclusion is an equality to a square, not an inequality — nonnegativity is read off it
in `reflection_positive_of_paired`. The integrand must already be of the paired shape; nothing here
puts a Boltzmann weight into that shape, and no coupling appears. Integrability of the product is
not hypothesised, so degenerate cases fall to Lean's junk value for a non-integrable integral.

DERIVED: the exponent `2` is the square on the right, which is what the two factors combine to. No
other numeral appears in the statement. -/
theorem pairing_with_reflection_nonneg
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (e : S ≃ T)
    (hθ : ∀ i : S, ((e i : ι)) = θ (i : ι))
    (h : (S → MassGap.SUN.SU N) → ℝ) (hm : Measurable h) :
    (∫ U, h (fun i : S => U (i : ι)) * h (fun i : S => U (θ (i : ι))) ∂(vol ι N))
      = (∫ U, h (fun i : S => U (i : ι)) ∂(vol ι N)) ^ 2 := by
  -- the reflected copy, as a function of the negative half alone
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

/-- `0 ≤ ∫ U, h (U|_S) * h ((U ∘ θ)|_S) ∂(vol ι N)`, under the same hypotheses as
`pairing_with_reflection_nonneg`. The proof rewrites by that identity and applies `sq_nonneg`.

DERIVED: `0` is the lower bound on the integral. No other numeral appears in the statement; the
square has been rewritten away. -/
theorem reflection_positive_of_paired
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (e : S ≃ T)
    (hθ : ∀ i : S, ((e i : ι)) = θ (i : ι))
    (h : (S → MassGap.SUN.SU N) → ℝ) (hm : Measurable h) :
    0 ≤ ∫ U, h (fun i : S => U (i : ι)) * h (fun i : S => U (θ (i : ι))) ∂(vol ι N) := by
  rw [pairing_with_reflection_nonneg S T hST θ e hθ h hm]
  exact sq_nonneg _

#print axioms reflection_positive_of_paired

/-- If `F` is pointwise equal to a finite sum `∑ k, c k * (g k (U|_S) * g k ((U ∘ θ)|_S))` with
`0 ≤ c k`, each `g k` measurable and each paired product integrable, then
`0 ≤ ∫ U, F U ∂(vol ι N)`.

The proof rewrites `F` by `hF`, exchanges sum and integral with `integral_finset_sum` using the
integrability hypothesis, pulls out each `c k` with `integral_const_mul`, and applies
`pairing_with_reflection_nonneg` and `sq_nonneg` to each term before `Finset.sum_nonneg`.

Scope: `K` is a `Fintype`, so the sum is finite — an infinite convergent expansion is not covered,
and neither is any question of exchanging a limit with the integral. The existence of such an
expansion, and the nonnegativity of its coefficients, are hypotheses `hF` and `hc`.

DERIVED: `0` occurs twice, as the lower bound on each coefficient `c k` and as the lower bound on the
integral of `F`. No other numeral appears in the statement. -/
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

/-- `0 ≤ ∫ U, O (U|_S) * O ((U ∘ θ)|_S) ∂(vol ι N)` for any measurable `O` on the `S`-coordinates,
against the bare product Haar measure `vol ι N`.

Scope: this is `reflection_positive_of_paired` with the function renamed, and the two statements are
identical. No coupling and no Boltzmann weight appear in it: the measure is product Haar, which is
the `β = 0` case, and the observable itself plays the role of the paired function. The proof is that
 theorem applied directly.

DERIVED: `0` is the lower bound on the integral. No other numeral appears in the statement. -/
theorem reflection_positive_at_zero
    (S T : Finset ι) (hST : Disjoint S T) (θ : Equiv.Perm ι) (e : S ≃ T)
    (hθ : ∀ i : S, ((e i : ι)) = θ (i : ι))
    (O : (S → MassGap.SUN.SU N) → ℝ) (hO : Measurable O) :
    0 ≤ ∫ U, O (fun i : S => U (i : ι)) * O (fun i : S => U (θ (i : ι))) ∂(vol ι N) :=
  reflection_positive_of_paired S T hST θ e hθ O hO

#print axioms reflection_positive_at_zero

/-! ## Locality of the holonomy, and the resulting action split

The three theorems below are what lets a sum over plaquettes be regarded as a function of a subset of
the links. `hol_congr_on_support` is the locality itself: a plaquette's holonomy depends only on the
links its own boundary word names. `action_split` partitions the plaquette sum over a `Finset` and
its complement — that step is `Finset.sum_filter_add_sum_filter_not` and carries no geometry.
`action_on_congr_of_support` combines the two: a block of plaquettes whose boundary words lie inside
`S` contributes a quantity determined by `U` restricted to `S`.

That restriction property is what a function has to satisfy to be the `h` of
`pairing_with_reflection_nonneg`. Writing a Wilson Boltzmann weight in the paired form that theorem
requires is not done in this file.
-/

/-- For a boundary-word assignment `bd : P → List (L × Bool)`, a plaquette `p`, and configurations
`U`, `V` agreeing at every link occurring in `(bd p).map Prod.fst`,
`wilsonHol bd p U = wilsonHol bd p V`. The proof rewrites the mapped list entrywise with
`List.map_congr_left`; the ordered product is then the same list.

Scope: `L` and `P` are arbitrary types and `bd` is arbitrary — no lattice geometry is used. Agreement
is required only on the links the word names, not on their orientations or on any neighbourhood.

DERIVED: no numeral appears in the statement. -/
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

/-- `∑ p, φ (wilsonHol bd p U)` equals the sum over `{p | p ∈ A}` plus the sum over `{p | p ∉ A}`,
for any `A : Finset P`. It is `Finset.sum_filter_add_sum_filter_not` reversed.

Scope: this is the partition of a finite sum and nothing more — it says nothing about which links
each piece reads. That property is `action_on_congr_of_support`, which uses
`hol_congr_on_support`.

DERIVED: no numeral appears in the statement. -/
theorem action_split {L P : Type} [Fintype L] [Fintype P] [DecidableEq P]
    (bd : P → List (L × Bool)) (φ : MassGap.SUN.SU N → ℝ) (A : Finset P)
    (U : L → MassGap.SUN.SU N) :
    ∑ p, φ (MassGap.WilsonLattice.wilsonHol bd p U)
      = (∑ p ∈ Finset.univ.filter (fun p => p ∈ A), φ (MassGap.WilsonLattice.wilsonHol bd p U))
        + ∑ p ∈ Finset.univ.filter (fun p => p ∉ A), φ (MassGap.WilsonLattice.wilsonHol bd p U) :=
  (Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ A) _).symm

#print axioms action_split

/-- If every plaquette of `A` draws every link of its boundary word from `S`, and `U`, `V` agree on
all of `S`, then `∑ p ∈ A, φ (wilsonHol bd p U) = ∑ p ∈ A, φ (wilsonHol bd p V)`. It is
`hol_congr_on_support` applied under `Finset.sum_congr`.

This is the statement that `A`'s contribution to the action is determined by `U` restricted to `S`,
which is what a function must satisfy to serve as the `h` of `pairing_with_reflection_nonneg`.

Scope: `φ` is an arbitrary real-valued function on the group; no exponential, coupling or Boltzmann
weight is involved.

DERIVED: no numeral appears in the statement. -/
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
