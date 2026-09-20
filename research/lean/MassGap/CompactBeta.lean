import Mathlib
import MassGap.Complete
import MassGap.ContactDominance
import MassGap.WilsonHypercubic

/-!
# The coupling quantifier swap on a COMPACT interval, and what it costs

`WilsonModel.existence_and_gap_of_substrate` consumes `∃ B, ∀ N β, d2At N β ≤ B` — a bound uniform in
BOTH the aperture `N` and the coupling `β`. `ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity`
proves the swap `(∀ β, ∃ B, ∀ N) → (∃ B, ∀ N β)` is not formally valid, by exhibiting `sepRead`.

This file asks what extra hypothesis makes the swap valid on a compact coupling interval, proves it,
and then measures what supplying that hypothesis would cost.

## The positive result

`jointUniform_of_pointwise_of_equicontinuous`: for ANY family `f : ι → ℝ → ℝ` and any COMPACT `K ⊆ ℝ`,

    (∀ β ∈ K, ∃ B, ∀ i, f i β ≤ B)          -- index-uniform bound at each coupling
  + (∀ ε > 0, ∃ δ > 0, ∀ i, ∀ β₁ β₂ ∈ K, |β₁-β₂| < δ → |f i β₁ - f i β₂| < ε)   -- equicontinuity
                                             --  UNIFORM IN THE INDEX
  → ∃ B, ∀ i, ∀ β ∈ K, f i β ≤ B

It is stated about an abstract family, not about the Wilson measure, so the content is visible: a
finite subcover of `K` by `δ`-balls, the index-uniform bound at each centre, and `+ε` to move off the
centre. `Set.Icc` is the instance (`jointUniform_on_Icc`, via `isCompact_Icc`).

BOTH hypotheses are load-bearing, and both failures are exhibited rather than asserted:

* `equicontinuity_is_load_bearing` — `spikeFam n β = if β = 1/(n+1) then n else 0` is index-uniformly
  bounded at every point of `Icc 0 1` and unbounded over the family on it. Compactness alone gives
  nothing.
* `compactness_is_load_bearing` — `rampFam n β = min β n` is 1-Lipschitz in `β` uniformly in `n`,
  hence equicontinuous, is bounded at each `β`, and is unbounded over the family on `Set.univ`.

## Why the no-go survives, and it is not close

`sepRead N β = if (N:ℝ) ≤ β then midRead N else contactRead N` fails the new theorem's hypotheses in
two INDEPENDENT ways, so no contradiction is available:

* `sepMoment_jointUniform_on_Icc` — on EVERY compact interval `Icc a b`, `sepRead`'s moments are
  already bounded uniformly in both arguments, by `((|a|+|b|+1)/2)²`. The counterexample satisfies the
  new theorem's CONCLUSION on every compact set; it is a statement about `β → ∞` and nothing else.
* `sepMoment_not_equicontinuous_on_Icc` — it also fails the equicontinuity hypothesis on `Icc 0 1`,
  where it jumps by `1` at `β = 1`. `sepMoment_modulus_degrades` gives the sharp form: at aperture
  `N = 2k+1` the jump is `(k+1)²`, so the modulus of continuity degrades like `N²` in the aperture.
  That second failure is the one that matters for the reduction, and it is exactly the failure a real
  bound has to rule out.

## What the reduction costs — the verdict

`equicontinuousInBeta_of_uniform_lipschitz` says the hypothesis is supplied by an
APERTURE-UNIFORM Lipschitz constant for `β ↦ d2At N β`. `WilsonAnalytic.wilsonSystem_expect_hasDerivAt`
gives the exact derivative `d⟨O⟩/dβ = −Cov(O,S)`, so such a constant is exactly a bound on that
covariance holding uniformly in the aperture. Two facts settle what that costs:

* `clay_covariance_constant_not_aperture_uniform` — `wilsonCorrAt N β = WilsonBridge.corrClay (N+1) β`
  lives on the four-dimensional periodic lattice of extent `N+1`, whose plaquette count is
  `4·4·(N+1)^4 = 16(N+1)^4` (`WilsonHypercubic.card_plaq`). The only UNCONDITIONAL covariance bound in
  the tree is `WilsonAnalytic.cov_bound_extensive`, `|Cov(O,S)| ≤ 4M·#Plaq`; here the aperture IS the
  extent, so that constant grows like `N⁴` and is not aperture-uniform by any margin. The
  volume-free alternatives — `cov_bound_local`, `cov_bound_summable` and their Lipschitz corollaries
  — are conditional on clustering, which is the open input.
* `profile_to_moment_not_uniformly_lipschitz` — and even a volume-free bound on the individual
  correlators would not be enough. `d2At` is the NORMALISED circular second moment, so a sup-norm
  perturbation of size `t` in the raw profile moves it by `t/(1+t)·((N+1)/2)²`: the map from the
  correlation to `d2At` is itself not uniformly Lipschitz in the aperture. The probe's own total
  mass is `1 + t`, so this is not the denominator vanishing — the amplification is the weight
  `circLag²` the moment applies to a lag the aperture has just made available, and a lower bound on
  the total mass does not touch it.

So the compact-interval route does NOT reduce the open problem. It relocates it: from "a bound
uniform in `N` and `β`" to "a modulus of continuity in `β` uniform in `N`", and the second is
available only from the clustering estimate the first was waiting on.

DERIVED: no numeral in this file is a magnitude. `1` and `1/2` are the `ε` at which a failure is
exhibited, `4` is the problem's dimension, `16 = 4·4` is `card_plaq`'s own arithmetic at that
dimension, and `(N+1)/2` is half the periodic extent.
-/

namespace MassGap.CompactBeta

/-! ## The three properties, named -/

/-- A bound uniform in the family index, at each point of `K` separately. The bound may depend on the
point — this is the APERTURE half of the substrate hypothesis when `ι = ℕ` is the aperture. -/
def PointwiseUniform {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∀ β ∈ K, ∃ B : ℝ, ∀ i, f i β ≤ B

/-- One bound serving every index and every point of `K` — the substrate hypothesis, restricted
to `K`. -/
def JointUniform {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∃ B : ℝ, ∀ i, ∀ β ∈ K, f i β ≤ B

/-- Equicontinuity in the coupling, UNIFORM IN THE INDEX: one `δ` serves every member of the family.
This is the extra hypothesis, and the uniformity in `i` is the whole of its content — without it each
member is merely continuous, which every member of `sepRead`'s family already is away from its own
jump.

DERIVED: the two `0`s are the POSITIVITY conditions of the ε–δ definition of continuity, not
magnitudes: `ε` is universally quantified over the positive reals and `δ` existentially, so no value
of either is named and no scale is set. The definition would read identically for any family of real
functions on any subset of `ℝ`. -/
def EquicontinuousInBeta {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ β₁ ∈ K, ∀ β₂ ∈ K, |β₁ - β₂| < δ → |f i β₁ - f i β₂| < ε

/-! ## The swap, on a compact set -/

/-- **THE QUANTIFIER SWAP IS VALID ON A COMPACT SET, GIVEN INDEX-UNIFORM EQUICONTINUITY.**

A pointwise index-uniform bound plus equicontinuity uniform in the index plus compactness gives a
bound uniform in both. No property of the Wilson measure is used and none can be: the statement is
about an arbitrary family of real functions.

The argument is the finite subcover and nothing else. Take `δ` for `ε = 1`; the `δ`-balls about the
points of `K` cover `K`; compactness extracts finitely many centres; each centre carries its own
index-uniform bound; the maximum of those finitely many bounds plus `1` serves everywhere, because
every point of `K` is within `δ` of a chosen centre.

DERIVED: the `1` is the `ε` the argument is run at, and it is arbitrary — any positive value gives
the same conclusion with `B` shifted by it. It is not a magnitude. -/
theorem jointUniform_of_pointwise_of_equicontinuous {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hpt : PointwiseUniform f K) (heq : EquicontinuousInBeta f K) :
    JointUniform f K := by
  classical
  obtain ⟨δ, hδ, hδ'⟩ := heq 1 one_pos
  -- the pointwise bounds as a TOTAL function of the centre, so a finite maximum can be taken
  have hpt' : ∀ β : ℝ, ∃ B : ℝ, ∀ i, β ∈ K → f i β ≤ B := by
    intro β
    by_cases hβ : β ∈ K
    · obtain ⟨B, hB⟩ := hpt β hβ
      exact ⟨B, fun i _ => hB i⟩
    · exact ⟨0, fun i h => absurd h hβ⟩
  choose g hg using hpt'
  have hcover : K ⊆ ⋃ c ∈ K, Set.Ioo (c - δ) (c + δ) := by
    intro x hx
    exact Set.mem_biUnion hx (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  obtain ⟨t, htK, htfin, htcov⟩ := hK.elim_finite_subcover_image (fun c _ => isOpen_Ioo) hcover
  obtain ⟨M, hM⟩ := (htfin.image g).bddAbove
  refine ⟨M + 1, fun i β hβ => ?_⟩
  obtain ⟨c, hct, hcβ⟩ := Set.mem_iUnion₂.mp (htcov hβ)
  have hcK : c ∈ K := htK hct
  have hIoo := Set.mem_Ioo.mp hcβ
  have habs : |β - c| < δ := by
    rw [abs_sub_lt_iff]
    exact ⟨by linarith [hIoo.2], by linarith [hIoo.1]⟩
  have h1 : |f i β - f i c| < 1 := hδ' i β hβ c hcK habs
  have h2 : g c ≤ M := hM ⟨c, hct, rfl⟩
  have h3 : f i c ≤ g c := hg c i hcK
  have h4 : f i β - f i c < 1 := lt_of_le_of_lt (le_abs_self _) h1
  linarith

/-- The swap on a closed bounded interval — the form the substrate hypothesis would use. -/
theorem jointUniform_on_Icc {ι : Type*} (f : ι → ℝ → ℝ) (a b : ℝ)
    (hpt : PointwiseUniform f (Set.Icc a b)) (heq : EquicontinuousInBeta f (Set.Icc a b)) :
    JointUniform f (Set.Icc a b) :=
  jointUniform_of_pointwise_of_equicontinuous f _ isCompact_Icc hpt heq

/-- A Lipschitz constant that does not depend on the index supplies the equicontinuity. This is the
form the Wilson side would have to deliver: `WilsonAnalytic.expect_lipschitz_local` and
`expect_lipschitz_summable` are exactly Lipschitz statements, and what matters is whether their
constant is free of the aperture. -/
theorem equicontinuousInBeta_of_uniform_lipschitz {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ) (L : ℝ)
    (hL : 0 ≤ L) (h : ∀ i x y, |f i x - f i y| ≤ L * |x - y|) :
    EquicontinuousInBeta f K := by
  intro ε hε
  have hpos : (0 : ℝ) < L + 1 := by linarith
  refine ⟨ε / (L + 1), by positivity, fun i β₁ _ β₂ _ hlt => ?_⟩
  have h1 := h i β₁ β₂
  have hstep : L * |β₁ - β₂| ≤ L * (ε / (L + 1)) := by
    exact mul_le_mul_of_nonneg_left hlt.le hL
  have hfin : L * (ε / (L + 1)) < ε := by
    have hrw : L * (ε / (L + 1)) = L * ε / (L + 1) := by ring
    rw [hrw, div_lt_iff₀ hpos]
    nlinarith
  linarith

/-! ## Both hypotheses are load-bearing -/

/-- A family with one spike per index, at a point that moves toward `0`.

CHOSEN: this is a WITNESS family, picked to show the equicontinuity hypothesis of
`jointUniform_of_pointwise_of_equicontinuous` cannot be dropped. Choosing it costs nothing — the
theorem is stated over an arbitrary family and this only exhibits that the hypothesis is not vacuous.

DERIVED: within the choice, no numeral is a magnitude. The spike sits at `1/(n+1)` because `n+1` is
the least shift keeping the denominator nonzero at `n = 0`; the resulting points are distinct, lie in
`Icc 0 1`, and accumulate at `0`, which is what puts the counterexample on a COMPACT set. The `0` is
the value away from the spike — each member is supported at one point — so it is an absence of
weight, not a level. The spike HEIGHT is `n`, the index itself, and that is what makes the family
unbounded over the index; it is not a constant. -/
noncomputable def spikeFam (n : ℕ) (β : ℝ) : ℝ := if β = 1 / ((n : ℝ) + 1) then (n : ℝ) else 0

/-- **COMPACTNESS ALONE GIVES NOTHING.** `spikeFam` is index-uniformly bounded at every point of
`Icc 0 1` — at `β` the bound is `max 0 (1/β)`, since a nonzero value forces `n + 1 = 1/β` — and
unbounded over the family on that same compact interval. So the equicontinuity hypothesis of
`jointUniform_of_pointwise_of_equicontinuous` cannot be dropped. -/
theorem equicontinuity_is_load_bearing :
    PointwiseUniform spikeFam (Set.Icc (0 : ℝ) 1) ∧ ¬ JointUniform spikeFam (Set.Icc (0 : ℝ) 1) := by
  constructor
  · intro β _
    refine ⟨max 0 (1 / β), fun n => ?_⟩
    unfold spikeFam
    split_ifs with hb
    · have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hinv : 1 / β = (n : ℝ) + 1 := by
        rw [hb, one_div_one_div]
      have : (n : ℝ) ≤ 1 / β := by rw [hinv]; linarith
      exact le_trans this (le_max_right _ _)
    · exact le_max_left _ _
  · rintro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := exists_nat_gt B
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmem : 1 / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hn1]
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
    have hval : spikeFam n (1 / ((n : ℝ) + 1)) = (n : ℝ) := by
      unfold spikeFam; rw [if_pos rfl]
    have := hB n _ hmem
    rw [hval] at this
    linarith

/-- The index truncates a ramp; every member is 1-Lipschitz.

CHOSEN: a WITNESS family, picked to show compactness cannot be dropped from
`jointUniform_of_pointwise_of_equicontinuous`. Choosing it costs nothing — the theorem quantifies
over an arbitrary family and this only exhibits that the hypothesis is not vacuous.

DERIVED: the definition contains no numeral; the `1` is in the prose and is the LIPSCHITZ CONSTANT
that truncation forces, proved as `abs_min_sub_min_le` below — `|min x c − min y c| ≤ |x − y|`,
because clipping cannot increase a difference. It is read off the identity `β ↦ β`, not chosen. The
truncation level is `n`, the index itself, which is what makes the family unbounded over
`Set.univ`. -/
noncomputable def rampFam (n : ℕ) (β : ℝ) : ℝ := min β (n : ℝ)

private theorem min_sub_min_le_abs (x y c : ℝ) : min x c - min y c ≤ |x - y| := by
  rcases le_total y c with hy | hy
  · have h1 : min y c = y := min_eq_left hy
    have h2 : min x c ≤ x := min_le_left _ _
    have h3 : x - y ≤ |x - y| := le_abs_self _
    rw [h1]; linarith
  · have h1 : min y c = c := min_eq_right hy
    have h2 : min x c ≤ c := min_le_right _ _
    have h3 : (0 : ℝ) ≤ |x - y| := abs_nonneg _
    rw [h1]; linarith

private theorem abs_min_sub_min_le (x y c : ℝ) : |min x c - min y c| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  refine ⟨min_sub_min_le_abs x y c, ?_⟩
  rw [abs_sub_comm]
  exact min_sub_min_le_abs y x c

/-- **EQUICONTINUITY ALONE GIVES NOTHING EITHER.** `rampFam` is 1-Lipschitz in `β` uniformly in the
index, hence equicontinuous on all of `ℝ`, and is bounded at each `β` by `β` itself; it is unbounded
over the family on `Set.univ`. So compactness cannot be dropped, and the escape route is the same one
`sepRead` takes: `β → ∞`. -/
theorem compactness_is_load_bearing :
    PointwiseUniform rampFam (Set.univ : Set ℝ)
      ∧ EquicontinuousInBeta rampFam (Set.univ : Set ℝ)
      ∧ ¬ JointUniform rampFam (Set.univ : Set ℝ) := by
  refine ⟨fun β _ => ⟨β, fun n => min_le_left _ _⟩, ?_, ?_⟩
  · refine equicontinuousInBeta_of_uniform_lipschitz rampFam _ 1 zero_le_one (fun n x y => ?_)
    rw [one_mul]
    exact abs_min_sub_min_le x y _
  · rintro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := exists_nat_gt B
    have := hB n (n : ℝ) (Set.mem_univ _)
    rw [show rampFam n (n : ℝ) = (n : ℝ) from min_self _] at this
    linarith

/-! ## The no-go's witness, measured against the new hypotheses -/

/-- `ContactDominance.sepRead`'s circular second moment, as a family indexed by the aperture.

DERIVED: the exponent `2` is the definition of a SECOND moment — this is `Complete.d2At` and
`EvenAperture.d2Even` evaluated at `sepRead` rather than a new quantity, and the substrate hypothesis
is stated about that moment. The distance is `Moment.circLag`, the separation ON THE CIRCLE, for the
same reason it is there: it is the only distance the read can see. Nothing is introduced here. -/
noncomputable def sepMoment (N : ℕ) (β : ℝ) : ℝ :=
  ∑ d, (ContactDominance.sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2

/-- **THE COUNTEREXAMPLE ALREADY SATISFIES THE NEW CONCLUSION ON EVERY COMPACT INTERVAL.**

`ContactDominance.sepRead_moment_le` caps the moment at `((β+1)/2)²`, which on `Icc a b` is capped in
turn by `((|a|+|b|+1)/2)²`. So `sepRead` is not a counterexample to `jointUniform_on_Icc`: it meets
its conclusion outright. The no-go is a statement about unbounded coupling and about nothing else.

DERIVED: `|a| + |b| + 1` is a bound on `|β| + 1` over the interval, read off the interval's own
endpoints; `((β+1)/2)²` is `sepRead_moment_le`'s own cap. -/
theorem sepMoment_jointUniform_on_Icc (a b : ℝ) : JointUniform sepMoment (Set.Icc a b) := by
  refine ⟨((|a| + |b| + 1) / 2) ^ 2, fun N β hβ => ?_⟩
  obtain ⟨h1, h2⟩ := hβ
  have hA : -|a| ≤ a := neg_abs_le a
  have hB : b ≤ |b| := le_abs_self b
  have hA0 : (0 : ℝ) ≤ |a| := abs_nonneg a
  have hB0 : (0 : ℝ) ≤ |b| := abs_nonneg b
  have hsq : (β + 1) ^ 2 ≤ (|a| + |b| + 1) ^ 2 := by
    apply sq_le_sq' <;> linarith
  have hcap : sepMoment N β ≤ ((β + 1) / 2) ^ 2 := ContactDominance.sepRead_moment_le N β
  calc sepMoment N β ≤ ((β + 1) / 2) ^ 2 := hcap
    _ = (β + 1) ^ 2 / 4 := by ring
    _ ≤ (|a| + |b| + 1) ^ 2 / 4 := by linarith
    _ = ((|a| + |b| + 1) / 2) ^ 2 := by ring

/-- The moment at an aperture strictly above the coupling is zero. -/
theorem sepMoment_eq_zero (N : ℕ) (β : ℝ) (h : β < (N : ℝ)) : sepMoment N β = 0 := by
  unfold sepMoment ContactDominance.sepRead
  rw [if_neg (not_le.mpr h)]
  exact ContactDominance.contactRead_moment N

/-- The moment at the switch point is half the extent, squared. -/
theorem sepMoment_at_switch (N : ℕ) : sepMoment N (N : ℝ) = ((((N + 1) / 2 : ℕ)) : ℝ) ^ 2 := by
  unfold sepMoment ContactDominance.sepRead
  rw [if_pos (le_refl ((N : ℝ)))]
  exact ContactDominance.midRead_moment N

/-- **AND IT FAILS THE NEW HYPOTHESIS TOO.** On `Icc 0 1` the family jumps by `1` at `β = 1` in its
`N = 1` member, so no `δ` works at `ε = 1/2`. This is the second, independent reason the no-go and
`jointUniform_on_Icc` cannot conflict.

DERIVED: `1/2` is any value below the jump, which is `1` because `((1+1)/2)² = 1`; it is exhibited,
not chosen for size. -/
theorem sepMoment_not_equicontinuous_on_Icc :
    ¬ EquicontinuousInBeta sepMoment (Set.Icc (0 : ℝ) 1) := by
  intro h
  obtain ⟨δ, hδ, hδ'⟩ := h (1 / 2) (by norm_num)
  have hge : 1 - δ / 2 ≤ max 0 (1 - δ / 2) := le_max_right _ _
  have hlt : max 0 (1 - δ / 2) < 1 := max_lt (by norm_num) (by linarith)
  have hmem1 : max 0 (1 - δ / 2) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, le_of_lt hlt⟩
  have hmem2 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, le_refl 1⟩
  have hclose : |max 0 (1 - δ / 2) - 1| < δ := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - max 0 (1 - δ / 2))]
    linarith
  have hkey := hδ' 1 _ hmem1 1 hmem2 hclose
  have e1 : sepMoment 1 (max 0 (1 - δ / 2)) = 0 := by
    refine sepMoment_eq_zero 1 _ ?_
    rw [Nat.cast_one]
    exact hlt
  have e2 : sepMoment 1 (1 : ℝ) = 1 := by
    have := sepMoment_at_switch 1
    rw [Nat.cast_one] at this
    rw [this]
    norm_num
  rw [e1, e2] at hkey
  rw [show (0 : ℝ) - 1 = -1 by ring, abs_neg, abs_one] at hkey
  linarith

/-- **THE SHARP FORM OF THE FAILURE: THE MODULUS DEGRADES LIKE THE SQUARE OF THE APERTURE.**

At every `ε` and every `δ` there is an aperture and a pair of couplings closer than `δ` whose moments
differ by more than `ε`. The witness is `N = 2k+1` with the pair straddling `β = N`, where the jump is
exactly `(k+1)²` — so the family has no modulus of continuity uniform in the aperture, at any scale.
This is what a real bound on `d2At` would have to exclude, and it is the shape of the obstruction:
the jump grows with the aperture, not merely with the coupling. -/
theorem sepMoment_modulus_degrades (ε δ : ℝ) (hδ : 0 < δ) :
    ∃ (N : ℕ) (β₁ β₂ : ℝ), |β₁ - β₂| < δ ∧ ε < |sepMoment N β₁ - sepMoment N β₂| := by
  obtain ⟨k, hk⟩ := exists_nat_gt ε
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine ⟨2 * k + 1, ((2 * k + 1 : ℕ) : ℝ) - δ / 2, ((2 * k + 1 : ℕ) : ℝ), ?_, ?_⟩
  · rw [show ((2 * k + 1 : ℕ) : ℝ) - δ / 2 - ((2 * k + 1 : ℕ) : ℝ) = -(δ / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  · have e1 : sepMoment (2 * k + 1) (((2 * k + 1 : ℕ) : ℝ) - δ / 2) = 0 :=
      sepMoment_eq_zero _ _ (by linarith)
    have e2 : sepMoment (2 * k + 1) (((2 * k + 1 : ℕ) : ℝ)) = ((k : ℝ) + 1) ^ 2 := by
      have h := sepMoment_at_switch (2 * k + 1)
      have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      rw [hdiv] at h
      rw [h]
      push_cast
      ring
    rw [e1, e2, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    nlinarith

/-- **THE NO-GO AND THE COMPACT SWAP ARE COMPATIBLE, FOR TWO INDEPENDENT REASONS.**

Stated as one theorem so the three facts are read together: the global swap fails on `sepRead`; on
every compact interval `sepRead` already satisfies the swap's conclusion; and on `Icc 0 1` it fails
the swap's equicontinuity hypothesis. Nothing here weakens
`ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity`, and nothing there bears on
`jointUniform_on_Icc`. -/
theorem no_go_and_compact_swap_are_compatible :
    (¬ ∃ B : ℝ, ∀ (N : ℕ) (β : ℝ), sepMoment N β ≤ B)
      ∧ (∀ a b : ℝ, JointUniform sepMoment (Set.Icc a b))
      ∧ (¬ EquicontinuousInBeta sepMoment (Set.Icc (0 : ℝ) 1)) :=
  ⟨ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity.2,
    sepMoment_jointUniform_on_Icc, sepMoment_not_equicontinuous_on_Icc⟩

/-! ## What would have to be supplied — the cost, measured -/

private theorem le_pow_four (x : ℝ) (hx : 1 ≤ x) : x ≤ x ^ 4 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (0 : ℝ) ≤ x - 1 := by linarith
  have h2 : (0 : ℝ) ≤ x ^ 2 + x + 1 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg h0 h1) h2]

/-- The Clay lattice's plaquette count at aperture `N`. `wilsonCorrAt N β` is
`WilsonBridge.corrClay (N+1) β`, which lives on `WilsonHypercubic.bd (d := 4) (n := N+1)`, so the
aperture IS the periodic extent and the volume is `(N+1)⁴`.

DERIVED: `4` is the problem's dimension and `16 = 4·4` is `card_plaq`'s `d·d` at that dimension. -/
theorem clay_plaq_count (N : ℕ) :
    (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ) = 16 * ((N : ℝ) + 1) ^ 4 := by
  rw [MassGap.WilsonHypercubic.card_plaq]
  push_cast
  ring

/-- **THE ONLY UNCONDITIONAL COVARIANCE BOUND IS NOT APERTURE-UNIFORM.**

`WilsonAnalytic.cov_bound_extensive` bounds `|Cov(O,S)|` by `4·M·#Plaq`, and through
`wilsonSystem_expect_hasDerivAt` that is the Lipschitz constant available in `β` with no hypothesis.
On the Clay lattice `#Plaq = 16(N+1)⁴`, so that constant exceeds every `B` as the aperture grows: it
cannot supply `equicontinuousInBeta_of_uniform_lipschitz`. The volume-free alternatives in the same
file (`cov_bound_local`, `cov_bound_summable`) carry a clustering hypothesis. -/
theorem clay_covariance_constant_not_aperture_uniform (M : ℝ) (hM : 0 < M) (B : ℝ) :
    ∃ N : ℕ, B < 4 * M * (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ) := by
  have h4M : (0 : ℝ) < 4 * M := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (B / (4 * M))
  refine ⟨n, ?_⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hp := le_pow_four ((n : ℝ) + 1) hx
  have hnlt : B < 4 * M * (n : ℝ) := by
    rw [div_lt_iff₀ h4M] at hn
    linarith
  have hge : (n : ℝ) ≤ 16 * ((n : ℝ) + 1) ^ 4 := by linarith
  rw [clay_plaq_count]
  calc B < 4 * M * (n : ℝ) := hnlt
    _ ≤ 4 * M * (16 * ((n : ℝ) + 1) ^ 4) := mul_le_mul_of_nonneg_left hge (le_of_lt h4M)

/-! ### And a volume-free bound on the correlators would still not be enough

`d2At` is the NORMALISED moment. The probe below puts unit weight at lag zero and weight `t` at half
the period; a sup-norm perturbation of size `t` in the raw profile therefore moves the normalised
circular second moment by `t/(1+t)·((N+1)/2)²`, which grows with the aperture at fixed `t`. -/

/-- Unit weight at contact, weight `t` at half the period.

DERIVED: no numeral here is a magnitude. `Fin (N + 1)` is the LAG ARITY at aperture `N` —
`wilsonCorrAt`'s own index type, one index per lag including contact. `d = 0` names the CONTACT lag,
an index and not a value. The `1` on it is unit weight, which is the normalisation that makes the
probe's total mass exactly `1 + t` (`probeRho_sum`) and so makes the sup-norm perturbation exactly
`t`; the quantity actually varied is `t`, a parameter. The other `0` is the absence of weight at
every remaining lag. The second support point is `ContactDominance.midLag N`, half the period, which
is where `circLag` is largest — read off the circle, not picked. -/
noncomputable def probeRho (N : ℕ) (t : ℝ) : Fin (N + 1) → ℝ :=
  fun d => (if d = 0 then (1 : ℝ) else 0)
    + t * (if d = ContactDominance.midLag N then (1 : ℝ) else 0)

theorem probeRho_sum (N : ℕ) (t : ℝ) : ∑ d, probeRho N t d = 1 + t := by
  unfold probeRho
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem probeRho_moment (N : ℕ) (t : ℝ) :
    ∑ d, probeRho N t d * (Moment.circLag d : ℝ) ^ 2 = t * ((((N + 1) / 2 : ℕ)) : ℝ) ^ 2 := by
  classical
  have hterm : ∀ d : Fin (N + 1), probeRho N t d * (Moment.circLag d : ℝ) ^ 2
      = (if d = 0 then (Moment.circLag d : ℝ) ^ 2 else 0)
        + t * (if d = ContactDominance.midLag N then (Moment.circLag d : ℝ) ^ 2 else 0) := by
    intro d
    unfold probeRho
    split_ifs <;> ring
  have hz : Moment.circLag (0 : Fin (N + 1)) = 0 := by
    have hv : ((0 : Fin (N + 1)) : ℕ) = 0 := rfl
    unfold Moment.circLag
    rw [hv]
    omega
  rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq' Finset.univ (0 : Fin (N + 1)) (fun d => (Moment.circLag d : ℝ) ^ 2),
    Finset.sum_ite_eq' Finset.univ (ContactDominance.midLag N)
      (fun d => (Moment.circLag d : ℝ) ^ 2)]
  simp only [Finset.mem_univ, if_true]
  rw [ContactDominance.circLag_midLag N, hz]
  norm_num

/-- The probe as a read. Nonnegativity and positive total mass hold for every `t ≥ 0`, so this meets
the two clauses `wilson_reflection_positive_at` asserts.

DERIVED: `0 ≤ t` is a SIGN CONDITION on the parameter, not a bound on it — it is exactly what makes
the profile nonnegative, which is the first clause `Moment.Read` requires, and `t` is otherwise
unrestricted. The remaining `0`s discharge that nonnegativity clause and the positive-total-mass
clause `0 < ∑ d, probeRho N t d`; both are signs. The `0`s and `1`s inside the profile are
`probeRho`'s, unchanged — the contact index and its unit weight. `Moment.Read.p` divides by the
total, so the unit weight cancels and no scale survives into the read. -/
noncomputable def probeRead (N : ℕ) (t : ℝ) (ht : 0 ≤ t) : Moment.Read N where
  ρ := probeRho N t
  hρ := fun d => by
    unfold probeRho
    have h1 : (0 : ℝ) ≤ if d = 0 then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ if d = ContactDominance.midLag N then (1 : ℝ) else 0 := by
      split_ifs <;> norm_num
    have h3 := mul_nonneg ht h2
    linarith
  hpos := by
    have h := probeRho_sum N t
    show (0 : ℝ) < ∑ d, probeRho N t d
    rw [h]
    linarith

theorem probeRead_moment (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ d, (probeRead N t ht).p d * (Moment.circLag d : ℝ) ^ 2
      = t * ((((N + 1) / 2 : ℕ)) : ℝ) ^ 2 / (1 + t) := by
  have hsum : ∑ d', (probeRead N t ht).ρ d' = 1 + t := probeRho_sum N t
  have hp : ∀ d, (probeRead N t ht).p d = probeRho N t d / (1 + t) := by
    intro d
    unfold Moment.Read.p
    rw [hsum]
    rfl
  have hstep : ∀ d ∈ Finset.univ, (probeRead N t ht).p d * (Moment.circLag d : ℝ) ^ 2
      = probeRho N t d * (Moment.circLag d : ℝ) ^ 2 / (1 + t) := by
    intro d _
    rw [hp d]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, probeRho_moment]

/-- **THE MAP FROM THE CORRELATION TO THE NORMALISED MOMENT IS NOT UNIFORMLY LIPSCHITZ IN THE
APERTURE.**

For every `L` there are an aperture and two reads whose raw profiles differ by at most `t` at every
lag, and whose circular second moments differ by more than `L·t`. So a Lipschitz constant for the
individual correlators — which is what `WilsonAnalytic`'s covariance bounds are about, volume-free or
not — does not by itself give a Lipschitz constant for `d2At` uniform in the aperture. The lost
factor is `((N+1)/2)²`, the largest circle lag the aperture admits. It is not an artifact of a
vanishing denominator: the probe's total mass is `1 + t`, bounded above and below by construction,
so the factor survives the normalisation and a floor on the total mass would not remove it. -/
theorem profile_to_moment_not_uniformly_lipschitz (L : ℝ) :
    ∃ (N : ℕ) (t : ℝ) (ht : 0 ≤ t),
      (∀ d, |probeRho N t d - probeRho N 0 d| ≤ t) ∧
      L * t < |(∑ d, (probeRead N t ht).p d * (Moment.circLag d : ℝ) ^ 2)
        - (∑ d, (probeRead N 0 le_rfl).p d * (Moment.circLag d : ℝ) ^ 2)| := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * L)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine ⟨2 * k + 1, 1, zero_le_one, ?_, ?_⟩
  · intro d
    unfold probeRho
    have hif : (0 : ℝ) ≤ if d = ContactDominance.midLag (2 * k + 1) then (1 : ℝ) else 0 := by
      split_ifs <;> norm_num
    have hif1 : (if d = ContactDominance.midLag (2 * k + 1) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    rw [show ((if d = 0 then (1 : ℝ) else 0)
        + 1 * (if d = ContactDominance.midLag (2 * k + 1) then (1 : ℝ) else 0))
      - ((if d = 0 then (1 : ℝ) else 0)
        + 0 * (if d = ContactDominance.midLag (2 * k + 1) then (1 : ℝ) else 0))
      = (if d = ContactDominance.midLag (2 * k + 1) then (1 : ℝ) else 0) by ring]
    rw [abs_of_nonneg hif]
    exact hif1
  · rw [probeRead_moment, probeRead_moment]
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [hdiv]
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hval : (1 : ℝ) * ((k : ℝ) + 1) ^ 2 / (1 + 1) - 0 * ((k : ℝ) + 1) ^ 2 / (1 + 0)
        = ((k : ℝ) + 1) ^ 2 / 2 := by ring
    rw [hval, abs_of_nonneg (by positivity), mul_one]
    nlinarith

/-! ## The consequence for `d2At`, stated as the conditional it is -/

/-- **STEP 4, AND IT IS CONDITIONAL.** An aperture-uniform bound at each coupling of a compact
interval, plus equicontinuity in the coupling uniform in the aperture, gives the substrate bound on
that interval. The first input is available at one coupling from
`ContactDominance.aperture_uniform_of_share_envelope`; the second is NOT available from anything
proved, for the reasons `clay_covariance_constant_not_aperture_uniform` and
`profile_to_moment_not_uniformly_lipschitz` record. -/
theorem d2At_jointUniform_on_Icc_of_equicontinuous (a b : ℝ)
    (hpt : ∀ β ∈ Set.Icc a b, ∃ B : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ B)
    (heq : EquicontinuousInBeta (fun (N : ℕ) (β : ℝ) => MassGap.d2At N β) (Set.Icc a b)) :
    ∃ B : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc a b, MassGap.d2At N β ≤ B :=
  jointUniform_on_Icc _ a b hpt heq

/-- The same conclusion from an APERTURE-UNIFORM Lipschitz constant, which is the form the covariance
bound would have to take. `L` does not depend on `N` — that is the whole hypothesis, and it is the
one nothing in the tree supplies unconditionally. -/
theorem d2At_jointUniform_on_Icc_of_uniform_lipschitz (a b L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ (N : ℕ) (x y : ℝ), |MassGap.d2At N x - MassGap.d2At N y| ≤ L * |x - y|)
    (hpt : ∀ β ∈ Set.Icc a b, ∃ B : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ B) :
    ∃ B : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc a b, MassGap.d2At N β ≤ B :=
  jointUniform_on_Icc _ a b hpt
    (equicontinuousInBeta_of_uniform_lipschitz _ _ L hL hlip)

#print axioms jointUniform_of_pointwise_of_equicontinuous
#print axioms jointUniform_on_Icc
#print axioms equicontinuousInBeta_of_uniform_lipschitz
#print axioms equicontinuity_is_load_bearing
#print axioms compactness_is_load_bearing
#print axioms sepMoment_jointUniform_on_Icc
#print axioms sepMoment_eq_zero
#print axioms sepMoment_at_switch
#print axioms sepMoment_not_equicontinuous_on_Icc
#print axioms sepMoment_modulus_degrades
#print axioms no_go_and_compact_swap_are_compatible
#print axioms clay_plaq_count
#print axioms clay_covariance_constant_not_aperture_uniform
#print axioms probeRho_sum
#print axioms probeRho_moment
#print axioms probeRead_moment
#print axioms profile_to_moment_not_uniformly_lipschitz
#print axioms d2At_jointUniform_on_Icc_of_equicontinuous
#print axioms d2At_jointUniform_on_Icc_of_uniform_lipschitz

end MassGap.CompactBeta
