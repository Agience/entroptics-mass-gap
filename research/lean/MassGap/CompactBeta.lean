import Mathlib
import MassGap.Complete
import MassGap.ContactDominance
import MassGap.WilsonHypercubic

/-!
# Exchanging `∀ β, ∃ B, ∀ i` for `∃ B, ∀ i, ∀ β` on a compact set

`WilsonModel.existence_and_gap_of_substrate` consumes `∃ B, ∀ N β, d2At N β ≤ B`, a bound uniform in
both the aperture and the coupling. This file names three properties of a family `f : ι → ℝ → ℝ` on a
set `K ⊆ ℝ` and relates them.

* `PointwiseUniform f K` — `∀ β ∈ K, ∃ B, ∀ i, f i β ≤ B`: a bound uniform in the index, at each
  point separately.
* `JointUniform f K` — `∃ B, ∀ i, ∀ β ∈ K, f i β ≤ B`: one bound for all indices and all points.
* `EquicontinuousInBeta f K` — the ε–δ condition with one `δ` serving every index.

`jointUniform_of_pointwise_of_equicontinuous` derives the second from the first and third when `K` is
compact, by covering `K` with `δ`-balls at `ε = 1`, extracting a finite subcover, and taking the
maximum of the centres' bounds plus one. `jointUniform_on_Icc` is the `Set.Icc` instance, and
`equicontinuousInBeta_of_uniform_lipschitz` supplies the equicontinuity from an index-independent
Lipschitz constant.

Two families show the hypotheses are not redundant. `spikeFam n β = if β = 1/(n+1) then n else 0` is
`PointwiseUniform` on `Icc 0 1` and not `JointUniform` there (`equicontinuity_is_load_bearing`).
`rampFam n β = min β n` is `PointwiseUniform` and `EquicontinuousInBeta` on `Set.univ` and not
`JointUniform` there (`compactness_is_load_bearing`).

`sepMoment` is the circular second moment of `ContactDominance.sepRead`, the family
`ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity` uses.
`sepMoment_jointUniform_on_Icc` shows it is `JointUniform` on every `Set.Icc a b`;
`sepMoment_not_equicontinuous_on_Icc` shows it is not `EquicontinuousInBeta` on `Icc 0 1`; and
`sepMoment_modulus_degrades` shows that at aperture `2 * k + 1` the jump across `β = N` is `(k+1)^2`.
`no_go_and_compact_swap_are_compatible` states the three together.

The last group is about what would supply the equicontinuity for `d2At`. `clay_plaq_count` computes
the plaquette count of the Clay lattice as `16 * (N+1)^4`;
`clay_covariance_constant_not_aperture_uniform` shows `4 * M * #Plaq` exceeds every bound as `N`
grows. `probeRho`, `probeRead` and `profile_to_moment_not_uniformly_lipschitz` exhibit two reads whose
raw profiles differ by at most `t` at every lag and whose normalised circular second moments differ
by more than `L * t`, for any `L`. `d2At_jointUniform_on_Icc_of_equicontinuous` and
`d2At_jointUniform_on_Icc_of_uniform_lipschitz` are the two conditional statements at `MassGap.d2At`.

Scope: the swap theorem is stated over an arbitrary family of real functions; no property of the
Wilson measure enters it. The two `d2At` theorems are conditional on hypotheses supplied by the
caller. `WilsonAnalytic.cov_bound_local` and `cov_bound_summable` are the volume-free covariance
bounds, and both carry a clustering hypothesis.
-/

namespace MassGap.CompactBeta

/-! ## The three properties of a family `f : ι → ℝ → ℝ` on a set `K ⊆ ℝ` -/

/-- `∀ β ∈ K, ∃ B : ℝ, ∀ i, f i β ≤ B`: at each point of `K` there is a bound serving every index.
The bound may depend on the point. With `ι = ℕ` the aperture, this is the aperture half of the
substrate hypothesis.

DERIVED: no numeral appears in the statement. -/
def PointwiseUniform {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∀ β ∈ K, ∃ B : ℝ, ∀ i, f i β ≤ B

/-- `∃ B : ℝ, ∀ i, ∀ β ∈ K, f i β ≤ B`: one bound serving every index and every point of `K`. This
is the substrate hypothesis restricted to `K`, and the conclusion of
`jointUniform_of_pointwise_of_equicontinuous`.

DERIVED: no numeral appears in the statement. -/
def JointUniform {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∃ B : ℝ, ∀ i, ∀ β ∈ K, f i β ≤ B

/-- `∀ ε > 0, ∃ δ > 0, ∀ i, ∀ β₁ β₂ ∈ K, |β₁ - β₂| < δ → |f i β₁ - f i β₂| < ε`: the ε–δ condition
with the quantifier over the index `i` inside the choice of `δ`, so one `δ` serves every member of
the family. Without that placement the condition would say only that each member is continuous.

DERIVED: `0` occurs twice, as the positivity condition on `ε` and on `δ`. `ε` is universally and `δ`
existentially quantified over the positive reals, so no value of either is named. -/
def EquicontinuousInBeta {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ β₁ ∈ K, ∀ β₂ ∈ K, |β₁ - β₂| < δ → |f i β₁ - f i β₂| < ε

/-! ## From `PointwiseUniform` to `JointUniform` on a compact set -/

/-- For a family `f : ι → ℝ → ℝ` and a compact `K ⊆ ℝ`, `PointwiseUniform f K` together with
`EquicontinuousInBeta f K` gives `JointUniform f K`.

The proof takes `δ` from the equicontinuity at `ε = 1`, totalises the pointwise bounds to a function
`g : ℝ → ℝ` by `choose`, covers `K` by the open intervals `Ioo (c - δ) (c + δ)` centred at its
points, extracts a finite subcover, bounds `g` above by `M` on the finitely many centres, and returns
`M + 1`: every point of `K` lies within `δ` of a centre, where the equicontinuity costs less than
one.

Scope: the statement is about an arbitrary family of real functions; no property of any measure
enters. Compactness and index-uniform equicontinuity are both required — `equicontinuity_is_load_bearing`
and `compactness_is_load_bearing` exhibit families failing each.

DERIVED: no numeral appears in the statement. The `ε = 1` the proof runs at is arbitrary — any
positive value gives the same conclusion with the bound shifted by it. -/
theorem jointUniform_of_pointwise_of_equicontinuous {ι : Type*} (f : ι → ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hpt : PointwiseUniform f K) (heq : EquicontinuousInBeta f K) :
    JointUniform f K := by
  classical
  obtain ⟨δ, hδ, hδ'⟩ := heq 1 one_pos
  -- the pointwise bounds as a total function of the centre, so a finite maximum can be taken
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

/-- `jointUniform_of_pointwise_of_equicontinuous` at `K := Set.Icc a b`, with compactness supplied by
`isCompact_Icc`. This is the form the substrate hypothesis is stated on.

DERIVED: no numeral appears in the statement; `a` and `b` are the caller's endpoints. -/
theorem jointUniform_on_Icc {ι : Type*} (f : ι → ℝ → ℝ) (a b : ℝ)
    (hpt : PointwiseUniform f (Set.Icc a b)) (heq : EquicontinuousInBeta f (Set.Icc a b)) :
    JointUniform f (Set.Icc a b) :=
  jointUniform_of_pointwise_of_equicontinuous f _ isCompact_Icc hpt heq

/-- If `|f i x - f i y| ≤ L * |x - y|` at every index and every pair, with `0 ≤ L`, then
`EquicontinuousInBeta f K` for every `K`. The witness is `δ := ε / (L + 1)`, positive because `L + 1`
is, and the bound then gives `L * |β₁ - β₂| ≤ L * ε / (L + 1) < ε`.

Scope: `L` does not depend on `i` — that is what makes the resulting `δ` index-independent. The
conclusion holds for any `K`, compact or not. `WilsonAnalytic.expect_lipschitz_local` and
`expect_lipschitz_summable` are Lipschitz statements of this shape.

DERIVED: `0` is the lower bound on the Lipschitz constant `L`, which is what makes multiplying the
inequality by it order-preserving. -/
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

/-! ## Families showing neither hypothesis can be dropped -/

/-- The family `spikeFam n β = if β = 1 / (n + 1) then n else 0`: each member is supported at the
single point `1 / (n + 1)`, where it takes the value `n`.

CHOSEN: a witness family, exhibited to show the equicontinuity hypothesis of
`jointUniform_of_pointwise_of_equicontinuous` is not redundant. The theorem is stated over an
arbitrary family, so the choice constrains nothing.

DERIVED: `1` occurs twice — as the numerator of the spike location `1 / (n + 1)`, and as the shift
in its denominator, the least shift keeping the denominator nonzero at `n = 0`. The resulting points
are distinct, lie in `Icc 0 1` and accumulate at `0`, which is what places the family on a compact
set. `0` is the value away from the spike, an absence of weight. The spike height is `n`, the index
itself, which is what makes the family unbounded over the index. -/
noncomputable def spikeFam (n : ℕ) (β : ℝ) : ℝ := if β = 1 / ((n : ℝ) + 1) then (n : ℝ) else 0

/-- `PointwiseUniform spikeFam (Set.Icc 0 1)` holds and `JointUniform spikeFam (Set.Icc 0 1)` does
not. At a point `β` the bound is `max 0 (1 / β)`, since a nonzero value forces `n + 1 = 1 / β`; the
family is unbounded because `spikeFam n` attains `n` at a point of the interval, for every `n`.

So compactness of the domain does not on its own give `JointUniform`: the equicontinuity hypothesis
of `jointUniform_of_pointwise_of_equicontinuous` is used.

DERIVED: `0` and `1` are the endpoints of the interval `Set.Icc 0 1`, appearing once in each
conjunct; the interval is compact and contains every spike location `1 / (n + 1)` together with their
limit point. -/
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

/-- The family `rampFam n β = min β n`: the identity in `β`, truncated at the index. Every member is
Lipschitz with constant one, by `abs_min_sub_min_le` below — clipping cannot increase a difference —
and the truncation level is the index itself.

CHOSEN: a witness family, exhibited to show compactness of the domain is used in
`jointUniform_of_pointwise_of_equicontinuous`. The theorem is stated over an arbitrary family, so
the choice constrains nothing.

DERIVED: no numeral appears in the definition. The Lipschitz constant one is read off the identity
`β ↦ β` rather than chosen; the truncation level is `n`, the index. -/
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

/-- `PointwiseUniform rampFam Set.univ` and `EquicontinuousInBeta rampFam Set.univ` both hold, and
`JointUniform rampFam Set.univ` does not. The pointwise bound at `β` is `β` itself; the
equicontinuity comes from `equicontinuousInBeta_of_uniform_lipschitz` at constant one, via
`abs_min_sub_min_le`; and `rampFam n n = n` is unbounded over the index.

So compactness of the domain is used in `jointUniform_of_pointwise_of_equicontinuous`. The failure is
at large `β`, which is where `ContactDominance.sepRead`'s failure also sits.

DERIVED: no numeral appears in the statement; the domain is `Set.univ`. -/
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

/-! ## `ContactDominance.sepRead`'s moment against the two hypotheses -/

/-- `∑ d, (ContactDominance.sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2`: the circular second
moment of `sepRead`, as a family indexed by the aperture `N` and the coupling `β`. It is the quantity
`MassGap.d2At` and `EvenAperture.d2Even` compute, evaluated at `sepRead` rather than at the Wilson
correlation.

DERIVED: the exponent `2` is what makes this a second moment. The distance is `Moment.circLag`, the
separation on the circle, which is the distance a read on a periodic lattice sees. -/
noncomputable def sepMoment (N : ℕ) (β : ℝ) : ℝ :=
  ∑ d, (ContactDominance.sepRead N β).p d * (Moment.circLag d : ℝ) ^ 2

/-- `JointUniform sepMoment (Set.Icc a b)` at every pair of endpoints. The witness bound is
`((|a| + |b| + 1) / 2) ^ 2`: `ContactDominance.sepRead_moment_le` caps the moment at `((β + 1) / 2) ^ 2`,
and on `Icc a b` the quantity `β + 1` is bounded in absolute value by `|a| + |b| + 1`.

So `sepMoment` satisfies the conclusion of `jointUniform_on_Icc` on every compact interval.

DERIVED: no numeral appears in the statement; `a` and `b` are the caller's endpoints. The bound
`((|a| + |b| + 1) / 2) ^ 2` is constructed in the proof from those endpoints and
`sepRead_moment_le`'s own cap. -/
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

/-- `sepMoment N β = 0` whenever `β < N`. Below the switch point `sepRead` is
`ContactDominance.contactRead N`, whose moment is zero by
`ContactDominance.contactRead_moment` — all its weight sits at lag zero, where `circLag` vanishes.

DERIVED: `0` is the value of the moment, which is the weight-zero contact read's own. -/
theorem sepMoment_eq_zero (N : ℕ) (β : ℝ) (h : β < (N : ℝ)) : sepMoment N β = 0 := by
  unfold sepMoment ContactDominance.sepRead
  rw [if_neg (not_le.mpr h)]
  exact ContactDominance.contactRead_moment N

/-- `sepMoment N N = (((N + 1) / 2 : ℕ) : ℝ) ^ 2`. At `β = N` the condition `(N : ℝ) ≤ β` holds, so
`sepRead` is `ContactDominance.midRead N`, whose moment `ContactDominance.midRead_moment` computes:
all its weight sits at the lag half a period away, where `circLag` is `(N + 1) / 2`.

Scope: the division `(N + 1) / 2` is on `ℕ`, so it floors at even `N`.

DERIVED: `1` is the `+ 1` making the extent `N + 1` from the aperture `N`; the first `2` is the
halving that places the lag opposite the origin on the circle; the exponent `2` is the second
moment's. -/
theorem sepMoment_at_switch (N : ℕ) : sepMoment N (N : ℝ) = ((((N + 1) / 2 : ℕ)) : ℝ) ^ 2 := by
  unfold sepMoment ContactDominance.sepRead
  rw [if_pos (le_refl ((N : ℝ)))]
  exact ContactDominance.midRead_moment N

/-- `EquicontinuousInBeta sepMoment (Set.Icc 0 1)` does not hold. Taking `ε = 1 / 2`, the member at
`N = 1` has `sepMoment 1 β = 0` for `β < 1` by `sepMoment_eq_zero` and `sepMoment 1 1 = 1` by
`sepMoment_at_switch`, so the pair `max 0 (1 - δ / 2)` and `1` lies within any `δ` and differs by
one.

DERIVED: `0` and `1` are the endpoints of the interval `Set.Icc 0 1`, which contains the switch
point `β = 1` of the member at `N = 1`. The `ε = 1 / 2` used in the proof is any value below the
jump, which is `1` because `((1 + 1) / 2) ^ 2 = 1`. -/
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

/-- For every real `ε` and every `δ > 0` there are an aperture `N` and couplings `β₁`, `β₂` with
`|β₁ - β₂| < δ` and `ε < |sepMoment N β₁ - sepMoment N β₂|`.

The witness is `N = 2 * k + 1` for `k` above `ε`, with `β₁ = N - δ / 2` and `β₂ = N` straddling the
switch point. `sepMoment_eq_zero` gives `0` on the left and `sepMoment_at_switch` gives `(k + 1) ^ 2`
on the right, since `(2 * k + 1 + 1) / 2 = k + 1`.

So the jump at the switch point grows with the aperture: no modulus of continuity serves every
aperture at once.

DERIVED: `0` is the positivity condition on `δ`. No other numeral appears in the statement; the
`2 * k + 1`, the halving of `δ` and the resulting `(k + 1) ^ 2` are all constructed in the proof. -/
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

/-- Three facts about `sepMoment`, conjoined: there is no bound serving every aperture and every real
coupling (`ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity`); on every
`Set.Icc a b` there is one (`sepMoment_jointUniform_on_Icc`); and on `Set.Icc 0 1` the family is not
equicontinuous in the index-uniform sense (`sepMoment_not_equicontinuous_on_Icc`).

Stated together so the three are read at once. The first is about unbounded coupling; the second and
third are about what `jointUniform_on_Icc` asks for.

DERIVED: `0` and `1` are the endpoints of `Set.Icc 0 1` in the third conjunct, the interval on which
the equicontinuity fails. No other numeral appears in the statement. -/
theorem no_go_and_compact_swap_are_compatible :
    (¬ ∃ B : ℝ, ∀ (N : ℕ) (β : ℝ), sepMoment N β ≤ B)
      ∧ (∀ a b : ℝ, JointUniform sepMoment (Set.Icc a b))
      ∧ (¬ EquicontinuousInBeta sepMoment (Set.Icc (0 : ℝ) 1)) :=
  ⟨ContactDominance.aperture_uniformity_does_not_give_coupling_uniformity.2,
    sepMoment_jointUniform_on_Icc, sepMoment_not_equicontinuous_on_Icc⟩

/-! ## The size of the available Lipschitz constants -/

/-- `x ≤ x ^ 4` for `1 ≤ x`, by `nlinarith` on the factorisation `x ^ 4 - x = x(x-1)(x²+x+1)`.
Used below to compare the plaquette count with the aperture it is a quartic in.

DERIVED: `1` is the lower bound on `x` that makes the factorisation nonnegative; `4` is the exponent
the plaquette count carries, `WilsonHypercubic.card_plaq`'s. -/
private theorem le_pow_four (x : ℝ) (hx : 1 ≤ x) : x ≤ x ^ 4 := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (0 : ℝ) ≤ x - 1 := by linarith
  have h2 : (0 : ℝ) ≤ x ^ 2 + x + 1 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg h0 h1) h2]

/-- `(Fintype.card (WilsonHypercubic.Plaq 4 (N + 1)) : ℝ) = 16 * ((N : ℝ) + 1) ^ 4`, by
`WilsonHypercubic.card_plaq` and `push_cast`. `MassGap.wilsonCorrAt N β` is
`WilsonBridge.corrClay (N + 1) β`, which lives on the lattice of extent `N + 1`, so the aperture is
the periodic extent and the volume is `(N + 1) ^ 4`.

DERIVED: the first `4` is the spacetime dimension in the plaquette type; `1` occurs twice, as the
`+ 1` relating the extent to the aperture on each side; `16` is `card_plaq`'s factor `d * d` at
`d = 4`; the exponent `4` is `n ^ d` at the same dimension. -/
theorem clay_plaq_count (N : ℕ) :
    (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ) = 16 * ((N : ℝ) + 1) ^ 4 := by
  rw [MassGap.WilsonHypercubic.card_plaq]
  push_cast
  ring

/-- For every `M > 0` and every `B`, there is an aperture `N` with
`B < 4 * M * Fintype.card (WilsonHypercubic.Plaq 4 (N + 1))`. The proof picks `n` above
`B / (4 * M)` and uses `clay_plaq_count` together with `x ≤ x ^ 4` for `x ≥ 1`.

`WilsonAnalytic.cov_bound_extensive` bounds `|Cov(O, S)|` by `4 * M * #Plaq`, and through
`WilsonAnalytic.wilsonSystem_expect_hasDerivAt` that is a Lipschitz constant in `β`. This statement
says that constant is unbounded over the aperture, so it does not supply the hypothesis of
`equicontinuousInBeta_of_uniform_lipschitz`. `WilsonAnalytic.cov_bound_local` and
`cov_bound_summable` are volume-free and carry a clustering hypothesis.

DERIVED: `0` is the positivity condition on `M`; the first `4` is the factor in
`cov_bound_extensive`'s own bound; the second `4` is the spacetime dimension in the plaquette type;
`1` is the `+ 1` relating the extent to the aperture. -/
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

/-! ### The map from a raw profile to the normalised moment

`MassGap.d2At` is the normalised circular second moment. The probe below puts unit weight at lag zero
and weight `t` at half the period; a sup-norm perturbation of size `t` in the raw profile moves the
normalised moment by `t / (1 + t) * ((N + 1) / 2) ^ 2`, which grows with the aperture at fixed `t`.
The probe's total mass is `1 + t`, so the growth is not a vanishing denominator: it is the weight
`circLag ^ 2` applied at the largest lag the aperture admits. -/

/-- The raw profile on `Fin (N + 1)` carrying unit weight at lag `0` and weight `t` at
`ContactDominance.midLag N`, zero elsewhere. Its total mass is `1 + t` (`probeRho_sum`) and its
unnormalised second moment is `t * ((N + 1) / 2) ^ 2` (`probeRho_moment`).

DERIVED: `1` in the type is the `+ 1` in the lag index type `Fin (N + 1)`, one index per lag
including contact — `wilsonCorrAt`'s own arity at aperture `N`. In the body, `0` is the contact lag
index and the weight carried at every lag outside the support, and `1` is the unit weight at contact,
which is what makes the total mass exactly `1 + t` and the sup-norm perturbation exactly `t`. The
second support point is `ContactDominance.midLag N`, half the period, where `circLag` is largest. -/
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

/-- `probeRho N t` packaged as a `Moment.Read N`, for `0 ≤ t`. The `hρ` field is nonnegativity of the
profile, from nonnegativity of the two indicator terms and of `t`; the `hpos` field is
`0 < ∑ d, probeRho N t d`, which `probeRho_sum` evaluates to `1 + t`.

Scope: `0 ≤ t` is what makes the profile nonnegative; `t` is otherwise unrestricted.
`Moment.Read.p` divides by the total mass, so the unit weight at contact cancels and no scale
survives into the normalised read.

DERIVED: `0` is the lower bound on `t`, the sign condition the two `Moment.Read` clauses need. The
numerals inside the profile are `probeRho`'s, unchanged. -/
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

/-- For every real `L` there are an aperture `N`, a parameter `t ≥ 0`, and the two reads
`probeRead N t` and `probeRead N 0` whose raw profiles satisfy
`|probeRho N t d - probeRho N 0 d| ≤ t` at every lag, while their normalised circular second moments
differ by more than `L * t`.

The witness is `N = 2 * k + 1` for `k` above `2 * L`, with `t = 1`. `probeRead_moment` evaluates the
two moments as `(k + 1) ^ 2 / 2` and `0`.

So a Lipschitz constant for the individual correlators does not by itself give one for the
normalised moment uniform in the aperture; the factor between them is `((N + 1) / 2) ^ 2`, the
largest circle lag the aperture admits. The probe's total mass is `1 + t`, bounded above and below,
so the factor is not an artifact of a vanishing denominator and a floor on the total mass would not
remove it.

DERIVED: `0` occurs three times — the lower bound on `t`, and the parameter value at which each of
the two comparison objects `probeRho N 0` and `probeRead N 0` is taken; the exponent `2` occurs
twice, once in each circular second moment. -/
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

/-! ## The two conditional statements at `MassGap.d2At` -/

/-- `jointUniform_on_Icc` at `f := fun N β => MassGap.d2At N β`: an aperture-uniform bound at each
coupling of `Set.Icc a b`, together with equicontinuity in the coupling uniform in the aperture,
gives one bound serving every aperture and every coupling in the interval.

Scope: both hypotheses are the caller's. `ContactDominance.aperture_uniform_of_share_envelope` is one
source of the first at a single coupling; for the second,
`clay_covariance_constant_not_aperture_uniform` and `profile_to_moment_not_uniformly_lipschitz`
record the size of the constants the tree's covariance bounds supply.

DERIVED: no numeral appears in the statement; `a` and `b` are the caller's endpoints. -/
theorem d2At_jointUniform_on_Icc_of_equicontinuous (a b : ℝ)
    (hpt : ∀ β ∈ Set.Icc a b, ∃ B : ℝ, ∀ N : ℕ, MassGap.d2At N β ≤ B)
    (heq : EquicontinuousInBeta (fun (N : ℕ) (β : ℝ) => MassGap.d2At N β) (Set.Icc a b)) :
    ∃ B : ℝ, ∀ (N : ℕ), ∀ β ∈ Set.Icc a b, MassGap.d2At N β ≤ B :=
  jointUniform_on_Icc _ a b hpt heq

/-- The same conclusion as `d2At_jointUniform_on_Icc_of_equicontinuous`, with the equicontinuity
hypothesis replaced by a Lipschitz bound `|d2At N x - d2At N y| ≤ L * |x - y|` with `0 ≤ L`, through
`equicontinuousInBeta_of_uniform_lipschitz`.

Scope: `L` does not depend on `N`, which is what makes the resulting `δ` aperture-independent. Both
`hlip` and `hpt` are the caller's.

DERIVED: `0` is the lower bound on the Lipschitz constant `L`, inherited from
`equicontinuousInBeta_of_uniform_lipschitz`. -/
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
