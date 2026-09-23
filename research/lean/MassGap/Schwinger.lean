import Mathlib
import MassGap.InfiniteVolume
import MassGap.Hankel

/-!
# MassGap.Schwinger — the infinite-volume two-point function as a bounded moment sequence

## The object

`InfiniteVolume.exists_infinite_volume_gapped_limit` produces `L : ℕ → ℝ`: one real number per
natural-number lag, the pointwise limit of the finite-extent Clay correlation along a subsequence of
extents. This file records the conditions `L` satisfies as a sequence.

`L` is a sequence of numbers, not a distribution. Three things separate it from a Schwinger
function:

1. the lag variable is `ℕ`, a lattice separation along direction `2`, not a point of `ℝ⁴`;
2. `L` is a function on that index, not a functional on test functions;
3. no measure is exhibited here of which `L` is the moment sequence.

Nothing here is a measure on a space of distributions, and nothing here is an
Osterwalder–Schrader measure.

## What is proved

* `exists_subseq_tendsto_all` — the diagonal extraction of `InfiniteVolume`, stated for an arbitrary
  uniformly bounded double sequence rather than for `corrLag` alone.
* `exists_even_extent_limit` — a limit taken along the apertures `2j+1`, so that the lattice extent
  `2j+2` is even at every member of the sequence, with `|L k| ≤ 4` at every lag. The reflection
  geometry of `Hankel.corrClay_hankel_psd` requires `n = 2m`, so the parity is fixed before the
  limit is taken.
* `hankel_psd_at_even_extent` — the finite-extent Hankel form written in the natural-number lag: at
  aperture `2J+1` and lags `a i ≤ J`, `0 ≤ ∑ᵢ∑ⱼ cᵢcⱼ corrLag (aᵢ+aⱼ)`. This is
  `Hankel.corrClay_hankel_psd` with the `Fin n` arithmetic discharged — the sum does not wrap
  (`Nat.mod_eq_of_lt`) and `corrLag`'s clamp does nothing.
* `limit_hankel_psd` — `0 ≤ ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ)` at every finite family of lags, with no bound on the
  lags. The finite-extent statement is confined to lags below half the extent; in the limit that
  confinement is gone, because a fixed finite family of lags is admissible at all large extents.
* `limit_abs_le_pow` — `|L k| ≤ B·R^k` at every `k`, with `B = max 4 (coreConst (16·4) β / R)`, at
  every rate `R` with `coreRate (16·4) β ≤ R < 1`.
* `sq_le_of_quad_nonneg`, `ratio_le_of_geometric` — the two elementary engines. The first is the
  discriminant; the second says a nonnegative log-convex sequence whose growth is `O(r^p)` has
  `Q 1 ≤ r · Q 0`.
* `shiftForm_one_le` / `shift_two_le` — the Hankel form shifted by one lag is bounded by `R²` times
  the unshifted one:

      ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ+2) ≤ R² · ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ)

  at every finite family of lags and coefficients, given positive semidefiniteness of the unshifted
  form at every family and the single geometric bound `|L k| ≤ B·R^k`. Positive semidefiniteness of
  the shifted form itself is the separate `shiftForm_nonneg`. The proof uses no operator theory:
  positive semidefiniteness at the doubled family `ι × Bool` gives log-convexity of
  `p ↦ ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ+2p)` by the discriminant, the geometric bound caps that sequence by
  `D·(R²)^p`, and a log-convex sequence cannot be capped by a rate below its own first ratio.
* `even_moment_le` — `L(2k) ≤ (R²)^k·L 0`, an upper bound on the even entries.
* `exists_infinite_volume_bounded_moment_data` — the assembly, on the derived interval `[0,b)`.

## Scope

No measure is constructed. Hamburger's theorem — a positive-semidefinite Hankel sequence is the
moment sequence of a positive measure on `ℝ` — is not in Mathlib v4.31, in its full, truncated or
bounded form, and this file does not build it. What the file states about `L` are the two Hankel
conditions, the geometric bound and summability, all as inequalities on the sequence.

## The test-function side

`summable_of_geometric` gives `Summable L`, and `summable_mul_of_bounded` gives that the pairing
`f ↦ ∑ₖ L k · f k` converges absolutely for every bounded `f : ℕ → ℝ`. The pairing is not bundled as
a `ContinuousLinearMap` here, and its index is the lattice lag, not a point of `ℝ⁴`.

DERIVED: `2` in `2j+1` is the reflection geometry's own — `Hankel.corrClay_hankel_psd` requires
`n = 2m` — and `2` in the shift is the lag the doubled family reaches, `(p+1)+(p+1) − 2p = 2`. `4` is
`InfiniteVolume.wilsonCorrAt_abs_le_four`'s bound, `128` and `16·4` are `InfiniteVolume`'s. No
constant is chosen here, and the rate `R` is universally quantified rather than picked.

Build: `python code/lean_build.py build MassGap.Schwinger`.
-/

namespace MassGap.Schwinger

open Filter
open scoped Topology
open MassGap.InfiniteVolume

/-! ## Part 0 — two elementary engines

Neither mentions the lattice. The first is the discriminant of a nonnegative quadratic; the second
bounds the first ratio of a log-convex sequence by its growth rate. -/

/-- The discriminant. If `0 ≤ A` and `t²·A + 2t·B + C ≥ 0` at every real `t`, then `B² ≤ A·C`. At
`A > 0` the vertex `t = −B/A` gives it; at `A = 0` a nonzero `B` makes the affine function unbounded
below, and the evaluation at `t = −(C+1)/(2B)` exhibits that.

DERIVED: the `0`s are the signs tested in `hA : 0 ≤ A` and in the quadratic's nonnegativity; the
`2` on `t ^ 2` and the `2` in the cross term are the quadratic's own shape, and the `2` on `B ^ 2`
is the conclusion's. `−B/A` is the parabola's vertex. Nothing chosen. -/
theorem sq_le_of_quad_nonneg {A B C : ℝ} (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ t ^ 2 * A + 2 * t * B + C) : B ^ 2 ≤ A * C := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hA0' : A = 0 := hA0.symm
    by_cases hB : B = 0
    · rw [hB, hA0']; simp
    · exfalso
      have ht := h (-(C + 1) / (2 * B))
      rw [hA0'] at ht
      have e : (-(C + 1) / (2 * B)) ^ 2 * 0 + 2 * (-(C + 1) / (2 * B)) * B + C = -1 := by
        field_simp
        ring
      rw [e] at ht
      linarith
  · have hA' : A ≠ 0 := ne_of_gt hApos
    have ht := h (-(B / A))
    have e : (-(B / A)) ^ 2 * A + 2 * (-(B / A)) * B + C = C - B ^ 2 / A := by
      field_simp
      ring
    rw [e] at ht
    have h1 : B ^ 2 / A ≤ C := by linarith
    calc B ^ 2 = B ^ 2 / A * A := by field_simp
      _ ≤ C * A := mul_le_mul_of_nonneg_right h1 hApos.le
      _ = A * C := by ring

#print axioms sq_le_of_quad_nonneg

/-- Bernoulli's inequality at a nonnegative `u`: `1 + m·u ≤ (1 + u)^m` at every natural `m`. It is
proved here by induction on `m` rather than taken from Mathlib.

DERIVED: the `0` is the sign tested in `hu : 0 ≤ u`; the two `1`s are the unit — the constant term
of the linear lower bound and the base of the power. Nothing chosen. -/
theorem one_add_mul_le_pow_self {u : ℝ} (hu : 0 ≤ u) :
    ∀ m : ℕ, 1 + (m : ℝ) * u ≤ (1 + u) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      have h1 : (0 : ℝ) ≤ 1 + u := by linarith
      have h2 : (1 + (n : ℝ) * u) * (1 + u) ≤ (1 + u) ^ n * (1 + u) :=
        mul_le_mul_of_nonneg_right ih h1
      have h3 : (0 : ℝ) ≤ (n : ℝ) * (u * u) :=
        mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hu hu)
      rw [pow_succ]
      push_cast
      nlinarith [h2, h3]

#print axioms one_add_mul_le_pow_self

/-- A ratio above one has unbounded powers: at `1 < θ` and any real `M` there is a natural `m` with
`M < θ ^ m`. It comes from `one_add_mul_le_pow_self` at `u = θ − 1` and an integer above
`(M − 1)/(θ − 1)`. No upper bound on `M` and no sign condition on it.

DERIVED: the statement's only numeral is the `1` of `hθ : 1 < θ`, the unit the ratio must exceed.
Nothing chosen. -/
theorem exists_pow_gt {θ : ℝ} (hθ : 1 < θ) (M : ℝ) : ∃ m : ℕ, M < θ ^ m := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((M - 1) / (θ - 1))
  refine ⟨m, ?_⟩
  have hu : 0 < θ - 1 := by linarith
  have hune : θ - 1 ≠ 0 := ne_of_gt hu
  have hb : 1 + (m : ℝ) * (θ - 1) ≤ θ ^ m := by
    have h := one_add_mul_le_pow_self (u := θ - 1) hu.le m
    have he : (1 : ℝ) + (θ - 1) = θ := by ring
    rwa [he] at h
  have hlt : (M - 1) / (θ - 1) * (θ - 1) < (m : ℝ) * (θ - 1) :=
    mul_lt_mul_of_pos_right hm hu
  have he2 : (M - 1) / (θ - 1) * (θ - 1) = M - 1 := by field_simp
  rw [he2] at hlt
  linarith

#print axioms exists_pow_gt

/-- A nonnegative log-convex sequence cannot beat its own growth rate. If `0 ≤ Q p` at every `p`,
`Q(p+1)² ≤ Q p · Q(p+2)` at every `p`, and `Q p ≤ D·r^p` at every `p` with `r > 0`, then
`Q 1 ≤ r · Q 0`.

The ratios of a log-convex sequence are nondecreasing, so `Q m ≥ Q 0 · (Q 1/Q 0)^m`; if
`Q 1 > r·Q 0` that lower bound outgrows `D·r^m` by `exists_pow_gt`, which the geometric hypothesis
forbids. The `Q 0 = 0` case is separate: log-convexity then forces `Q 1 = 0` as well. No sign
condition is placed on `D`; it is constrained only through the geometric hypothesis.

DERIVED: the `0`s are the sign tested in `hr : 0 < r`, the sign tested in `hQ0`, and the index `0`
in the conclusion's `Q 0`. The `1`s are the index shifts `p + 1` and the index `1` in the
conclusion's `Q 1`. The `2`s are the square in the log-convexity hypothesis and the index shift
`p + 2` it pairs with. `r`, `D` and `Q` are the caller's. -/
theorem ratio_le_of_geometric {Q : ℕ → ℝ} {D r : ℝ} (hr : 0 < r)
    (hQ0 : ∀ p, 0 ≤ Q p)
    (hlc : ∀ p, Q (p + 1) ^ 2 ≤ Q p * Q (p + 2))
    (hgb : ∀ p, Q p ≤ D * r ^ p) :
    Q 1 ≤ r * Q 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hrne : r ≠ 0 := ne_of_gt hr
  -- `Q 0 = 0` is impossible: log-convexity would force `Q 1 = 0` too.
  have hQ0pos : 0 < Q 0 := by
    rcases (hQ0 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 := hlc 0
      rw [← h] at h2
      simp at h2
      have h3 : Q 1 ≤ 0 := by nlinarith [hQ0 1, h2]
      rw [← h] at hcon
      simp at hcon
      linarith
  have hne : Q 0 ≠ 0 := ne_of_gt hQ0pos
  set ρ : ℝ := Q 1 / Q 0 with hρ
  have hρQ : ρ * Q 0 = Q 1 := by rw [hρ]; field_simp
  have hrρ : r < ρ := by nlinarith [hQ0pos, hcon, hρQ]
  have hρpos : 0 < ρ := lt_trans hr hrρ
  -- the ratio invariant: log-convexity propagates the first ratio forward
  have hinv : ∀ m : ℕ, 0 < Q m ∧ Q 0 * ρ ^ m ≤ Q m ∧ ρ * Q m ≤ Q (m + 1) := by
    intro m
    induction m with
    | zero =>
        refine ⟨hQ0pos, by simp, ?_⟩
        show ρ * Q 0 ≤ Q 1
        rw [hρQ]
    | succ n ih =>
        obtain ⟨hpos, hge, hnext⟩ := ih
        have hpos' : 0 < Q (n + 1) := lt_of_lt_of_le (mul_pos hρpos hpos) hnext
        refine ⟨hpos', ?_, ?_⟩
        · calc Q 0 * ρ ^ (n + 1) = ρ * (Q 0 * ρ ^ n) := by ring
            _ ≤ ρ * Q n := mul_le_mul_of_nonneg_left hge hρpos.le
            _ ≤ Q (n + 1) := hnext
        · have h2 := hlc n
          have h3 : ρ * Q (n + 1) * Q n ≤ Q (n + 2) * Q n := by
            calc ρ * Q (n + 1) * Q n = ρ * Q n * Q (n + 1) := by ring
              _ ≤ Q (n + 1) * Q (n + 1) := mul_le_mul_of_nonneg_right hnext hpos'.le
              _ = Q (n + 1) ^ 2 := by ring
              _ ≤ Q n * Q (n + 2) := h2
              _ = Q (n + 2) * Q n := by ring
          exact le_of_mul_le_mul_right h3 hpos
  -- the lower bound outgrows the geometric cap
  have hstep : ∀ m : ℕ, (ρ / r) ^ m * Q 0 ≤ D := by
    intro m
    have h1 : Q 0 * ρ ^ m ≤ D * r ^ m := le_trans (hinv m).2.1 (hgb m)
    have hrm : 0 < r ^ m := pow_pos hr m
    have h2 : (ρ / r) ^ m * r ^ m = ρ ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp
    have h3 : ((ρ / r) ^ m * Q 0) * r ^ m ≤ D * r ^ m := by
      calc ((ρ / r) ^ m * Q 0) * r ^ m = Q 0 * ((ρ / r) ^ m * r ^ m) := by ring
        _ = Q 0 * ρ ^ m := by rw [h2]
        _ ≤ D * r ^ m := h1
    exact le_of_mul_le_mul_right h3 hrm
  have hθ : 1 < ρ / r := by
    have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
    have hcancel : r * r⁻¹ = 1 := mul_inv_cancel₀ hrne
    rw [div_eq_mul_inv]
    have hlt := mul_lt_mul_of_pos_right hrρ hrinv
    linarith [hlt, hcancel]
  obtain ⟨m, hm⟩ := exists_pow_gt hθ (D / Q 0)
  have h4 : D / Q 0 * Q 0 < (ρ / r) ^ m * Q 0 := mul_lt_mul_of_pos_right hm hQ0pos
  have h5 : D / Q 0 * Q 0 = D := by field_simp
  rw [h5] at h4
  linarith [hstep m, h4]

#print axioms ratio_le_of_geometric

/-! ## Part 1 — the diagonal extraction, for an arbitrary bounded double sequence

`InfiniteVolume.exists_subseq_tendsto_all_lags` is this argument at `f = corrLag · β ·`. It is
restated here for a general `f` because the sequence this file needs is `corrLag` composed with the
even-extent apertures, which is not `corrLag` itself. -/

/-- Every row of a double sequence taking values in `Set.Icc (-C) C` converges along one filter
refining `atTop`, to a limit sequence `L` with `|L k| ≤ C`. The filter is `Ultrafilter.of atTop`,
and compactness of `Set.Icc (-C) C` supplies each row's limit.

DERIVED: no numeral. `C` is the caller's bound. -/
theorem exists_filter_tendsto_all (f : ℕ → ℕ → ℝ) {C : ℝ}
    (hb : ∀ k N, f k N ∈ Set.Icc (-C) C) :
    ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧ ∃ L : ℕ → ℝ, (∀ k, |L k| ≤ C) ∧
      ∀ k, Tendsto (fun N => f k N) l (𝓝 (L k)) := by
  classical
  let u : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hle : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le (atTop : Filter ℕ)
  have hk : ∀ k : ℕ, ∃ a ∈ Set.Icc (-C) C,
      Tendsto (fun N => f k N) (u : Filter ℕ) (𝓝 a) := by
    intro k
    have hmem : Set.Icc (-C) C ∈ (Ultrafilter.map (fun N => f k N) u : Filter ℝ) := by
      rw [Ultrafilter.coe_map]
      exact Filter.mem_map.mpr (Filter.univ_mem' (fun N => hb k N))
    obtain ⟨a, ha, hlim⟩ := isCompact_Icc.ultrafilter_le_nhds
      (Ultrafilter.map (fun N => f k N) u) (le_principal_iff.mpr hmem)
    refine ⟨a, ha, ?_⟩
    have hmap : Filter.map (fun N => f k N) (u : Filter ℕ) ≤ 𝓝 a := by
      rw [← Ultrafilter.coe_map]
      exact hlim
    exact hmap
  choose L hLmem hLtend using hk
  exact ⟨(u : Filter ℕ), u.neBot', hle, L,
    fun k => abs_le.mpr (Set.mem_Icc.mp (hLmem k)), hLtend⟩

#print axioms exists_filter_tendsto_all

/-- One strictly monotone `φ : ℕ → ℕ` along which every row of a uniformly bounded double sequence
converges, with the limits bounded by the same `C`. It is `InfiniteVolume.diagSeq`'s diagonal
extraction applied to `exists_filter_tendsto_all`, stated for an arbitrary double sequence rather
than for `corrLag`.

DERIVED: no numeral. `C` is the caller's bound. -/
theorem exists_subseq_tendsto_all (f : ℕ → ℕ → ℝ) {C : ℝ}
    (hb : ∀ k N, f k N ∈ Set.Icc (-C) C) :
    ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ (∀ k, |L k| ≤ C) ∧
      ∀ k, Tendsto (fun j => f k (φ j)) atTop (𝓝 (L k)) := by
  classical
  obtain ⟨l, hNeBot, hle, L, hLbound, hLtend⟩ := exists_filter_tendsto_all f hb
  haveI : l.NeBot := hNeBot
  have hstep : ∀ n m : ℕ, ∃ N, m < N ∧ ∀ k, k ≤ n →
      |f k N - L k| < 1 / ((n : ℝ) + 1) := by
    intro n m
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h1 : ∀ k : ℕ, ∀ᶠ N in l, |f k N - L k| < 1 / ((n : ℝ) + 1) := by
      intro k
      have hx := (Metric.tendsto_nhds.mp (hLtend k)) (1 / ((n : ℝ) + 1)) hpos
      filter_upwards [hx] with N hN
      rwa [Real.dist_eq] at hN
    have hall : ∀ᶠ N in l, ∀ i : Fin (n + 1),
        |f (i : ℕ) N - L (i : ℕ)| < 1 / ((n : ℝ) + 1) :=
      Filter.eventually_all.mpr (fun i => h1 (i : ℕ))
    have hgt : ∀ᶠ N in l, m < N := (Filter.eventually_gt_atTop m).filter_mono hle
    obtain ⟨N, hN1, hN2⟩ := (hall.and hgt).exists
    refine ⟨N, hN2, fun k hk => ?_⟩
    exact hN1 ⟨k, by omega⟩
  choose F hF1 hF2 using hstep
  refine ⟨L, MassGap.InfiniteVolume.diagSeq F, ?_, hLbound, ?_⟩
  · refine strictMono_nat_of_lt_succ (fun n => ?_)
    rw [MassGap.InfiniteVolume.diagSeq_succ]
    exact hF1 (n + 1) (MassGap.InfiniteVolume.diagSeq F n)
  · have hdiag : ∀ n k : ℕ, k ≤ n →
        |f k (MassGap.InfiniteVolume.diagSeq F n) - L k| < 1 / ((n : ℝ) + 1) := by
      intro n
      cases n with
      | zero =>
          intro k hk
          rw [MassGap.InfiniteVolume.diagSeq_zero]
          exact hF2 0 0 k hk
      | succ m =>
          intro k hk
          rw [MassGap.InfiniteVolume.diagSeq_succ]
          exact hF2 (m + 1) (MassGap.InfiniteVolume.diagSeq F m) k hk
    intro k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    refine ⟨max k M, fun j hj => ?_⟩
    have hkj : k ≤ j := le_trans (le_max_left _ _) hj
    have hMj : M ≤ j := le_trans (le_max_right _ _) hj
    have hMjr : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hMj
    rw [Real.dist_eq]
    calc |f k (MassGap.InfiniteVolume.diagSeq F j) - L k|
        < 1 / ((j : ℝ) + 1) := hdiag j k hkj
      _ ≤ 1 / ((M : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          linarith
      _ < ε := hM

#print axioms exists_subseq_tendsto_all

/-! ## Part 2 — the limit along even extents

The aperture `2j+1` carries the lattice extent `2j+2 = 2(j+1)`, even at every `j`. That is what
`Hankel.corrClay_hankel_psd` requires, and therefore what the limit is taken along. -/

/-- At every real `β` there is a strictly monotone `φ` and an `L : ℕ → ℝ` with `|L k| ≤ 4` such that
`corrLag k β (2·φ j + 1)` converges to `L k` at every lag `k`. It is `exists_subseq_tendsto_all`
applied to `fun k j => corrLag k β (2*j + 1)`, whose uniform bound is
`InfiniteVolume.corrLag_mem_Icc`. Every aperture in the sequence is odd, so every lattice extent is
even. No hypothesis is placed on `β`.

DERIVED: `4` is `corrLag_mem_Icc`'s bound, itself `InfiniteVolume.wilsonCorrAt_abs_le_four`'s. The
`2` and the `1` in `2 * φ j + 1` make the aperture odd and hence the extent even, which is what
`Hankel.corrClay_hankel_psd`'s `n = 2m` requires. Nothing chosen. -/
theorem exists_even_extent_limit (β : ℝ) :
    ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ (∀ k, |L k| ≤ 4) ∧
      ∀ k, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k)) :=
  exists_subseq_tendsto_all (fun k j => corrLag k β (2 * j + 1))
    (fun k j => corrLag_mem_Icc k β (2 * j + 1))

#print axioms exists_even_extent_limit

/-! ## Part 3 — the Hankel form in the natural-number lag -/

/-- The finite-extent Hankel form, written in the natural-number lag:
`0 ≤ ∑ᵢ∑ᵢ' cᵢcᵢ' corrLag (aᵢ + aᵢ') β (2J+1)` for any finite family of lags bounded by `J`.

At aperture `2J+1` — lattice extent `2J+2 = 2(J+1)`, even, half-extent `J+1` — every family with
`a i ≤ J` is admissible, the `Fin` addition of two such lags does not wrap (`Nat.mod_eq_of_lt`), and
`corrLag`'s clamp `min (a i + a i') (2J+1)` does nothing because `a i + a i' ≤ 2J`. So
`Hankel.corrClay_hankel_psd` reads as a statement about the natural-number lag function directly.
The hypothesis `hJ : ∀ i, a i ≤ J` is what confines this to lags below half the extent; no
hypothesis is placed on `β` or on the coefficients `c`.

DERIVED: the `0` is the sign asserted of the form. `2J+1` is the aperture whose extent is even,
forced by `Hankel.corrClay_hankel_psd`'s `n = 2m` and by `LogConvex.obsPlus_mem`'s requirement that
a level lie strictly below the reflection plane. Nothing chosen. -/
theorem hankel_psd_at_even_extent {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) (β : ℝ)
    (J : ℕ) (hJ : ∀ i, a i ≤ J) :
    0 ≤ ∑ i, ∑ i', c i * c i' * corrLag (a i + a i') β (2 * J + 1) := by
  classical
  have hlt : ∀ i, a i < 2 * J + 1 + 1 := fun i => by have := hJ i; omega
  set e : ι → Fin (2 * J + 1 + 1) := fun i => ⟨a i, hlt i⟩ with he_def
  have hval : ∀ i, ((e i : Fin (2 * J + 1 + 1)) : ℕ) = a i := by
    intro i
    simp [he_def]
  have hem : ∀ i, ((e i : Fin (2 * J + 1 + 1)) : ℕ) < J + 1 := by
    intro i
    rw [hval]
    have := hJ i
    omega
  have key := MassGap.Hankel.corrClay_hankel_psd (2 * J + 1 + 1) (J + 1) (by omega)
    (by omega) β e hem c
  have hterm : ∀ i i' : ι,
      corrLag (a i + a i') β (2 * J + 1)
        = MassGap.WilsonBridge.corrClay (2 * J + 1 + 1) β (e i + e i') := by
    intro i i'
    have hsum : ((e i + e i' : Fin (2 * J + 1 + 1)) : ℕ) = a i + a i' := by
      rw [Fin.val_add, hval, hval]
      refine Nat.mod_eq_of_lt ?_
      have h1 := hJ i
      have h2 := hJ i'
      omega
    unfold MassGap.InfiniteVolume.corrLag
    rw [MassGap.StrongArm.wilsonCorrAt_eq_corrClay]
    congr 1
    apply Fin.ext
    rw [hsum]
    show min (a i + a i') (2 * J + 1) = a i + a i'
    have h1 := hJ i
    have h2 := hJ i'
    omega
  calc (0 : ℝ) ≤ ∑ i, ∑ i', c i * c i'
        * MassGap.WilsonBridge.corrClay (2 * J + 1 + 1) β (e i + e i') := key
    _ = ∑ i, ∑ i', c i * c i' * corrLag (a i + a i') β (2 * J + 1) :=
        Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun i' _ => by rw [hterm i i']))

#print axioms hankel_psd_at_even_extent

/-- The limit sequence is a positive-semidefinite Hankel sequence:

    0 ≤ ∑ᵢ ∑ᵢ' cᵢ cᵢ' L(aᵢ + aᵢ')

with no constraint on the lags `a : ι → ℕ` and none on the coefficients `c`. The hypotheses are that
`φ` is strictly monotone and that `corrLag k β (2·φ j + 1)` converges to `L k` at every `k`; `L`
itself is otherwise unconstrained, so the conclusion is about whatever sequence those limits define.
`hankel_psd_at_even_extent` is confined to lags below half the extent; that confinement disappears
in the limit, because a fixed finite family of lags is admissible at every large enough extent
(`Finset.univ.sup a ≤ j ≤ φ j`) and the inequality is closed under pointwise limits (`ge_of_tendsto`).
`ι` is required to be a `Fintype` in `Type`.

DERIVED: the `0` is the sign asserted of the form; the `2` and the `1` in `2 * φ j + 1` are the odd
aperture, inherited from `exists_even_extent_limit`. Nothing chosen. -/
theorem limit_hankel_psd {β : ℝ} {L : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (htend : ∀ k, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k)))
    {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i') := by
  classical
  have hlim : Tendsto
      (fun j => ∑ i, ∑ i', c i * c i' * corrLag (a i + a i') β (2 * φ j + 1))
      atTop (𝓝 (∑ i, ∑ i', c i * c i' * L (a i + a i'))) := by
    refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun i' _ => ?_))
    exact (htend (a i + a i')).const_mul (c i * c i')
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (Finset.univ.sup a)] with j hj
  refine hankel_psd_at_even_extent a c β (φ j) (fun i => ?_)
  have h1 : a i ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ i)
  have h2 : j ≤ φ j := MassGap.InfiniteVolume.self_le_of_strictMono hφ j
  omega

#print axioms limit_hankel_psd

/-- The `2 × 2` minor of the limit, written out: `0 ≤ t²·L 0 + 2t·L 1 + L 2` at every real `t`. It
is `limit_hankel_psd` at `ι = Fin 2` with lags `(0, 1)` and coefficients `(t, 1)`, so it constrains
the three lowest lags of `L` and refers to no extent.

DERIVED: the `2` in `t ^ 2` and the `2` in the cross term are the quadratic's own shape; `L 0`,
`L 1` and `L 2` are the three lowest lags the `2 × 2` minor reaches; the `0` is the sign asserted;
the `2` and `1` in `2 * φ j + 1` are the odd aperture. Nothing chosen. -/
theorem limit_hankel_psd_two {β : ℝ} {L : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (htend : ∀ k, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k))) (t : ℝ) :
    0 ≤ t ^ 2 * L 0 + 2 * t * L 1 + L 2 := by
  have h := limit_hankel_psd hφ htend (ι := Fin 2)
    (fun i => if i = 0 then 0 else 1) (fun i => if i = 0 then t else 1)
  simp only [Fin.sum_univ_two] at h
  norm_num at h
  linarith

#print axioms limit_hankel_psd_two

/-! ## Part 4 — the limit's floor and its decay, as one geometric bound -/

/-- The contact floor survives the limit: `exp (−128β)·δ₀ ≤ L 0`. The floor `hfloor` is a hypothesis
supplied by the caller, uniform in the extent `N` and holding at every nonnegative coupling; at lag
zero `corrLag_zero` identifies `corrLag 0 β` with `wilsonCorrAt`, and `ge_of_tendsto'` carries the
bound through the limit. `δ₀` is fixed before `β` is chosen.

DERIVED: `128` is `InfiniteVolume.exists_uniform_contact_floor`'s exponent, not a choice here; the
`0`s are the sign tested in `hβ` and in `hfloor`'s hypothesis, and the lag `0` at which the floor is
read; the `2` and `1` in `2 * φ j + 1` are the odd aperture. -/
theorem limit_zero_ge {β : ℝ} (hβ : 0 ≤ β) {δ₀ : ℝ}
    (hfloor : ∀ (N : ℕ) (β' : ℝ), 0 ≤ β' →
      Real.exp (-(128 * β')) * δ₀ ≤ MassGap.wilsonCorrAt N β' 0)
    {L : ℕ → ℝ} {φ : ℕ → ℕ}
    (htend : ∀ k, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k))) :
    Real.exp (-(128 * β)) * δ₀ ≤ L 0 := by
  refine ge_of_tendsto' (htend 0) (fun j => ?_)
  show Real.exp (-(128 * β)) * δ₀ ≤ corrLag 0 β (2 * φ j + 1)
  rw [corrLag_zero]
  exact hfloor _ β hβ

#print axioms limit_zero_ge

/-- The geometric clustering survives the limit: at `1 ≤ k`,
`|L k| ≤ coreConst (16·4) β · coreRate (16·4) β ^ (k−1)`. `InfiniteVolume.corrLag_abs_le_geometric`
holds at every large enough extent, and `Tendsto.abs` with `le_of_tendsto` carries it across. It is
stated at `1 ≤ k` only; lag zero is covered separately in `limit_abs_le_pow`.

DERIVED: `16 * 4` is `InfiniteVolume`'s argument to `coreConst` and `coreRate`; the `1` in `hr` is
the unit the rate must fall below; the `1` in `hk` and in `k - 1` is the lowest lag the clustering
estimate reaches; the `0` is the sign tested in `hβ`; the `2` and `1` in `2 * φ j + 1` are the odd
aperture. -/
theorem limit_abs_le_geometric {β : ℝ} (hβ : 0 ≤ β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    {L : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (htend : ∀ k, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k)))
    {k : ℕ} (hk : 1 ≤ k) :
    |L k| ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
      * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (k - 1) := by
  have habs : Tendsto (fun j => |corrLag k β (2 * φ j + 1)|) atTop (𝓝 |L k|) := (htend k).abs
  refine le_of_tendsto habs ?_
  filter_upwards [eventually_ge_atTop k] with j hj
  have h2 : j ≤ φ j := MassGap.InfiniteVolume.self_le_of_strictMono hφ j
  exact corrLag_abs_le_geometric hk (by omega) hβ hr

#print axioms limit_abs_le_geometric

/-- One geometric bound at every lag, lag zero included: `|L k| ≤ B·R^k` with
`B = max 4 (coreConst (16·4) β / R)`. The rate `R` is universally quantified over
`coreRate (16·4) β ≤ R < 1` with `0 < R`, so the bound holds simultaneously at every admissible `R`.
Lag zero uses the hypothesis `hL4 : ∀ k, |L k| ≤ 4`; the remaining lags use
`limit_abs_le_geometric`, whose `coreConst·R^{k−1}` is rewritten as `(coreConst/R)·R^k`, which is
where `0 < R` is needed. `hC : 0 ≤ coreConst (16·4) β` is a hypothesis, not derived here.

DERIVED: `4` is `InfiniteVolume.wilsonCorrAt_abs_le_four`'s bound, appearing twice — as the
hypothesis covering lag zero and inside the `max`; `16 * 4` is `InfiniteVolume`'s argument to
`coreConst` and `coreRate`; the `0`s are the signs tested in `hβ`, `hC` and `hR0`; the `1` is the
unit `R` must fall below; the `2` and `1` in `2 * φ j + 1` are the odd aperture. -/
theorem limit_abs_le_pow {β R : ℝ} (hβ : 0 ≤ β)
    (hC : 0 ≤ MassGap.StrongCoupling.coreConst (16 * 4) β)
    (hrate : MassGap.StrongCoupling.coreRate (16 * 4) β ≤ R) (hR0 : 0 < R) (hR1 : R < 1)
    {L : ℕ → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hL4 : ∀ k, |L k| ≤ 4)
    (htend : ∀ k, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k))) :
    ∀ k, |L k| ≤ max 4 (MassGap.StrongCoupling.coreConst (16 * 4) β / R) * R ^ k := by
  have hr1 : MassGap.StrongCoupling.coreRate (16 * 4) β < 1 := lt_of_le_of_lt hrate hR1
  have hRne : R ≠ 0 := ne_of_gt hR0
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : |L 0| ≤ 4 := hL4 0
    have h1 : (4 : ℝ) ≤ max 4 (MassGap.StrongCoupling.coreConst (16 * 4) β / R) :=
      le_max_left _ _
    simpa using le_trans h0 h1
  · have h1 := limit_abs_le_geometric hβ hr1 hφ htend hk
    have h2 : MassGap.StrongCoupling.coreRate (16 * 4) β ^ (k - 1) ≤ R ^ (k - 1) :=
      pow_le_pow_left₀ (MassGap.StrongCoupling.coreRate_nonneg _ hβ) hrate (k - 1)
    have h3 : MassGap.StrongCoupling.coreConst (16 * 4) β
        * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (k - 1)
        ≤ MassGap.StrongCoupling.coreConst (16 * 4) β * R ^ (k - 1) :=
      mul_le_mul_of_nonneg_left h2 hC
    have hk' : k - 1 + 1 = k := by omega
    have h4 : MassGap.StrongCoupling.coreConst (16 * 4) β / R * R ^ k
        = MassGap.StrongCoupling.coreConst (16 * 4) β * R ^ (k - 1) := by
      conv_lhs => rw [← hk']
      rw [pow_succ]
      have he : MassGap.StrongCoupling.coreConst (16 * 4) β / R * (R ^ (k - 1) * R)
          = MassGap.StrongCoupling.coreConst (16 * 4) β * R ^ (k - 1) * (R / R) := by ring
      rw [he, div_self hRne, mul_one]
    have h5 : MassGap.StrongCoupling.coreConst (16 * 4) β / R * R ^ k
        ≤ max 4 (MassGap.StrongCoupling.coreConst (16 * 4) β / R) * R ^ k :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hR0.le k)
    calc |L k| ≤ MassGap.StrongCoupling.coreConst (16 * 4) β
          * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (k - 1) := h1
      _ ≤ MassGap.StrongCoupling.coreConst (16 * 4) β * R ^ (k - 1) := h3
      _ = MassGap.StrongCoupling.coreConst (16 * 4) β / R * R ^ k := h4.symm
      _ ≤ max 4 (MassGap.StrongCoupling.coreConst (16 * 4) β / R) * R ^ k := h5

#print axioms limit_abs_le_pow

/-! ## Part 5 — the shifted Hankel form

The shifted form is the Hankel form read at lags moved up by a fixed amount. This part derives a
bound on the shifted form in terms of the unshifted one from the geometric decay, by an elementary
argument. -/

/-- Splitting a double sum over the doubled index `ι × Bool` into its four blocks, for an arbitrary
`Lf : ℕ → ℝ`, lag assignment `A` and coefficient assignment `Cf` on `ι × Bool`. It is
`Fintype.sum_prod_type` and `Fintype.sum_bool` with the four terms grouped as
`(true,true) + (true,false)` and `(false,true) + (false,false)`.

DERIVED: no numeral. -/
theorem sum_prod_bool_split {ι : Type} [Fintype ι] (Lf : ℕ → ℝ) (A : ι × Bool → ℕ)
    (Cf : ι × Bool → ℝ) :
    ∑ x, ∑ y, Cf x * Cf y * Lf (A x + A y)
      = ((∑ i, ∑ i', Cf (i, true) * Cf (i', true) * Lf (A (i, true) + A (i', true)))
          + (∑ i, ∑ i', Cf (i, true) * Cf (i', false) * Lf (A (i, true) + A (i', false))))
        + ((∑ i, ∑ i', Cf (i, false) * Cf (i', true) * Lf (A (i, false) + A (i', true)))
          + (∑ i, ∑ i', Cf (i, false) * Cf (i', false) * Lf (A (i, false) + A (i', false)))) := by
  classical
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
  ring

#print axioms sum_prod_bool_split

section Shift

variable {L : ℕ → ℝ}

/-- The Hankel quadratic form of `L` at a family of lags `a` with coefficients `c`, shifted by `p`:
`∑ᵢ∑ᵢ' cᵢcᵢ' L(aᵢ + aᵢ' + 2p)`. No hypothesis on `L`, `a` or `c`.

DERIVED: the `2` is the Hankel index's own arithmetic — entry `(i,i')` reads `L (a i + a i')`, so
shifting both indices by `p` shifts the entry by `2p`. It is the shape of the matrix, not a step
size: the shift is by `p`, and `2 * p` is where that lands. -/
noncomputable def shiftForm (L : ℕ → ℝ) {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ)
    (p : ℕ) : ℝ :=
  ∑ i, ∑ i', c i * c i' * L (a i + a i' + 2 * p)

#print axioms shiftForm

/-- The shifted form is nonnegative at every `p`, given positive semidefiniteness `hpsd` of the
unshifted Hankel form at every finite family of lags. It is `hpsd` at the family `fun i => a i + p`,
since `(a i + p) + (a i' + p) = a i + a i' + 2p`. The hypothesis quantifies over `ι : Type` with a
`Fintype` instance, so `hpsd` must be available at the shifted family too, which is why it is taken
in that universally quantified form rather than at one fixed `ι`.

DERIVED: the `0`s are the sign asserted of the unshifted form in `hpsd` and of the shifted form in
the conclusion. The `2` reaching the statement sits inside `shiftForm`. -/
theorem shiftForm_nonneg
    (hpsd : ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
      0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i'))
    {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) (p : ℕ) :
    0 ≤ shiftForm L a c p := by
  have h := hpsd ι (fun i => a i + p) c
  refine le_of_le_of_eq h ?_
  unfold shiftForm
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => ?_))
  congr 2
  omega

#print axioms shiftForm_nonneg

/-- The doubled family. Positive semidefiniteness at the index `ι × Bool` carrying the lags
`a i + p` with coefficients `t·c` on the `true` half and the lags `a i + p + 2` with coefficients
`c` on the `false` half gives
`0 ≤ t²·shiftForm p + 2t·shiftForm (p+1) + shiftForm (p+2)` at every real `t`. The two cross blocks
are equal and each contributes `t·shiftForm (p+1)`, which is where the `2t` comes from;
`sum_prod_bool_split` is what separates the four blocks.

DERIVED: the `0`s are the sign asserted of the unshifted form in `hpsd` and of the quadratic in the
conclusion. The `2` on `t ^ 2` is the quadratic's own shape and the `2` in the cross term counts the
two equal off-diagonal blocks. The index shifts `p + 1` and `p + 2` are where the doubled family's
lag offset of `2` lands: two halves separated by `2` put the cross term at `p + 1`. -/
theorem shiftForm_quad
    (hpsd : ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
      0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i'))
    {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) (p : ℕ) (t : ℝ) :
    0 ≤ t ^ 2 * shiftForm L a c p + 2 * t * shiftForm L a c (p + 1)
        + shiftForm L a c (p + 2) := by
  classical
  set A : ι × Bool → ℕ := fun x => a x.1 + (if x.2 = true then p else p + 2) with hA
  set Cf : ι × Bool → ℝ := fun x => if x.2 = true then t * c x.1 else c x.1 with hC
  have hAt : ∀ i : ι, A (i, true) = a i + p := by intro i; simp [hA]
  have hAf : ∀ i : ι, A (i, false) = a i + p + 2 := by
    intro i
    have hstep : A (i, false) = a i + (p + 2) := by simp [hA]
    omega
  have hCt : ∀ i : ι, Cf (i, true) = t * c i := by intro i; simp [hC]
  have hCf : ∀ i : ι, Cf (i, false) = c i := by intro i; simp [hC]
  have h := hpsd (ι × Bool) A Cf
  rw [sum_prod_bool_split L A Cf] at h
  have b1 : (∑ i, ∑ i', Cf (i, true) * Cf (i', true) * L (A (i, true) + A (i', true)))
      = t ^ 2 * shiftForm L a c p := by
    unfold shiftForm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [hCt i, hCt i', hAt i, hAt i']
    have hidx : a i + p + (a i' + p) = a i + a i' + 2 * p := by omega
    rw [hidx]
    ring
  have b2 : (∑ i, ∑ i', Cf (i, true) * Cf (i', false) * L (A (i, true) + A (i', false)))
      = t * shiftForm L a c (p + 1) := by
    unfold shiftForm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [hCt i, hCf i', hAt i, hAf i']
    have hidx : a i + p + (a i' + p + 2) = a i + a i' + 2 * (p + 1) := by omega
    rw [hidx]
    ring
  have b3 : (∑ i, ∑ i', Cf (i, false) * Cf (i', true) * L (A (i, false) + A (i', true)))
      = t * shiftForm L a c (p + 1) := by
    unfold shiftForm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [hCf i, hCt i', hAf i, hAt i']
    have hidx : a i + p + 2 + (a i' + p) = a i + a i' + 2 * (p + 1) := by omega
    rw [hidx]
    ring
  have b4 : (∑ i, ∑ i', Cf (i, false) * Cf (i', false) * L (A (i, false) + A (i', false)))
      = shiftForm L a c (p + 2) := by
    unfold shiftForm
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => ?_))
    rw [hCf i, hCf i', hAf i, hAf i']
    have hidx : a i + p + 2 + (a i' + p + 2) = a i + a i' + 2 * (p + 2) := by omega
    rw [hidx]
  rw [b1, b2, b3, b4] at h
  linarith

#print axioms shiftForm_quad

/-- The shifted form is capped geometrically in `p`: `shiftForm L a c p ≤ ((∑ᵢ|cᵢ|)²·B)·(R²)^p`,
with a constant free of `p`. It is the triangle inequality on the double sum together with
`|L k| ≤ B·R^k` at `k = 2p`, and `R ≤ 1` is what lets `R^(a i + a i' + 2p)` be replaced by `R^(2p)`.
The hypotheses are `0 < R`, `R ≤ 1` and `0 ≤ B`; no positivity is assumed of `L` or of `c`.

DERIVED: the `0`s are the signs tested in `hR0` and `hB`; the `1` is the unit `R` must not exceed;
the `2` in `R ^ 2` and in `(∑ᵢ|cᵢ|) ^ 2` are the doubling of the shift and the square of the
coefficient sum, both forced by the Hankel index reading `a i + a i' + 2p`. -/
theorem shiftForm_le_geometric {B R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (hB : 0 ≤ B)
    (hb : ∀ k, |L k| ≤ B * R ^ k)
    {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) (p : ℕ) :
    shiftForm L a c p ≤ ((∑ i, |c i|) ^ 2 * B) * (R ^ 2) ^ p := by
  classical
  have h1 : shiftForm L a c p ≤ |shiftForm L a c p| := le_abs_self _
  have h2 : |shiftForm L a c p| ≤ ∑ i, ∑ i', |c i| * |c i'| * (B * R ^ (2 * p)) := by
    unfold shiftForm
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => ?_))
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i' _ => ?_))
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (hb _) ?_
    refine mul_le_mul_of_nonneg_left ?_ hB
    exact pow_le_pow_of_le_one hR0.le hR1 (by omega)
  have key : ∀ i : ι, (∑ i', |c i| * |c i'| * (B * R ^ (2 * p)))
      = |c i| * ((∑ i', |c i'|) * (B * R ^ (2 * p))) := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i' _ => by ring)
  have h3 : (∑ i, ∑ i', |c i| * |c i'| * (B * R ^ (2 * p)))
      = ((∑ i, |c i|) ^ 2 * B) * (R ^ 2) ^ p := by
    calc (∑ i, ∑ i', |c i| * |c i'| * (B * R ^ (2 * p)))
        = ∑ i, |c i| * ((∑ i', |c i'|) * (B * R ^ (2 * p))) :=
          Finset.sum_congr rfl (fun i _ => key i)
      _ = (∑ i, |c i|) * ((∑ i', |c i'|) * (B * R ^ (2 * p))) := by rw [← Finset.sum_mul]
      _ = ((∑ i, |c i|) ^ 2 * B) * (R ^ 2) ^ p := by rw [← pow_mul]; ring
  linarith [h1, h2, h3]

#print axioms shiftForm_le_geometric

/-- The Hankel form shifted by one lag is at most `R²` times the unshifted one:
`shiftForm L a c 1 ≤ R² · shiftForm L a c 0`, at every finite family of lags and coefficients. The
hypotheses are positive semidefiniteness of the unshifted form at every family, `0 < R ≤ 1`, and the
single geometric bound `|L k| ≤ B·R^k`; `0 ≤ B` is not assumed but read off `hb` at `k = 0`.

The proof: `shiftForm_quad` and `sq_le_of_quad_nonneg` give log-convexity of
`p ↦ shiftForm L a c p`, `shiftForm_le_geometric` caps that sequence by `D·(R²)^p`, and
`ratio_le_of_geometric` says a nonnegative log-convex sequence capped by `D·r^p` has first ratio at
most `r`. No operator theory, no completion, no spectral theorem.

This is a bound relating two forms; positive semidefiniteness of the shifted form itself is the
separate `shiftForm_nonneg`.

DERIVED: the `0`s are the sign asserted in `hpsd`, the sign tested in `hR0`, and the shift index in
`shiftForm L a c 0`; the `1`s are the unit `R` must not exceed and the shift index in
`shiftForm L a c 1`; the `2` in `R ^ 2` is the doubling of a one-lag shift, since shifting both
Hankel indices by `1` moves the entry by `2`. `R` and `B` are the caller's. -/
theorem shiftForm_one_le
    (hpsd : ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
      0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i'))
    {B R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (hb : ∀ k, |L k| ≤ B * R ^ k)
    {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) :
    shiftForm L a c 1 ≤ R ^ 2 * shiftForm L a c 0 := by
  have hB : 0 ≤ B := by
    have h0 := hb 0
    have h1 : (0 : ℝ) ≤ |L 0| := abs_nonneg _
    simp at h0
    linarith
  refine ratio_le_of_geometric (Q := fun p => shiftForm L a c p)
    (D := (∑ i, |c i|) ^ 2 * B) (r := R ^ 2) (pow_pos hR0 2)
    (fun p => shiftForm_nonneg hpsd a c p) (fun p => ?_)
    (fun p => shiftForm_le_geometric hR0 hR1 hB hb a c p)
  exact sq_le_of_quad_nonneg (shiftForm_nonneg hpsd a c p)
    (fun t => shiftForm_quad hpsd a c p t)

#print axioms shiftForm_one_le

/-- `shiftForm_one_le` with both shifts unfolded to sums:
`∑ᵢ∑ᵢ' cᵢcᵢ' L(aᵢ+aᵢ'+2) ≤ R² · ∑ᵢ∑ᵢ' cᵢcᵢ' L(aᵢ+aᵢ')`. Same hypotheses, same content.

DERIVED: the `0` is the sign asserted in `hpsd` and the `0` of `hR0`; the `1` is the unit `R` must
not exceed; the `2` in the lag `a i + a i' + 2` is a one-lag shift read at both Hankel indices, and
the `2` in `R ^ 2` is the matching power. -/
theorem shift_two_le
    (hpsd : ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
      0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i'))
    {B R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (hb : ∀ k, |L k| ≤ B * R ^ k)
    {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ) :
    ∑ i, ∑ i', c i * c i' * L (a i + a i' + 2)
      ≤ R ^ 2 * ∑ i, ∑ i', c i * c i' * L (a i + a i') := by
  have h := shiftForm_one_le hpsd hR0 hR1 hb a c
  unfold shiftForm at h
  simpa using h

#print axioms shift_two_le

/-- An upper bound on the even entries: `L (2k) ≤ (R²)^k · L 0` at every `k`. The induction step is
`shift_two_le` at `ι = Fin 2`, the constant lag family `fun _ => n` and the coefficients `(1, 0)`,
which reduces the double sum to `L (2n+2) ≤ R²·L (2n)`. It is a one-sided bound on `L` at even lags;
no lower bound and no statement about odd lags follows from it.

DERIVED: the `2` in `L (2 * k)` and in `R ^ 2` is the Hankel doubling, as in `shift_two_le`; the
`0`s are the sign asserted in `hpsd`, the sign tested in `hR0`, and the lag `0` in `L 0`; the `1` is
the unit `R` must not exceed. -/
theorem even_moment_le
    (hpsd : ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
      0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i'))
    {B R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (hb : ∀ k, |L k| ≤ B * R ^ k) :
    ∀ k : ℕ, L (2 * k) ≤ (R ^ 2) ^ k * L 0 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have h := shift_two_le hpsd hR0 hR1 hb (ι := Fin 2) (fun _ => n)
        (fun i => if i = 0 then 1 else 0)
      simp only [Fin.sum_univ_two] at h
      norm_num at h
      have hstep : L (2 * n + 2) ≤ R ^ 2 * L (2 * n) := by
        simpa [two_mul] using h
      have hR2 : (0 : ℝ) ≤ R ^ 2 := by positivity
      have h2 : R ^ 2 * L (2 * n) ≤ R ^ 2 * ((R ^ 2) ^ n * L 0) :=
        mul_le_mul_of_nonneg_left ih hR2
      have hidx3 : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hidx3]
      calc L (2 * n + 2) ≤ R ^ 2 * L (2 * n) := hstep
        _ ≤ R ^ 2 * ((R ^ 2) ^ n * L 0) := h2
        _ = (R ^ 2) ^ (n + 1) * L 0 := by rw [pow_succ]; ring

#print axioms even_moment_le

end Shift

/-! ## Part 6 — the test-function side

`L` is summable, so the pairing with any bounded sequence converges absolutely. The index is the
lattice lag `ℕ`, not a point of `ℝ⁴`. -/

/-- A geometrically bounded sequence is summable: `|L k| ≤ B·R^k` with `0 ≤ R < 1` gives
`Summable L`, by comparison with `summable_geometric_of_lt_one` scaled by `B`. Absolute
summability is what the comparison gives, and `Summable.of_norm` converts it.

DERIVED: the `0` is the sign tested in `hR0` and the `1` is the unit `R` must fall strictly below,
which is what makes the geometric series converge. `B` and `R` are the caller's. -/
theorem summable_of_geometric {L : ℕ → ℝ} {B R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hb : ∀ k, |L k| ≤ B * R ^ k) : Summable L := by
  have hgeo : Summable (fun k : ℕ => B * R ^ k) :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left B
  have habs : Summable (fun k : ℕ => |L k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb hgeo
  have hnorm : Summable (fun k : ℕ => ‖L k‖) := by
    simpa [Real.norm_eq_abs] using habs
  exact hnorm.of_norm

#print axioms summable_of_geometric

/-- The pairing with a bounded test sequence converges absolutely: at `|L k| ≤ B·R^k` with
`0 ≤ R < 1` and `|f k| ≤ M` at every `k`, both `fun k => |L k * f k|` and `fun k => L k * f k` are
summable, the majorant being `|L k|·M`. The statement is summability of the termwise product; the
sum is not bundled as a linear functional here, and the index is the lattice lag, not a point
of `ℝ⁴`.

DERIVED: the `0` is the sign tested in `hR0` and the `1` is the unit `R` must fall strictly below.
`B`, `R` and `M` are the caller's. -/
theorem summable_mul_of_bounded {L : ℕ → ℝ} {B R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hb : ∀ k, |L k| ≤ B * R ^ k) (f : ℕ → ℝ) {M : ℝ} (hf : ∀ k, |f k| ≤ M) :
    Summable (fun k => |L k * f k|) ∧ Summable (fun k => L k * f k) := by
  have hgeo : Summable (fun k : ℕ => B * R ^ k) :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left B
  have habs : Summable (fun k : ℕ => |L k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb hgeo
  have hle : ∀ k, |L k * f k| ≤ |L k| * M := by
    intro k
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf k) (abs_nonneg _)
  have hmajor : Summable (fun k : ℕ => |L k| * M) := habs.mul_right M
  have hsum : Summable (fun k : ℕ => |L k * f k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle hmajor
  refine ⟨hsum, ?_⟩
  have hnorm : Summable (fun k : ℕ => ‖L k * f k‖) := by
    simpa [Real.norm_eq_abs] using hsum
  exact hnorm.of_norm

#print axioms summable_mul_of_bounded

/-! ## Part 7 — the assembly -/

/-- The assembly. There is a `b > 0` and a `δ₀ > 0` such that at every `β` in `[0, b)` the rate
`coreRate (16·4) β` is below one and there is a strictly increasing sequence of apertures
`2·φ j + 1`, each carrying an even lattice extent, along which `corrLag k β` converges at every lag
`k` to `L : ℕ → ℝ` satisfying

* the contact term `e^{−128β}·δ₀ ≤ L 0`, with `δ₀` fixed before `β` is chosen;
* `0 ≤ ∑ᵢ∑ᵢ' cᵢcᵢ' L(aᵢ+aᵢ')` at every finite family of lags and coefficients, with no bound on the
  lags;
* at every rate `R` with `coreRate (16·4) β ≤ R < 1` and `0 < R`: the geometric bound
  `|L k| ≤ max 4 (coreConst (16·4) β / R) · R^k`, the shift bound
  `∑ᵢ∑ᵢ' cᵢcᵢ' L(aᵢ+aᵢ'+2) ≤ R²·∑ᵢ∑ᵢ' cᵢcᵢ' L(aᵢ+aᵢ')`, and `Summable L`.

`b` comes from `StrongCoupling.core_rate_lt_one_of_small (16·4)` and `δ₀` from
`InfiniteVolume.exists_uniform_contact_floor`. The conclusion is a conjunction of inequalities on
the sequence `L`; no measure is constructed and none is claimed.

DERIVED: the `0`s are the signs tested in `0 < b`, `0 < δ₀`, `0 ≤ β` and `0 < R`, the sign asserted
of the Hankel form, and the lag `0` in `L 0`. The `1`s are the unit that `coreRate` and `R` fall
below, and the `1` in the aperture `2 * φ j + 1`, whose `2` makes the extent even. `4` is
`InfiniteVolume.wilsonCorrAt_abs_le_four`'s bound inside the `max`; `128` and `16 * 4` are
`InfiniteVolume`'s and `StrongCoupling`'s; the `2` in the lag `a i + a i' + 2` and in `R ^ 2` is the
Hankel doubling of a one-lag shift. No constant is chosen. -/
theorem exists_infinite_volume_bounded_moment_data :
    ∃ b : ℝ, 0 < b ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ β : ℝ, 0 ≤ β → β < b →
        MassGap.StrongCoupling.coreRate (16 * 4) β < 1 ∧
        ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
          (∀ k : ℕ, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k))) ∧
          Real.exp (-(128 * β)) * δ₀ ≤ L 0 ∧
          (∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
            0 ≤ ∑ i, ∑ i', c i * c i' * L (a i + a i')) ∧
          (∀ R : ℝ, MassGap.StrongCoupling.coreRate (16 * 4) β ≤ R → 0 < R → R < 1 →
            (∀ k : ℕ, |L k|
                ≤ max 4 (MassGap.StrongCoupling.coreConst (16 * 4) β / R) * R ^ k) ∧
            (∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (c : ι → ℝ),
              ∑ i, ∑ i', c i * c i' * L (a i + a i' + 2)
                ≤ R ^ 2 * ∑ i, ∑ i', c i * c i' * L (a i + a i')) ∧
            Summable L) := by
  obtain ⟨b, hb, hrate⟩ := MassGap.StrongCoupling.core_rate_lt_one_of_small (16 * 4)
  obtain ⟨δ₀, hδ₀, hfloor⟩ := MassGap.InfiniteVolume.exists_uniform_contact_floor
  refine ⟨b, hb, δ₀, hδ₀, fun β hβ0 hβb => ?_⟩
  have hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1 := hrate β hβ0 hβb
  refine ⟨hr, ?_⟩
  obtain ⟨L, φ, hφ, hL4, htend⟩ := exists_even_extent_limit β
  have hCpos : 0 ≤ MassGap.StrongCoupling.coreConst (16 * 4) β := by
    have hpre : (128 : ℝ) ≤ MassGap.StrongCoupling.corePrefactor (16 * 4) β :=
      MassGap.StrongCoupling.le_corePrefactor (16 * 4) hβ0
    have hden : 0 < 1 - MassGap.StrongCoupling.coreRate (16 * 4) β := by linarith
    unfold MassGap.StrongCoupling.coreConst
    exact div_nonneg (by linarith) hden.le
  refine ⟨L, φ, hφ, htend, ?_, ?_, ?_⟩
  · exact limit_zero_ge hβ0 hfloor htend
  · exact fun ι _ a c => limit_hankel_psd hφ htend a c
  · intro R hrate' hR0 hR1
    have hpow := limit_abs_le_pow hβ0 hCpos hrate' hR0 hR1 hφ hL4 htend
    refine ⟨hpow, ?_, ?_⟩
    · exact fun ι _ a c =>
        shift_two_le (fun ι' _ a' c' => limit_hankel_psd hφ htend a' c') hR0 hR1.le hpow a c
    · exact summable_of_geometric hR0.le hR1 hpow

#print axioms exists_infinite_volume_bounded_moment_data

end MassGap.Schwinger
