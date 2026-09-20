import Mathlib
import MassGap.InfiniteVolume
import MassGap.Hankel

/-!
# MassGap.Schwinger — the infinite-volume two-point function as a BOUNDED MOMENT SEQUENCE

## What the object is, and what it is not

`InfiniteVolume.exists_infinite_volume_gapped_limit` produces `L : ℕ → ℝ`: one real number per
natural-number lag, the pointwise limit of the finite-extent Clay correlation along a subsequence of
extents. That is a SEQUENCE OF NUMBERS. A Schwinger function is a distribution — a continuous linear
functional on a space of test functions on `ℝ⁴` — and the distance between the two is three named
things:

1. the lag variable is `ℕ`, a lattice separation along direction `2`, not a point of `ℝ⁴`;
2. `L` is a function on that index, not a functional on test functions;
3. nothing exhibits `L` as the moments, or the Fourier coefficients, of any measure.

This file closes (3) as far as it can be closed without the Hamburger construction itself, and states
(1) and (2) exactly rather than papering over them. Nothing here is a measure on a space of
distributions, and nothing here is an Osterwalder–Schrader measure.

## What is proved

* `exists_subseq_tendsto_all` — the diagonal extraction of `InfiniteVolume`, stated for an arbitrary
  uniformly bounded double sequence rather than for `corrLag` alone.
* `exists_even_extent_limit` — the same limit as `InfiniteVolume.exists_subseq_tendsto_all_lags`, but
  taken along the apertures `2j+1`, so that the lattice extent `2j+2` is EVEN at every member of the
  sequence. The reflection geometry of `Hankel.corrClay_hankel_psd` requires `n = 2m`; no
  finite-extent Hankel statement is available at an odd extent, so the parity has to be chosen before
  the limit is taken. The bound `|L k| ≤ 4`, the contact floor and the decay are unaffected.
* `hankel_psd_at_even_extent` — the finite-extent Hankel form written in the NATURAL-NUMBER lag: at
  aperture `2J+1` and lags `a i ≤ J`, `0 ≤ ∑ᵢ∑ⱼ cᵢcⱼ ρ(aᵢ+aⱼ)`. This is
  `Hankel.corrClay_hankel_psd` with the `Fin n` arithmetic discharged — the sum does not wrap
  (`Nat.mod_eq_of_lt`) and `corrLag`'s clamp does nothing.
* `limit_hankel_psd` — **the limit sequence is a positive-semidefinite Hankel sequence at EVERY
  finite family of lags, with no bound on the lags at all.** The finite-extent statement is confined
  to lags below half the extent; in the limit that confinement is gone, because any fixed finite
  family of lags is admissible at all large extents. This is the hypothesis of the FULL (not
  truncated) Hamburger moment problem. The extent-6 witness recorded in `Hankel`'s header does not
  bear on it: that witness is a statement about the six lags of one finite lattice, not about a
  sequence defined at every lag.
* `limit_abs_le_pow` — `|L k| ≤ B·R^k` at every `k`, from the geometric clustering, at every rate `R`
  with `coreRate (16·4) β ≤ R < 1`.
* `sq_le_of_quad_nonneg`, `ratio_le_of_geometric` — the two elementary engines. The first is the
  discriminant; the second says a nonnegative log-convex sequence whose growth is `O(r^p)` has
  `Q 1 ≤ r · Q 0`.
* `shiftForm_one_le` / `shift_two_le` — **the shifted Hankel matrix is positive semidefinite**:

      ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ+2) ≤ R² · ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ)

  at every finite family of lags and coefficients. Together with `limit_hankel_psd` this is the
  hypothesis of the BOUNDED Hamburger problem — the condition under which the classical construction
  places a representing measure on `[−R, R]` rather than on all of `ℝ`. The proof is elementary and
  uses no operator theory: positive semidefiniteness at the doubled family `ι × Bool` gives
  log-convexity of `p ↦ ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ+2p)` by the discriminant, the geometric bound caps that
  sequence by `D·(R²)^p`, and a log-convex sequence cannot be capped by a rate below its own first
  ratio.
* `even_moment_le` — `L(2k) ≤ R^{2k}·L 0`, the visible consequence.
* `exists_infinite_volume_bounded_moment_data` — the assembly, on the derived interval `[0,b)`.

## What this does NOT give

A measure. Hamburger's theorem — a positive-semidefinite Hankel sequence is the moment sequence of a
positive measure on `ℝ` — is not in Mathlib v4.31, and neither is the truncated nor the bounded
version. Constructing one here means the classical route: the semi-inner product `⟨p,q⟩ = Λ(pq)` on
`ℝ[X]`, its Hausdorff completion, multiplication by `X` as a BOUNDED self-adjoint operator — bounded
by `shiftForm_one_le`, which is exactly what the shifted form buys and what bare positive
semidefiniteness never gives — the continuous functional calculus, and Riesz–Markov on the spectrum.
Those pieces exist in Mathlib; the assembly does not, and it is not attempted here.

So `L` is still a sequence of numbers. What has changed is that it is now a sequence of numbers
carrying both Hankel conditions of a compactly supported moment sequence, at every lag, where the
tree previously had one condition at lags below half of a finite extent.

## The test-function side

`summable_of_geometric` gives `Summable L`, and `summable_mul_of_bounded` gives that the pairing
`f ↦ ∑ₖ L k · f k` converges absolutely for every bounded `f : ℕ → ℝ`. That is a bounded linear
functional on the bounded sequences in content, but it is NOT bundled as a `ContinuousLinearMap`
here, and its index is the lattice lag, so it is not a distribution on `ℝ⁴` and must not be read as
one.

DERIVED: `2` in `2j+1` is the reflection geometry's own — `Hankel.corrClay_hankel_psd` requires
`n = 2m` — and `2` in the shift is the lag the doubled family reaches, `(p+1)+(p+1) − 2p = 2`. `4` is
`InfiniteVolume.wilsonCorrAt_abs_le_four`'s bound, `128` and `16·4` are `InfiniteVolume`'s. No
constant is chosen here, none is fitted, and the rate `R` is universally quantified rather than
picked.

Build: `python code/lean_build.py build MassGap.Schwinger`.
-/

namespace MassGap.Schwinger

open Filter
open scoped Topology
open MassGap.InfiniteVolume

/-! ## Part 0 — two elementary engines

Neither mentions the lattice. The first is the discriminant of a nonnegative quadratic; the second is
the only genuinely new estimate in the file. -/

/-- **The discriminant.** If `t²·A + 2t·B + C ≥ 0` at every real `t`, then `B² ≤ A·C`. At `A > 0` the
vertex `t = −B/A` gives it; at `A = 0` a nonzero `B` makes the affine function unbounded below.

DERIVED: the `2` is the cross term's own and `−B/A` is the parabola's vertex. Nothing chosen. -/
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

/-- Bernoulli's inequality, by induction, so that nothing here depends on Mathlib's spelling. -/
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

/-- A ratio above one has unbounded powers. -/
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

/-- **A nonnegative log-convex sequence cannot beat its own growth rate.**

If `Q p ≥ 0`, `Q(p+1)² ≤ Q p · Q(p+2)` and `Q p ≤ D·r^p` with `r > 0`, then `Q 1 ≤ r · Q 0`.

The ratios `Q(p+1)/Q p` of a log-convex sequence are nondecreasing, so `Q m ≥ Q 0 · (Q 1/Q 0)^m`; if
`Q 1 > r·Q 0` that lower bound outgrows `D·r^m`, which the hypothesis forbids. The `Q 0 = 0` case is
separate and immediate: log-convexity then forces `Q 1 = 0` as well.

This is the one place where the geometric decay does work that positive semidefiniteness alone
cannot.

DERIVED: no constant. `r`, `D` and `Q` are the caller's. -/
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

/-- Every row converges along one ultrafilter refining `atTop`. -/
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

/-- **One subsequence along which every row converges.** `InfiniteVolume.diagSeq`'s diagonal
extraction, for an arbitrary uniformly bounded double sequence. -/
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

/-! ## Part 2 — the limit along EVEN extents

The aperture `2j+1` carries the lattice extent `2j+2 = 2(j+1)`, even at every `j`. That is what
`Hankel.corrClay_hankel_psd` requires, and therefore what the limit has to be taken along. -/

/-- **The correlation converges at every lag along a subsequence of EVEN extents.** -/
theorem exists_even_extent_limit (β : ℝ) :
    ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ (∀ k, |L k| ≤ 4) ∧
      ∀ k, Tendsto (fun j => corrLag k β (2 * φ j + 1)) atTop (𝓝 (L k)) :=
  exists_subseq_tendsto_all (fun k j => corrLag k β (2 * j + 1))
    (fun k j => corrLag_mem_Icc k β (2 * j + 1))

#print axioms exists_even_extent_limit

/-! ## Part 3 — the Hankel form in the natural-number lag -/

/-- **The finite-extent Hankel form, written in the natural-number lag.**

At aperture `2J+1` — lattice extent `2J+2 = 2(J+1)`, even, half-extent `J+1` — every family of lags
`a i ≤ J` is admissible, the `Fin` addition of two such lags does not wrap (`Nat.mod_eq_of_lt`), and
`corrLag`'s clamp `min (a i + a i') (2J+1)` does nothing because `a i + a i' ≤ 2J`. So
`Hankel.corrClay_hankel_psd` reads as a statement about the natural-number lag function directly.

DERIVED: `2J+1` is the aperture whose extent is even and `J+1` is half of it; both are forced by
`Hankel.corrClay_hankel_psd`'s `n = 2m` and by `LogConvex.obsPlus_mem`'s requirement that a level lie
strictly below the reflection plane. Nothing chosen. -/
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

/-- **THE LIMIT SEQUENCE IS A POSITIVE-SEMIDEFINITE HANKEL SEQUENCE, AT EVERY FINITE FAMILY OF
LAGS.**

    0 ≤ ∑ᵢ ∑ⱼ cᵢ cⱼ L(aᵢ + aⱼ)

with NO constraint on the lags `a : ι → ℕ` and none on the coefficients. The finite-extent statement
`Hankel.corrClay_hankel_psd` is confined to lags below half the extent; that confinement disappears
in the limit, because a fixed finite family of lags is admissible at every large enough extent
(`Finset.univ.sup a ≤ j ≤ φ j`) and the inequality is closed under pointwise limits.

This is the hypothesis of the full Hamburger moment problem: a statement about a sequence defined at
every lag, which is why the extent-6 witness in `Hankel`'s header — a statement about the six lags of
one finite lattice — does not bear on it. -/
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

/-- **Non-vacuity — the `2 × 2` minor of the limit.** A one-parameter family of constraints on the
three lowest lags of the limit sequence, with no reference to any extent. -/
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

/-- The contact floor survives the limit. -/
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

/-- The geometric clustering survives the limit. -/
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

/-- **ONE geometric bound at every lag, lag zero included.**

`|L k| ≤ B·R^k` with `B = max 4 (coreConst/R)`, at every rate `R` between the estimate's own
`coreRate (16·4) β` and one. The rate is the caller's: nothing is chosen here, and the statement
holds simultaneously at every admissible `R`.

DERIVED: `4` is `InfiniteVolume.wilsonCorrAt_abs_le_four`'s bound, which is what covers lag zero; the
division by `R` is what turns `coreConst·R^{k−1}` into `(coreConst/R)·R^k`. -/
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

The point of the file. Positive semidefiniteness alone says nothing about where a representing
measure would live; the shifted form is the localisation condition, and it follows from the geometric
decay by an entirely elementary argument. -/

/-- Splitting a double sum over the doubled index `ι × Bool` into its four blocks. -/
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

/-- The Hankel quadratic form of `L` at a family of lags, shifted by `p`.

DERIVED: the `2` is the Hankel index's own arithmetic — entry `(i,i')` reads `L (a i + a i')`, so
shifting BOTH indices by `p` shifts the entry by `2p`. It is the shape of the matrix, not a step
size: the shift is by `p`, and `2 * p` is where that lands. -/
noncomputable def shiftForm (L : ℕ → ℝ) {ι : Type} [Fintype ι] (a : ι → ℕ) (c : ι → ℝ)
    (p : ℕ) : ℝ :=
  ∑ i, ∑ i', c i * c i' * L (a i + a i' + 2 * p)

#print axioms shiftForm

/-- The shifted form is nonnegative: it is the Hankel form at the shifted family of lags. -/
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

/-- **The doubled family.** Positive semidefiniteness at the family carrying the lags `a i + p` with
coefficients `t·c` and the lags `a i + p + 2` with coefficients `c` is a nonnegative quadratic in `t`
whose three coefficients are the shifted forms at `p`, `p+1` and `p+2`.

DERIVED: the shift `2` between the two halves is what puts the cross term at `p+1`. -/
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

/-- The shifted form is capped by the geometric bound, with a constant free of `p`. -/
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

/-- **THE SHIFTED HANKEL MATRIX IS POSITIVE SEMIDEFINITE.**

    ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ+2) ≤ R² · ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ)

at every finite family of lags and coefficients, given positive semidefiniteness of the unshifted
form at every family together with the single geometric bound `|L k| ≤ B·R^k`, `0 < R ≤ 1`.

This is the localisation condition of the moment problem. With it, the classical construction places
a representing measure on `[−R, R]`; without it, positive semidefiniteness says nothing about where
one would live, and for a truncated sequence there may be none at all.

The proof: the doubled family gives log-convexity of `p ↦ shiftForm L a c p` through the
discriminant, the geometric bound caps that sequence by `D·(R²)^p`, and `ratio_le_of_geometric` says
a nonnegative log-convex sequence capped by `D·r^p` has first ratio at most `r`. No operator theory,
no completion, no spectral theorem.

DERIVED: the shift `2` is the doubled family's own; `R` and `B` are the caller's. -/
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

/-- `shiftForm_one_le` with both shifts written out. -/
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

/-- **The even moments decay at the rate.** `L(2k) ≤ (R²)^k·L 0`, from the shifted form at the single
lag `k`. Recorded because it is the cleanest visible consequence: the moment sequence has exponential
order at most `R`, which is Carleman's condition with room to spare, so the moment problem for `L` is
determinate as well as compactly supported. -/
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

/-! ## Part 6 — the test-function side, stated for what it is

`L` is summable, so the pairing with any bounded sequence converges absolutely. The index is the
lattice lag `ℕ`; this is not a distribution on `ℝ⁴` and not an Osterwalder–Schrader object. -/

/-- A geometrically bounded sequence is summable. -/
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

/-- **The pairing with a bounded test sequence converges absolutely.** `f ↦ ∑ₖ L k · f k` is a
bounded linear functional on the bounded sequences in content — the majorant is `(∑ₖ|L k|)·M`. It is
NOT bundled as a `ContinuousLinearMap` here, and its index is the lattice lag, so it is not a
distribution on `ℝ⁴`. -/
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

/-- **THE INFINITE-VOLUME TWO-POINT FUNCTION IS A BOUNDED MOMENT SEQUENCE, ON A DERIVED COUPLING
INTERVAL.**

On `[0,b)` — `b` from `StrongCoupling.core_rate_lt_one_of_small`, carrying no numeral — there is a
strictly increasing sequence of apertures `2·φ j + 1`, each carrying an EVEN lattice extent, along
which the Clay correlation converges at every lag to `L : ℕ → ℝ`, and `L` satisfies

* a positive contact term `e^{−128β}·δ₀ ≤ L 0`, with `δ₀ > 0` fixed before the coupling and the
  extent are chosen;
* `0 ≤ ∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ)` at EVERY finite family of lags and coefficients — full Hankel
  positivity, with no bound on the lags;
* at every rate `R` with `coreRate (16·4) β ≤ R < 1`: the geometric bound `|L k| ≤ B·R^k`, the
  SHIFTED Hankel positivity `∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ+2) ≤ R²·∑ᵢ∑ⱼ cᵢcⱼ L(aᵢ+aⱼ)`, and `Summable L`.

Those are jointly the hypothesis of the BOUNDED Hamburger moment problem: a sequence with both Hankel
conditions is the moment sequence of a positive measure supported in `[−R,R]`. The measure itself is
NOT constructed — Mathlib v4.31 has no moment problem — so what this theorem delivers is the complete
hypothesis and not the conclusion.

DERIVED: `2·φ j + 1` is the aperture whose extent is even, forced by the reflection geometry; `128`
and `16·4` are `InfiniteVolume`'s; the shift `2` is the doubled family's. No constant is chosen. -/
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
