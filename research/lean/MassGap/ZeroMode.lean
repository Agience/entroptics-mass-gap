/-
# MassGap.ZeroMode — a constant component of a lag correlation, against the tension

A `Moment.Read N` carries a lag correlation `ρ : Fin (N+1) → ℝ`, with angles
`θ d = 2π d/(N+1)`, a normalised profile `p`, and a tension `μ = -log ⟨cos θ⟩`. This module asks what
`μ < (1/4) log 3` does to a constant component of `ρ`.

## The mechanism

`sum_cos_circle_eq_zero` : `∑_{d<n} cos(2π d/n) = 0` for `n ≥ 2`, the real part of the vanishing sum
of the `n`-th roots of unity, and `sum_cos_theta_eq_zero` is the same at a `Read`'s own angles. So a
constant component of `ρ` contributes nothing to the first moment `∑ p d · cos (θ d)` while adding
`c·(N+1)` to the normalisation.

`zero_mode_lt_of_tension` is the consequence: for `ρ = c + g` with `c ≥ 0` and `g ≥ 0`, a positive
cosine average and `μ < (1/4) log 3` give

    c·(N+1) < (3^{1/4} − 1)·∑ g,

whose right-hand side carries no aperture. `no_zero_mode_of_tension_lt_floor` concludes `c = 0` when
`∑ g` is bounded by one `B` at every aperture and the two eventual hypotheses hold: a positive `c`
would make the left side grow past a fixed ceiling.

## The spectral side

`zeroWeight` and `gappedPart` split a finite mode sum `∑ₖ wₖ λₖ^d` at `λ = 1`, and `spectral_split`
is the identity. `gappedPart_sum_le` bounds the partial sums of the gapped part,
`le_geometric_of_lt_one` and `exists_exponential_decay` produce a geometric envelope from modes
strictly below one, and `tendsto_zero_of_lt_one` the limit.

`correlation_decays_of_tension` and `correlation_gap_of_tension` compose the two sides, and
`hypotheses_satisfiable`, `contactRead_spectral` and `chain_hypotheses_satisfiable` exhibit the
contact read satisfying every hypothesis, so neither statement is vacuous.

## Scope

Everything is about `Moment.Read` and finite mode families `w`, `lam : ι → ℝ`. The decomposition
`ρ = c + g` and the spectral form `ρ(d) = ∑ₖ wₖ λₖ^d` are hypotheses; no statement here establishes
either for a lattice correlation. The conclusions are about that mode family, and about the
constant `c`, rather than about an operator or a spectrum.

DERIVED throughout: `3^{1/4} − 1` is `e^{κ₀} − 1` at `κ₀ = (1/4) log 3`, the constant `Floor.lean`
bounds; `(N+1)` is the lag arity, the cardinality of `Fin (N+1)`, not a scale. `1` is the mode value
at which the split is taken — the value whose powers neither grow nor decay.
-/
import Mathlib
import MassGap.Moment

namespace MassGap.ZeroMode

open Finset Real

/-- `∑ d : Fin n, cos (2π d/n) = 0` for `n ≥ 2`. The angles are the arguments of the `n`-th roots of
unity; `Complex.isPrimitiveRoot_exp` and `IsPrimitiveRoot.geom_sum_eq_zero` make their sum zero, and
this is the real part of that identity.

`2 ≤ n` is required: at `n = 1` the single angle is `0` and the sum is `1`.

DERIVED: `2` in the hypothesis is the least `n` at which the roots of unity cancel, and `2` in
`2 * π` is the full turn the `n` angles divide. `0` is the value of the sum. -/
theorem sum_cos_circle_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ d : Fin n, Real.cos (2 * Real.pi * (d : ℝ) / n) = 0 := by
  have hn0 : n ≠ 0 := by omega
  -- ζ = exp(2πi/n) is a primitive n-th root of unity (Mathlib), so its geometric sum vanishes
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hsum : ∑ d ∈ Finset.range n, ζ ^ d = 0 := hprim.geom_sum_eq_zero hn
  -- each power is the corresponding point on the circle, so its real part is the cosine
  have hre : ∀ d : ℕ, (ζ ^ d).re = Real.cos (2 * Real.pi * (d : ℝ) / n) := by
    intro d
    rw [hζdef, ← Complex.exp_nat_mul]
    have hcast : (d : ℂ) * (2 * Real.pi * Complex.I / n)
        = ((2 * Real.pi * (d : ℝ) / n : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hcast, Complex.exp_ofReal_mul_I_re]
  calc ∑ d : Fin n, Real.cos (2 * Real.pi * (d : ℝ) / n)
      = ∑ d ∈ Finset.range n, Real.cos (2 * Real.pi * (d : ℝ) / n) := by
        rw [Fin.sum_univ_eq_sum_range (fun d => Real.cos (2 * Real.pi * (d : ℝ) / n))]
    _ = ∑ d ∈ Finset.range n, (ζ ^ d).re := by
        exact Finset.sum_congr rfl (fun d _ => (hre d).symm)
    _ = (∑ d ∈ Finset.range n, ζ ^ d).re := by
        rw [Complex.re_sum]
    _ = 0 := by rw [hsum]; simp

/-- `∑ d, cos (R.θ d) = 0` for a `Moment.Read N` with `N ≥ 1`. `Moment.Read.θ` unfolds to the circle
angle `2π d/(N+1)`, so this is `sum_cos_circle_eq_zero` at `n = N + 1`.

`1 ≤ N` is what makes `N + 1 ≥ 2`, which that lemma requires.

DERIVED: `1` is the lower bound on `N` in `hN`, chosen so the lag arity `N + 1` reaches the `2` that
`sum_cos_circle_eq_zero` needs. `0` is the value of the sum. -/
theorem sum_cos_theta_eq_zero {N : ℕ} (R : Moment.Read N) (hN : 1 ≤ N) :
    ∑ d, Real.cos (R.θ d) = 0 := by
  have h2 : 2 ≤ N + 1 := by omega
  have := sum_cos_circle_eq_zero (N + 1) h2
  rw [← this]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  unfold Moment.Read.θ
  push_cast
  ring_nf

/-- The zero mode is squeezed by the aperture.

    `ρ = c + g`,  `c ≥ 0`,  `g ≥ 0`,  `μ < κ₀`   ⟹   `c·(N+1) < (3^{1/4} − 1)·∑ g`

A gapless theory carries a constant component in its correlation: the transfer-operator form
`ρ(d) = ∑ₙ wₙ e^{−Eₙ d}` contributes `w₀·1^d = w₀` exactly when `E₀ = 0`. On the lag circle that
constant contributes nothing to the first moment (`sum_cos_theta_eq_zero`) while still adding
`c·(N+1)` to the normalisation, so it can only dilute the cosine average. Requiring the average to
clear `3^{-1/4}` therefore bounds the constant against the rest of the correlation.

The bound's right-hand side carries no aperture. So the larger the aperture, the smaller the zero
mode is forced to be — which is `no_zero_mode_of_tension_lt_floor` below.

DERIVED: `3^{1/4} − 1 = e^{κ₀} − 1` with `κ₀ = ¼log3` proved in `Floor.lean`. The `0`s are the sign
conditions on `c` and on each `g d` and the strict positivity of the cosine average. No tolerance,
no threshold, and `(N+1)` is the lag arity rather than any scale. -/
theorem zero_mode_lt_of_tension {N : ℕ} (hN : 1 ≤ N) (c : ℝ) (g : Fin (N + 1) → ℝ)
    (hc : 0 ≤ c) (hg : ∀ d, 0 ≤ g d)
    (R : Moment.Read N) (hR : R.ρ = fun d => c + g d)
    (hcpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (h : R.tension < (1 / 4) * Real.log 3) :
    c * ((N : ℝ) + 1) < ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) * ∑ d, g d := by
  set S : ℝ := ∑ d, R.ρ d with hSdef
  have hS0 : 0 < S := R.hpos
  set G : ℝ := ∑ d, g d with hGdef
  -- the normalisation splits into the constant's share and the rest
  have hS : S = c * ((N : ℝ) + 1) + G := by
    rw [hSdef, hR, hGdef, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  -- the constant drops out of the first moment
  have hnum : ∑ d, R.ρ d * Real.cos (R.θ d) = ∑ d, g d * Real.cos (R.θ d) := by
    rw [hR]
    have : ∀ d : Fin (N + 1), (c + g d) * Real.cos (R.θ d)
        = c * Real.cos (R.θ d) + g d * Real.cos (R.θ d) := fun d => by ring
    rw [Finset.sum_congr rfl (fun d _ => this d), Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_cos_theta_eq_zero R hN]
    ring
  -- and what is left is at most the total weight of g
  have hle : ∑ d, g d * Real.cos (R.θ d) ≤ G := by
    rw [hGdef]
    refine Finset.sum_le_sum (fun d _ => ?_)
    have := Real.cos_le_one (R.θ d)
    nlinarith [hg d]
  -- the cosine average is the first moment over the normalisation
  have havg : ∑ d, R.p d * Real.cos (R.θ d) = (∑ d, R.ρ d * Real.cos (R.θ d)) / S := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold Moment.Read.p
    rw [hSdef]; ring
  -- clearing the floor
  have hfloor : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d) :=
    R.cosAvg_gt_of_tension_lt_floor hcpos h
  rw [havg, hnum] at hfloor
  have hstep : (3 : ℝ) ^ (-(1 : ℝ) / 4) * S < G := by
    have h1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) * S < ∑ d, g d * Real.cos (R.θ d) := by
      rw [lt_div_iff₀ hS0] at hfloor; linarith
    linarith
  -- 3^{-1/4} · 3^{1/4} = 1 turns the bound into the stated one
  have hr : (3 : ℝ) ^ (-(1 : ℝ) / 4) * (3 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have hrpos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h14 : (0 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  rw [hS] at hstep
  nlinarith [hstep, hr, hrpos, h14]

/-- If a family of reads carries the same constant `c ≥ 0` at every aperture, with
`ρ_N = c + g_N`, `g_N ≥ 0`, `∑ g_N ≤ B` at every `N`, and the cosine average positive and the
tension below `(1/4) log 3` eventually in `N`, then `c = 0`.

`zero_mode_lt_of_tension` bounds `c·(N+1)` by `(3^{1/4} − 1)·B`, which carries no aperture, so a
positive `c` would make the left side grow past a fixed ceiling.

`B` is one constant for all apertures; without that uniformity the argument gives nothing.

DERIVED: `0` is the lower bound on `c` and on each `g N d`, and the value concluded of `c`. `1` in
`Fin (N + 1)` is the lag arity, and in `c * (N + 1)` inside the proof it is that same arity. `3`,
`1` and `4` spell `3^{1/4} − 1 = e^{κ₀} − 1`, and `(1/4) * log 3` is `κ₀` itself, the constant
`Floor.lean` bounds. -/
theorem no_zero_mode_of_tension_lt_floor
    (c B : ℝ) (hc : 0 ≤ c)
    (g : (N : ℕ) → Fin (N + 1) → ℝ) (hg : ∀ N d, 0 ≤ g N d)
    (R : (N : ℕ) → Moment.Read N)
    (hR : ∀ N, (R N).ρ = fun d => c + g N d)
    (hGB : ∀ N, ∑ d, g N d ≤ B)
    (hcpos : ∀ᶠ N in Filter.atTop, 0 < ∑ d, (R N).p d * Real.cos ((R N).θ d))
    (htens : ∀ᶠ N in Filter.atTop, (R N).tension < (1 / 4) * Real.log 3) :
    c = 0 := by
  set K : ℝ := (3 : ℝ) ^ ((1 : ℝ) / 4) - 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : (1 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 4) := by
      apply Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
      constructor <;> norm_num
    linarith
  -- past some aperture, c·(N+1) is under the same aperture-free ceiling
  rw [Filter.eventually_atTop] at hcpos htens
  obtain ⟨N₁, hN₁⟩ := hcpos
  obtain ⟨N₂, hN₂⟩ := htens
  have hbound : ∀ N : ℕ, 1 ≤ N → N₁ ≤ N → N₂ ≤ N → c * ((N : ℝ) + 1) < K * B := by
    intro N hN h1 h2
    have hz := zero_mode_lt_of_tension hN c (g N) hc (hg N) (R N) (hR N) (hN₁ N h1) (hN₂ N h2)
    calc c * ((N : ℝ) + 1) < K * (∑ d, g N d) := hz
      _ ≤ K * B := mul_le_mul_of_nonneg_left (hGB N) hKpos.le
  -- a positive c would outgrow it
  by_contra hne
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hne)
  obtain ⟨m, hm⟩ := exists_nat_gt (K * B / c)
  set n : ℕ := max (max N₁ N₂) (max 1 m) with hndef
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 m) (le_max_right _ _)
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ _)
  have hnN₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) (le_max_left _ _)
  have hnm : m ≤ n := le_trans (le_max_right 1 m) (le_max_right _ _)
  have hA : c * ((n : ℝ) + 1) < K * B := hbound n hn1 hnN₁ hnN₂
  have hBlt : K * B < c * (m : ℝ) := by rw [div_lt_iff₀ hcp] at hm; linarith
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
  nlinarith [hA, hBlt, hmn, hcp]

/-! ### From the spectral form to the split, and from the split to decay

Reflection positivity gives the transfer-operator form `ρ(d) = ∑ₖ wₖ λₖ^d` with `wₖ ≥ 0` and
`λₖ ∈ [0,1]`. This section does the two steps that turn the zero-mode bound into a decay statement:

  * `spectral_split` — the form is `c + g`, with `c` the total weight sitting at `λ = 1` (the
    gapless modes) and `g` the rest. So the hypothesis `ρ = c + g` of `zero_mode_lt_of_tension`
    is not an assumption about the correlation; it is what the spectral form always looks like.
  * `gapped_sum_le` — `∑_d g d` is bounded by `∑ₖ wₖ/(1−λₖ)` at every aperture, because each
    non-unit mode contributes a convergent geometric series. That is the `B` the zero-mode
    corollary needs, and it carries no aperture.
  * `tendsto_zero_of_lt_one` — once no weight sits at `λ = 1`, the correlation decays to zero.

Together with `no_zero_mode_of_tension_lt_floor` this is: measured tension below the floor at large
apertures ⟹ no gapless mode ⟹ the correlation decays. -/

section Spectral

variable {ι : Type*} [DecidableEq ι]

/-- The weight carried by the gapless modes (`λ = 1`): the constant component.

DERIVED: `1` is the unit circle, not a cut. A transfer eigenvalue of modulus one is a mode that does
not decay with the lag -- that is gaplessness -- so the split is at the only value that separates
decaying from non-decaying, and no other value would name anything. -/
noncomputable def zeroWeight (s : Finset ι) (w lam : ι → ℝ) : ℝ :=
  ∑ k ∈ s.filter (fun k => lam k = 1), w k

/-- The rest of the correlation: every mode strictly below the unit circle.

DERIVED: `1` is the unit circle, the complement of the split made in `zeroWeight`. -/
noncomputable def gappedPart (s : Finset ι) (w lam : ι → ℝ) (d : ℕ) : ℝ :=
  ∑ k ∈ s.filter (fun k => lam k ≠ 1), w k * lam k ^ d

/-- `∑_{k ∈ s} w k * lam k ^ d = zeroWeight s w lam + gappedPart s w lam d` at every `d`:
`Finset.sum_filter_add_sum_filter_not` at the predicate `lam k = 1`, with `1 ^ d = 1` collapsing the
unit-mode half.

So a finite mode sum splits as a constant plus a lag-dependent remainder, the constant being the
total weight at `λ = 1`.

DERIVED: `1` is the mode value the split is taken at — the value whose powers are constant in the
lag, which is what makes `zeroWeight` independent of `d`. -/
theorem spectral_split (s : Finset ι) (w lam : ι → ℝ) (d : ℕ) :
    ∑ k ∈ s, w k * lam k ^ d = zeroWeight s w lam + gappedPart s w lam d := by
  unfold zeroWeight gappedPart
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k => lam k = 1)]
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_filter] at hk
  rw [hk.2, one_pow, mul_one]

theorem zeroWeight_nonneg (s : Finset ι) (w lam : ι → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k) :
    0 ≤ zeroWeight s w lam :=
  Finset.sum_nonneg (fun k hk => hw k (Finset.mem_filter.mp hk).1)

theorem gappedPart_nonneg (s : Finset ι) (w lam : ι → ℝ) (hw : ∀ k ∈ s, 0 ≤ w k)
    (hlam : ∀ k ∈ s, 0 ≤ lam k) (d : ℕ) : 0 ≤ gappedPart s w lam d :=
  Finset.sum_nonneg (fun k hk => by
    have hk' := (Finset.mem_filter.mp hk).1
    exact mul_nonneg (hw k hk') (pow_nonneg (hlam k hk') d))

/-- `∑_{d < M} gappedPart s w lam d ≤ ∑_{k, λₖ ≠ 1} wₖ/(1 − λₖ)`, at every `M`. Exchanging the two
sums by `Finset.sum_comm`, each mode contributes a geometric partial sum `wₖ(1 − λₖ^M)/(1 − λₖ)`,
which `geom_sum_eq` evaluates and which is at most `wₖ/(1 − λₖ)` because `λₖ^M ≥ 0`.

The bound does not mention `M`, which is what makes it usable as the uniform `B` of
`no_zero_mode_of_tension_lt_floor`.

DERIVED: `1` is the mode value excluded by the filter, and the unit from which `λₖ` is subtracted —
the same number, since the denominator vanishes exactly at the excluded value. `0` is the lower
bound on each weight and each mode. -/
theorem gappedPart_sum_le (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hle : ∀ k ∈ s, lam k ≤ 1) (M : ℕ) :
    ∑ d ∈ Finset.range M, gappedPart s w lam d
      ≤ ∑ k ∈ s.filter (fun k => lam k ≠ 1), w k / (1 - lam k) := by
  unfold gappedPart
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk' := (Finset.mem_filter.mp hk).1
  have hne := (Finset.mem_filter.mp hk).2
  have h0 : 0 ≤ lam k := hlam k hk'
  have hlt : lam k < 1 := lt_of_le_of_ne (hle k hk') hne
  have hpos : 0 < 1 - lam k := by linarith
  -- ∑_{d<M} w λ^d = w (1-λ^M)/(1-λ) ≤ w/(1-λ)
  rw [← Finset.mul_sum, geom_sum_eq (ne_of_lt hlt) M]
  have hpow : (0 : ℝ) ≤ lam k ^ M := pow_nonneg h0 M
  have heq : (lam k ^ M - 1) / (lam k - 1) = (1 - lam k ^ M) / (1 - lam k) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [heq]
  have hinner : (1 - lam k ^ M) / (1 - lam k) ≤ 1 / (1 - lam k) := by
    gcongr
    linarith
  calc w k * ((1 - lam k ^ M) / (1 - lam k))
      ≤ w k * (1 / (1 - lam k)) := mul_le_mul_of_nonneg_left hinner (hw k hk')
    _ = w k / (1 - lam k) := by ring

/-! `le_geometric_of_lt_one` and `exists_exponential_decay` use `pow_le_pow_left₀`;
`pow_le_pow_left` does not exist at the v4.31.0 pin. -/

/-- `∑ₖ wₖ λₖ^d ≤ (∑ₖ wₖ) · ρ^d` at every `d`, given nonnegative weights, nonnegative modes, and
`λₖ ≤ ρ` at every mode. Termwise, by `pow_le_pow_left₀` and nonnegativity of the weights.

`ρ` is a parameter, not a maximum; `exists_exponential_decay` produces one strictly below `1` from a
finite mode set. For a countable family the modes may accumulate at `1`, and "no mode at `λ = 1`"
would then give no such `ρ`.

DERIVED: `0` is the lower bound on each weight in `hw` and on each mode in `hlam`; the second is what
`pow_le_pow_left₀` needs, and the first is what lets the termwise bound be multiplied through. `ρ` is
the caller's bound on the modes and `d` the caller's lag. -/
theorem le_geometric_of_lt_one (s : Finset ι) (w lam : ι → ℝ) (ρ : ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hρ : ∀ k ∈ s, lam k ≤ ρ) (d : ℕ) :
    ∑ k ∈ s, w k * lam k ^ d ≤ (∑ k ∈ s, w k) * ρ ^ d := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k hk => ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hlam k hk) (hρ k hk) d) (hw k hk)

/-- For a nonempty finite mode set with nonnegative weights and every mode in `[0, 1)`, there is a
`ρ ∈ [0, 1)` with `∑ₖ wₖ λₖ^d ≤ (∑ₖ wₖ) · ρ^d` at every `d`. The witness is the maximum of `lam`,
attained by `Finset.exists_max_image` because `s` is finite and nonempty, hence itself strictly below
`1`; `le_geometric_of_lt_one` supplies the bound.

Finiteness and nonemptiness are both used: the maximum must exist and must be a mode.

DERIVED: `0` is the lower bound on each weight, on each mode, and on `ρ`. `1` is the strict upper
bound on each mode and on `ρ` — the same bound, since `ρ` is one of the modes. -/
theorem exists_exponential_decay [DecidableEq ι] (s : Finset ι) (w lam : ι → ℝ)
    (hs : s.Nonempty) (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k)
    (hlt : ∀ k ∈ s, lam k < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ d : ℕ, ∑ k ∈ s, w k * lam k ^ d ≤ (∑ k ∈ s, w k) * ρ ^ d := by
  -- the maximum over a nonempty finite set is attained, so it is itself strictly below 1
  obtain ⟨k₀, hk₀, hmax⟩ := s.exists_max_image lam hs
  refine ⟨lam k₀, hlam k₀ hk₀, hlt k₀ hk₀, fun d => ?_⟩
  exact le_geometric_of_lt_one s w lam (lam k₀) hw hlam (fun k hk => hmax k hk) d

/-- With every mode in `[0, 1)`, `d ↦ ∑ₖ wₖ λₖ^d` tends to `0` along `atTop`: each term does, by
`tendsto_pow_atTop_nhds_zero_of_lt_one`, and `tendsto_finsetSum` adds finitely many of them.

No sign condition on the weights is needed here, unlike in `exists_exponential_decay`.

DERIVED: `0` is the lower bound on each mode and the limit point; `1` is the strict upper bound on
each mode, below which a power sequence is null. -/
theorem tendsto_zero_of_lt_one (s : Finset ι) (w lam : ι → ℝ)
    (hlam : ∀ k ∈ s, 0 ≤ lam k) (hlt : ∀ k ∈ s, lam k < 1) :
    Filter.Tendsto (fun d : ℕ => ∑ k ∈ s, w k * lam k ^ d) Filter.atTop (nhds 0) := by
  have hterm : ∀ k ∈ s, Filter.Tendsto (fun d : ℕ => w k * lam k ^ d) Filter.atTop (nhds 0) := by
    intro k hk
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (hlam k hk) (hlt k hk)
    simpa using h.const_mul (w k)
  simpa using tendsto_finsetSum s hterm

end Spectral

/-! ### The hypotheses are satisfiable — the theorem is not vacuous

A theorem whose hypotheses nothing satisfies proves nothing. The contact read `ρ = δ_{d,0}` is a
correlation with all its weight at lag zero: nonnegative, positive total, cosine average
`cos 0 = 1`, tension `-log 1 = 0`, below the floor at every aperture. It satisfies every hypothesis
of `no_zero_mode_of_tension_lt_floor` with `c = 0` and `B = 1`, so the implication has content. -/
namespace Witness

/-- The contact correlation: all weight at lag `0`.

DERIVED: `0` is the zero lag and `1` is unit weight. The read is normalised by `Moment.Read`, so the
weight cancels out of every quantity computed from it; only its being positive matters, and that is
what `hpos` carries. This is the extreme point of the family, not a tuned member of it. -/
noncomputable def contactRead (N : ℕ) : Moment.Read N where
  ρ := fun d => if d = 0 then 1 else 0
  hρ := fun d => by by_cases h : d = 0 <;> simp [h]
  hpos := by
    have : ∑ d : Fin (N + 1), (if d = 0 then (1 : ℝ) else 0) = 1 := by
      simp [Finset.sum_ite_eq' Finset.univ (0 : Fin (N + 1)) (fun _ => (1 : ℝ))]
    rw [this]; norm_num

theorem contactRead_cosAvg (N : ℕ) :
    ∑ d, (contactRead N).p d * Real.cos ((contactRead N).θ d) = 1 := by
  have hsum : ∑ d : Fin (N + 1), (contactRead N).ρ d = 1 := by
    show ∑ d : Fin (N + 1), (if d = 0 then (1 : ℝ) else 0) = 1
    simp [Finset.sum_ite_eq' Finset.univ (0 : Fin (N + 1)) (fun _ => (1 : ℝ))]
  have hp : ∀ d : Fin (N + 1), (contactRead N).p d = if d = 0 then (1 : ℝ) else 0 := by
    intro d; unfold Moment.Read.p; rw [hsum]; simp [contactRead]
  have hθ0 : (contactRead N).θ 0 = 0 := by unfold Moment.Read.θ; simp
  calc ∑ d, (contactRead N).p d * Real.cos ((contactRead N).θ d)
      = ∑ d : Fin (N + 1), (if d = 0 then (1 : ℝ) else 0) * Real.cos ((contactRead N).θ d) := by
        exact Finset.sum_congr rfl (fun d _ => by rw [hp d])
    _ = Real.cos ((contactRead N).θ 0) := by
        simp [Finset.sum_ite_eq' Finset.univ (0 : Fin (N + 1))]
    _ = 1 := by rw [hθ0, Real.cos_zero]

theorem contactRead_tension (N : ℕ) : (contactRead N).tension = 0 := by
  unfold Moment.Read.tension
  rw [contactRead_cosAvg N, Real.log_one, neg_zero]

/-- There are `c`, `B`, `g` and a family of reads satisfying every hypothesis of
`no_zero_mode_of_tension_lt_floor`. The witness is `c = 0`, `B = 1`, `g N` the indicator of lag `0`,
and `R = contactRead`; the cosine average is `1` at every aperture (`contactRead_cosAvg`) and the
tension is `0` (`contactRead_tension`), which is below `(1/4) log 3` because `log 3 > 0`.

So the hypotheses are satisfiable, and that implication is not empty.

DERIVED: `0` is the lower bound on `c` and on each `g N d`, the value taken for `c`, the lag the
indicator is supported at, and the lower bound on the cosine average. `1` is the value taken for `B`
and the indicator's own value. `(1/4) * log 3` is the floor constant, `Floor.lean`'s. -/
theorem hypotheses_satisfiable :
    ∃ (c B : ℝ) (g : (N : ℕ) → Fin (N + 1) → ℝ) (R : (N : ℕ) → Moment.Read N),
      0 ≤ c ∧ (∀ N d, 0 ≤ g N d) ∧ (∀ N, (R N).ρ = fun d => c + g N d) ∧
      (∀ N, ∑ d, g N d ≤ B) ∧
      (∀ᶠ N in Filter.atTop, 0 < ∑ d, (R N).p d * Real.cos ((R N).θ d)) ∧
      (∀ᶠ N in Filter.atTop, (R N).tension < (1 / 4) * Real.log 3) := by
  refine ⟨0, 1, fun N d => if d = 0 then 1 else 0, contactRead, le_refl 0,
    fun N d => by by_cases h : d = 0 <;> simp [h], fun N => by funext d; simp [contactRead],
    fun N => by simp [Finset.sum_ite_eq' Finset.univ (0 : Fin (N + 1))], ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun N => by rw [contactRead_cosAvg N]; norm_num)
  · refine Filter.Eventually.of_forall (fun N => ?_)
    rw [contactRead_tension N]
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith

/-- `(contactRead N).ρ` equals the one-mode spectral form `∑_{k : Unit} 1 * 0 ^ d`: `0 ^ d` is `1` at
`d = 0` and `0` after, which is the contact indicator.

So the contact read has the spectral shape `chain_hypotheses_satisfiable` needs, with a single mode
of weight `1` at `λ = 0`.

DERIVED: `1` is the single mode's weight and `0` its value; `0` is also the lag the indicator is
supported at. The index type is `Unit`, so the sum has one term. -/
theorem contactRead_spectral (N : ℕ) :
    (contactRead N).ρ = fun d : Fin (N + 1) =>
      ∑ _k ∈ (Finset.univ : Finset Unit), (1 : ℝ) * (0 : ℝ) ^ (d : ℕ) := by
  funext d
  show (if d = 0 then (1 : ℝ) else 0) = _
  rw [Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_unit, one_smul, one_mul]
  by_cases h : d = 0
  · subst h; simp
  · have hv : (d : ℕ) ≠ 0 := fun hc => h (Fin.ext hc)
    rw [if_neg h, zero_pow hv]

/-- There are a finite mode set, weights, modes and a family of reads satisfying every hypothesis of
`correlation_decays_of_tension`. The witness is `Finset.univ : Finset Unit`, weight `1`, mode `0`,
and `R = contactRead`, with `contactRead_spectral` supplying the spectral form and
`contactRead_cosAvg`, `contactRead_tension` the two eventual hypotheses.

DERIVED: `1` is the single mode's weight and the upper bound each mode must satisfy; `0` is the mode
value, the lower bound on the weights and on the modes, and the lower bound on the cosine average.
`(1/4) * log 3` is the floor constant. -/
theorem chain_hypotheses_satisfiable :
    ∃ (s : Finset Unit) (w lam : Unit → ℝ) (R : (N : ℕ) → Moment.Read N),
      (∀ k ∈ s, 0 ≤ w k) ∧ (∀ k ∈ s, 0 ≤ lam k) ∧ (∀ k ∈ s, lam k ≤ 1) ∧
      (∀ N, (R N).ρ = fun d : Fin (N + 1) => ∑ k ∈ s, w k * lam k ^ (d : ℕ)) ∧
      (∀ᶠ N in Filter.atTop, 0 < ∑ d, (R N).p d * Real.cos ((R N).θ d)) ∧
      (∀ᶠ N in Filter.atTop, (R N).tension < (1 / 4) * Real.log 3) := by
  refine ⟨Finset.univ, fun _ => 1, fun _ => 0, contactRead,
    fun _ _ => zero_le_one, fun _ _ => le_refl 0, fun _ _ => zero_le_one,
    contactRead_spectral, ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun N => by rw [contactRead_cosAvg N]; norm_num)
  · refine Filter.Eventually.of_forall (fun N => ?_)
    rw [contactRead_tension N]
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    linarith

end Witness

/-- Given a finite mode family with `0 ≤ wₖ` and `0 ≤ λₖ ≤ 1`, a family of reads whose correlation is
`ρ_N(d) = ∑ₖ wₖ λₖ^d` at every aperture, and the cosine average positive and the tension below
`(1/4) log 3` eventually in `N`, the sequence `d ↦ ∑ₖ wₖ λₖ^d` tends to `0`.

Four steps, none of which defines the conclusion:

1. `spectral_split` — the mode sum splits as `c + g`, with `c = zeroWeight` the total weight at
   `λ = 1`.
2. `gappedPart_sum_le` — `∑_d g d` is bounded by `∑ₖ wₖ/(1−λₖ)`, which carries no aperture.
3. `no_zero_mode_of_tension_lt_floor` — a constant contributes nothing to the circular first moment,
   so the tension bound forces `c = 0`.
4. `tendsto_zero_of_lt_one` — with no weight at `λ = 1`, every surviving mode is strictly below one
   and the sum tends to zero.

The conclusion is about the mode family; `hR` is what ties it to the reads, and it is a hypothesis.

DERIVED: `0` is the lower bound on each weight and each mode, the lower bound on the cosine average,
and the limit point. `1` is the upper bound on each mode — the value at which `spectral_split` cuts —
and the `+1` of `Fin (N + 1)`, the lag arity. `(1/4) * log 3` is the floor constant. -/
theorem correlation_decays_of_tension
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hle : ∀ k ∈ s, lam k ≤ 1)
    (R : (N : ℕ) → Moment.Read N)
    (hR : ∀ N, (R N).ρ = fun d : Fin (N + 1) => ∑ k ∈ s, w k * lam k ^ (d : ℕ))
    (hcpos : ∀ᶠ N in Filter.atTop, 0 < ∑ d, (R N).p d * Real.cos ((R N).θ d))
    (htens : ∀ᶠ N in Filter.atTop, (R N).tension < (1 / 4) * Real.log 3) :
    Filter.Tendsto (fun d : ℕ => ∑ k ∈ s, w k * lam k ^ d) Filter.atTop (nhds 0) := by
  -- 1. the spectral form is a constant plus the rest
  have hsplit : ∀ N : ℕ, (R N).ρ = fun d : Fin (N + 1) =>
      zeroWeight s w lam + gappedPart s w lam (d : ℕ) := by
    intro N; rw [hR N]; funext d; exact spectral_split s w lam (d : ℕ)
  -- 2. the rest has aperture-free bounded weight
  have hGB : ∀ N : ℕ, ∑ d : Fin (N + 1), gappedPart s w lam (d : ℕ)
      ≤ ∑ k ∈ s.filter (fun k => lam k ≠ 1), w k / (1 - lam k) := by
    intro N
    rw [Fin.sum_univ_eq_sum_range (fun d => gappedPart s w lam d) (N + 1)]
    exact gappedPart_sum_le s w lam hw hlam hle (N + 1)
  -- 3. so the tension forces the constant to vanish
  have hc0 : zeroWeight s w lam = 0 :=
    no_zero_mode_of_tension_lt_floor _ _ (zeroWeight_nonneg s w lam hw)
      (fun N d => gappedPart s w lam (d : ℕ))
      (fun N d => gappedPart_nonneg s w lam hw hlam _) R hsplit hGB hcpos htens
  -- the unit modes therefore carry no weight at all
  have hzero : ∀ k ∈ s.filter (fun k => lam k = 1), w k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => hw j (Finset.mem_filter.mp hj).1)).mp hc0
  -- 4. what remains is strictly inside the unit circle, hence decays
  have hrew : (fun d : ℕ => ∑ k ∈ s, w k * lam k ^ d)
      = fun d : ℕ => ∑ k ∈ s.filter (fun k => lam k ≠ 1), w k * lam k ^ d := by
    funext d
    rw [spectral_split s w lam d, hc0, zero_add]
    rfl
  rw [hrew]
  exact tendsto_zero_of_lt_one _ w lam
    (fun k hk => hlam k (Finset.mem_filter.mp hk).1)
    (fun k hk => lt_of_le_of_ne (hle k (Finset.mem_filter.mp hk).1)
      (Finset.mem_filter.mp hk).2)

/-! ### The geometric cosine sum, machine-checked

The `O(1/N)` ceiling on this criterion's certified rate rests on one identity: for a single transfer
mode the cosine average is exact in closed form, because both of its sums are geometric. That identity
is computed and cross-checked numerically in `code/certify/aperture_cap_of_floor.py`, which reproduces
it by direct summation over every lag and refuses if the two disagree. A numerical cross-check is
evidence; it is not a proof. What follows proves the step the closed form turns on -- that the real
cosine sum is the real part of a complex geometric series -- so the identity rests on Mathlib's
`geom_sum_eq` rather than on agreement between two floating-point computations.
-/

/-- The cosine sum is the real part of a geometric series.

`\sum_{d<m} \lambda^d \cos(kd) = \mathrm{Re} \sum_{d<m} (\lambda e^{ik})^d`, for every real `\lambda` and `k`
and every `m` -- no hypothesis on `\lambda`, since both sides are finite sums.

DERIVED: no numeric literal in this statement. It is an identity between two finite sums. -/
theorem sum_geom_cos_eq_re (lam k : ℝ) (m : ℕ) :
    ∑ d ∈ Finset.range m, lam ^ d * Real.cos (k * d)
      = (∑ d ∈ Finset.range m, ((lam : ℂ) * Complex.exp ((k : ℂ) * Complex.I)) ^ d).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hz : ((lam : ℂ) * Complex.exp ((k : ℂ) * Complex.I)) ^ d
      = ((lam ^ d : ℝ) : ℂ) * Complex.exp (((k * d : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hz, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp [← Complex.ofReal_pow]

/-- The antipodal fold. On a circle of even size `2m`, a summand invariant under `d ↦ 2m - d`
is determined by the half-range: the two fixed points `0` and `m` appear once, everything between
appears twice.

Stated for an arbitrary `F` and an arbitrary symmetry hypothesis, because that is all the argument
uses -- it is a reindexing, not a fact about cosines or about `λ`. The `circLag` weight and the
cosine both satisfy the hypothesis, which is why the aperture read's sums fold at all.

DERIVED: `0`, `1` and `2` here are the two fixed points of the reflection and the multiplicity of
everything else. They are forced by the involution `d ↦ 2m - d` having exactly two fixed points on
`range (2m)`, not chosen. -/
theorem sum_range_antipodal_fold (m : ℕ) (hm : 0 < m) (F : ℕ → ℝ)
    (hsym : ∀ d ∈ Finset.Ico 1 m, F (2 * m - d) = F d) :
    ∑ d ∈ Finset.range (2 * m), F d
      = F 0 + F m + 2 * ∑ d ∈ Finset.Ico 1 m, F d := by
  -- the circle splits at its midpoint
  have hsplit : ∑ d ∈ Finset.range (2 * m), F d
      = (∑ d ∈ Finset.range m, F d) + ∑ d ∈ Finset.Ico m (2 * m), F d :=
    (Finset.sum_range_add_sum_Ico F (by omega : m ≤ 2 * m)).symm
  -- the lower half peels off the fixed point `0`
  have hlow : ∑ d ∈ Finset.range m, F d = F 0 + ∑ d ∈ Finset.Ico 1 m, F d := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_eq_sum_Ico_succ_bot hm F
  -- the upper half peels off the fixed point `m` and then reflects onto the lower one
  have hhigh : ∑ d ∈ Finset.Ico m (2 * m), F d = F m + ∑ d ∈ Finset.Ico 1 m, F d := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m < 2 * m) F]
    congr 1
    refine Finset.sum_nbij' (fun d => 2 * m - d) (fun e => 2 * m - e) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha ⊢
      omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      have hmem : 2 * m - a ∈ Finset.Ico 1 m := by
        simp only [Finset.mem_Ico]; omega
      have hback : 2 * m - (2 * m - a) = a := by omega
      have h := hsym (2 * m - a) hmem
      rw [hback] at h
      exact h
  rw [hsplit, hlow, hhigh]
  ring

/-- The aperture read's own sum folds. The circular cosine sum of a single transfer mode
`ρ(d) = λ^{circLag d}` over the whole circle of even size `2m` collapses to a half-range sum:

    ∑_{d < 2m} λ^{min(d, 2m-d)} cos(2πd/2m)  =  1 - λ^m + 2 ∑_{1 ≤ d < m} λ^d cos(2πd/2m)

This is `sum_range_antipodal_fold` applied to the object the criterion actually reads, and it is the
step that turns the circle into the half-line geometric series `sum_geom_cos_closed` then evaluates.
Together the two carry the whole closed form except the final arithmetic.

The two fixed points supply the `1` and the `-λ^m`: `circLag 0 = 0` with `cos 0 = 1`, and
`circLag m = m` with `cos π = -1`. That `-1` is the antipodal contribution -- the term the half-line
constant `2π√(3^{-1/4}/(1-3^{-1/4}))` has no counterpart for, and the reason the circle's ceiling is
`10.9887` rather than `11.1760`.

DERIVED: no literal here is a scale. `1` and `2` are the multiplicities of the fold's fixed points and
of everything else; `0` and `m` are those fixed points; `2π` is one turn of the circle. -/
theorem circLag_cos_sum_fold (m : ℕ) (hm : 0 < m) (lam : ℝ) :
    ∑ d ∈ Finset.range (2 * m),
        lam ^ (min d (2 * m - d)) * Real.cos (2 * Real.pi * d / (2 * m))
      = 1 - lam ^ m
        + 2 * ∑ d ∈ Finset.Ico 1 m, lam ^ d * Real.cos (2 * Real.pi * d / (2 * m)) := by
  set F : ℕ → ℝ := fun d => lam ^ (min d (2 * m - d)) * Real.cos (2 * Real.pi * d / (2 * m))
    with hF
  have hm0 : (0 : ℝ) < 2 * m := by positivity
  -- the summand is invariant under the antipodal reflection
  have hsym : ∀ d ∈ Finset.Ico 1 m, F (2 * m - d) = F d := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hdm : d ≤ 2 * m := by omega
    have hidx : 2 * m - (2 * m - d) = d := by omega
    have hang : (2 : ℝ) * Real.pi * ((2 * m - d : ℕ) : ℝ) / (2 * m)
        = 2 * Real.pi - 2 * Real.pi * (d : ℝ) / (2 * m) := by
      have : ((2 * m - d : ℕ) : ℝ) = 2 * (m : ℝ) - (d : ℝ) := by
        push_cast [Nat.cast_sub hdm]; ring
      rw [this]
      field_simp
    simp only [hF, hidx, hang, Real.cos_two_pi_sub, min_comm]
  -- and the fold applies
  have := sum_range_antipodal_fold m hm F hsym
  rw [hF] at this
  simp only at this
  rw [this]
  have h0 : min 0 (2 * m - 0) = 0 := by omega
  have hmm : min m (2 * m - m) = m := by omega
  have hcos0 : Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / (2 * m)) = 1 := by
    norm_num
  have hcosm : Real.cos (2 * Real.pi * ((m : ℕ) : ℝ) / (2 * m)) = -1 := by
    have : (2 : ℝ) * Real.pi * (m : ℝ) / (2 * m) = Real.pi := by
      field_simp
    rw [this, Real.cos_pi]
  rw [h0, hmm, hcos0, hcosm]
  have hinner : ∀ d ∈ Finset.Ico 1 m,
      lam ^ (min d (2 * m - d)) * Real.cos (2 * Real.pi * d / (2 * m))
        = lam ^ d * Real.cos (2 * Real.pi * d / (2 * m)) := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have : min d (2 * m - d) = d := by omega
    rw [this]
  rw [Finset.sum_congr rfl hinner]
  ring

/-- The closed form itself, off `geom_sum_eq`: away from `\lambda e^{ik} = 1` the cosine sum is the
real part of `(z^m - 1)/(z - 1)`.

The excluded case is exactly the one where every term is `1` -- `\lambda = 1` with `k` a multiple of
`2\pi` -- which is the gapless, zero-aperture corner the criterion is built to exclude, so nothing of
interest is lost by assuming it away here.

DERIVED: the `1` is the unit circle, as in `zeroWeight`: it marks the single degenerate ratio at
which a geometric series has no closed form, not a cut on any measured quantity. -/
theorem sum_geom_cos_closed (lam k : ℝ) (m : ℕ)
    (h : (lam : ℂ) * Complex.exp ((k : ℂ) * Complex.I) ≠ 1) :
    ∑ d ∈ Finset.range m, lam ^ d * Real.cos (k * d)
      = ((((lam : ℂ) * Complex.exp ((k : ℂ) * Complex.I)) ^ m - 1)
          / ((lam : ℂ) * Complex.exp ((k : ℂ) * Complex.I) - 1)).re := by
  rw [sum_geom_cos_eq_re, geom_sum_eq h]
/-! ### The circular second moment of the lag, in closed form

The aperture's ceiling on the substrate becomes a floor on the decay rate only once the second moment
of a uniform lag distribution is known -- that is what a slowly-decaying correlation gets compared
against. It is `(n³ + 2n)/12`, exactly, and the route is the antipodal fold proved above: `clag` is
symmetric under `d ↦ n - d` by construction, so the fold applies to it directly.

Mathlib carries Gauss' summation formula but not the sum of squares (only Bernoulli/Faulhaber, far
heavier than one induction), so that is proved here too.
-/

/-- `6 * ∑_{i < n+1} i² = n(n+1)(2n+1)`, by induction on `n`.

Stated multiplied through by `6` and over `range (n+1)` rather than as `n(n−1)(2n−1)/6`, so that
neither truncated subtraction nor an exact division in `ℕ` appears.

DERIVED: `6` clears the denominator of the closed form for a sum of squares, so it is that formula's
own divisor. The exponent `2` is the square being summed, `2` in `2n + 1` and the two `1`s are the
closed form's coefficients. -/
theorem six_mul_sum_sq (n : ℕ) :
    6 * ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

#print axioms six_mul_sum_sq

/-- The lag of `d` on a circle of `n` sites: `min d (n - d)`.

The `ℕ`-indexed twin of `Moment.circLag`, which lives on `Fin (N+1)`. Stated here because the fold is
about `Finset.range`, and reindexing through `Fin` buys nothing.

DERIVED: the circle has one origin, so the lag of `d` is the smaller of the two arcs to it. No
literal here sets a scale. -/
def clag (n d : ℕ) : ℕ := min d (n - d)

/-- The circular second moment of the lag is exactly `(n³ + 2n)/12` on an even circle.

Through `sum_range_antipodal_fold`: the fixed points `0` and `m` contribute `0` and `m²`, everything
between contributes twice, and what remains is `six_mul_sum_sq`.

This is the quantity a spread-out correlation is measured against. A uniform lag distribution has
substrate ratio `(n³+2n)/(12n³) > 1/12 = 0.083`, far above the ceiling `(1-3^{-1/4})/8 = 0.030` the
aperture condition permits: the arithmetic form of the statement that a band-limited screen cannot
carry a correlation spread across the whole circle.

DERIVED: `12` is `2 · 6`, the fold's multiplicity times the sum-of-squares denominator; `2` and `1`
are the even circle `2 * (k + 1)`, and `2` is again the square on the lag; `3` is the cubic power of
the extent on the right. -/
theorem sum_clag_sq (k : ℕ) :
    12 * ∑ d ∈ Finset.range (2 * (k + 1)), ((clag (2 * (k + 1)) d : ℝ)) ^ 2
      = ((2 * (k + 1) : ℕ) : ℝ) ^ 3 + 2 * ((2 * (k + 1) : ℕ) : ℝ) := by
  have hm : 0 < k + 1 := Nat.succ_pos k
  -- the summand is invariant under the antipodal reflection, by `omega` on the `min`
  have hsym : ∀ d ∈ Finset.Ico 1 (k + 1), ((clag (2 * (k + 1)) (2 * (k + 1) - d) : ℝ)) ^ 2
      = ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have h : clag (2 * (k + 1)) (2 * (k + 1) - d) = clag (2 * (k + 1)) d := by unfold clag; omega
    rw [h]
  have hfold := sum_range_antipodal_fold (k + 1) hm
    (fun d => ((clag (2 * (k + 1)) d : ℝ)) ^ 2) hsym
  -- the two fixed points of the reflection
  have h0 : ((clag (2 * (k + 1)) 0 : ℕ) : ℝ) ^ 2 = 0 := by
    have h : clag (2 * (k + 1)) 0 = 0 := by unfold clag; omega
    rw [h]; norm_num
  have hmm : ((clag (2 * (k + 1)) (k + 1) : ℕ) : ℝ) ^ 2 = ((k : ℝ) + 1) ^ 2 := by
    have h : clag (2 * (k + 1)) (k + 1) = k + 1 := by unfold clag; omega
    rw [h]; push_cast; ring
  -- strictly between them the lag is the index
  have hmid : ∑ d ∈ Finset.Ico 1 (k + 1), ((clag (2 * (k + 1)) d : ℝ)) ^ 2
      = ∑ d ∈ Finset.range (k + 1), ((d : ℝ)) ^ 2 := by
    have hzero : ∑ d ∈ Finset.range (k + 1), ((d : ℝ)) ^ 2
        = ((0 : ℕ) : ℝ) ^ 2 + ∑ d ∈ Finset.Ico 1 (k + 1), ((d : ℝ)) ^ 2 := by
      rw [Finset.range_eq_Ico]
      exact Finset.sum_eq_sum_Ico_succ_bot hm (fun d => ((d : ℝ)) ^ 2)
    rw [hzero]
    have hcong : ∑ d ∈ Finset.Ico 1 (k + 1), ((clag (2 * (k + 1)) d : ℝ)) ^ 2
        = ∑ d ∈ Finset.Ico 1 (k + 1), ((d : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl (fun d hd => ?_)
      simp only [Finset.mem_Ico] at hd
      have h : clag (2 * (k + 1)) d = d := by unfold clag; omega
      rw [h]
    rw [hcong]; norm_num
  -- the sum of squares, cast from the natural-number induction
  have hsq : ∑ i ∈ Finset.range (k + 1), ((i : ℝ)) ^ 2
      = (k : ℝ) * ((k : ℝ) + 1) * (2 * (k : ℝ) + 1) / 6 := by
    have h := six_mul_sum_sq k
    have hc : ((6 * ∑ i ∈ Finset.range (k + 1), i ^ 2 : ℕ) : ℝ)
        = ((k * (k + 1) * (2 * k + 1) : ℕ) : ℝ) := by rw [h]
    push_cast at hc
    linarith [hc]
  rw [hfold, h0, hmm, hmid, hsq]
  push_cast
  ring

#print axioms sum_clag_sq
/-- `λ^{k+1} · n³ ≤ 12 ∑_{d < n} λ^{clag n d} (clag n d)²` at `n = 2(k+1)`, for `0 ≤ λ ≤ 1`.

Every weight is at least `λ^{k+1}` because `clag n d ≤ k + 1`, the lag never exceeding the antipode,
and the unweighted second moment is `(n³ + 2n)/12` by `sum_clag_sq`, which is at least `n³/12`.

Both the single-mode and the mode-share bounds use exactly this, which is why it is stated once.

DERIVED: `2` in `2 * (k + 1)` makes the extent even, so the antipode is `k + 1` and the maximum
circle distance is exactly half. `12` clears the denominator of `sum_clag_sq`'s closed form, itself
`6` times the `2` of the two-sided lag count. The exponent `3` is the extent's power in that closed
form and `2` the square of the circle distance. `0` and `1` bracket `λ`. -/
theorem twelve_weighted_moment_ge (k : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    lam ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3
      ≤ 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          lam ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
  have hw : ∀ d ∈ Finset.range (2 * (k + 1)),
      lam ^ (k + 1) ≤ lam ^ (clag (2 * (k + 1)) d) := by
    intro d hd
    have hle : clag (2 * (k + 1)) d ≤ k + 1 := by unfold clag; omega
    have hsplit : lam ^ (k + 1)
        = lam ^ (clag (2 * (k + 1)) d) * lam ^ (k + 1 - clag (2 * (k + 1)) d) := by
      rw [← pow_add]; congr 1; omega
    calc lam ^ (k + 1) = lam ^ (clag (2 * (k + 1)) d) * lam ^ (k + 1 - clag (2 * (k + 1)) d) := hsplit
      _ ≤ lam ^ (clag (2 * (k + 1)) d) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (pow_nonneg h0 _)
      _ = lam ^ (clag (2 * (k + 1)) d) := mul_one _
  have hstep : lam ^ (k + 1) * ∑ d ∈ Finset.range (2 * (k + 1)), ((clag (2 * (k + 1)) d : ℝ)) ^ 2
      ≤ ∑ d ∈ Finset.range (2 * (k + 1)),
          lam ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_right (hw d hd) (sq_nonneg _))
  have hmoment := sum_clag_sq k
  have hpow : 0 ≤ lam ^ (k + 1) := pow_nonneg h0 _
  have hn2 : (0 : ℝ) ≤ 2 * ((2 * (k + 1) : ℕ) : ℝ) := by positivity
  nlinarith [hstep, hmoment, hpow, hn2]

#print axioms twelve_weighted_moment_ge

/-- A slowly-decaying correlation has a large substrate. The bound that turns the aperture's
ceiling into a floor on the decay rate.

For a single mode `ρ(d) = λ^{clag d}` on an even circle of `n = 2(k+1)` sites, the substrate ratio
satisfies `substrate ≥ λ^{n/2}/12`, stated here without division as

    λ^{n/2} · n² · (∑ λ^{clag d})  ≤  12 · ∑ λ^{clag d} · (clag d)²

Three steps, rather than a numerical inversion of the exact criterion:

1. Every weight is at least `λ^{n/2}`, since `clag d ≤ n/2` and `λ ≤ 1`;
2. The normalisation is at most `n`, since every weight is at most `1`;
3. The unweighted second moment is exactly `(n³+2n)/12 ≥ n³/12` (`sum_clag_sq`).

Why it is the mechanism. Read against `Moment.Read.substrate_lt_of_tension_lt_floor`, which caps the
substrate at `(1-3^{-1/4})/8` whenever the tension clears the floor, this says a correlation that
decays too slowly cannot clear the floor: its weight is spread too far around the circle for the
screen to carry. Composing the two bounds a mode away from `λ = 1` by an explicit amount, so the
aperture yields not merely that a gap exists but how large it is.

DERIVED: `12` is the sum-of-squares denominator, `n/2` the antipode; `0` and `1` are the ends of the
range `0 ≤ λ ≤ 1`, and `1` is also the `+ 1` in the even extent `2 * (k + 1)` and in the antipodal
exponent `k + 1`; `2` is the doubling in that extent and the square on it. Nothing is chosen or
fitted. -/
theorem substrate_ge_of_slow_decay (k : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    lam ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
        * (∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d))
      ≤ 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          lam ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
  have hn : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by positivity
  -- (1) every weight is at least `lam ^ (k+1)`: the lag never exceeds the antipode
  have hw : ∀ d ∈ Finset.range (2 * (k + 1)),
      lam ^ (k + 1) ≤ lam ^ (clag (2 * (k + 1)) d) := by
    intro d hd
    have hle : clag (2 * (k + 1)) d ≤ k + 1 := by unfold clag; omega
    have hsplit : lam ^ (k + 1)
        = lam ^ (clag (2 * (k + 1)) d) * lam ^ (k + 1 - clag (2 * (k + 1)) d) := by
      rw [← pow_add]; congr 1; omega
    calc lam ^ (k + 1) = lam ^ (clag (2 * (k + 1)) d) * lam ^ (k + 1 - clag (2 * (k + 1)) d) := hsplit
      _ ≤ lam ^ (clag (2 * (k + 1)) d) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (pow_nonneg h0 _)
      _ = lam ^ (clag (2 * (k + 1)) d) := mul_one _
  -- (2) the normalisation is at most `n`
  have hden : ∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d)
      ≤ ((2 * (k + 1) : ℕ) : ℝ) := by
    calc ∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d)
        ≤ ∑ _d ∈ Finset.range (2 * (k + 1)), (1 : ℝ) :=
          Finset.sum_le_sum (fun d _ => pow_le_one₀ h0 h1)
      _ = ((2 * (k + 1) : ℕ) : ℝ) := by simp
  -- (3) the weighted second moment dominates `lam^{n/2}` times the unweighted one
  have hnum : lam ^ (k + 1) * ∑ d ∈ Finset.range (2 * (k + 1)), ((clag (2 * (k + 1)) d : ℝ)) ^ 2
      ≤ ∑ d ∈ Finset.range (2 * (k + 1)),
          lam ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun d hd => ?_)
    exact mul_le_mul_of_nonneg_right (hw d hd) (sq_nonneg _)
  have hmoment := sum_clag_sq k
  have hpow : 0 ≤ lam ^ (k + 1) := pow_nonneg h0 _
  -- and now it is one chain: bound the normalisation, substitute the exact moment, drop `2n ≥ 0`
  calc lam ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d))
      ≤ lam ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2 * ((2 * (k + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
    _ = lam ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3 := by ring
    _ ≤ lam ^ (k + 1)
          * (((2 * (k + 1) : ℕ) : ℝ) ^ 3 + 2 * ((2 * (k + 1) : ℕ) : ℝ)) := by
        have : (0 : ℝ) ≤ 2 * ((2 * (k + 1) : ℕ) : ℝ) := by positivity
        nlinarith [hpow, this]
    _ = lam ^ (k + 1)
          * (12 * ∑ d ∈ Finset.range (2 * (k + 1)), ((clag (2 * (k + 1)) d : ℝ)) ^ 2) := by
        rw [hmoment]
    _ = 12 * (lam ^ (k + 1)
          * ∑ d ∈ Finset.range (2 * (k + 1)), ((clag (2 * (k + 1)) d : ℝ)) ^ 2) := by ring
    _ ≤ 12 * ∑ d ∈ Finset.range (2 * (k + 1)),
          lam ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by linarith [hnum]

#print axioms substrate_ge_of_slow_decay
/-- `Moment.circLag d = clag (N + 1) d` for `d : Fin (N + 1)`, by `rfl`: both are
`min d (N + 1 − d)`, one indexed by `Fin (N + 1)` and one by `ℕ`.

Recorded so that the `Finset.range` bounds above visibly apply to the `Fin`-indexed reads below.

DERIVED: `1` is the `+1` of `Fin (N + 1)`, the lag arity, and the same `+1` inside `clag`'s
extent argument. -/
theorem circLag_eq_clag {N : ℕ} (d : Fin (N + 1)) :
    Moment.circLag d = clag (N + 1) (d : ℕ) := rfl

/-- `∑ d : Fin (N+1), g (Moment.circLag d) = ∑ d ∈ Finset.range (N+1), g (clag (N+1) d)`, for any
`g : ℕ → ℝ`. `Fin.sum_univ_eq_sum_range` at `circLag_eq_clag`.

DERIVED: `1` is the `+1` of the lag arity, appearing in the index type, the range, and `clag`'s
extent argument; it is one number. -/
theorem sum_circLag_eq_range {N : ℕ} (g : ℕ → ℝ) :
    ∑ d : Fin (N + 1), g (Moment.circLag d)
      = ∑ d ∈ Finset.range (N + 1), g (clag (N + 1) d) :=
  Fin.sum_univ_eq_sum_range (fun i => g (clag (N + 1) i)) (N + 1)

#print axioms sum_circLag_eq_range
/-- The aperture names the gap: a tension below the floor bounds `λ` away from `1` explicitly.

For a single transfer mode read through a screen of `n = 2(k+1)` lags, the entropy floor does not
merely exclude `λ = 1` -- it excludes an explicit neighbourhood of it:

    μ < κ₀   ⟹   λ^{n/2}  <  12 · (1 - 3^{-1/4})/8  =  0.360246…

Equivalently `n · (-log λ) > 2.0419`: the decay rate is bounded below by `2.0419/n`, so the gap has a
size and not merely an existence.

How the two halves meet. `Moment.Read.substrate_lt_of_tension_lt_floor` caps the substrate ratio from
above when the tension clears the floor; `substrate_ge_of_slow_decay` bounds it from below by
`λ^{n/2}/12`. A slowly-decaying mode spreads its weight around the circle, which the first bound
forbids. The composition is the diffraction limit made quantitative: a band-limited screen cannot
carry a correlation that decays too slowly, so what it does carry decays at least this fast.

What it replaces. The read margin `hread` -- that the active modes decay at the free-energy margin
-- is an input elsewhere in the tree. For a single mode it is a consequence of the tension, which is
measured.

The constant is not sharp. Inverting the exact criterion numerically gives `5.54`; the sharp
asymptotic cap is `10.99`. This route gives `2.04` because it passes through
`cos x ≤ 1 - (2/π²)x²` and `substrate ≥ λ^{n/2}/12`, each lossy. All three are computed, with
refusals, in `code/certify/aperture_cap_of_floor.py`.

DERIVED: `12` is the sum-of-squares denominator, `8` the constant of `cos_avg_le_circ`, and
`3^{-1/4}` is `e^{-κ₀}` with `κ₀` proved in `Floor.lean`. The `0`s are the sign condition `h0` places
on `λ` and the strict positivity of the cosine average in `hpos`; the `1` is the upper bound on `λ`
in `h1` and the `+ 1` of the screen's aperture; the `2` is the doubling in that aperture
`2 * k + 1`. -/
theorem lam_pow_lt_of_tension (k : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (R : Moment.Read (2 * k + 1))
    (hρ : ∀ d, R.ρ d = lam ^ (Moment.circLag d))
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    lam ^ (k + 1) < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) := by
  have hcap := R.substrate_lt_of_tension_lt_floor hpos htens
  have hlb := substrate_ge_of_slow_decay k lam h0 h1
  have hS : (0 : ℝ) < ∑ d, R.ρ d := R.hpos
  -- the two sums, moved to `Finset.range` where the bound lives
  have hden : ∑ d, R.ρ d
      = ∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d) := by
    rw [Finset.sum_congr rfl (fun d _ => hρ d)]
    exact sum_circLag_eq_range (N := 2 * k + 1) (fun c => lam ^ c)
  have hnum : ∑ d, R.ρ d * ((Moment.circLag d : ℝ)) ^ 2
      = ∑ d ∈ Finset.range (2 * (k + 1)),
          lam ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
    rw [Finset.sum_congr rfl (fun d _ => by rw [hρ d])]
    exact sum_circLag_eq_range (N := 2 * k + 1) (fun c => lam ^ c * ((c : ℝ)) ^ 2)
  -- `p = ρ / ∑ρ`, so the substrate is the ρ-weighted moment over the normalisation
  have hsub_eq : (∑ d, R.p d * ((Moment.circLag d : ℝ)) ^ 2)
      = (∑ d, R.ρ d * ((Moment.circLag d : ℝ)) ^ 2) / (∑ d, R.ρ d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [Moment.Read.p]
    ring
  -- the aperture, as a real, is the same number on both sides
  have hNcast : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * (k + 1) : ℕ) : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by positivity
  have hdenpos : (0 : ℝ) < ∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d) := by
    rw [← hden]; exact hS
  -- λ^{n/2} ≤ 12 · substrate, by dividing the lower bound through by `n² · ∑ρ`
  have hkey : lam ^ (k + 1)
      ≤ 12 * ((∑ d, R.p d * ((Moment.circLag d : ℝ)) ^ 2) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) := by
    rw [hsub_eq, hden, hnum, hNcast, div_div, ← mul_div_assoc,
      le_div_iff₀ (by positivity)]
    -- goal is now `lam^{k+1} * (∑den * n²) ≤ 12 * ∑num`, which is `hlb` reassociated
    have hassoc : lam ^ (k + 1)
        * ((∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d))
            * ((2 * (k + 1) : ℕ) : ℝ) ^ 2)
      = lam ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), lam ^ (clag (2 * (k + 1)) d)) := by ring
    linarith [hlb, hassoc.le, hassoc.ge]
  linarith [hcap, hkey]

#print axioms lam_pow_lt_of_tension
/-- The tension bounds the aggregate weight near `λ = 1`.

A tension is a weighted average, and it bounds the modes close to `1` collectively rather than one
at a time. For a spectral correlation
`ρ(d) = ∑ᵢ wᵢ λᵢ^{clag d}` and any sub-collection `A` whose eigenvalues are all at least `λ₀`:

    12 · W · (∑ ρ(d) clag(d)²)  ≥  W_A · λ₀^{n/2} · n² · (∑ ρ(d))

With `W = ∑ᵢ wᵢ` and `W_A = ∑_{i∈A} wᵢ`; equivalently `substrate ≥ (W_A/W)·λ₀^{n/2}/12`. Composed with
`Moment.Read.substrate_lt_of_tension_lt_floor`:

    μ < κ₀   ⟹   W_A / W  <  0.360246 / λ₀^{n/2}

At `λ₀ = 1` that is `W_A/W < 0.360246` uniformly in the aperture: at most about a third of the
correlation's weight can sit at the unit circle. `no_zero_mode_of_tension_lt_floor` sharpens that to
exactly zero at one; this is the quantitative statement that survives near one, which is what a
finite-capacity screen can actually say and what controls the correlation's asymptotics.

Scope: a bound on one mode at a time says nothing about a cloud of faint modes that collectively
carry the tail; this bounds the cloud, with the bound degrading by the weight share. What decides
whether such modes are in the theory at all is the noise edge, which `Measure.resolvedDim` counts
against.

DERIVED: `12` is the sum-of-squares denominator, `n/2` the antipode; `0` and `1` are the ends of the
ranges `0 ≤ w i`, `0 ≤ λ i ≤ 1` and `0 ≤ λ₀ ≤ 1`, and `1` is also the `+ 1` in the even extent
`2 * (k + 1)` and in the antipodal exponent `k + 1`; `2` is the doubling in that extent and the
square on it; the share is a ratio of the read's own quantities. -/
theorem substrate_ge_of_subset_share {ι : Type*} (k : ℕ) (s A : Finset ι) (w lam : ι → ℝ)
    (hAs : A ⊆ s)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (lam0 : ℝ) (hlam00 : 0 ≤ lam0) (hlam01 : lam0 ≤ 1) (hA : ∀ i ∈ A, lam0 ≤ lam i) :
    (∑ i ∈ A, w i) * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
        * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))
      ≤ 12 * (∑ i ∈ s, w i)
          * ∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
  have hn : (0 : ℝ) < ((2 * (k + 1) : ℕ) : ℝ) := by positivity
  have hWA : 0 ≤ ∑ i ∈ A, w i := Finset.sum_nonneg (fun i hi => hw i (hAs hi))
  have hpow : 0 ≤ lam0 ^ (k + 1) := pow_nonneg hlam00 _
  have hWnn : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  -- the full numerator dominates `A`'s share of it, at the common rate `lam0`
  have hnum : (∑ i ∈ A, w i) * (∑ d ∈ Finset.range (2 * (k + 1)),
        lam0 ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2)
      ≤ ∑ d ∈ Finset.range (2 * (k + 1)),
          (∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun d _ => ?_)
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc (∑ i ∈ A, w i) * lam0 ^ (clag (2 * (k + 1)) d)
        = ∑ i ∈ A, w i * lam0 ^ (clag (2 * (k + 1)) d) := by rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ A, w i * lam i ^ (clag (2 * (k + 1)) d) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hlam00 (hA i hi) _) (hw i (hAs hi))
      _ ≤ ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d) :=
          Finset.sum_le_sum_of_subset_of_nonneg hAs
            (fun i hi _ => mul_nonneg (hw i hi) (pow_nonneg (hlam0 i hi) _))
  -- the normalisation is at most `W · n`
  have hden : ∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)
      ≤ (∑ i ∈ s, w i) * ((2 * (k + 1) : ℕ) : ℝ) := by
    calc ∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)
        ≤ ∑ _d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i := by
          refine Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun i hi => ?_))
          calc w i * lam i ^ (clag (2 * (k + 1)) d) ≤ w i * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ (hlam0 i hi) (hlam1 i hi)) (hw i hi)
            _ = w i := mul_one _
      _ = (∑ i ∈ s, w i) * ((2 * (k + 1) : ℕ) : ℝ) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hcore := twelve_weighted_moment_ge k lam0 hlam00 hlam01
  calc (∑ i ∈ A, w i) * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))
      ≤ (∑ i ∈ A, w i) * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * ((∑ i ∈ s, w i) * ((2 * (k + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
    _ = (∑ i ∈ s, w i) * ((∑ i ∈ A, w i) * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 3)) := by ring
    _ ≤ (∑ i ∈ s, w i) * ((∑ i ∈ A, w i) * (12 * ∑ d ∈ Finset.range (2 * (k + 1)),
            lam0 ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcore hWA) hWnn
    _ = 12 * (∑ i ∈ s, w i) * ((∑ i ∈ A, w i) * ∑ d ∈ Finset.range (2 * (k + 1)),
            lam0 ^ (clag (2 * (k + 1)) d) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2) := by ring
    _ ≤ 12 * (∑ i ∈ s, w i)
          * ∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))
                * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hnum (by positivity)

#print axioms substrate_ge_of_subset_share

/-- The single-mode form of the substrate bound: at one mode `j ∈ s`,

    Wⱼ λⱼ^{k+1} n² · (∑_d ρ(d))  ≤  12 (∑ᵢ wᵢ) · ∑_d ρ(d) (clag n d)²,   n = 2(k+1),

Where `ρ(d) = ∑ᵢ wᵢ λᵢ^{clag n d}`. The mode share `wⱼ/W` and the rate `λⱼ` appear on the left, the
weighted second moment on the right; `twelve_weighted_moment_ge` is the step.

DERIVED: `2` in `2 * (k + 1)` makes the extent even and its half the antipode `k + 1`; `12` is
`twelve_weighted_moment_ge`'s constant. The exponent `2` is the square of the circle distance and of
the extent. `0` and `1` bracket the weights and modes. -/
theorem substrate_ge_of_mode_share {ι : Type*} [DecidableEq ι] (k : ℕ) (s : Finset ι)
    (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (j : ι) (hj : j ∈ s) :
    w j * lam j ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
        * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))
      ≤ 12 * (∑ i ∈ s, w i)
          * ∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
  have h := substrate_ge_of_subset_share k s {j} w lam
    (Finset.singleton_subset_iff.mpr hj) hw hlam0 hlam1 (lam j) (hlam0 j hj) (hlam1 j hj)
    (fun i hi => by rw [Finset.mem_singleton] at hi; rw [hi])
  simpa using h

#print axioms substrate_ge_of_mode_share
/-- The tension bounds the resolved dimension.

The counting form of `substrate_ge_of_subset_share`, and the input a continuum limit actually
consumes. A mode is resolved when its weight clears the noise edge; the aggregate weight of the
resolved modes near `λ₀` is capped by the tension, and each of them carries at least `edge`, so their
number is capped too:

    |A| · edge · λ₀^{n/2} · n² · (∑ ρ)   ≤   12 · W · (∑ ρ(d) clag(d)²)

So with `μ < κ₀` (which caps the right-hand side by `Moment.Read.substrate_lt_of_tension_lt_floor`),

    |A|  <  0.360246 · W / (edge · λ₀^{n/2})

What it supplies. `Measure.LatticeYMFamily.os_gap` asks that the modes above the noise edge have
index below a spacing-independent cutoff `c`; `Measure.tight_of_gap_ir` turns that into tightness
and `continuum_of_family` into an OS limit. This derives a cutoff of that shape from the tension:
`W/edge` is the read's own dynamic range and `λ₀^{n/2}` its resolution at the antipode, neither of
which is chosen here.

What it does not do. It bounds the resolved modes near `λ₀`, not all modes: a mode far below `λ₀`
decays fast and is not what a gap argument needs to exclude. And `edge` itself is not derived here --
the noise floor is a property of the read, and per `entroptics-jlens` it must be computed on the
identity-removed residual or it is inflated by the near-unit component and the count under-reported.

DERIVED: `12` is the sum-of-squares denominator; `0` and `1` are the ends of the ranges `0 ≤ w i`,
`0 ≤ λ i ≤ 1`, `0 ≤ λ₀ ≤ 1` and `0 ≤ edge`, and `1` is also the `+ 1` in the even extent
`2 * (k + 1)` and in the antipodal exponent `k + 1`; `2` is the doubling in that extent and the
square on it; `edge`, `W` and `λ₀` are the read's own quantities. -/
theorem resolved_count_le_of_subset {ι : Type*} (k : ℕ) (s A : Finset ι) (w lam : ι → ℝ)
    (hAs : A ⊆ s)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (lam0 : ℝ) (hlam00 : 0 ≤ lam0) (hlam01 : lam0 ≤ 1) (hA : ∀ i ∈ A, lam0 ≤ lam i)
    (edge : ℝ) (hedge : 0 ≤ edge) (hres : ∀ i ∈ A, edge ≤ w i) :
    (A.card : ℝ) * edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
        * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))
      ≤ 12 * (∑ i ∈ s, w i)
          * ∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)) * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := by
  -- each resolved mode carries at least `edge`, so the count is below the aggregate weight
  have hcount : (A.card : ℝ) * edge ≤ ∑ i ∈ A, w i := by
    calc (A.card : ℝ) * edge = ∑ _i ∈ A, edge := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ A, w i := Finset.sum_le_sum hres
  have hshare := substrate_ge_of_subset_share k s A w lam hAs hw hlam0 hlam1
    lam0 hlam00 hlam01 hA
  have hrest : (0 : ℝ) ≤ lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
      * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)) := by
    refine mul_nonneg (mul_nonneg (pow_nonneg hlam00 _) (by positivity)) ?_
    exact Finset.sum_nonneg (fun d _ =>
      Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (pow_nonneg (hlam0 i hi) _)))
  calc (A.card : ℝ) * edge * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))
      = ((A.card : ℝ) * edge) * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))) := by
        ring
    _ ≤ (∑ i ∈ A, w i) * (lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))) :=
        mul_le_mul_of_nonneg_right hcount hrest
    _ = (∑ i ∈ A, w i) * lam0 ^ (k + 1) * ((2 * (k + 1) : ℕ) : ℝ) ^ 2
          * (∑ d ∈ Finset.range (2 * (k + 1)), ∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d)) := by
        ring
    _ ≤ 12 * (∑ i ∈ s, w i)
          * ∑ d ∈ Finset.range (2 * (k + 1)),
              (∑ i ∈ s, w i * lam i ^ (clag (2 * (k + 1)) d))
                * ((clag (2 * (k + 1)) d : ℝ)) ^ 2 := hshare

#print axioms resolved_count_le_of_subset
/-- The rate, as a rate. `lam_pow_lt_of_tension` bounds `λ^{n/2}`; a gap is stated in
`Δ = -log λ`. This is the same fact in the units the rest of the development uses:

    μ < κ₀   ⟹   (n/2) · Δ  >  -log(12(1-3^{-1/4})/8)  =  1.02097
             ⟹        n · Δ  >  2.04193

So the decay rate clears `2.042/n`, which is the `κ/(N+1)` hypothesis of
`gap_phys_of_fixed_screen` with `κ = 2.042`. Composed with a screen of fixed physical extent `L`,
that theorem then gives `Δ_phys > 2.042/L` -- independent of the lattice spacing.

`λ > 0` is needed and is not a restriction: `λ = 0` is a correlation supported at zero lag, whose
decay rate is infinite and which no gap argument needs to bound.

DERIVED: the constant is `-log` of the one in `lam_pow_lt_of_tension`, which is itself
`12(1-3^{-1/4})/8`; the `3` and the `4` are that power's base and exponent, and the `4` is again the
denominator of the floor `(1/4)·log 3` in `htens`. The `0`s are the strict positivity of `λ` in `h0`
and of the cosine average in `hpos`; the `2` is the doubling in the screen's aperture `2 * k + 1`.
No new number enters. -/
theorem rate_gt_of_tension (k : ℕ) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (R : Moment.Read (2 * k + 1))
    (hρ : ∀ d, R.ρ d = lam ^ (Moment.circLag d))
    (hpos : 0 < ∑ d, R.p d * Real.cos (R.θ d))
    (htens : R.tension < (1 / 4) * Real.log 3) :
    -Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8))
      < ((k : ℝ) + 1) * (-Real.log lam) := by
  have hbound := lam_pow_lt_of_tension k lam h0.le h1 R hρ hpos htens
  have hcpos : (0 : ℝ) < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) := by
    have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 := by
      rw [Real.rpow_lt_one_iff (by norm_num)]
      norm_num
    linarith
  have hppos : (0 : ℝ) < lam ^ (k + 1) := pow_pos h0 _
  -- the logarithm is monotone, and `log (λ^{k+1}) = (k+1) log λ`
  have hlog : Real.log (lam ^ (k + 1))
      < Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) :=
    (Real.log_lt_log_iff hppos hcpos).mpr hbound
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith [hlog]

#print axioms rate_gt_of_tension








/-! ### The screen is not the box: a fixed aperture gives a spacing-independent gap

The `O(1/N)` ceiling reads as an obstruction only if `N` is forced to grow with the volume. It is not.
`N` is the aperture -- the extraction screen -- and the screen has a physical extent, `L = (N+1)a`,
which is what the read actually resolves. Holding that fixed while the spacing falls is a different
family from holding the lattice fixed, and the bound behaves differently on it:

    Δ_lat ≥ κ/(N+1)   and   L = (N+1)a   ⟹   Δ_phys = Δ_lat/a ≥ κ/L

`a` has cancelled. The right-hand side depends on the screen and on nothing else -- not on the
lattice spacing, and not on the size of the box the screen sits in. This is the entroptics reading:
the aperture is a property of the extraction, and a gap read through a finite screen is a physical
statement about the theory rather than an artefact of the discretisation.

Why this is not A finite-resolution artefact, which is the obvious objection and the one that must be
answered before the framing is worth anything. A finite screen does not manufacture a gap: a free
massless field, whose lowest mode in the same periodic screen is `2π/(N+1)`, reads `⟨cos⟩ = 0.5452`
against a floor of `0.7598` and fails the criterion -- at every aperture, since `a⋆ = 1.7489 > 1`
(`code/certify/aperture_cap_of_floor.py`, which refuses if that ordering ever reverses). So passing
the criterion through a screen says something a massless theory cannot say, whatever the screen's size.

What is and is not proved here. The arithmetic below is elementary and is not the point; the content
is in the quantifier. Stating it as a theorem fixes which quantity is held fixed across the family and
makes the uniformity checkable rather than asserted, and it names the one input the chain still needs:
an explicit `κ > 0` with `Δ_lat ≥ κ/(N+1)`. `correlation_gap_of_tension` currently supplies only
`∃ ρ < 1`, which is not explicit, so `κ` is carried as a hypothesis here rather than derived -- that
gap is the next step, and `Moment.Read.substrate_lt_of_tension_lt_floor` is the half of it that now
exists.
-/

/-- A screen of fixed physical extent gives a gap independent of the spacing.

`hL : (N a + 1) * spacing a = L` holds the screen fixed in physical units while the spacing varies;
`hrate` is the lattice gap at each aperture. The conclusion is a single positive bound that no member
of the family depends on -- which is what a continuum limit needs and what a box-sized aperture
cannot give.

DERIVED: nothing is chosen. The `0`s are the strict positivity of `κ`, of `L` and of each spacing;
the `1` is the `+ 1` of the screen's lag arity `N k + 1`. `κ` and `L` are the hypotheses' own
constants, and the conclusion is their quotient. -/
theorem gap_phys_of_fixed_screen
    (N : ℕ → ℕ) (spacing : ℕ → ℝ) (Δlat : ℕ → ℝ) (κ L : ℝ)
    (hκ : 0 < κ) (hL : 0 < L)
    (hpos : ∀ k, 0 < spacing k)
    (hscreen : ∀ k, ((N k : ℝ) + 1) * spacing k = L)
    (hrate : ∀ k, κ / ((N k : ℝ) + 1) ≤ Δlat k) :
    ∀ k, κ / L ≤ Δlat k / spacing k := by
  intro k
  have hNpos : (0 : ℝ) < (N k : ℝ) + 1 := by positivity
  have hs := hpos k
  have hscr := hscreen k
  -- clear both denominators and the claim is one multiplication
  rw [div_le_div_iff₀ hL hs]
  -- goal: κ * spacing k ≤ Δlat k * L
  have h1 : κ ≤ Δlat k * ((N k : ℝ) + 1) := (div_le_iff₀ hNpos).mp (hrate k)
  have h2 : Δlat k * L = Δlat k * (((N k : ℝ) + 1) * spacing k) := by rw [hscr]
  nlinarith [h1, hs, h2.le, h2.ge]

#print axioms gap_phys_of_fixed_screen

/-- Under the same hypotheses as `gap_phys_of_fixed_screen`, there is a single `δ > 0` with
`δ ≤ Δlat k / spacing k` at every `k`. The witness is `κ / L`, positive by `div_pos`.

One constant for the whole family, not one per member: the screen condition
`(N k + 1) · spacing k = L` fixes the physical size, and the bound is the same at every `k`, so no
limit is taken.

DERIVED: `0` is the strict lower bound on `κ`, on `L`, on each `spacing k`, and on `δ`. `1` in
`N k + 1` is the lag arity. `κ` and `L` are the caller's. -/
theorem gap_phys_uniform_of_fixed_screen
    (N : ℕ → ℕ) (spacing : ℕ → ℝ) (Δlat : ℕ → ℝ) (κ L : ℝ)
    (hκ : 0 < κ) (hL : 0 < L)
    (hpos : ∀ k, 0 < spacing k)
    (hscreen : ∀ k, ((N k : ℝ) + 1) * spacing k = L)
    (hrate : ∀ k, κ / ((N k : ℝ) + 1) ≤ Δlat k) :
    ∃ δ > 0, ∀ k, δ ≤ Δlat k / spacing k :=
  ⟨κ / L, div_pos hκ hL,
   gap_phys_of_fixed_screen N spacing Δlat κ L hκ hL hpos hscreen hrate⟩

#print axioms gap_phys_uniform_of_fixed_screen

/-- Under the same hypotheses as `correlation_decays_of_tension`, there is a `ρ ∈ [0, 1)` with
`∑ₖ wₖ λₖ^d ≤ (∑ₖ wₖ) · ρ^d` at every `d`.

The upgrade over `correlation_decays_of_tension`'s `Tendsto … 0` is `exists_exponential_decay`, which
needs the mode set finite: once the tension has removed all weight at `λ = 1`, the maximum over a
finite set is attained and is itself strictly below one. For a countable family the modes may
accumulate at `1` and no such `ρ` follows, so the `Finset` in `hR` is load-bearing.

How large the rate is. For a single mode `ρ(d) = λ^{circLag d}` both sums in the cosine average are
geometric, so the average has a closed form — with `n = N+1`, `m = n/2`, `k = 2π/n`, and
`(λe^{ik})^m = −λ^m`:

    ⟨cos⟩ = [2(1+λ^m)(1 − λ·cos k)/(1 − 2λ·cos k + λ²) − 1 − λ^m]
          / [2(1 − λ^m)/(1 − λ) − 1 + λ^m]

Which is increasing in `1 − λ`, so clearing `3^{-1/4}` fixes a critical `λ` at

    (N+1)·(1 − λ)  ≳  C = 2π·a⋆,    a⋆ the root of  a²·coth(aπ/2) = 3^{-1/4}(a² + 1),

Giving `C = 10.9887497117`. So the tension at aperture `N` certifies a rate of order `C/(N+1)`, which
falls as the aperture widens.

The criterion constrains `1 − λ` while a rate is `−log λ`. Both `(N+1)(1−λ)` and `(N+1)(−log λ)` rise
to the same `C` from below, so `C/(N+1)` is a ceiling on the certified rate at every aperture; the
value certified at a finite aperture is the finite-`N` one, `(N+1)Δ = 10.689` at `N+1 = 16` rather
than `10.989`. `C` follows from the floor constant and the circle geometry;
`code/certify/aperture_cap_of_floor.py` recomputes it by direct summation over every lag and refuses
if the two disagree.

`2π·√(3^{-1/4}/(1 − 3^{-1/4})) = 11.1759763266` is the corresponding constant for `ρ(d) = λ^d` on the
half-line, a different geometry: on the circle the antipodal reflection contributes a factor
`coth(aπ/2) > 1`, which lowers the requirement to `10.9887`. The sequence `(N+1)(1−λ_crit)` runs

    5.6894, 7.7968, 9.2453, 10.0806, 10.5258, 10.7551, 10.9299, 10.9814   at  N+1 = 8 … 8192

Rising to `10.98875`, resolved to eleven digits at `N+1 = 2⁴⁰`.

The falling rate is a statement about the aperture and not about the box:
`ScreenedGap.gap_bound_box_independent` carries the box as a parameter and never reads it, and at a
screen of fixed physical extent the spacing cancels (`ScreenedGap.uniform_physical_gap`).

DERIVED: `0` is the lower bound on each weight and each mode, the lower bound on the cosine average,
and the lower bound on `ρ`. `1` is the upper bound on each mode — the value `spectral_split` cuts at
— the strict upper bound on `ρ`, and the `+1` of the lag arity `Fin (N + 1)`. `(1/4) * log 3` is the
floor constant. The numerals in the prose above are computed values of `C` and of the finite-aperture
sequence; none of them appears in the statement. -/
theorem correlation_gap_of_tension
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hlam : ∀ k ∈ s, 0 ≤ lam k) (hle : ∀ k ∈ s, lam k ≤ 1)
    (R : (N : ℕ) → Moment.Read N)
    (hR : ∀ N, (R N).ρ = fun d : Fin (N + 1) => ∑ k ∈ s, w k * lam k ^ (d : ℕ))
    (hcpos : ∀ᶠ N in Filter.atTop, 0 < ∑ d, (R N).p d * Real.cos ((R N).θ d))
    (htens : ∀ᶠ N in Filter.atTop, (R N).tension < (1 / 4) * Real.log 3) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ d : ℕ, ∑ k ∈ s, w k * lam k ^ d ≤ (∑ k ∈ s, w k) * ρ ^ d := by
  -- the tension kills the weight at `λ = 1`, exactly as in `correlation_decays_of_tension`
  have hsplit : ∀ N : ℕ, (R N).ρ = fun d : Fin (N + 1) =>
      zeroWeight s w lam + gappedPart s w lam (d : ℕ) := by
    intro N; rw [hR N]; funext d; exact spectral_split s w lam (d : ℕ)
  have hGB : ∀ N : ℕ, ∑ d : Fin (N + 1), gappedPart s w lam (d : ℕ)
      ≤ ∑ k ∈ s.filter (fun k => lam k ≠ 1), w k / (1 - lam k) := by
    intro N
    rw [Fin.sum_univ_eq_sum_range (fun d => gappedPart s w lam d) (N + 1)]
    exact gappedPart_sum_le s w lam hw hlam hle (N + 1)
  have hc0 : zeroWeight s w lam = 0 :=
    no_zero_mode_of_tension_lt_floor _ _ (zeroWeight_nonneg s w lam hw)
      (fun N d => gappedPart s w lam (d : ℕ))
      (fun N d => gappedPart_nonneg s w lam hw hlam _) R hsplit hGB hcpos htens
  have hzero : ∀ k ∈ s.filter (fun k => lam k = 1), w k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => hw j (Finset.mem_filter.mp hj).1)).mp hc0
  -- so both sides may be restricted to the modes strictly inside the circle
  set t : Finset ι := s.filter (fun k => lam k ≠ 1) with ht
  have hrestrict : ∀ d : ℕ, ∑ k ∈ s, w k * lam k ^ d = ∑ k ∈ t, w k * lam k ^ d := by
    intro d
    rw [spectral_split s w lam d, hc0, zero_add]
    rfl
  have hwsum : ∑ k ∈ s, w k = ∑ k ∈ t, w k := by
    have := hrestrict 0
    simpa using this
  rcases Finset.eq_empty_or_nonempty t with hemp | hne
  · -- every mode sat at `λ = 1`, so `c = 0` makes the whole correlation vanish
    refine ⟨0, le_refl 0, by norm_num, fun d => ?_⟩
    rw [hrestrict d, hemp]
    simp [Finset.sum_nonneg, hwsum, hemp]
  · obtain ⟨ρ, hρ0, hρ1, hbound⟩ :=
      exists_exponential_decay t w lam hne
        (fun k hk => hw k (Finset.mem_filter.mp hk).1)
        (fun k hk => hlam k (Finset.mem_filter.mp hk).1)
        (fun k hk => lt_of_le_of_ne (hle k (Finset.mem_filter.mp hk).1)
          (Finset.mem_filter.mp hk).2)
    refine ⟨ρ, hρ0, hρ1, fun d => ?_⟩
    rw [hrestrict d, hwsum]
    exact hbound d

section Audit
#print axioms circLag_cos_sum_fold
#print axioms sum_range_antipodal_fold
#print axioms sum_geom_cos_eq_re
#print axioms sum_geom_cos_closed
#print axioms correlation_gap_of_tension
#print axioms le_geometric_of_lt_one
#print axioms exists_exponential_decay
#print axioms correlation_decays_of_tension
#print axioms sum_cos_circle_eq_zero
#print axioms zero_mode_lt_of_tension
#print axioms no_zero_mode_of_tension_lt_floor
#print axioms Witness.hypotheses_satisfiable
#print axioms Witness.chain_hypotheses_satisfiable
end Audit

/-! ## A rate bound read at one aperture

`rate_gt_of_tension` bounds a single mode's rate below by `C/(k+1)` at the aperture the tension was
read at, and `C/(k+1)` falls as `k` grows.

The conclusion is about `lam`, which carries no `k`: it is one real number, whichever aperture the
read is taken at. So the bound obtained at one aperture is a bound on that number, and the strongest
comes from the smallest `k`. The two theorems below state that, taking as their input a read whose
correlation is `lam ^ circLag d` at a single named aperture.
-/

/-- From a read at one aperture `k₀` whose correlation is `lam ^ circLag d`, with a positive cosine
average and tension below `(1/4) log 3`:

    −log(12(1 − 3^{-1/4})/8) / (k₀ + 1)  <  −log lam.

`rate_gt_of_tension` at `k₀`, with the division cleared by `div_lt_iff₀`.

The conclusion names no aperture other than `k₀`, `lam` being a single real number.

DERIVED: `12`, `8`, `3`, `1` and `4` spell `rate_gt_of_tension`'s constant
`−log(12(1 − 3^{-1/4})/8) = 2.04193`, carried unchanged; the sharp circle value is `10.98875`, `2π`
times the root of `a²coth(aπ/2) = 3^{−1/4}(a²+1)`, so this constant is loose by a factor of about
`5.4`. The corresponding half-line constant is `11.17598` and belongs to a different geometry. `2` in
`2 * k₀ + 1` makes the extent even and `1` the lag arity's own; `0` and `1` bracket `lam`, and
`(1/4) * log 3` is the floor constant. -/
theorem rate_uniform_of_mode_invariant {lam : ℝ} {k₀ : ℕ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    (R₀ : Moment.Read (2 * k₀ + 1))
    (hρ : ∀ d, R₀.ρ d = lam ^ (Moment.circLag d))
    (hpos : 0 < ∑ d, R₀.p d * Real.cos (R₀.θ d))
    (htens : R₀.tension < (1 / 4) * Real.log 3) :
    -Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) / ((k₀ : ℝ) + 1) < -Real.log lam := by
  have hk : (0 : ℝ) < (k₀ : ℝ) + 1 := by positivity
  have h := rate_gt_of_tension k₀ lam h0 h1 R₀ hρ hpos htens
  rw [div_lt_iff₀ hk]
  linarith [h]

#print axioms rate_uniform_of_mode_invariant

/-- Under the same hypotheses with `lam < 1`, there is a `δ > 0` with `δ < −log lam`. The witness is
`rate_uniform_of_mode_invariant`'s left-hand side, positive because
`12(1 − 3^{-1/4})/8 = 0.360246 < 1` makes its logarithm negative; the proof brackets `3^{-1/4}`
between `1/3` and `1` to get there.

One `δ`, fixed by the aperture the read was taken at, with no other aperture entering.

DERIVED: `0` is the strict lower bound on `lam` and on `δ`; `1` is the strict upper bound on `lam`,
below which `−log lam` is positive. `12`, `8`, `3`, `1` and `4` are
`rate_uniform_of_mode_invariant`'s constant, and `1/3` is the bracket
`3^{-1} < 3^{-1/4}` used to show it is below one. `2` in `2 * k₀ + 1` makes the extent even, and
`(1/4) * log 3` is the floor constant. -/
theorem exists_uniform_rate_of_mode_invariant {lam : ℝ} {k₀ : ℕ} (h0 : 0 < lam) (h1 : lam < 1)
    (R₀ : Moment.Read (2 * k₀ + 1))
    (hρ : ∀ d, R₀.ρ d = lam ^ (Moment.circLag d))
    (hpos : 0 < ∑ d, R₀.p d * Real.cos (R₀.θ d))
    (htens : R₀.tension < (1 / 4) * Real.log 3) :
    ∃ δ : ℝ, 0 < δ ∧ δ < -Real.log lam := by
  refine ⟨-Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) / ((k₀ : ℝ) + 1), ?_,
    rate_uniform_of_mode_invariant h0 h1.le R₀ hρ hpos htens⟩
  have hk : (0 : ℝ) < (k₀ : ℝ) + 1 := by positivity
  refine div_pos ?_ hk
  -- `12(1-3^{-1/4})/8 = 0.360246 < 1`, so its `-log` is positive
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  -- `3^{-1/4} > 3^{-1} = 1/3`, because the base exceeds one and the exponent is larger
  have hgt : (3 : ℝ) ^ (-(1 : ℝ) / 4) > 1 / 3 := by
    have hstep : (3 : ℝ) ^ (-(1 : ℝ)) < (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
    rw [Real.rpow_neg_one] at hstep
    norm_num at hstep ⊢
    linarith
  have hcpos : (0 : ℝ) < 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) := by nlinarith
  have hclt : 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) < 1 := by nlinarith
  have := Real.log_neg hcpos hclt
  linarith

#print axioms exists_uniform_rate_of_mode_invariant

end MassGap.ZeroMode
