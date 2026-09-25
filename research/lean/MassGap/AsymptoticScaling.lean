import Mathlib
import MassGap.ClayAssembly
import MassGap.Running

/-!
# MassGap.AsymptoticScaling — a fixed two-loop running spacing, and the predicates built on it

## A form of the statement that every witness satisfies

`free_spacing_scaling_is_also_vacuous`: for any positive `m` tending to zero there exists a positive
spacing `a` tending to zero with `m β / a β` converging to a positive limit — witnessed by `a := m`
itself. So existentially quantifying the spacing makes the statement discharge for every such `m`,
whatever `m` is.

## The spacing this file fixes instead

`aRunStd N β = ((24π²β)/(11N²))^{51/121} · exp(−(12π²β)/(11N²))`, the two-loop running spacing of
`SU(N)` at the standard Wilson coupling `β = 2N/g²` (each plane counted once), with the scale `Λ` set to
`1`. The Wilson systems of this development count every plane twice, so their coupling `β` is the
standard `2β` (`PlaqCount.boltz_eq_std`), and their spacing is `aRun N β = aRunStd N (2β)`, at
`g² = N/β`, largest at `β = 17N²/(88π²)`. `N` is the colour count,
not a lattice extent: it enters only through `b₀`, `b₁` and `g² = 2N/β`. It is

    a(β)·Λ  =  (b₀ g²)^{−b₁/(2b₀²)} · exp(−1/(2b₀ g²)),        g² = 2N/β

at `b₀ = 11N/(3·16π²)` and `b₁ = 34N²/(3·(16π²)²)`, the coefficients of `μ dg/dμ = −b₀g³ − b₁g⁵`.
`Running` states the same coefficients as `11N/3` and `34N²/3`, the `SU(N)` values in the form
`μ dg/dμ = −(11N/3)g³/(16π²) − (34N²/3)g⁵/(16π²)²`; the `1/(16π²)` is part of the beta function, and
`aRunStd` carries it. The exponent is POSITIVE on the base written here: the formula carries
`(b₀g²)^{−b₁/(2b₀²)}`, and `b₀g² = 11N²/(24π²β)` (`b0_g_sq`) is the reciprocal of that base, so
inverting it flips the sign. The three identities `b1_over_two_b0_sq`, `one_over_four_N_b0` and
`b0_g_sq` evaluate `b₁/(2b₀²)`, `1/(4N b₀)` and `b₀g²` from those coefficients to the numerals `aRun`
carries. The colour count and `π` cancel from `b₁/(2b₀²) = 51/121`, so that exponent is the same for
every `SU(N)`. `aRun_pos` gives positivity for `1 ≤ N` and `0 < β`.

## The predicates

`AsymptoticScalingAt N m` says `m β / aRun N β` converges to a positive limit, `aRun N` being the
`SU(N)` spacing at colour count `N`. With `aRun` fixed rather than existential the predicate is a
constraint on `m` alone:
`asymptotic_scaling_is_satisfiable` gives `m = c · aRun N` as a witness, and
`asymptotic_scaling_has_content` shows `m = aRun N · exp(−β)` refutes it;
`asymptotic_scaling_is_a_real_constraint` states both together.

`decayAt` and `mLatAt` are the lag-one decay ratio `ρ(1)/ρ(0)` and `−log` of it.
`mLatAt_at_zero_coupling_is_junk` records `mLatAt 5 0 = 0`, a consequence of `Real.log 0 = 0` together
with `ρ(1) = 0` at zero coupling, so statements about `mLatAt` are guarded by `0 < decayAt`.
`mLatAt_nonneg` gives `0 ≤ mLatAt N β` at even extent `N + 1 = 2m` with `3 ≤ m`.

`fixed_colours_pins_the_spacing`: at one fixed colour count `N`, if `AsymptoticScalingAt N m` holds
and `m` is eventually at least a positive constant, then the `SU(N)` spacing `aRun N` is eventually at
least a positive constant. `aRun N` falls below every positive level arbitrarily far out
(`exists_beta_aRun_lt`), so `bounded_mass_fails_scaling` concludes that no `m` bounded below by a
positive constant satisfies `AsymptoticScalingAt N`.

`AsymptoticScalingJoint Nof` reads the lattice mass `mLatAt (Nof β) β` at an extent `Nof β` that
grows with the coupling, against `aRun 3`, the two-loop spacing of `SU(3)` at the Wilson coupling:
`mLatAt` reads `wilsonCorrAt`, whose ensemble `WilsonBridge.corrClay` is taken at colour count `3`. It
is a definition, and nothing in this file proves it.

No declaration here proves `AsymptoticScalingAt` or `AsymptoticScalingJoint` for `mLatAt`.

DERIVED: every numeral in `aRun` is evaluated from `b₀ = 11N/(3·16π²)`, `b₁ = 34N²/(3·(16π²)²)` and
`g² = 2N/β`. `51/121` is `b₁/(2b₀²)`; `24π²/11` in the base is `(b₀g²)⁻¹` per unit `β/N²`; `12π²/11`
in the exponential is `1/(4N b₀)` per `1/N²`, half the base constant; `2N/β` is the `SU(N)` relation
between the Wilson coupling and `g²`. CHOSEN: `Λ = 1`. The `3` in `AsymptoticScalingJoint`'s
`aRun 3` is the colour count of `WilsonBridge.corrClay`'s ensemble, `SU(3)`. `0` is positivity, and
the lags `1` and `0` in `decayAt` are the nearest-neighbour and contact separations.
-/

namespace MassGap.AsymptoticScaling

open Filter Topology

/-! ## 1. Quantifying the spacing existentially -/

/-- For any `m : ℝ → ℝ` that is everywhere positive and tends to `0`, there exists a positive `a`
tending to `0` and a positive `mphys` with `m β / a β → mphys`. The witness is `a := m` and
`mphys := 1`, the ratio being constantly `1` by `div_self`. So adding a convergence clause to an
existentially quantified spacing leaves the statement satisfied by every such `m`.

DERIVED: the `0`s are the pointwise positivity asked of `m` and of the produced `a`, the limit both
are asked to reach, and the positivity of `mphys`. The witness `mphys = 1` appears in the proof, not
in the statement. -/
theorem free_spacing_scaling_is_also_vacuous (m : ℝ → ℝ) (hm : ∀ β, 0 < m β)
    (h0 : Tendsto m atTop (nhds 0)) :
    ∃ a : ℝ → ℝ, (∀ β, 0 < a β) ∧ Tendsto a atTop (nhds 0) ∧
      ∃ mphys : ℝ, 0 < mphys ∧ Tendsto (fun β => m β / a β) atTop (nhds mphys) := by
  refine ⟨m, hm, h0, 1, one_pos, ?_⟩
  have h : (fun β => m β / m β) = fun _ => (1 : ℝ) :=
    funext fun β => div_self (ne_of_gt (hm β))
  rw [h]
  exact tendsto_const_nhds

#print axioms free_spacing_scaling_is_also_vacuous

/-! ## 2. The running spacing, from the beta function -/

/-- The two-loop running lattice spacing of `SU(N)` at colour count `N` and Wilson coupling `β`, with
`Λ` set to one: `((24π²β)/(11N²))^(51/121) · exp(−(12π²β)/(11N²))`. It is

    a(β)·Λ  =  (b₀ g²)^{−b₁/(2b₀²)} · exp(−1/(2b₀ g²))

at `b₀ = 11N/(3·16π²)`, `b₁ = 34N²/(3·(16π²)²)` (the coefficients of `μ dg/dμ = −b₀g³ − b₁g⁵`) and
`g² = 2N/β`, the relation between `g²` and the standard coupling of the Wilson action
`β · Σ_{planes} wilsonDensity`, each plane counted once, `wilsonDensity = 1 − Re tr/N`; the Lean Wilson
systems, which count each plane twice, read `aRun`. `N` enters only through `b₀`, `b₁` and `g²`, so
it is the number of colours and never a lattice extent. An `rpow` times an exponential; no hypothesis
on `N` or `β`, so the base may be zero or negative and `aRunStd_pos` is stated separately.

Against the lattice: `aRunStd 2 2.30 / aRunStd 2 2.40 ≈ 1.2856` and `aRunStd 2 2.40 / aRunStd 2 2.50 ≈ 1.2866`,
the two-loop ratios PAPER §8's `SU(2)` scaling test quotes as `1.286` and `1.287`; `Λ` cancels from
both.

With `u = 24π²β/(11N²)`, `aRunStd N β = u^{51/121} · exp(−u/2)`, which rises for `u < 102/121` and falls
beyond it. So at fixed `N` the spacing is largest, about `0.6105`, at `β = 17N²/(44π²) ≈ 0.0391·N²`,
and falls toward zero past it.

DERIVED: `51/121` is `b₁/(2b₀²)`, `b1_over_two_b0_sq`; `24`, `11` and the `2` of `π²` in the base are
`(b₀g²)⁻¹` at `g² = 2N/β`, the reciprocal of `b0_g_sq`'s right side; `12`, `11` and the `2` of `π²` in
the exponential are `1/(4N b₀)` times `β`, which is `1/(2b₀g²)`, `one_over_four_N_b0`; the `2` of each
`N²` comes from the same identities. `11N/3` and `34N²/3` are the coefficients `Running.b0_pos` and
`Running.b1_pos` are stated for; `16π²` is the normalisation of the beta function they sit in. The
figures above are `aRunStd` evaluated at the couplings named; `102/121 = 2 · 51/121` is where the
derivative `51/(121u) − 1/2` of the logarithm vanishes, and `17/44 = (102/121)·(11/24)` is that `u`
solved for `β/N²` up to the `π²`. CHOSEN: `Λ = 1`, a unit, which cancels from every ratio this file
forms. -/
noncomputable def aRunStd (N : ℕ) (β : ℝ) : ℝ :=
  ((24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) ^ (51 / 121 : ℝ)
    * Real.exp (-(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2))

#print axioms aRunStd

/-! ### The numerals of `aRunStd`, evaluated from the normalised coefficients

`aRunStd`'s `51/121`, `24π²/11` and `12π²/11` are written out in the definition. Each identity below
states that one of them IS the corresponding expression in `b₀ = 11N/(3·16π²)`,
`b₁ = 34N²/(3·(16π²)²)` and `g² = 2N/β`, with the right-hand side written in `aRunStd`'s own numerals, so
the definition is checked against the two-loop formula and not merely consistent with it. `Running`
defines no constants for `b₀` and `b₁`; the coefficients are written out here in the normalisation of
`μ dg/dμ = −b₀g³ − b₁g⁵`.
-/

/-- `(34N²/(3·(16π²)²)) / (2·(11N/(3·16π²))²) = 51/121` for `N ≠ 0`, by `field_simp; ring`. The
colour count and `π` cancel, so the value is independent of both. This is `aRunStd`'s rpow exponent.

DERIVED: `0` in `hN` is what `field_simp` needs to clear `N` from the denominators; `34`, the `2` of
`N ^ 2` and `3` are `b₁`'s numerator `34N²/3`; `16` and the `2` of `π ^ 2` are the `16π²` of the
normalisation, and the outer `2` on `(16π²)²` is its square at two loops; `11` and `3` are `b₀`'s
numerator `11N/3`; `2 *` and the `2` squaring `b₀` are the doubling and square in `b₁/(2b₀²)`;
`51/121` is `306/726` in lowest terms, which is `aRunStd`'s exponent. -/
theorem b1_over_two_b0_sq {N : ℝ} (hN : N ≠ 0) :
    (34 * N ^ 2 / (3 * (16 * Real.pi ^ 2) ^ 2)) / (2 * (11 * N / (3 * (16 * Real.pi ^ 2))) ^ 2)
      = 51 / 121 := by
  field_simp
  ring

#print axioms b1_over_two_b0_sq

/-- `1/(4N·(11N/(3·16π²))) = 12π²/(11N²)` for `N ≠ 0`, by `field_simp; ring`. Times `β` this is
`1/(2b₀g²)` at `g² = 2N/β`, the argument of `aRunStd`'s exponential factor `exp(−(12π²β)/(11N²))`.

DERIVED: `0` in `hN` is what `field_simp` needs to clear `N`; `1` and `4` are `1/(4N b₀)`, the
two-loop exponent `1/(2b₀g²)` at `g² = 2N/β` divided by `β`; `11`, `3`, `16` and the `2` of `π ^ 2`
are `b₀ = 11N/(3·16π²)`; `12`, `11` and the `2`s on the right are the same quantity multiplied out,
`3·16/(4·11) = 12/11`, which is what `aRunStd` carries. -/
theorem one_over_four_N_b0 {N : ℝ} (hN : N ≠ 0) :
    1 / (4 * N * (11 * N / (3 * (16 * Real.pi ^ 2)))) = 12 * Real.pi ^ 2 / (11 * N ^ 2) := by
  field_simp
  ring

#print axioms one_over_four_N_b0

/-- `(11N/(3·16π²))·(2N/β) = 11N²/(24π²β)` for `β ≠ 0`, by `field_simp; ring`. This is `b₀ g²` at
the `SU(N)` relation `g² = 2N/β`, the reciprocal of `aRunStd`'s rpow base `(24π²β)/(11N²)`.

DERIVED: `0` in `hβ` is what `field_simp` needs to clear `β`; `11`, `3`, `16` and the `2` of `π ^ 2`
are `b₀ = 11N/(3·16π²)`; `2` in `2 * N` is the `SU(N)` relation `g² = 2N/β`; `11`, `24` and the `2`s
on the right are the product multiplied out, `22/48 = 11/24` in lowest terms. -/
theorem b0_g_sq {N β : ℝ} (hβ : β ≠ 0) :
    (11 * N / (3 * (16 * Real.pi ^ 2))) * (2 * N / β) = 11 * N ^ 2 / (24 * Real.pi ^ 2 * β) := by
  field_simp
  ring

#print axioms b0_g_sq


/-- `0 < aRunStd N β` for `1 ≤ N` and `0 < β`. The rpow base `(24π²β)/(11N²)` is positive by
`positivity` under both hypotheses (`π > 0` is `positivity`'s own), so `Real.rpow_pos_of_pos`
applies, and the exponential factor is positive unconditionally. `1 ≤ N` is what keeps `(N : ℝ)` away
from zero.

DERIVED: `1` in `hN` is the least colour count at which `N²` is nonzero, so the rpow base is defined
and positive; the `0`s are the positivity of `β` and the positivity concluded of `aRunStd`. -/
theorem aRunStd_pos {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) : 0 < aRunStd N β := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hbase : (0 : ℝ) < (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by positivity
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (Real.exp_pos _)

#print axioms aRunStd_pos

/-- `exp (-t) ≤ 4 / t²` for `t > 0`, from `Real.add_one_le_exp` applied at `t/2` and squared:
`exp t = exp (t/2)² ≥ (1 + t/2)² ≥ (t/2)²`.

Elementary on purpose. The decay of `aRunStd` in the coupling is what the continuum reading needs, and
proving it this way keeps the argument inside lemmas this development already uses.

DERIVED: `4` is `2²`, the square of the halving in `exp t = exp (t/2)²`; the halving is there so
that `Real.add_one_le_exp` can be squared rather than used once. `2` is that halving and the square.
`1` is `add_one_le_exp`'s own offset. `0` is the sign condition on `t`. -/
theorem exp_neg_le_four_div_sq {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ 4 / t ^ 2 := by
  have hhalf : 1 + t / 2 ≤ Real.exp (t / 2) := by
    have := Real.add_one_le_exp (t / 2); linarith
  have hpos : (0 : ℝ) < Real.exp (t / 2) := Real.exp_pos _
  have hsq : (t / 2) ^ 2 ≤ Real.exp (t / 2) ^ 2 := by nlinarith [hhalf, ht]
  have hexp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hexp] at hsq
  have ht2 : (0 : ℝ) < t ^ 2 / 4 := by positivity
  have hle : t ^ 2 / 4 ≤ Real.exp t := by nlinarith [hsq]
  -- `exp (-t) * t² ≤ 4`, then divide. Stated as a product first so no inverse inequality is
  -- rewritten under a hypothesis.
  have hgoal : Real.exp (-t) * t ^ 2 ≤ 4 := by
    rw [Real.exp_neg]
    have hinv : (0 : ℝ) ≤ (Real.exp t)⁻¹ := by positivity
    have hstep : (Real.exp t)⁻¹ * t ^ 2 ≤ (Real.exp t)⁻¹ * (4 * Real.exp t) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hle]) hinv
    have hcol : (Real.exp t)⁻¹ * (4 * Real.exp t) = 4 := by
      field_simp
    rw [hcol] at hstep
    exact hstep
  rw [le_div_iff₀ (by positivity : (0:ℝ) < t ^ 2)]
  exact hgoal

#print axioms exp_neg_le_four_div_sq

/-- `aRunStd N` decays at least like `1 / β` once the base has passed `1`: for `N ≥ 1` and
`(24π²β) / (11N²) ≥ 1`,

    aRunStd N β ≤ ((24π²β) / (11N²)) * (4 / ((12π²β) / (11N²)) ^ 2).

The power factor is bounded by its base because the exponent `51/121` is at most `1`
(`Real.rpow_le_rpow_of_exponent_le`, then `Real.rpow_one`), and the exponential by
`exp_neg_le_four_div_sq`, after `neg_div` moves the sign outside the quotient.

DERIVED: `24`, `12` and `11` are `aRunStd`'s own constants, which the normalised coefficients fix
(`b0_g_sq`, `one_over_four_N_b0`); `4` is `exp_neg_le_four_div_sq`'s. Every `2` is a square — the
`π²` and `N²` of `aRunStd`'s constants, and the square in `exp_neg_le_four_div_sq`'s `4 / t²`. `1` is the
least colour count in `hN` and the threshold the base must pass for `x ^ p ≤ x`. `0` is the sign of
the coupling. The exponent `51/121` is `aRunStd`'s and appears in the PROOF, where the bound
`x ^ p ≤ x ^ 1` is applied; the statement does not mention it. -/
theorem aRunStd_le_of_base_ge_one {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β)
    (hbase : (1 : ℝ) ≤ (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) :
    aRunStd N β ≤ ((24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2))
      * (4 / ((12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) ^ 2) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hb : (0 : ℝ) < (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by positivity
  have hc : (0 : ℝ) < (12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by positivity
  -- the power factor is at most its base
  have hpow : ((24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) ^ (51 / 121 : ℝ)
      ≤ (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (51 / 121 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at h
  -- the exponential factor; `neg_div` is `-b / a = -(b / a)`
  have hexp : Real.exp (-(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2))
      ≤ 4 / ((12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) ^ 2 := by
    have hrw : -(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)
        = -((12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) := neg_div _ _
    rw [hrw]
    exact exp_neg_le_four_div_sq hc
  have hepos : (0 : ℝ) < Real.exp (-(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) :=
    Real.exp_pos _
  unfold aRunStd
  exact mul_le_mul hpow hexp (le_of_lt hepos) (le_of_lt hb)

#print axioms aRunStd_le_of_base_ge_one

/-- The previous bound, collapsed: `aRunStd N β ≤ 22·N² / (3π²β)` once the base has passed `1`.

With `u = 24π²β/(11N²)` the exponential's argument is `u/2`, so the bound reads
`u · 4/(u/2)² = 16/u = 16·11N²/(24π²β)`, and `16·11/24 = 22/3`. A plain `1/β` decay at fixed colour
count.

DERIVED: `22/3 = 16 · 11/24`, where `16 = 4 · 2²` comes from `exp_neg_le_four_div_sq`'s `4` and the
halving between `aRunStd`'s base constant `24π²/11` and its exponential constant `12π²/11`, and `11/24`
is the reciprocal of the base constant; the `2`s of `N²` and `π²` are `aRunStd`'s. `24` and `11` in
`hbase` are `aRunStd`'s base. `1` is the threshold the base passes. `0` is a sign condition. Nothing
chosen. -/
theorem aRunStd_le_inv_of_base_ge_one {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β)
    (hbase : (1 : ℝ) ≤ (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) :
    aRunStd N β ≤ 22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * β) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h := aRunStd_le_of_base_ge_one hN hβ hbase
  have hcol : ((24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2))
        * (4 / ((12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) ^ 2)
      = 22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * β) := by
    field_simp
    ring
  rwa [hcol] at h

#print axioms aRunStd_le_inv_of_base_ge_one

/-- `aRunStd N` is continuous: a rpow with nonnegative exponent composed with a linear map, times an
exponential composed with another.

`Real.continuous_rpow_const` needs the exponent nonnegative, which `51/121` is.

DERIVED: `51/121`, `24`, `12`, `11` and the `2`s of `π²` and `N²` are `aRunStd`'s own constants. `0` is
the nonnegativity of the exponent that `Real.continuous_rpow_const` requires. -/
theorem continuous_aRunStd (N : ℕ) : Continuous (aRunStd N) := by
  have h1 : Continuous fun β : ℝ => (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) :=
    (continuous_const.mul continuous_id).div_const _
  have h2 : Continuous fun β : ℝ => -(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) :=
    ((continuous_const.mul continuous_id).neg).div_const _
  exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 51 / 121)).comp h1).mul
    (Real.continuous_exp.comp h2)

#print axioms continuous_aRunStd

/-- Past any coupling, and below any positive target, there is a coupling at which `aRunStd N` is
smaller: `∃ β > β₀, aRunStd N β < ε`.

The witness clears three conditions at once — past `β₀`, past the base threshold `11N²/(24π²)`, and
past `22N²/(3π²ε)` — by taking a maximum and adding one.

DERIVED: `11` and `24` in the base threshold are where `aRunStd`'s base `(24π²β)/(11N²)` reaches `1`;
`22` and `3` are `aRunStd_le_inv_of_base_ge_one`'s; every `2` is the square of `N` or `π`. `1` is added
to a maximum to make each inequality strict, which is the standard witness for "past every one of
these" and is not a magnitude; `1` in `hN` is the least colour count. `0` is the sign condition on
`ε` and on the coupling. -/
theorem exists_beta_aRunStd_lt {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (β₀ : ℝ) :
    ∃ β : ℝ, β₀ < β ∧ 0 < β ∧ aRunStd N β < ε := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set β : ℝ := max (max β₀ (11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2)))
    (22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * ε)) + 1 with hβdef
  have hgt0 : β₀ < β := by
    have := le_max_left β₀ (11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2))
    have h2 := le_max_left (max β₀ (11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2)))
      (22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * ε))
    rw [hβdef]; linarith
  have hbaseth : 11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2) < β := by
    have := le_max_right β₀ (11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2))
    have h2 := le_max_left (max β₀ (11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2)))
      (22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * ε))
    rw [hβdef]; linarith
  have hepsth : 22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * ε) < β := by
    have := le_max_right (max β₀ (11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2)))
      (22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * ε))
    rw [hβdef]; linarith
  have hpos : 0 < β := by
    have h11 : (0 : ℝ) < 11 * (N : ℝ) ^ 2 / (24 * Real.pi ^ 2) := by positivity
    linarith
  refine ⟨β, hgt0, hpos, ?_⟩
  -- `div_lt_iff₀` clears the `π²` denominators, leaving inequalities linear in the monomials
  -- `N²` and `π²·β` (resp. `π²·β·ε`), which `linarith` identifies up to ring normalisation.
  have hbase : (1 : ℝ) ≤ (24 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 11 * (N : ℝ) ^ 2)]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 24 * Real.pi ^ 2)] at hbaseth
    linarith
  have hb := aRunStd_le_inv_of_base_ge_one hN hpos hbase
  have hlt : 22 * (N : ℝ) ^ 2 / (3 * Real.pi ^ 2 * β) < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * Real.pi ^ 2 * β)]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * Real.pi ^ 2 * ε)] at hepsth
    linarith
  exact lt_of_le_of_lt hb hlt

#print axioms exists_beta_aRunStd_lt

/-- **A coupling realising a chosen spacing, arbitrarily far out.** For `N ≥ 1`, any target
`0 < a < aRunStd N β₁` is attained: `∃ β ≥ β₁, aRunStd N β = a`.

`exists_beta_aRunStd_lt` puts a coupling past `β₁` where `aRunStd` is below the target,
`continuous_aRunStd` makes the map continuous between, and `intermediate_value_uIcc` produces the
coupling — the idiom `ConfinesZero.confinesAtAnAperture_of_missesTheFloor` uses.

This is the branch asymptotic freedom lives on: `β₁` is arbitrary, so the coupling can be demanded
as large as one likes. `N` is the colour count and is held fixed;
`SubstrateArms.physical_gap_at_the_running_spacing` uses this at `N = 3`, the `SU(3)` of the Wilson
ensemble.

DERIVED: `1` is the least colour count in `hN`, which is what keeps `(N : ℝ)` away from zero so
`aRunStd`'s base is defined; `0` is the target's sign in `ha`. `a`, `β₁` and `N` are the caller's. -/
theorem exists_beta_aRunStd_eq {N : ℕ} (hN : 1 ≤ N) {a β₁ : ℝ} (ha : 0 < a)
    (hlt : a < aRunStd N β₁) :
    ∃ β : ℝ, β₁ ≤ β ∧ aRunStd N β = a := by
  obtain ⟨β₂, h21, _, hsmall⟩ := exists_beta_aRunStd_lt hN ha β₁
  have hcont : ContinuousOn (aRunStd N) (Set.uIcc β₁ β₂) := (continuous_aRunStd N).continuousOn
  have hmem : a ∈ Set.uIcc (aRunStd N β₁) (aRunStd N β₂) := by
    rw [Set.mem_uIcc]
    exact Or.inr ⟨le_of_lt hsmall, le_of_lt hlt⟩
  obtain ⟨x, hxmem, hx⟩ := intermediate_value_uIcc hcont hmem
  refine ⟨x, ?_, hx⟩
  rw [Set.uIcc_of_le (le_of_lt h21)] at hxmem
  exact hxmem.1

#print axioms exists_beta_aRunStd_eq



/-! ### The spacing at the Lean coupling

The Wilson systems of this development index a plaquette by an ordered pair of directions, so every
plane is counted twice, and the Boltzmann weight at coupling `β` is the standard Wilson weight at `2β`
(`PlaqCount.boltz_eq_std`). The spacing of the Lean Wilson family at its coupling `β` is therefore
`aRunStd N (2β)`.
-/

/-- **The two-loop spacing at the Lean coupling.** `aRun N β = aRunStd N (2β)`: the standard two-loop
spacing at `β_std = 2β` (`PlaqCount.boltz_eq_std`), so the gauge coupling is `g² = N/β`. With
`u = 48π²β/(11N²)`, `aRun N β = u^{51/121} · exp(−u/2)`, largest at `β = 17N²/(88π²)`.

DERIVED: `2` is the number of orderings of a plane, `PlaqCount.boltz_eq_std`'s factor. -/
noncomputable def aRun (N : ℕ) (β : ℝ) : ℝ := aRunStd N (2 * β)

#print axioms aRun

/-- `0 < aRun N β` for `1 ≤ N` and `0 < β` (`aRunStd_pos` at `2β`).

DERIVED: `1` is the least colour count; `0` is the sign of `β` and of the spacing. -/
theorem aRun_pos {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) : 0 < aRun N β :=
  aRunStd_pos hN (by linarith)

#print axioms aRun_pos

/-- `aRun N` is continuous (`continuous_aRunStd` composed with `β ↦ 2β`).

DERIVED: no numeral beyond `aRun`'s. -/
theorem continuous_aRun (N : ℕ) : Continuous (aRun N) :=
  (continuous_aRunStd N).comp (continuous_const.mul continuous_id)

#print axioms continuous_aRun

/-- Past any coupling and below any positive target there is a coupling at which `aRun N` is smaller
(`exists_beta_aRunStd_lt` at `2β₀`, halved).

DERIVED: `1` is the least colour count; `0` is the sign of `ε` and of the coupling; `2` is `aRun`'s
factor. -/
theorem exists_beta_aRun_lt {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) (β₀ : ℝ) :
    ∃ β : ℝ, β₀ < β ∧ 0 < β ∧ aRun N β < ε := by
  obtain ⟨β, h1, h2, h3⟩ := exists_beta_aRunStd_lt hN hε (2 * β₀)
  refine ⟨β / 2, by linarith, by linarith, ?_⟩
  show aRunStd N (2 * (β / 2)) < ε
  rw [show 2 * (β / 2) = β by ring]
  exact h3

#print axioms exists_beta_aRun_lt

/-- Every positive target below `aRun N β₁` is attained past `β₁` (intermediate values of the
continuous `aRun N`, `exists_beta_aRun_lt`).

DERIVED: `1` is the least colour count; `0` is the target's sign. -/
theorem exists_beta_aRun_eq {N : ℕ} (hN : 1 ≤ N) {a β₁ : ℝ} (ha : 0 < a)
    (hlt : a < aRun N β₁) :
    ∃ β : ℝ, β₁ ≤ β ∧ aRun N β = a := by
  obtain ⟨β₂, h21, _, hsmall⟩ := exists_beta_aRun_lt hN ha β₁
  have hcont : ContinuousOn (aRun N) (Set.uIcc β₁ β₂) := (continuous_aRun N).continuousOn
  have hmem : a ∈ Set.uIcc (aRun N β₁) (aRun N β₂) := by
    rw [Set.mem_uIcc]
    exact Or.inr ⟨le_of_lt hsmall, le_of_lt hlt⟩
  obtain ⟨x, hxmem, hx⟩ := intermediate_value_uIcc hcont hmem
  refine ⟨x, ?_, hx⟩
  rw [Set.uIcc_of_le (le_of_lt h21)] at hxmem
  exact hxmem.1

#print axioms exists_beta_aRun_eq

/-! ## 3. The statement -/

/-- The predicate `∃ mphys, 0 < mphys ∧ Tendsto (fun β => m β / aRun N β) atTop (nhds mphys)`: the
ratio of `m` to the running spacing of `SU(N)`, `N` the colour count, converges to a finite positive
limit as `β → ∞`.

`aRun N` is a fixed function, not an existential, so the predicate constrains `m`:
`asymptotic_scaling_is_satisfiable` and `asymptotic_scaling_has_content` exhibit an `m` on each side.
The limit's finiteness is carried by `Tendsto` into `nhds mphys` with `mphys : ℝ`.

DERIVED: `0` is the strict positivity demanded of the limit, which is what rules out a ratio tending
to zero. -/
def AsymptoticScalingAt (N : ℕ) (m : ℝ → ℝ) : Prop :=
  ∃ mphys : ℝ, 0 < mphys ∧ Tendsto (fun β => m β / aRun N β) atTop (nhds mphys)

#print axioms AsymptoticScalingAt

/-- `AsymptoticScalingAt N (fun β => c * aRun N β)` for `1 ≤ N` and `0 < c`, with limit `c`. The
ratio is eventually constantly `c`, by `field_simp` against `aRun_pos`, which needs `β > 0` — hence
the `eventually_gt_atTop` filter.

DERIVED: `1` in `hN` is `aRun_pos`'s colour-count hypothesis; `0` in `hc` is what makes `c` a legal
value for the predicate's `mphys`. -/
theorem asymptotic_scaling_is_satisfiable {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 < c) :
    AsymptoticScalingAt N (fun β => c * aRun N β) := by
  refine ⟨c, hc, ?_⟩
  have heq : (fun β => (c * aRun N β) / aRun N β) =ᶠ[atTop] fun _ => c := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    field_simp [ne_of_gt (aRun_pos hN hβ)]
  exact Tendsto.congr' heq.symm tendsto_const_nhds

#print axioms asymptotic_scaling_is_satisfiable

/-- `¬ AsymptoticScalingAt N (fun β => aRun N β * Real.exp (-β))` for `1 ≤ N`. The ratio is
eventually `exp(−β)`, which tends to `0`, and `tendsto_nhds_unique` against a positive `mphys` is a
contradiction. So the predicate is refutable, by a lattice mass that decays faster than the running
spacing by the factor `exp(−β)`.

DERIVED: `1` in `hN` is `aRun_pos`'s colour-count hypothesis, needed to divide by `aRun N β`. -/
theorem asymptotic_scaling_has_content {N : ℕ} (hN : 1 ≤ N) :
    ¬ AsymptoticScalingAt N (fun β => aRun N β * Real.exp (-β)) := by
  rintro ⟨mphys, hpos, hlim⟩
  have heq : (fun β => (aRun N β * Real.exp (-β)) / aRun N β)
      =ᶠ[atTop] fun β => Real.exp (-β) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    field_simp [ne_of_gt (aRun_pos hN hβ)]
  have hzero : Tendsto (fun β : ℝ => Real.exp (-β)) atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero
  have := tendsto_nhds_unique (Tendsto.congr' heq hlim) hzero
  exact absurd this (ne_of_gt hpos)

#print axioms asymptotic_scaling_has_content

/-- Both sides at once, for `1 ≤ N`: some `m` satisfies `AsymptoticScalingAt N` and some `m` does
not. The witnesses are `fun β => 1 * aRun N β` (via `asymptotic_scaling_is_satisfiable`) and
`fun β => aRun N β * Real.exp (-β)` (via `asymptotic_scaling_has_content`).

DERIVED: `1` in `hN` is `aRun_pos`'s colour-count hypothesis, inherited from both witnesses. -/
theorem asymptotic_scaling_is_a_real_constraint {N : ℕ} (hN : 1 ≤ N) :
    (∃ m : ℝ → ℝ, AsymptoticScalingAt N m) ∧ (∃ m : ℝ → ℝ, ¬ AsymptoticScalingAt N m) :=
  ⟨⟨fun β => 1 * aRun N β, asymptotic_scaling_is_satisfiable hN one_pos⟩,
   ⟨fun β => aRun N β * Real.exp (-β), asymptotic_scaling_has_content hN⟩⟩

#print axioms asymptotic_scaling_is_a_real_constraint

/-! ## 4. The lattice mass, and the joint limit in extent and coupling -/

/-- The lag-one decay ratio `wilsonCorrAt N β 1 / wilsonCorrAt N β 0` at extent `N` and coupling
`β`. A quotient of two correlation values at fixed separations; no hypothesis guards the denominator,
so `Real.div` returns `0` where `ρ(0) = 0`.

DERIVED: `1` and `0` are the two LAGS the ratio relates, the nearest neighbour against the contact
value; neither is a magnitude. CHOSEN: lag one among the available lags, because it is the only odd
lag the tree bounds (`WeakArm.wilsonCorrAt_le_at_zero_at_extent_six`), every right-hand lag
`LogConvex.corrClay_log_convex` produces being even. The ratio is then an effective mass at one
separation rather than an asymptotic decay rate. -/
noncomputable def decayAt (N : ℕ) (β : ℝ) : ℝ :=
  MassGap.wilsonCorrAt N β 1 / MassGap.wilsonCorrAt N β 0

#print axioms decayAt

/-- `- Real.log (decayAt N β)`, the lattice mass read at lag one.

Mathlib's `Real.log 0 = 0`, and `PowerTail.wilsonCorrAt_at_zero_coupling` puts `ρ(1) = 0` at zero
coupling, so `mLatAt N 0 = 0` — the value recorded by `mLatAt_at_zero_coupling_is_junk`. The
statements below are therefore guarded by `0 < decayAt N β`, which fails there.

DERIVED: no numeral. The lags `1` and `0` sit inside `decayAt`, not in this definition. -/
noncomputable def mLatAt (N : ℕ) (β : ℝ) : ℝ := - Real.log (decayAt N β)

#print axioms mLatAt

/-- `mLatAt 5 0 = 0`: at extent five (period six) and zero coupling, the lattice mass evaluates to
zero, because `ρ(1) = 0` there (`PowerTail.wilsonCorrAt_at_zero_coupling`, whose hypothesis
`1 ≤ circLag 1` is checked by `decide`) and `Real.log 0 = 0`. Recorded so the value is not mistaken
for a vanishing mass; the same computation applies at every extent whose period is at least two.

DERIVED: `5` is the extent `N`, chosen so `Fin 6` makes `circLag 1 = 1` decidable; the first `0` is
the coupling at which `ρ(1)` vanishes, and the second is the resulting value of `mLatAt`, which comes
from `Real.log 0 = 0` rather than from any decay. -/
theorem mLatAt_at_zero_coupling_is_junk : mLatAt 5 0 = 0 := by
  have hc : Moment.circLag (1 : Fin 6) = 1 := by decide
  have hz : MassGap.wilsonCorrAt 5 0 1 = 0 :=
    MassGap.PowerTail.wilsonCorrAt_at_zero_coupling 5 1 (by rw [hc])
  simp [mLatAt, decayAt, hz]

#print axioms mLatAt_at_zero_coupling_is_junk

/-- `0 ≤ mLatAt N β` at even extent `N + 1 = 2m` with `3 ≤ m`, for `0 ≤ β` and where the decay ratio
is positive. `WeakArm.wilsonCorrAt_le_at_zero` bounds `ρ(1) ≤ ρ(0)` and
`PlaqVariance.corrClay_zero_pos` makes `ρ(0)` positive, so `decayAt N β ≤ 1` and `Real.log_nonpos`
applies. Stated at even extent only, and at nonnegative coupling only.

DERIVED: `1` in `hm` and `2` in `2 * m` are the even-extent condition `N + 1 = 2m` that
`WeakArm.wilsonCorrAt_le_at_zero` requires; `3` in `hm3` is that lemma's own least half-extent; `0` in
`hβ` is the nonnegative coupling it is stated on; `0` in `hpos` is what `Real.log_nonpos` needs of the
ratio, and `0` in the conclusion is the resulting lower bound on `−log`. -/
theorem mLatAt_nonneg {N m : ℕ} (hm : N + 1 = 2 * m) (hm3 : 3 ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (hpos : 0 < decayAt N β) : 0 ≤ mLatAt N β := by
  have hle := MassGap.WeakArm.wilsonCorrAt_le_at_zero N m hm hm3 hβ 1
  have h0 : 0 < MassGap.wilsonCorrAt N β 0 := MassGap.PlaqVariance.corrClay_zero_pos N β
  have hratio : decayAt N β ≤ 1 := by
    rw [decayAt, div_le_one h0]
    exact hle
  have := Real.log_nonpos (le_of_lt hpos) hratio
  simp only [mLatAt]
  linarith

#print axioms mLatAt_nonneg

/-! ### A mass bounded below pins the `SU(N)` spacing, and so fails the predicate -/

/-- At one fixed colour count `N` with `1 ≤ N`: if `AsymptoticScalingAt N m` holds and `c ≤ m β`
eventually for some `c > 0`, then there is a `c' > 0` with `c' ≤ aRun N β` eventually. The witness
is `c' = c / (mphys + 1)`, obtained by bounding the ratio `m β / aRun N β` above near its limit.

So a mass `m` that stays away from zero, read against the `SU(N)` running spacing `aRun N`, forces
that spacing to stay away from zero along the same filter. `N` is `aRun`'s colour count and is the
same fixed `N` throughout; the statement involves no lattice extent, and `m` is any function of the
coupling. `bounded_mass_fails_scaling` combines this with `exists_beta_aRun_lt`.

DERIVED: `1` in `hN` is `aRun_pos`'s colour-count hypothesis; `0` in `hc` is the positivity of the
assumed lower bound on `m`, and `0` in the conclusion is the positivity of the produced bound on
`aRun N`. The `mphys + 1` used to turn convergence into an eventual upper bound occurs in the proof,
not in the statement. -/
theorem fixed_colours_pins_the_spacing {N : ℕ} (hN : 1 ≤ N) {m : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ᶠ β in atTop, c ≤ m β)
    (hscal : AsymptoticScalingAt N m) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ β in atTop, c' ≤ aRun N β := by
  obtain ⟨mphys, hpos, hlim⟩ := hscal
  have hub : ∀ᶠ β in atTop, m β / aRun N β < mphys + 1 :=
    hlim.eventually (gt_mem_nhds (by linarith : mphys < mphys + 1))
  have hmpos : (0 : ℝ) < mphys + 1 := by linarith
  refine ⟨c / (mphys + 1), by positivity, ?_⟩
  filter_upwards [hbdd, hub, eventually_gt_atTop (0 : ℝ)] with β hb hu hβ
  have haR : 0 < aRun N β := aRun_pos hN hβ
  rw [div_lt_iff₀ haR] at hu
  rw [div_le_iff₀ hmpos]
  nlinarith [hb, hu]

#print axioms fixed_colours_pins_the_spacing

/-- `¬ AsymptoticScalingAt N m` for `1 ≤ N` whenever `c ≤ m β` eventually for some `c > 0`: a mass
bounded below by a positive constant does not scale with the `SU(N)` spacing.
`fixed_colours_pins_the_spacing` would give `c' > 0` with `c' ≤ aRun N β` eventually, from some `β₀`
on (`Filter.eventually_atTop`), and `exists_beta_aRun_lt` gives a coupling past `β₀` with
`aRun N β < c'`.

So a lattice-unit mass that stays away from zero, such as a margin bounded below uniformly in the
coupling, is not a continuum mass in the sense of `AsymptoticScalingAt`.

DERIVED: `1` in `hN` is `aRun_pos`'s colour-count hypothesis, carried from both lemmas composed;
`0` in `hc` is the positivity of the assumed lower bound on `m`. -/
theorem bounded_mass_fails_scaling {N : ℕ} (hN : 1 ≤ N) {m : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ᶠ β in atTop, c ≤ m β) :
    ¬ AsymptoticScalingAt N m := by
  intro hscal
  obtain ⟨c', hc', hev⟩ := fixed_colours_pins_the_spacing hN hc hbdd hscal
  obtain ⟨β₀, hβ₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨β, hβ, _, hlt⟩ := exists_beta_aRun_lt hN hc' β₀
  exact absurd (hβ₀ β (le_of_lt hβ)) (not_le.mpr hlt)

#print axioms bounded_mass_fails_scaling

/-- The joint-limit predicate, for a trajectory of lattice extents `Nof : ℝ → ℕ`: `Nof β → ∞` as
`β → ∞`, and `mLatAt (Nof β) β / aRun 3 β` converges to a positive limit. The lattice mass is read at
the extent `Nof β`, which moves with the coupling. The spacing is `aRun 3`, the two-loop running
spacing of `SU(3)` at the Lean Wilson coupling `β = 3/g²`, which depends on the coupling alone: `mLatAt`
reads `wilsonCorrAt N β = WilsonBridge.corrClay (N + 1) β`, and `corrClay` is `corrHyper` at colour
count `3`, so `SU(3)` is the gauge group whose spacing the mass is divided by. The second conjunct is
`AsymptoticScalingAt 3 (fun β => mLatAt (Nof β) β)`, so `bounded_mass_fails_scaling` refutes it for
any `Nof` along which the lattice mass stays above a positive constant.

`Nof` is a parameter rather than existentially quantified; `∃ Nof, AsymptoticScalingJoint Nof` would
admit the same kind of witness `free_spacing_scaling_is_also_vacuous` supplies for the spacing. This
is a definition; nothing in this file proves it for any `Nof`, and the refutation above takes the
lower bound on the lattice mass as a hypothesis.

DERIVED: `3` in `aRun 3` is the colour count of `WilsonBridge.corrClay`'s ensemble, `SU(3)`, the
gauge group whose correlation `mLatAt` reads; `3` in `β = 3/g²` is `N` at that `N`, `g² = N/β` at the
Lean coupling. `0` is the
strict positivity demanded of the limit. `Nof` and the limit are variables. -/
def AsymptoticScalingJoint (Nof : ℝ → ℕ) : Prop :=
  Tendsto (fun β => (Nof β : ℝ)) atTop atTop ∧
    ∃ mphys : ℝ, 0 < mphys ∧
      Tendsto (fun β => mLatAt (Nof β) β / aRun 3 β) atTop (nhds mphys)

#print axioms AsymptoticScalingJoint

/-! ### How `aRunStd` depends on the colour count

At fixed positive `β` the two factors of `aRunStd N β` move in opposite directions as the colour count
`N` grows. The rpow base `(24π²β)/(11N²)` falls and its exponent `51/121` is positive, so the rpow
factor falls; the exponential's argument `−(12π²β)/(11N²)` rises toward zero, so the exponential
factor rises. With `u = 24π²β/(11N²)` the product is `u^{51/121} · exp(−u/2)`, which rises in `u` for
`u < 102/121` and falls beyond it, so at fixed `β` the spacing rises with `N` while
`N² < 44π²β/17 ≈ 25.54·β` and falls once `N² > 44π²β/17`. At `β = 1` the turn lies between `N = 5`
and `N = 6`: the spacing evaluates to `7.690·10⁻⁵, 0.1378, 0.4367, 0.6104, 0.5971, 0.4701, 0.1342`
across `N = 1, 2, 3, 5, 6, 10, 50`. For `aRun N β = aRunStd N (2β)` the turn is at `N² = 88π²β/17`.

`aRun_exp_factor_increasing_in_colours` proves that the exponential factor increases with `N`. The
monotonicity of the rpow factor and of the product is not proved here.

DERIVED: `102/121` is `2 · 51/121`, where the derivative `51/(121u) − 1/2` of
`log (u^{51/121} · exp(−u/2))` vanishes; `44/17` is `u = 102/121` solved for `N²/(π²β)` through
`u = 24π²β/(11N²)`, since `24 · 121 / (11 · 102) = 44/17`, and `25.54` is `44π²/17` evaluated. The
figures are `aRun` evaluated at `β = 1` and those seven colour counts. -/

/-- `exp(−(12π²β)/(11M²)) < exp(−(12π²β)/(11N²))` for `0 < β`, `0 < M` and `M < N`: the exponential
factor of `aRun` is strictly increasing in the colour count at fixed positive coupling. By
`Real.exp_lt_exp` and `div_lt_div_iff₀` on the two positive denominators, then
`mul_lt_mul_of_pos_left` against the positive numerator `12π²β`. Only this factor of `aRun` is
covered; the rpow factor, which decreases in the colour count, is not.

DERIVED: `0` in `hβ` and `0` in `hM` are what make both denominators and the numerator positive, so
the quotient comparison is in the stated direction; `12`, `11` and the `2`s of `π²`, `M²` and `N²`
are `aRun`'s own exponential argument `−(12π²β)/(11N²)`, from `one_over_four_N_b0`. -/
theorem aRun_exp_factor_increasing_in_colours {β : ℝ} (hβ : 0 < β) {M N : ℕ}
    (hM : 0 < M) (h : M < N) :
    Real.exp (-(12 * Real.pi ^ 2 * β) / (11 * (M : ℝ) ^ 2))
      < Real.exp (-(12 * Real.pi ^ 2 * β) / (11 * (N : ℝ) ^ 2)) := by
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNr : (M : ℝ) < (N : ℝ) := by exact_mod_cast h
  have hM2 : (0 : ℝ) < 11 * (M : ℝ) ^ 2 := by positivity
  have hN2 : (0 : ℝ) < 11 * (N : ℝ) ^ 2 := by nlinarith
  have hlt : 11 * (M : ℝ) ^ 2 < 11 * (N : ℝ) ^ 2 := by nlinarith
  have hP : (0 : ℝ) < 12 * Real.pi ^ 2 * β := by positivity
  refine Real.exp_lt_exp.mpr ?_
  rw [div_lt_div_iff₀ hM2 hN2]
  -- goal: `-(12π²β) * (11N²) < -(12π²β) * (11M²)`, linear in the monomials `π²βN²` and `π²βM²`
  linarith [mul_lt_mul_of_pos_left hlt hP]

#print axioms aRun_exp_factor_increasing_in_colours


end MassGap.AsymptoticScaling
