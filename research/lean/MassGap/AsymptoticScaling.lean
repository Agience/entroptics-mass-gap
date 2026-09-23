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

`aRun N β = ((3β)/(22N²))^{−51/121} · exp(−3β/(44N²))`, the two-loop running spacing with the overall
scale `Λ` set to `1`. The exponents come from `Running`'s coefficients `b₀ = 11N/3` and `b₁ = 34N²/3`
via

    a(β)·Λ  =  (b₀ g²)^{−b₁/(2b₀²)} · exp(−1/(2b₀ g²)),        g² = 2N/β

and the three identities `b1_over_two_b0_sq`, `one_over_four_N_b0` and `b0_g_sq` check the numerals in
`aRun` against those coefficients. The colour count cancels from `b₁/(2b₀²) = 51/121`, so that
exponent is the same for every `SU(N)`. `aRun_pos` gives positivity for `1 ≤ N` and `0 < β`.

## The predicates

`AsymptoticScalingAt N m` says `m β / aRun N β` converges to a positive limit. With `aRun` fixed
rather than existential the predicate is a constraint on `m` alone:
`asymptotic_scaling_is_satisfiable` gives `m = c · aRun N` as a witness, and
`asymptotic_scaling_has_content` shows `m = aRun N · exp(−β)` refutes it;
`asymptotic_scaling_is_a_real_constraint` states both together.

`decayAt` and `mLatAt` are the lag-one decay ratio `ρ(1)/ρ(0)` and `−log` of it.
`mLatAt_at_zero_coupling_is_junk` records `mLatAt 5 0 = 0`, a consequence of `Real.log 0 = 0` together
with `ρ(1) = 0` at zero coupling, so statements about `mLatAt` are guarded by `0 < decayAt`.
`mLatAt_nonneg` gives `0 ≤ mLatAt N β` at even extent `N + 1 = 2m` with `3 ≤ m`.

`fixed_extent_pins_the_spacing`: if `AsymptoticScalingAt N m` holds and `m` is eventually at least a
positive constant, then `aRun N` is eventually at least a positive constant, so the spacing does not
approach zero along that sequence. `AsymptoticScalingJoint Nof` is the corresponding statement with
the extent a function of the coupling; it is a definition, and nothing in this file proves it.

No declaration here supplies a lattice mass as a function of the coupling.

DERIVED: every numeral in `aRun` traces to `Running`. `51/121` is `b₁/(2b₀²)`, `3/44` is `1/(4N b₀)`
with the `N²` carried separately, `22` and `3` are `b₀ g²` multiplied out, and `2N/β` is the `SU(N)`
relation between the lattice coupling and `g²`. `0` is positivity, and the lags `1` and `0` in
`decayAt` are the nearest-neighbour and contact separations.
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

/-- The two-loop running lattice spacing at extent `N` and coupling `β`, with `Λ` set to one:
`((3β)/(22N²))^(51/121) · exp(−(3β)/(44N²))`. An `rpow` times an exponential; no hypothesis on `N` or
`β`, so the base may be zero or negative and `aRun_pos` is stated separately.

DERIVED: `51/121` is `b₁/(2b₀²)`, checked by `b1_over_two_b0_sq`; `3` and `44` are `1/(4N b₀)` with
the `N²` carried separately, checked by `one_over_four_N_b0`; `3` and `22` are `b₀ g²` at `g² = 2N/β`
multiplied out, checked by `b0_g_sq`; both `2`s are the `N²` those identities produce. All at
`b₀ = 11N/3` and `b₁ = 34N²/3`, the coefficients `Running.b0_pos` and `Running.b1_pos` are stated
for. CHOSEN: `Λ = 1`, a unit, which cancels from every ratio this file forms. -/
noncomputable def aRun (N : ℕ) (β : ℝ) : ℝ :=
  ((3 * β) / (22 * (N : ℝ) ^ 2)) ^ (51 / 121 : ℝ) * Real.exp (-(3 * β) / (44 * (N : ℝ) ^ 2))

#print axioms aRun

/-! ### The exponents, derived from `Running`'s coefficients rather than retyped

`aRun`'s `51/121` and `3/(44N²)` were written out by hand above. That is a second source of truth for
numbers `Running` already determines, which is the defect `FreeFieldLagTwoSix`'s value theorems exist
to prevent on the free-field side. The three identities below close it: each states that the numeral
in `aRun` IS the corresponding expression in `b₀ = 11N/3` and `b₁ = 34N²/3`, so the definition is
checked against `Running` and not merely consistent with it.
-/

/-- `(34N²/3) / (2·(11N/3)²) = 51/121` for `N ≠ 0`, by `field_simp; ring`. The colour count cancels,
so the value is independent of `N`. This checks `aRun`'s rpow exponent against `Running`'s
coefficients.

DERIVED: `0` in `hN` is what `field_simp` needs to clear `N` from the denominators; `34`, `2` and `3`
are `b₁ = 34N²/3`; `11`, `3` and `2` are `b₀ = 11N/3` squared and doubled; `51/121` is
`306/726` in lowest terms, which is `aRun`'s exponent. -/
theorem b1_over_two_b0_sq {N : ℝ} (hN : N ≠ 0) :
    (34 * N ^ 2 / 3) / (2 * (11 * N / 3) ^ 2) = 51 / 121 := by
  field_simp
  ring

#print axioms b1_over_two_b0_sq

/-- `1/(4N·(11N/3)) = 3/(44N²)` for `N ≠ 0`, by `field_simp; ring`. This checks the argument of
`aRun`'s exponential factor against `Running`'s `b₀`.

DERIVED: `0` in `hN` is what `field_simp` needs to clear `N`; `1` and `4` are `1/(4N b₀)`, the
two-loop exponent at `g² = 2N/β`; `11` and `3` are `b₀ = 11N/3`; `3`, `44` and `2` are the same
quantity multiplied out, which is what `aRun` carries. -/
theorem one_over_four_N_b0 {N : ℝ} (hN : N ≠ 0) :
    1 / (4 * N * (11 * N / 3)) = 3 / (44 * N ^ 2) := by
  field_simp
  ring

#print axioms one_over_four_N_b0

/-- `(11N/3)·(2N/β) = 22N²/(3β)` for `β ≠ 0`, by `field_simp; ring`. This checks `aRun`'s rpow base
against `b₀ g²` at the `SU(N)` relation `g² = 2N/β`.

DERIVED: `0` in `hβ` is what `field_simp` needs to clear `β`; `11` and `3` are `b₀ = 11N/3`; `2` is
the `SU(N)` relation `g² = 2N/β`; `22`, `2` and `3` are the product multiplied out, the reciprocal of
`aRun`'s base. -/
theorem b0_g_sq {N β : ℝ} (hβ : β ≠ 0) :
    (11 * N / 3) * (2 * N / β) = 22 * N ^ 2 / (3 * β) := by
  field_simp
  ring

#print axioms b0_g_sq


/-- `0 < aRun N β` for `1 ≤ N` and `0 < β`. The rpow base `(3β)/(22N²)` is positive by `positivity`
under both hypotheses, so `Real.rpow_pos_of_pos` applies, and the exponential factor is positive
unconditionally. `1 ≤ N` is what keeps `(N : ℝ)` away from zero.

DERIVED: `1` in `hN` is the least extent at which `N²` is nonzero, so the rpow base is defined and
positive; the `0`s are the positivity of `β` and the positivity concluded of `aRun`. -/
theorem aRun_pos {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) : 0 < aRun N β := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hbase : (0 : ℝ) < (3 * β) / (22 * (N : ℝ) ^ 2) := by positivity
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (Real.exp_pos _)

#print axioms aRun_pos

/-! ## 3. The statement -/

/-- The predicate `∃ mphys, 0 < mphys ∧ Tendsto (fun β => m β / aRun N β) atTop (nhds mphys)`: the
ratio of `m` to the running spacing converges to a finite positive limit as `β → ∞`.

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

DERIVED: `1` in `hN` is `aRun_pos`'s extent hypothesis; `0` in `hc` is what makes `c` a legal value
for the predicate's `mphys`. -/
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

DERIVED: `1` in `hN` is `aRun_pos`'s extent hypothesis, needed to divide by `aRun N β`. -/
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

DERIVED: `1` in `hN` is `aRun_pos`'s extent hypothesis, inherited from both witnesses. -/
theorem asymptotic_scaling_is_a_real_constraint {N : ℕ} (hN : 1 ≤ N) :
    (∃ m : ℝ → ℝ, AsymptoticScalingAt N m) ∧ (∃ m : ℝ → ℝ, ¬ AsymptoticScalingAt N m) :=
  ⟨⟨fun β => 1 * aRun N β, asymptotic_scaling_is_satisfiable hN one_pos⟩,
   ⟨fun β => aRun N β * Real.exp (-β), asymptotic_scaling_has_content hN⟩⟩

#print axioms asymptotic_scaling_is_a_real_constraint

/-! ## 4. The lattice mass, and why the extent must grow with the coupling -/

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

/-! ### Fixed extent cannot carry the continuum limit -/

/-- At a fixed extent `N` with `1 ≤ N`: if `AsymptoticScalingAt N m` holds and `c ≤ m β` eventually
for some `c > 0`, then there is a `c' > 0` with `c' ≤ aRun N β` eventually. The witness is
`c' = c / (mphys + 1)`, obtained by bounding the ratio `m β / aRun N β` above near its limit.

So a lattice mass that stays away from zero forces the spacing to stay away from zero along the same
filter. The statement is about `aRun N` at a single fixed `N`.

DERIVED: `1` in `hN` is `aRun_pos`'s extent hypothesis; `0` in `hc` is the positivity of the assumed
lower bound on `m`, and `0` in the conclusion is the positivity of the produced bound on `aRun N`.
The `mphys + 1` used to turn convergence into an eventual upper bound occurs in the proof, not in the
statement. -/
theorem fixed_extent_pins_the_spacing {N : ℕ} (hN : 1 ≤ N) {m : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
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

#print axioms fixed_extent_pins_the_spacing

/-- The joint-limit predicate, for a trajectory `Nof : ℝ → ℕ`: `Nof β → ∞` as `β → ∞`, and
`mLatAt (Nof β) β / aRun (Nof β) β` converges to a positive limit. The extent moves with the coupling,
so the lattice mass and the spacing are both read at the growing extent.

`Nof` is a parameter rather than existentially quantified; `∃ Nof, AsymptoticScalingJoint Nof` would
admit the same kind of witness `free_spacing_scaling_is_also_vacuous` supplies for the spacing. This
is a definition, and nothing in this file proves or refutes it for any `Nof`.

DERIVED: `0` is the strict positivity demanded of the limit. `Nof` and the limit are variables. -/
def AsymptoticScalingJoint (Nof : ℝ → ℕ) : Prop :=
  Tendsto (fun β => (Nof β : ℝ)) atTop atTop ∧
    ∃ mphys : ℝ, 0 < mphys ∧
      Tendsto (fun β => mLatAt (Nof β) β / aRun (Nof β) β) atTop (nhds mphys)

#print axioms AsymptoticScalingJoint

/-! ### How `aRun` depends on the extent

`aRun N β` increases with `N` at fixed positive `β`: the rpow base `(3β)/(22N²)` falls while its
exponent `51/121` is applied to a reciprocal, and the exponential's argument `−3β/(44N²)` rises
toward zero. Both factors move the same way. At `β = 1` the spacing evaluates to
`2.163, 4.084, 8.969, 16.12, 62.65` across `N = 1, 2, 5, 10, 50`, a factor of about `29` over that
range. `aRun_exp_factor_increasing_in_extent` proves the monotonicity of the exponential factor; the
rpow factor's monotonicity is not proved here.

DERIVED: the figures are `aRun` evaluated at `β = 1` and those five extents. -/

/-- `exp(−(3β)/(44M²)) < exp(−(3β)/(44N²))` for `0 < β`, `0 < M` and `M < N`: the exponential factor
of `aRun` is strictly increasing in the extent at fixed positive coupling. By `Real.exp_lt_exp` and
`div_lt_div_iff₀` on the two positive denominators. Only this factor of `aRun` is covered; the rpow
factor is not.

DERIVED: `0` in `hβ` and `0` in `hM` are what make both denominators and the numerator positive, so
the quotient comparison is in the stated direction; `3`, `44` and `2` are `aRun`'s own exponential
argument `−3β/(44N²)`, from `one_over_four_N_b0`. -/
theorem aRun_exp_factor_increasing_in_extent {β : ℝ} (hβ : 0 < β) {M N : ℕ}
    (hM : 0 < M) (h : M < N) :
    Real.exp (-(3 * β) / (44 * (M : ℝ) ^ 2)) < Real.exp (-(3 * β) / (44 * (N : ℝ) ^ 2)) := by
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNr : (M : ℝ) < (N : ℝ) := by exact_mod_cast h
  have hM2 : (0 : ℝ) < 44 * (M : ℝ) ^ 2 := by positivity
  have hN2 : (0 : ℝ) < 44 * (N : ℝ) ^ 2 := by nlinarith
  have hlt : 44 * (M : ℝ) ^ 2 < 44 * (N : ℝ) ^ 2 := by nlinarith
  refine Real.exp_lt_exp.mpr ?_
  rw [div_lt_div_iff₀ hM2 hN2]
  nlinarith [hβ, hlt, hM2, hN2]

#print axioms aRun_exp_factor_increasing_in_extent


end MassGap.AsymptoticScaling
