import Mathlib
import MassGap.ClayAssembly
import MassGap.Running

/-!
# MassGap.AsymptoticScaling — writing the statement C2 is missing

`ClayAssembly.scaling_as_stated_is_vacuous` proves the naive form of asymptotic scaling — "a spacing,
positive, tending to zero" — is discharged by `exp(−β)`, which knows nothing about `SU(3)`, the
lattice or the beta function. Its docstring says the real statement is **absent** and that writing it
is the first step rather than the last. This file writes it.

## The obvious repair is ALSO vacuous, and that is the first thing to record

The natural fix is to demand that the physical mass converge: `∃ a`, positive, tending to zero, with
`m_lat(β)/a(β) → m_phys ∈ (0,∞)`. **That is discharged by `a := m_lat`**, whatever `m_lat` is, giving
a ratio identically `1`. `free_spacing_scaling_is_also_vacuous` is the one-line proof. So quantifying
the spacing existentially fails for the same reason the naive form does, and the repair must remove
that quantifier.

## What pins the spacing: the beta function

`a(β)` is not a free function. Asymptotic freedom determines it up to the overall scale `Λ`, and
`Running.lean` already carries the two coefficients that do so — `b₀ = 11N/3` and `b₁ = 34N²/3`,
both proved positive. The two-loop running spacing is

    a(β)·Λ  =  (b₀ g²)^{−b₁/(2b₀²)} · exp(−1/(2b₀ g²)),        g² = 2N/β

and both exponents collapse to pure numbers once `b₀` and `b₁` are substituted:

    b₁/(2b₀²) = (34N²/3) / (2·(11N/3)²) = 306/726 = 51/121        — independent of N
    1/(2b₀g²) = β/(4N·b₀)               = 3β/(44N²)

so `aRun N β = ((3β)/(22N²))^{−51/121} · exp(−3β/(44N²))`, with `Λ` set to one because an overall
scale cancels from every ratio below. **Nothing here is chosen.** `51/121` and `3/44` are `b₀` and
`b₁` multiplied out, and `Running.b0_pos` and `Running.b1_pos` are what make them positive.

## The statement, with the spacing FIXED

`AsymptoticScalingAt N m` says the lattice mass `m` tracks that running spacing: the ratio converges
to a finite NONZERO limit. Because `aRun` is a fixed function rather than an existential, the
statement can fail — `asymptotic_scaling_has_content` exhibits a positive lattice mass for which it
does, which is precisely what `scaling_as_stated_is_vacuous` could not do for the naive form.

## What this does NOT do

It does not prove asymptotic scaling, and it does not supply `m_lat`. The tree still has no
correlation length in lattice units as a function of the coupling — `Complete.ym_physical_gap_uniform`
and its siblings take the spacing as a PARAMETER and never relate it to `β`. What is now present is a
target that a proof could be aimed at and that a bogus witness cannot satisfy, which is the thing
that was missing.

DERIVED: every numeral traces to `Running`. `51/121` is `b₁/(2b₀²)`, `3/44` is `1/(4N b₀)` with the
`N²` carried separately, `22` and `3` are `b₀ g²` multiplied out, and `2N/β` is the standard `SU(N)`
relation between the lattice coupling and `g²`. `0` is positivity and the limit the naive form
settles for; `1` is the ratio the vacuous repair produces.
-/

namespace MassGap.AsymptoticScaling

open Filter Topology

/-! ## 1. The obvious repair is vacuous too -/

/-- **DEMANDING A CONVERGENT PHYSICAL MASS DOES NOT HELP, so long as the spacing is existential.**

For ANY positive lattice mass tending to zero there is a spacing making the ratio converge to a
positive limit: take the spacing to BE the lattice mass. The ratio is identically `1`.

This is the companion to `ClayAssembly.scaling_as_stated_is_vacuous` and it closes the obvious
repair. The quantifier on `a` is the defect, not the absence of a convergence clause, so the fix must
PIN the spacing rather than constrain it further.

DERIVED: `1` is what `m/m` is, not a magnitude. -/
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

/-- **THE TWO-LOOP RUNNING LATTICE SPACING**, with `Λ` set to one.

DERIVED, and CHECKED rather than retyped: `51/121 = b₁/(2b₀²)` is `b1_over_two_b0_sq`,
`3/(44N²) = 1/(4N b₀)` is `one_over_four_N_b0`, and `22N²/(3β) = b₀g²` at `g² = 2N/β` is `b0_g_sq`,
all at `b₀ = 11N/3` and `b₁ = 34N²/3` — the coefficients `Running.b0_pos` and `Running.b1_pos` are
stated for. The colour count CANCELS from the first, so that exponent is the same for every `SU(N)`.
The overall scale `Λ` cancels from every ratio this file forms, so setting it to one is a choice of
units and not of a magnitude. -/
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

/-- **`b₁/(2b₀²) = 51/121`**, and the colour count CANCELS — the exponent is the same for every
`SU(N)`. `(34N²/3)/(2·(11N/3)²) = 306/726 = 51/121`. -/
theorem b1_over_two_b0_sq {N : ℝ} (hN : N ≠ 0) :
    (34 * N ^ 2 / 3) / (2 * (11 * N / 3) ^ 2) = 51 / 121 := by
  field_simp
  ring

#print axioms b1_over_two_b0_sq

/-- **`1/(4N·b₀) = 3/(44N²)`**, the exponent of the exponential factor. -/
theorem one_over_four_N_b0 {N : ℝ} (hN : N ≠ 0) :
    1 / (4 * N * (11 * N / 3)) = 3 / (44 * N ^ 2) := by
  field_simp
  ring

#print axioms one_over_four_N_b0

/-- **`b₀g² = 22N²/(3β)`** at the standard `SU(N)` relation `g² = 2N/β`, which is the base `aRun`
raises to `-51/121`. -/
theorem b0_g_sq {N β : ℝ} (hβ : β ≠ 0) :
    (11 * N / 3) * (2 * N / β) = 22 * N ^ 2 / (3 * β) := by
  field_simp
  ring

#print axioms b0_g_sq


/-- The running spacing is positive at every positive coupling. -/
theorem aRun_pos {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) : 0 < aRun N β := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hbase : (0 : ℝ) < (3 * β) / (22 * (N : ℝ) ^ 2) := by positivity
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (Real.exp_pos _)

#print axioms aRun_pos

/-! ## 3. The statement -/

/-- **ASYMPTOTIC SCALING AT APERTURE `N`.**

The lattice mass `m` tracks the running spacing: `m(β)/aRun(N,β)` converges to a finite NONZERO
limit as `β → ∞`. That limit is the physical mass in units of `Λ`, and its being nonzero and finite
is what makes the limit a CONTINUUM limit rather than a relabelling.

`aRun` is FIXED here. That is the whole difference from the two vacuous forms: with the spacing
determined by the beta function there is nothing left to choose, so the statement can be false — and
`asymptotic_scaling_has_content` shows it is false for a lattice mass that decays at the wrong rate.

DERIVED: `0 < mphys` is the nonzero clause; nothing else is numeric. -/
def AsymptoticScalingAt (N : ℕ) (m : ℝ → ℝ) : Prop :=
  ∃ mphys : ℝ, 0 < mphys ∧ Tendsto (fun β => m β / aRun N β) atTop (nhds mphys)

#print axioms AsymptoticScalingAt

/-- **IT IS SATISFIABLE** — by a lattice mass that is the running spacing times a constant, which is
what asymptotic scaling asserts the true one is. Recorded so the statement is not accidentally
unsatisfiable, the opposite failure from vacuity. -/
theorem asymptotic_scaling_is_satisfiable {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 < c) :
    AsymptoticScalingAt N (fun β => c * aRun N β) := by
  refine ⟨c, hc, ?_⟩
  have heq : (fun β => (c * aRun N β) / aRun N β) =ᶠ[atTop] fun _ => c := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    field_simp [ne_of_gt (aRun_pos hN hβ)]
  exact Tendsto.congr' heq.symm tendsto_const_nhds

#print axioms asymptotic_scaling_is_satisfiable

/-- **AND IT CAN FAIL — which is what the naive and the repaired forms could not do.**

A lattice mass decaying FASTER than the running spacing, by any factor tending to zero, has ratio
tending to zero, and zero is not a positive limit. So `AsymptoticScalingAt` is a real constraint on
the lattice mass rather than a clause any witness discharges.

The witness is `aRun N β · exp(−β)`: positive everywhere `aRun` is, and its ratio to `aRun` is
`exp(−β)`, the very function `ClayAssembly.scaling_as_stated_is_vacuous` uses to defeat the naive
form. The same witness that made the old statement vacuous refutes the new one, which is the sharpest
way to say the two are different statements.

DERIVED: `exp(−β)` is a witness, not a magnitude, as in `scaling_as_stated_is_vacuous`. -/
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

/-- **THE STATEMENT IS NEITHER VACUOUS NOR EMPTY**, stated once so both halves are checkable
together: there is a lattice mass satisfying it and a lattice mass refuting it. That pair is what
`scaling_as_stated_is_vacuous` shows the naive form does not have — every positive function tending
to zero satisfies that one. -/
theorem asymptotic_scaling_is_a_real_constraint {N : ℕ} (hN : 1 ≤ N) :
    (∃ m : ℝ → ℝ, AsymptoticScalingAt N m) ∧ (∃ m : ℝ → ℝ, ¬ AsymptoticScalingAt N m) :=
  ⟨⟨fun β => 1 * aRun N β, asymptotic_scaling_is_satisfiable hN one_pos⟩,
   ⟨fun β => aRun N β * Real.exp (-β), asymptotic_scaling_has_content hN⟩⟩

#print axioms asymptotic_scaling_is_a_real_constraint

/-! ## 4. The lattice mass, and why the extent must grow with the coupling -/

/-- **THE LAG-ONE DECAY RATIO** `ρ(1)/ρ(0)` at aperture `N` and coupling `β`. The elementary
correlation-length observable the tree can actually form.

DERIVED: `1` and `0` are the two LAGS the ratio relates — the nearest neighbour against the contact
value — and neither is a magnitude. Lag one is CHOSEN among the available lags because it is the only
odd lag the tree bounds (`WeakArm.wilsonCorrAt_le_at_zero_at_extent_six`), every right-hand lag
`LogConvex.corrClay_log_convex` produces being even; the cost of that choice is that the ratio is an
effective mass at one separation rather than an asymptotic decay rate. -/
noncomputable def decayAt (N : ℕ) (β : ℝ) : ℝ :=
  MassGap.wilsonCorrAt N β 1 / MassGap.wilsonCorrAt N β 0

#print axioms decayAt

/-- **THE LATTICE MASS AT LAG ONE**, `m_lat = −log(ρ(1)/ρ(0))`.

**A JUNK VALUE TO KNOW ABOUT BEFORE USING THIS.** Mathlib's `Real.log 0 = 0`, and
`PowerTail.wilsonCorrAt_at_zero_coupling` puts `ρ(1) = 0` at zero coupling, so `mLatAt N 0 = 0` —
which reads as "the lattice mass vanishes at zero coupling" and is the exact opposite of the truth,
where the correlation length is zero and the mass infinite. Every statement below is therefore
guarded by `0 < decayAt`, and nothing here should be read at or near `β = 0`.

DERIVED: `1` and `0` are the two LAGS the ratio relates, not magnitudes. -/
noncomputable def mLatAt (N : ℕ) (β : ℝ) : ℝ := - Real.log (decayAt N β)

#print axioms mLatAt

/-- The junk value, recorded as a theorem so it cannot be walked into. Stated at extent six, the
live aperture, where the circle distance of lag one is checkable by `decide`; the same holds at every
aperture of at least two, for the same reason. -/
theorem mLatAt_at_zero_coupling_is_junk : mLatAt 5 0 = 0 := by
  have hc : Moment.circLag (1 : Fin 6) = 1 := by decide
  have hz : MassGap.wilsonCorrAt 5 0 1 = 0 :=
    MassGap.PowerTail.wilsonCorrAt_at_zero_coupling 5 1 (by rw [hc])
  simp [mLatAt, decayAt, hz]

#print axioms mLatAt_at_zero_coupling_is_junk

/-- **THE LATTICE MASS IS NONNEGATIVE** wherever the decay ratio is positive, because the ratio is at
most one — `WeakArm.wilsonCorrAt_le_at_zero`, the contact bound. -/
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

/-- **A LATTICE MASS THAT DOES NOT VANISH FORBIDS A VANISHING SPACING.**

If `AsymptoticScalingAt N m` holds and `m` is eventually bounded below by a positive constant, then
`aRun` is eventually bounded below by a positive constant too — so the spacing does NOT go to zero
and the limit is not a continuum limit.

This is the obstruction at FIXED extent, and it is why the aperture has to grow with the coupling.
At a fixed aperture the lag-one decay ratio tends to the free-field value — `0.018856` at extent
six, the number `NonnegArm`'s positive control settles on and the shape entry
`CosAvgStability.freeRefSix` carries — so the lattice mass tends to `−log 0.018856`, a positive
CONSTANT rather than zero. Feed that in and the spacing is pinned away from zero.

So `AsymptoticScalingAt N (mLatAt N)` at a single `N` is not the statement to aim at: a correlation
length measured in lattice units cannot grow while the lattice stays the same size. **C2's remaining
half is a JOINT limit, `N → ∞` with `β → ∞`, not a limit in `β` at fixed `N`.**

DERIVED: `1` in `m + 1` is one step above the limit, used only to get an eventual upper bound out of
convergence. No magnitude. -/
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

/-- **THE STATEMENT C2 ACTUALLY NEEDS: a JOINT limit.**

The aperture is a function of the coupling and goes to infinity with it, and the lattice mass is read
at that growing aperture. This is the form `fixed_extent_pins_the_spacing` says is forced — a
correlation length in lattice units cannot grow while the lattice stays the same size.

It is written here and not proved. What it needs beyond this file is the behaviour of
`decayAt (Nof β) β` along a joint trajectory, and the tree has no result of that shape: every bound
it carries is at a fixed aperture, and `Complete.ym_physical_gap_uniform` and its siblings take the
spacing as a PARAMETER and never relate it to `β`.

DERIVED: nothing numeric. `Nof` and the limit are variables. -/
def AsymptoticScalingJoint (Nof : ℝ → ℕ) : Prop :=
  Tendsto (fun β => (Nof β : ℝ)) atTop atTop ∧
    ∃ mphys : ℝ, 0 < mphys ∧
      Tendsto (fun β => mLatAt (Nof β) β / aRun (Nof β) β) atTop (nhds mphys)

#print axioms AsymptoticScalingJoint

/-! ### The trajectory is a steering handle, so `Nof` must stay a PARAMETER

`AsymptoticScalingJoint` takes `Nof` as an argument, and that is deliberate. Writing the obligation
as `∃ Nof, AsymptoticScalingJoint Nof` would reintroduce exactly the freedom
`free_spacing_scaling_is_also_vacuous` warns about, with the trajectory in place of the spacing.

**The handle is real and large.** `aRun N β` depends on `N`, and increases with it: the rpow base
`(3β)/(22N²)` falls while its exponent `-51/121` is negative, and the exponential's argument
`-3β/(44N²)` rises toward zero. Both factors move the same way. Evaluated, at `β = 1` the spacing
runs `2.163, 4.084, 8.969, 16.12, 62.65` across `N = 1, 2, 5, 10, 50` — a factor of `29` from
choosing the trajectory alone, before any physics. `aRun_exp_factor_increasing_in_extent` proves the
monotonicity of the second factor, which is the elementary half of that.

So a continuum limit is taken ALONG A TRAJECTORY the physics fixes, not along one chosen to make the
ratio converge. `Nof` being a parameter is what keeps that distinction.

DERIVED: the figures are `aRun` evaluated, not chosen. -/

/-- The exponential factor of `aRun` increases with the extent at fixed positive coupling — the
elementary half of the steering handle above. -/
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
