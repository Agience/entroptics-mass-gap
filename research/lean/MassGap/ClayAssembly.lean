import Mathlib
import MassGap.MomentShape
import MassGap.GNSHilbert
import MassGap.LatticeTranslNoGo
import MassGap.LagTwoSix
import MassGap.CompactBeta
import MassGap.WeakArm
import MassGap.LagTwoEight

/-!
# MassGap.ClayAssembly — the remaining distance to the Clay statement, as a type

Every other module in this tree proves something. This one states what is NOT proved, in one place,
against the genuine objects, so that the distance to the Clay statement is a TYPE rather than prose
in a planning document. `ClayRemaining` is that type. A term of it, together with what the tree
already proves, is the Clay statement; there is no term of it, and each field names why.

## Why a structure of hypotheses rather than a conditional theorem

`ApertureRoute.FlagshipAt` is already a conditional theorem, and `FlagshipScope` is the reason that
is not enough: `flagship_for_bogus` discharges the ENTIRE flagship conjunction for `bogusYM`, whose
tension is the constant zero and which contains no read, no correlation, no lattice and no gauge
group. A conditional whose conclusion a fabricated object satisfies measures nothing. So every field
below is stated against `wilsonCorrAt` / `GNSHilbert.ymH` / the Wilson Gibbs measure by name, and
`remaining_is_not_vacuous` records the guards that make each one bite.

## The four open inputs, and they are NOT independent

`I1` is B5, the one open inequality. `I2` is the clustering estimate B5's own middle coupling range
needs. `I3` is asymptotic scaling. `I4` is the Hamiltonian. The dependencies are the content:

* **`I2` is upstream of `I1`.** B5 is a `∀ β ≥ 0` statement. Strong coupling closes small `β` and
  weak coupling is asymptotic at large `β`; the middle is `Interior.d2_le_of_analytic_grid`, whose
  every analytic step is proved and whose Lipschitz constant is
  `WilsonAnalytic.cov_bound_extensive`'s `4M·#Plaq`. At the Clay reads the aperture IS the extent, so
  `CompactBeta.clay_covariance_constant_not_aperture_uniform` proves that constant exceeds every
  bound. The volume-free alternatives `cov_bound_local` and `cov_bound_summable` take clustering as
  an ARGUMENT. So `I1` is not reachable without `I2`.
* **`I3` is upstream of `I1` TOO, and that is the part a planning document keeps losing.**
  `corr_at_max_lag_eq_lag_one` below proves `ρ(N) = ρ(1)` at EVERY aperture and EVERY real coupling:
  the correlation at the largest lag IS the correlation at lag one. A fixed-extent periodic
  correlation therefore does not decay — it returns. `Complete.ym_wilson_decay_to_half_period` says
  the same thing from the spectral side and says it is all a gap buys on a torus. Clustering in the
  true sense is the `n → ∞` statement, so it is downstream of the infinite-volume limit, which is
  `I3`'s half of C2.
* **`I3` is upstream of C6**, by `LatticeTranslNoGo.transl_eq_id_of_finite_order` and
  `addHom_to_int_lattice_eq_zero`: `OSData.transl` is an `ℝ⁴` action, `ℝ⁴` is divisible, and no
  lattice translation group is — at finite extent by finite order, on `ℤ⁴` because `ℤ` is not
  divisible either.
* **`I4` is independent of the other three** and is the one C1 item that does not wait on the
  continuum: `GNSHilbert.ymH` exists at fixed spacing.

So the dependency graph has ONE root, `I3`, and `I2` beside it; `I1` waits on both; `I4` waits on
nothing. That is the ordering, and it is why "close B5 first" is the wrong plan.

## What is already proved, and is therefore NOT in the structure

`GNSHilbert.ymH` is a complete complex Hilbert space built from the genuine Wilson Gibbs reflection
form, `ymOmega` is a unit vector, and `nontrivial_ymH` proves the space is not the zero space. Clay
§6.5 makes the Hilbert space part of the solution and it is done. `hilbert_space_half_of_C1_is_proved`
restates that here unconditionally, so the structure carries only what is open.

## The footprint, and the one place it is not foundational

Every THEOREM here is foundational-only. The structure TYPE `ClayRemaining` is not: it carries
`Complete.wilson_reflection_positive_at`, the named axiom, and the reason is worth recording rather
than hiding. `I2_clustering` quantifies over EVERY aperture `N`, and `Complete.d2At N β` at general
`N` routes through reflection positivity — while the PROVED version,
`Complete.wilson_reflection_positive_at_even`, covers even extent `≥ 4` only. Extent four is `2·2`,
so the Clay instance itself does not use the axiom; an APERTURE-UNIFORM statement necessarily does,
because it reaches the odd apertures the proof does not.

That is a fact about the clustering input, not an accident of how the field is written: any bound
uniform in the aperture has to say something at apertures where this tree's reflection positivity is
cited rather than proved.

Build: `python research/code/lean_build.py build MassGap.ClayAssembly`.
-/

namespace MassGap.ClayAssembly

open Filter

/-! ## 1. A fixed-extent correlation does not decay — it returns -/

/-- **`ρ(N) = ρ(1)`: THE CORRELATION AT THE LARGEST LAG IS THE CORRELATION AT LAG ONE.**

At every aperture `N ≥ 1` and every real coupling. `Moment.circLag d = min d (N+1−d)`, so
`circLag ⟨N⟩ = min N 1 = 1 = circLag ⟨1⟩`, and `MomentShape.wilsonCorrAt_circLag_congr` — circle
symmetry, proved at every aperture and coupling — carries the values across.

**This is why B5 at a fixed extent cannot be clustering.** Clustering asks the connected correlator to
become small at large separation; on a periodic lattice the largest separation is not large, it is
lag one seen from the other side. `Complete.ym_wilson_decay_to_half_period` reaches the same wall from
the spectral side and its docstring says so: past `n/2` the periodic correlation turns back up, and
clustering in the true sense is the `n → ∞` statement.

DERIVED: no numeral is chosen. `1` is the lag whose circle distance the largest lag shares, and `N`
is the largest element of `Fin (N+1)`. -/
theorem corr_at_max_lag_eq_lag_one (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    MassGap.wilsonCorrAt N β ⟨N, Nat.lt_succ_self N⟩
      = MassGap.wilsonCorrAt N β ⟨1, Nat.lt_succ_of_le hN⟩ := by
  refine MassGap.MomentShape.wilsonCorrAt_circLag_congr N β ?_
  show Moment.circLag (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
      = Moment.circLag (⟨1, Nat.lt_succ_of_le hN⟩ : Fin (N + 1))
  unfold Moment.circLag
  simp only []
  omega

/-- **THE SAME FACT AS A REFUTATION.** There is no aperture at which the Wilson correlation is
smaller at the largest lag than at lag one — not by any margin, at any coupling. So no statement of
the form "the correlation is below `ε` beyond separation `r`" can hold at fixed extent with `r` past
the half period, however `ε` is chosen. -/
theorem no_fixed_extent_decay_past_half_period (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    ¬ (MassGap.wilsonCorrAt N β ⟨N, Nat.lt_succ_self N⟩
        < MassGap.wilsonCorrAt N β ⟨1, Nat.lt_succ_of_le hN⟩) := by
  rw [corr_at_max_lag_eq_lag_one N hN β]
  exact lt_irrefl _

/-! ## 2. The half of C1 that is proved, restated so the structure need not carry it -/

/-- **CLAY §6.5's HILBERT SPACE EXISTS, UNCONDITIONALLY.** A complete complex inner-product space
built from `ReflectionStrong.wilsonGibbsReflForm` — the genuine Wilson Gibbs reflection form — with a
unit vacuum and provably more than the zero vector in it. No coupling condition, no hypothesis.

Stated here so that `ClayRemaining` carries only what is OPEN: the Hilbert space is not in it because
it is done. What remains of C1 is the Hamiltonian, which is `TransferMovesSomething` below. -/
theorem hilbert_space_half_of_C1_is_proved {d n N : ℕ} [NeZero n]
    (hN : N ≠ 0) (τ : Fin d) (a : Fin n) (m : ℕ) (hm : n = 2 * m) (hm0 : 0 < m) (β : ℝ) :
    ‖MassGap.GNSHilbert.ymOmega hN τ a m hm hm0 β‖ = 1
      ∧ Nontrivial (MassGap.GNSHilbert.ymH hN τ a m hm hm0 β) :=
  ⟨MassGap.GNSHilbert.ymOmega_norm hN τ a m hm hm0 β,
    MassGap.GNSHilbert.nontrivial_ymH hN τ a m hm hm0 β⟩

/-- **`I4`, THE HAMILTONIAN'S OPERATOR, STATED SO THAT `T = 1` FAILS IT.** A `TransferData` whose
induced operator MOVES something.

The `∃ x, opT D x ≠ x` is the whole content and it is not decoration.
`GNSHilbert.ym_target_discharged_trivially` builds `trivialTransfer`, an UNCONDITIONAL `TransferData`
on the genuine Wilson slab algebra with no premise at all, discharging every clause of "Hilbert
space, unit vacuum, positive self-adjoint contraction with `TΩ = Ω`" — and a sixth conjunct saying
`T` is the IDENTITY. `shiftSlab_eq_id` proves the lattice shift is the identity on `SlabShiftStable`'s
own premise, and `HalfLineTransfer.shiftObs_pow_period` proves the shift has finite order, so a
finite-order contraction is an isometry and carries no decay. Every operator the tree can currently
produce fails this predicate, which is exactly why it is the open item.

`-log T` needs `0 ∉ spectrum T` rather than injectivity, so this predicate is necessary and not
sufficient; it is stated as the first thing that is missing, not as the whole of C1's remainder.

DERIVED: no numeral is chosen and none is a level or a threshold. The literals in this declaration
are the identities of the algebraic instances it quantifies over — `0` and `1` of the scalar ring in
`AddCommGroup A` and `Module ℝ A` — and they reach the statement through those instances rather than
through anything this file decides. -/
def TransferMovesSomething {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) : Prop :=
  ∃ x : MassGap.GNSHilbert.H D.toReflForm, MassGap.GNSHilbert.opT D x ≠ x

/-! ## 3. The remaining distance -/

/-- **THE FOUR OPEN INPUTS, against the genuine objects.**

Each field is a statement about `wilsonCorrAt`, the Wilson Gibbs measure, or `GNSHilbert.ymH` by
name. None is about a model, a fabricated spectrum, or an opaque `Prop`, which is the failure
`FlagshipScope.flagship_for_bogus` exhibits and `WightmanData.trivialOSData` exhibits on the OS side.

* `I1_lagTwo` — **B5.** The one open inequality, at the extent the Clay instance uses. `K` is the
  caller's and the thresholds are `LagTwoBound.lagTwoThreshold`,
  `LagTwoQuadratic.lagTwoThresholdQuad` and `LagTwoSix.lagTwoThresholdSix`.
* `I2_clustering` — the aperture-uniform covariance bound. Stated as: ONE constant `L`, at EVERY
  aperture and every coupling, bounding the β-derivative of the substrate. This is exactly what
  `CompactBeta.clay_covariance_constant_not_aperture_uniform` proves the unconditional constant is
  not.
Two of the four inputs are deliberately NOT fields, and the reasons differ. `I3`, asymptotic scaling,
is absent because the obvious statement of it is VACUOUS — `scaling_as_stated_is_vacuous` proves it
is discharged by `exp(−β)` — and the real statement needs a correlation length in lattice units that
this tree does not have. `I4`, the Hamiltonian, is absent because stating it needs the `TransferData`
it is about, so it is `TransferMovesSomething` above, parameterised by that datum. -/
structure ClayRemaining where
  /-- **B5.** -/
  I1_lagTwo : ∃ K : ℝ, 0 < K ∧ K < MassGap.LagTwoSix.lagTwoThresholdSix ∧
    ∀ β : ℝ, 0 ≤ β →
      MassGap.wilsonCorrAt 5 β ⟨2, by omega⟩ ≤ K * MassGap.wilsonCorrAt 5 β ⟨0, by omega⟩
  /-- **Clustering, uniform in the aperture.** -/
  I2_clustering : ∃ L : ℝ, 0 ≤ L ∧
    ∀ (N : ℕ) (β₁ β₂ : ℝ),
      |MassGap.d2At N β₁ - MassGap.d2At N β₂| ≤ L * |β₁ - β₂|

#print axioms ClayRemaining
#print axioms TransferMovesSomething

/-- **`I3` IS NOT A FIELD, BECAUSE THE OBVIOUS STATEMENT OF IT IS VACUOUS — and here is the proof.**

Asymptotic scaling is the missing input to C2's spacing limit and to C8. The naive way to state it is
"a spacing as a function of the coupling, positive, tending to zero": that is discharged by
`exp(−β)`, which knows nothing about `SU(3)`, the lattice, or the beta function. So writing it into
`ClayRemaining` would have added a field a one-line witness satisfies — the failure
`FlagshipScope.flagship_for_bogus` exhibits for the flagship and `WightmanData.trivialOSData`
exhibits for the OS side, committed a third time.

**What the real statement needs, and where it now lives.** `a(β)` has to be tied to the theory: the
physical mass `m_phys = m_lat(β)/a(β)` must converge to a finite nonzero limit as `β → ∞`, which is
what makes the limit a CONTINUUM limit rather than a relabelling. **`MassGap.AsymptoticScaling`
writes that**, and it is downstream of this file, which is why the field is still not here.

It also shows the obvious repair fails: `free_spacing_scaling_is_also_vacuous` proves that leaving
the spacing EXISTENTIAL is discharged by taking `a := m_lat`, ratio identically `1`. The spacing has
to be PINNED, and `Running`'s `b₀ = 11N/3` and `b₁ = 34N²/3` pin it — `aRun` is built from them and
is the first thing to consume that file. `mLatAt` supplies the lattice mass, with the warning that
`Real.log 0 = 0` makes its value at zero coupling a junk `0`.

What remains genuinely open is the JOINT limit: `fixed_extent_pins_the_spacing` shows a lattice mass
bounded away from zero forbids a vanishing spacing, so scaling cannot be stated at fixed extent
either. `Complete.ym_physical_gap_uniform` and its siblings take the spacing `L` as a PARAMETER and
never relate it to `β`.

So C2's remaining half is not formalisation debt with a statement waiting to be proved. **The
statement itself is absent**, and writing it is the first step, not the last.

DERIVED: no numeral. `exp(−β)` is a witness, not a magnitude, and any positive function tending to
zero does the same job. -/
theorem scaling_as_stated_is_vacuous :
    ∃ a : ℝ → ℝ, (∀ β, 0 < a β) ∧ Tendsto a atTop (nhds 0) := by
  refine ⟨fun β => Real.exp (-β), fun β => Real.exp_pos _, ?_⟩
  simpa using Real.tendsto_exp_neg_atTop_nhds_zero

#print axioms scaling_as_stated_is_vacuous

/-! ## 4. `I4` is not reachable from ANY finite-order map, not merely from the shift

`GNSHilbert`'s statement of the open item is "a transfer operator that is not the finite-order
shift". The theorems below sharpen that from a remark about one map to a property of every map of
finite order: on a `TransferData`, finite order plus contractivity forces the form to be PRESERVED,
so such a `T` is an isometry and carries no decay at all. Since
`HalfLineTransfer.shiftObs_pow_period` gives `(shiftObs τ)ⁿ = id` with no hypothesis on the module,
the coupling or the reflection, EVERY operator assembled from lattice translations on a periodic
lattice falls under this. `I4` therefore needs an operator that is not built from lattice
translations at all — a strictly stronger requirement than avoiding one particular map. -/

/-- **The form along the orbit is ANTITONE.** `T_contract` says one step cannot expand the form;
iterating gives the whole sequence. This is the only place contractivity is used. -/
theorem form_iterate_antitone {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (x : A) :
    Antitone (fun k : ℕ => D.form ((fun y => D.T y)^[k] x) ((fun y => D.T y)^[k] x)) := by
  refine antitone_nat_of_succ_le (fun k => ?_)
  have h := D.T_contract ((fun y => D.T y)^[k] x)
  simpa [Function.iterate_succ_apply'] using h

/-- **A FINITE-ORDER CONTRACTION IS AN ISOMETRY OF THE FORM.**

If `Tⁿ = id` for some `n ≥ 1`, then `form (T x) (T x) = form x x` at EVERY `x`. The proof is a
squeeze and nothing else: the form along the orbit is antitone, and the order sends step `n` back to
step `0`, so every value between them is equal — in particular the value at step one.

**This is why `I4` cannot come from the lattice.** `HalfLineTransfer.shiftObs_pow_period` proves
`(shiftObs τ)ⁿ = id` on EVERY observable of the periodic lattice, with no hypothesis on the module,
the coupling or the reflection. So any `TransferData` whose `T` is assembled from lattice
translations has an isometric `T`, hence an `opT` that preserves norms and admits no contraction
factor below one anywhere — not merely on the vacuum complement.
`GNSHilbert.shiftSlab_eq_id` is the extreme case of this at the slab, where the order is one.

DERIVED: no numeral is chosen. `0` and `1` are the orbit steps the squeeze compares and `n` is the
caller's order. -/
theorem finite_order_contraction_is_isometry {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (x : A) :
    D.form (D.T x) (D.T x) = D.form x x := by
  have hanti := form_iterate_antitone D x
  have h1 : D.form ((fun y => D.T y)^[n] x) ((fun y => D.T y)^[n] x)
      ≤ D.form ((fun y => D.T y)^[1] x) ((fun y => D.T y)^[1] x) := hanti hn
  have h0 : D.form ((fun y => D.T y)^[1] x) ((fun y => D.T y)^[1] x)
      ≤ D.form ((fun y => D.T y)^[0] x) ((fun y => D.T y)^[0] x) := hanti (Nat.zero_le 1)
  rw [hper x] at h1
  simp only [Function.iterate_one, Function.iterate_zero_apply] at h1 h0 ⊢
  linarith

/-- **The bridge to the tree's own idiom.** `HalfLineTransfer.shiftObs_pow_period` and
`no_rate_below_one_of_finite_order` state periodicity as `(D.T ^ p) x = x`, a power in the
endomorphism monoid, while the squeeze above runs on `Function.iterate`. Without this the theorem
would be orphaned from the two results it is about.

DERIVED: no numeral. `0` and `1` are the induction's base and step. -/
theorem pow_apply_eq_iterate {A : Type*} [AddCommGroup A] [Module ℝ A]
    (f : A →ₗ[ℝ] A) (k : ℕ) (x : A) : (f ^ k) x = (fun y => f y)^[k] x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      -- `Module.End`'s multiplication IS composition, so the last step is definitional. Spelled with
      -- `rfl` rather than a named `mul_apply` lemma because `LinearMap.mul_apply` does not exist at
      -- the v4.31.0 pin -- verified by this build refusing it.
      rw [Function.iterate_succ_apply, ← ih, pow_succ]
      rfl

/-- **THE ISOMETRY STATEMENT IN THE FORM THE TREE STATES PERIODICITY IN.** Same content as
`finite_order_contraction_is_isometry`, with `(D.T ^ n) x = x` as the hypothesis, so it applies
directly to `HalfLineTransfer.shiftObs_pow_period`. -/
theorem finite_order_contraction_is_isometry_pow {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (D.T ^ n) y = y) (x : A) :
    D.form (D.T x) (D.T x) = D.form x x :=
  finite_order_contraction_is_isometry D n hn
    (fun y => by rw [← pow_apply_eq_iterate D.T n y]; exact hper y) x

/-- **AND THEN IT MOVES NOTHING THE FORM CAN SEE.** A finite-order `T` leaves the form's value
unchanged at every vector, so it cannot be the source of a spectral gap: `-log T` needs
`0 ∉ spectrum T`, and an isometry has all of its spectrum on the unit circle.

Stated as the contrapositive of `TransferMovesSomething`'s intent: a `D` satisfying this is exactly
one that `I4` rules out, and every lattice-translation `D` satisfies it. -/
theorem no_decay_of_finite_order {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : Transfer.TransferData A) (n : ℕ) (hn : 1 ≤ n)
    (hper : ∀ y : A, (fun z => D.T z)^[n] y = y) (ρ : ℝ) (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (x : A)
    (hdecay : D.form (D.T x) (D.T x) ≤ ρ * D.form x x) :
    D.form x x = 0 := by
  have hiso := finite_order_contraction_is_isometry D n hn hper x
  rw [hiso] at hdecay
  nlinarith [D.form_nonneg x]

/-! ## 5. `I2` IS NOT CIRCULAR, and that is what separates it from the aperture route

The aperture route died because `Moment.Read.substrate_lt_of_tension_lt_floor` takes confinement as
its HYPOTHESIS — `DiffractionNoGo` §1. The obvious worry about `I2` is the same one: clustering and
a mass gap sound like the same statement, and assuming clustering to prove the gap would be the same
circle in different clothes.

**It is not the same statement, and the difference is provable.** What
`WilsonAnalytic.cov_bound_summable` consumes is a dominating profile whose TOTAL is bounded
independently of the volume — summable decay. What a mass gap gives is EXPONENTIAL decay. Exponential
implies summable; summable does not imply exponential, and the theorem below exhibits the gap between
them. So `I2` assumes strictly less than it would help prove.

This matters for what to work on. A route that assumes its own conclusion cannot be repaired by
sharpening constants; a route that assumes something strictly weaker can be. `I2` is in the second
class and the aperture was in the first. -/

/-- **SUMMABLE DECAY DOES NOT IMPLY EXPONENTIAL DECAY**, so the clustering input `I2` consumes is
strictly weaker than the mass gap it helps establish, and the interior route is not circular.

The witness is `c d = 1/(d+1)²`: nonnegative, summable, and dominated by no geometric profile. The
argument is one line of asymptotics — if `c d ≤ C·rᵈ` with `r < 1` then `(d+1)²·c d ≤ C·(d+1)²·rᵈ`,
whose right side tends to zero while the left side is identically one.

**And the physics is not incidental to the choice.** In four dimensions a MASSLESS theory has
plaquette–plaquette connected correlations falling like a power of the separation, and a power law
steep enough is summable. So the separating case is not a contrivance: it is the very configuration
`I2` must not silently exclude, which is why the hypothesis has to be summability rather than a rate.

DERIVED: the exponent `2` is the least integer power making `1/(d+1)^p` summable in the sense used
here; `1` is the shift that keeps the denominator away from zero. Neither is a level, and any
summable non-geometric profile witnesses the same separation. -/
theorem summable_clustering_is_weaker_than_a_gap :
    ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧ Summable c ∧
      ¬ ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ d, c d ≤ C * r ^ d := by
  refine ⟨fun d => 1 / ((d : ℝ) + 1) ^ 2, fun d => by positivity, ?_, ?_⟩
  · -- summability, by comparison with the shifted `1/n²`
    have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      simpa using (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact h
  · rintro ⟨C, r, hr0, hr1, hdom⟩
    -- `(d+1)²·rᵈ → 0`, in the same two pieces `StrongArm.exists_geom_quartic_bound` splits into:
    -- `(d+1)² ≤ 2d² + 2` is `(d−1)² ≥ 0`, so the quadratic limit and the bare geometric one suffice.
    have h2 : Tendsto (fun d : ℕ => ((d : ℝ) ^ 2 * r ^ d)) atTop (nhds 0) :=
      tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
    have h0 : Tendsto (fun d : ℕ => r ^ d) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hsum : Tendsto (fun d : ℕ => |C| * (2 * ((d : ℝ) ^ 2 * r ^ d) + 2 * r ^ d))
        atTop (nhds 0) := by
      simpa using (((h2.const_mul (2 : ℝ)).add (h0.const_mul (2 : ℝ))).const_mul |C|)
    obtain ⟨d, hd⟩ := (hsum.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
    have hrpow : (0 : ℝ) ≤ r ^ d := pow_nonneg hr0 d
    have hsq : ((d : ℝ) + 1) ^ 2 ≤ 2 * (d : ℝ) ^ 2 + 2 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
    have hpos : (0 : ℝ) < ((d : ℝ) + 1) ^ 2 := by positivity
    have h1 : (1 : ℝ) ≤ C * r ^ d * ((d : ℝ) + 1) ^ 2 := by
      have hk := hdom d
      rw [div_le_iff₀ hpos] at hk
      linarith
    have step1 : C * r ^ d * ((d : ℝ) + 1) ^ 2 ≤ |C| * r ^ d * ((d : ℝ) + 1) ^ 2 := by
      have hnn : (0 : ℝ) ≤ r ^ d * ((d : ℝ) + 1) ^ 2 := by positivity
      nlinarith [le_abs_self C, hnn]
    have step2 : |C| * r ^ d * ((d : ℝ) + 1) ^ 2 ≤ |C| * r ^ d * (2 * (d : ℝ) ^ 2 + 2) := by
      have hnn : (0 : ℝ) ≤ |C| * r ^ d := by positivity
      nlinarith [hsq, hnn]
    have step3 : |C| * r ^ d * (2 * (d : ℝ) ^ 2 + 2)
        = |C| * (2 * ((d : ℝ) ^ 2 * r ^ d) + 2 * r ^ d) := by ring
    linarith [hd, h1, step1, step2, step3]

#print axioms summable_clustering_is_weaker_than_a_gap

/-- **AND THE WEIGHT `I2` ACTUALLY CARRIES IS `circLag²`, SO SUMMABILITY IS THE WRONG HYPOTHESIS —
a BOUNDED SECOND MOMENT is.**

This corrects the field's own description. `I2_clustering` is a Lipschitz bound on
`Complete.d2At`, and `d2At N β = ∑_d p_d · circLag(d)²` — the moment weights each lag by the SQUARE
of its circle distance. `CompactBeta.profile_to_moment_not_uniformly_lipschitz` is the machine-checked
statement that this matters: for every `L` there are an aperture and two reads whose raw profiles
differ by at most `t` at every lag and whose moments differ by more than `L·t`, the lost factor being
`((N+1)/2)²`. So a volume-free bound on the INDIVIDUAL correlators — which is all
`WilsonAnalytic.cov_bound_summable` delivers — does not give `I2`.

**What the obstruction's witness is, and why it points somewhere.** The profile that defeats the
Lipschitz bound is a SPIKE at the middle lag (`ContactDominance.midLag`). That is exactly the shape a
decaying correlation does not have, so the obstruction does not show the Wilson profile suffers it —
it shows the map is bad on ARBITRARY reads. On profiles dominated by `c` with `∑_k c k · k² < ∞` the
moment is bounded uniformly in the aperture, because that sum IS the moment. So the honest form of
`I2` is: the connected correlator is dominated by a profile with a bounded SECOND MOMENT in the
circle distance, uniformly in the volume.

**That is still strictly weaker than a mass gap**, which is what this theorem records: `1/(d+1)⁴` has
a summable second moment and is dominated by no geometric profile. So sharpening `I2` from summability
to a bounded second moment does NOT make it circular — it stays in the class the aperture route was
not.

DERIVED: the exponent `4` is `2 + 2` — two powers to beat the `circLag²` weight and two to leave a
summable remainder — and `1` is the shift keeping the denominator from zero. Neither is a level, and
any profile with a finite second moment and no geometric bound witnesses the same separation. -/
theorem bounded_second_moment_clustering_is_weaker_than_a_gap :
    ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧ Summable (fun d => c d * ((d : ℝ)) ^ 2) ∧
      ¬ ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ d, c d ≤ C * r ^ d := by
  refine ⟨fun d => 1 / ((d : ℝ) + 1) ^ 4, fun d => by positivity, ?_, ?_⟩
  · -- second moment: `d²/(d+1)⁴ ≤ 1/(d+1)²`, and that is summable
    have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      simpa using (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    refine hbase.of_nonneg_of_le (fun d => by positivity) (fun d => ?_)
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
    have hpos4 : (0 : ℝ) < ((d : ℝ) + 1) ^ 4 := by positivity
    -- `d²/(d+1)⁴ ≤ 1/(d+1)²` is `d² ≤ (d+1)²`, taken through a single subtraction so that only
    -- `div_nonneg` is named -- `div_le_div_iff` does not exist at the v4.31.0 pin.
    rw [← sub_nonneg]
    have hrw : 1 / ((d : ℝ) + 1) ^ 2 - 1 / ((d : ℝ) + 1) ^ 4 * ((d : ℝ)) ^ 2
        = (((d : ℝ) + 1) ^ 2 - ((d : ℝ)) ^ 2) / ((d : ℝ) + 1) ^ 4 := by
      field_simp
    rw [hrw]
    exact div_nonneg (by nlinarith [hd]) hpos4.le
  · rintro ⟨C, r, hr0, hr1, hdom⟩
    have h4 : Tendsto (fun d : ℕ => ((d : ℝ) ^ 4 * r ^ d)) atTop (nhds 0) :=
      tendsto_pow_const_mul_const_pow_of_lt_one 4 hr0 hr1
    have h0 : Tendsto (fun d : ℕ => r ^ d) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hsum : Tendsto (fun d : ℕ => |C| * (8 * ((d : ℝ) ^ 4 * r ^ d) + 8 * r ^ d))
        atTop (nhds 0) := by
      simpa using (((h4.const_mul (8 : ℝ)).add (h0.const_mul (8 : ℝ))).const_mul |C|)
    obtain ⟨d, hd⟩ := (hsum.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
    have hrpow : (0 : ℝ) ≤ r ^ d := pow_nonneg hr0 d
    have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hq : ((d : ℝ) + 1) ^ 4 ≤ 8 * (d : ℝ) ^ 4 + 8 := by
      nlinarith [sq_nonneg ((d : ℝ) - 1), sq_nonneg ((d : ℝ) + 1), sq_nonneg ((d : ℝ) ^ 2 - 1), hdn]
    have hpos : (0 : ℝ) < ((d : ℝ) + 1) ^ 4 := by positivity
    have h1 : (1 : ℝ) ≤ C * r ^ d * ((d : ℝ) + 1) ^ 4 := by
      have hk := hdom d
      rw [div_le_iff₀ hpos] at hk
      linarith
    have step1 : C * r ^ d * ((d : ℝ) + 1) ^ 4 ≤ |C| * r ^ d * ((d : ℝ) + 1) ^ 4 := by
      have hnn : (0 : ℝ) ≤ r ^ d * ((d : ℝ) + 1) ^ 4 := by positivity
      nlinarith [le_abs_self C, hnn]
    have step2 : |C| * r ^ d * ((d : ℝ) + 1) ^ 4 ≤ |C| * r ^ d * (8 * (d : ℝ) ^ 4 + 8) := by
      have hnn : (0 : ℝ) ≤ |C| * r ^ d := by positivity
      nlinarith [hq, hnn]
    have step3 : |C| * r ^ d * (8 * (d : ℝ) ^ 4 + 8)
        = |C| * (8 * ((d : ℝ) ^ 4 * r ^ d) + 8 * r ^ d) := by ring
    linarith [hd, h1, step1, step2, step3]

#print axioms bounded_second_moment_clustering_is_weaker_than_a_gap

/-! ## 6. `LawAbove` IS THE REMAINING OBLIGATION, and it cannot come from a coupling-uniform argument

`NonnegArm.LawAbove b` is the tree's own name for what is left, and its docstring says so: *"THE
REMAINING OBLIGATION… Nothing else is open."* The chain is short and every other link is proved —
`NonnegArm.lawBelow_holds` gives the law on `[0, b]` unconditionally, and
`ApertureRoute.confinement_at_an_aperture_of_law_above_cut` carries `LawAbove b` to
`ConfinesAtAnAperture` and thence to the flagship.

**The split point is tiny, and that is measured rather than assumed.** `b` comes from
`ContactFloor.contact_relative_unconditional`, whose own hypothesis is
`StrongCoupling.coreRate (16*4) b < 1` with `coreRate K β = 4(K+1)²(e^{2β}−1)e^{4βK}` at `K = 64`.
Solving `coreRate 64 b = 1` gives `b = 2.936e−5`. So the PROVED arm covers `[0, 2.94e−5]` and
`LawAbove` must carry everything above it, including the measured peak at `β = 2.8`.

**And the theorem below says where not to look for it.** -/

/-- **THE FLAT PROFILE REFUTES `LawAbove`.**

`LawAbove` asks for ONE `C`, at EVERY aperture. On the flat profile `ρ ≡ 1` the requirement
`ρ(d) ≤ C·ρ(0)/circLag(d)⁴` reads `1 ≤ C/circLag(d)⁴`, i.e. `C ≥ circLag(d)⁴` — and at extent `2m`
the middle lag has `circLag = m`, so `C` would have to exceed `m⁴` at every `m`. No real number does.

**THE ARITHMETIC IS NOT NEW AND IS NOT RE-PROVED HERE.** `WeakArm.exists_lag_halving` already gives,
for every `C` and every cut, a lag `k` past the cut with `C/k⁴ < 1/2`, by the same ceiling
construction. This theorem is that lemma applied at the flat profile, and the only thing it adds is
the SENTENCE BELOW — which is about what the tree proves elsewhere, not about arithmetic.

**What that rules out, and it is a whole class of attacks.**
`FreeFieldLagTwo.flat_profile_meets_every_uniform_fact` proves `ρ ≡ 1` satisfies EVERY
coupling-uniform fact this tree proves — nonnegativity, positive total mass, circle symmetry,
log-convexity, contact dominance, `LinkGram`'s `ρ(2) ≤ ρ(1)` and `SlabQuadratic`'s quadratic. So no
argument assembled from those facts can reach `LawAbove`, however the pieces are put together:
the conclusion is false on a profile all of them admit.

`LawAbove` therefore requires genuine `β`-DEPENDENCE. That is the same wall the shape route hits for
B5, which is no coincidence — `LawAbove` implies B5 through the substrate, so it inherits B5's
obstructions and adds the aperture-uniformity of `C` on top.

**AND THE OBVIOUS `β`-DEPENDENT ROUTE IS CIRCULAR.** `WeakArm.no_uniform_quartic_constant_of_vanishing_rate`
settles what a geometric envelope `ρ(d)/ρ(0) ≤ e^{−M·d}` would have to supply: its rate must be
bounded away from ZERO **uniformly in the coupling AND the aperture**, because a rate positive at each
coupling separately is defeated lag by lag. Its docstring names that as exactly what `[b, ∞)` lacks.
A rate bounded away from zero uniformly in coupling and aperture IS the mass gap, so reaching
`LawAbove` through an envelope assumes the conclusion — the same circle
`DiffractionNoGo` §1 found in the aperture route.

This does NOT close `LawAbove`: the theorem constrains the ENVELOPE route only, and nothing here says
the law must come that way. What it does is leave the live question sharp — whether `LawAbove` is
reachable without an envelope — rather than leaving "clustering" to do unexamined work.

DERIVED: the exponent `4` is `LawAbove`'s own, and `NonnegArm`'s docstring derives it as the integer
above the convergence threshold `3` for `∑ k²·C/k^s`, with `ShareEnvelope.cubic_contact_relative_gives_no_bound`
proving `3` itself false. `1` is the lag cut excluding the contact term. Nothing here is chosen. -/
theorem flat_profile_admits_no_uniform_quartic_constant :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → (1 : ℝ) ≤ C / ((m : ℝ)) ^ 4 := by
  rintro ⟨C, _, h⟩
  -- The arithmetic is `WeakArm.exists_lag_halving`, at the level `1/2` it is already stated with.
  -- Re-proving it here would have been a second copy of the same ceiling construction.
  obtain ⟨k, _, hk1, hhalf⟩ := MassGap.WeakArm.exists_lag_halving C 1
  have := h k hk1
  linarith

#print axioms flat_profile_admits_no_uniform_quartic_constant

/-! ## 7. THE STRONG ARM HAS AN ABSOLUTE CEILING, and it is nowhere near the physics

`LagTwoBound.exists_cut_lag_two_ratio` and its extent-eight twin
`LagTwoEight.exists_cut_lag_two_ratio_eight` both run under `StrongCoupling.coreRate (16·4) β < 1`,
and the cut they produce is `2.936e−5`. The natural hope is that a sharper cluster expansion — a
smaller touch degree `K`, a better prefactor — pushes that up far enough to meet the weak arm.

**It cannot, and the reason has nothing to do with `K`.** `coreRate K β = 4(K+1)²(e^{2β}−1)e^{4βK}`
carries the per-plaquette activity `e^{2β}−1` as a FACTOR, and the other two factors are at least one
at every `K` and every `β ≥ 0`. So `coreRate K β < 1` forces `4(e^{2β}−1) < 1` on its own, and that is
a bound on `β` with no `K` in it at all. -/

/-- **NO CHOICE OF TOUCH DEGREE LETS THE STRONG ARM PAST `β = 0.12`.**

At every `K` and every `β ≥ 0`, `coreRate K β < 1` forces `β < 0.12`. The measured peak of the
observable this programme is about sits at `β = 2.8`, a factor above `23` away, so the strong-coupling
arm does not reach the physical region and no improvement to the expansion's constants will take it
there. `CLAY-GOAL`'s prose puts the ceiling at `ln 2 / 2 = 0.347` for a hypothetical expansion needing
activity below one; `coreRate`'s own `4(K+1)²` makes the real ceiling tighter still.

**What this does NOT say.** It bounds `coreRate`, hence every route that runs under
`coreRate K β < 1` — which is both strong arms in this tree. It says nothing about a DIFFERENT
strong-coupling estimate not of this form, and it is not an impossibility proof for the middle
interval; it locates the middle interval's lower end.

DERIVED: `0.12` is a round rational ABOVE the true ceiling `log(5/4)/2 = 0.111572`, chosen so the
bound is loose in the safe direction — a tighter numeral would strengthen the theorem and is not
needed, since the claim is about the gap to `2.8`. `4`, `2` and the `+1` are `coreRate`'s own
constants; `1.12` and `1.2544 = 1.12²` come from `Real.add_one_le_exp` at `0.12` and nothing else. -/
theorem coreRate_lt_one_forces_small_beta {K : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (h : MassGap.StrongCoupling.coreRate K β < 1) : β < 0.12 := by
  by_contra hcon
  push_neg at hcon
  have h12 : (1.12 : ℝ) ≤ Real.exp 0.12 := by
    have := Real.add_one_le_exp (0.12 : ℝ); linarith
  have hsplit : Real.exp (2 * 0.12) = Real.exp 0.12 * Real.exp 0.12 := by
    rw [← Real.exp_add]; ring_nf
  have hexp024 : (1.2544 : ℝ) ≤ Real.exp (2 * 0.12) := by
    rw [hsplit]; nlinarith [h12, Real.exp_pos (0.12 : ℝ)]
  have hmono : Real.exp (2 * 0.12) ≤ Real.exp (2 * β) :=
    Real.exp_le_exp.mpr (by linarith)
  have hE : (1.2544 : ℝ) ≤ Real.exp (2 * β) := le_trans hexp024 hmono
  have hK1 : (1 : ℝ) ≤ ((K : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  have hK : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := by nlinarith [hK1]
  have hEK : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := by
    refine Real.one_le_exp ?_
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith [hβ]
  unfold MassGap.StrongCoupling.coreRate at h
  -- three chained products; `nlinarith` will not find them, so each is supplied
  have hactnn : (0 : ℝ) ≤ Real.exp (2 * β) - 1 := by linarith
  have hKm1 : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 2 - 1 := by linarith
  have hb1 : (Real.exp (2 * β) - 1) ≤ ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1) := by
    nlinarith [mul_nonneg hKm1 hactnn]
  have hX : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1) := by
    nlinarith [hb1, hactnn]
  have hb2 : 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1)
      ≤ 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp (2 * β) - 1) * Real.exp (4 * β * (K : ℝ)) :=
    le_mul_of_one_le_right hX hEK
  linarith [h, hb1, hb2, hE]

#print axioms coreRate_lt_one_forces_small_beta

/-! ## 8. The guards — why no field is dischargeable by a witness with nothing in it -/

/-- **`I2` IS NOT MET BY THE UNCONDITIONAL BOUND, and that is a theorem rather than a remark.**
`CompactBeta.clay_covariance_constant_not_aperture_uniform` exhibits, for every candidate constant, an
aperture at which `cov_bound_extensive`'s `4M·#Plaq` exceeds it — because at the Clay reads the
aperture IS the extent and `#Plaq = 16(N+1)⁴`. So the only unconditional route to `I2` fails, and
what is left is clustering.

Recorded as the name to consult rather than restated, because restating a machine-checked theorem in
a weaker form is how a tree starts disagreeing with itself. -/
theorem I2_needs_clustering_not_the_extensive_bound (M : ℝ) (hM : 0 < M) (B : ℝ) :
    ∃ N : ℕ, B < 4 * M * (Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (N + 1)) : ℝ) :=
  MassGap.CompactBeta.clay_covariance_constant_not_aperture_uniform M hM B

/-- **`I1` DOES NOT GIVE CLUSTERING BY ITSELF**, restated from `corr_at_max_lag_eq_lag_one` so the
dependency is visible where the structure is. Whatever `I1` bounds at lag two, the correlation at the
LARGEST lag is the lag-one value at every aperture and coupling, so no fixed-extent bound is a decay
statement past the half period. -/
theorem I1_is_not_clustering (N : ℕ) (hN : 1 ≤ N) (β : ℝ) :
    MassGap.wilsonCorrAt N β ⟨N, Nat.lt_succ_self N⟩
      = MassGap.wilsonCorrAt N β ⟨1, Nat.lt_succ_of_le hN⟩ :=
  corr_at_max_lag_eq_lag_one N hN β

#print axioms form_iterate_antitone
#print axioms finite_order_contraction_is_isometry
#print axioms pow_apply_eq_iterate
#print axioms finite_order_contraction_is_isometry_pow
#print axioms no_decay_of_finite_order
#print axioms corr_at_max_lag_eq_lag_one
#print axioms no_fixed_extent_decay_past_half_period
#print axioms hilbert_space_half_of_C1_is_proved
#print axioms I2_needs_clustering_not_the_extensive_bound
#print axioms I1_is_not_clustering

end MassGap.ClayAssembly
