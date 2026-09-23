import Mathlib
import MassGap.CubeBranch
import MassGap.OddLagSplit
import MassGap.Spectral
import MassGap.Apriori
import MassGap.Certify
import MassGap.Model
import MassGap.Moment
import MassGap.Sharp
import MassGap.Bessel
import MassGap.FreeField
import MassGap.Reconstruction
import MassGap.Capacity
import MassGap.WilsonBridge

/-!
# The mass gap from named inputs — assembly and results

`Apriori.lean` and `Model.lean` derive gap, non-triviality and `SO(4)` from the two a priori
statements `A1` (confinement) and `A2` (isotropy). This file discharges `A1` and `A2`, so the
conclusions below carry no `A1`/`A2` hypothesis.

## The one named axiom

The only `axiom` declared in this file is `wilson_reflection_positive_at` — reflection positivity of
the Wilson ensemble at every aperture (Osterwalder–Seiler, cited). Every other declaration here is a
definition or a theorem, and each reports the three foundational axioms plus that one.

Confinement is reached in one direction: a bound on the substrate puts the tension below the entropy
floor `κ₀ = ¼log3`. The aperture is a variable throughout, so the statements can say how the margin
moves as the window widens relative to the substrate.

## The results (in order)

* `confinement_of_bounded_substrate` — from `∃ B, ∀ N β, d2At N β ≤ B`, with no value for `B` named,
  the tension is below the floor at every large enough aperture and every coupling. No numeral
  appears in the statement.
* `confinement_of_growth_ratio` — the same from a weaker hypothesis: the substrate moment may grow
  with the aperture, provided the aperture-free ratio `substrateRatio` stays under a constant that
  clears the floor gap. A bounded moment is the special case.
* `substrateRatio_lt_of_tension_lt_floor` — the converse at one aperture: a tension below the floor
  forces the ratio under a ceiling built from the floor alone.
* `margin_tendsto_floor` — under one aperture-independent substrate bound the surplus `Δ = κ₀ − μ`
  converges to `κ₀`.
* `ym_mass_gap_of_substrate` — gap, non-triviality and `SO(4)` for `ymModelAt N` at every large
  enough aperture, from that one substrate hypothesis.
* `ym_mass_gap_of_ratio` — the same from the growth hypothesis.
* `ym_mass_gap_certified hconf` and `ym_mass_gap_of_junction hconf …` — the conditional forms at the
  pinned aperture, taking the confinement read as an explicit hypothesis.
* `ym_mass_gap_spectral` — the gap as decay of an arbitrary finite mode family, with the
  finite-aperture margin `‖m_k‖ ≤ 3^{-1/4}` an explicit hypothesis rather than a property of a chosen
  witness. That scale separates the `SU(N)` read (measured `0.18`–`0.30`) from the `U(1)`-Coulomb one
  (`m_hi ≈ 1`). `spectral_bar_nonvacuous` exhibits the hypothesis satisfied at any family size and
  any magnitude in `(0, 3^{-1/4}]`, naming no value. The ceiling's physical grounding is the
  out-of-Lean single-plaquette enclosure (`certify/small_volume_enclosure.py`).
* `ym_reconstructed_gap` — `H = -log T` is self-adjoint, `H ≥ 0`, with `0` in its spectrum and
  `spectrum H ⊆ {0} ∪ [κ₀, ∞)`. Foundational axioms only.
* `ym_mass_gap_grid_certified` — the alternative interior: a finite grid plus a measured modulus of
  continuity, taking the two ends as hypotheses.

`Otr_iso` (the `A2` isometry), `readYM_is_wilson` (the C-3 identification, by `rfl`),
`wilson_reflection_positive_at_even`, `ym_finite_aperture`, `rArgYM_pos`, `ym_ratio_pos` and
`ym_tension_is_moment` are theorems. The read is concrete (`Moment.Read`): `μYM`, `pcorrYM` and
`thetaYM` are all derived from one nonnegative correlation `readYM β : Read nCorrYM`.

## Scope

The physics input is reflection positivity. The confinement hypothesis is a statement about the
substrate — that its correlation has a finite length, so its moment about the circle distance does
not grow with the window — and it is supplied to the theorems rather than asserted by them. The
construction runs from the finite aperture out to the cited classical results it meets. See
PAPER §12. -/

namespace MassGap

open scoped Matrix

/-! ## The model's data: reading-A as a concrete map, and reflection positivity

`readYM` and `readingA_wilson` apply a concrete reading-A to the ensemble's correlation, so the C-3
identification is discharged by `rfl` (`readYM_is_wilson`). The read-side physical input is
reflection positivity (Osterwalder–Seiler), the named axiom `wilson_reflection_positive_at`. -/

/-- The correlation dimension of the entropy-matched read — the number of resolved lags, pinned to
the read aperture `L = 16` (the SU(2) `L16` configurations the certificate reads,
`certify/ym_crossover_confinement_of_grid.py`). Fixing it to a concrete value makes the
finite-aperture premise `ym_finite_aperture` a theorem discharged by `norm_num` rather than an
axiom; that premise holds for every `N ≥ 9`. Independence of the conclusion from `L` is the separate
`gap_uniform_in_volume_of_intensive`.

CHOSEN: `16` is the read aperture the shipped ensembles carry (`L16`). Every theorem in this file is
stated at a variable aperture `N` (`wilsonCorrAt`, `readYMAt`, `μYMAt`, `d2At`, `ymModelAt`), and the
pinned objects are the `nCorrYM` instance by `rfl` (`readYM_is_readYMAt`, `μYM_is_μYMAt`,
`ymModel_is_ymModelAt`). The `2` and `9` above are a citation and a remark, not inputs. -/
def nCorrYM : ℕ := 16

/-- The `SU(3)` Wilson ensemble's connected plaquette correlation at coupling `β`, in four
dimensions, over the `N + 1` lags.

It is constructed, not abstract. `WilsonBridge.corrClay` is the Gibbs expectation `⟨φ_{p₀}·φ_p⟩_β`
against normalised product Haar with the real Wilson Boltzmann weight, on
`WilsonHypercubic.bd (d := 4) (n := N+1)` — the periodic four-dimensional `SU(3)` lattice
`WilsonGauge`'s Osterwalder–Schrader measure is built on. The plane is spanned by directions `0` and
`1` and the lag runs along `2` transverse to it, so the lag is a spatial separation.

`wilson_reflection_positive_at` is therefore a statement about this constructed correlation, not the
defining property of an abstract one.

DERIVED: nothing here sets a scale. `4` is the problem's dimension, `3` is `SU(3)`, and `N + 1` is the
periodic extent the lag index runs over — the caller's aperture, carried through. -/
noncomputable def wilsonCorrAt (N : ℕ) (β : ℝ) : Fin (N + 1) → ℝ :=
  fun d => WilsonBridge.corrClay (N + 1) β d

/-- The correlation at the pinned aperture — the `nCorrYM` instance of `wilsonCorrAt`. The aperture
is a value of a variable, not a property of the theory, so the ensemble data carries it.

DERIVED: the `+ 1` is the lag arity — `Fin (N + 1)` indexes lags `0 … N`, so a window of size `N`
resolves `N + 1` of them. It is a counting fact about the index type, not a value. -/
noncomputable def wilsonCorr : ℝ → (Fin (nCorrYM + 1) → ℝ) := wilsonCorrAt nCorrYM

/-- Reflection positivity of the Wilson ensemble — cited (K. Osterwalder, E. Seiler, *Gauge field
theories on a lattice*, Ann. Phys. **110** (1978) 440). The whitened `:F²:` correlation is nonnegative
at every lag — the transfer-matrix spectral form `ρ(d) = Σ_n w_n e^{-E_n d}` with `w_n ≥ 0` — with
positive total mass. This is the read-side physical input, a named axiom that `#print axioms`
reports. With reading-A concrete (below) the model identification `readYM_is_wilson` is a `rfl`
theorem.

It is stated at every aperture, because that is what the cited result says: reflection positivity of
the Wilson measure is a property of the ensemble, not of the window a reader chooses. Stating it only
at `nCorrYM` would put the pinned window inside the physical input.

DERIVED: the only numeral in the statement is the `0` of `0 ≤ ρ d` and `0 < Σ ρ`, which is
nonnegativity and positive total mass — the content of the cited result, not a magnitude. The
`110`, `1978` and `440` above are the journal citation.

Scope against the theorem below. `wilson_reflection_positive_at_even` proves the same conjunction, at
the same `wilsonCorrAt`, whenever the extent is even and at least `4` and the coupling is
nonnegative. This axiom quantifies over every aperture and every real `β`, so it also covers odd
extents, extent two, and negative coupling.

The coupling restriction tracks the sign of the coupling.
`CharacterExpansion.NegControl.su3_kernel_nonneg_iff` proves an iff on two explicit `SU(3)` elements:
the Wilson cross kernel is positive-semidefinite exactly when the coupling is nonnegative. At `β < 0`
the object the odd-lag argument is about is itself negative on this group. The even lags carry no `β`
hypothesis (`ActionSplit.plaqReflPositive_of_even_lag`), because that argument is a conditional
square against a positive Boltzmann weight; the odd lags do.

The extent restriction is load-bearing: at `m = 1` levels `1` and `m` coincide, so two distinct
straddling plaquettes share a half-link while having different plane links, and the group action
cannot be defined coordinatewise (`OddLagSplit.negctl_plane_assignment_collides_at_m_one`). -/
axiom wilson_reflection_positive_at :
    ∀ (N : ℕ) (β : ℝ), (∀ d, 0 ≤ wilsonCorrAt N β d) ∧ 0 < ∑ d, wilsonCorrAt N β d

/-- The body of `wilson_reflection_positive_at`, proved at even extent and nonnegative coupling.

`wilsonCorrAt N β = WilsonBridge.corrClay (N+1) β` by definition, so this is the same conjunction the
axiom above asserts, on the stated domain, with `#print axioms` reporting the three foundational
axioms and nothing else. `OddLagSplit.corrClay_reflection_positive`'s whole hypothesis list is the
extent parity, `2 ≤ m`, and `0 ≤ β`.

The chain behind it: the action splits across a link-reflection plane into a positive half, its mirror and
a straddling remainder (`OddLagSplit.oplaq_side`, `sum_oplaq_split`); the mirror's contribution is the
positive half's at the reflected configuration (`sum_oplqMinus_eq_plus_refl`); the product Haar factors over
the three blocks with the integrand free to couple them (`integral_three_block`, via `sumPiEquivProdPi` and
one index equivalence); the mirror's variables transport onto the positive half (`measurePreserving_mirrorT`,
`reflConf_joinO_mirror`); the two fixed planes' opposite handedness is reconciled by inverting the plane
variables under the integral (`mixedAct_invAt_mul`, `invLink_measurePreserving`); and the straddling factor
is then one cross form of two block-diagonal words, which the Wilson kernel's positive-semidefiniteness
accepts (`CrossingIntegration.wilson_crossing_pairing_nonneg`). No representation theory enters anywhere.

DERIVED: `N + 1 = 2 * m` with `2 ≤ m` is the even-extent condition, so the extent is even and at
least four; `0 ≤ β` is the sign of the coupling. Both are `OddLagSplit.corrClay_reflection_positive`'s
own hypotheses, and `0 ≤ wilsonCorrAt N β d` and `0 < ∑ d, wilsonCorrAt N β d` are the conclusion's
nonnegativity and positive total mass. -/
theorem wilson_reflection_positive_at_even (N m : ℕ) (hm : N + 1 = 2 * m) (hm2 : 2 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) :
    (∀ d, 0 ≤ wilsonCorrAt N β d) ∧ 0 < ∑ d, wilsonCorrAt N β d :=
  MassGap.OddLagSplit.corrClay_reflection_positive N m hm hm2 hβ

#print axioms wilson_reflection_positive_at_even

/-- Reading-A as a concrete function. It packages a whitened, reflection-positive correlation into
the entropy-matched `Moment.Read`, from which the tension `μ`, the probability vector `p` and the
angles `θ` are all derived (`Moment.Read`).

DERIVED: `0 ≤ ρ d` and `0 < ∑ d, ρ d` are the two halves of the reflection-positivity hypothesis the
`Moment.Read` fields require; `Fin (N + 1)` is the lag arity of a window of size `N`. -/
noncomputable def readA {N : ℕ} (ρ : Fin (N + 1) → ℝ)
    (h : (∀ d, 0 ≤ ρ d) ∧ 0 < ∑ d, ρ d) : Moment.Read N :=
  { ρ := ρ, hρ := h.1, hpos := h.2 }

/-! ### The aperture as a variable

The read is defined at a variable aperture and the pinned objects are its `nCorrYM` instance
(`readYM_is_readYMAt`, `μYM_is_μYMAt`, both `rfl`). Stating the read this way lets the theorems say
how the margin moves as the window widens relative to the substrate.

`readYMAt` is the only declaration in the development that applies
`wilson_reflection_positive_at`; everything reporting that axiom reports it through this one
definition. -/

/-- Reading-A at an arbitrary aperture. -/
noncomputable def readYMAt (N : ℕ) (β : ℝ) : Moment.Read N :=
  readA (wilsonCorrAt N β) (wilson_reflection_positive_at N β)

/-- Reading-A of the Wilson ensemble (§2–§3), at the pinned aperture. It is the `nCorrYM` instance of
`readYMAt`, so the axiom is applied at exactly one place in the development — `readYMAt`'s
definition, immediately above — and the pinned read is not a second route to it.

DERIVED: `§2`–`§3` is a cross-reference to the paper, not a value. This definition introduces no
numeral of its own. -/
noncomputable def readingA_wilson (β : ℝ) : Moment.Read nCorrYM := readYMAt nCorrYM β
/-- The read the rest of the file reasons about, defined as reading-A of the Wilson ensemble at the
pinned aperture. -/
noncomputable def readYM (β : ℝ) : Moment.Read nCorrYM := readYMAt nCorrYM β

/-- The centre-vortex tension read through an aperture of size `N`, the `Moment.Read.tension` of
`readYMAt N β`. `μYM` is its `nCorrYM` instance. -/
noncomputable def μYMAt (N : ℕ) (β : ℝ) : ℝ := (readYMAt N β).tension

/-- The substrate's second moment about the circle distance, read through an aperture of size `N`.
Under the aperture reading this is a quantity of the substrate: the window contributes the separate
factor `(2π/(N+1))²` (`Moment.Read.thetaMoment_eq`), and clustering says this one does not grow with
`N`. -/
-- DERIVED: `Fin (N+1)` is the lag arity; the exponent 2 is what a second moment is; and the distance
-- is `Moment.circLag`, the separation on the circle, because that is the only distance the read can
-- see. `cos` is even and 2π-periodic, so `cos (θ d)` depends on the lag only through
-- `min d (N+1-d)` (`Moment.Read.cos_theta_circ`).
--
-- The circle distance is what makes the moment boundable. On a periodic extent of `N+1` sites the
-- correlation obeys ρ(N) = ρ(-1) = ρ(1), so the far half of the lag range is the near half
-- reflected; weighting it by the raw `d²` makes the moment grow like `N²` even at fixed correlation
-- length. For ρ(d) = e^{-dist/1.5}:
--
--     extent      8      16      32      64     128
--     raw       14.5    68.9     307    1305    5384
--     circle    1.97    3.03    3.28    3.28    3.28
--
-- So `∃ B, ∀ N, moment ≤ B` holds about the circle distance and fails about the raw index.
noncomputable def d2At (N : ℕ) (β : ℝ) : ℝ :=
  ∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2

/-- The substrate moment per unit squared aperture — `d2At` with the window factor `(2π/(N+1))²`
divided out. A bounded `d2At` is the special case; a bounded `substrateRatio` is the weakest
hypothesis the aperture argument consumes.

DERIVED: the `+ 1` is the periodic extent `N + 1` (the lag arity), and the exponent `2` squares it —
the aperture factor `(2π/(N+1))²` this quantity divides out, so that what remains carries no window.
Both come from `Moment.Read.thetaMoment_eq`. -/
noncomputable def substrateRatio (N : ℕ) (β : ℝ) : ℝ := d2At N β / ((N : ℝ) + 1) ^ 2

/-- The read's cosine average at aperture `N`, `∑ d, p d * cos (θ d)`. By
`confinement_at_iff_cosAvg` confinement at that aperture is equivalent to a lower bound on it. -/
noncomputable def cosAvgYMAt (N : ℕ) (β : ℝ) : ℝ :=
  ∑ d, (readYMAt N β).p d * Real.cos ((readYMAt N β).θ d)

/-- The C-3 model identification, by `rfl`: the read the file reasons about is reading-A of the
Wilson ensemble, since both sides are `readA (wilsonCorr β) _`. Reading-A is a concrete function and
both reads are built from the same ensemble correlation, so the identification holds definitionally.
The physical input is the named `wilson_reflection_positive_at`. -/
theorem readYM_is_wilson : readYM = readingA_wilson := rfl

/-- The centre-vortex tension read `μ(β) = -log⟨cos θ⟩_ρ = log(S(0)/S(2π/L))` [E], defined as the
min-entropy tension of the concrete correlation `readYM β` (`Moment.Read.tension`).

DERIVED: no numeral is introduced here — `tension` is `-log ⟨cos θ⟩_p`, defined in `Moment`. The
`0` and `2` above are a lag index and a section reference. -/
noncomputable def μYM (β : ℝ) : ℝ := (readYM β).tension
/-- The leading character ratio `r(x) = I₂(x)/I₁(x)` at an arbitrary Bessel argument, defined from
the modified-Bessel series (`Bessel.besselI`). The argument is a variable, so nothing downstream
depends on a particular value of it.

DERIVED: the orders `2` and `1` are the two leading characters of the group, and their ratio is what
the strong-coupling character expansion produces. Neither is a magnitude: they index the expansion. -/
noncomputable def rAt (x : ℝ) : ℝ := Bessel.besselI 2 x / Bessel.besselI 1 x

/-- The character ratio is positive at every positive argument. The modified Bessel `Iₙ(x) > 0` for
`x > 0` (every series term positive, `Bessel.besselI_pos`; the Watson 1944 fact, checked from the
elementary series), so `I₂/I₁ > 0`.

DERIVED: `0 < x` is the hypothesis and `0 < rAt x` the conclusion; both are sign conditions, and no
magnitude appears. -/
theorem rAt_pos {x : ℝ} (hx : 0 < x) : 0 < rAt x := Bessel.ratio_pos hx

/-- The Bessel argument at the strong-coupling threshold — one value of the variable `rAt` takes.
-- CHOSEN: `73/100` is the positive coupling scale (giving `r = I₂/I₁ ≈ 0.183` and `βc ≈ 0.75`,
-- consistent with the derived threshold `β² < ½ log 3`, i.e. `β < 0.74115…`, of
-- `Bessel.strong_coupling_below_threshold`). Only its positivity is ever used (`rArgYM_pos`), and
-- the threshold identity it feeds is proved at every positive argument (`βcAt_spec`), so this is an
-- instantiation rather than a premise. Changing it moves `βcYM` and no theorem. -/
noncomputable def rArgYM : ℝ := 73 / 100

/-- The Bessel argument is positive, by `norm_num` on `73 / 100`.

DERIVED: `0 < rArgYM` is a sign condition; the numerals of the value itself sit in `rArgYM`. -/
theorem rArgYM_pos : 0 < rArgYM := by unfold rArgYM; norm_num

/-- The character ratio at the pinned argument — the `rArgYM` instance of `rAt`. -/
noncomputable def rYM : ℝ := rAt rArgYM

/-- The character ratio is positive at the pinned argument — the `rArgYM` instance of `rAt_pos`.

DERIVED: `0 < rYM` is a sign condition and carries no magnitude. -/
theorem ym_ratio_pos : 0 < rYM := rAt_pos rArgYM_pos

/-- The entropy floor `κ₀ = ¼ log 3`, proved in `Floor.lean`.

DERIVED, both factors. `log 3` is the branching of a directed cube-path,
`Floor.directed_paths_card`. The `¼` is the reciprocal area per step: `CubeArea.boundary_card_eq`
proves the surface bounding a `k`-step path has exactly `4k+6` faces, and
`VortexCount.kappa0_is_the_surface_entropy_density` assembles the two into
`log(#surfaces)/area = k·log3/(4k+6) → ¼·log3`, which is this number. `4` and `3` are each the arity
of something the lattice already is. -/
noncomputable def κ₀YM : ℝ := 1 / 4 * Real.log 3

theorem κ₀YM_pos : 0 < κ₀YM := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold κ₀YM; linarith

/-! ### Confinement through a variable aperture

A bound on the substrate — its second moment about the circle distance, or that moment per unit
squared aperture — puts the tension below the entropy floor. Every statement below is an instance or
a limit of that implication, and none of them supplies a number. -/

/-- The pinned read is the `nCorrYM` instance of the aperture-general one. -/
theorem readYM_is_readYMAt : readYM = readYMAt nCorrYM := rfl

/-- The pinned tension is the `nCorrYM` instance of the aperture-general one. -/
theorem μYM_is_μYMAt : μYM = μYMAt nCorrYM := rfl

/-- Confinement at one aperture, from the read's own cosine average: if the average exceeds
`3 ^ (-(1 : ℝ) / 4)` then the tension is below the floor. Definitional, since `tension` is
`-log ⟨cos θ⟩_p`; stated because it is the form one measured scalar certifies.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is `e^{-κ₀}` at the floor `κ₀ = ¼log3` counted in `Floor`. No
magnitude is chosen. -/
theorem confinement_at_of_cosAvg {N : ℕ} {β : ℝ}
    (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgYMAt N β) : μYMAt N β < κ₀YM :=
  (readYMAt N β).tension_lt_floor_of_cosAvg hc

/-- The converse as well, so a tension below the floor and a cosine average above
`3 ^ (-(1 : ℝ) / 4)` are the same statement at one aperture. The positivity hypothesis is what a
nonpositive average cannot supply a logarithm for.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is `e^{-κ₀}` with `κ₀ = ¼log3`; `0 < cosAvgYMAt N β` is the domain of
the logarithm. -/
theorem confinement_at_iff_cosAvg {N : ℕ} {β : ℝ} (hpos : 0 < cosAvgYMAt N β) :
    μYMAt N β < κ₀YM ↔ (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgYMAt N β :=
  ⟨fun h => (readYMAt N β).cosAvg_gt_of_tension_lt_floor hpos h, confinement_at_of_cosAvg⟩

/-- `substrateRatio N β ≤ c` and `d2At N β ≤ c * ((N : ℝ) + 1) ^ 2` are the same hypothesis,
recorded as an iff so neither form reads as extra strength.

DERIVED: `((N : ℝ) + 1) ^ 2` is the periodic extent squared — the aperture factor `substrateRatio`
divides out, from `Moment.Read.thetaMoment_eq`. -/
theorem substrateRatio_le_iff {N : ℕ} {β c : ℝ} :
    substrateRatio N β ≤ c ↔ d2At N β ≤ c * ((N : ℝ) + 1) ^ 2 := by
  have hN : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
  rw [substrateRatio, div_le_iff₀ hN]

/-- `2 * (1 - Real.cos A) ≤ A ^ 2` on `[0, π]`, which is `sin x ≤ x` squared: `1 − cos A =
2sin²(A/2)` and `A² = 4(A/2)²`, so the claim is `sin(A/2) ≤ A/2` squared. No numerics, and no bound
on `A` beyond the half-turn that keeps the sine nonnegative.

At `A = arccos(3^{−1/4})` the left side is the origin-tangent threshold's numerator and the right
side is the sharp one's, which is what `taylor_le_substrateThreshold` uses.

DERIVED: `0 ≤ A` and `A ≤ Real.pi` are the half-turn the sine is nonnegative on; the `2` of
`2 * (1 - Real.cos A)` and the exponent `2` of `A ^ 2` are the double-angle identity's own, and the
`1` is the value of the cosine at zero. Nothing is chosen. -/
theorem two_one_sub_cos_le_sq {A : ℝ} (hA : 0 ≤ A) (hAπ : A ≤ Real.pi) :
    2 * (1 - Real.cos A) ≤ A ^ 2 := by
  have hhalf : 0 ≤ A / 2 := by linarith
  have hhalfπ : A / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hs : 0 ≤ Real.sin (A / 2) := Real.sin_nonneg_of_nonneg_of_le_pi hhalf hhalfπ
  have hle : Real.sin (A / 2) ≤ A / 2 := by
    rcases eq_or_lt_of_le hhalf with h | h
    · rw [← h, Real.sin_zero]
    · exact le_of_lt (Real.sin_lt h)
  -- `cos A = 1 − 2 sin²(A/2)`, from the double angle and the Pythagorean identity
  have hcos : Real.cos A = 1 - 2 * Real.sin (A / 2) ^ 2 := by
    have h2 : Real.cos (2 * (A / 2)) = 2 * Real.cos (A / 2) ^ 2 - 1 := Real.cos_two_mul _
    have hA2 : 2 * (A / 2) = A := by ring
    rw [hA2] at h2
    nlinarith [Real.sin_sq_add_cos_sq (A / 2)]
  rw [hcos]
  nlinarith [hs, hle]

#print axioms two_one_sub_cos_le_sq

/-- The sharp substrate threshold in closed form:

    substrateThreshold = arccos(3^{−1/4})² / (2π)²

`arccos` of the entropy floor, squared, over the window squared. `3^{−1/4} = e^{−κ₀}` with
`κ₀ = ¼log3` counted in `Floor`, and `(2π)²` is the window.

DERIVED: `3` and the exponent `−1/4` are `κ₀ = ¼log3` read as `e^{−κ₀}`, counted in `Floor` off
directed cube paths; `2` and `π` are the lag angle `θ_d = 2π·circLag d/(N+1)` the read is taken
through; the outer exponent `2` is the second moment's own. `1` is the numerator of that exponent.
This is `sharp_constant_pos` solved for `c`. -/
noncomputable def substrateThreshold : ℝ :=
  Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / (2 * Real.pi) ^ 2

/-- The sharp confinement criterion:

    substrateRatio N β < substrateThreshold   ⟹   μYMAt N β < κ₀YM

`confinement_at_of_ratio` reaches the same conclusion through `1 − x²/2 ≤ cos x`, whose threshold is
`2(1 − 3^{−1/4})/(2π)² ≈ 0.0121669` — the tangent to `t ↦ cos √t` at the origin, exact only for a
read concentrated at zero lag. This one takes the tangent at the threshold itself
(`Sharp.cos_avg_ge_tangent` with `A = arccos(3^{−1/4})`), where it is exact, and gives
`arccos(3^{−1/4})²/(2π)² ≈ 0.0126877` — about 4.3% more room. It is sharp: equality holds for the
point mass at `θ = A`, so no argument reading the correlation only through its second moment can do
better.

Measured scope. Against `data/9_3_dat_substrate_of_aperture.csv` the ratio `d2_circle / L²` clears
the threshold by 30× in 16 of 43 rows, and the thinnest margin is 1.98× (SU(3), β = 5.50, L = 6); at
L = 8 the SU(2) crossover rows sit near 4.7×. The margin is aperture-dependent by construction —
the ratio divides the moment by `L²` — so no single multiple describes the table. The read there is
spatial: `per_config_profiles` rolls axes 1–3 with period `L`, so the aperture is `L`, not `T`.

The criterion's constant is fixed by the entropy floor and the window between them. -/
theorem confinement_at_of_substrate_sharp {N : ℕ} {β : ℝ}
    (h : substrateRatio N β < substrateThreshold) : μYMAt N β < κ₀YM := by
  unfold substrateThreshold at h
  set f : ℝ := (3 : ℝ) ^ (-(1 : ℝ) / 4) with hfdef
  have hfpos : 0 < f := Real.rpow_pos_of_pos (by norm_num) _
  have hf1 : f < 1 := by
    rw [hfdef]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  set A : ℝ := Real.arccos f with hAdef
  have hA : 0 < A := Real.arccos_pos.mpr hf1
  have hAπ : A < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hcosA : Real.cos A = f := Real.cos_arccos (by linarith) (le_of_lt hf1)
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  -- the threshold says exactly `(2π)²·substrateRatio < A²`
  have hmom : (2 * Real.pi) ^ 2 * substrateRatio N β < A ^ 2 := by
    rw [lt_div_iff₀ hpi] at h; linarith
  -- the aperture cancels exactly, as in `surplus_ge`
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcancel : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2
        * (∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2)
      = (2 * Real.pi) ^ 2 * substrateRatio N β := by
    unfold substrateRatio d2At
    field_simp
  have hge := Sharp.cos_avg_ge_tangent (readYMAt N β) hA hAπ
  rw [hcancel] at hge
  have hlam : 0 < Real.sin A / (2 * A) := by
    have hs : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA hAπ
    positivity
  have hgap : 0 < (Real.sin A / (2 * A)) * (A ^ 2 - (2 * Real.pi) ^ 2 * substrateRatio N β) :=
    mul_pos hlam (by linarith)
  refine confinement_at_of_cosAvg ?_
  show f < cosAvgYMAt N β
  unfold cosAvgYMAt
  rw [← hcosA]
  linarith

#print axioms confinement_at_of_substrate_sharp

/-- The origin-tangent threshold never exceeds the sharp one:

    2(1 − 3^{−1/4}) / (2π)²  ≤  substrateThreshold

`confinement_at_of_ratio` asks for `(2π)²c/2 < 1 − 3^{−1/4}`, i.e. `c` under the left-hand side;
`confinement_at_of_substrate_sharp` asks for `c < substrateThreshold`. So the first condition implies
the second, and `confinement_at_of_ratio` below is that derivation.

No numerics enter: put `A = arccos(3^{−1/4})`, so `cos A = 3^{−1/4}`, and it is
`two_one_sub_cos_le_sq`.

DERIVED: `2 * (1 - 3 ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2` is the origin tangent's own threshold —
`3 ^ (-(1 : ℝ) / 4)` is `e^{-κ₀}`, the `2` in the numerator is the denominator of `1 − x²/2` cleared,
and `(2π)²` is the window squared. -/
theorem taylor_le_substrateThreshold :
    2 * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2 ≤ substrateThreshold := by
  have h0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hcos : Real.cos (Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4))) = (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    Real.cos_arccos (by linarith) (le_of_lt h1)
  have hkey := two_one_sub_cos_le_sq (Real.arccos_nonneg ((3 : ℝ) ^ (-(1 : ℝ) / 4)))
    (Real.arccos_le_pi ((3 : ℝ) ^ (-(1 : ℝ) / 4)))
  rw [hcos] at hkey
  unfold substrateThreshold
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  exact div_le_div_of_nonneg_right hkey hpi.le

#print axioms taylor_le_substrateThreshold

/-- Confinement at one aperture and one coupling from the substrate ratio, a corollary of the sharp
criterion. The aperture cancels, so the hypothesis on `c` carries no aperture and the conclusion
holds at every `N` for which the ratio bound does.

This form asks for `(2π)²c/2 < 1 − 3^{−1/4}`, i.e. `c` under `2(1 − 3^{−1/4})/(2π)²`, the tangent to
`t ↦ cos √t` at the origin. `taylor_le_substrateThreshold` puts that threshold under
`substrateThreshold`, so this follows from `confinement_at_of_substrate_sharp`.

DERIVED: `(2 * Real.pi) ^ 2 * c / 2` is the window factor times the ratio, halved by the cosine
bound's own denominator, and `3 ^ (-(1 : ℝ) / 4)` is `e^{-κ₀}` at the floor `κ₀ = ¼log3`. -/
theorem confinement_at_of_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    {N : ℕ} {β : ℝ} (h : substrateRatio N β ≤ c) :
    μYMAt N β < κ₀YM := by
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hct : c < 2 * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2 := by
    rw [lt_div_iff₀ hpi]; linarith
  exact confinement_at_of_substrate_sharp
    (lt_of_le_of_lt h (lt_of_lt_of_le hct taylor_le_substrateThreshold))

/-- The same at a fixed coupling, eventually in the aperture: if the ratio bound holds for all large
`N`, so does `μYMAt N β < κ₀YM`.

DERIVED: `(2 * Real.pi) ^ 2 * c / 2` and `3 ^ (-(1 : ℝ) / 4)` are `confinement_at_of_ratio`'s own
threshold condition, carried through unchanged. -/
theorem confinement_at_coupling_of_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) (β : ℝ)
    (h : ∀ᶠ N : ℕ in Filter.atTop, substrateRatio N β ≤ c) :
    ∀ᶠ N : ℕ in Filter.atTop, μYMAt N β < κ₀YM := by
  filter_upwards [h] with N hN
  exact confinement_at_of_ratio hc hN

/-- Confinement from a moment allowed to grow with the aperture. The substrate moment need not be
bounded — it may grow like `c·(N+1)²` — provided the constant `c` clears the floor gap. A bounded
moment is the special case.

DERIVED: `(2 * Real.pi) ^ 2 * c / 2 < 1 - 3 ^ (-(1 : ℝ) / 4)` is `confinement_at_of_ratio`'s
threshold condition, and `c * ((N : ℝ) + 1) ^ 2` is the growth allowance in the extent squared. -/
theorem confinement_of_growth_bound {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, d2At N β ≤ c * ((N : ℝ) + 1) ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  filter_upwards [h] with N hN β
  exact confinement_at_of_ratio hc (substrateRatio_le_iff.mpr (hN β))

/-- The same hypothesis stated in `substrateRatio` rather than in `d2At`, the two being
interchanged by `substrateRatio_le_iff`.

DERIVED: `(2 * Real.pi) ^ 2 * c / 2 < 1 - 3 ^ (-(1 : ℝ) / 4)` is `confinement_at_of_ratio`'s
threshold condition, carried through. -/
theorem confinement_of_growth_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, substrateRatio N β ≤ c) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  filter_upwards [h] with N hN β
  exact confinement_at_of_ratio hc (hN β)

/-- Confinement at every large enough aperture, from one substrate bound:

    (∀ N β, d2At N β ≤ B)  ⟹  ∀ᶠ N, ∀ β, μYMAt N β < κ₀YM

No numeral appears in the statement. `B` is supplied by the caller and never named; the aperture
threshold is not given — `∀ᶠ N in atTop` says only that one exists, and it is determined from `B`
alone by `Moment.aperture_factor_tendsto_zero`. `κ₀YM = ¼log3` is derived in `Floor`, per-area, with
no aperture in it.

The hypothesis says the lag moment is bounded independently of the window. The moment is taken about
the circle distance (see `d2At`): about the raw index no physical correlation is bounded at every
aperture. -/
theorem confinement_of_substrate_bound {B : ℝ} (hB : ∀ N β, d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  filter_upwards [hev] with N hN β
  exact (readYMAt N β).tension_lt_floor_of_circ_moment (hB N β) hN

/-- The same with the bound existentially quantified: the hypothesis is that the substrate has an
aperture-independent moment, with no value supplied for it anywhere. -/
theorem confinement_of_bounded_substrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  obtain ⟨B, hB⟩ := h
  exact confinement_of_substrate_bound hB

/-- Confinement from one decay rate:

    (∀ N β d, p d ≤ C·r^{circLag d})  with  r < 1   ⟹   ∀ᶠ N, ∀ β, μYMAt N β < κ₀YM

The hypothesis is a rate rather than a family of aperture-indexed bounds. The aperture-uniformity
that `confinement_of_substrate_bound` demands comes from
`Moment.circ_moment_le_of_geometric`: the bound it produces, `2C·∑' k, k²rᵏ`, is a convergent series
with no `N` in it.

Under reflection positivity the connected correlation has the transfer-matrix form `ρ(d) = ∑ₙ wₙλₙᵈ`
with `wₙ ≥ 0` — the half-line shape, which on this periodic lattice is degenerate under the proved
`ρ(d) = ρ(n−d)` symmetry (`MomentShape.wilsonCorrAt_neg`, feeding `Spectral.flat_of_aperiodic`).
`Spectral.PeriodicSpectralForm` carries the shape a transfer matrix on a circle gives, and a
transfer gap `Δ` puts every excited `λₙ ≤ e^{−Δ}`, so `ZeroMode.exists_exponential_decay` delivers
this hypothesis with `r = e^{−Δ}`. The decay is in the circle distance rather than the raw lag
because the correlation on a periodic extent satisfies `ρ(d) = ρ(N+1−d)`.

DERIVED: `0 ≤ C`, `0 ≤ r` and `r < 1` are the sign and contraction conditions
`Moment.circ_moment_le_of_geometric` requires, and the `1` in `Fin (N + 1)` is the lag arity of a
window of size `N`. None is chosen here. -/
theorem confinement_of_geometric_decay {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (readYMAt N β).p d ≤ C * r ^ (Moment.circLag d)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  refine confinement_of_substrate_bound (B := 2 * C * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k) ?_
  intro N β
  exact Moment.circ_moment_le_of_geometric (readYMAt N β) hC hr0 hr1 (hdecay N β)

#print axioms confinement_of_geometric_decay

/-- The same with the decay in the raw lag, the form reflection positivity produces: a `τ`-th power
of the transfer operator is a `τ`-th power of each eigenvalue, so `ρ(d) = ∑ₙ wₙλₙᵈ ≤ (∑ₙwₙ)·rᵈ` with
`r` the largest excited eigenvalue (`ZeroMode.le_geometric_of_lt_one`,
`ZeroMode.exists_exponential_decay`).

`Moment.circ_decay_of_lag_decay` converts to the circle distance the aperture argument consumes. The
conversion runs one way only, because `r < 1` makes the smaller exponent the weaker bound, so the
two forms are stated separately.

DERIVED: `0 ≤ C`, `0 ≤ r` and `r < 1` are inherited from `confinement_of_geometric_decay`, and the
`1` in `Fin (N + 1)` is the lag arity. -/
theorem confinement_of_lag_decay {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (readYMAt N β).p d ≤ C * r ^ (d : ℕ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM :=
  confinement_of_geometric_decay hC hr0 hr1
    (fun N β => Moment.circ_decay_of_lag_decay (readYMAt N β) hC hr0 hr1.le (hdecay N β))

#print axioms confinement_of_lag_decay

/-! ### The same chain on a set of couplings

`confinement_of_lag_decay` asks for one `r < 1` at every coupling. Under reflection positivity
`r = e^{−Δ}` with `Δ` the gap in lattice units, which runs with the coupling and tends to zero in the
continuum limit; neighbouring statements in this tree show that a decay factor moving with the
coupling admits no uniform constant (`LogDerivNoGo.no_uniform_bound_on_torus_profile`,
`FreeFieldLagTwo.flat_profile_meets_every_uniform_fact`,
`FlatProfileAllApertures.flat_profile_defeats_the_criterion_at_every_even_aperture`).

`ym_A1_of_grid` splits `β` into three regions and needs a constant only on each. The three
statements below are the confinement chain on an arbitrary set `S` of couplings.

The proofs are the `β`-uniform ones verbatim: `confinement_of_substrate_bound`'s aperture condition
contains no `β`, and `β` is introduced after `filter_upwards` and used only to instantiate the
hypothesis. At `S = Set.univ` these recover the originals. -/

/-- Confinement from a substrate bound holding on a set `S` of couplings.

DERIVED: the `2`s and the `4` are `confinement_of_substrate_bound`'s own — the aperture factor
`(2π/(N+1))²/2` and the floor `3^{−1/4}`. Nothing new is chosen. -/
theorem confinement_on_of_substrate_bound {B : ℝ} {S : Set ℝ}
    (hB : ∀ N, ∀ β ∈ S, d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β ∈ S, μYMAt N β < κ₀YM := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  filter_upwards [hev] with N hN β hβ
  exact (readYMAt N β).tension_lt_floor_of_circ_moment (hB N β hβ) hN

#print axioms confinement_on_of_substrate_bound

/-- Confinement from a geometric rate in the circle distance, holding on a set `S` of couplings.

DERIVED: the `2` in the bound `2C·∑ k²rᵏ` is `Moment.circ_moment_le_of_geometric`'s, from the
two sides of the circle, and the `2` in `k²` is that same lemma's circular lag. `0` is the sign of
`C` and of `r`, both required by the lemma being applied. `1` is the contraction threshold `r` must
sit below, and the `1` in `Fin (N + 1)` is the aperture's own offset — `readYMAt N β` reads `N + 1`
lags. Every one of them is inherited; none is chosen here. -/
theorem confinement_on_of_geometric_decay {C r : ℝ} {S : Set ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r)
    (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ), ∀ β ∈ S, ∀ d : Fin (N + 1),
      (readYMAt N β).p d ≤ C * r ^ (Moment.circLag d)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β ∈ S, μYMAt N β < κ₀YM :=
  confinement_on_of_substrate_bound (B := 2 * C * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k)
    (fun N β hβ => Moment.circ_moment_le_of_geometric (readYMAt N β) hC hr0 hr1 (hdecay N β hβ))

#print axioms confinement_on_of_geometric_decay

/-- Confinement from a raw-lag rate holding on a set `S` of couplings. The `β`-uniform sibling
`confinement_of_lag_decay` asks for one `r < 1` at every coupling; this one asks for a constant on
`S` alone.

Scope: the conclusion is `∀ᶠ N in atTop`, at all sufficiently large apertures, so it does not supply
`ym_A1_of_grid`'s `hinterior`, which is `∀ β ∈ Icc βloYM bhi, μYM β < κ₀YM` at the single pinned
aperture — `μYM_is_μYMAt` gives `μYM = μYMAt nCorrYM` by `rfl` with `nCorrYM = 16`, and an eventual
statement does not deliver that one value. `hinterior` is supplied by
`ym_crossover_confinement_of_grid`, from a Lipschitz constant, the aperture condition at `nCorrYM`,
and a finite grid of measured moments.

DERIVED: no numeral of its own. `1` is the contraction threshold `r` must sit below, which
`Moment.circ_decay_of_lag_decay` requires; the `1` in `Fin (N + 1)` is the aperture's offset, since
`readYMAt N β` reads `N + 1` lags. `0` is the sign of `C` and of `r`, both demanded by the same
lemma. All four are inherited. -/
theorem confinement_on_of_lag_decay {C r : ℝ} {S : Set ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ), ∀ β ∈ S, ∀ d : Fin (N + 1),
      (readYMAt N β).p d ≤ C * r ^ (d : ℕ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β ∈ S, μYMAt N β < κ₀YM :=
  confinement_on_of_geometric_decay hC hr0 hr1
    (fun N β hβ => Moment.circ_decay_of_lag_decay (readYMAt N β) hC hr0 hr1.le (hdecay N β hβ))

#print axioms confinement_on_of_lag_decay


/-- Confinement from a positive-weight spectral representation. If the read's weights have the
transfer form `p d = ∑ₖ wₖ λₖᵈ` with `wₖ ≥ 0`, every `λₖ ≤ r < 1`, and total weight bounded by `C`
uniformly in the aperture and the coupling, then the tension is below the floor at every large
enough aperture and every coupling.

Osterwalder–Seiler gives the self-adjoint transfer operator and the nonnegativity of the weights
`wₖ = |⟨v,eₖ⟩|²`, which is the content of `wₖ ≥ 0`. A spectral gap `Δ` is `λₖ ≤ e^{−Δ} < 1` on the
excited modes, so `r = e^{−Δ}`. The gap itself is the caller's to supply.

The steps between the hypothesis and the conclusion are proved here: the geometric bound
(`ZeroMode.le_geometric_of_lt_one`), the conversion to the circle distance
(`Moment.circ_decay_of_lag_decay`), the aperture-uniform moment bound
(`Moment.circ_moment_le_of_geometric`), the entropy-floor comparison, and the model assembly. The
footprint is the foundational three plus `wilson_reflection_positive_at`.

A geometric rate is strictly stronger than the bounded moment `ym_mass_gap_of_substrate` consumes:
`Substrate.bounded_moment_does_not_give_geometric_decay` exhibits a family of reads (contact weight
`1` plus a far atom of weight `(k+1)⁻³` at the antipode) whose circle moment is `1/(k+1) ≤ 1` at
every aperture, so it satisfies `confinement_of_bounded_substrate`'s hypothesis with `B = 1`, while
no geometric `C·rᵈ` bounds it.

DERIVED: `0 ≤ C`, `0 ≤ w`, `0 ≤ lam`, `0 ≤ r` are sign conditions, `r < 1` the contraction, and the
`1` in `Fin (N + 1)` the lag arity. All are `ZeroMode.le_geometric_of_lt_one`'s and
`confinement_of_lag_decay`'s own. -/
theorem confinement_of_spectral_form {ι : Type*} [DecidableEq ι] {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (s : ℕ → ℝ → Finset ι) (w lam : ℕ → ℝ → ι → ℝ)
    (hw : ∀ N β, ∀ k ∈ s N β, 0 ≤ w N β k)
    (hlam0 : ∀ N β, ∀ k ∈ s N β, 0 ≤ lam N β k)
    (hlamr : ∀ N β, ∀ k ∈ s N β, lam N β k ≤ r)
    (hwsum : ∀ N β, ∑ k ∈ s N β, w N β k ≤ C)
    (hrep : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (readYMAt N β).p d = ∑ k ∈ s N β, w N β k * lam N β k ^ (d : ℕ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  refine confinement_of_lag_decay hC hr0 hr1 ?_
  intro N β d
  rw [hrep N β d]
  refine le_trans (ZeroMode.le_geometric_of_lt_one (s N β) (w N β) (lam N β) r
    (hw N β) (hlam0 N β) (hlamr N β) (d : ℕ)) ?_
  exact mul_le_mul_of_nonneg_right (hwsum N β) (pow_nonneg hr0 _)

#print axioms confinement_of_spectral_form

/-! ### The half-line spectral form and the periodic one

`confinement_of_spectral_form` just above takes `hrep : (readYMAt N β).p d = ∑ w λ^d`, the half-line
shape. On this lattice that shape forces a flat correlator:

* `WilsonHypercubic.Site` is `Fin d → Fin n` and `shift` adds in `Fin n`, so the lattice is a periodic
  torus with `n = N+1`, and `wilsonCorrAt N β`'s lag index `Fin (N+1)` spans the whole period;
* `ρ(d) = ρ(n−d)` is proved, by `MomentShape.corrHyper_neg` and its corollaries `corrClay_neg` and
  `wilsonCorrAt_neg`, at every extent and every real coupling with no hypothesis. The useful form is
  `MomentShape.wilsonCorrAt_circLag_congr`: the correlation reads the lag only through
  `Moment.circLag`. The route is `LogConvex.EW_plaqE_pair_shift` (translation invariance of the
  two-plaquette expectation, itself derived from the reflection) at `P = 0`, plus the
  lag-independence of the one-point term (`ReflectPositive.EW_plaqE_lag`). `ZeroMode`'s "symmetric
  under `d ↦ n − d`" is a different statement: it is about `clag`, the lag function, where it is
  arithmetic, not about `ρ`;
* with that symmetry, `Spectral.flat_of_aperiodic` makes a half-line shape force `ρ` flat from lag
  one, unconditionally. It assumes `1 ≤ d`, so `ρ(0)` is unconstrained and a contact term at lag
  zero survives it. Nothing in the tree evaluates `wilsonCorrAt` at any lag, and the reflection-
  positivity axiom is satisfied by a constant positive `ρ`.

`Spectral.PeriodicSpectralForm` carries the shape a transfer matrix on a circle gives,
`ρ(d) = ∑ w (λ^d + λ^{n−d})`, and `Spectral.periodic_decay_le_circLag` turns a gap on its spectrum
into decay at `Moment.circLag`, which is what `confinement_of_geometric_decay` consumes. -/

/-- A gap on the transfer spectrum gives confinement. Given the periodic spectral form for the
Wilson correlation at every aperture, with every contributing `λ` below a common `r < 1` and the
weights controlled relative to the total mass, the tension sits below the floor eventually in the
aperture.

The gap hypothesis `hlamr` is restricted to modes of nonzero weight, and that restriction is
required: `Transfer.one_le_of_eigenvalues_le` proves that a bound on every transfer eigenvalue
forces that bound to be at least one, since the vacuum sits at eigenvalue exactly one with weight
`‖Ω‖²`, so `1 = ∑ wᵢλᵢ ≤ r∑wᵢ = r`. Only normalisation is used there. The connected correlator is
the case where the vacuum weight vanishes, the disconnected part being the vacuum contribution.

A spectral gap therefore delivers confinement through the substrate moment; both the periodic form
`S` and the gap `hlamr` are hypotheses here.

DERIVED: `0 ≤ C`, `0 ≤ r` and `r < 1` are `confinement_of_geometric_decay`'s sign and contraction
conditions; `(S N β).w k ≠ 0` selects the contributing modes; the `2` in `2 * (∑ k, (S N β).w k)`
is the two sides of the circle in `Spectral.periodic_decay_le_circLag`; and `N + 1` is the period. -/
theorem confinement_of_periodic_spectral_form {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (S : ∀ (N : ℕ) (β : ℝ), Spectral.PeriodicSpectralForm (N + 1) (wilsonCorrAt N β))
    (hlamr : ∀ (N : ℕ) (β : ℝ) (k : (S N β).Idx), (S N β).w k ≠ 0 → (S N β).lam k ≤ r)
    (hCbound : ∀ (N : ℕ) (β : ℝ),
      2 * (∑ k, (S N β).w k) ≤ C * (∑ d, wilsonCorrAt N β d)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  refine confinement_of_geometric_decay hC hr0 hr1 ?_
  intro N β d
  -- The total mass is positive without the reflection-positivity axiom: the hypothesis `S` already
  -- carries nonnegative transfer weights, so `Spectral.rho_nonneg` gives every lag, and
  -- `PlaqVariance.corrClay_zero_pos` — the plaquette-energy variance, foundational-only — gives the
  -- lag-zero term strictly. DERIVED: the index `0` is the lag the variance sits at; no value.
  have hnn : ∀ d' : Fin (N + 1), 0 ≤ wilsonCorrAt N β d' := fun d' => Spectral.rho_nonneg (S N β) d'
  have h0 : 0 < wilsonCorrAt N β 0 := PlaqVariance.corrClay_zero_pos N β
  have hpos : 0 < ∑ d', wilsonCorrAt N β d' :=
    ReflectPositive.sum_pos_of_head_pos _ hnn h0
  have hrho := Spectral.periodic_decay_le_circLag (S N β) (hlamr N β) hr0 d
  show wilsonCorrAt N β d / (∑ d', wilsonCorrAt N β d') ≤ C * r ^ (Moment.circLag d)
  rw [div_le_iff₀ hpos]
  calc wilsonCorrAt N β d
      ≤ 2 * (∑ k, (S N β).w k) * r ^ (Moment.circLag d) := hrho
    _ ≤ (C * (∑ d', wilsonCorrAt N β d')) * r ^ (Moment.circLag d) :=
        mul_le_mul_of_nonneg_right (hCbound N β) (pow_nonneg hr0 _)
    _ = C * r ^ (Moment.circLag d) * (∑ d', wilsonCorrAt N β d') := by ring

#print axioms confinement_of_periodic_spectral_form

/-- The surplus bound, pointwise in the read:

    κ₀ + log(1 − (2π)²·substrateRatio N β / 2)  ≤  κ₀ − μYMAt N β

No threshold and no comparison constant appears. The right-hand side is the entropy surplus at
aperture `N` and coupling `β`; the left-hand side is built from `κ₀ = ¼log3` (derived in `Floor`,
per-area, by counting `3^k` directed cube paths), the window `2π`, and `substrateRatio N β` itself
rather than a bound on it.

`surplus_ge_of_ratio` takes a hypothesis `substrateRatio N β ≤ c` and asks `(2π)²c/2 < 1 − 3^{−1/4}`.
That inequality is the condition for the left-hand side here to be positive — the zero-crossing of
the logarithm, solved for `c` — and `0.012167` is recovered by solving
`κ₀ + log(1 − (2π)²c/2) = 0`.

The one hypothesis is that the logarithm has an argument, `(2π)²·substrateRatio/2 < 1`, which is a
domain condition.

DERIVED: `(2 * Real.pi) ^ 2` is the window squared, from `Moment.Read.thetaMoment_eq`, and the
division by `2` is the denominator of the cosine bound `1 − x²/2 ≤ cos x`. The `1` is that bound's
own constant term. -/
theorem surplus_ge (N : ℕ) (β : ℝ)
    (hdom : (2 * Real.pi) ^ 2 * substrateRatio N β / 2 < 1) :
    κ₀YM + Real.log (1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2) ≤ κ₀YM - μYMAt N β := by
  have hA : (0 : ℝ) < 1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2 := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- the aperture cancels exactly: no inequality is spent here, because the ratio is the read itself
  have hcancel : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2
        * (∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2) / 2
      = (2 * Real.pi) ^ 2 * substrateRatio N β / 2 := by
    unfold substrateRatio d2At
    field_simp
  have hcos : 1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2 ≤ cosAvgYMAt N β := by
    rw [← hcancel]; exact (readYMAt N β).cos_avg_ge_circ
  have htens : μYMAt N β ≤ -Real.log (1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2) := by
    have hlog := Real.log_le_log hA hcos
    show -Real.log (cosAvgYMAt N β) ≤ _
    linarith
  linarith

#print axioms surplus_ge

/-- The same bound divided by the spacing. On a screen of fixed physical extent `L = (N+1)·a` the
spacing is `a = L/(N+1)` and the physical surplus is `(κ₀ − μ)/a`, bounded below by a quantity built
from the read alone:

    ((N+1)/L) · (κ₀ + log(1 − (2π)²·substrateRatio N β / 2))  ≤  (κ₀ − μYMAt N β) / (L/(N+1))

Every symbol on the left is measured (`substrateRatio N β`), derived (`κ₀ = ¼log3`), the window
(`2π`), or the screen (`L`).

`ym_physical_gap_of_ratio` reaches `κ/L` from `substrateRatio ≤ c` with `c < 2(1−3^{−1/4})/(2π)²` and
names `κ` separately. Here the rate is read off instead, and it is positive exactly when
`substrateRatio N β < 2(1−3^{−1/4})/(2π)²` (`surplus_pos_iff_substrate`).

DERIVED: `0 < L` is the screen's positivity, `(2 * Real.pi) ^ 2` the window squared, the division by
`2` the denominator of `1 − x²/2 ≤ cos x`, and the `1`s are that bound's constant term and the
extent offset `(N : ℝ) + 1`. -/
theorem ym_physical_gap_ge (N : ℕ) (β L : ℝ) (hL : 0 < L)
    (hdom : (2 * Real.pi) ^ 2 * substrateRatio N β / 2 < 1) :
    (((N : ℝ) + 1) / L)
        * (κ₀YM + Real.log (1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2))
      ≤ (κ₀YM - μYMAt N β) / (L / ((N : ℝ) + 1)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hrewrite : (κ₀YM - μYMAt N β) / (L / ((N : ℝ) + 1))
      = (((N : ℝ) + 1) / L) * (κ₀YM - μYMAt N β) := by
    field_simp
  rw [hrewrite]
  refine mul_le_mul_of_nonneg_left (surplus_ge N β hdom) ?_
  positivity

#print axioms ym_physical_gap_ge

/-- The bound `ym_physical_gap_ge` gives is positive exactly when

    substrateRatio N β  <  2 · (1 − 3^{−1/4}) / (2π)²

and this is an iff. The decimal `0.012167…` that `surplus_ge_of_ratio` carries as a hypothesis is the
right-hand side: the zero of `κ₀ + log(1 − (2π)²x/2)`, solved for `x`.

DERIVED: `3 ^ (-(1 : ℝ) / 4) = e^{−κ₀}` with `κ₀ = ¼log3` derived in `Floor` by counting directed
cube paths; `(2 * Real.pi) ^ 2` is the window `Moment.Read.thetaMoment_eq` produces; the division by
`2` is the denominator of the cosine bound `1 − x²/2 ≤ cos x`; `0` is the sign the surplus is
compared against. The decimal appears in this file only inside this comment. -/
theorem surplus_pos_iff_substrate (N : ℕ) (β : ℝ)
    (hdom : (2 * Real.pi) ^ 2 * substrateRatio N β / 2 < 1) :
    0 < κ₀YM + Real.log (1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2)
      ↔ substrateRatio N β < 2 * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2 := by
  have hA : (0 : ℝ) < 1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2 := by linarith
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hval : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -κ₀YM := by
    rw [Real.log_rpow (by norm_num)]; unfold κ₀YM; ring
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  constructor
  · intro h
    -- κ₀ + log(1 − y) > 0  ⟹  1 − y > e^{−κ₀} = 3^{−1/4}
    have hlog : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4))
        < Real.log (1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2) := by
      rw [hval]; linarith
    have := (Real.log_lt_log_iff h3pos hA).mp hlog
    rw [lt_div_iff₀ hpi]
    linarith
  · intro h
    have hlt : (2 * Real.pi) ^ 2 * substrateRatio N β / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
      rw [lt_div_iff₀ hpi] at h; linarith
    have hstep : (3 : ℝ) ^ (-(1 : ℝ) / 4)
        < 1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2 := by linarith
    have := (Real.log_lt_log_iff h3pos hA).mpr hstep
    rw [hval] at this
    linarith

#print axioms surplus_pos_iff_substrate

/-- The sharp surplus bound:

    κ₀ + log cos(2π·√substrateRatio N β)  ≤  κ₀ − μYMAt N β

`surplus_ge` bounds the same surplus by `κ₀ + log(1 − (2π)²·substrateRatio/2)`, through the tangent
to `t ↦ cos √t` at the origin. This takes the tangent at the read's own root-mean-square angle, where
the correction term vanishes identically (`Sharp.cos_avg_ge_cos_rms`); it is Jensen's inequality for
that convex function.

Equality holds for the point mass at `θ = 2π√substrateRatio`, so no argument reading the correlation
only through its second moment improves it. Every constant in the chain from the read to the surplus
is `κ₀ = ¼log3`, the window `2π`, or the ratio itself.

The two hypotheses are the domain of the logarithm: the ratio is nonnegative, and the rms angle
stays inside the quarter-turn where the cosine is positive.

DERIVED: `0 ≤ substrateRatio N β` is a sign condition (`substrateRatio_nonneg` proves it
unconditionally), `(2 * Real.pi) ^ 2` is the window squared, and `(Real.pi / 2) ^ 2` is the
quarter-turn squared, which is where `Real.cos` is positive. -/
theorem surplus_ge_sharp (N : ℕ) (β : ℝ)
    (hpos : 0 ≤ substrateRatio N β)
    (hdom : (2 * Real.pi) ^ 2 * substrateRatio N β < (Real.pi / 2) ^ 2) :
    κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * substrateRatio N β)))
      ≤ κ₀YM - μYMAt N β := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcancel : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2
        * (∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2)
      = (2 * Real.pi) ^ 2 * substrateRatio N β := by
    unfold substrateRatio d2At
    field_simp
  have hm0 : 0 ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2
      * (∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2) := by
    rw [hcancel]; exact mul_nonneg (by positivity) hpos
  have hmπ : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2
      * (∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2) < Real.pi ^ 2 := by
    rw [hcancel]; nlinarith
  have hge := Sharp.cos_avg_ge_cos_rms (readYMAt N β) hm0 hmπ
  rw [hcancel] at hge
  -- the rms angle is inside the quarter-turn, so the cosine there is positive
  set A : ℝ := Real.sqrt ((2 * Real.pi) ^ 2 * substrateRatio N β) with hAdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hAlt : A < Real.pi / 2 := by
    have hstep : A < Real.sqrt ((Real.pi / 2) ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) hdom
    rwa [Real.sqrt_sq (by positivity)] at hstep
  have hcosA : 0 < Real.cos A :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hAlt⟩
  have htens : μYMAt N β ≤ -Real.log (Real.cos A) := by
    have hlog := Real.log_le_log hcosA hge
    show -Real.log (cosAvgYMAt N β) ≤ _
    unfold cosAvgYMAt
    linarith
  linarith

#print axioms surplus_ge_sharp

/-- The same on a screen of fixed physical extent `L = (N+1)·a`, with `a = L/(N+1)`:

    ((N+1)/L) · (κ₀ + log cos(2π·√substrateRatio N β))  ≤  (κ₀ − μYMAt N β) / a

This is `ym_physical_gap_ge` with the sharp surplus in place of the origin-tangent one. `κ₀ = ¼log3`
is counted in `Floor`, `2π` is the window, `L` is the screen, and `substrateRatio N β` is the read.

DERIVED: `0 < L` and `0 ≤ substrateRatio N β` are sign conditions, `(2 * Real.pi) ^ 2` is the window
squared, `(Real.pi / 2) ^ 2` the quarter-turn squared, and the `1` is the extent offset
`(N : ℝ) + 1`. -/
theorem ym_physical_gap_ge_sharp (N : ℕ) (β L : ℝ) (hL : 0 < L)
    (hpos : 0 ≤ substrateRatio N β)
    (hdom : (2 * Real.pi) ^ 2 * substrateRatio N β < (Real.pi / 2) ^ 2) :
    (((N : ℝ) + 1) / L)
        * (κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * substrateRatio N β))))
      ≤ (κ₀YM - μYMAt N β) / (L / ((N : ℝ) + 1)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hrewrite : (κ₀YM - μYMAt N β) / (L / ((N : ℝ) + 1))
      = (((N : ℝ) + 1) / L) * (κ₀YM - μYMAt N β) := by
    field_simp
  rw [hrewrite]
  refine mul_le_mul_of_nonneg_left (surplus_ge_sharp N β hpos hdom) ?_
  positivity

#print axioms ym_physical_gap_ge_sharp

/-- The substrate ratio is nonnegative: a probability weight against a square, divided by a positive
extent. A fact about the read, not a hypothesis.

DERIVED: `0 ≤ substrateRatio N β` is the conclusion and the only numeral in the statement. -/
theorem substrateRatio_nonneg (N : ℕ) (β : ℝ) : 0 ≤ substrateRatio N β := by
  unfold substrateRatio d2At
  refine div_nonneg (Finset.sum_nonneg (fun d _ => ?_)) (by positivity)
  exact mul_nonneg ((readYMAt N β).p_nonneg d) (sq_nonneg _)

#print axioms substrateRatio_nonneg

/-- The sharp surplus at `c` is positive below the sharp threshold:
`κ₀ + log cos(2π√c) > 0 ⟺ cos(2π√c) > 3^{−1/4} ⟺ 2π√c < arccos(3^{−1/4}) ⟺ c < substrateThreshold`.
So `substrateThreshold` is the bound's zero, solved for `c`, rather than a separate condition
imposed on it.

DERIVED: `0 ≤ c` is a sign condition and `(2 * Real.pi) ^ 2` the window squared; the floor's own
numerals sit in `substrateThreshold`. -/
theorem sharp_constant_pos {c : ℝ} (hc0 : 0 ≤ c) (hc : c < substrateThreshold) :
    0 < κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hW : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have h0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have harc : (2 * Real.pi) ^ 2 * c < Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
    unfold substrateThreshold at hc
    rw [lt_div_iff₀ hW] at hc; linarith
  have hAnn : 0 ≤ Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) := Real.arccos_nonneg _
  have hlt : Real.sqrt ((2 * Real.pi) ^ 2 * c) < Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) := by
    have hstep : Real.sqrt ((2 * Real.pi) ^ 2 * c)
        < Real.sqrt (Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) harc
    rwa [Real.sqrt_sq hAnn] at hstep
  have hhalf : Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) < Real.pi / 2 :=
    Real.arccos_lt_pi_div_two.mpr h0
  have hcos : (3 : ℝ) ^ (-(1 : ℝ) / 4) < Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)) := by
    have hcc : Real.cos (Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4))) = (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
      Real.cos_arccos (by linarith) (le_of_lt h1)
    rw [← hcc]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (Real.sqrt_nonneg _) (by linarith) hlt
  have hval : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -κ₀YM := by
    rw [Real.log_rpow (by norm_num)]; unfold κ₀YM; ring
  have hlog : -κ₀YM < Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c))) := by
    rw [← hval]; exact Real.log_lt_log h0 hcos
  linarith

#print axioms sharp_constant_pos

/-- A gap in physical units, uniform along a refining family. Fix a screen of physical extent `L`,
refine it — `a = L/(N+1) → 0` as the aperture grows — and suppose the substrate ratio stays under one
`c` below the sharp threshold, at every aperture of the family and every coupling. Then

    (κ₀ + log cos(2π√c)) / L  ≤  (κ₀ − μYMAt (N₀+i) β) / a          for every `i` and `β`

and the left-hand side is a positive constant fixed before the family is indexed
(`uniform_gap_constant_pos`). A continuum limit needs the gaps to share a positive lower bound, not
merely that each lattice has one.

`substrateRatio` is `⟨d²⟩/(N+1)²`, a squared separation over a squared extent, both in lattice
units, so the spacing cancels and what remains is a property of the screen. A bound on it says the
correlation length is a bounded fraction of the screen, not that it is bounded in lattice units.
`c < substrateThreshold` says that fraction clears `arccos(3^{−1/4})/2π`. `κ₀ = ¼log3` is counted in
`Floor`, `2π` is the window, `L` is the screen, and `c` is the caller's bound on the read.

This reaches `ScreenedGap.uniform_physical_gap`'s conclusion from the sharp bound directly.
`ScreenedGap.Screened` carries `hrate : κ/(N+1) ≤ κ₀ − μ` as a field, and `surplus_ge_sharp` gives a
constant lower bound instead, which is stronger at every aperture.

DERIVED: `0 ≤ c` and `0 < L` are sign conditions, `(2 * Real.pi) ^ 2` is the window squared, and the
`1` is the extent offset `((N₀ + i : ℕ) : ℝ) + 1`. -/
theorem ym_physical_gap_uniform {c L : ℝ} (hc0 : 0 ≤ c) (hc : c < substrateThreshold)
    (hL : 0 < L) (N₀ : ℕ)
    (hsub : ∀ (i : ℕ) (β : ℝ), substrateRatio (N₀ + i) β ≤ c) :
    ∀ (i : ℕ) (β : ℝ),
      (κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)))) / L
        ≤ (κ₀YM - μYMAt (N₀ + i) β) / (L / (((N₀ + i : ℕ) : ℝ) + 1)) := by
  intro i β
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hW : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  -- the threshold bounds the rms angle by `arccos(3^{−1/4})`, which is inside the quarter-turn
  have harc : (2 * Real.pi) ^ 2 * c < Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by
    unfold substrateThreshold at hc
    rw [lt_div_iff₀ hW] at hc; linarith
  have harc_lt : Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) < Real.pi / 2 := by
    have h0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    exact Real.arccos_lt_pi_div_two.mpr h0
  have harc_nn : 0 ≤ Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) := Real.arccos_nonneg _
  have hdomc : (2 * Real.pi) ^ 2 * c < (Real.pi / 2) ^ 2 := by nlinarith
  set n : ℝ := ((N₀ + i : ℕ) : ℝ) + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  -- the read at this aperture sits under `c`, so its sharp surplus is at least the one at `c`
  have hsr := hsub i β
  have hsrnn := substrateRatio_nonneg (N₀ + i) β
  have hdom : (2 * Real.pi) ^ 2 * substrateRatio (N₀ + i) β < (Real.pi / 2) ^ 2 := by nlinarith
  have hmono : Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c))
      ≤ Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * substrateRatio (N₀ + i) β)) := by
    -- `cos` falls across the quarter-turn and `sqrt` rises, so a smaller ratio is a larger cosine
    refine Real.cos_le_cos_of_nonneg_of_le_pi (Real.sqrt_nonneg _) ?_ ?_
    · have : Real.sqrt ((2 * Real.pi) ^ 2 * c) ≤ Real.sqrt ((Real.pi / 2) ^ 2) :=
        Real.sqrt_le_sqrt (le_of_lt hdomc)
      rw [Real.sqrt_sq (by positivity)] at this; linarith
    · exact Real.sqrt_le_sqrt (by nlinarith)
  have hcosc : 0 < Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)) := by
    have hle : Real.sqrt ((2 * Real.pi) ^ 2 * c) < Real.pi / 2 := by
      have hstep : Real.sqrt ((2 * Real.pi) ^ 2 * c) < Real.sqrt ((Real.pi / 2) ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) hdomc
      rwa [Real.sqrt_sq (by positivity)] at hstep
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.sqrt_nonneg ((2 * Real.pi) ^ 2 * c)], hle⟩
  have hlog : Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)))
      ≤ Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * substrateRatio (N₀ + i) β))) :=
    Real.log_le_log hcosc hmono
  have hsurp := surplus_ge_sharp (N₀ + i) β hsrnn hdom
  have hconst : κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)))
      ≤ κ₀YM - μYMAt (N₀ + i) β := by linarith
  -- and `1/L ≤ n/L`, because the aperture arity is at least one
  have hrewrite : (κ₀YM - μYMAt (N₀ + i) β) / (L / n)
      = (n / L) * (κ₀YM - μYMAt (N₀ + i) β) := by field_simp
  rw [hrewrite]
  -- the aperture arity is at least one, and the constant is positive, so scaling by `n` only helps
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]; have : (0 : ℝ) ≤ ((N₀ + i : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  have hC0 : 0 < κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c))) :=
    sharp_constant_pos hc0 hc
  have key : κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)))
      ≤ n * (κ₀YM - μYMAt (N₀ + i) β) := by nlinarith
  rw [div_le_iff₀ hL]
  have hflat : (n / L) * (κ₀YM - μYMAt (N₀ + i) β) * L
      = n * (κ₀YM - μYMAt (N₀ + i) β) := by field_simp
  rw [hflat]
  exact key

#print axioms ym_physical_gap_uniform

/-- The constant `ym_physical_gap_uniform` delivers is positive, so the bound is a gap rather than a
tautology. It is positive when `c` is under the sharp threshold, which is the hypothesis, so nothing
further is assumed here.

DERIVED: `0 ≤ c` and `0 < L` are sign conditions and `(2 * Real.pi) ^ 2` is the window squared;
`sharp_constant_pos` supplies the rest. -/
theorem uniform_gap_constant_pos {c L : ℝ} (hc0 : 0 ≤ c) (hc : c < substrateThreshold)
    (hL : 0 < L) :
    0 < (κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)))) / L :=
  div_pos (sharp_constant_pos hc0 hc) hL

#print axioms uniform_gap_constant_pos

/-- The surplus is the logarithm of the measured cosine average. `μ = −log⟨cos θ⟩` by definition, so

    κ₀ − μYMAt N β  =  κ₀ + log (cosAvgYMAt N β)

is an identity, not a bound. The circle moment, the tangent and the threshold are routes to bounding
the right-hand side from below using less than the full distribution. -/
theorem surplus_eq_log_cosAvg (N : ℕ) (β : ℝ) :
    κ₀YM - μYMAt N β = κ₀YM + Real.log (cosAvgYMAt N β) := by
  show κ₀YM - -Real.log (cosAvgYMAt N β) = _
  ring

#print axioms surplus_eq_log_cosAvg

/-- The same statement in the cosine average, with no moment and no tangent. Fix a screen of
physical extent `L` and refine it. If the measured cosine average stays at or above some `γ` strictly
above the entropy floor, at every aperture of the family and every coupling, then

    (κ₀ + log γ) / L  ≤  (κ₀ − μYMAt (N₀+i) β) / a          for every `i` and `β`

and `κ₀ + log γ > 0` because `γ > 3^{−1/4} = e^{−κ₀}`.

`confinement_at_iff_cosAvg` makes `μ < κ₀ ⟺ ⟨cos θ⟩ > 3^{−1/4}` an iff. `ym_physical_gap_uniform`
reaches the same conclusion from `substrateRatio ≤ c`, which is that condition relaxed to a second
moment; the relaxation is sharp at second-moment order (`Sharp.cos_avg_ge_cos_rms`), and the 2.37×
window between the sufficient and necessary substrate bounds is what it costs. The aperture route
certifies the hypothesis from one number rather than the whole distribution.

`γ` is the measured cosine average, `κ₀ = ¼log3` is counted in `Floor`, and `L` is the screen.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is `e^{−κ₀}` at the floor `κ₀ = ¼log3`, `0 < L` is a sign condition,
and the `1` is the extent offset `((N₀ + i : ℕ) : ℝ) + 1`. -/
theorem ym_physical_gap_uniform_exact {γ L : ℝ}
    (hγ : (3 : ℝ) ^ (-(1 : ℝ) / 4) < γ) (hL : 0 < L) (N₀ : ℕ)
    (hcos : ∀ (i : ℕ) (β : ℝ), γ ≤ cosAvgYMAt (N₀ + i) β) :
    ∀ (i : ℕ) (β : ℝ),
      (κ₀YM + Real.log γ) / L
        ≤ (κ₀YM - μYMAt (N₀ + i) β) / (L / (((N₀ + i : ℕ) : ℝ) + 1)) := by
  intro i β
  have h0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hγ0 : 0 < γ := lt_trans h0 hγ
  have hval : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -κ₀YM := by
    rw [Real.log_rpow (by norm_num)]; unfold κ₀YM; ring
  have hCpos : 0 < κ₀YM + Real.log γ := by
    have := Real.log_lt_log h0 hγ
    rw [hval] at this; linarith
  -- the surplus is the log of the measured average, which the hypothesis floors
  have hstep : κ₀YM + Real.log γ ≤ κ₀YM - μYMAt (N₀ + i) β := by
    rw [surplus_eq_log_cosAvg]
    have := Real.log_le_log hγ0 (hcos i β)
    linarith
  set n : ℝ := ((N₀ + i : ℕ) : ℝ) + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]; have : (0 : ℝ) ≤ ((N₀ + i : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  have hrewrite : (κ₀YM - μYMAt (N₀ + i) β) / (L / n)
      = (n / L) * (κ₀YM - μYMAt (N₀ + i) β) := by field_simp
  rw [hrewrite, div_le_iff₀ hL]
  have hflat : (n / L) * (κ₀YM - μYMAt (N₀ + i) β) * L
      = n * (κ₀YM - μYMAt (N₀ + i) β) := by field_simp
  rw [hflat]
  nlinarith

#print axioms ym_physical_gap_uniform_exact

/-! ## The mass the read measures

`⟨cos θ⟩ = ∑_d p_d cos(2πd/(N+1))` is the `k=1` Fourier mode of the normalised correlation, so

    μ = log (Ŝ(0) / Ŝ(k₁)),      k₁ = 2π/(N+1)

the structure factor at zero momentum over its value at the lowest lattice momentum. That is the
second-moment mass estimator, and it inverts: writing `k̂₁ = 2 sin(π/(N+1))` for the lattice momentum,

    Ŝ(0)/Ŝ(k₁) = 1 + k̂₁²/m²   ⟹   m = k̂₁ / √(e^μ − 1).

`μ` falls like `1/(N+1)²` as the aperture grows — measured, `μ·L²` is flat at `≈3.1` across
`L = 8…32`. At fixed mass `k̂₁² ≈ (2π/L)²` falls like `1/L²`, so `μ ∼ 1/L²` is what a fixed mass
produces. Inverting on the released ensembles gives `m` constant to ±7.2% across a range over which
`μ` itself falls 14.6×.

So `κ₀ − μ` is not `a·m_phys`; the mass is `k̂₁/√(e^μ − 1)`, and that is what carries the spacing. -/

/-- The lowest nonzero lattice momentum at aperture `N`, `k̂₁ = 2 sin(π/(N+1))`.

DERIVED: `2` and the sine are the lattice momentum `k̂ = 2 sin(k/2)` at `k = k₁ = 2π/(N+1)`, the
smallest nonzero momentum a periodic extent of `N+1` sites carries. Neither is chosen. -/
noncomputable def khat1 (N : ℕ) : ℝ := 2 * Real.sin (Real.pi / ((N : ℝ) + 1))

/-- The second-moment mass in lattice units, `m = k̂₁/√(e^μ − 1)`, read off the same `μ` the
confinement criterion uses. It carries the lattice spacing as `m_phys = m/a`.

DERIVED: the `1` is subtracted because `e^μ = Ŝ(0)/Ŝ(k₁) = 1 + k̂₁²/m²` — it is the zero-momentum term
of that ratio, so `e^μ − 1` is the excess over it, and the whole definition is that identity solved
for `m`. Nothing is chosen, and no scale enters: `k̂₁` is the aperture's own lowest momentum. -/
noncomputable def m2At (N : ℕ) (β : ℝ) : ℝ :=
  khat1 N / Real.sqrt (Real.exp (μYMAt N β) - 1)

/-- `e^{κ₀} = 3^{1/4}`, the floor read as a contrast rather than as a rate.

DERIVED: `3 ^ ((1 : ℝ) / 4)` is `e^{κ₀}` with `κ₀ = ¼ log 3` as `κ₀YM` defines it; the identity is
`Real.rpow_def_of_pos` unfolded. -/
theorem exp_κ₀YM : Real.exp κ₀YM = (3 : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
  unfold κ₀YM
  ring_nf

#print axioms exp_κ₀YM

/-- `3^{1/4} > 1`, which is `exp_κ₀YM` together with `κ₀YM_pos`. It is what makes
`√(3^{1/4} − 1)` a positive real, so the mass bounds below may divide by it.

DERIVED: `3 ^ ((1 : ℝ) / 4)` is `e^{κ₀}` with `κ₀ = ¼ log 3`, and `1` is `e^0`. -/
theorem one_lt_three_rpow : (1 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [← exp_κ₀YM]
  have hx := Real.exp_lt_exp.mpr κ₀YM_pos
  rwa [Real.exp_zero] at hx

#print axioms one_lt_three_rpow

/-- Confinement bounds the mass from below. `μ < κ₀` caps `e^μ − 1` by `3^{1/4} − 1`, and the mass
divides by that square root, so the cap becomes a floor under the mass:

    μ < κ₀   ⟹   k̂₁ / √(3^{1/4} − 1)  <  m2At N β

`3^{1/4} = e^{κ₀}` with `κ₀ = ¼log3` counted in `Floor`, and `k̂₁` is the lattice momentum the
aperture carries.

DERIVED: `1 ≤ N` puts the angle `π/(N+1)` inside the half-turn where the sine is positive;
`0 < μYMAt N β` is what makes `e^μ − 1` positive; and `3 ^ ((1 : ℝ) / 4) - 1` is `e^{κ₀} − 1`, with
`4` the reciprocal area per step of the floor count. -/
theorem m2_gt_of_confinement {N : ℕ} {β : ℝ} (hN : 1 ≤ N)
    (hpos : 0 < μYMAt N β) (h : μYMAt N β < κ₀YM) :
    khat1 N / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) < m2At N β := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- the lattice momentum is positive: the angle is in the open half-turn
  have hang : Real.pi / ((N : ℝ) + 1) < Real.pi := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [div_lt_iff₀ hNpos]; nlinarith [Real.pi_pos]
  have hk : 0 < khat1 N := by
    unfold khat1
    have := Real.sin_pos_of_pos_of_lt_pi (by positivity : (0:ℝ) < Real.pi / ((N:ℝ)+1)) hang
    linarith
  have h1 : Real.exp (μYMAt N β) - 1 < (3 : ℝ) ^ ((1 : ℝ) / 4) - 1 := by
    have hx := Real.exp_lt_exp.mpr h
    rw [exp_κ₀YM] at hx; linarith
  have h0 : 0 < Real.exp (μYMAt N β) - 1 := by
    have hx := Real.exp_lt_exp.mpr hpos
    rw [Real.exp_zero] at hx
    linarith
  have hs0 : 0 < Real.sqrt (Real.exp (μYMAt N β) - 1) := Real.sqrt_pos.mpr h0
  have hs : Real.sqrt (Real.exp (μYMAt N β) - 1)
      < Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) := Real.sqrt_lt_sqrt h0.le h1
  unfold m2At
  exact div_lt_div_of_pos_left hk hs0 hs

#print axioms m2_gt_of_confinement

/-- The lattice momentum is at least `4/(N+1)`, by Jordan's inequality `sin x ≥ (2/π)x` on the
quarter-turn, where `π/(N+1)` sits once the aperture carries at least two sites.

DERIVED: `2/π` is Jordan's constant, tight at `π/2`; multiplied through `k̂₁ = 2 sin(π/(N+1))` it
gives `4/(N+1)`. The `4` is `2 × 2/π × π`, and `1 ≤ N` is the hypothesis that puts the angle inside
the quarter-turn. -/
theorem four_div_le_khat1 {N : ℕ} (hN : 1 ≤ N) : 4 / ((N : ℝ) + 1) ≤ khat1 N := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : 0 ≤ Real.pi / ((N : ℝ) + 1) := by positivity
  have hx2 : Real.pi / ((N : ℝ) + 1) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hNpos (by norm_num : (0:ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hj := Real.mul_le_sin hx0 hx2
  have hval : 2 / Real.pi * (Real.pi / ((N : ℝ) + 1)) = 2 / ((N : ℝ) + 1) := by
    field_simp
  rw [hval] at hj
  unfold khat1
  have : 2 * (2 / ((N : ℝ) + 1)) ≤ 2 * Real.sin (Real.pi / ((N : ℝ) + 1)) := by linarith
  calc 4 / ((N : ℝ) + 1) = 2 * (2 / ((N : ℝ) + 1)) := by ring
    _ ≤ 2 * Real.sin (Real.pi / ((N : ℝ) + 1)) := this

#print axioms four_div_le_khat1

/-- The physical mass bounded below, with no spacing in the bound. On a screen of physical extent
`L = (N+1)·a`, so `a = L/(N+1)`, confinement alone gives

    4 / (L·√(3^{1/4} − 1))  ≤  m2At N β / a

and the left-hand side carries no lattice spacing and no aperture — only the screen `L`, the entropy
floor through `3^{1/4} = e^{κ₀}`, and Jordan's constant. Numerically `4/√(3^{1/4}−1) = 7.115`, rising
to `2π/√(3^{1/4}−1) = 11.176` as the aperture grows and `(N+1)·sin(π/(N+1)) → π`
(`continuum_mass_bound_tendsto`).

Scope: the bound dilutes as the screen grows, so it is a finite-volume statement.
`(κ₀ − μ)/a` diverges as `a → 0` because `κ₀ − μ` tends to the counting floor rather than to zero, so
`κ₀ − μ` is not `a·m_phys`; the second-moment mass divided by the spacing is finite, positive and
spacing-free.

DERIVED: `1 ≤ N` and `0 < L` are the aperture and screen conditions, `0 < μYMAt N β` makes
`e^μ − 1` positive, `4` is Jordan's constant times the momentum's own `2`, and
`3 ^ ((1 : ℝ) / 4) - 1` is `e^{κ₀} − 1`. -/
theorem physical_mass_ge_of_confinement {N : ℕ} {β L : ℝ} (hN : 1 ≤ N) (hL : 0 < L)
    (hpos : 0 < μYMAt N β) (h : μYMAt N β < κ₀YM) :
    4 / (L * Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)) ≤ m2At N β / (L / ((N : ℝ) + 1)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hroot : 0 < Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) :=
    Real.sqrt_pos.mpr (by linarith [one_lt_three_rpow])
  have hstep := m2_gt_of_confinement hN hpos h
  have hjordan := four_div_le_khat1 hN
  have hchain : 4 / ((N : ℝ) + 1) / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) ≤ m2At N β := by
    have : 4 / ((N : ℝ) + 1) / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)
        ≤ khat1 N / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) :=
      div_le_div_of_nonneg_right hjordan hroot.le
    linarith
  have hrw : m2At N β / (L / ((N : ℝ) + 1)) = m2At N β * ((N : ℝ) + 1) / L := by
    field_simp
  rw [hrw, le_div_iff₀ hL]
  have hgoal : 4 / (L * Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)) * L
      = 4 / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) := by
    field_simp
  rw [hgoal]
  have hexp : 4 / ((N : ℝ) + 1) / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) * ((N : ℝ) + 1)
      = 4 / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) := by field_simp
  calc 4 / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)
      = 4 / ((N : ℝ) + 1) / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) * ((N : ℝ) + 1) := hexp.symm
    _ ≤ m2At N β * ((N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hchain (le_of_lt hNpos)

#print axioms physical_mass_ge_of_confinement

/-- A mass bound that does not weaken with the aperture:

    e^μ − 1 ≤ C·k̂₁²   ⟹   1/√C ≤ m2At N β

with `1/√C` carrying no aperture. `physical_mass_ge_of_confinement` bounds the mass by
`k̂₁/√(3^{1/4}−1)` instead, and `k̂₁ → 0` as the aperture grows, so that bound dilutes.

The hypothesis is that the structure-factor contrast `e^μ − 1 = (Ŝ(0) − Ŝ(k₁))/Ŝ(k₁)` scales like
the lowest momentum squared, which is a scaling law between two measured quantities rather than a
magnitude compared against a threshold. `C` is supplied by the caller and given no value here.
`C = 1/m²`, so the content is that the extracted mass does not fall as the box grows; on the
released SU(2) ensembles at β=2.30 that holds to ±7.2% across `L = 8…32`, over a range in which `μ`
itself falls 14.6×.

Composed with `Certify.gap_uniform_in_volume_of_intensive`, which takes an intensive margin and
returns one rate for every volume, this is the infinite-volume half.

DERIVED: `0 < C`, `1 ≤ N` and `0 < μYMAt N β` are the sign and aperture conditions, and the exponent
`2` in `khat1 N ^ 2` is the squared momentum the contrast is compared against. -/
theorem m2_ge_of_scaling {C : ℝ} (hC : 0 < C) {N : ℕ} {β : ℝ} (hN : 1 ≤ N)
    (hpos : 0 < μYMAt N β)
    (h : Real.exp (μYMAt N β) - 1 ≤ C * khat1 N ^ 2) :
    1 / Real.sqrt C ≤ m2At N β := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hang : Real.pi / ((N : ℝ) + 1) < Real.pi := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [div_lt_iff₀ hNpos]; nlinarith [Real.pi_pos]
  have hk : 0 < khat1 N := by
    unfold khat1
    have := Real.sin_pos_of_pos_of_lt_pi (by positivity : (0:ℝ) < Real.pi / ((N:ℝ)+1)) hang
    linarith
  have h0 : 0 < Real.exp (μYMAt N β) - 1 := by
    have hx := Real.exp_lt_exp.mpr hpos
    rw [Real.exp_zero] at hx
    linarith
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  -- the contrast's square root is at most `√C · k̂₁`
  have hsq : Real.sqrt (Real.exp (μYMAt N β) - 1) ≤ Real.sqrt C * khat1 N := by
    have hrw : C * khat1 N ^ 2 = (Real.sqrt C * khat1 N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC.le]
    have := Real.sqrt_le_sqrt (h.trans (le_of_eq hrw))
    rwa [Real.sqrt_sq (by positivity)] at this
  have hs0 : 0 < Real.sqrt (Real.exp (μYMAt N β) - 1) := Real.sqrt_pos.mpr h0
  -- so the mass, which divides by it, is at least `1/√C`
  unfold m2At
  rw [div_le_div_iff₀ hsC hs0]
  calc 1 * Real.sqrt (Real.exp (μYMAt N β) - 1)
      ≤ 1 * (Real.sqrt C * khat1 N) := by linarith
    _ = khat1 N * Real.sqrt C := by ring

#print axioms m2_ge_of_scaling

/-- The same hypothesis on a screen of extent `L = (N+1)a` gives `m_phys = m2At/a ≥ (N+1)/(L√C)`,
which grows with the aperture rather than diluting — the opposite behaviour to
`physical_mass_ge_of_confinement`.

DERIVED: `0 < C`, `0 < L`, `1 ≤ N` and `0 < μYMAt N β` are the sign and aperture conditions, and the
exponent `2` in `khat1 N ^ 2` is the squared momentum. -/
theorem physical_mass_ge_of_scaling {C L : ℝ} (hC : 0 < C) (hL : 0 < L) {N : ℕ} {β : ℝ}
    (hN : 1 ≤ N) (hpos : 0 < μYMAt N β)
    (h : Real.exp (μYMAt N β) - 1 ≤ C * khat1 N ^ 2) :
    ((N : ℝ) + 1) / (L * Real.sqrt C) ≤ m2At N β / (L / ((N : ℝ) + 1)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hstep := m2_ge_of_scaling hC hN hpos h
  have hrw : m2At N β / (L / ((N : ℝ) + 1)) = m2At N β * ((N : ℝ) + 1) / L := by field_simp
  rw [hrw, div_le_div_iff₀ (by positivity) hL]
  -- `1/√C ≤ m` is `1 ≤ m√C`, and the goal is that scaled by the positive `(N+1)·L`
  have hm : (1 : ℝ) ≤ m2At N β * Real.sqrt C := (div_le_iff₀ hsC).mp hstep
  have hprod := mul_le_mul_of_nonneg_left hm (le_of_lt (mul_pos hNpos hL))
  nlinarith [hprod]

#print axioms physical_mass_ge_of_scaling

/-- A mass bound fixed at one aperture and carried to all of them:

    m2At is the same at every aperture,  and  μ < κ₀ at one aperture N₀
      ⟹  k̂₁ N₀ / √(3^{1/4}−1)  <  m2At N β    at every aperture

`m2_gt_of_confinement` bounds the mass at aperture `N` by `k̂₁ N / √(3^{1/4}−1)`, and `k̂₁ N → 0`, so
applied aperture by aperture that erodes. Here the right-hand side is read off whichever `N₀` the
confinement is established at, and the bound is strongest at the coarsest such window, because `k̂₁`
is largest there.

Direction of the two bounds: reflection positivity bounds the gap above (`m_eff ≥ Δ`, §8.7b). The
floor bounds `μ = log(Ŝ(0)/Ŝ(k₁))` above, which bounds the mass below, because
`m² = k̂₁²/(e^μ − 1)`.

`hinv` says the mass does not depend on the window, not that it is positive. On the released SU(2)
ensembles at β=2.30 it holds to ±7.2% across `L = 8…32`, over a range in which `μ` itself falls
14.6×. Numerically `k̂₁/√(3^{1/4}−1)` is `3.557` at extent 2 and `1.361` at extent 8, against a
measured lattice mass of `3.32`–`3.82` across that range.

DERIVED: `1 ≤ N₀` puts the angle inside the half-turn, `0 < μYMAt N₀ β` makes `e^μ − 1` positive,
and `3 ^ ((1 : ℝ) / 4) - 1` is `e^{κ₀} − 1` at the floor `κ₀ = ¼log3`. -/
theorem m2_ge_of_aperture_invariant {β : ℝ} {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hpos : 0 < μYMAt N₀ β) (hconf : μYMAt N₀ β < κ₀YM)
    (hinv : ∀ N : ℕ, m2At N β = m2At N₀ β) :
    ∀ N : ℕ, khat1 N₀ / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) < m2At N β := by
  intro N
  rw [hinv N]
  exact m2_gt_of_confinement hN₀ hpos hconf

#print axioms m2_ge_of_aperture_invariant

/-- The same as an existence claim: one positive `δ`, fixed before the aperture is chosen, that
every aperture's mass clears.

Scope: this is the infinite-volume direction, `N → ∞` at fixed `β`, where the spacing does not move
and `δ/a` is a positive physical mass. It says nothing about `β → ∞` with `a → 0`, where the lattice
mass must itself scale like the spacing.

DERIVED: `1 ≤ N₀` and `0 < μYMAt N₀ β` are `m2_ge_of_aperture_invariant`'s own hypotheses, and
`0 < δ` is the conclusion's sign condition. -/
theorem exists_uniform_mass_of_aperture_invariant {β : ℝ} {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hpos : 0 < μYMAt N₀ β) (hconf : μYMAt N₀ β < κ₀YM)
    (hinv : ∀ N : ℕ, m2At N β = m2At N₀ β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ < m2At N β := by
  refine ⟨khat1 N₀ / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1), ?_,
    m2_ge_of_aperture_invariant hN₀ hpos hconf hinv⟩
  have hNpos : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
  have hang : Real.pi / ((N₀ : ℝ) + 1) < Real.pi := by
    have h1 : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
    rw [div_lt_iff₀ hNpos]; nlinarith [Real.pi_pos]
  have hk : 0 < khat1 N₀ := by
    unfold khat1
    have := Real.sin_pos_of_pos_of_lt_pi (by positivity : (0:ℝ) < Real.pi / ((N₀:ℝ)+1)) hang
    linarith
  exact div_pos hk (Real.sqrt_pos.mpr (by linarith [one_lt_three_rpow]))

#print axioms exists_uniform_mass_of_aperture_invariant

/-- The aperture's lowest momentum in physical units has a limit:

    (N+1) · k̂₁ N  =  2 (N+1) sin(π/(N+1))  →  2π

On a screen of fixed physical extent `L = (N+1)a` this says `k̂₁/a → 2π/L`: the lowest momentum the
aperture carries converges to the screen's own lowest momentum. It is the `a → 0` direction of
`Aperture.gap_refinement_invariant`, said in the momentum the mass is read against.

The proof is `sin t / t → 1` at `t = π/(N+1) → 0`.

DERIVED: `2 * Real.pi` is the limit of `(N+1)·k̂₁ N`, with the `2` carried from
`k̂₁ = 2 sin(π/(N+1))`, and the `1` is the extent offset `(N : ℝ) + 1`. -/
theorem khat1_mul_tendsto :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1) * khat1 N) Filter.atTop
      (nhds (2 * Real.pi)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- `t_N = π/(N+1) → 0`, through nonzero values
  have hNat : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have ht : Filter.Tendsto (fun N : ℕ => Real.pi / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hNat
  -- `sin t / t → 1` is the derivative of `sin` at `0`
  have hslope : Filter.Tendsto (fun t : ℝ => Real.sin t / t) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    have hd : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
    have := hasDerivAt_iff_tendsto_slope.mp hd
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht0
    simp [slope_def_field, Real.sin_zero, div_eq_inv_mul]
  have htne : ∀ᶠ N : ℕ in Filter.atTop, Real.pi / ((N : ℝ) + 1) ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := by
    filter_upwards with N
    have : (0 : ℝ) < Real.pi / ((N : ℝ) + 1) := by positivity
    exact ne_of_gt this
  have hwithin : Filter.Tendsto (fun N : ℕ => Real.pi / ((N : ℝ) + 1)) Filter.atTop
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht htne
  have hcomp := hslope.comp hwithin
  -- assemble: (N+1)·2 sin(π/(N+1)) = 2π · [sin(t)/t]
  have hEq : (fun N : ℕ => ((N : ℝ) + 1) * khat1 N)
      =ᶠ[Filter.atTop]
      (fun N : ℕ => 2 * Real.pi
        * (Real.sin (Real.pi / ((N : ℝ) + 1)) / (Real.pi / ((N : ℝ) + 1)))) := by
    filter_upwards with N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    unfold khat1
    field_simp
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa using (hcomp.const_mul (2 * Real.pi))

#print axioms khat1_mul_tendsto

/-- The continuum limit of the confinement mass bound. At a screen of fixed physical extent `L`,
with the spacing `a = L/(N+1)`, the bound from confinement is `k̂₁ N / √(3^{1/4}−1)` in lattice units,
so `(N+1)·k̂₁ N / (L√(3^{1/4}−1))` in physical ones. By `khat1_mul_tendsto` that converges to

    2π / (L · √(3^{1/4} − 1))   ≈   11.176 / L

with only the screen, the entropy floor and the window in it.

`physical_mass_ge_of_confinement` gives `4/(L√(3^{1/4}−1)) ≈ 7.115/L` at every finite aperture, via
Jordan's inequality. This is the same bound in the limit, 57% larger — the difference is `2π`
against Jordan's `4`, i.e. `sin t ≥ (2/π)t` against `sin t ≈ t`.

Which cap constant this is. The limit `2π/√(3^{1/4}−1) = 11.17598` is algebraically
`2π√(T/(1−T))` at `T = 3^{−1/4}`, the constant of the unfolded shape `ρ(d) = λ^d` — equivalently of
the periodic `cosh` correlator `λ^d + λ^{n−d}`, which has the same limit, and of the lattice free
field's `Ŝ(k) = 1/(m² + k̂²)`. `m2At` inverts exactly that structure factor, and the inversion is
exact for a single-mass periodic correlator.

The neighbouring constant `10.98875` belongs to the folded shape `ρ(d) = λ^min(d,n−d)`
(`ZeroMode.circLag_cos_sum_fold`, `CellSpectrum`'s aperture cap), where the minimum-image fold adds
weight at large lag and contributes the `coth(aπ/2) > 1` factor. Both shapes live on the same circle
and the fold is the difference. The folded constant is the smaller, which is why the aperture cap is
quoted with it. The two differ by `0.19`, closer than any simulated aperture is to its own limit, so
the repository carries a guard against quoting one for the other. The finite-aperture bound
`7.115/L` does not depend on either.

DERIVED: `0 < L` is the screen's positivity, `2 * Real.pi` is `khat1_mul_tendsto`'s limit,
`3 ^ ((1 : ℝ) / 4) - 1` is `e^{κ₀} − 1` at the floor `κ₀ = ¼log3`, and `1` is also the extent offset
`(N : ℝ) + 1`. -/
theorem continuum_mass_bound_tendsto (L : ℝ) (hL : 0 < L) :
    Filter.Tendsto
      (fun N : ℕ => ((N : ℝ) + 1) * khat1 N / (L * Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)))
      Filter.atTop
      (nhds (2 * Real.pi / (L * Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)))) := by
  have hroot : 0 < Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) :=
    Real.sqrt_pos.mpr (by linarith [one_lt_three_rpow])
  exact khat1_mul_tendsto.div_const _

#print axioms continuum_mass_bound_tendsto

/-- The physical mass bounded below uniformly in the aperture, on a fixed screen:

    δ  ≤  m2At N β / a        at every aperture `N` and coupling `β`,   `a = L/(N+1)`

`δ` is fixed before the family is indexed. The two hypotheses are scaling laws between measured
quantities rather than magnitudes compared against thresholds:

* `hscale` — `e^μ − 1 ≤ C N · k̂₁²`. The structure-factor contrast goes like the lowest momentum
  squared. Measured on the released SU(2) ensembles: `C` flat to ±13.7% (β=2.30, L=8…32), ±7.5%
  (β=2.40), ±12.2% (β=2.60), over a range in which `μ` itself falls 14.6×.
* `hphys` — `√(C N) ≤ (N+1)/(Lδ)`. Since `C = 1/m²`, this says the lattice mass falls like the
  spacing, `m_lat ∼ a`. Measured on the smeared channel: `ξ_phys√σ` agrees to 5.0% across a 1.343×
  change of spacing, giving `m_phys/√σ ≈ 3.86` against the SU(2) `0⁺⁺` glueball at `≈3.6√σ`. On the
  raw channel the agreement is 21.4% and in the opposite direction, that channel being contact-scale.

Scope. `hphys` unfolds to the conclusion: with `C = 1/m²` it says `m/a ≥ δ`, which is `m_phys ≥ δ`.
This theorem carries the bound through the screen's arithmetic and adds no content of its own. The
content sits in the two statements it composes:

* `physical_mass_ge_of_confinement` gives `m_phys ≥ 4/(L√(3^{1/4}−1))` from `μ < κ₀` alone, with no
  assumed mass — positive and spacing-free, but diluting as the screen grows.
* `m2_ge_of_scaling` converts a `μ` that vanishes like `1/(N+1)²` into a mass that does not.

`C` is fixed in lattice units, so a spacing-independent `δ` needs `C ∼ 1/(a·m_phys)²`. That is
measured on the smeared channel (scale-covariant to 5.0%) and not on the raw one (21.4%, opposite
direction).

DERIVED: `0 < L`, `0 < δ`, `0 < C N`, `1 ≤ N` and `0 < μYMAt N β` are the sign and aperture
conditions; the exponent `2` in `khat1 N ^ 2` is the squared momentum; the `1` also appears as the
extent offset `(N : ℝ) + 1`. -/
theorem ym_physical_mass_uniform {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (C : ℕ → ℝ)
    (hC : ∀ N, 0 < C N)
    (hscale : ∀ (N : ℕ) (β : ℝ), 1 ≤ N → 0 < μYMAt N β →
      Real.exp (μYMAt N β) - 1 ≤ C N * khat1 N ^ 2)
    (hphys : ∀ N : ℕ, Real.sqrt (C N) ≤ ((N : ℝ) + 1) / (L * δ)) :
    ∀ (N : ℕ) (β : ℝ), 1 ≤ N → 0 < μYMAt N β → δ ≤ m2At N β / (L / ((N : ℝ) + 1)) := by
  intro N β hN hpos
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsC : 0 < Real.sqrt (C N) := Real.sqrt_pos.mpr (hC N)
  have hstep := m2_ge_of_scaling (hC N) hN hpos (hscale N β hN hpos)
  -- `1/√C ≤ m`, and `√C ≤ (N+1)/(Lδ)`, so `m ≥ Lδ/(N+1)`
  have hlow : L * δ / ((N : ℝ) + 1) ≤ m2At N β := by
    refine le_trans ?_ hstep
    rw [div_le_div_iff₀ hNpos hsC]
    have := hphys N
    rw [le_div_iff₀ (by positivity : (0:ℝ) < L * δ)] at this
    nlinarith [this, hNpos, hsC]
  have hrw : m2At N β / (L / ((N : ℝ) + 1)) = m2At N β * ((N : ℝ) + 1) / L := by field_simp
  rw [hrw, le_div_iff₀ hL]
  have := mul_le_mul_of_nonneg_right hlow (le_of_lt hNpos)
  have hflat : L * δ / ((N : ℝ) + 1) * ((N : ℝ) + 1) = L * δ := by field_simp
  rw [hflat] at this
  nlinarith [this]

#print axioms ym_physical_mass_uniform

/-- Confinement with a size: under `substrateRatio N β ≤ c` and the same threshold
`confinement_of_growth_ratio` uses, the entropy surplus clears

    κ₀ + log(1 − (2π)²c/2)

which carries no aperture. It is `surplus_ge` weakened by monotonicity of the logarithm.

`ScreenedGap.Screened` asks for `hrate : κ/(N+1) ≤ κ₀ − μ`, and `ZeroMode.rate_gt_of_tension`
supplies that only for a single geometric mode. A constant lower bound is stronger than `κ/(N+1)` at
every large aperture, so this supplies `hrate` for the actual read, at any `κ`, with no assumption on
the mode structure.

DERIVED: `0 ≤ c` is a sign condition; `(2 * Real.pi) ^ 2 * c / 2 < 1 - 3 ^ (-(1 : ℝ) / 4)` is
`confinement_at_of_ratio`'s threshold, with the window squared, the cosine bound's denominator `2`,
and `e^{−κ₀}` at the floor `κ₀ = ¼log3`. -/
theorem surplus_ge_of_ratio {c : ℝ} (hc0 : 0 ≤ c)
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    {N : ℕ} {β : ℝ} (h : substrateRatio N β ≤ c) :
    Real.log (1 - (2 * Real.pi) ^ 2 * c / 2) + κ₀YM ≤ κ₀YM - μYMAt N β := by
  -- One path: this is `surplus_ge` weakened by monotonicity of `log`. The comparison constant `c`
  -- buys nothing the measured ratio does not already give, and no cosine bound is re-derived here.
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hA : (0 : ℝ) < 1 - (2 * Real.pi) ^ 2 * c / 2 := by linarith
  have hpi : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
  have hmono : (2 * Real.pi) ^ 2 * substrateRatio N β / 2 ≤ (2 * Real.pi) ^ 2 * c / 2 := by
    have := mul_le_mul_of_nonneg_left h hpi
    linarith
  have hdom : (2 * Real.pi) ^ 2 * substrateRatio N β / 2 < 1 := by linarith
  have hlog : Real.log (1 - (2 * Real.pi) ^ 2 * c / 2)
      ≤ Real.log (1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2) :=
    Real.log_le_log hA (by linarith)
  have := surplus_ge N β hdom
  linarith

#print axioms surplus_ge_of_ratio

/-- The lattice surplus clears `κ/((N : ℝ) + 1)` at every large enough aperture, for any `κ`, from
the aperture-free ratio bound alone. This is the `hrate` field of `ScreenedGap.Screened`, which
`ZeroMode.rate_gt_of_tension` supplies only for a single geometric mode. Composed with a screen of
fixed physical extent `L = (N+1)a` the spacing cancels and `ScreenedGap.uniform_physical_gap` returns
`Δ_phys ≥ κ/L`.

DERIVED: `0 ≤ c` is a sign condition, `(2 * Real.pi) ^ 2 * c / 2 < 1 - 3 ^ (-(1 : ℝ) / 4)` is
`confinement_at_of_ratio`'s threshold, and the `1` is also the extent offset `(N : ℝ) + 1`. -/
theorem rate_of_ratio {c κ : ℝ} (hc0 : 0 ≤ c)
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, substrateRatio N β ≤ c) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, κ / ((N : ℝ) + 1) ≤ κ₀YM - μYMAt N β := by
  set g : ℝ := Real.log (1 - (2 * Real.pi) ^ 2 * c / 2) + κ₀YM with hg
  -- the constant floor is positive, because the threshold is exactly `log` of the floor gap
  have hA : (0 : ℝ) < 1 - (2 * Real.pi) ^ 2 * c / 2 := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  have hgpos : 0 < g := by
    have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 1 - (2 * Real.pi) ^ 2 * c / 2 := by linarith
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    have hlog : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4))
        < Real.log (1 - (2 * Real.pi) ^ 2 * c / 2) := Real.log_lt_log h3 hlt
    have hval : Real.log ((3 : ℝ) ^ (-(1 : ℝ) / 4)) = -κ₀YM := by
      rw [Real.log_rpow (by norm_num)]; unfold κ₀YM; ring
    rw [hval] at hlog
    rw [hg]; linarith
  -- and `κ/(N+1)` eventually falls below any positive constant
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop, κ / ((N : ℝ) + 1) ≤ g := by
    have htend : Filter.Tendsto (fun N : ℕ => κ / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have hN : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact Filter.Tendsto.div_atTop tendsto_const_nhds hN
    exact htend.eventually_le_const hgpos
  filter_upwards [h, hsmall] with N hN hle β
  exact le_trans hle (surplus_ge_of_ratio hc0 hc (hN β))

#print axioms rate_of_ratio

/-- The physical gap with the lattice spacing divided out. Read the theory through a screen of fixed
physical extent `L`, so the aperture grows as the spacing falls, `(N+1)·a = L`. Then from the
aperture-free ratio bound alone,

    κ/L  ≤  (κ₀ − μYMAt N β) / a       at every member of the family,

with the right-hand side the gap in physical units. The spacing cancels:
`(κ₀−μ)/a = (κ₀−μ)(N+1)/L`, and `rate_of_ratio` gives `(κ₀−μ)(N+1) ≥ κ`.

`κ/L` is one number fixed before the family is indexed, and every member of the family clears it, so
the gaps share a positive lower bound rather than each lattice merely having one.

The hypothesis is `substrateRatio N β ≤ c` with `(2π)²c/2 < 1 − 3^{−1/4}`, i.e. the substrate's
second moment per unit squared aperture stays under `0.012167`. No strong-coupling expansion, no
cluster expansion, and no restriction on the mode structure of the read.

DERIVED: `0 ≤ c` and `0 < L` are sign conditions, `(2 * Real.pi) ^ 2 * c / 2 < 1 - 3 ^ (-(1 : ℝ) / 4)`
is `confinement_at_of_ratio`'s threshold, and the `1` is also the extent offset. -/
theorem ym_physical_gap_of_ratio {c κ L : ℝ} (hc0 : 0 ≤ c)
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hL : 0 < L)
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, substrateRatio N β ≤ c) :
    ∃ N₀ : ℕ, ∀ (i : ℕ) (β : ℝ),
      κ / L ≤ (κ₀YM - μYMAt (N₀ + i) β) / (L / ((((N₀ + i : ℕ)) : ℝ) + 1)) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (rate_of_ratio (κ := κ) hc0 hc h)
  refine ⟨N₀, fun i β => ?_⟩
  have hrate := hN₀ (N₀ + i) (Nat.le_add_right _ _) β
  set n : ℝ := (((N₀ + i : ℕ)) : ℝ) + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  -- the spacing cancels: dividing by `L/n` is multiplying by `n/L`
  have hrewrite : (κ₀YM - μYMAt (N₀ + i) β) / (L / n)
      = (κ₀YM - μYMAt (N₀ + i) β) * n / L := by
    field_simp
  have key : κ ≤ (κ₀YM - μYMAt (N₀ + i) β) * n := (div_le_iff₀ hnpos).mp hrate
  rw [hrewrite, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hL.le)

#print axioms ym_physical_gap_of_ratio

/-- The converse at one aperture: a tension below the floor forces the substrate ratio under
`(1 − 3^{−1/4})/8`, a ceiling built from the floor alone.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is `e^{−κ₀}` at the floor `κ₀ = ¼log3`, and the divisor `8` is the
window factor `(2π)²` bounded below by `2·4²` in `Moment.Read.substrate_lt_of_tension_lt_floor`;
`0 < cosAvgYMAt N β` is the domain of the logarithm. -/
theorem substrateRatio_lt_of_tension_lt_floor {N : ℕ} {β : ℝ} (hpos : 0 < cosAvgYMAt N β)
    (h : μYMAt N β < κ₀YM) :
    substrateRatio N β < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 :=
  (readYMAt N β).substrate_lt_of_tension_lt_floor hpos h

/-- The entropy surplus read through an aperture of size `N`. -/
noncomputable def ΔYMAt (N : ℕ) (β : ℝ) : ℝ := κ₀YM - μYMAt N β

/-- A positive entropy surplus and confinement are the same statement at any aperture, `ΔYMAt`
being `κ₀YM - μYMAt N β` by definition. This is the form `YMGap.ymGapped` consumes.

DERIVED: `0 < ΔYMAt N β` is the sign of the surplus, the only numeral in the statement. -/
theorem gap_pos_iff_confinement_at (N : ℕ) (β : ℝ) : 0 < ΔYMAt N β ↔ μYMAt N β < κ₀YM := by
  unfold ΔYMAt; constructor <;> intro h <;> linarith

/-- The decay factor `e^{−Δ}` is strictly inside the unit disk exactly when the surplus is positive,
at any aperture.

DERIVED: `1` is the unit modulus `Real.exp 0` and `0 < ΔYMAt N β` the sign of the surplus. -/
theorem oneway_margin_at (N : ℕ) (β : ℝ) : Real.exp (-(ΔYMAt N β)) < 1 ↔ 0 < ΔYMAt N β := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- Under one aperture-independent substrate bound the tension tends to zero, so the surplus
`Δ = κ₀ − μ` converges to `κ₀`. The limit is taken in the aperture at a fixed coupling. -/
theorem margin_tendsto_floor {B : ℝ} (hB : ∀ N β, d2At N β ≤ B) (β : ℝ) :
    Filter.Tendsto (fun N => ΔYMAt N β) Filter.atTop (nhds κ₀YM) := by
  have h : Filter.Tendsto (fun N => μYMAt N β) Filter.atTop (nhds 0) :=
    Moment.tension_tendsto_zero_of_bounded_circ_moment B (fun N => readYMAt N β)
      (fun N => hB N β)
  simpa [ΔYMAt] using tendsto_const_nhds.sub h

-- The confinement route, footprinted. Each of these carries the foundational three plus
-- `wilson_reflection_positive_at` and nothing else.
#print axioms confinement_at_of_cosAvg
#print axioms confinement_at_iff_cosAvg
#print axioms substrateRatio_le_iff
#print axioms confinement_at_of_ratio
#print axioms confinement_at_coupling_of_ratio
#print axioms confinement_of_growth_bound
#print axioms confinement_of_growth_ratio
#print axioms confinement_of_substrate_bound
#print axioms confinement_of_bounded_substrate
#print axioms substrateRatio_lt_of_tension_lt_floor
#print axioms margin_tendsto_floor

/-- The threshold coupling at an arbitrary Bessel argument, defined as where the linear character
bound meets the floor: `β_c(x) = κ₀ / (2 r(x))`.
-- DERIVED: the `2` is the character bound's own slope `μ ≤ 2βr`, and `κ₀` is the proved floor.
-- Solving `2βr = κ₀` for `β` is the definition; no value is chosen. -/
noncomputable def βcAt (x : ℝ) : ℝ := κ₀YM / (2 * rAt x)

/-- The threshold identity `2 β_c r = κ₀` holds at every positive argument, so the pinned `rArgYM`
is one value of a variable rather than a number the identity depends on.

DERIVED: `0 < x` is the positivity `rAt_pos` needs to divide by the ratio, and the `2` is `βcAt`'s
own slope factor. -/
theorem βcAt_spec {x : ℝ} (hx : 0 < x) : 2 * βcAt x * rAt x = κ₀YM := by
  have hr : rAt x ≠ 0 := ne_of_gt (rAt_pos hx)
  unfold βcAt
  field_simp

#print axioms βcAt_spec

/-- The threshold coupling at the pinned argument — the `rArgYM` instance of `βcAt`. -/
noncomputable def βcYM : ℝ := βcAt rArgYM
/-- A strong-coupling reference point strictly below the threshold.
-- CHOSEN: the offset `1` only has to be positive — it names a point below `β_c` for the grid route's
-- case split, and every theorem using it takes the behaviour there as a hypothesis. Any positive
-- offset gives the same theorems. -/
noncomputable def βloYM : ℝ := βcYM - 1

/-! ## A1's constants and the cited standard inputs -/

/-! ### A1's interior: crossover confinement from a bounded correlation moment

The min-entropy tension the gap reads is `μ = log(S(0)/S(2π/L))` of the whitened `:F²:` correlation.
With reflection positivity (`ρ ≥ 0`, so `λ₁ = S(0)`, `λ₂ ≥ S(2π/L)`;
`FreeField.structure_factor_peak_at_zero`), `μ ≤ -log ⟨cos θ⟩_ρ`, and the step
`⟨cos θ⟩ ≥ 1-⟨θ²⟩/2 ⟹ (moment bound) ⟹ μ < κ₀` is checked in
`Moment.tension_lt_floor_of_moment` from reflection positivity and `cos x ≥ 1-x²/2` alone. So A1's
interior is a theorem given a bounded correlation second moment `⟨θ²⟩/2 < 1-3^{-1/4}`, equivalently
`M₂ < (1-3^{-1/4})L²/(2π²)`, a finite correlation length. The measured input is the bounded moment —
the finite-specific-heat / SU(N) no-bulk-transition content (cited; measured `M₂ ≤ 0.15` against
`0.78`, margin growing ∝ L²). -/

/-- The whitened `:F²:` correlation as a probability vector over its lag index, taken from
`readYM β` (`p = ρ/Σρ`, nonnegative and summing to one by construction).

DERIVED: the `1` is the lag arity of `Fin (nCorrYM + 1)` — a window of size `nCorrYM` resolves that
many lags. -/
noncomputable def pcorrYM (β : ℝ) : Fin (nCorrYM + 1) → ℝ := (readYM β).p
/-- The angular structure `θ_d = 2π d /(L+1)` of the correlation, taken from `readYM β`
(`Moment.Read.θ`).

DERIVED: the `1` is the lag arity of `Fin (nCorrYM + 1)`. -/
noncomputable def thetaYM (β : ℝ) : Fin (nCorrYM + 1) → ℝ := (readYM β).θ

/-- The correlation weights are nonnegative, since `p = ρ/Σρ` with `ρ ≥ 0`.

DERIVED: `0 ≤ pcorrYM β d` is the conclusion and the only numeral in the statement. -/
theorem pcorr_nonneg : ∀ β d, 0 ≤ pcorrYM β d := fun β d => (readYM β).p_nonneg d
/-- The correlation weights sum to one, `Σ(ρ/Σρ) = 1`.

DERIVED: the `1` is the total probability mass. -/
theorem pcorr_sum : ∀ β, ∑ d, pcorrYM β d = 1 := fun β => (readYM β).p_sum

/-- The read is the min-entropy tension of the correlation, `μ = -log⟨cos θ⟩_ρ`, which equals
`log(S(0)/S(2π/L))` under reflection positivity with `λ₁=S(0)` and `λ₂ ≥ S(2π/L)`. It holds by
`rfl`: `μYM` is `(readYM β).tension`, which is `-log⟨cos θ⟩_ρ` by definition. -/
theorem ym_tension_is_moment : ∀ β,
    μYM β = - Real.log (∑ d, pcorrYM β d * Real.cos (thetaYM β d)) := fun _ => rfl

/-! ### A1's interior: the uniform finite-correlation-length bound

The interior input is a bound on the correlation's lag second moment `⟨d²⟩ = ∑_d p_d d²`, a squared
correlation length: `⟨d²⟩(β) ≤ 1` uniformly for `β ≥ βcYM`. The `1/L²` aperture scaling is proved
(`Moment.Read.tension_lt_floor_of_circ_moment`, reached from a raw-index bound by
`circ_moment_le_lag_moment`): the θ-moment factors as `⟨θ²⟩ = (2π/(L+1))² ⟨d²⟩`, so the fixed bound
`B = 1` puts `μ` under the floor at every large `L`, with margin ∝ L², and `1` sits `3.52×` under the
aperture threshold `B₁₆ ≈ 3.52` (`ym_finite_aperture`). Measured, `⟨d²⟩` stays under `1` across the
crossover (figures in PAPER §9), with the free-field weak-coupling limit `⟨d²⟩ → ~0.12`
(`FreeField`). The bound is consistent with the provable `⟨d²⟩ ≥ 0` and holds on the whole half-line
`β ≥ βcYM`. It is the spatial correlation moment, distinct from the energy susceptibility `χ_v`
(Shannon/specific-heat), the Rényi relation of PAPER §8.4.

A flat `0 ≤ ⟨d²⟩ ≤ 1`, consistent with `pcorr_nonneg` and `sq_nonneg`, is what
`tension_lt_floor_of_circ_moment` consumes through `circ_moment_le_lag_moment`; any `B < 3.52`, the
aperture ceiling at `N = 16`, suffices, and `1` is the certified value (`99.9%`
empirical-Bernstein). The closed-form envelope and its Lipschitz regularity come from the grid route
`ym_crossover_confinement_of_grid`, a measured modulus of continuity. -/

/-- The finite-aperture premise, proved. With the certified bound `B = 1`, the aperture condition
`(2π/(N+1))² · B / 2 < 1 − 3^{-1/4}` is a numeric inequality about the aperture
`N = nCorrYM = 16`, discharged by `norm_num` from `π < 3.15` (upper-bounding the `(2π/17)²` factor)
and `3^{-1/4} ≤ 4/5` (from `(5/4)⁴ = 625/256 ≤ 3`, lower-bounding the floor gap by `1/5`):
`(2π/17)²/2 ≈ 0.068 < 1/5 ≤ 1 − 3^{-1/4}`. The same inequality holds for every `N ≥ 9`. Independence
of the conclusion from `L` is the separate `Certify.gap_uniform_in_volume_of_intensive`.

DERIVED: `2 * Real.pi / (nCorrYM + 1)` is the aperture's own window, the `* 1` is the certified
moment bound `B = 1` carried explicitly, the division by `2` is the denominator of `1 − x²/2 ≤ cos x`,
and `3 ^ (-(1 : ℝ) / 4)` is `e^{−κ₀}` at the floor `κ₀ = ¼log3`. -/
theorem ym_finite_aperture :
    (2 * Real.pi / (nCorrYM + 1)) ^ 2 * 1 / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  -- floor gap: 3^{-1/4} ≤ 4/5, so 1 - 3^{-1/4} ≥ 1/5
  have h54 : (5 / 4 : ℝ) ≤ (3 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num,
        Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num),
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (3 : ℝ) ^ (-(1 : ℝ) / 4) = ((3 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := by
    rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.rpow_neg (by norm_num)]
  have h45 : (3 : ℝ) ^ (-(1 : ℝ) / 4) ≤ 4 / 5 := by
    rw [hneg, inv_le_comm₀ hpos (by norm_num)]
    calc ((4 : ℝ) / 5)⁻¹ = 5 / 4 := by norm_num
      _ ≤ (3 : ℝ) ^ ((1 : ℝ) / 4) := h54
  -- aperture factor: (2π/(16+1))² · 1 / 2 = (2π/17)² / 2 ≈ 0.068 < 1/5
  have hN : ((nCorrYM : ℝ) + 1) = 17 := by norm_num [nCorrYM]
  rw [hN]
  nlinarith [hpi, hpi0, h45, sq_nonneg Real.pi]

/-- The circle moment is under the raw lag moment, so a bound read off the raw index — which is what
the grid certificates measure — feeds the circle-moment route. The inequality is
`min d (N+1−d) ≤ d` weighted by a probability vector, and it runs one way only. A raw bound is the
stronger of the two, which is why `d2At` is stated about the circle.

DERIVED: the exponent `2` on both sides is the second moment's own. -/
theorem circ_moment_le_lag_moment {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ ∑ d, R.p d * (d : ℝ) ^ 2 := by
  refine Finset.sum_le_sum (fun d _ => ?_)
  have hle : ((Moment.circLag d : ℕ) : ℝ) ≤ ((d : ℕ) : ℝ) := by
    exact_mod_cast min_le_left (d : ℕ) (N + 1 - (d : ℕ))
  have h0 : (0 : ℝ) ≤ ((Moment.circLag d : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by nlinarith) (R.p_nonneg d)

-- `ym_crossover_confinement_of_grid` is the deterministic-read alternative to the substrate route:
-- a finite grid plus a measured modulus of continuity, with no bound asserted on the substrate.

/-- A1's interior confinement from a finite grid certificate. On the compact interval `[a,b]`: if
the whitened lag second moment `⟨d²⟩(β) = ∑_d pcorrYM β d · d²` is `L`-Lipschitz there (`hlip`, a
measured modulus of continuity) and a `δ`-net certifies `⟨d²⟩ ≤ B - L·δ` (`hcover`, finitely many
deterministic reads with the margin absorbed), then under the aperture condition
`(2π/(nCorrYM+1))²·B/2 < 1 - 3^{-1/4}` the tension stays below the floor on all of `[a,b]`. The `∀β`
content is a finite grid plus the Lipschitz constant `L` (`Certify.le_of_lipschitz_grid` and the
proved aperture scaling), foundational axioms only. `L` is the measured input: a smoothness of the
read between grid points, a spike in which would be a critical point.

DERIVED: `0 ≤ L` is a sign condition; `2 * Real.pi / (nCorrYM + 1)`, the exponent `2`, the division
by `2` and `3 ^ (-(1 : ℝ) / 4)` are the aperture condition's own, as in `ym_finite_aperture`; and the
exponent `2` on `(d : ℝ) ^ 2` is the second moment's. `B`, `L`, `δ`, `a` and `b` are variables. -/
theorem ym_crossover_confinement_of_grid {a b B L δ : ℝ} (hL : 0 ≤ L)
    (haperture : (2 * Real.pi / (nCorrYM + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |(∑ d, pcorrYM x d * (d : ℝ) ^ 2) - (∑ d, pcorrYM y d * (d : ℝ) ^ 2)| ≤ L * |x - y|)
    (hcover : ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧
      (∑ d, pcorrYM γ d * (d : ℝ) ^ 2) ≤ B - L * δ) :
    ∀ β ∈ Set.Icc a b, μYM β < κ₀YM := by
  intro β hβ
  have hbound : ∑ d, pcorrYM β d * (d : ℝ) ^ 2 ≤ B :=
    le_of_lipschitz_grid hL hlip hcover β hβ
  unfold μYM κ₀YM
  exact (readYM β).tension_lt_floor_of_circ_moment
    (le_trans (circ_moment_le_lag_moment (readYM β)) hbound) haperture

/-! ## A2's data and the cited Nyquist-Shannon sampling isometry -/

/-- The orientation type of the directional read: the permutations of the four lattice axes.

DERIVED: `4` is the spacetime dimension the development is stated in — the number of axes a
hypercubic lattice has, so the orientations are their permutations. It is not a size or a cutoff. -/
abbrev DYM : Type := Equiv.Perm (Fin 4)

/-- The transport is the axis permutation's own matrix and is orthogonal. A permutation matrix has
exactly one `1` in each row and column, so `Pᵀ P = 1`: the transport between two orientations of the
lattice preserves the sample inner product because relabelling axes does.

DERIVED: the `1` is the identity matrix that orthogonality means. -/
theorem permMatrix_orthogonal (σ : DYM) :
    (σ.permMatrix ℝ)ᵀ * σ.permMatrix ℝ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

/-- The base directional window `F₀` at a reference orientation; the read acts on its Gram `Xᵀ X`
[E §3]. It is left abstract because `A2` holds for every base window. -/
opaque Fbase : Matrix (Fin 4) (Fin 4) ℝ
/-- O(4), the orthogonal 4×4 matrices, is inhabited by the identity `1`, so a transport valued in it
is well-formed and computable, with `1` the default value. -/
instance : Inhabited {M : Matrix (Fin 4) (Fin 4) ℝ // Mᵀ * M = 1} := ⟨⟨1, by simp⟩⟩

/-- The transport from the reference orientation to `d`, valued in O(4), constructed as the
permutation matrix of the axis permutation `d`. Below the Nyquist threshold (PAPER §8.6,
`a⋆ k₀ = 0.364 < 1`) the reconstruction `Rc` and sampling `Sm` maps are exact isometries — the
discrete samples carry the continuum inner product with no loss (Nyquist–Shannon) — so in
`Otr = Rc·Um·Sm` (`Apriori.resampling_orthogonal`) the sampling factors collapse to the identity and
the net transport between orientations is a relabelling of axes.

The transport is constructed rather than abstract, so it is not constant: `ym_A2_nonvacuous` below
exhibits two axis permutations whose transports are distinct matrices, which a constant transport
would make `ym_A2`'s `∀ d d', R d = R d'` hold for.

DERIVED: `4` is the spacetime dimension, as in `DYM`, so the matrix is `4×4`; `1` is the identity
`Pᵀ P = 1` that orthogonality means, proved in `permMatrix_orthogonal` and not imposed. The `0.364`
and `8.6` quoted above are the measured Nyquist threshold `a⋆k₀` and its reported margin, cited here;
neither enters this definition. -/
noncomputable def OtrO (d : DYM) : {M : Matrix (Fin 4) (Fin 4) ℝ // Mᵀ * M = 1} :=
  ⟨d.permMatrix ℝ, permMatrix_orthogonal d⟩
/-- The transport as a plain matrix — the underlying element of `OtrO d`.

DERIVED: `4` is the spacetime dimension, so the matrix is `4×4`, as in `DYM`. -/
noncomputable def Otr (d : DYM) : Matrix (Fin 4) (Fin 4) ℝ := (OtrO d).1
/-- The spectral read: a scalar functional of the characteristic polynomial [E §3, §10]. -/
opaque freadYM : Polynomial ℝ → ℝ

/-- The Nyquist transport is orthogonal — the O(4) membership of `OtrO`. The transport preserves the
sample inner product below the Nyquist threshold (Nyquist–Shannon; PAPER §8.6, `a⋆ k₀ = 0.364`), so
it lies in O(4), which discharges A2's sampling composition (`ym_A2`) with no axiom. The general
"preserves the sample inner product implies orthogonal" fact is
`Apriori.orthogonal_of_preserves_dotProduct`.

DERIVED: the `1` is the identity matrix orthogonality is stated against. -/
theorem Otr_iso (d : DYM) : (Otr d)ᵀ * Otr d = 1 := (OtrO d).2

/-- The orientation type has 24 elements, so `A2`'s conclusion `∀ d d', R d = R d'` quantifies over
a group of that size. It is the same `Equiv.Perm (Fin 4)` the measure side's
`WilsonHypercubic.axisSymmetry` acts by.

DERIVED: `24` is `4!`, the order of the permutation group on the four lattice axes; `Fintype.card_perm`
computes it. -/
theorem card_DYM : Fintype.card DYM = 24 := by
  simp [Fintype.card_perm]
  decide

#print axioms card_DYM

/-- The transports at distinct axis permutations are distinct matrices: the identity permutation and
a transposition have determinants `1` and `-1`. A constant transport would make `∀ d d', R d = R d'`
hold because every orientation carried the same window, and this rules that reading out. It is the
`A2` counterpart of `spectral_bar_nonvacuous`. -/
theorem ym_A2_nonvacuous : ∃ d d' : DYM, Otr d ≠ Otr d' := by
  refine ⟨1, Equiv.swap 0 1, fun h => ?_⟩
  have hd : (Otr (1 : DYM)).det = (Otr (Equiv.swap (0 : Fin 4) 1)).det := congrArg Matrix.det h
  rw [Otr, Otr, OtrO, OtrO] at hd
  simp only [Matrix.det_permutation, Equiv.Perm.sign_one,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)] at hd
  norm_num at hd

#print axioms ym_A2_nonvacuous

/-- The sampled correlation window at orientation `d`, the base window transported by `Otr d`:
`F d = F₀ · Otr d`. The directional windows therefore relate by an orthogonal transport by
construction, and `Fym d' = Fym d · ((Otr d)ᵀ · Otr d')` is a theorem.

DERIVED: `4` is the spacetime dimension, so the window is a `4×4` matrix, as in `DYM`. -/
noncomputable def Fym (d : DYM) : Matrix (Fin 4) (Fin 4) ℝ := Fbase * Otr d

/-! ## The model instance -/

/-- A lattice Yang–Mills model witness. The tension read `μYM` and the directional Gram read supply
the two entropy-matched reads; the one-mode window with dominant magnitude `e^{-(κ₀-μ)}` supplies the
finite-aperture correlator. `κ` and `κ₀` are both set to `κ₀YM`, so `hfloor` is `le_refl`.

DERIVED: the `1` is the mode weight of a single-mode model — `P β k = 1` because there is one mode
and the weights sum to one. It is a normalisation forced by the structure, not a fitted value. -/
noncomputable def ymModel : LatticeYM where
  Idx := Unit
  Dir := DYM
  s := fun _ => (Finset.univ : Finset Unit)
  P := fun _ _ => 1
  m := fun β _ => ((Real.exp (-(κ₀YM - μYM β)) : ℝ) : ℂ)
  μ := μYM
  R := fun d => freadYM ((Fym d)ᵀ * Fym d).charpoly
  κ₀ := κ₀YM
  κ := κ₀YM
  hfloor := le_refl _
  hread := by
    intro β _ _
    have h : ‖((Real.exp (-(κ₀YM - μYM β)) : ℝ) : ℂ)‖ = Real.exp (-(κ₀YM - μYM β)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq h

/-! ## A1 and A2 as theorems -/

/-- `A2` for `ymModel`. The directional window `F d = F₀ · Otr d` transports by an orthogonal Nyquist
map, so its Gram `(F d)ᵀ (F d)` relates across orientations by an orthogonal congruence and the Gram
spectral read is direction-independent (`Apriori.continuumRotationCongruence_of_gram` and
`A2_continuum_of_congruence`). The sampling composition `F d' = F d · ((Otr d)ᵀ · Otr d')` is proved;
the input is that the transport is orthogonal (`Otr_iso`), the Nyquist–Shannon sampling isometry. -/
theorem ym_A2 : A2_YM ymModel := by
  show A2 (fun d => freadYM ((Fym d)ᵀ * Fym d).charpoly)
  refine A2_continuum_of_congruence freadYM (fun d => (Fym d)ᵀ * Fym d)
    (continuumRotationCongruence_of_gram Fym (fun d d' => (Otr d)ᵀ * Otr d') ?_ ?_)
  · intro d d'
    exact orthogonal_mul
      (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp (Otr_iso d)) (Otr_iso d')
  · intro d d'
    show Fbase * Otr d' = Fbase * Otr d * ((Otr d)ᵀ * Otr d')
    rw [← Matrix.mul_assoc, Matrix.mul_assoc Fbase (Otr d) ((Otr d)ᵀ),
      mul_eq_one_comm.mp (Otr_iso d), Matrix.mul_one]

/-! ## The model at a variable aperture, and the gap from the substrate -/

/-- The lattice Yang–Mills witness read through an aperture of size `N`. `ymModel` is its `nCorrYM`
instance (`ymModel_is_ymModelAt`, by `rfl`).

DERIVED: as in `ymModel`, the `1` is the single mode's weight, forced by normalisation. -/
noncomputable def ymModelAt (N : ℕ) : LatticeYM where
  Idx := Unit
  Dir := DYM
  s := fun _ => (Finset.univ : Finset Unit)
  P := fun _ _ => 1
  m := fun β _ => ((Real.exp (-(κ₀YM - μYMAt N β)) : ℝ) : ℂ)
  μ := μYMAt N
  R := fun d => freadYM ((Fym d)ᵀ * Fym d).charpoly
  κ₀ := κ₀YM
  κ := κ₀YM
  hfloor := le_refl _
  hread := by
    intro β _ _
    have h : ‖((Real.exp (-(κ₀YM - μYMAt N β)) : ℝ) : ℂ)‖ = Real.exp (-(κ₀YM - μYMAt N β)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq h

/-- The pinned model is the `nCorrYM` instance of the aperture-general one. -/
theorem ymModel_is_ymModelAt : ymModel = ymModelAt nCorrYM := rfl

/-- Isotropy holds at every aperture, since `R` does not depend on the aperture. -/
theorem ym_A2_at (N : ℕ) : A2_YM (ymModelAt N) := ym_A2

/-- Gap, non-triviality and `SO(4)` for `ymModelAt N` at every large enough aperture, from one
substrate hypothesis. From `∃ B, ∀ N β, d2At N β ≤ B` — an aperture-independent bound on the
substrate's moment about the circle distance, with no value supplied — the three conclusions hold at
every coupling, with no restriction to `β ≥ 0` and no coupling-by-coupling case split.

The hypothesis is a property of the substrate rather than a value measured through a particular
window. At a frozen window the corresponding statement is reached by splitting the coupling line into
arms and supplying a separate input on each (`ym_A1_of_grid`).

DERIVED: the `0` is the limit `nhds 0` the mode sum tends to, and the sign in
`(ymModelAt N).μ β - (ymModelAt N).κ < 0`. -/
theorem ym_mass_gap_of_substrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (∀ β, Filter.Tendsto
          (fun τ => ‖∑ k ∈ (ymModelAt N).s β,
            (ymModelAt N).P β k * ((ymModelAt N).m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
        (∀ β, (ymModelAt N).μ β - (ymModelAt N).κ < 0) ∧
        (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d') := by
  filter_upwards [confinement_of_bounded_substrate h] with N hN
  exact mass_gap_of_model (ymModelAt N) hN (ym_A2_at N)

#print axioms ym_mass_gap_of_substrate

/-- The same from the growth hypothesis: the substrate moment may grow with the aperture,
`substrateRatio ≤ c`, provided `c` clears the floor gap. A bounded moment is the special case.

DERIVED: `(2 * Real.pi) ^ 2 * c / 2 < 1 - 3 ^ (-(1 : ℝ) / 4)` is `confinement_at_of_ratio`'s own
threshold — the window squared, the cosine bound's denominator, and `e^{−κ₀}` at the floor
`κ₀ = ¼log3` — and `0` is the limit and the sign of the non-triviality clause. -/
theorem ym_mass_gap_of_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, substrateRatio N β ≤ c) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (∀ β, Filter.Tendsto
          (fun τ => ‖∑ k ∈ (ymModelAt N).s β,
            (ymModelAt N).P β k * ((ymModelAt N).m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
        (∀ β, (ymModelAt N).μ β - (ymModelAt N).κ < 0) ∧
        (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d') := by
  filter_upwards [confinement_of_growth_ratio hc h] with N hN
  exact mass_gap_of_model (ymModelAt N) hN (ym_A2_at N)

#print axioms ym_mass_gap_of_ratio

/-- Gap, non-triviality and `SO(4)` for `ymModelAt N` at every large enough aperture and every
coupling, from one hypothesis: the read's weights decay geometrically in the circle distance at some
rate `r < 1`. No aperture, no threshold and no value for `r` is named in the statement.

Under reflection positivity `ρ(d) = ∑ₙ wₙλₙᵈ` with `wₙ ≥ 0`, so the hypothesis is that the transfer
operator has a gap (`ZeroMode.exists_exponential_decay` supplies it from `λₙ < 1` on a finite mode
set, with `r` the largest excited eigenvalue). The steps between — the aperture-uniform moment bound,
the entropy floor comparison, the model assembly — carry the foundational three plus reflection
positivity.

DERIVED: `0 ≤ C` and `0 ≤ r` are sign conditions, `r < 1` the contraction, the `1` in `Fin (N + 1)`
the lag arity, and `0` also the limit `nhds 0`. -/
theorem ym_mass_gap_of_decay {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (readYMAt N β).p d ≤ C * r ^ (Moment.circLag d)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (∀ β, Filter.Tendsto
          (fun τ => ‖∑ k ∈ (ymModelAt N).s β,
            (ymModelAt N).P β k * ((ymModelAt N).m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
        (∀ β, (ymModelAt N).μ β - (ymModelAt N).κ < 0) ∧
        (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d') := by
  filter_upwards [confinement_of_geometric_decay hC hr0 hr1 hdecay] with N hN
  exact mass_gap_of_model (ymModelAt N) hN (ym_A2_at N)

#print axioms ym_mass_gap_of_decay

/-- Gap, non-triviality and `SO(4)` at every large enough aperture and every coupling, from the
hypothesis that the read's weights decay geometrically in the raw lag at some rate `r < 1`.

Under reflection positivity that hypothesis is a spectral gap on the transfer operator, with
`r = e^{−Δ}`: the correlation is `∑ₙ wₙλₙᵈ` with `wₙ ≥ 0`, and a gap is `λₙ ≤ e^{−Δ} < 1` on the
excited modes. No aperture, threshold or value for `r` appears in the statement or the proof, and the
gap itself is the caller's to supply.

DERIVED: `0 ≤ C` and `0 ≤ r` are sign conditions, `r < 1` the contraction, the `1` in `Fin (N + 1)`
the lag arity, and `0` also the limit `nhds 0`. -/
theorem ym_mass_gap_of_lag_decay {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (readYMAt N β).p d ≤ C * r ^ (d : ℕ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (∀ β, Filter.Tendsto
          (fun τ => ‖∑ k ∈ (ymModelAt N).s β,
            (ymModelAt N).P β k * ((ymModelAt N).m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
        (∀ β, (ymModelAt N).μ β - (ymModelAt N).κ < 0) ∧
        (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d') := by
  filter_upwards [confinement_of_lag_decay hC hr0 hr1 hdecay] with N hN
  exact mass_gap_of_model (ymModelAt N) hN (ym_A2_at N)

#print axioms ym_mass_gap_of_lag_decay

/-! ## The conditional forms at the pinned aperture -/

-- The axiom footprint of everything below: the standard three plus `wilson_reflection_positive_at`.
-- `Otr_iso` is a theorem (the O(4) membership of the Nyquist transport `OtrO`), and C-3 is the
-- theorem `readYM_is_wilson := rfl` (reading-A is the concrete `readA`, and
-- `readYM = readingA_wilson` by construction), so neither is in the footprint. What the footprint
-- shows is reflection positivity (Osterwalder–Seiler), the read-side physical input, named and
-- cited.

/-- Gap `C(τ) → 0`, non-triviality `μ − κ < 0` and `SO(4)` over an arbitrary mode family `m`, in
place of `ymModel.m := e^{−(κ₀−μ)}`. The read margin `hread` is discharged by
`Capacity.hread_of_junction` from three inputs: the modes decay at the transfer gap
`‖m_k‖ ≤ e^{−Δ}` (`hdom`), `κ₀ − μ ≤ c` (`hfe`, the centre-vortex free-energy junction — 't Hooft
1978 / Greensite 2003) and `c ≤ Δ` (`hgap`, the contraction rate lower-bounding the transfer gap).

Confinement enters as the hypothesis `hconf` and isotropy is the proved `A2` of `ymModel`, so the
footprint is the foundational three plus reflection positivity; `hfe` and `hgap` are hypotheses over
the free modes rather than axioms. `ym_mass_gap_of_decay_at_floor` shows the three are equivalent to
one.

Scope: the statement is at the pinned aperture and at nonnegative coupling only.

DERIVED: `0 ≤ β` restricts to nonnegative coupling, and `0` is also the limit `nhds 0` and the sign
in `μYM β - κ₀YM < 0`. -/
theorem ym_mass_gap_of_junction
    (hconf : ∀ β, 0 ≤ β → μYM β < κ₀YM)
    (m : ℝ → Unit → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, 0 ≤ β → κ₀YM - μYM β ≤ c β) (hgap : ∀ β, 0 ≤ β → c β ≤ Δ β) :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - κ₀YM < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') := by
  refine ⟨fun β hβ => ?_, fun β hβ => ?_, ym_A2⟩
  · exact gap_of_confinement (ymModel.s β) (ymModel.P β) (m β) κ₀YM (μYM β)
      (hconf β hβ)
      (Capacity.hread_of_junction (ymModel.s β) (m β) (hdom β hβ) (le_refl κ₀YM) (hfe β hβ) (hgap β hβ))
  · exact confines_of_tension_lt_floor (le_refl κ₀YM) (hconf β hβ)

#print axioms ym_mass_gap_of_junction

/-- The same conclusion from one hypothesis in place of `ym_mass_gap_of_junction`'s three.

`c` and `Δ` there are supplied by the caller, constrained only by `κ₀ − μ ≤ c`, `c ≤ Δ` and
`‖m‖ ≤ e^{−Δ}`. Taking `c = Δ = κ₀ − μ` makes the first two `le_refl` and leaves the third, so
`hdom ∧ hfe ∧ hgap` is implied by `hdecay` below; `decay_at_floor_of_junction` gives the converse,
since `‖m‖ ≤ e^{−Δ} ≤ e^{−c} ≤ e^{−(κ₀−μ)}` whenever the three hold. The two are equivalent, and the
single form says that the modes decay at least at the counted free-energy density.

DERIVED: `0 ≤ β` restricts to nonnegative coupling, and `0` is also the limit `nhds 0` and the sign
in `μYM β - κ₀YM < 0`. -/
theorem ym_mass_gap_of_decay_at_floor
    (hconf : ∀ β, 0 ≤ β → μYM β < κ₀YM)
    (m : ℝ → Unit → ℂ)
    (hdecay : ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β,
      ‖m β k‖ ≤ Real.exp (-(κ₀YM - μYM β))) :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - κ₀YM < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') :=
  ym_mass_gap_of_junction hconf m (fun β => κ₀YM - μYM β) (fun β => κ₀YM - μYM β)
    hdecay (fun _ _ => le_refl _) (fun _ _ => le_refl _)

/-- The converse direction: any `c` and `Δ` satisfying `ym_mass_gap_of_junction`'s three hypotheses
give the single decay statement, so the consolidation above is an equivalence.

DERIVED: `0 ≤ β` restricts to nonnegative coupling and is the only numeral in the statement. -/
theorem decay_at_floor_of_junction (m : ℝ → Unit → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, 0 ≤ β → κ₀YM - μYM β ≤ c β) (hgap : ∀ β, 0 ≤ β → c β ≤ Δ β) :
    ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β, ‖m β k‖ ≤ Real.exp (-(κ₀YM - μYM β)) := by
  intro β hβ k hk
  refine le_trans (hdom β hβ k hk) (Real.exp_le_exp.mpr ?_)
  have := le_trans (hfe β hβ) (hgap β hβ)
  linarith

#print axioms ym_mass_gap_of_decay_at_floor
#print axioms decay_at_floor_of_junction

/-! ## The floor as a parameter

`κ₀YM := ¼ log 3` is a literal, and `ymModel` sets `κ := κ₀YM` with `hfloor := le_refl _`, collapsing
two fields `LatticeYM` keeps apart: `κ₀`, a proved lower bound, and `κ`, the entropy density. Four
numbers sit in that neighbourhood, and they bound different families:

* `¼ log 3 = 0.2746531` — directed cube-paths. This is the one that is a proved lower bound on the
  vortex family the development counts (`Floor.directed_paths_card` and `CubeArea.boundary_card_eq`,
  carried to `Plaq 4 n` by `VortexFamily.three_pow_le_vortexCount`).
* `(11 log 3 + log 10)/48 = 0.2997358` — branched cube-trees (`CubeBranch.branch_floor_ten`). It is
  a bound on a different object: `vortexFamily` requires `IsClosedSurface`, `IsConnectedSurface` and
  membership in `Plaq 4 n`, while `CubeBranch.branched_surfaces_count_and_area` produces
  `Finset (Finset Face)` with `Face = Fin 3 × Cube`, the 3-D cube-boundary type. Connectedness of the
  branched boundary (disclosed in `CubeBranch`) and the 4-D embedding stand between them, and
  `plaqSurface`, `plaqSurface_closed` and `plaqSurface_connected` are written against a path
  `s : Fin k → Fin 3` rather than a general `Finset Cube`. `branch_floor_gt_pinned` is an inequality
  between two real numbers and says nothing about the families.
* `0.455483` — front-capped void-excluded animals, exact-rational Collatz–Wielandt
  (`certify/floor_ladder_exact.py`). Certified outside Lean, about the animal family.
* the surface connective constant puts the true limsup near `0.83`.

The theorems below take the floor as a parameter, so a conclusion follows at whichever of these is a
proved lower bound on the counted family. Every flagship above names `κ₀YM` directly. -/

/-- Clustering and non-triviality at a floor supplied as a parameter rather than as `¼ log 3`:
confinement below `κ₀` and mode decay at its own margin.

Direction of the parameter: raising `κ₀` weakens `hconf : μYM β < κ₀`, which asserts less, and
strengthens `hdecay`, whose modes must clear a bigger margin. The conclusion's first conjunct is the
same `Prop` for every `κ₀ > μ`, since `gap_of_confinement` needs only `‖m‖ < 1`; the second is
`hconf` restated.

This is `Aperture.gap_of_confinement` applied at `ymModel.s β` and `ymModel.P β`, that lemma already
being parameterised in `κ₀`.

DERIVED: `0 ≤ β` restricts to nonnegative coupling, and `0` is also the limit `nhds 0` and the sign
in `μYM β - κ₀ < 0`. -/
theorem ym_mass_gap_at_floor (κ₀ : ℝ)
    (hconf : ∀ β, 0 ≤ β → μYM β < κ₀)
    (m : ℝ → Unit → ℂ)
    (hdecay : ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β,
      ‖m β k‖ ≤ Real.exp (-(κ₀ - μYM β))) :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - κ₀ < 0) := by
  refine ⟨fun β hβ => ?_, fun β hβ => by have := hconf β hβ; linarith⟩
  exact gap_of_confinement (ymModel.s β) (ymModel.P β) (m β) κ₀ (μYM β) (hconf β hβ) (hdecay β hβ)

/-- The `κ₀ = ¼ log 3` instance of `ym_mass_gap_at_floor`.

Scope: the conclusion is a two-way conjunction. `ym_mass_gap_of_decay_at_floor` concludes a
three-way one ending `∀ d d', ymModel.R d = ymModel.R d'`, the `SO(4)` isotropy half, which
`gap_of_confinement` does not supply, so a caller needing isotropy uses that statement instead.

DERIVED: `0 ≤ β` restricts to nonnegative coupling, and `0` is also the limit `nhds 0` and the sign
in `μYM β - κ₀YM < 0`. -/
theorem ym_mass_gap_at_floor_is_the_pinned_one
    (hconf : ∀ β, 0 ≤ β → μYM β < κ₀YM)
    (m : ℝ → Unit → ℂ)
    (hdecay : ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β,
      ‖m β k‖ ≤ Real.exp (-(κ₀YM - μYM β))) :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - κ₀YM < 0) :=
  ym_mass_gap_at_floor κ₀YM hconf m hdecay

/-- The instance of `ym_mass_gap_at_floor` at `(11 log 3 + log 10)/48`.
`CubeBranch.branch_floor_ten` proves `¼ log 3 <` that number, so this instance has a weaker
confinement hypothesis than the pinned one, `μYM β <` a larger number asserting less.

Scope: that number bounds a different family from `vortexFamily`. `CubeBranch` counts branched
cube-trees in the 3-D `Face = Fin 3 × Cube` type, while `vortexFamily` lives in `Plaq 4 n` and
demands connectedness as well.

DERIVED: `(11 * Real.log 3 + Real.log 10) / 48` is `CubeBranch.branch_floor_ten`'s branched cube-tree
density, carried through unchanged; `0 ≤ β` restricts to nonnegative coupling and `0` is also the
limit `nhds 0` and the sign of the non-triviality clause. -/
theorem ym_mass_gap_at_branch_floor
    (hconf : ∀ β, 0 ≤ β → μYM β < (11 * Real.log 3 + Real.log 10) / 48)
    (m : ℝ → Unit → ℂ)
    (hdecay : ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β,
      ‖m β k‖ ≤ Real.exp (-((11 * Real.log 3 + Real.log 10) / 48 - μYM β))) :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - (11 * Real.log 3 + Real.log 10) / 48 < 0) :=
  ym_mass_gap_at_floor _ hconf m hdecay

/-- An inequality between two real numbers, `¼ log 3 < (11 log 3 + log 10)/48`, named here so the
arithmetic is visible beside the statements that use it. It says nothing about which family either
number bounds.

DERIVED: `(11 * Real.log 3 + Real.log 10) / 48` is `CubeBranch.branch_floor_ten`'s branched
cube-tree density, carried through unchanged. -/
theorem branch_floor_gt_pinned : κ₀YM < (11 * Real.log 3 + Real.log 10) / 48 :=
  CubeBranch.branch_floor_ten

#print axioms ym_mass_gap_at_floor
#print axioms ym_mass_gap_at_floor_is_the_pinned_one
#print axioms ym_mass_gap_at_branch_floor
#print axioms branch_floor_gt_pinned

/-! ## The gap stated about the Wilson correlation

`ym_mass_gap_of_decay_at_floor` quantifies over an arbitrary `m : ℝ → Unit → ℂ`, and `ymModel`
instantiates it at one element with `m` defined equal to its own bound. Read at that instance, its
clustering conclusion is that a single complex number of modulus below one has powers tending to
zero, and its hypothesis is about a parameter with no proved link to the ensemble;
`Apriori.hread_of_dominant`, the lemma downstream of it, is `le_trans`.

The statements below say the same gap about the Wilson correlation.
`Spectral.PeriodicSpectralForm (N+1) (wilsonCorrAt N β)` is the transfer-matrix decomposition on a
circle, `ρ(d) = ∑ₖ wₖ (λₖ^d + λₖ^{n−d})` with `wₖ ≥ 0`. With it, `P` and `m` are not supplied: they
are `w` and `λ`, the correlator is `wilsonCorrAt N β` at every resolved lag, and the decay hypothesis
is that every transfer energy clears `κ₀ − μ`.

The half-line shape `∑ w λ^d` is not available here: this lattice is a periodic torus, `ρ` is
symmetric under `d ↦ n−d`, and `Spectral.flat_of_aperiodic` proves that a half-line shape plus that
symmetry forces `ρ` flat from lag one.

The hypothesis is thereby a property of a defined object rather than a bound on a free family. -/

/-- The proposition that the Wilson correlation at aperture `N` and coupling `β` admits a periodic
transfer-matrix decomposition with nonnegative weights.

The shape is `ρ(d) = ∑ₖ wₖ (λₖ^d + λₖ^{n−d})` with `n = N+1`, not the half-line `∑ w λ^d`.
`WilsonHypercubic.Site` is `Fin d → Fin n` and `shift` adds in `Fin n`, so the lattice is a periodic
torus; `wilsonCorrAt N β = corrClay (N+1) β` with the lag running the whole period; and
`ρ(d) = ρ(n−d)` is proved, by `MomentShape.corrHyper_neg` and `wilsonCorrAt_neg`, at every extent and
every real coupling with no hypothesis, so `Moment.circLag` reads the correlation correctly
(`MomentShape.wilsonCorrAt_circLag_congr`). `ZeroMode`'s `d ↦ n − d` symmetry is a different
statement, about `clag` rather than about `ρ`. With the symmetry proved,
`Spectral.flat_of_aperiodic` forces a half-line `ρ` flat from lag one; that lemma assumes `1 ≤ d` and
leaves a contact term at lag zero free.

DERIVED: the period `N+1` is forced by `WilsonHypercubic.Site = Fin d → Fin n` with `shift` adding in
`Fin n`, so it is the aperture's own circumference. `w ≥ 0` is reflection positivity's content, and
`λ ∈ [0,1]` is `0 ≤ T ≤ 1` — the lower end from positivity, the upper from contractivity of a
probability measure's transfer operator, a normalisation rather than a gap.

Who supplies it. `SlabQuadratic.wilsonSpectral` supplies `WilsonSpectral 3 β` for every `β ≥ 0` from
two reflection-positivity instances and no operator, foundational axioms only; `N` there is the
literal `3`, so that producer covers one aperture at every nonnegative coupling.
`Spectral2.wilsonSpectral_at_zero_coupling` covers every aperture at `β = 0`. Nothing supplies both,
and nothing supplies `β < 0`.

What it supplies is existence: the `Prop` is `Nonempty`, carrying no mode count and no rate, and
`SpectralFour.fourRepresentable_const` proves the constant triple representable, so it does not on
its own separate a gapped correlation from a flat one. The measured correlator does not adjudicate
it either: the ensemble's bin count leaves fewer degrees of freedom than the error model such a test
has parameters, and the mid-range lags carry no signal. That arithmetic lives with the read, in
`code/8_7_run_gap_correlator.py`. -/
def WilsonSpectral (N : ℕ) (β : ℝ) : Prop :=
  Nonempty (Spectral.PeriodicSpectralForm (N + 1) (wilsonCorrAt N β))

/-- Given the decomposition, the periodic spectral sum equals the ensemble's correlation at every
lag the period resolves.

DERIVED: the `1` is the period offset — `Fin (N + 1)` indexes the lags and `(N + 1) - (d : ℕ)` is the
reflected lag on the circle. -/
theorem wilson_sum_eq_corr {N : ℕ} {β : ℝ}
    (S : Spectral.PeriodicSpectralForm (N + 1) (wilsonCorrAt N β)) (d : Fin (N + 1)) :
    ∑ k, S.w k * ((S.lam k) ^ (d : ℕ) + (S.lam k) ^ ((N + 1) - (d : ℕ)))
      = wilsonCorrAt N β d :=
  Spectral.sum_eq_rho S d

/-- Decay of the Wilson correlation out to half the period, from a gap on the transfer spectrum.

Scope: the conclusion is stated under `hhalf : 2 * (d : ℕ) ≤ N + 1`. Past `n/2` the periodic
correlation turns back up, so no bound of this shape holds there, and no periodic correlator tends to
zero. Clustering in the `n → ∞` sense is a separate statement.

The gap hypothesis `hgap` is restricted to modes of nonzero weight. `Transfer.one_le_of_eigenvalues_le`
proves that a bound on every transfer eigenvalue forces that bound to be at least one, because the
vacuum sits at eigenvalue exactly one with weight `‖Ω‖²`. The connected correlator is the case where
the vacuum weight vanishes, the disconnected part being the vacuum contribution.

DERIVED: `S.w k ≠ 0` selects the contributing modes; `2 * (d : ℕ) ≤ N + 1` is half the period; the
`2` in `2 * (∑ k, S.w k)` is the two sides of the circle in `Spectral.periodic_decay_le`; and
`N + 1` is the period. -/
theorem ym_wilson_decay_to_half_period {N : ℕ} {β : ℝ}
    (S : Spectral.PeriodicSpectralForm (N + 1) (wilsonCorrAt N β))
    (hgap : ∀ k, S.w k ≠ 0 → S.lam k ≤ Real.exp (-(κ₀YM - μYMAt N β)))
    (d : Fin (N + 1)) (hhalf : 2 * (d : ℕ) ≤ N + 1) :
    wilsonCorrAt N β d ≤ 2 * (∑ k, S.w k) * Real.exp (-(κ₀YM - μYMAt N β)) ^ (d : ℕ) :=
  Spectral.periodic_decay_le S hgap (Real.exp_pos _).le d hhalf

#print axioms wilson_sum_eq_corr
#print axioms ym_wilson_decay_to_half_period

/-- Gap, non-triviality and `SO(4)` for `ymModel` from the single hypothesis `hconf`: the tension
stays below the floor at every nonnegative coupling, `∀ β, 0 ≤ β → μYM β < κ₀YM`. That is equivalent
to `contrast < 3^{1/4}` (`Certify.confinement_iff_contrast_lt_rpow`).

`#print axioms` reports the three foundational axioms plus `wilson_reflection_positive_at` (via
`ymModel.μ`) and nothing else; `rArgYM_pos` is a theorem. This is the conditional form at the pinned
aperture. `hconf` is supplied either by the substrate route above
(`confinement_of_bounded_substrate`, stated at a variable aperture) or by measurement: su2/su3 read
`μ ≈ 0` against `κ₀` with a finite-aperture margin `m_hi ≈ 0.18 < 3^{-1/4}`, and U(1) tracks its own
transition, the confined phase below `β_c` reading a finite aperture and the Coulomb phase reading
`m_hi ≈ 1` (`research/code` runtime probe, PAPER §9). The finite aperture is structural in `ymModel`,
which carries one mode; the margin certificate is the evidence that the SU(N) ensemble is that
finite-mode model.

DERIVED: `0 ≤ β` restricts to nonnegative coupling, and `0` is also the limit `nhds 0` and the sign
in `ymModel.μ β - ymModel.κ < 0`. -/
theorem ym_mass_gap_certified (hconf : ∀ β, 0 ≤ β → μYM β < κ₀YM) :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (ymModel.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → ymModel.μ β - ymModel.κ < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') := by
  refine ⟨fun β hβ => ?_, fun β hβ => ?_, ym_A2⟩
  · exact gap_of_confinement (ymModel.s β) (ymModel.P β) (ymModel.m β) ymModel.κ₀ (ymModel.μ β)
      (hconf β hβ) (ymModel.hread β)
  · exact confines_of_tension_lt_floor ymModel.hfloor (hconf β hβ)

#print axioms ym_mass_gap_certified

/-- The tension is nonnegative, unconditionally. `μYMAt N β = -log ⟨cos θ⟩_p` with `p` a probability
vector, so `⟨cos θ⟩_p ∈ [-1,1]` and its logarithm is at most zero. Foundational axioms only. -/
theorem μYMAt_nonneg (N : ℕ) (β : ℝ) : 0 ≤ μYMAt N β := by
  unfold μYMAt
  set R := readYMAt N β
  have hcos : ∀ d, |R.p d * Real.cos (R.θ d)| ≤ R.p d := by
    intro d
    rw [abs_mul, abs_of_nonneg (R.p_nonneg d)]
    exact mul_le_of_le_one_right (R.p_nonneg d) (Real.abs_cos_le_one _)
  have habs : |∑ d, R.p d * Real.cos (R.θ d)| ≤ 1 :=
    le_trans (Finset.abs_sum_le_sum_abs _ _)
      (le_trans (Finset.sum_le_sum (fun d _ => hcos d)) (le_of_eq R.p_sum))
  have hlog : Real.log (∑ d, R.p d * Real.cos (R.θ d)) ≤ 0 := by
    rw [← Real.log_abs]; exact Real.log_nonpos (abs_nonneg _) habs
  show 0 ≤ - Real.log (∑ d, R.p d * Real.cos (R.θ d))
  linarith

/-- The `nCorrYM` instance of `μYMAt_nonneg`. -/
theorem μYM_nonneg (β : ℝ) : 0 ≤ μYM β := μYMAt_nonneg nCorrYM β

/-! ## The gap as an entropy surplus, and its decay margin

The construction runs from the aperture outward, its inverse a fibre (PAPER §12). The gap is the
entropy surplus `Δ = κ₀ − μ`, and confinement `μ < κ₀` is `Δ > 0`, the disorder entropy density above
the tension. -/

/-- The mass gap as the **entropy surplus** `Δ(β) = κ₀ − μ(β)`: the centre-vortex disorder entropy
density above the tension. -/
noncomputable def ΔYM (β : ℝ) : ℝ := κ₀YM - μYM β

/-- `ΔYM β > 0` exactly when the tension is below the floor, `μYM β < κ₀YM`. Foundational axioms
only.

DERIVED: `0 < ΔYM β` is the sign of the surplus, the only numeral in the statement. -/
theorem gap_pos_iff_confinement (β : ℝ) : 0 < ΔYM β ↔ μYM β < κ₀YM := by
  unfold ΔYM; constructor <;> intro h <;> linarith

/-- The decay factor `e^{−Δ}` is strictly inside the unit disk exactly when the surplus is positive,
so the band-limited screen forgets at the surplus rate.

DERIVED: `1` is the unit modulus `Real.exp 0` and `0 < ΔYM β` the sign of the surplus. -/
theorem oneway_margin (β : ℝ) : Real.exp (-(ΔYM β)) < 1 ↔ 0 < ΔYM β := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- Confinement gives a positive surplus: from `μYM β < κ₀YM` at nonnegative coupling, `ΔYM β > 0`.

DERIVED: `0 ≤ β` restricts to nonnegative coupling and `0 < ΔYM β` is the conclusion's sign. -/
theorem entropy_surplus_pos (hconf : ∀ β, 0 ≤ β → μYM β < κ₀YM) (β : ℝ) (hβ : 0 ≤ β) : 0 < ΔYM β :=
  (gap_pos_iff_confinement β).mpr (hconf β hβ)

/-! ## The spectral form: the gap as decay of a mode family

No magnitude and no family size is named below. The finite-aperture margin
`‖m_k‖ ≤ 3^{-1/4} = e^{-κ₀}` is a hypothesis over an arbitrary mode family rather than a property of
a chosen witness. The ceiling is derived: `3^{-1/4}` is `e^{-κ₀}` with `κ₀ = ¼log3` proved in
`Floor`, and its physical grounding is the exact-rational single-plaquette enclosure
(`certify/small_volume_enclosure.py`), a certificate outside the Lean footprint.

`spectral_bar_nonvacuous` exhibits the hypothesis satisfied, at any family size and any magnitude in
`(0, 3^{-1/4}]`, without naming a value. -/

/-- The gap as decay of an arbitrary finite mode family, at an arbitrary aperture. For any finite
set of transfer or DMD modes `m : ι → ℂ`, read through an aperture of size `N` at a coupling whose
tension is below the floor, if the dominant magnitude is at or below the entropy-floor ceiling
`m_hi ≤ 3^{-1/4} = e^{-κ₀}` then `‖∑ P_k m_k^τ‖ → 0`.

Since `3^{-1/4} = e^{-κ₀} ≤ e^{-(κ₀-μ)}` for `μ ≥ 0` (`μYMAt_nonneg`), the margin supplies the
finite-aperture premise of `gap_of_confinement`. The margin hypothesis is read per ensemble: the
`SU(N)` DMD read satisfies it (measured `m_hi ≈ 0.18–0.30`) and the `U(1)`-Coulomb read
(`m_hi ≈ 1`, a persistent unit-circle mode) does not.

DERIVED: `3 ^ (-(1 : ℝ) / 4)` is `e^{-κ₀}` at the floor `κ₀ = ¼log3` counted in `Floor`, and `0` is
the limit `nhds 0`. `mhi`, `s`, `P` and `m` are variables. -/
theorem ym_mass_gap_spectral {ι : Type*} (N : ℕ) (s : Finset ι) (P m : ι → ℂ) (β mhi : ℝ)
    (hconf : μYMAt N β < κ₀YM) (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi)
    (haperture : mhi ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) := by
  refine gap_of_confinement s P m κ₀YM (μYMAt N β) hconf (fun k hk => ?_)
  refine le_trans (hmargin k hk) (le_trans haperture ?_)
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    unfold κ₀YM; congr 1; ring
  rw [h3]
  exact Real.exp_le_exp.mpr (by have := μYMAt_nonneg N β; linarith)

#print axioms ym_mass_gap_spectral

/-- A fixed geometric family decays at every volume index `F` at once, for any family size and any
magnitude at or below the ceiling, with a positive rate `κ` fixed before `F` is chosen.

Scope: neither the rate nor the volume index carries content here.
`VolumeRate.ym_gap_uniform_in_volume_shape_is_vacuous` reproduces this conclusion and proves it
equivalent to a single `Tendsto`, the summand being independent of `F`. The bound is intensive by
hypothesis. This is a statement about the mode side with no read in it; foundational axioms only.

The corresponding statement about the read — that the entropy-matched read of the `SU(N)` ensemble is
intensive, `∃ r<1, ∀F, m_hi(F) ≤ r` — is the separate input named in `Interior`.

DERIVED: `0 < x` and `x ≤ 3 ^ (-(1 : ℝ) / 4)` bound the magnitude by `e^{-κ₀}` at the floor
`κ₀ = ¼log3`; `Fin (n + 1)` is the family size; `(1 : ℂ)` is the uniform weight; `0` is the limit and
the sign of `κ`. -/
theorem ym_gap_uniform_in_volume (n : ℕ) (x : ℝ) (hx0 : 0 < x)
    (hx : x ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ _F : ℕ,
      Filter.Tendsto
        (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * ((x : ℂ)) ^ τ‖) Filter.atTop (nhds 0) := by
  have hlt1 : x < 1 := by have := Moment.floor_rhs_pos; linarith
  exact gap_uniform_in_volume_of_intensive
    (s := fun _ => (Finset.univ : Finset (Fin (n + 1)))) (P := fun _ _ => (1 : ℂ))
    (μ := fun _ _ => ((x : ℂ))) (μ₁ := fun _ => x) (r := x) hx0 hlt1
    (fun _ => le_refl x) (fun _ _ _ => le_of_eq (Complex.norm_of_nonneg hx0.le))

#print axioms ym_gap_uniform_in_volume

/-- The three conclusions in spectral form, at every coupling `β ≥ 0`: decay of an arbitrary finite
mode family carrying the margin, non-triviality `μ − κ₀ < 0` from the supplied confinement read, and
`SO(4)` invariance (`ym_A2_at`). The aperture, the mode family and the magnitude are all variables.

DERIVED: `0 ≤ β` restricts to nonnegative coupling, `3 ^ (-(1 : ℝ) / 4)` is `e^{-κ₀}` at the floor
`κ₀ = ¼log3`, and `0` is also the limit and the sign of the non-triviality clause. -/
theorem ym_mass_gap_spectral_bar {ι : Type*} (N : ℕ) (s : Finset ι) (P m : ι → ℂ) (mhi : ℝ)
    (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM) (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi)
    (haperture : mhi ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    (∀ β : ℝ, 0 ≤ β → Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYMAt N β - κ₀YM < 0) ∧
      (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d') :=
  ⟨fun β hβ => ym_mass_gap_spectral N s P m β mhi (hconf β hβ) hmargin haperture,
    fun β hβ => confines_of_tension_lt_floor (le_refl κ₀YM) (hconf β hβ), ym_A2_at N⟩

#print axioms ym_mass_gap_spectral_bar

/-- The margin hypothesis of `ym_mass_gap_spectral` is satisfiable at any family size and any
magnitude strictly positive and at or below the ceiling `3^{-1/4} = e^{-κ₀}`, and the decay it asks
for follows. The magnitude is a variable, so this covers every such instance rather than one.
Foundational axioms only.

DERIVED: `0 < x` and `x ≤ 3 ^ (-(1 : ℝ) / 4)` bound the magnitude by `e^{-κ₀}` at the floor
`κ₀ = ¼log3`; `Fin (n + 1)` is the family size; `(1 : ℂ)` is the uniform weight; `0` is also the
limit `nhds 0`. -/
theorem spectral_bar_nonvacuous (n : ℕ) (x : ℝ) (hx0 : 0 < x)
    (hx : x ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    Filter.Tendsto
      (fun τ => ‖∑ _k : Fin (n + 1), (1 : ℂ) * ((x : ℂ)) ^ τ‖) Filter.atTop (nhds 0) := by
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]; unfold κ₀YM; congr 1; ring
  exact gap_at_finite_F Finset.univ (fun _ => (1 : ℂ)) (fun _ => ((x : ℂ))) κ₀YM_pos
    (fun _ _ => by
      rw [Complex.norm_of_nonneg hx0.le]
      exact le_trans hx (le_of_eq h3))

#print axioms spectral_bar_nonvacuous

/-- The reconstructed Hamiltonian has mass gap `κ₀`. For a self-adjoint Euclidean-time transfer
operator `T` whose spectrum sits in `{1} ∪ [ε, 3^{-1/4}]` — the vacuum eigenvalue `1` and the excited
spectrum at or below the entropy-floor ceiling `3^{-1/4} = e^{-κ₀}` — the reconstructed Hamiltonian
`H = -log T` (continuous functional calculus, `Reconstruction.hamiltonian`) is self-adjoint and
nonnegative, has `0` in its spectrum, and satisfies `spectrum H ⊆ {0} ∪ [κ₀, ∞)`. Foundational
axioms only (`Reconstruction.reconstruct_qm_core`).

DERIVED: `1` is the vacuum eigenvalue, `0 < ε` the positive lower end of the excited band,
`3 ^ (-(1 : ℝ) / 4)` its upper end `e^{-κ₀}` at the floor `κ₀ = ¼log3`, and `0` the vacuum energy in
the conclusion. -/
theorem ym_reconstructed_gap {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (T : A) {ε : ℝ} (hT : IsSelfAdjoint T) (hε : 0 < ε) (h1 : (1 : ℝ) ∈ spectrum ℝ T)
    (hsp : spectrum ℝ T ⊆ {1} ∪ Set.Icc ε ((3 : ℝ) ^ (-(1 : ℝ) / 4))) :
    IsSelfAdjoint (Reconstruction.hamiltonian T) ∧ 0 ≤ Reconstruction.hamiltonian T ∧
      (0 : ℝ) ∈ spectrum ℝ (Reconstruction.hamiltonian T) ∧
      spectrum ℝ (Reconstruction.hamiltonian T) ⊆ {0} ∪ Set.Ici κ₀YM := by
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]; unfold κ₀YM; congr 1; ring
  rw [h3] at hsp
  exact Reconstruction.reconstruct_qm_core T hT hε κ₀YM_pos h1 hsp

#print axioms ym_reconstructed_gap

-- The interior crossover confinement discharged by a finite grid plus a Lipschitz constant, leaving
-- the foundational three and `wilson_reflection_positive_at` (via `readYM`).
#print axioms ym_crossover_confinement_of_grid

/-- `A1_YM ymModel`, i.e. `∀ β, μYM β < κ₀YM`, by case analysis on three pieces supplied by the
caller: the strong end `β < βloYM` (`hstrong`, reachable from `apriori_A1_strong` and a cited
character bound), the compact interior `β ∈ [βloYM, bhi]` (`hinterior`, supplied by
`ym_crossover_confinement_of_grid`), and the weak end `β ≥ bhi` (`hweak`, reachable from a cited
asymptotic-freedom convergence). All three are hypotheses, so no axiom is added here. -/
theorem ym_A1_of_grid {bhi : ℝ}
    (hstrong : ∀ β, β < βloYM → μYM β < κ₀YM)
    (hinterior : ∀ β ∈ Set.Icc βloYM bhi, μYM β < κ₀YM)
    (hweak : ∀ β, bhi ≤ β → μYM β < κ₀YM) :
    A1_YM ymModel := by
  show ∀ β, μYM β < κ₀YM
  intro β
  rcases lt_or_ge β βloYM with h | h
  · exact hstrong β h
  · rcases le_or_gt β bhi with h2 | h2
    · exact hinterior β ⟨h, h2⟩
    · exact hweak β (le_of_lt h2)

/-- Gap, non-triviality and `SO(4)` for `ymModel` from the two ends (`hstrong`, `hweak`) and the
interior (`hinterior`). No bound on the substrate is asserted: the interior
`∀ β ∈ [βloYM, bhi], μYM β < κ₀YM` is supplied by `ym_crossover_confinement_of_grid`, a finite grid
of deterministic `⟨d²⟩` reads plus a modulus-of-continuity bound `L`, backed by the dense-β data
(`certify/ym_crossover_confinement_of_grid.py`), continuity being a finite-volume analyticity
theorem. Where the substrate route takes a property of the correlation, this one takes a finite
measured grid.

DERIVED: `0` is the limit `nhds 0` the mode sum tends to and the sign in
`ymModel.μ β - ymModel.κ < 0`. -/
theorem ym_mass_gap_grid_certified {bhi : ℝ}
    (hstrong : ∀ β, β < βloYM → μYM β < κ₀YM)
    (hinterior : ∀ β ∈ Set.Icc βloYM bhi, μYM β < κ₀YM)
    (hweak : ∀ β, bhi ≤ β → μYM β < κ₀YM) :
    (∀ β, Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (ymModel.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, ymModel.μ β - ymModel.κ < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') :=
  mass_gap_of_model ymModel (ym_A1_of_grid hstrong hinterior hweak) ym_A2

#print axioms ym_mass_gap_grid_certified

end MassGap
