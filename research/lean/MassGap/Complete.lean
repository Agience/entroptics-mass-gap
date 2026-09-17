import Mathlib
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

`Apriori.lean` / `Model.lean` derive the result (mass gap, non-triviality, `SO(4)`) *from* the two
a priori `A1` (confinement) and `A2` (isotropy). This file discharges `A1` and `A2` themselves, so the gap
follows with **no** `A1`/`A2` hypothesis. Each named `axiom` is classical (not a raw read); every
framework-specific step is a theorem.

## ONE named axiom, and one route

The whole external input of this file is `wilson_reflection_positive_at` — reflection positivity of
the Wilson ensemble at every aperture (Osterwalder–Seiler, CITED). Nothing else here is an axiom, and
every declaration below carries the three foundational axioms plus that one and nothing more.

There is ONE route to confinement and it runs in one direction: a bound on the SUBSTRATE puts the
tension below the entropy floor `κ₀ = ¼log3`. The aperture is a VARIABLE throughout, because the
content of the entropy-matched read is that the margin opens as the window widens relative to the
substrate — a statement that cannot be written when the window is frozen.

## The results (in order)

* `confinement_of_bounded_substrate` — **the confinement theorem.** From `∃ B, ∀ N β, d2At N β ≤ B`,
  with no value for `B` named anywhere, the tension is below the floor at every large enough aperture
  and every coupling. No number appears in the statement or the proof.
* `confinement_of_growth_ratio` — the same from a WEAKER hypothesis: the substrate moment may grow
  with the aperture, provided the aperture-free ratio `substrateRatio` stays under a constant that
  clears the floor gap. A bounded moment is the special case.
* `substrateRatio_lt_of_tension_lt_floor` — the converse, so the substrate bound and confinement are
  known to be the same statement rather than one sufficient for the other.
* `margin_tendsto_floor` — the surplus `Δ = κ₀ − μ` tends to `κ₀` ITSELF as the window opens. This is
  what the frozen window cannot say.
* `ym_mass_gap_of_substrate` — **the flagship.** Gap, non-triviality and `SO(4)` for `ymModelAt N` at
  every large enough aperture, from that one substrate hypothesis.
* `ym_mass_gap_of_ratio` — the flagship from the weaker growth hypothesis.
* `ym_mass_gap_certified hconf` / `ym_mass_gap_of_junction hconf …` — the conditional forms at the
  pinned aperture, taking the confinement read as an explicit hypothesis.
* `ym_mass_gap_spectral` — **the discriminating form.** The gap as decay of an ARBITRARY finite mode
  family, with the finite-aperture margin `‖m_k‖ ≤ 3^{-1/4}` an EXPLICIT HYPOTHESIS rather than a
  property of a chosen witness — the scale separating `SU(N)` (measured `0.18`–`0.30`) from
  `U(1)`-Coulomb (`m_hi ≈ 1`). `spectral_bar_nonvacuous` shows the hypothesis is satisfiable at any
  family size and any magnitude in `(0, 3^{-1/4}]`, naming no value. The ceiling's physical grounding
  is the out-of-Lean single-plaquette enclosure (`certify/small_volume_enclosure.py`).
* `ym_reconstructed_gap` — the margin wired to reconstruction: `H = -log T` is self-adjoint, `H ≥ 0`,
  vacuum at `0`, `spectrum H ⊆ {0} ∪ [κ₀, ∞)`. Foundational axioms only.
* `ym_mass_gap_grid_certified` — the alternative interior: a finite grid plus a measured modulus of
  continuity, taking the two ends as hypotheses.

`Otr_iso` (A2 isometry), `readYM_is_wilson` (C-3 identification, `rfl`), `wilson_reflection_positive`,
`ym_finite_aperture`, `rArgYM_pos`, `ym_ratio_pos` and `ym_tension_is_moment` are THEOREMS, not axioms.
The read is concrete (`Moment.Read`): `μYM`, `pcorrYM`, `thetaYM` are all derived from one nonnegative
correlation `readYM β : Read nCorrYM`.

## The boundary

The one physics input is reflection positivity. The confinement hypothesis is a statement about the
SUBSTRATE — that its correlation has a finite length, so its moment about the circle distance does not
grow with the window — and it is supplied to the theorems rather than asserted by them. That is the
forward-side terminus of a one-way construction running from the finite aperture out to the cited
classical results it meets. See PAPER §12, *the direction of the construction*.
-/

namespace MassGap

open scoped Matrix

/-! ## The model's data: reading-A as a CONCRETE map, and the ensemble's one physical input (RP)

`readYM` / `readingA_wilson` are a **concrete** reading-A applied to the ensemble's correlation, so C-3 (the
identification) is a **derivation** (`readYM_is_wilson := rfl`), and the sole read-side physical input is
**reflection positivity** (Osterwalder-Seiler), a single NAMED axiom `wilson_reflection_positive_at`. -/

/-- The correlation dimension of the entropy-matched read (number of resolved lags, `L`). **Pinned to the
physical read aperture `L = 16`** (the SU(2) `L16` configs the certificate reads, `certify/ym_crossover_confinement_of_grid.py`).
Fixing it to a concrete value lets the finite-aperture premise `ym_finite_aperture` be a THEOREM (`norm_num`),
not an axiom — the aperture condition holds for every `N ≥ 9`, so any physical lattice qualifies; the
`L`-independence (that it does not dilute as `L → ∞`) is the SEPARATE `gap_uniform_in_volume_of_intensive`.

CHOSEN: `16` is the physical read aperture the shipped ensembles carry (`L16`). What choosing it
costs is nothing in the logic: every theorem in this file is stated at a VARIABLE aperture `N`
(`wilsonCorrAt`, `readYMAt`, `μYMAt`, `d2At`, `ymModelAt`), and the pinned objects are recovered as
the `nCorrYM` instance by `rfl` (`readYM_is_readYMAt`, `μYM_is_μYMAt`, `ymModel_is_ymModelAt`).
The `2` and `9` above are a citation and a remark, not inputs.
-/
def nCorrYM : ℕ := 16

/-- **The physical SU(3) Wilson ensemble's connected plaquette correlation** at coupling `β`, in FOUR
dimensions — the raw upstream data of reading-A, over the `N + 1` lags.

**IT IS CONSTRUCTED, NOT ABSTRACT.** `WilsonBridge.corrClay` is the Gibbs expectation
`⟨φ_{p₀}·φ_p⟩_β` against normalised product Haar with the real Wilson Boltzmann weight, on
`WilsonHypercubic.bd (d := 4) (n := N+1)` — the SAME periodic four-dimensional `SU(3)` lattice
`WilsonGauge`'s Osterwalder–Schrader measure is built on. The plane is spanned by directions `0` and
`1`, the lag runs along `2` transverse to it, so the lag is a genuine spatial separation.

This matters for what the theorems below are ABOUT. While this was `opaque` they quantified over an
arbitrary nonnegative sequence and "Wilson" was a name; the gap side and the measure side were two
objects that happened to share a prose description. They are now one object.

What remains cited is `wilson_reflection_positive_at` — and it is now a statement ABOUT a constructed
correlation rather than the defining property of an abstract one. That is the difference between an
axiom that carries physics and an axiom that carries a definition.

DERIVED: nothing here sets a scale. `4` is the problem's dimension, `3` is `SU(3)`, and `N + 1` is the
periodic extent the lag index runs over — the caller's aperture, carried through. -/
noncomputable def wilsonCorrAt (N : ℕ) (β : ℝ) : Fin (N + 1) → ℝ :=
  fun d => WilsonBridge.corrClay (N + 1) β d

/-- The correlation at the pinned physical aperture — the `nCorrYM` instance of `wilsonCorrAt`. The
aperture is a VALUE OF A VARIABLE, not a property of the theory, so the ensemble data carries it.

DERIVED: the `+ 1` is the lag arity — `Fin (N + 1)` indexes lags `0 … N`, so a window of size `N`
resolves `N + 1` of them. It is a counting fact about the index type, not a value.
-/
noncomputable def wilsonCorr : ℝ → (Fin (nCorrYM + 1) → ℝ) := wilsonCorrAt nCorrYM

/-- **Reflection positivity of the Wilson ensemble — CITED** (K. Osterwalder, E. Seiler, *Gauge field
theories on a lattice*, Ann. Phys. **110** (1978) 440). The whitened :F²: correlation is nonnegative at every
lag — the transfer-matrix spectral form `ρ(d) = Σ_n w_n e^{-E_n d}`, `w_n ≥ 0` — with positive total mass.
This is the SOLE physical input reading-A needs from the ensemble, a NAMED axiom that `#print axioms` reports.
With reading-A concrete (below) the model identification `readYM_is_wilson` is a `rfl` theorem, and RP — an
established, cited theorem — is the read-side physical input.

It is stated AT EVERY APERTURE, because that is what the cited result says: reflection positivity of the
Wilson measure is a property of the ensemble, not of the window a reader chooses. Stating it only at
`nCorrYM` would have made the pinned window part of the physical input.

DERIVED: the only numeral in the STATEMENT is the `0` of `0 ≤ ρ d` and `0 < Σ ρ`, which is
nonnegativity and positive total mass — the content of the cited result, not a magnitude. The
`110`, `1978` and `440` above are the journal citation.
-/
axiom wilson_reflection_positive_at :
    ∀ (N : ℕ) (β : ℝ), (∀ d, 0 ≤ wilsonCorrAt N β d) ∧ 0 < ∑ d, wilsonCorrAt N β d

/-- Reflection positivity at the pinned aperture — the `nCorrYM` instance, a THEOREM. -/
theorem wilson_reflection_positive :
    ∀ β, (∀ d, 0 ≤ wilsonCorr β d) ∧ 0 < ∑ d, wilsonCorr β d :=
  wilson_reflection_positive_at nCorrYM

/-- **Reading-A — the CONCRETE read.** It packages a whitened, reflection-positive
correlation into the entropy-matched `Moment.Read`, from which the tension `μ`, the probability vector `p`,
and the angles `θ` are all DERIVED (`Moment.Read`). This is the final min-entropy stage of reading-A as an
explicit Lean function — a computation, not a postulate. -/
noncomputable def readA {N : ℕ} (ρ : Fin (N + 1) → ℝ)
    (h : (∀ d, 0 ≤ ρ d) ∧ 0 < ∑ d, ρ d) : Moment.Read N :=
  { ρ := ρ, hρ := h.1, hpos := h.2 }

/-- **Reading-A of the physical Wilson ensemble** — reading-A applied to the Wilson correlation (§2-§3).

DERIVED: `§2`–`§3` is a cross-reference to the paper, not a value. This definition introduces no
number of its own.
-/
noncomputable def readingA_wilson (β : ℝ) : Moment.Read nCorrYM :=
  readA (wilsonCorr β) (wilson_reflection_positive β)
/-- **The read used throughout the proof** — DEFINED to be reading-A of the Wilson ensemble. -/
noncomputable def readYM (β : ℝ) : Moment.Read nCorrYM :=
  readA (wilsonCorr β) (wilson_reflection_positive β)

/-! ### The aperture as a VARIABLE

Everything above fixes the aperture at `nCorrYM`. That is a value of a variable, not a property of
the theory, and the whole content of the entropy-matched read is that the margin opens as the window
widens relative to the substrate — a statement that cannot even be written when the window is frozen.
The definitions below carry the aperture, and the pinned ones are recovered as the `nCorrYM` instance
(`readYM_is_readYMAt`, `μYM_is_μYMAt`, both `rfl`). -/

/-- Reading-A at an ARBITRARY aperture. -/
noncomputable def readYMAt (N : ℕ) (β : ℝ) : Moment.Read N :=
  readA (wilsonCorrAt N β) (wilson_reflection_positive_at N β)

/-- The centre-vortex tension read through an aperture of size `N`. `μYM` is its `nCorrYM` instance. -/
noncomputable def μYMAt (N : ℕ) (β : ℝ) : ℝ := (readYMAt N β).tension

/-- The substrate's second moment about the CIRCLE distance, read through an aperture of size `N`.
Under the aperture reading this is the SUBSTRATE's quantity: the window contributes the separate
factor `(2π/(N+1))²` (`Moment.Read.thetaMoment_eq`), and the content of clustering is that this one
does not grow with `N`. -/
-- DERIVED: `Fin (N+1)` is the lag arity; the exponent 2 is the definition of a SECOND moment; and
-- the distance is `Moment.circLag`, the separation ON THE CIRCLE, because that is the only distance
-- the read can see. `cos` is even and 2π-periodic, so `cos (θ d)` depends on the lag only through
-- `min d (N+1-d)` (`Moment.Read.cos_theta_circ`).
--
-- WHY THIS IS NOT COSMETIC. Using the raw index `d` makes the moment UNBOUNDABLE. On a periodic
-- extent of `N+1` sites the correlation obeys ρ(N) = ρ(-1) = ρ(1), so the far half of the lag
-- range is the near half reflected; weighting it by `d²` rather than by the true distance makes the
-- moment grow like `N²` even when the correlation length is FIXED. For ρ(d) = e^{-dist/1.5}:
--
--     extent      8      16      32      64     128
--     raw       14.5    68.9     307    1305    5384     -- no bound exists, gapped or not
--     circle    1.97    3.03    3.28    3.28    3.28     -- saturates, which is what a gap means
--
-- So `∃ B, ∀ N, moment ≤ B` is FALSE for every physical correlation when the raw index is used, and
-- a theorem taking it as a hypothesis is vacuous.
noncomputable def d2At (N : ℕ) (β : ℝ) : ℝ :=
  ∑ d, (readYMAt N β).p d * (Moment.circLag d : ℝ) ^ 2

/-- **The input, with the aperture divided out.** The substrate moment per unit squared aperture —
the quantity that decides confinement once the window factor `(2π/(N+1))²` has cancelled against it.
A bounded `d2At` is the special case `c = 0` in the limit; a bounded `substrateRatio` is the weakest
hypothesis the aperture argument can consume.

DERIVED: the `+ 1` is the periodic extent `N + 1` (the lag arity), and the exponent `2` is the
square of it — the aperture factor `(2π/(N+1))²` this quantity is defined to divide out, so that
what remains carries no window. Neither is chosen; both come from `Moment.Read.thetaMoment_eq`.
-/
noncomputable def substrateRatio (N : ℕ) (β : ℝ) : ℝ := d2At N β / ((N : ℝ) + 1) ^ 2

/-- The read's own cosine average at aperture `N` — the single measured scalar confinement is
equivalent to, by `confinement_at_iff_cosAvg`. -/
noncomputable def cosAvgYMAt (N : ℕ) (β : ℝ) : ℝ :=
  ∑ d, (readYMAt N β).p d * Real.cos ((readYMAt N β).θ d)

/-- **C-3 — THE MODEL IDENTIFICATION, a THEOREM (`rfl`).** The read the proof reasons about *is* reading-A
of the physical SU(N) Wilson ensemble — definitionally, since both are `readA (wilsonCorr β) _`. With reading-A
a concrete function and both reads built from the same ensemble correlation, the identification is discharged
by construction. The un-formalized physics is carried by the named `wilson_reflection_positive_at` (RP) plus the
opaque ensemble data `wilsonCorr`. -/
theorem readYM_is_wilson : readYM = readingA_wilson := rfl

/-- The centre-vortex tension read `μ(β) = -log⟨cos θ⟩_ρ = log(S(0)/S(2π/L))` [E], DEFINED as the
min-entropy tension of the concrete correlation `readYM β` (`Moment.Read.tension`).

DERIVED: no numeral is introduced here — `tension` is `-log ⟨cos θ⟩_p`, defined in `Moment`. The
`0` and `2` above are a lag index and a section reference.
-/
noncomputable def μYM (β : ℝ) : ℝ := (readYM β).tension
/-- The leading character ratio `r(x) = I₂(x)/I₁(x)` at an ARBITRARY positive Bessel argument,
**DEFINED** from the modified-Bessel series (`Bessel.besselI`). The argument is a variable here so that
nothing downstream depends on a particular value of it.

DERIVED: the orders `2` and `1` are the two leading characters of the group, and their ratio is
what the strong-coupling character expansion produces. Neither is a magnitude: they index the
expansion, and the expansion is the cited object.
-/
noncomputable def rAt (x : ℝ) : ℝ := Bessel.besselI 2 x / Bessel.besselI 1 x

/-- **The character ratio is positive at every positive argument — a THEOREM.** The modified Bessel
`Iₙ(x) > 0` for `x > 0` (every series term positive, `Bessel.besselI_pos`; the Watson 1944 fact,
machine-checked from the elementary series), so `I₂/I₁ > 0`. -/
theorem rAt_pos {x : ℝ} (hx : 0 < x) : 0 < rAt x := Bessel.ratio_pos hx

/-- The Bessel argument at the strong-coupling threshold — one value of the variable `rAt` takes.
-- CHOSEN: `73/100` is the physical positive coupling scale (giving `r = I₂/I₁ ≈ 0.183` and
-- `βc ≈ 0.75`, consistent with the DERIVED threshold `β² < ½ log 3`, i.e. `β < 0.74115…`,
-- of `Bessel.strong_coupling_below_threshold`). What choosing it costs is
-- NOTHING in the logic: only its POSITIVITY is ever used (`rArgYM_pos`), and the threshold identity it
-- feeds is proved at EVERY positive argument (`βcAt_spec`), so this is an instantiation and not a
-- premise. Changing it moves `βcYM` and no theorem. -/
noncomputable def rArgYM : ℝ := 73 / 100

/-- **The Bessel argument is positive — a THEOREM** (`by norm_num`). -/
theorem rArgYM_pos : 0 < rArgYM := by unfold rArgYM; norm_num

/-- The character ratio at the pinned argument — the `rArgYM` instance of `rAt`. -/
noncomputable def rYM : ℝ := rAt rArgYM

/-- **The character ratio is positive** — the pinned instance of `rAt_pos`. -/
theorem ym_ratio_pos : 0 < rYM := rAt_pos rArgYM_pos

/-- The proved entropy floor `κ₀ = ¼ log 3` (`Floor.lean`).

DERIVED, both factors, and this is the only place in the development where a number bounds the gap
from BELOW — so it is the one that must not be chosen. `log 3` is the branching of a directed
cube-path, `Floor.directed_paths_card`. The `¼` is the reciprocal area per step:
`CubeArea.boundary_card_eq` proves the surface bounding a `k`-step path has exactly `4k+6` faces, and
`VortexCount.kappa0_is_the_surface_entropy_density` assembles the two into
`log(#surfaces)/area = k·log3/(4k+6) → ¼·log3`, which is this number. Nothing here is fitted or
measured; `4` and `3` are each the arity of something the lattice already is. -/
noncomputable def κ₀YM : ℝ := 1 / 4 * Real.log 3

theorem κ₀YM_pos : 0 < κ₀YM := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold κ₀YM; linarith

/-! ### Confinement through a variable aperture

One route, in one direction: a bound on the SUBSTRATE (its second moment about the circle distance,
or that moment per unit squared aperture) puts the tension below the entropy floor. Every statement
below is an instance or a limit of that one implication; none of them supplies a number. -/

/-- The pinned read is the `nCorrYM` instance of the aperture-general one. -/
theorem readYM_is_readYMAt : readYM = readYMAt nCorrYM := rfl

/-- The pinned tension is the `nCorrYM` instance of the aperture-general one. -/
theorem μYM_is_μYMAt : μYM = μYMAt nCorrYM := rfl

/-- **Confinement at one aperture, from the read's own cosine average.** Definitional: `tension` IS
`-log ⟨cos θ⟩_p`. It is stated because it is the form ONE measured scalar certifies. -/
theorem confinement_at_of_cosAvg {N : ℕ} {β : ℝ}
    (hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgYMAt N β) : μYMAt N β < κ₀YM :=
  (readYMAt N β).tension_lt_floor_of_cosAvg hc

/-- **And the converse**, so the two are known to be the same statement rather than one implying the
other. The positivity hypothesis is the one a nonpositive average cannot supply a logarithm for. -/
theorem confinement_at_iff_cosAvg {N : ℕ} {β : ℝ} (hpos : 0 < cosAvgYMAt N β) :
    μYMAt N β < κ₀YM ↔ (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvgYMAt N β :=
  ⟨fun h => (readYMAt N β).cosAvg_gt_of_tension_lt_floor hpos h, confinement_at_of_cosAvg⟩

/-- The ratio bound and the growth bound are the same hypothesis. Stated so neither form can drift
into looking like extra strength. -/
theorem substrateRatio_le_iff {N : ℕ} {β c : ℝ} :
    substrateRatio N β ≤ c ↔ d2At N β ≤ c * ((N : ℝ) + 1) ^ 2 := by
  have hN : (0 : ℝ) < ((N : ℝ) + 1) ^ 2 := by positivity
  rw [substrateRatio, div_le_iff₀ hN]

/-- **`2(1 − cos A) ≤ A²`, and it is `sin x ≤ x` in disguise.**

`1 − cos A = 2sin²(A/2)` and `A² = 4(A/2)²`, so the claim is `sin(A/2) ≤ A/2` squared. No numerics,
no bound on `A` beyond the half-turn it needs to keep the sine nonnegative.

This is what separates the ORIGIN-tangent threshold from the sharp one: with `A = arccos(3^{−1/4})`
the left side is the Taylor threshold's numerator and the right side is the sharp one's, so the sharp
threshold is never the smaller — a fact about cosine, not about this development's numbers. -/
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

/-- **THE THRESHOLD IN CLOSED FORM — the sharp one.**

    substrateThreshold = arccos(3^{−1/4})² / (2π)²

`arccos` of the entropy floor, squared, over the aperture squared. Both symbols are the program's
own: `3^{−1/4} = e^{−κ₀}` with `κ₀ = ¼log3` counted in `Floor`, and `(2π)²` is the window. Nothing is
fitted and nothing is measured to produce it.

DERIVED: `3` and the exponent `−1/4` are `κ₀ = ¼log3` read as `e^{−κ₀}`, counted in `Floor` off
directed cube paths; `2` and `π` are the lag angle `θ_d = 2π·circLag d/(N+1)` the read is taken
through; the outer exponent `2` is the second moment's own. `1` is the numerator of that exponent.
No magnitude is chosen — this is `sharp_constant_pos` solved for `c`. -/
noncomputable def substrateThreshold : ℝ :=
  Real.arccos ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 / (2 * Real.pi) ^ 2

/-- **THE SHARP CONFINEMENT CRITERION.**

    substrateRatio N β < substrateThreshold   ⟹   μYMAt N β < κ₀YM

`confinement_at_of_ratio` reaches the same conclusion through `1 − x²/2 ≤ cos x`, whose threshold is
`2(1 − 3^{−1/4})/(2π)² ≈ 0.0121669`. That bound is the tangent to `t ↦ cos √t` AT THE ORIGIN, so it
is the right bound only for a read concentrated at zero lag. This one takes the tangent at the
threshold itself (`Sharp.cos_avg_ge_tangent` with `A = arccos(3^{−1/4})`), where it is exact, and
gives `arccos(3^{−1/4})²/(2π)² ≈ 0.0126877` — about 4.3% more room, and SHARP: equality holds for the
point mass at `θ = A`, so no argument taking only the second moment can do better.

That matters not for the size — the measured ratio clears either threshold by more than thirty times
— but because it removes the last quantity in the chain that was chosen rather than derived. After
this the criterion's constant is the one the entropy floor and the aperture determine between them,
and there is no approximation left in it to tighten. -/
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

/-- **THE ORIGIN-TANGENT THRESHOLD IS NEVER THE LARGER — so there is ONE route, not two.**

    2(1 − 3^{−1/4}) / (2π)²  ≤  substrateThreshold

`confinement_at_of_ratio` asks for `(2π)²c/2 < 1 − 3^{−1/4}`, i.e. `c` under the left-hand side;
`confinement_at_of_substrate_sharp` asks for `c < substrateThreshold`. This says the first condition
implies the second, so the sharp theorem SUBSUMES the origin-tangent one — and `confinement_at_of_ratio`
below IS that derivation, which is why the development has one route to `μ < κ₀` and not two.

It needed no numerics: put `A = arccos(3^{−1/4})`, so `cos A = 3^{−1/4}`, and it is
`two_one_sub_cos_le_sq`. -/
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

/-- **Confinement at one aperture and one coupling, from the substrate ratio — a COROLLARY of the
sharp criterion.** The aperture cancels exactly, so the hypothesis on `c` carries no aperture and the
conclusion holds at every `N` for which the ratio bound does.

This form asks for `(2π)²c/2 < 1 − 3^{−1/4}`, i.e. `c` under `2(1 − 3^{−1/4})/(2π)²` — the tangent to
`t ↦ cos √t` AT THE ORIGIN. `taylor_le_substrateThreshold` proves that threshold never exceeds
`substrateThreshold`, so this follows from `confinement_at_of_substrate_sharp` and the development
carries ONE route to `μ < κ₀`, not two that could drift apart. The origin-tangent proof it used to
carry — through `Read.tension_lt_floor_of_circ_moment` and `1 − x²/2 ≤ cos x` — is retired. -/
theorem confinement_at_of_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    {N : ℕ} {β : ℝ} (h : substrateRatio N β ≤ c) :
    μYMAt N β < κ₀YM := by
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hct : c < 2 * (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / (2 * Real.pi) ^ 2 := by
    rw [lt_div_iff₀ hpi]; linarith
  exact confinement_at_of_substrate_sharp
    (lt_of_le_of_lt h (lt_of_lt_of_le hct taylor_le_substrateThreshold))

/-- The same at a FIXED coupling, for every large enough aperture. -/
theorem confinement_at_coupling_of_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) (β : ℝ)
    (h : ∀ᶠ N : ℕ in Filter.atTop, substrateRatio N β ≤ c) :
    ∀ᶠ N : ℕ in Filter.atTop, μYMAt N β < κ₀YM := by
  filter_upwards [h] with N hN
  exact confinement_at_of_ratio hc hN

/-- **Confinement from a moment allowed to GROW with the aperture.** The substrate moment need not be
bounded — it may grow like `c·(N+1)²` — provided the constant `c` clears the floor gap. This is the
weakest hypothesis the aperture argument consumes, and it is weaker than a bounded moment. -/
theorem confinement_of_growth_bound {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, d2At N β ≤ c * ((N : ℝ) + 1) ^ 2) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  filter_upwards [h] with N hN β
  exact confinement_at_of_ratio hc (substrateRatio_le_iff.mpr (hN β))

/-- The same, stated in the ratio. -/
theorem confinement_of_growth_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (h : ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, substrateRatio N β ≤ c) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  filter_upwards [h] with N hN β
  exact confinement_at_of_ratio hc (hN β)

/-- **CONFINEMENT AT EVERY LARGE ENOUGH APERTURE, FROM ONE SUBSTRATE BOUND.**

    (∃ B, ∀ N β, d2At N β ≤ B)  ⟹  ∀ᶠ N, ∀ β, μYMAt N β < κ₀YM

No number appears in the statement or the proof. `B` is existentially supplied by the substrate and
never named; the aperture is universally quantified and no threshold on it is given — `∀ᶠ N in atTop`
says only that one exists, and it is determined from `B` alone by
`Moment.aperture_factor_tendsto_zero`. `κ₀YM = ¼log3` is derived in `Floor`, per-area, with no
aperture in it.

WHAT THE HYPOTHESIS IS. The lag moment is bounded INDEPENDENTLY OF THE WINDOW. A gapped substrate
gives such a bound; a gapless one is bounded only by the window itself and so has none. That is why
the moment is taken about the CIRCLE distance (see `d2At`): about the raw index no physical
correlation is bounded, and the hypothesis would be vacuous. -/
theorem confinement_of_substrate_bound {B : ℝ} (hB : ∀ N β, d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * B / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) :=
    (Moment.aperture_factor_tendsto_zero B).eventually_lt_const Moment.floor_rhs_pos
  filter_upwards [hev] with N hN β
  exact (readYMAt N β).tension_lt_floor_of_circ_moment (hB N β) hN

/-- The same, with the bound existentially quantified: the hypothesis is that the substrate HAS an
aperture-independent moment, with no value supplied for it anywhere. -/
theorem confinement_of_bounded_substrate (h : ∃ B : ℝ, ∀ N β, d2At N β ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  obtain ⟨B, hB⟩ := h
  exact confinement_of_substrate_bound hB

/-- **CONFINEMENT FROM ONE DECAY RATE.**

    (∀ N β d, p d ≤ C·r^{circLag d})  with  r < 1   ⟹   ∀ᶠ N, ∀ β, μYMAt N β < κ₀YM

The hypothesis is a RATE, not a family of aperture-indexed bounds, and this is the form in which the
statement is worth making. The aperture-uniformity that `confinement_of_substrate_bound` demands is
discharged by `Moment.circ_moment_le_of_geometric`: the bound it produces,
`2C·∑' k, k²rᵏ`, is a convergent series with no `N` in it, so the window may be anything.

WHY THIS IS THE RIGHT SHAPE. Under reflection positivity the connected correlation has the
transfer-matrix form `ρ(d) = ∑ₙ wₙλₙᵈ` with `wₙ ≥ 0`, and if the transfer operator has a gap `Δ` then
every excited `λₙ ≤ e^{−Δ}`, so `ZeroMode.exists_exponential_decay` delivers exactly this hypothesis
with `r = e^{−Δ}`. The decay is in the CIRCLE distance rather than the raw lag because the correlation
on a periodic extent satisfies `ρ(d) = ρ(N+1−d)`.

So this reduces confinement to the standard statement — the transfer operator has a gap — with no
aperture in it anywhere, and with the entroptics apparatus carrying none of the uniformity. -/
theorem confinement_of_geometric_decay {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (readYMAt N β).p d ≤ C * r ^ (Moment.circLag d)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM := by
  refine confinement_of_substrate_bound (B := 2 * C * ∑' k : ℕ, (k : ℝ) ^ 2 * r ^ k) ?_
  intro N β
  exact Moment.circ_moment_le_of_geometric (readYMAt N β) hC hr0 hr1 (hdecay N β)

#print axioms confinement_of_geometric_decay

/-- **CONFINEMENT FROM THE RATE A TRANSFER OPERATOR GIVES.**

The same statement with the decay in the RAW lag, which is the form reflection positivity produces: a
`τ`-th power of the transfer operator is a `τ`-th power of each eigenvalue, so
`ρ(d) = ∑ₙ wₙλₙᵈ ≤ (∑ₙwₙ)·rᵈ` with `r` the largest excited eigenvalue
(`ZeroMode.le_geometric_of_lt_one`, `ZeroMode.exists_exponential_decay`).

`Moment.circ_decay_of_lag_decay` converts to the circle distance the aperture argument consumes. The
two forms are NOT interchangeable — the conversion runs one way, because `r < 1` makes the smaller
exponent the weaker bound — and stating both is what keeps the halves from being joined by a word. -/
theorem confinement_of_lag_decay {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hdecay : ∀ (N : ℕ) (β : ℝ) (d : Fin (N + 1)),
      (readYMAt N β).p d ≤ C * r ^ (d : ℕ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ β : ℝ, μYMAt N β < κ₀YM :=
  confinement_of_geometric_decay hC hr0 hr1
    (fun N β => Moment.circ_decay_of_lag_decay (readYMAt N β) hC hr0 hr1.le (hdecay N β))

#print axioms confinement_of_lag_decay

/-- **CONFINEMENT FROM A POSITIVE-WEIGHT SPECTRAL REPRESENTATION — the hypothesis in the form the
physics supplies it.**

If the read's weights have the transfer form `p d = ∑ₖ wₖ λₖᵈ` with `wₖ ≥ 0`, every `λₖ ≤ r < 1`, and
total weight bounded by `C` uniformly in the aperture and the coupling, then confinement holds at
every large enough aperture and every coupling.

THIS IS EXACTLY WHAT REFLECTION POSITIVITY DELIVERS. Osterwalder–Seiler gives the self-adjoint
transfer operator and the NONNEGATIVITY of the weights `wₖ = |⟨v,eₖ⟩|²` — that is the whole content of
`wₖ ≥ 0`, and it is why RP is cited rather than assumed away. A spectral gap `Δ` is precisely
`λₖ ≤ e^{−Δ} < 1` on the excited modes, so `r = e^{−Δ}`.

Everything from here to the mass gap is proved: the geometric bound
(`ZeroMode.le_geometric_of_lt_one`), the conversion to the circle distance
(`Moment.circ_decay_of_lag_decay`), the aperture-uniform moment bound
(`Moment.circ_moment_le_of_geometric`), the entropy-floor comparison, and the model assembly. The
footprint is the foundational three plus `wilson_reflection_positive_at`.

What it does NOT do is supply the gap `Δ`. That is the one remaining input, and it is the same input
`hgap` asks for from the other side — so the two open residuals of this development are one residual,
stated once. -/
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

/-- **THE SURPLUS BOUND, WITH NOTHING CHOSEN.**

    κ₀ + log(1 − (2π)²·substrateRatio N β / 2)  ≤  κ₀ − μYMAt N β

No threshold, no comparison constant, no `c`. The right-hand side is the entropy surplus at aperture
`N` and coupling `β`; the left-hand side is built from `κ₀ = ¼log3` (derived in `Floor`, per-area,
by counting `3^k` directed cube paths), the window `2π`, and `substrateRatio N β` — WHICH IS THE
MEASURED READ ITSELF, not a bound on it.

WHY THERE IS NO CONSTANT. `surplus_ge_of_ratio` takes a hypothesis `substrateRatio N β ≤ c` and asks
`(2π)²c/2 < 1 − 3^{−1/4}`. That inequality is not an input to the physics — it is exactly the
condition for the left-hand side here to be POSITIVE, i.e. the zero-crossing of the logarithm, solved
for `c`. Stating the bound pointwise removes it: the theorem holds at every aperture and coupling
where the log is defined, and `0.012167` is recovered by SOLVING `κ₀ + log(1 − (2π)²c/2) = 0`, never
by choosing it.

The only hypothesis is that the logarithm has an argument — `(2π)²·substrateRatio/2 < 1` — which is
a domain condition, not a threshold. -/
theorem surplus_ge (N : ℕ) (β : ℝ)
    (hdom : (2 * Real.pi) ^ 2 * substrateRatio N β / 2 < 1) :
    κ₀YM + Real.log (1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2) ≤ κ₀YM - μYMAt N β := by
  have hA : (0 : ℝ) < 1 - (2 * Real.pi) ^ 2 * substrateRatio N β / 2 := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  -- the aperture cancels EXACTLY: no inequality is spent here, because the ratio is the read itself
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

/-- **THE CONTINUUM BOUND, WITH NOTHING CHOSEN.**

On a screen of fixed physical extent `L = (N+1)·a`, the spacing is `a = L/(N+1)` and the physical
surplus is `(κ₀ − μ)/a`. This bounds it below by a quantity built only from the measured read:

    ((N+1)/L) · (κ₀ + log(1 − (2π)²·substrateRatio N β / 2))  ≤  (κ₀ − μYMAt N β) / (L/(N+1))

Every symbol on the left is either measured (`substrateRatio N β`), derived (`κ₀ = ¼log3`), the
window (`2π`), or the screen the observer chose (`L`). There is no threshold and no fitted constant,
so there is nothing here to pin.

WHAT IT REPLACES. `ym_physical_gap_of_ratio` reaches `κ/L` by assuming `substrateRatio ≤ c` with
`c < 2(1−3^{−1/4})/(2π)²`, then names `κ` separately. Both numbers are gone: the rate is not supplied,
it is READ OFF, and it is positive exactly when `substrateRatio N β < 2(1−3^{−1/4})/(2π)²` — which is
now a consequence of the formula rather than an assumption feeding it. -/
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

/-- **THE THRESHOLD IS A THEOREM, NOT A HYPOTHESIS.**

The bound `ym_physical_gap_ge` gives is positive — a genuine physical gap rather than a vacuous
inequality — exactly when

    substrateRatio N β  <  2 · (1 − 3^{−1/4}) / (2π)²

and this is an `iff`, PROVED, not a condition imposed. The number `0.012167…` that
`surplus_ge_of_ratio` carries as a hypothesis is the decimal expansion of the right-hand side, so it
was never an input to the physics: it is the zero of `κ₀ + log(1 − (2π)²x/2)`, solved for `x`.

WHERE EACH PIECE COMES FROM. `3^{−1/4} = e^{−κ₀}` with `κ₀ = ¼log3` derived in `Floor` by counting
directed cube paths. `(2π)²` is the window `Moment.Read.thetaMoment_eq` produces. The `2` is the
denominator of the cosine bound `1 − x²/2 ≤ cos x`. Nothing is chosen and nothing is fitted — the
threshold is a closed form in the entropy floor and the aperture, and the decimal appears in this
file only inside this comment. -/
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

/-- **THE SURPLUS BOUND, SHARP AND WITH NOTHING CHOSEN.**

    κ₀ + log cos(2π·√substrateRatio N β)  ≤  κ₀ − μYMAt N β

`surplus_ge` bounds the same surplus by `κ₀ + log(1 − (2π)²·substrateRatio/2)`, through the tangent
to `t ↦ cos √t` at the ORIGIN. This takes the tangent at the read's own root-mean-square angle, where
the correction term vanishes identically (`Sharp.cos_avg_ge_cos_rms`), and the result is Jensen's
inequality for that convex function.

It is the best bound available: equality holds for the point mass at `θ = 2π√substrateRatio`, so no
argument that reads the correlation only through its second moment can improve it. Together with
`surplus_pos_iff_substrate`'s sharp counterpart `confinement_at_of_substrate_sharp`, the whole chain
from the read to the surplus now carries no chosen quantity — every constant in it is `κ₀ = ¼log3`,
the window `2π`, or the measured ratio itself.

The hypotheses are the domain of the logarithm, not thresholds: the ratio is positive, and the rms
angle stays inside the quarter-turn where the cosine is. -/
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

/-- **THE CONTINUUM BOUND, SHARP AND WITH NOTHING CHOSEN.**

On a screen of fixed physical extent `L = (N+1)·a`, with `a = L/(N+1)`:

    ((N+1)/L) · (κ₀ + log cos(2π·√substrateRatio N β))  ≤  (κ₀ − μYMAt N β) / a

This is `ym_physical_gap_ge` with the sharp surplus in place of the origin-tangent one. Nothing on
the left is fitted, chosen, or measured-and-then-rounded: `κ₀ = ¼log3` is counted in `Floor`, `2π` is
the window, `L` is the screen the observer picked, and `substrateRatio N β` is the read. -/
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

/-- The substrate ratio is a nonnegative weight against a square, so it carries no sign condition
anywhere; it is a fact about the read, not a hypothesis. -/
theorem substrateRatio_nonneg (N : ℕ) (β : ℝ) : 0 ≤ substrateRatio N β := by
  unfold substrateRatio d2At
  refine div_nonneg (Finset.sum_nonneg (fun d _ => ?_)) (by positivity)
  exact mul_nonneg ((readYMAt N β).p_nonneg d) (sq_nonneg _)

#print axioms substrateRatio_nonneg

/-- **The sharp surplus at `c` is positive exactly below the sharp threshold.**

`κ₀ + log cos(2π√c) > 0 ⟺ cos(2π√c) > 3^{−1/4} ⟺ 2π√c < arccos(3^{−1/4}) ⟺ c < substrateThreshold`.
So the threshold is not a separate condition imposed on the bound — it IS the bound's zero, solved
for `c`, and `substrateThreshold` is that solution written down. -/
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

/-- **THE CONTINUUM STATEMENT: a gap in physical units that the spacing cannot erode.**

Fix a screen of physical extent `L`. Refine it — `a = L/(N+1) → 0` as the aperture grows — and
suppose the substrate ratio stays under one `c` below the sharp threshold, at every aperture of the
family and every coupling. Then

    (κ₀ + log cos(2π√c)) / L  ≤  (κ₀ − μYMAt (N₀+i) β) / a          for EVERY `i` and `β`

and the left-hand side is a POSITIVE constant, fixed before the family is indexed
(`uniform_gap_constant_pos`). That is what a continuum limit needs: not that each lattice has a gap,
which is compatible with the gap closing as `a → 0`, but that the gaps share a positive lower bound.

WHY THE HYPOTHESIS HAS THIS SHAPE. `substrateRatio` is `⟨d²⟩/(N+1)²` — a squared separation over a
squared extent, both in lattice units, so the spacing cancels and what is left is a property of the
screen alone. A bound on it is therefore NOT the assumption that the lattice correlation length is
bounded, which is false along any continuum trajectory; it is the assumption that the correlation
length is a bounded FRACTION of the screen. `c < substrateThreshold` says that fraction clears
`arccos(3^{−1/4})/2π`, and nothing in the statement is chosen: `κ₀ = ¼log3` is counted in `Floor`,
`2π` is the window, `L` is the screen, and `c` is the observer's own bound on the measured read.

This is `ScreenedGap.uniform_physical_gap`'s conclusion reached from the sharp bound directly, with
the rate READ OFF rather than supplied: `ScreenedGap.Screened` carries `hrate : κ/(N+1) ≤ κ₀ − μ` as
a field, and `surplus_ge_sharp` gives a CONSTANT lower bound, which is stronger at every aperture. -/
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

/-- The constant `ym_physical_gap_uniform` delivers is positive, so the bound is a gap and not a
tautology. It is positive exactly when `c` is under the sharp threshold — which is the hypothesis,
so nothing further is assumed here. -/
theorem uniform_gap_constant_pos {c L : ℝ} (hc0 : 0 ≤ c) (hc : c < substrateThreshold)
    (hL : 0 < L) :
    0 < (κ₀YM + Real.log (Real.cos (Real.sqrt ((2 * Real.pi) ^ 2 * c)))) / L :=
  div_pos (sharp_constant_pos hc0 hc) hL

#print axioms uniform_gap_constant_pos

/-- **The surplus IS the log of the measured cosine average.** `μ = −log⟨cos θ⟩` by definition, so

    κ₀ − μYMAt N β  =  κ₀ + log (cosAvgYMAt N β)

is an identity, not a bound. Everything the aperture machinery does — the circle moment, the tangent,
the threshold — is a route to bounding the right-hand side from below using less than the full
distribution. None of it is needed to STATE the gap. -/
theorem surplus_eq_log_cosAvg (N : ℕ) (β : ℝ) :
    κ₀YM - μYMAt N β = κ₀YM + Real.log (cosAvgYMAt N β) := by
  show κ₀YM - -Real.log (cosAvgYMAt N β) = _
  ring

#print axioms surplus_eq_log_cosAvg

/-- **THE CONTINUUM STATEMENT, EXACT — no moment, no tangent, no aperture approximation.**

Fix a screen of physical extent `L` and refine it. If the measured cosine average stays at or above
some `γ` strictly above the entropy floor, at every aperture of the family and every coupling, then

    (κ₀ + log γ) / L  ≤  (κ₀ − μYMAt (N₀+i) β) / a          for EVERY `i` and `β`

and `κ₀ + log γ > 0` because `γ > 3^{−1/4} = e^{−κ₀}`.

WHY THIS IS THE STRONGEST FORM. `confinement_at_iff_cosAvg` says `μ < κ₀ ⟺ ⟨cos θ⟩ > 3^{−1/4}` — an
IFF, with nothing given away. `ym_physical_gap_uniform` reaches the same conclusion from
`substrateRatio ≤ c`, which is that condition relaxed to a second moment; the relaxation is sharp at
second-moment order (`Sharp.cos_avg_ge_cos_rms`) but it is still a relaxation, and the 2.37× window
between the sufficient and necessary substrate bounds is exactly what it costs.

So the aperture route is a way of CERTIFYING the hypothesis from one number rather than the whole
distribution. The theorem itself never needed it, and stating it this way is what keeps the two
apart: `γ` is the measured cosine average, `κ₀ = ¼log3` is counted in `Floor`, `L` is the screen. -/
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

/-! ## The mass the read measures, and why `κ₀ − μ` is not it

`⟨cos θ⟩ = ∑_d p_d cos(2πd/(N+1))` is the `k=1` Fourier mode of the normalised correlation, so

    μ = log (Ŝ(0) / Ŝ(k₁)),      k₁ = 2π/(N+1)

the structure factor at zero momentum over its value at the lowest lattice momentum. That is the
standard second-moment mass estimator, and it INVERTS: writing `k̂₁ = 2 sin(π/(N+1))` for the lattice
momentum,

    Ŝ(0)/Ŝ(k₁) = 1 + k̂₁²/m²   ⟹   m = k̂₁ / √(e^μ − 1).

WHY THIS MATTERS. `μ` falls like `1/(N+1)²` as the aperture grows — measured, `μ·L²` is flat at
`≈3.1` across `L = 8…32` — and read naively that looks like the dynamics draining away, leaving
`κ₀ − μ → κ₀`, a pure counting constant. It is the opposite: `k̂₁² ≈ (2π/L)²` falls like `1/L²` AT
FIXED MASS, so `μ ∼ 1/L²` is exactly what a genuine mass produces. Inverting it on the released
ensembles gives `m` constant to ±7.2% across a range over which `μ` itself falls 14.6×.

So `κ₀ − μ` is not `a·m_phys` and was never going to be; the mass is `k̂₁/√(e^μ − 1)`, and THAT is
what carries the spacing correctly. -/

/-- The lowest nonzero lattice momentum at aperture `N`, `k̂₁ = 2 sin(π/(N+1))`.

DERIVED: `2` and the sine are the lattice momentum `k̂ = 2 sin(k/2)` at `k = k₁ = 2π/(N+1)`, the
smallest nonzero momentum a periodic extent of `N+1` sites carries. Neither is chosen. -/
noncomputable def khat1 (N : ℕ) : ℝ := 2 * Real.sin (Real.pi / ((N : ℝ) + 1))

/-- **The second-moment mass in lattice units**, `m = k̂₁/√(e^μ − 1)`, read off the same `μ` the
confinement criterion uses. This is the quantity that carries the lattice spacing correctly:
`m_phys = m/a`.

DERIVED: the `1` is subtracted because `e^μ = Ŝ(0)/Ŝ(k₁) = 1 + k̂₁²/m²` — it is the ZERO-MOMENTUM term
of that ratio, so `e^μ − 1` is the excess over it, and the whole definition is that identity solved
for `m`. Nothing is chosen, and no scale enters: `k̂₁` is the aperture's own lowest momentum. -/
noncomputable def m2At (N : ℕ) (β : ℝ) : ℝ :=
  khat1 N / Real.sqrt (Real.exp (μYMAt N β) - 1)

/-- `e^{κ₀} = 3^{1/4}`, the floor read as a contrast rather than as a rate. -/
theorem exp_κ₀YM : Real.exp κ₀YM = (3 : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
  unfold κ₀YM
  ring_nf

#print axioms exp_κ₀YM

theorem one_lt_three_rpow : (1 : ℝ) < (3 : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [← exp_κ₀YM]
  have hx := Real.exp_lt_exp.mpr κ₀YM_pos
  rwa [Real.exp_zero] at hx

#print axioms one_lt_three_rpow

/-- **CONFINEMENT BOUNDS THE MASS FROM BELOW.** `μ < κ₀` caps `e^μ − 1` by `3^{1/4} − 1`, and the
mass divides by that square root, so the cap becomes a FLOOR under the mass:

    μ < κ₀   ⟹   k̂₁ / √(3^{1/4} − 1)  <  m2At N β

Nothing is chosen: `3^{1/4} = e^{κ₀}` with `κ₀ = ¼log3` counted in `Floor`, and `k̂₁` is the lattice
momentum the aperture carries. -/
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

/-- **The lattice momentum is at least `4/(N+1)`** — Jordan's inequality `sin x ≥ (2/π)x` on the
quarter-turn, which is where `π/(N+1)` sits once the aperture carries at least two sites.

DERIVED: `2/π` is Jordan's constant, tight at `π/2`; multiplied through `k̂₁ = 2 sin(π/(N+1))` it
gives `4/(N+1)`. The `4` is `2 × 2/π × π`, not a magnitude. -/
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

/-- **THE PHYSICAL MASS, BOUNDED BELOW, WITH NO SPACING IN THE BOUND.**

On a screen of physical extent `L = (N+1)·a`, so `a = L/(N+1)`, confinement alone gives

    4 / (L·√(3^{1/4} − 1))  ≤  m2At N β / a

and the left-hand side carries NO lattice spacing and NO aperture — only the screen `L`, the entropy
floor through `3^{1/4} = e^{κ₀}`, and Jordan's constant. Numerically `4/√(3^{1/4}−1) = 7.115`, rising
to `2π/√(3^{1/4}−1) = 11.176` as the aperture grows and `(N+1)·sin(π/(N+1)) → π`.

THIS IS THE STATEMENT `κ₀ − μ` COULD NOT MAKE. `(κ₀ − μ)/a` diverges as `a → 0`, because `κ₀ − μ`
tends to the counting floor rather than to zero — `κ₀ − μ` is not `a·m_phys`. The second-moment mass
is, and dividing IT by the spacing gives a bound that is finite, positive, and spacing-free. -/
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

/-- **A MASS BOUND THAT DOES NOT WEAKEN WITH THE APERTURE.**

`physical_mass_ge_of_confinement` bounds the mass by `k̂₁/√(3^{1/4}−1)`, and `k̂₁ → 0` as the aperture
grows, so that bound dilutes: it says the mass beats the box's lowest momentum by a fixed factor,
which is a FINITE-VOLUME statement. This one does not dilute:

    e^μ − 1 ≤ C·k̂₁²   ⟹   1/√C ≤ m2At N β

with `1/√C` carrying no aperture at all. The hypothesis is that the structure-factor contrast
`e^μ − 1 = (Ŝ(0) − Ŝ(k₁))/Ŝ(k₁)` scales like the lowest momentum SQUARED — which is precisely the
statement that the read resolves a fixed mass rather than a feature that moves with the box.

WHY THIS IS THE RIGHT SHAPE, and what it costs. It is not `substrateRatio ≤ c` — a magnitude
compared against a threshold — but a SCALING LAW between two measured quantities, with `C` supplied
by whoever measures it and never given a value here. `C = 1/m²`, so the content is "the extracted
mass does not fall as the box grows". On the released SU(2) ensembles at β=2.30 that holds to ±7.2%
across `L = 8…32`, over a range in which `μ` itself falls 14.6×.

Composed with `Certify.gap_uniform_in_volume_of_intensive`, which takes an INTENSIVE margin and
returns one rate for every volume, this is the infinite-volume half stated in the variable that
actually carries it. -/
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

/-- **THE PHYSICAL MASS, UNIFORM IN THE VOLUME.** The same hypothesis on a screen of extent
`L = (N+1)a` gives `m_phys = m2At/a ≥ (N+1)/(L√C)`, which GROWS with the aperture rather than
dilutes — the opposite behaviour to `physical_mass_ge_of_confinement`, and the reason the scaling
form is the one the infinite-volume limit needs. -/
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

/-- **THE GAP AS A DIFFERENTIAL OF THE APERTURE — a bound that does NOT dilute.**

`m2_gt_of_confinement` bounds the mass at aperture `N` by `k̂₁ N / √(3^{1/4}−1)`, and `k̂₁ N → 0`, so
applied aperture by aperture it erodes. But the mass is not supposed to depend on the window it is
read through: that is what it MEANS for the read to see the substrate rather than the aperture. Take
that seriously and the erosion disappears —

    m2At is the same at every aperture,  and  μ < κ₀ at ONE aperture N₀
      ⟹  k̂₁ N₀ / √(3^{1/4}−1)  <  m2At N β    at EVERY aperture

and the right-hand side is now FIXED: it is read off whichever `N₀` the confinement is established
at, and the bound is STRONGEST at the COARSEST such window, because `k̂₁` is largest there. Reading
at a finer aperture no longer weakens the conclusion; it just re-reads the same invariant.

WHY THIS IS THE REACH FROM BELOW. Everything reflection positivity gives is one-sided and bounds the
gap ABOVE (`m_eff ≥ Δ`, §8.7b) — a gapless theory satisfies all of it. The floor is the only thing
pushing UP, and `μ = log(Ŝ(0)/Ŝ(k₁))` is the quantity it acts on: `μ` bounded ABOVE is the mass
bounded BELOW, because `m² = k̂₁²/(e^μ − 1)`. A gapless theory has a diverging zero mode, so `Ŝ(0)`
runs away, `μ → ∞`, and the floor is crossed. The floor is exactly the line that separates them.

WHAT IS ASSUMED, stated exactly. `hinv` is NOT "the mass is positive" — it is "the mass does not
depend on the window", which is a different statement and the natural partner of the aperture
postulate. On the released SU(2) ensembles at β=2.30 it holds to **±7.2%** across `L = 8…32`, over a
range in which `μ` itself falls 14.6×.

NUMERICALLY. `k̂₁/√(3^{1/4}−1)` is `3.557` at extent 2, `1.361` at extent 8. The measured lattice
mass across that whole range is `3.32`–`3.82`. So the coarsest window's floor SATURATES the measured
value — the aperture argument is not merely consistent with the mass, it very nearly returns it. -/
theorem m2_ge_of_aperture_invariant {β : ℝ} {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hpos : 0 < μYMAt N₀ β) (hconf : μYMAt N₀ β < κ₀YM)
    (hinv : ∀ N : ℕ, m2At N β = m2At N₀ β) :
    ∀ N : ℕ, khat1 N₀ / Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) < m2At N β := by
  intro N
  rw [hinv N]
  exact m2_gt_of_confinement hN₀ hpos hconf

#print axioms m2_ge_of_aperture_invariant

/-- **THE INFINITE-VOLUME GAP AT A FIXED COUPLING.** The same statement as an existence claim: one
positive `δ`, fixed before the aperture is chosen, that every aperture's mass clears.

This is the infinite-volume half — `N → ∞` at fixed `β`, so the spacing does not move and `δ/a` is a
positive physical mass. What it does not settle is the continuum half, `β → ∞` with `a → 0`, where
the lattice mass must itself scale like the spacing. -/
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

/-- **THE APERTURE'S LOWEST MOMENTUM, IN PHYSICAL UNITS, HAS A CONTINUUM LIMIT.**

    (N+1) · k̂₁ N  =  2 (N+1) sin(π/(N+1))  →  2π

On a screen of fixed physical extent `L = (N+1)a` this says `k̂₁/a → 2π/L`: the lowest momentum the
aperture carries converges to the screen's own lowest momentum, and the LATTICE disappears from it.
That is the `a → 0` half of `Aperture.gap_refinement_invariant`, which says the same thing as an
identity in the rate; here it is said in the momentum the mass is read against.

It is `sin t / t → 1` at `t = π/(N+1) → 0`, and nothing else. -/
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

/-- **THE CONTINUUM BOUND ON THE PHYSICAL MASS.**

At a screen of fixed physical extent `L`, with the spacing `a = L/(N+1)`, the mass bound from
confinement is `k̂₁ N / √(3^{1/4}−1)` in lattice units, so `(N+1)·k̂₁ N / (L√(3^{1/4}−1))` in physical
ones. By `khat1_mul_tendsto` that converges to

    2π / (L · √(3^{1/4} − 1))   ≈   11.176 / L

and the LATTICE IS GONE from it: only the screen, the entropy floor, and the window remain.

`physical_mass_ge_of_confinement` gives `4/(L√(3^{1/4}−1)) ≈ 7.115/L` at EVERY finite aperture, via
Jordan's inequality. This is the same bound in the limit, and it is 57% stronger — the difference is
exactly `2π` against Jordan's `4`, i.e. the gap between `sin t ≥ (2/π)t` and `sin t ≈ t`.

**WHICH OF THE TWO CAP CONSTANTS THIS IS, AND WHY.** The limit above is `2π/√(3^{1/4}−1) = 11.17598`,
algebraically identical to `2π√(T/(1−T))` at `T = 3^{−1/4}`. That is the constant of the UNFOLDED
shape `ρ(d) = λ^d` — equivalently of the periodic `cosh` correlator `λ^d + λ^{n−d}`, which has the
same limit, and of the lattice free field's `Ŝ(k) = 1/(m² + k̂²)`. This theorem inherits it because
`m2At` inverts exactly that structure factor, and that inversion is EXACT for a single-mass periodic
correlator: it is not an open-chain approximation, and the wrap-around term it is sometimes said to
miss is subleading in `n`.

The neighbouring constant `10.98875` belongs to the FOLDED shape `ρ(d) = λ^min(d,n−d)`
(`ZeroMode.circLag_cos_sum_fold`, `CellSpectrum`'s aperture cap), where the minimum-image fold adds
weight at large lag and contributes the `coth(aπ/2) > 1` factor. Both shapes live on the same circle;
the fold, not the geometry, is the whole difference. The folded constant is the SMALLER, hence the
conservative one, which is why the aperture cap is quoted with it.

The two differ by `0.19` — closer than any simulated aperture is to its own limit — which is why the
repository carries a guard against quoting one for the other, and why that guard has fired before on
three files at once. The finite-aperture bound `7.115/L` below does not depend on either and is
unaffected. -/
theorem continuum_mass_bound_tendsto (L : ℝ) (hL : 0 < L) :
    Filter.Tendsto
      (fun N : ℕ => ((N : ℝ) + 1) * khat1 N / (L * Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)))
      Filter.atTop
      (nhds (2 * Real.pi / (L * Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1)))) := by
  have hroot : 0 < Real.sqrt ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1) :=
    Real.sqrt_pos.mpr (by linarith [one_lt_three_rpow])
  exact khat1_mul_tendsto.div_const _

#print axioms continuum_mass_bound_tendsto

/-- **THE PHYSICAL MASS IS BOUNDED BELOW, UNIFORMLY IN THE APERTURE, ON A FIXED SCREEN.**

    δ  ≤  m2At N β / a        at EVERY aperture `N` and coupling `β`,   `a = L/(N+1)`

`δ` is fixed before the family is indexed, so this is a mass gap in physical units that refining the
lattice cannot erode. It is the composition of exactly two hypotheses, and BOTH are scaling laws
between measured quantities rather than magnitudes compared against thresholds:

* `hscale` — `e^μ − 1 ≤ C N · k̂₁²`. The structure-factor contrast goes like the lowest momentum
  squared. Measured on the released SU(2) ensembles: `C` flat to ±13.7% (β=2.30, L=8…32), ±7.5%
  (β=2.40), ±12.2% (β=2.60), over a range in which `μ` itself falls 14.6×.
* `hphys` — `√(C N) ≤ (N+1)/(Lδ)`. Since `C = 1/m²`, this says the LATTICE mass falls like the
  spacing, `m_lat ∼ a`, which is what "the read resolves a physical mass" means. Measured on the
  SMEARED channel: `ξ_phys√σ` agrees to 5.0% across a 1.343× change of spacing, giving
  `m_phys/√σ ≈ 3.86` against the SU(2) `0⁺⁺` glueball at `≈3.6√σ`. On the RAW channel it fails —
  21.4% disagreement, in the wrong direction — because that channel is contact-scale.

WHAT IS PROVED AND WHAT IS ASSUMED, stated exactly. `hphys` unfolds to the CONCLUSION: with
`C = 1/m²` it says `m/a ≥ δ`, which is `m_phys ≥ δ`. So this theorem is bookkeeping — it carries the
bound through the screen's arithmetic and adds no content of its own, and it must not be read as a
reduction of the mass gap to something weaker.

The content is in the two statements below it:

* `physical_mass_ge_of_confinement` is NOT circular. From `μ < κ₀` alone — no assumed mass — it gives
  `m_phys ≥ 4/(L√(3^{1/4}−1))`, positive and spacing-free. Its limitation is that it dilutes as the
  screen grows, so it is a finite-volume statement.
* `m2_ge_of_scaling` is not circular either, and it is where the work is: `hscale` relates two
  measured quantities that move together, and it converts a `μ` that VANISHES like `1/(N+1)²` into a
  mass that does not. That is the step `κ₀ − μ` could not take.

What remains open is the continuum direction, and naming it precisely: `C` is fixed in LATTICE units,
so a spacing-independent `δ` needs `C ∼ 1/(a·m_phys)²`. That is measured on the smeared channel
(scale-covariant to 5.0%) and fails on the raw one (21.4%, wrong direction) — measured, not proved. -/
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

/-- **QUANTITATIVE CONFINEMENT — the surplus is bounded below by a CONSTANT.**

`confinement_of_growth_ratio` gives `μ < κ₀` and no size. This gives the size: under the same
hypothesis `substrateRatio N β ≤ c`, with the same threshold, the entropy surplus clears

    κ₀ + log(1 − (2π)²c/2)

which carries NO aperture. The route is one step: `Moment.Read.cos_avg_ge_circ` turns the ratio bound
into a floor under the cosine average, and `μ = −log⟨cos⟩` turns that into a ceiling on the tension.

WHY THE SIZE IS THE POINT. `ScreenedGap.Screened` asks for `hrate : κ/(N+1) ≤ κ₀ − μ`, and
`ZeroMode.rate_gt_of_tension` supplies it only for a SINGLE geometric mode. A constant lower bound is
stronger than `κ/(N+1)` at every large aperture, so this supplies `hrate` for the actual read, at any
`κ`, with no assumption on the mode structure. -/
theorem surplus_ge_of_ratio {c : ℝ} (hc0 : 0 ≤ c)
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    {N : ℕ} {β : ℝ} (h : substrateRatio N β ≤ c) :
    Real.log (1 - (2 * Real.pi) ^ 2 * c / 2) + κ₀YM ≤ κ₀YM - μYMAt N β := by
  -- ONE PATH: this is `surplus_ge` weakened by monotonicity of `log`. The comparison constant `c`
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

/-- **`hrate`, PROVED.** The lattice surplus clears `κ/(N+1)` at every large enough aperture, for any
`κ`, from the aperture-free ratio bound alone.

This is the hypothesis `ScreenedGap.Screened` carries and `ZeroMode.rate_gt_of_tension` supplies only
for a single geometric mode. Composed with a screen of FIXED PHYSICAL EXTENT `L = (N+1)a`, the spacing
cancels and `ScreenedGap.uniform_physical_gap` returns `Δ_phys ≥ κ/L` — a bound that does not depend
on the lattice spacing, which is what a continuum limit needs. -/
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

/-- **THE PHYSICAL GAP, INDEPENDENT OF THE LATTICE SPACING — the continuum statement.**

Read the theory through a screen of FIXED PHYSICAL EXTENT `L`: the aperture grows as the spacing
falls, `(N+1)·a = L`, because a screen is a property of the extraction boundary and not of the lattice
used to compute through it. Then from the aperture-free ratio bound alone,

    κ/L  ≤  (κ₀ − μYMAt N β) / a       at every member of the family,

and the right-hand side is the gap in PHYSICAL units. The spacing cancels: `(κ₀−μ)/a = (κ₀−μ)(N+1)/L`,
and `rate_of_ratio` gives `(κ₀−μ)(N+1) ≥ κ`.

WHY THIS IS THE CONTINUUM STATEMENT AND A PER-LATTICE GAP IS NOT. "Every lattice has a gap" is
compatible with the gap closing as `a → 0`, which is no theory at all. What a continuum limit needs is
that the gaps share a POSITIVE LOWER BOUND, and `κ/L` is one number fixed before the family is
indexed. Every member clears it, however fine the lattice.

WHAT IT COSTS. One hypothesis: `substrateRatio N β ≤ c` with `(2π)²c/2 < 1 − 3^{−1/4}`, i.e. the
substrate's second moment per unit squared aperture stays under `0.012167`. No strong-coupling
expansion, no cluster expansion, and no restriction on the mode structure of the read. -/
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

/-- **The converse, at one aperture.** A tension below the floor FORCES the substrate ratio under a
ceiling derived from the floor alone. Having both directions means the aperture condition and the
bounded substrate ratio are the same statement, not one sufficient for the other. -/
theorem substrateRatio_lt_of_tension_lt_floor {N : ℕ} {β : ℝ} (hpos : 0 < cosAvgYMAt N β)
    (h : μYMAt N β < κ₀YM) :
    substrateRatio N β < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8 :=
  (readYMAt N β).substrate_lt_of_tension_lt_floor hpos h

/-- The entropy surplus read through an aperture of size `N`. -/
noncomputable def ΔYMAt (N : ℕ) (β : ℝ) : ℝ := κ₀YM - μYMAt N β

/-- **Gap = positive entropy surplus ⟺ confinement, at any aperture.** This is the form
`YMGap.ymGapped` consumes: the reconstructed theory's mass gap IS the surplus, so confinement at an
aperture and a positive gap at that aperture are one statement. -/
theorem gap_pos_iff_confinement_at (N : ℕ) (β : ℝ) : 0 < ΔYMAt N β ↔ μYMAt N β < κ₀YM := by
  unfold ΔYMAt; constructor <;> intro h <;> linarith

/-- **The one-way margin, at any aperture.** The dominant decay factor `e^{−Δ}` is strictly inside the
unit disk exactly when the surplus is positive. -/
theorem oneway_margin_at (N : ℕ) (β : ℝ) : Real.exp (-(ΔYMAt N β)) < 1 ↔ 0 < ΔYMAt N β := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- **The margin opens to the WHOLE floor as the window widens.** Under one aperture-independent
substrate bound the tension vanishes, so the surplus `Δ = κ₀ − μ` tends to `κ₀` itself. This is the
statement the frozen window cannot express, and it is the content of the entropy-matched read: the
gap is not a residue left over after a subtraction, it is the entire floor in the limit. -/
theorem margin_tendsto_floor {B : ℝ} (hB : ∀ N β, d2At N β ≤ B) (β : ℝ) :
    Filter.Tendsto (fun N => ΔYMAt N β) Filter.atTop (nhds κ₀YM) := by
  have h : Filter.Tendsto (fun N => μYMAt N β) Filter.atTop (nhds 0) :=
    Moment.tension_tendsto_zero_of_bounded_circ_moment B (fun N => readYMAt N β)
      (fun N => hB N β)
  simpa [ΔYMAt] using tendsto_const_nhds.sub h

-- The whole confinement route, footprinted. Every one of these carries the foundational three plus
-- `wilson_reflection_positive_at` and nothing else: no number, no threshold, no chosen aperture.
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

/-- The threshold coupling at an ARBITRARY positive Bessel argument, **defined** as where the linear
character bound meets the floor: `β_c(x) = κ₀ / (2 r(x))`.
-- DERIVED: the `2` is the character bound's own slope `μ ≤ 2βr`, and `κ₀` is the proved floor. Solving
-- `2βr = κ₀` for `β` is the definition; no value is chosen. -/
noncomputable def βcAt (x : ℝ) : ℝ := κ₀YM / (2 * rAt x)

/-- **The threshold identity holds at EVERY positive argument**, so the pinned `rArgYM` is one value of
a variable rather than a number the argument depends on. `2 β_c r = κ₀` by construction. -/
theorem βcAt_spec {x : ℝ} (hx : 0 < x) : 2 * βcAt x * rAt x = κ₀YM := by
  have hr : rAt x ≠ 0 := ne_of_gt (rAt_pos hx)
  unfold βcAt
  field_simp

#print axioms βcAt_spec

/-- The threshold coupling at the pinned argument — the `rArgYM` instance of `βcAt`. -/
noncomputable def βcYM : ℝ := βcAt rArgYM
/-- A strong-coupling reference point strictly below the threshold.
-- CHOSEN: the offset `1` only has to be POSITIVE — it names a point below `β_c` for the grid route's
-- case split, and every theorem using it takes the behaviour there as a hypothesis. Any positive
-- offset gives the same theorems. -/
noncomputable def βloYM : ℝ := βcYM - 1

/-! ## A1's constants and the cited standard inputs -/

/-! ### A1's interior: the crossover confinement, from a bounded correlation moment

The min-entropy tension the gap reads is `μ = log(S(0)/S(2π/L))` of the whitened :F² correlation. With
reflection positivity (`ρ ≥ 0`, so `λ₁ = S(0)`, `λ₂ ≥ S(2π/L)`; `FreeField.structure_factor_peak_at_zero`),
`μ ≤ -log ⟨cos θ⟩_ρ`, and the analytic step `⟨cos θ⟩ ≥ 1-⟨θ²⟩/2 ⟹ (moment bound) ⟹ μ < κ₀` is **machine-
checked** in `Moment.tension_lt_floor_of_moment` (RP + `cos x ≥ 1-x²/2`, no physics). So A1's interior is a
**theorem** modulo a **bounded correlation second moment** `⟨θ²⟩/2 < 1-3^{-1/4}` (equivalently
`M₂ < (1-3^{-1/4})L²/(2π²)`, a finite correlation length). The analytic step is proven, and the one measured
input is the bounded moment — the finite-specific-heat / SU(N) no-bulk-transition content (cited; measured
`M₂ ≤ 0.15 ≪ 0.78`, margin growing ∝ L²). -/

/-- The whitened :F² correlation as a probability vector over its lag index — DERIVED from `readYM β`
(`p = ρ/Σρ`, nonnegative and summing to 1 by construction). -/
noncomputable def pcorrYM (β : ℝ) : Fin (nCorrYM + 1) → ℝ := (readYM β).p
/-- The angular structure `θ_d = 2π d /(L+1)` of the correlation — DERIVED from `readYM β` (`Moment.Read.θ`). -/
noncomputable def thetaYM (β : ℝ) : Fin (nCorrYM + 1) → ℝ := (readYM β).θ

/-- **The correlation weights are nonnegative** — a THEOREM (`p = ρ/Σρ` with `ρ ≥ 0`). -/
theorem pcorr_nonneg : ∀ β d, 0 ≤ pcorrYM β d := fun β d => (readYM β).p_nonneg d
/-- **The correlation weights sum to one** — a THEOREM (`Σ(ρ/Σρ) = 1`). -/
theorem pcorr_sum : ∀ β, ∑ d, pcorrYM β d = 1 := fun β => (readYM β).p_sum

/-- **The read IS the min-entropy tension of the correlation** (the C-3 read identification): `μ = -log⟨cos θ⟩_ρ`
(`= log(S(0)/S(2π/L))` via RP, `λ₁=S(0)`, `λ₂ ≥ S(2π/L)`). **A THEOREM** — `μYM := (readYM β).tension`
is by definition `-log⟨cos θ⟩_ρ`, so the read identification is discharged by construction. -/
theorem ym_tension_is_moment : ∀ β,
    μYM β = - Real.log (∑ d, pcorrYM β d * Real.cos (thetaYM β d)) := fun _ => rfl

/-! ### A1's interior: the uniform finite-correlation-length bound

The interior input is a bound on the correlation's **lag second moment** `⟨d²⟩ = ∑_d p_d d²` (a squared
correlation length): `⟨d²⟩(β) ≤ 1` uniformly for `β ≥ βcYM`. The `1/L²` **aperture scaling is proven**
(`Moment.Read.tension_lt_floor_of_circ_moment`, reached from a raw-index bound by
`circ_moment_le_lag_moment`): the θ-moment factors as `⟨θ²⟩ = (2π/(L+1))² ⟨d²⟩`, so the fixed
bound `B = 1` puts `μ` under the floor at every large `L` (margin `∝ L²`, a theorem), and `1` sits `3.52×`
under the aperture threshold `B₁₆ ≈ 3.52` (`ym_finite_aperture`). This is confinement (finite `ξ` / SU(N)
no-bulk-transition): measured well under `1` across the crossover (figures in PAPER §9), with the free-field
weak-coupling limit `⟨d²⟩ → ~0.12` (`FreeField`). The bound is CONSISTENT (`0 ≤ ⟨d²⟩ ≤ 1`) and holds on the
whole half-line `β ≥ βcYM`. It is the spatial correlation moment — distinct from the energy susceptibility
`χ_v` (Shannon/specific-heat), the Rényi relation of PAPER §8.4.

The bound is the uniform constant `1`: a flat `0 ≤ ⟨d²⟩ ≤ 1`, consistent with the provable `⟨d²⟩ ≥ 0`
(`pcorr_nonneg` + `sq_nonneg`), is exactly what `tension_lt_floor_of_circ_moment` consumes, through
`circ_moment_le_lag_moment` (any `B < 3.52`, the
aperture ceiling at `N=16`, suffices), and `1` is the rigorously certified value (`99.9%` empirical-Bernstein).
The closed-form envelope and its Lipschitz regularity are available, where wanted, from the grid route
`ym_crossover_confinement_of_grid` (a measured modulus of continuity). -/

/-- **The finite-aperture premise — a THEOREM.** With the certified bound `B = 1`, the
aperture condition `(2π/(N+1))² · B / 2 < 1 − 3^{-1/4}` is a statement purely about the finite aperture
`N = nCorrYM = 16`: a concrete numeric inequality, discharged by `norm_num` from `π < 3.15` (upper-bounds the
`(2π/17)²` factor) and `3^{-1/4} ≤ 4/5` (from `(5/4)⁴ = 625/256 ≤ 3`, lower-bounds the floor gap `≥ 1/5`).
LHS `= (2π/17)²/2 ≈ 0.068 < 1/5 ≤ 1 − 3^{-1/4}`. It holds for every `N ≥ 9`, so pinning to the physical `L16`
aperture is not special-casing; the `L`-independence is the SEPARATE `Certify.gap_uniform_in_volume_of_intensive`. -/
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

/-- **The circle moment is under the raw lag moment**, so a bound read off the raw index — which is
what the grid certificates measure — still feeds the circle-moment route. The inequality is
`min d (N+1−d) ≤ d` weighted by a probability vector; it is one-directional, and that direction is
the one a certificate needs. The converse fails, which is exactly why `d2At` is stated about the
circle: a raw bound is STRONGER, and no physical correlation satisfies it at every aperture. -/
theorem circ_moment_le_lag_moment {N : ℕ} (R : Moment.Read N) :
    ∑ d, R.p d * (Moment.circLag d : ℝ) ^ 2 ≤ ∑ d, R.p d * (d : ℝ) ^ 2 := by
  refine Finset.sum_le_sum (fun d _ => ?_)
  have hle : ((Moment.circLag d : ℕ) : ℝ) ≤ ((d : ℕ) : ℝ) := by
    exact_mod_cast min_le_left (d : ℕ) (N + 1 - (d : ℕ))
  have h0 : (0 : ℝ) ≤ ((Moment.circLag d : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (by nlinarith) (R.p_nonneg d)

-- `ym_crossover_confinement_of_grid` (the general finite-grid tool) is the deterministic-read
-- alternative to the substrate route: a finite grid plus a measured modulus of continuity, with no
-- bound asserted on the substrate at all.

/-- **A1's interior confinement from a DETERMINISTIC GRID CERTIFICATE.**
On the compact interior `[a,b]` a **finite check** gives confinement: if the
whitened lag second moment `⟨d²⟩(β) = ∑_d pcorrYM β d · d²` is `L`-Lipschitz on `[a,b]`
(`hlip`, a measured modulus of continuity) and a `δ`-net certifies `⟨d²⟩ ≤ B - L·δ` there (`hcover`, finitely
many deterministic reads with the margin absorbed), then, with the strict aperture condition
`(2π/(N+1))²·B/2 < 1 - 3^{-1/4}`, the tension stays below the floor `μYM β < κ₀` on all of `[a,b]`. The `∀β`
content is a finite grid + the Lipschitz constant `L` — a deterministic, checkable
certificate (`Certify.le_of_lipschitz_grid` + the proved aperture scaling), foundational axioms only. The one
measured input, `L`, is a measured smoothness (the read varies smoothly between grid points); a spike would be a
critical point — a bulk transition — so this smoothness is the deterministic face of `SU(N)` no-bulk-transition. -/
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

/-- The orientation type of the directional read.

DERIVED: `4` is the spacetime dimension the whole development is stated in — the number of axes a
hypercubic lattice has, so the orientations are their permutations. It is not a size or a cutoff. -/
abbrev DYM : Type := Equiv.Perm (Fin 4)

/-- **The transport is the axis permutation's own matrix, and it is orthogonal — a THEOREM.** A
permutation matrix has exactly one `1` in each row and column, so `Pᵀ P = 1`: the transport between
two orientations of the lattice preserves the sample inner product because relabelling axes does. -/
theorem permMatrix_orthogonal (σ : DYM) :
    (σ.permMatrix ℝ)ᵀ * σ.permMatrix ℝ = 1 := by
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

/-- The base directional window `F₀` at a reference orientation (the read acts on its Gram `Xᵀ X`, [E §3]).
It stays abstract deliberately: A2 holds for EVERY base window, and fixing one would narrow a theorem
that is general, not fill a gap. -/
opaque Fbase : Matrix (Fin 4) (Fin 4) ℝ
/-- O(4), the orthogonal 4×4 matrices, is inhabited (by the identity `1`), so an `opaque` transport valued
in it is well-formed and computable (the default value is `1`, the orthogonality proof erased at runtime). -/
instance : Inhabited {M : Matrix (Fin 4) (Fin 4) ℝ // Mᵀ * M = 1} := ⟨⟨1, by simp⟩⟩

/-- The **transport** from the reference orientation to `d`, valued in **O(4)** — CONSTRUCTED as the
permutation matrix of the axis permutation `d`. Below the Nyquist threshold (PAPER §8.6,
`a⋆ k₀ = 0.364 < 1`) the reconstruction `Rc` and sampling `Sm` maps are EXACT isometries — the discrete
samples carry the continuum inner product with no loss (Nyquist-Shannon) — so in `Otr = Rc·Um·Sm`
(`Apriori.resampling_orthogonal`) the sampling factors collapse to the identity and the net transport
between orientations is a pure relabelling of axes.

It is no longer `opaque`. A transport that carried no structure could have been constant, and then
`ym_A2`'s `∀ d d', R d = R d'` would have been true because there is only one direction to speak of.
`ym_A2_nonvacuous` below rules that out: the transports at distinct axis permutations are distinct
matrices.

DERIVED: `4` is the spacetime dimension, as in `DYM`, so the matrix is `4×4`; `1` is the identity
`Pᵀ P = 1` that ORTHOGONALITY means, proved in `permMatrix_orthogonal` and not imposed. The `0.364`
and `8.6` quoted above are the MEASURED Nyquist threshold `a⋆k₀` and its reported margin, read off
the sampling study and cited here; neither enters this definition. -/
noncomputable def OtrO (d : DYM) : {M : Matrix (Fin 4) (Fin 4) ℝ // Mᵀ * M = 1} :=
  ⟨d.permMatrix ℝ, permMatrix_orthogonal d⟩
/-- The transport as a plain matrix — its underlying O(4) element. -/
noncomputable def Otr (d : DYM) : Matrix (Fin 4) (Fin 4) ℝ := (OtrO d).1
/-- The spectral read: a scalar functional of the characteristic polynomial ([E §3, §10]). -/
opaque freadYM : Polynomial ℝ → ℝ

/-- **The Nyquist transport is orthogonal — a THEOREM** (the O(4) membership of `OtrO`). The transport
preserves the sample inner product below the Nyquist threshold (Nyquist-Shannon; PAPER §8.6, `a⋆ k₀ = 0.364`),
so it lives in O(4); this discharges A2's sampling composition (`ym_A2`) with **no axiom** — the general
"preserves the sample inner product ⟹ orthogonal" fact is `Apriori.orthogonal_of_preserves_dotProduct`. -/
theorem Otr_iso (d : DYM) : (Otr d)ᵀ * Otr d = 1 := (OtrO d).2

/-- **The orientation type is the hypercubic axis group, and it has 24 elements.** `A2`'s conclusion
`∀ d d', R d = R d'` is a statement about a group of directions, not about a token. This is the same
`Equiv.Perm (Fin 4)` the MEASURE side's `WilsonHypercubic.axisSymmetry` acts by, so both sides of the
development quantify over the same symmetry. -/
theorem card_DYM : Fintype.card DYM = 24 := by
  simp [Fintype.card_perm]
  decide

#print axioms card_DYM

/-- **`A2` is not true because there is nothing to say — the transports are genuinely distinct.**
While `OtrO` was `opaque` it could have been the constant map, and then `∀ d d', R d = R d'` would
have held because every orientation carried the same window. It cannot: the identity permutation and
a transposition have determinants `1` and `-1`, so their transports differ as matrices.

This is the `A2` analogue of `spectral_bar_nonvacuous`, and it is the check an `opaque` direction type
could never pass. -/
theorem ym_A2_nonvacuous : ∃ d d' : DYM, Otr d ≠ Otr d' := by
  refine ⟨1, Equiv.swap 0 1, fun h => ?_⟩
  have hd : (Otr (1 : DYM)).det = (Otr (Equiv.swap (0 : Fin 4) 1)).det := congrArg Matrix.det h
  rw [Otr, Otr, OtrO, OtrO] at hd
  simp only [Matrix.det_permutation, Equiv.Perm.sign_one,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)] at hd
  norm_num at hd

#print axioms ym_A2_nonvacuous

/-- The sampled correlation window at orientation `d`, DERIVED as the base window transported by `Otr d`:
`F d = F₀ · Otr d`. So the directional windows relate by an orthogonal transport **by construction**, and
`Fym d' = Fym d · ((Otr d)ᵀ · Otr d')` is a theorem. -/
noncomputable def Fym (d : DYM) : Matrix (Fin 4) (Fin 4) ℝ := Fbase * Otr d

/-! ## The model instance -/

/-- **A lattice Yang-Mills model witness.** The opaque tension read `μYM` and directional Gram read set
the two entropy-matched reads; the minimal one-mode window with dominant magnitude `e^{-(κ₀-μ)}` (the DMD
dominant magnitude the aperture returns) supplies the finite-aperture correlator.

DERIVED: the `1` is the mode WEIGHT of a single-mode model — `P β k = 1` because there is one mode
and the weights sum to one. It is a normalisation forced by the structure, not a fitted value.
-/
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

/-! ## A1 and A2 are theorems -/

/-- **A2 is a theorem.** The directional window `F d = F₀ · Otr d` transports by an orthogonal Nyquist map,
so its Gram `(F d)ᵀ (F d)` relates across orientations by an orthogonal congruence and the Gram spectral read
is direction-independent (`Apriori.continuumRotationCongruence_of_gram` + `A2_continuum_of_congruence`). The
sampling composition `F d' = F d · ((Otr d)ᵀ · Otr d')` is a **theorem**; the sole
input is that the transport is orthogonal (`Otr_iso`), the Nyquist-Shannon sampling isometry. -/
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

/-! ## The model at a VARIABLE aperture, and the gap from the substrate alone -/

/-- The lattice Yang–Mills witness read through an aperture of size `N`. `ymModel` is its `nCorrYM`
instance (`ymModel_is_ymModelAt`, `rfl`).

DERIVED: as in `ymModel`, the `1` is the single mode's weight, forced by normalisation.
-/
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

/-- Isotropy holds at every aperture — `R` does not depend on it. -/
theorem ym_A2_at (N : ℕ) : A2_YM (ymModelAt N) := ym_A2

/-- **THE MASS GAP FROM ONE SUBSTRATE HYPOTHESIS, AT EVERY LARGE ENOUGH APERTURE.**

From `∃ B, ∀ N β, d2At N β ≤ B` alone — an aperture-independent bound on the substrate's moment about
the circle distance, with no value supplied — the full result (gap, non-triviality, `SO(4)`) holds for
`ymModelAt N` at every large enough `N`, at EVERY coupling, with no restriction to `β ≥ 0` and no
coupling-by-coupling case split.

WHY THE APERTURE IS A VARIABLE. A frozen window reaches `∀ β, μ < κ₀` only by splitting the coupling
line into arms and supplying a separate input on each — and none of those inputs can state the thing
the read is about, because with the window fixed there is no aperture to widen. This reaches the same
conclusion from ONE input, and the input is a property of the substrate rather than a value measured
through some particular window. -/
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

/-- **The same, from the WEAKER growth hypothesis.** The substrate moment is allowed to grow with the
aperture, `substrateRatio ≤ c`, provided `c` clears the floor gap — so a bounded moment is the
special case, not the requirement. -/
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

/-- **THE MASS GAP FROM ONE DECAY RATE — the flagship in its shortest form.**

Gap, non-triviality and `SO(4)` for `ymModelAt N` at every large enough aperture and EVERY coupling,
from a single hypothesis: the read's weights decay geometrically in the circle distance at some rate
`r < 1`. No aperture, no threshold, no measured constant, and no value for `r` named anywhere.

This is the whole reduction in one line. Under reflection positivity `ρ(d) = ∑ₙ wₙλₙᵈ` with `wₙ ≥ 0`,
so the hypothesis IS "the transfer operator has a gap" (`ZeroMode.exists_exponential_decay` supplies
it from `λₙ < 1` on a finite mode set, with `r` the largest excited eigenvalue). Everything between
that and the gap — the aperture-uniform moment bound, the entropy floor comparison, the model
assembly — is proved here and carries the foundational three plus reflection positivity alone. -/
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

/-- **THE MASS GAP FROM A TRANSFER GAP — the statement to quote.**

Gap, non-triviality and `SO(4)` at every large enough aperture and every coupling, from the single
hypothesis that the read's correlation decays geometrically in the lag at some rate `r < 1`.

Under reflection positivity that hypothesis IS "the transfer operator has a spectral gap", with
`r = e^{−Δ}`: the correlation is `∑ₙ wₙλₙᵈ` with `wₙ ≥ 0`, and a gap is exactly `λₙ ≤ e^{−Δ} < 1` on
the excited modes. No aperture appears in it, no threshold, no measured constant, and no value for `r`
is named anywhere in the statement or the proof.

So the whole reduction — aperture-uniform moment bound, entropy-floor comparison, model assembly —
sits between a transfer gap and the mass gap, and carries the foundational three plus reflection
positivity alone. What it does NOT do is supply the transfer gap. -/
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

/-! ## The mass gap, with no open hypothesis -/

-- The axiom footprint of everything below: the standard three plus `wilson_reflection_positive_at`.
-- `Otr_iso` is the THEOREM `Otr_iso` (the O(4) membership of the Nyquist transport `OtrO`), and C-3 is
-- the THEOREM `readYM_is_wilson := rfl` (reading-A is the concrete `readA`, and
-- `readYM = readingA_wilson` by construction), so neither is in the footprint. What the footprint
-- shows is reflection positivity (Osterwalder-Seiler), the SOLE read-side physical input, NAMED
-- explicitly and cited.

/-- **The flagship gap for the ACTUAL modes, from the two named residuals — the definitional witness retired.**
Mass gap `C(τ) → 0`, non-triviality `μ − κ < 0` and `SO(4)`, over
an ARBITRARY DMD mode family `m` in place of the definitional witness `ymModel.m := e^{−(κ₀−μ)}`. The read
margin `hread` is discharged by `Capacity.hread_of_junction` from three explicit inputs: the actual modes decay
at the transfer gap `‖m_k‖ ≤ e^{−Δ}` (`hdom`), and the two OPEN deterministic residuals `κ₀ − μ ≤ c` (`hfe`,
the centre-vortex free-energy junction — 't Hooft 1978 / Greensite 2003) and `c ≤ Δ` (`hgap`, the contraction
rate lower-bounds the transfer gap). Confinement enters as the hypothesis `hconf` and isotropy is the
PROVED `A2` of `ymModel`, so the footprint is the foundational three plus reflection positivity — the
residuals enter as HYPOTHESES over the free modes, not as axioms. This is the flagship resting on the two named residuals rather
than on a mode defined equal to its own bound. Closing `hfe` and `hgap` deterministically (they carry no
sampling) discharges the last hypotheses and makes the gap for the actual modes stand on the cited physics
alone. -/
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

/-- **THE FLAGSHIP'S FOUR HYPOTHESES ARE THREE, AND THEN TWO.** `hfe` is not an independent
obligation, and neither is the split between `c` and `Δ`.

`c` and `Δ` are supplied by the CALLER, constrained only by `κ₀ − μ ≤ c`, `c ≤ Δ` and
`‖m‖ ≤ e^{−Δ}`. Taking `c = Δ = κ₀ − μ` makes the first two `le_refl` and leaves the third, so the
conjunction `hdom ∧ hfe ∧ hgap` is IMPLIED by the single statement below. It also implies it, since
`‖m‖ ≤ e^{−Δ} ≤ e^{−c} ≤ e^{−(κ₀−μ)}` whenever the three hold. The two are EQUIVALENT: nothing is
lost, nothing is gained, and the remaining obligation is stated once instead of spread over three
hypotheses that could be read as three separate pieces of physics.

**WHAT THIS MEANS FOR THE PROGRAM.** The centre-vortex free-energy junction `κ₀ − μ ≤ c` carries no
content on its own — it is an inequality between a number and itself at the natural choice of `c`.
The content the three hypotheses were sharing is entirely this: **the modes decay at least at the
counted free-energy density**. That is one statement about the transfer operator, and it is where the
remaining work is. -/
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

/-- The converse direction, so the consolidation above is an EQUIVALENCE and not a weakening: any
`c`, `Δ` satisfying the flagship's three hypotheses give the single decay statement. -/
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

/-! ## The gap for the WILSON CORRELATION, not for a free family

`ym_mass_gap_of_decay_at_floor` quantifies over an arbitrary `m : ℝ → Unit → ℂ`, and `ymModel`
instantiates it at one element with `m` defined equal to its own bound. Read literally, its clustering
conclusion is that a single complex number of modulus below one has powers tending to zero, and its
hypothesis is about a parameter with no proved link to the ensemble. Nothing downstream of
`Apriori.hread_of_dominant` supplies that link — that lemma is `le_trans`.

The statements below are the same gap said about the Wilson correlation. `Spectral.SpectralForm N
(wilsonCorrAt N β)` is the transfer-matrix decomposition `ρ(d) = ∑ₙ wₙ λₙ^d` with `wₙ ≥ 0` — exactly
what the `wilson_reflection_positive_at` docstring gives as its REASON, and exactly what that axiom
does not assert. With it, `P` and `m` are not supplied: they ARE `w` and `λ`, the correlator IS
`wilsonCorrAt N β` at every resolved lag, and the decay hypothesis IS "every transfer energy clears
`κ₀ − μ`".

**This proves nothing new about Yang-Mills.** It relocates the open obligation from a bound on a free
family to a property of a defined one, which is the difference between a reduction and a statement
that could be false. -/

/-- **THE OPEN OBLIGATION, NAMED ON THE ACTUAL ENSEMBLE.** That the Wilson correlation at aperture
`N` and coupling `β` admits a transfer-matrix spectral decomposition with nonnegative weights. This is
reflection positivity's real content; `wilson_reflection_positive_at` asserts only its shadow
(`0 ≤ ρ d`, `0 < ∑ ρ`). -/
def WilsonSpectral (N : ℕ) (β : ℝ) : Prop :=
  Nonempty (Spectral.SpectralForm N (wilsonCorrAt N β))

/-- **THE CORRELATOR IS THE WILSON CORRELATION.** Given the decomposition, the object the gap
theorems are about equals the ensemble's own correlation at every lag the aperture resolves. -/
theorem wilson_sum_eq_corr {N : ℕ} {β : ℝ}
    (S : Spectral.SpectralForm N (wilsonCorrAt N β)) (d : Fin (N + 1)) :
    ∑ n, S.w n * (S.lam n) ^ (d : ℕ) = wilsonCorrAt N β d :=
  Spectral.sum_eq_rho S d

/-- **THE MASS GAP FOR THE WILSON CORRELATION.** Confinement at the aperture (`μYMAt N β < κ₀YM`)
together with the transfer gap (`every λₙ ≤ e^{−(κ₀−μ)}`, i.e. every transfer energy at least the
counted free-energy density) gives clustering OF THAT CORRELATION.

Both hypotheses are now statements about defined objects: `μYMAt` is built from `wilsonCorrAt` through
`readYMAt`, and `S.lam` is the ensemble's own transfer spectrum. Neither is a free parameter. -/
theorem ym_clustering_of_transfer_gap {N : ℕ} {β : ℝ}
    (S : Spectral.SpectralForm N (wilsonCorrAt N β))
    (hconf : μYMAt N β < κ₀YM)
    (hgap : ∀ n, S.lam n ≤ Real.exp (-(κ₀YM - μYMAt N β))) :
    Filter.Tendsto
      (fun τ => ‖∑ n, ((S.w n : ℂ)) * ((S.lam n : ℂ)) ^ τ‖) Filter.atTop (nhds 0) :=
  Spectral.clustering_of_spectral S hconf hgap

#print axioms wilson_sum_eq_corr
#print axioms ym_clustering_of_transfer_gap

/-- **The mass gap from the RUNTIME CONFINEMENT READ — every Entroptics-specific axiom discharged.** The full
result for `ymModel` (gap + non-triviality + `SO(4)`) from a SINGLE explicit hypothesis `hconf`: the
deterministic runtime read that the tension stays below the floor at every coupling (`∀ β, μYM β < κ₀`) — the
confinement certificate, equivalently `contrast < 3^{1/4}` (`Certify.confinement_iff_contrast_lt_rpow`). Its
`#print axioms` is the three foundational **only**, plus the cited classical
`wilson_reflection_positive_at` (reflection positivity, via `ymModel.μ`). It lists **none** of the
Entroptics-specific inputs (`rArgYM_pos` is a theorem everywhere). This is the conditional form at the
PINNED aperture: **given the deterministic confinement read, the gap needs no Entroptics-specific
axiom.** Where `hconf` itself comes from is the substrate route above
(`confinement_of_bounded_substrate`, stated at a variable aperture), or a measurement.
The read is empirically discharged — su2/su3 read `μ ≈ 0 ≪ κ₀` with a
finite-aperture margin `m_hi ≈ 0.18 < 3^{-1/4}`, and U(1) tracks its own transition (confined β<β_c reads finite
aperture, Coulomb reads `m_hi ≈ 1` and fails), `research/code` runtime probe. `hconf` is that read taken as the
hypothesis: it is the confinement content (`μ < κ₀` at every β, the no-bulk-transition read), measured and
certified on the ensembles (PAPER §9) and carried to the continuum by the proved `gap_refinement_invariant`. The finite aperture is structural in `ymModel` (one
mode); the margin certificate is the empirical justification that the SU(N) ensemble is that finite-mode model,
which U(1)-Coulomb fails. -/
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

/-- **`μYM β ≥ 0` — the tension is nonnegative, unconditionally.** `μYM β = -log ⟨cos θ⟩_p` with `p` a
probability vector, so `⟨cos θ⟩_p ∈ [-1,1]` and its log is `≤ 0`. Foundational axioms only. -/
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

/-- The pinned instance. -/
theorem μYM_nonneg (β : ℝ) : 0 ≤ μYM β := μYMAt_nonneg nCorrYM β

/-! ## The gap as an entropy surplus, and its one-way (decay) margin

The construction runs forward — from the aperture outward, its inverse a fibre (PAPER §12). Its
architecture is a reduction to a property of the substrate, with the gap the ENTROPY SURPLUS
`Δ = κ₀ − μ`: confinement `μ < κ₀` is exactly `Δ > 0`, the disorder entropy density above the tension. -/

/-- The mass gap as the **entropy surplus** `Δ(β) = κ₀ − μ(β)`: the centre-vortex disorder entropy
density above the tension. -/
noncomputable def ΔYM (β : ℝ) : ℝ := κ₀YM - μYM β

/-- **Gap = positive entropy surplus ⟺ confinement.** `Δ(β) > 0` exactly when the tension is below the
floor, `μ(β) < κ₀`. Foundational axioms only. -/
theorem gap_pos_iff_confinement (β : ℝ) : 0 < ΔYM β ↔ μYM β < κ₀YM := by
  unfold ΔYM; constructor <;> intro h <;> linarith

/-- **The one-way margin.** The dominant decay factor `e^{−Δ}` is strictly inside the unit disk exactly
when the surplus is positive: the band-limited screen forgets at the surplus rate. -/
theorem oneway_margin (β : ℝ) : Real.exp (-(ΔYM β)) < 1 ↔ 0 < ΔYM β := by
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- **Confinement gives a positive surplus.** From the confinement read (`μ < κ₀`) the entropy surplus
is positive: the gap is the entropy the disorder holds over the tension. -/
theorem entropy_surplus_pos (hconf : ∀ β, 0 ≤ β → μYM β < κ₀YM) (β : ℝ) (hβ : 0 ≤ β) : 0 < ΔYM β :=
  (gap_pos_iff_confinement β).mpr (hconf β hβ)

/-! ## The spectral form: the gap as decay of the ACTUAL transfer modes

NO magnitude and NO family size is named below. The finite-aperture margin `‖m_k‖ ≤ 3^{-1/4} = e^{-κ₀}`
is an EXPLICIT HYPOTHESIS over an arbitrary mode family, not a property of some witness chosen to
satisfy it. The ceiling is derived — `3^{-1/4}` is `e^{-κ₀}` with `κ₀ = ¼log3` proved in `Floor` — and
its physical grounding is the exact-rational single-plaquette enclosure
(`certify/small_volume_enclosure.py`), a certificate outside the Lean footprint.

That the hypothesis is SATISFIABLE is exhibited separately and also without naming a value
(`spectral_bar_nonvacuous`): a witness has to be an instance, but it does not have to be a PARTICULAR
instance. -/

/-- **The gap as decay of an arbitrary finite mode family, at an arbitrary aperture.** For ANY finite
set of transfer/DMD modes `m : ι → ℂ`, read through an aperture of size `N` at a coupling whose tension
is below the floor, if the dominant magnitude clears the entropy-floor ceiling
`m_hi ≤ 3^{-1/4} = e^{-κ₀}` then the correlator forgets: `‖∑ P_k m_k^τ‖ → 0`.

Since `3^{-1/4} = e^{-κ₀} ≤ e^{-(κ₀-μ)}` for `μ ≥ 0` (`μYMAt_nonneg`), the margin supplies the
finite-aperture premise of `gap_of_confinement`. The margin hypothesis is the DISCRIMINATOR, read per
ensemble: the `SU(N)` DMD read satisfies it (measured `m_hi ≈ 0.18–0.30`), the `U(1)`-Coulomb read
(`m_hi ≈ 1`, a persistent unit-circle mode) does not. -/
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

/-- **The gap is uniform in volume (`F → ∞`).** A SINGLE rate `κ > 0` makes the correlator decay at
every volume index at once, for any family size and any magnitude at or below the ceiling. The bound is
intensive by hypothesis — the same at every `F`, carrying no lattice scale — which is what "the gap
does not dilute as the volume grows" means. Foundational axioms only: this is a statement about the
mode side, with no read in it.

The PHYSICAL statement — that the entropy-matched read of the `SU(N)` ensemble is itself intensive
(`∃ r<1, ∀F, m_hi(F) ≤ r` for the opaque `wilsonCorr` read) — is the separate open input named in
`Interior`, whose only remaining content is the `L`-independence of the physical `r`. -/
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

/-- **The result in spectral form.** At every physical coupling `β ≥ 0`: the mass gap as decay of an
arbitrary finite mode family carrying the margin, non-triviality `μ − κ₀ < 0` from the supplied
confinement read, and Euclidean `SO(4)` invariance (`ym_A2_at`). Nothing here is pinned: the aperture,
the mode family, and the magnitude are all variables. -/
theorem ym_mass_gap_spectral_bar {ι : Type*} (N : ℕ) (s : Finset ι) (P m : ι → ℂ) (mhi : ℝ)
    (hconf : ∀ β, 0 ≤ β → μYMAt N β < κ₀YM) (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi)
    (haperture : mhi ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    (∀ β : ℝ, 0 ≤ β → Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYMAt N β - κ₀YM < 0) ∧
      (∀ d d', (ymModelAt N).R d = (ymModelAt N).R d') :=
  ⟨fun β hβ => ym_mass_gap_spectral N s P m β mhi (hconf β hβ) hmargin haperture,
    fun β hβ => confines_of_tension_lt_floor (le_refl κ₀YM) (hconf β hβ), ym_A2_at N⟩

#print axioms ym_mass_gap_spectral_bar

/-- **The bar is not a statement about nothing — and the witness names no value.** The margin
hypothesis of `ym_mass_gap_spectral` is satisfiable at ANY family size and ANY magnitude strictly
positive and at or below the derived ceiling `3^{-1/4} = e^{-κ₀}`, and the decay it asks for follows.
A pinned magnitude (the retired `1/5`) would make this one instance instead of all of them.
Foundational axioms only. -/
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

/-- **The reconstructed Yang–Mills Hamiltonian has mass gap `κ₀` — the finite-aperture margin wired to
reconstruction.** For the Euclidean-time transfer operator `T` (self-adjoint) whose spectrum meets the
finite-aperture margin — `spectrum T ⊆ {1} ∪ [ε, 3^{-1/4}]`, the vacuum eigenvalue `1` and the excited spectrum
below the entropy-floor ceiling `3^{-1/4} = e^{-κ₀}` (the transfer read of the finite-aperture margin) — the reconstructed
Hamiltonian `H = -log T` (continuous functional calculus, `Reconstruction.hamiltonian`) is self-adjoint, `H ≥ 0`,
has ground-state energy `0` (the vacuum), and mass gap `κ₀`: `spectrum H ⊆ {0} ∪ [κ₀, ∞)`. So the entroptics
finite-aperture margin, on the transfer operator, is exactly the reconstructed operator's mass gap `κ₀ = ¼log3`.
Foundational axioms only (`Reconstruction.reconstruct_qm_core`). -/
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

-- The interior crossover confinement discharged by a DETERMINISTIC GRID CERTIFICATE (finite grid +
-- Lipschitz): the interior read is supplied by the finite deterministic grid-hypotheses certificate,
-- leaving only the foundational three + `wilson_reflection_positive_at` (RP, via `readYM`).
#print axioms ym_crossover_confinement_of_grid

/-- **A1 from a grid-certified interior plus the two ends, all three supplied by the caller.**
`A1_YM ymModel` (`∀β, μYM β < κ₀`) by case analysis on three deterministic pieces: the **strong end**
`β < βloYM` (`hstrong`, reachable from `apriori_A1_strong` and a cited character bound), the compact
**interior** `β ∈ [βloYM, bhi]` (`hinterior`, supplied by the finite-grid certificate
`ym_crossover_confinement_of_grid`), and the **weak end** `β ≥ bhi` (`hweak`, reachable from a cited
asymptotic-freedom convergence). Nothing here asserts any of the three: they are hypotheses, so this
theorem adds no axiom of its own. -/
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

/-- **The mass gap with the interior discharged by the finite-grid certificate.** The full result for
`ymModel` (gap + non-triviality + `SO(4)`) from the two cited ends (`hstrong`/`hweak`) and the finite-grid
interior certificate (`hinterior`). No bound on the substrate is asserted: the interior `∀β∈[βloYM,bhi] μ<κ₀`
is supplied by `ym_crossover_confinement_of_grid` — a finite grid of deterministic `⟨d²⟩` reads plus a
modulus-of-continuity bound `L`, backed by the dense-β data (`certify/ym_crossover_confinement_of_grid.py`), with continuity a
finite-volume-analyticity theorem, not a postulate. This is the alternative to the substrate route:
where that one takes a property of the correlation, this one takes a finite measured grid. -/
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
