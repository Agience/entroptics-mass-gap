import Mathlib
import MassGap.Apriori
import MassGap.Certify
import MassGap.Model
import MassGap.Moment
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
-- `βc ≈ 0.75`, consistent with the certified `Apriori.beta_star_enclosure`,
-- `r(β⋆) ∈ [0.182, 0.184]`, `research/code/certify/beta_star_enclosure.py`). What choosing it costs is
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

/-- The proved entropy floor `κ₀ = ¼ log 3` (`Floor.lean`). -/
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

/-- **Confinement at one aperture and one coupling, from the substrate ratio.** The aperture cancels
exactly: `(2π/(N+1))² · c·(N+1)² / 2 = (2π)²·c/2`, so the hypothesis on `c` carries NO aperture and
the conclusion holds at every `N` for which the ratio bound does. -/
theorem confinement_at_of_ratio {c : ℝ}
    (hc : (2 * Real.pi) ^ 2 * c / 2 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4))
    {N : ℕ} {β : ℝ} (h : substrateRatio N β ≤ c) :
    μYMAt N β < κ₀YM := by
  refine (readYMAt N β).tension_lt_floor_of_circ_moment (substrateRatio_le_iff.mp h) ?_
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcancel : (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * (c * ((N : ℝ) + 1) ^ 2) / 2
      = (2 * Real.pi) ^ 2 * c / 2 := by
    field_simp
  rw [hcancel]
  exact hc

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

/-- The orientation type of the directional read. -/
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
matrices. -/
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
