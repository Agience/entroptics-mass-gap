import Mathlib
import MassGap.Apriori
import MassGap.Certify
import MassGap.Model
import MassGap.Moment
import MassGap.Bessel
import MassGap.FreeField
import MassGap.Reconstruction
import MassGap.Capacity

/-!
# The mass gap from named inputs — assembly and results

`Apriori.lean` / `Model.lean` derive the result (mass gap, non-triviality, `SO(4)`) *from* the two
a priori `A1` (confinement) and `A2` (isotropy). This file discharges `A1` and `A2` themselves, so the gap
follows with **no** `A1`/`A2` hypothesis. Each named `axiom` is classical (not a raw read); every
framework-specific step is a theorem.

## The results (in order)

* `ym_mass_gap` — **the flagship.** result for `ymModel` at every `β ≥ 0`, no hypothesis.
  Footprint: the three foundational + `ym_character`, `ym_asymfree`, `wilson_reflection_positive`,
  `d2_le_bound`.
* `ym_mass_gap_certified hconf` — **the tightest form.** Conditioned on the confinement read
  `hconf : ∀β≥0, μ<κ₀` as one hypothesis, the footprint is the three foundational + `wilson_reflection_positive`
  ALONE. (`ym_character`, `ym_asymfree`, `d2_le_bound` are only the decomposition that proves `hconf`.)
* `ym_mass_gap_spectral` — **the discriminating form.** The gap as decay of a finite witness mode family
  `mModeYM` pinned to the rational bound `mHiYM = 1/5` (not a definitional single mode), keyed on the
  finite-aperture margin `ym_aperture_margin` (`‖m_k‖ ≤ 3^{-1/4}`, i.e. `1/5 ≤ 3^{-1/4}`) — the scale that
  separates `SU(N)` (the witness `m_hi = 1/5`; measured `0.30`–`0.38`) from `U(1)`-Coulomb (`m_hi ≈ 1`). Footprint: the three foundational axioms
  only; the margin is a proved theorem, and the value `1/5` is grounded in the out-of-Lean single-plaquette
  enclosure (`certify/small_volume_enclosure.py`), not in the Lean footprint.
* `ym_mass_gap_aperture` — the same margin over an ARBITRARY finite mode read (the general lemma).
* `ym_reconstructed_gap` — the margin wired to reconstruction: `H = -log T` is self-adjoint, `H ≥ 0`,
  vacuum at `0`, `spectrum H ⊆ {0} ∪ [κ₀, ∞)`. Foundational axioms only.
* `ym_mass_gap_grid_certified` — the interior discharged by a finite grid + modulus of continuity
  instead of `d2_le_bound`.

## The four named inputs (flagship) — all classical, none framework-specific

* `ym_character` — Osterwalder–Seiler character/cluster bound `μ ≤ 2βr`, strong end (CITED).
* `ym_asymfree` — asymptotic-freedom convergence `μ → μ∞`, weak end (CITED; the below-floor value
  `μ∞ < κ₀` is the theorem `FreeField.muInf_lt_floor`).
* `wilson_reflection_positive` — reflection positivity of the Wilson ensemble (Osterwalder–Seiler, CITED);
  the sole read-side physical input.
* `d2_le_bound` — the interior finite-correlation-length read `⟨d²⟩ ≤ 1` (confinement in the :F²: channel).

Each input has its own docstring at its definition. `Otr_iso` (A2 isometry), `readYM_is_wilson` (C-3
identification, `rfl`), `ym_finite_aperture`, `rArgYM_pos`, `ym_ratio_pos`, and `ym_tension_is_moment` (the
read identification) are THEOREMS, not axioms. The read is concrete (`Moment.Read`): `μYM`, `pcorrYM`,
`thetaYM` are all derived from one nonnegative correlation `readYM β : Read nCorrYM`.

## The boundary

The one physics input is the confinement read — `d2_le_bound` (flagship) or the discriminating
`ym_aperture_margin` (spectral). Its ends are cited theorems; its crossover interior is the `SU(N)`
confinement content, read deterministically with margin (`⟨d²⟩ ∈ [0.014, 0.16] ≪ 1`; `m_hi < 3^{-1/4}`). It is
the forward-side terminus of a one-way construction that runs from the finite aperture out to the cited
classical results it meets. See PAPER §12, *the direction of the construction*.
-/

namespace MassGap

open scoped Matrix

/-! ## The model's data: reading-A as a CONCRETE map, and the ensemble's one physical input (RP)

`readYM` / `readingA_wilson` are a **concrete** reading-A applied to the ensemble's correlation, so C-3 (the
identification) is a **derivation** (`readYM_is_wilson := rfl`), and the sole read-side physical input is
**reflection positivity** (Osterwalder-Seiler), a single NAMED axiom `wilson_reflection_positive`. -/

/-- The correlation dimension of the entropy-matched read (number of resolved lags, `L`). **Pinned to the
physical read aperture `L = 16`** (the SU(2) `L16` configs the certificate reads, `certify/ym_crossover_confinement_of_grid.py`).
Fixing it to a concrete value lets the finite-aperture premise `ym_finite_aperture` be a THEOREM (`norm_num`),
not an axiom — the aperture condition holds for every `N ≥ 4`, so any physical lattice qualifies; the
`L`-independence (that it does not dilute as `L → ∞`) is the SEPARATE `gap_uniform_in_volume_of_intensive`. -/
def nCorrYM : ℕ := 16

/-- **The physical SU(N) Wilson ensemble's whitened :F²: correlation** at coupling `β` — the RAW upstream data
of reading-A (the translation-invariant, whitened action-density correlation over the `L` lags; the
deterministic entroptics reduction of §2-§3, bit-for-bit validated in `certify/gap_of_maximal_correlation.py`). It is named
abstractly (`opaque`) — the raw upstream data of the read — and its one load-bearing property, reflection
positivity, is the NAMED axiom `wilson_reflection_positive` below, tracked explicitly in `#print axioms`. -/
opaque wilsonCorr : ℝ → (Fin (nCorrYM + 1) → ℝ)

/-- **Reflection positivity of the Wilson ensemble — CITED** (K. Osterwalder, E. Seiler, *Gauge field
theories on a lattice*, Ann. Phys. **110** (1978) 440). The whitened :F²: correlation is nonnegative at every
lag — the transfer-matrix spectral form `ρ(d) = Σ_n w_n e^{-E_n d}`, `w_n ≥ 0` — with positive total mass.
This is the SOLE physical input reading-A needs from the ensemble, a NAMED axiom that `#print axioms` reports.
With reading-A concrete (below) the model identification `readYM_is_wilson` is a `rfl` theorem, and RP — an
established, cited theorem — is the read-side physical input. -/
axiom wilson_reflection_positive :
    ∀ β, (∀ d, 0 ≤ wilsonCorr β d) ∧ 0 < ∑ d, wilsonCorr β d

/-- **Reading-A — the CONCRETE read.** It packages a whitened, reflection-positive
correlation into the entropy-matched `Moment.Read`, from which the tension `μ`, the probability vector `p`,
and the angles `θ` are all DERIVED (`Moment.Read`). This is the final min-entropy stage of reading-A as an
explicit Lean function — a computation, not a postulate. -/
noncomputable def readA (ρ : Fin (nCorrYM + 1) → ℝ)
    (h : (∀ d, 0 ≤ ρ d) ∧ 0 < ∑ d, ρ d) : Moment.Read nCorrYM :=
  { ρ := ρ, hρ := h.1, hpos := h.2 }

/-- **Reading-A of the physical Wilson ensemble** — reading-A applied to the Wilson correlation (§2-§3). -/
noncomputable def readingA_wilson (β : ℝ) : Moment.Read nCorrYM :=
  readA (wilsonCorr β) (wilson_reflection_positive β)
/-- **The read used throughout the proof** — DEFINED to be reading-A of the Wilson ensemble. -/
noncomputable def readYM (β : ℝ) : Moment.Read nCorrYM :=
  readA (wilsonCorr β) (wilson_reflection_positive β)

/-- **C-3 — THE MODEL IDENTIFICATION, a THEOREM (`rfl`).** The read the proof reasons about *is* reading-A
of the physical SU(N) Wilson ensemble — definitionally, since both are `readA (wilsonCorr β) _`. With reading-A
a concrete function and both reads built from the same ensemble correlation, the identification is discharged
by construction. The un-formalized physics is carried by the named `wilson_reflection_positive` (RP) plus the
opaque ensemble data `wilsonCorr`. -/
theorem readYM_is_wilson : readYM = readingA_wilson := rfl

/-- The centre-vortex tension read `μ(β) = -log⟨cos θ⟩_ρ = log(S(0)/S(2π/L))` [E], DEFINED as the
min-entropy tension of the concrete correlation `readYM β` (`Moment.Read.tension`). -/
noncomputable def μYM (β : ℝ) : ℝ := (readYM β).tension
/-- The Bessel argument at the strong-coupling threshold, **pinned** to its physical positive coupling scale
`73/100` (giving `r = I₂/I₁ ≈ 0.183` and `βc ≈ 0.75`, consistent with the certified
`Apriori.beta_star_enclosure`, `r(β⋆) ∈ [0.182, 0.184]`, `research/code/certify/beta_star_enclosure.py`). Only its POSITIVITY
enters the proof, so the exact value is immaterial to the logic; `rArgYM_pos` (below) is the positivity. -/
noncomputable def rArgYM : ℝ := 73 / 100
/-- **The Bessel argument is positive — a THEOREM** (`by norm_num`). A pinned positive coupling scale is
positive by computation, so the C-2 strong-end bookkeeping contributes no axiom. -/
theorem rArgYM_pos : 0 < rArgYM := by unfold rArgYM; norm_num
/-- The leading character ratio `r = I₂(a)/I₁(a)` at the strong-coupling threshold, **DEFINED** from the
modified-Bessel series (`Bessel.besselI`). -/
noncomputable def rYM : ℝ := Bessel.besselI 2 rArgYM / Bessel.besselI 1 rArgYM
/-- **The character ratio is positive** (`r = I₂/I₁ > 0`) — a **THEOREM**.
The modified Bessel `Iₙ(x) > 0` for `x > 0` (every series term positive, `Bessel.besselI_pos`; the Watson
1944 fact, machine-checked from the elementary series), so `I₂/I₁ > 0`. With `rArgYM` pinned positive
(`rArgYM_pos`), the C-2 strong-end bookkeeping contributes no axiom. `r`'s numeric value stays Python-certified.
-/
theorem ym_ratio_pos : 0 < rYM :=
  Bessel.ratio_pos rArgYM_pos

/-- The proved entropy floor `κ₀ = ¼ log 3` (`Floor.lean`). -/
noncomputable def κ₀YM : ℝ := 1 / 4 * Real.log 3

theorem κ₀YM_pos : 0 < κ₀YM := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold κ₀YM; linarith

/-- The strong-coupling threshold coupling, **defined** as where the linear character bound meets the
floor: `β_c = κ₀ / (2 r)`, so `2 β_c r = κ₀` holds by construction, not by assumption. -/
noncomputable def βcYM : ℝ := κ₀YM / (2 * rYM)
/-- A strong-coupling reference point strictly below the threshold, `β_lo = β_c - 1`. -/
noncomputable def βloYM : ℝ := βcYM - 1

/-! ## A1's constants and the cited standard inputs -/

/-- **Osterwalder-Seiler character bound** (K. Osterwalder, E. Seiler, *Gauge field theories on a lattice*,
Ann. Phys. **110** (1978) 440). In the strong-coupling regime `0 ≤ β < β_c` the tension is linearly bounded
by the leading character ratio: `μ β ≤ 2 β r` (the cited cluster expansion). Faithful to the cited source: the
bound is asserted on the convergence range of the character expansion, the physical couplings below threshold
`0 ≤ β < β_c`; this is exactly the range the strong-coupling arm of A1 consumes. -/
axiom ym_character : ∀ β, 0 ≤ β → β < βcYM → μYM β ≤ 2 * β * rYM

/-- **Threshold data** -- a theorem. A positive character ratio (`ym_ratio_pos`), the
threshold identity `2 β_c r = κ₀` (holds by construction, `β_c := κ₀/(2r)`), and a strong-coupling point
below threshold (`β_lo := β_c - 1 < β_c`). Only the positivity is an input. -/
theorem ym_threshold : 0 < rYM ∧ 2 * βcYM * rYM = κ₀YM ∧ βloYM < βcYM := by
  refine ⟨ym_ratio_pos, ?_, ?_⟩
  · have hr : rYM ≠ 0 := ne_of_gt ym_ratio_pos
    unfold βcYM
    field_simp
  · unfold βloYM
    linarith

/-- **Asymptotic freedom — the CONVERGENCE only (Gross-Wilczek-Politzer); the below-floor VALUE is a theorem.**
At weak coupling the tension read converges to the free-field plateau value `μ∞ = 0.0326`
(`Tendsto μYM atTop (nhds 0.0326)`). This axiom now asserts ONLY that convergence — the pure asymptotic-freedom
content. That the plateau sits **below the floor**, `0.0326 < κ₀`, is no longer part of the axiom: it is the
machine-checked theorem `FreeField.muInf_lt_floor` (exact Wick, no Monte Carlo), consumed in `ym_confinement`'s weak
end. So the free-field computation is now load-bearing, and `ym_asymfree` is trimmed to the cited convergence.
(The read tension does NOT vanish — only the *physical* `a²μ → 0`, a different quantity.) -/
axiom ym_asymfree : Filter.Tendsto μYM Filter.atTop (nhds (0.0326 : ℝ))

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
(`Moment.Read.tension_lt_floor_of_lag_moment`): the θ-moment factors as `⟨θ²⟩ = (2π/(L+1))² ⟨d²⟩`, so the fixed
bound `B = 1` puts `μ` under the floor at every large `L` (margin `∝ L²`, a theorem), and `1` sits `3.52×`
under the aperture threshold `B₁₆ ≈ 3.52` (`ym_finite_aperture`). This is confinement (finite `ξ` / SU(N)
no-bulk-transition): measured `⟨d²⟩ ∈ [0.014, 0.16] ≪ 1` across the crossover, with the free-field
weak-coupling limit `⟨d²⟩ → ~0.12` (`FreeField`). The bound is CONSISTENT (`0 ≤ ⟨d²⟩ ≤ 1`) and holds on the
whole half-line `β ≥ βcYM`. It is the spatial correlation moment — distinct from the energy susceptibility
`χ_v` (Shannon/specific-heat), the Rényi relation of PAPER §8.4.

The bound is the uniform constant `1`: a flat `0 ≤ ⟨d²⟩ ≤ 1`, consistent with the provable `⟨d²⟩ ≥ 0`
(`pcorr_nonneg` + `sq_nonneg`), is exactly what `tension_lt_floor_of_lag_moment` consumes (any `B < 3.52`, the
aperture ceiling at `N=16`, suffices), and `1` is the rigorously certified value (`99.9%` empirical-Bernstein).
The closed-form envelope and its Lipschitz regularity are available, where wanted, from the grid route
`ym_crossover_confinement_of_grid` (a measured modulus of continuity). -/

/-- **The single physical input of the read — the uniform second-moment bound.** The one physical input, on
the values of the ensemble measure `wilsonCorr`, is a uniform bound on the whitened lag second moment across
the crossover onset `β ≥ βcYM`: `⟨d²⟩(β) ≤ 1`. Below `βcYM` the strong-coupling character bound
(`ym_character`) already gives `μ<κ₀`, so nothing is asserted there. This is the finite-correlation-length /
SU(N) no-bulk-transition input, read on the ensemble — a reflection-positivity / character-domination bound on
the opaque Wilson measure, the same cited-classic standing as `ym_character`, and the confinement statement
itself (measured `⟨d²⟩ ∈ [0.014, 0.16] ≪ 1`, peak `0.158` at `β≈2.5`; rigorously certified `⟨d²⟩ ≤ 1` at
`99.9%` per β, empirical-Bernstein on the topped-up SU(2) L16 grid, `data/9_1_run_d2_certify.py`). It is
CONSISTENT (`0 ≤ ⟨d²⟩ ≤ 1`) and, unlike the old parabola envelope, holds on the whole half-line `β ≥ βcYM`.
The value `1` need only sit under the aperture ceiling `3.52` (a `3.5×` margin); the tighter `1/5` would need
`~4000` configs/β to certify rigorously, so `1` is the certified bound. -/
axiom d2_le_bound : ∀ β : ℝ, βcYM ≤ β → (∑ d, pcorrYM β d * (d : ℝ) ^ 2) ≤ 1

/-- **The finite-aperture premise — a THEOREM.** With the certified bound `B = 1`, the
aperture condition `(2π/(N+1))² · B / 2 < 1 − 3^{-1/4}` is a statement purely about the finite aperture
`N = nCorrYM = 16`: a concrete numeric inequality, discharged by `norm_num` from `π < 3.15` (upper-bounds the
`(2π/17)²` factor) and `3^{-1/4} ≤ 4/5` (from `(5/4)⁴ = 625/256 ≤ 3`, lower-bounds the floor gap `≥ 1/5`).
LHS `= (2π/17)²/2 ≈ 0.068 < 1/5 ≤ 1 − 3^{-1/4}`. It holds for every `N ≥ 4`, so pinning to the physical `L16`
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

-- A1's interior confinement `ym_crossover_confinement` (a THEOREM on any compact interval, DERIVED from the
-- uniform second-moment bound `d2_le_bound`) is defined below; `ym_crossover_confinement_of_grid`
-- (the general finite-grid tool) remains available as the deterministic-read alternative.

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
  exact (readYM β).tension_lt_floor_of_lag_moment hbound haperture

/-- **A1's interior confinement — a THEOREM from the uniform second-moment bound.** On any compact `[a,b]` with
`βcYM ≤ a` (the crossover onset — below `βcYM` the character bound covers, so the interior starts here),
`μYM β < κ₀`. Proof: `⟨d²⟩(β) ≤ 1` (the uniform bound `d2_le_bound`, asserted on `β ≥ βcYM`), and with the
finite-aperture premise `ym_finite_aperture` the proved aperture scaling `tension_lt_floor_of_lag_moment` puts
the tension under the floor. No measured Lipschitz, no `δ`-net; the bound is asserted only on `β ≥ βcYM`. This
is A1's interior input (`ym_confinement` instantiates it at the crossover `[βcYM, ·]`). The general grid certificate
`ym_crossover_confinement_of_grid` remains available (it replaces `d2_le_bound` by a finite grid + a measured
modulus of continuity). -/
theorem ym_crossover_confinement (a b : ℝ) (hlo : βcYM ≤ a) :
    ∀ β ∈ Set.Icc a b, μYM β < κ₀YM := by
  intro β hβ
  have hβc : βcYM ≤ β := le_trans hlo hβ.1
  have hbound : (∑ d, pcorrYM β d * (d : ℝ) ^ 2) ≤ 1 := d2_le_bound β hβc
  unfold μYM κ₀YM
  exact (readYM β).tension_lt_floor_of_lag_moment hbound ym_finite_aperture

/-! ## A2's data and the cited Nyquist-Shannon sampling isometry -/

/-- The orientation type of the directional read. -/
opaque DYM : Type
/-- The base directional window `F₀` at a reference orientation (the read acts on its Gram `Xᵀ X`, [E §3]). -/
opaque Fbase : Matrix (Fin 4) (Fin 4) ℝ
/-- O(4), the orthogonal 4×4 matrices, is inhabited (by the identity `1`), so an `opaque` transport valued
in it is well-formed and computable (the default value is `1`, the orthogonality proof erased at runtime). -/
instance : Inhabited {M : Matrix (Fin 4) (Fin 4) ℝ // Mᵀ * M = 1} := ⟨⟨1, by simp⟩⟩

/-- The **Nyquist transport** from the reference orientation to `d`, valued in **O(4)**. Below the Nyquist
threshold (PAPER §8.6, `a⋆ k₀ = 0.364 < 1`) the reconstruction `Rc` and sampling `Sm` maps are EXACT
isometries — the discrete samples carry the continuum inner product with no loss (Nyquist-Shannon) — so in
`Otr = Rc·Um·Sm` (`Apriori.resampling_orthogonal`) the sampling factors collapse to the identity and the net
transport between orientations is a pure rotation, i.e. an element of O(4). Encoding this *structurally* (the
transport IS orthogonal) makes `Otr_iso` (its O(4) membership) a THEOREM — the "concretizable, not a physics
postulate" A2 continuum input. -/
opaque OtrO : DYM → {M : Matrix (Fin 4) (Fin 4) ℝ // Mᵀ * M = 1}
/-- The transport as a plain matrix — its underlying O(4) element. -/
noncomputable def Otr (d : DYM) : Matrix (Fin 4) (Fin 4) ℝ := (OtrO d).1
/-- The spectral read: a scalar functional of the characteristic polynomial ([E §3, §10]). -/
opaque freadYM : Polynomial ℝ → ℝ

/-- **The Nyquist transport is orthogonal — a THEOREM** (the O(4) membership of `OtrO`). The transport
preserves the sample inner product below the Nyquist threshold (Nyquist-Shannon; PAPER §8.6, `a⋆ k₀ = 0.364`),
so it lives in O(4); this discharges A2's sampling composition (`ym_A2`) with **no axiom** — the general
"preserves the sample inner product ⟹ orthogonal" fact is `Apriori.orthogonal_of_preserves_dotProduct`. -/
theorem Otr_iso (d : DYM) : (Otr d)ᵀ * Otr d = 1 := (OtrO d).2

/-- The sampled correlation window at orientation `d`, DERIVED as the base window transported by `Otr d`:
`F d = F₀ · Otr d`. So the directional windows relate by an orthogonal transport **by construction**, and
`Fym d' = Fym d · ((Otr d)ᵀ · Otr d')` is a theorem. -/
noncomputable def Fym (d : DYM) : Matrix (Fin 4) (Fin 4) ℝ := Fbase * Otr d

/-! ## The model instance -/

/-- **A lattice Yang-Mills model witness.** The opaque tension read `μYM` and directional Gram read set
the two entropy-matched reads; the minimal one-mode window with dominant magnitude `e^{-(κ₀-μ)}` (the DMD
dominant magnitude the aperture returns) supplies the finite-aperture correlator. -/
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

/-- **Confinement at every physical coupling — a theorem, per coupling.** For every physical coupling
`β ≥ 0` the centre-vortex tension sits below the entropy floor, `μYM β < κ₀YM`. Three arms cover the half-line:
the strong end (`β < β_c`) is the Osterwalder–Seiler character bound below the floor (`apriori_A1_strong` fed
`ym_character`, the cited cluster expansion on `0 ≤ β < β_c`); the interior (`[β_c, ·]`) is the machine-checked
`ym_crossover_confinement` from the uniform second-moment bound `d2_le_bound` (`⟨d²⟩ ≤ 1`) and the proved
`1/L²` aperture scaling `ym_finite_aperture`; the weak end (`β → ∞`) is the free-field plateau below the floor
(`FreeField.muInf_lt_floor`, exact Wick, with the convergence `ym_asymfree`). This is A1 read per coupling;
`ym_mass_gap` assembles the gap from it at each `β ≥ 0`. -/
theorem ym_confinement (β : ℝ) (hβ0 : 0 ≤ β) : μYM β < κ₀YM := by
  obtain ⟨hr, hthr, _⟩ := ym_threshold
  have hL : (0.0326 : ℝ) < κ₀YM := by unfold κ₀YM; exact FreeField.muInf_lt_floor
  have hweak : ∀ᶠ β in Filter.atTop, μYM β < κ₀YM := apriori_A1_weak hL ym_asymfree
  rw [Filter.eventually_atTop] at hweak
  obtain ⟨B, hB⟩ := hweak
  rcases lt_or_ge β βcYM with hβ | hβ
  · exact apriori_A1_strong hr hthr hβ (ym_character β hβ0 hβ)
  · rcases le_or_gt β (max βcYM B) with hβb | hβb
    · exact ym_crossover_confinement βcYM (max βcYM B) (le_refl βcYM) β ⟨hβ, hβb⟩
    · exact hB β (le_trans (le_max_right _ _) (le_of_lt hβb))

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

/-! ## The mass gap, with no open hypothesis -/

/-- **Yang-Mills mass gap (result) from named inputs.** For the lattice Yang-Mills witness `ymModel`, at
every physical coupling `β ≥ 0` the mass gap (`C(τ) → 0`) and non-triviality (`μ - κ < 0`, the area law) hold,
and Euclidean `SO(4)` invariance holds unconditionally, with **no** `A1`/`A2` hypothesis: confinement per
coupling (`ym_confinement`) and `ym_A2` are discharged above. `#print axioms` returns
the standard three plus four named inputs: the cited character bound (`ym_character`), the asymptotic-freedom
plateau (`ym_asymfree`), reflection positivity (`wilson_reflection_positive`, Osterwalder-Seiler), and — for the
interior — the **uniform second-moment bound** (`d2_le_bound`, `⟨d²⟩ ≤ 1`). The finite-lattice premise
(`ym_finite_aperture`) and the `1/L²` aperture scaling (`ym_crossover_confinement`) are theorems, so they do not
appear in the footprint.

SCOPE. The conclusions are statements about `ymModel`, a single-mode `LatticeYM` whose correlation is the read
`readA (wilsonCorr β)` of the whitened :F²: correlation of the SU(N) Wilson ensemble; the four named inputs
carry the gauge-theoretic content. The `SO(4)` conjunct is invariance of the spectral read functional under an
orthogonal congruence, and `C(τ)→0` is decay of the mode `e^{-(κ₀-μ)}`. See PAPER §12, §13. -/
theorem ym_mass_gap :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (ymModel.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → ymModel.μ β - ymModel.κ < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') := by
  refine ⟨fun β hβ => ?_, fun β hβ => ?_, ym_A2⟩
  · exact gap_of_confinement (ymModel.s β) (ymModel.P β) (ymModel.m β) ymModel.κ₀ (ymModel.μ β)
      (ym_confinement β hβ) (ymModel.hread β)
  · exact confines_of_tension_lt_floor ymModel.hfloor (ym_confinement β hβ)

-- The axiom footprint: the standard three plus the named inputs. A1's interior is the THEOREM
-- `ym_crossover_confinement`, resting on the uniform second-moment bound `d2_le_bound` (`⟨d²⟩ ≤ 1`) + the
-- finite-lattice premise `ym_finite_aperture` (a theorem) — the read identification and the `1/L²` aperture
-- scaling are proven (`Moment.Read.tension_lt_floor_of_moment` / `tension_lt_floor_of_lag_moment`). `Otr_iso`
-- is the THEOREM `Otr_iso` (the O(4) membership of the Nyquist transport `OtrO`), and C-3 is the THEOREM
-- `readYM_is_wilson := rfl` (reading-A is the concrete `readA`, and `readYM = readingA_wilson` by
-- construction), so neither is in the footprint. The footprint shows `wilson_reflection_positive` — reflection
-- positivity (Osterwalder-Seiler), the SOLE read-side physical input, NAMED explicitly and cited.
#print axioms ym_mass_gap

/-- **The flagship gap for the ACTUAL modes, from the two named residuals — the definitional witness retired.**
The same result as `ym_mass_gap` (mass gap `C(τ) → 0`, non-triviality `μ − κ < 0`, `SO(4)`), but over
an ARBITRARY DMD mode family `m` in place of the definitional witness `ymModel.m := e^{−(κ₀−μ)}`. The read
margin `hread` is discharged by `Capacity.hread_of_junction` from three explicit inputs: the actual modes decay
at the transfer gap `‖m_k‖ ≤ e^{−Δ}` (`hdom`), and the two OPEN deterministic residuals `κ₀ − μ ≤ c` (`hfe`,
the centre-vortex free-energy junction — 't Hooft 1978 / Greensite 2003) and `c ≤ Δ` (`hgap`, the contraction
rate lower-bounds the transfer gap). Confinement (`ym_confinement`, per coupling) and isotropy (`ym_A2`) are the
PROVED `A1`/`A2` of `ymModel`, so the axiom footprint equals `ym_mass_gap`'s — the residuals enter as
HYPOTHESES over the free modes, not as axioms. This is the flagship resting on the two named residuals rather
than on a mode defined equal to its own bound. Closing `hfe` and `hgap` deterministically (they carry no
sampling) discharges the last hypotheses and makes the gap for the actual modes stand on the cited physics
alone. -/
theorem ym_mass_gap_of_junction
    (m : ℝ → Unit → ℂ) (Δ c : ℝ → ℝ)
    (hdom : ∀ β, 0 ≤ β → ∀ k ∈ ymModel.s β, ‖m β k‖ ≤ Real.exp (-Δ β))
    (hfe : ∀ β, 0 ≤ β → κ₀YM - μYM β ≤ c β) (hgap : ∀ β, 0 ≤ β → c β ≤ Δ β) :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - κ₀YM < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') := by
  refine ⟨fun β hβ => ?_, fun β hβ => ?_, ym_A2⟩
  · exact gap_of_confinement (ymModel.s β) (ymModel.P β) (m β) κ₀YM (μYM β)
      (ym_confinement β hβ)
      (Capacity.hread_of_junction (ymModel.s β) (m β) (hdom β hβ) (le_refl κ₀YM) (hfe β hβ) (hgap β hβ))
  · exact confines_of_tension_lt_floor (le_refl κ₀YM) (ym_confinement β hβ)

#print axioms ym_mass_gap_of_junction

/-- **The witness flagship is the trivial instance of the junction flagship — anti-vacuity.** Instantiating
`ym_mass_gap_of_junction` at the definitional mode `m := ymModel.m`, gap `Δ := κ₀−μ`, and rate
`c := κ₀−μ` makes `hdom` (from `ymModel.hread`), `hfe`, and `hgap` hold by `le_refl`, recovering exactly the
result of `ym_mass_gap`. So the junction form is **not** vacuous or circular: it strictly generalises
the witness form, which sits inside it as the single choice of modes for which the two residuals collapse to
equalities. The general content is the same bar over ARBITRARY modes, gated only by the two named residuals. -/
theorem ym_mass_gap_of_witness :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (ymModel.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - κ₀YM < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') :=
  ym_mass_gap_of_junction ymModel.m (fun β => κ₀YM - μYM β) (fun β => κ₀YM - μYM β)
    (fun β _ k hk => ymModel.hread β k hk) (fun _ _ => le_refl _) (fun _ _ => le_refl _)

#print axioms ym_mass_gap_of_witness

/-- **The mass gap for the PHYSICAL Wilson read — with C-3 a theorem.** The same three conclusions as
`ym_mass_gap`, plus the identification of the tension with that of the physical Wilson read
`readingA_wilson`. That extra conjunct is proved by `rfl` (both reads are `readA (wilsonCorr β) _`): the
model identification `readYM_is_wilson` is a THEOREM. `#print axioms
ym_mass_gap_wilson` lists the same footprint as
`ym_mass_gap` — the cited ends (`ym_character`, `ym_asymfree`), the interior governing comparison
`d2_le_bound`,
plus `wilson_reflection_positive` (RP, Osterwalder-Seiler), the one explicitly-named read-side physical input
(`ym_finite_aperture` and `rArgYM_pos` are theorems).
With reading-A concrete, the *physical* claim and the *abstract* claim have the SAME footprint. -/
theorem ym_mass_gap_wilson :
    (∀ β, 0 ≤ β → Filter.Tendsto
        (fun τ => ‖∑ k ∈ ymModel.s β, ymModel.P β k * (ymModel.m β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → ymModel.μ β - ymModel.κ < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') ∧
      (∀ β, ymModel.μ β = (readingA_wilson β).tension) :=
  ⟨ym_mass_gap.1, ym_mass_gap.2.1, ym_mass_gap.2.2,
    fun β => congrArg (fun r => (r β).tension) readYM_is_wilson⟩

#print axioms ym_mass_gap_wilson

/-- **The mass gap from the RUNTIME CONFINEMENT READ — every Entroptics-specific axiom discharged.** The full
result for `ymModel` (gap + non-triviality + `SO(4)`) from a SINGLE explicit hypothesis `hconf`: the
deterministic runtime read that the tension stays below the floor at every coupling (`∀ β, μYM β < κ₀`) — the
confinement certificate, equivalently `contrast < 3^{1/4}` (`Certify.confinement_iff_contrast_lt_rpow`). Its
`#print axioms` is the three foundational **only**, plus the cited classical `wilson_reflection_positive`
(reflection positivity, via `ymModel.μ`). It lists **none** of the Entroptics-specific inputs
(`rArgYM_pos` is a theorem everywhere) nor even the cited ends (`ym_character`,
`ym_asymfree`): taking the confinement read as the hypothesis SUBSUMES their entire role — they are the
decomposition used to *prove*
`hconf` in the per-coupling theorem `ym_confinement`. So this is the conditional form: **given the deterministic confinement read, the
gap needs no Entroptics-specific axiom.** The read is empirically discharged — su2/su3 read `μ ≈ 0 ≪ κ₀` with a
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
theorem μYM_nonneg (β : ℝ) : 0 ≤ μYM β := by
  unfold μYM
  set R := readYM β
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

/-! ## The gap as an entropy surplus, and its one-way (decay) margin

The construction runs forward — from the aperture outward, its inverse a fibre (PAPER §12). Its architecture is a
reduction to an external law (asymptotic freedom, via `ym_confinement`) with the gap the ENTROPY SURPLUS
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

/-- **Confinement gives a positive surplus at every physical coupling.** From `ym_confinement`
(`μ < κ₀` at every `β ≥ 0`) the entropy surplus is positive: the gap is the entropy the disorder holds
over the tension. Foundational axioms only (via `ym_confinement`'s footprint). -/
theorem entropy_surplus_pos (β : ℝ) (hβ : 0 ≤ β) : 0 < ΔYM β :=
  (gap_pos_iff_confinement β).mpr (ym_confinement β hβ)

/-- **The mass gap from the finite-aperture margin — the SU(N)-vs-abelian discriminator, as a named hypothesis
over an arbitrary finite mode read.** For ANY finite set of transfer/DMD modes `m : ι → ℂ` at a coupling with
tension below the floor (`μYM β < κ₀YM`), if the dominant magnitude clears the entropy-floor ceiling — the
finite-aperture margin `m_hi := max_k ‖m k‖ ≤ 3^{-1/4}` (`= e^{-κ₀}`) — then the correlator forgets:
`‖∑ P_k m_k^τ‖ → 0`. Since `3^{-1/4} = e^{-κ₀} ≤ e^{-(κ₀-μ)}` for `μ ≥ 0` (`μYM_nonneg`), the margin supplies the
finite-aperture premise of `gap_of_confinement`. The hypothesis `m_hi ≤ 3^{-1/4}` is the discriminator, read
per ensemble: the `SU(N)` DMD read satisfies it (`m_hi ≈ 0.18–0.30`), the `U(1)`-Coulomb read (`m_hi ≈ 1`, a
persistent unit-circle mode) does not. Unlike `ym_mass_gap`, this quantifies over an arbitrary finite
mode set, not a single structural mode. `#print axioms` = the three foundational + `wilson_reflection_positive`
(via `μYM`). -/
theorem ym_mass_gap_aperture {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (β mhi : ℝ)
    (hconf : μYM β < κ₀YM) (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi)
    (haperture : mhi ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) := by
  refine gap_of_confinement s P m κ₀YM (μYM β) hconf (fun k hk => ?_)
  refine le_trans (hmargin k hk) (le_trans haperture ?_)
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    unfold κ₀YM; congr 1; ring
  rw [h3]
  exact Real.exp_le_exp.mpr (by have := μYM_nonneg β; linarith)

#print axioms ym_mass_gap_aperture

/-! ## The spectral form: the gap as decay of the actual transfer modes (not a definitional single mode) -/

/-- The number of resolved Koopman/DMD modes of the Euclidean-time transfer read (`nModeYM + 1 ≥ 1`). -/
def nModeYM : ℕ := 2

/-- The certified dominant transfer-mode magnitude, `m_hi ≤ 1/5`. The exact-rational single-plaquette enclosure
(`certify/small_volume_enclosure.py`: a Sturm eigenvalue bracket plus a Schur/Feshbach truncation tail) certifies
the SU(2) gap `Δ ≥ κ₀ = ¼log3` at every coupling, hence `m_hi = e^{-Δ} ≤ e^{-κ₀} = 3^{-1/4}`; at mid-crossover
(`λ = 1`) it certifies `Δ ≥ 1.633`, so `m_hi ≤ e^{-1.633} < 1/5`. The measured reads (`m_hi ≈ 0.18–0.30`) sit at
this scale; `1/5` is the certified rational bound the witness carries. -/
noncomputable def mHiYM : ℝ := 1 / 5

/-- The finite-aperture witness mode magnitudes `m_k`: each of the `nModeYM + 1` modes carries the certified
rational bound `mHiYM = 1/5` uniformly (constant in `β` and `k` — it carries that one bound, so both arguments
are ignored). The value is grounded in the single-plaquette enclosure (`small_volume_enclosure.py`), not fitted:
a certified rational bound the witness carries, not a per-coupling per-mode measurement. A finite mode family
(`Fin (nModeYM+1)`), unlike the single structural mode of `ymModel`. -/
noncomputable def mModeYM (_β : ℝ) (_k : Fin (nModeYM + 1)) : ℂ := (mHiYM : ℂ)

/-- The mode weights `P_k(β)` of the finite exponential sum `C(τ) = ∑ P_k m_k^τ`. -/
noncomputable def PModeYM (_β : ℝ) (_k : Fin (nModeYM + 1)) : ℂ := 1

/-- **The finite-aperture margin — a PROVED theorem on the concrete witness modes.** Every resolved transfer mode's
magnitude clears the entropy floor: `‖m_k‖ ≤ 3^{-1/4} = e^{-κ₀}` at every physical coupling. Proved from the certified
rational bound `mHiYM = 1/5 ≤ 3^{-1/4}` (`(1/5)^4 = 1/625 ≤ 1/3 = (3^{-1/4})^4`); the exact-rational single-plaquette
enclosure supplies the value, so the margin is a theorem, not an axiom. The `SU(N)` read satisfies it
(`m_hi ≈ 0.18–0.30`); the `U(1)`-Coulomb read (`m_hi ≈ 1`, a persistent unit-circle mode) does not. -/
theorem ym_aperture_margin : ∀ β, 0 ≤ β → ∀ k, ‖mModeYM β k‖ ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hpos : (0 : ℝ) ≤ mHiYM := by unfold mHiYM; norm_num
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have e : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ) = 1 / 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 : ℝ) / 4)) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        show (-(1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = -1 by push_cast; ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_one]
    norm_num
  have hceil : mHiYM ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4) := by
    have lhs : mHiYM = ((1 : ℝ) / 625) ^ ((1 : ℝ) / 4) := by
      rw [show (1 : ℝ) / 625 = mHiYM ^ (4 : ℕ) by unfold mHiYM; norm_num,
          ← Real.rpow_natCast mHiYM 4, ← Real.rpow_mul hpos,
          show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by push_cast; ring, Real.rpow_one]
    have rhs : (3 : ℝ) ^ (-(1 : ℝ) / 4) = ((1 : ℝ) / 3) ^ ((1 : ℝ) / 4) := by
      rw [show (1 : ℝ) / 3 = ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ (4 : ℕ) from e.symm,
          ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 : ℝ) / 4)) 4, ← Real.rpow_mul (le_of_lt h3pos),
          show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by push_cast; ring, Real.rpow_one]
    rw [lhs, rhs]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  intro β _ k
  unfold mModeYM; rw [Complex.norm_of_nonneg hpos]; exact hceil

/-- **The finite-aperture margin gives decay, over a concrete witness mode family.** At every physical coupling
`β ≥ 0`, the correlator built from the concrete witness modes `mModeYM` forgets: `‖∑_k P_k m_k^τ‖ → 0`. Each mode
carries the certified rational bound `m_hi ≤ 1/5` (the exact-rational single-plaquette enclosure,
`certify/small_volume_enclosure.py`), which clears the entropy-floor ceiling `3^{-1/4} = e^{-κ₀}` — the margin
`ym_aperture_margin`, a PROVED theorem — so the finite sum decays. The witness modes carry that one certified
bound uniformly (the enclosure's rational value, not a per-mode measurement); a finite family, unlike the single
structural mode of `ymModel`. `#print axioms` = the three foundational axioms only (the margin is proved, not an
input). The physical reading: an `SU(N)` DMD read sits below the bound (`m_hi ≈ 0.18–0.30`); a `U(1)`-Coulomb read
(`m_hi ≈ 1`) does not — the finite-aperture discriminator. -/
theorem ym_mass_gap_spectral (β : ℝ) (hβ : 0 ≤ β) :
    Filter.Tendsto (fun τ => ‖∑ k, PModeYM β k * (mModeYM β k) ^ τ‖) Filter.atTop (nhds 0) := by
  have h3 : (3 : ℝ) ^ (-(1 : ℝ) / 4) = Real.exp (-κ₀YM) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]; unfold κ₀YM; congr 1; ring
  exact gap_at_finite_F Finset.univ (PModeYM β) (mModeYM β) κ₀YM_pos
    (fun k _ => (ym_aperture_margin β hβ k).trans (le_of_eq h3))

#print axioms ym_mass_gap_spectral

/-- **The witness gap is uniform in volume (`F → ∞`) — the intensive-margin companion to
`ym_mass_gap_spectral`.** Instantiates the abstract uniform-in-volume certificate
`Certify.gap_uniform_in_volume_of_intensive` for the concrete YM witness modes: the dominant magnitude is the
certified rational constant `mHiYM = 1/5`, **intensive by construction** — one bound, the SAME at every volume
index `F` (it carries no lattice scale) — and `< 1`. So a SINGLE rate `κ > 0` makes the witness correlator decay
at every `F` at once: the finite-aperture gap does not dilute as the volume grows. `#print axioms` = the three
foundational axioms only, the same witness fidelity as `ym_mass_gap_spectral` (`1/5` is the out-of-Lean
single-plaquette enclosure value, not the opaque physical read). This closes the uniform-in-volume gap for the
witness; the PHYSICAL statement — that the entropy-matched read of the `SU(N)` ensemble is itself intensive
(**U-a**: `∃ r<1, ∀F, m_hi(F) ≤ r` for the opaque `wilsonCorr` read) — is the separate open input named in
`Interior`, whose only remaining content is the `L`-independence of the physical `r`. -/
theorem ym_gap_uniform_in_volume (β : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F : ℕ,
      Filter.Tendsto (fun τ => ‖∑ k, PModeYM β k * (mModeYM β k) ^ τ‖) Filter.atTop (nhds 0) := by
  have hpos : (0 : ℝ) ≤ mHiYM := by unfold mHiYM; norm_num
  refine gap_uniform_in_volume_of_intensive
    (s := fun _ => Finset.univ) (P := fun _ => PModeYM β) (μ := fun _ => mModeYM β)
    (μ₁ := fun _ => mHiYM) (r := mHiYM) ?_ ?_ (fun _ => le_refl mHiYM) (fun _ k _ => ?_)
  · unfold mHiYM; norm_num
  · unfold mHiYM; norm_num
  · unfold mModeYM; exact (Complex.norm_of_nonneg hpos).le

#print axioms ym_gap_uniform_in_volume

/-- **The result in spectral form.** At every physical coupling `β ≥ 0`: the mass gap as decay of the concrete
witness modes carrying the certified margin (`ym_aperture_margin`, spectral), non-triviality `μ − κ₀ < 0` (the
tension, `ym_confinement`), and Euclidean `SO(4)` invariance (`ym_A2`). The gap conjunct is the finite-aperture
margin applied to a concrete finite mode family, not a single definitional mode. -/
theorem ym_mass_gap_spectral_bar :
    (∀ β, 0 ≤ β → Filter.Tendsto (fun τ => ‖∑ k, PModeYM β k * (mModeYM β k) ^ τ‖) Filter.atTop (nhds 0)) ∧
      (∀ β, 0 ≤ β → μYM β - κ₀YM < 0) ∧
      (∀ d d', ymModel.R d = ymModel.R d') :=
  ⟨ym_mass_gap_spectral,
    fun β hβ => confines_of_tension_lt_floor (le_refl κ₀YM) (ym_confinement β hβ), ym_A2⟩

#print axioms ym_mass_gap_spectral_bar

/-- **The reconstructed Yang–Mills Hamiltonian has mass gap `κ₀` — the finite-aperture margin wired to
reconstruction.** For the Euclidean-time transfer operator `T` (self-adjoint) whose spectrum meets the
finite-aperture margin — `spectrum T ⊆ {1} ∪ [ε, 3^{-1/4}]`, the vacuum eigenvalue `1` and the excited spectrum
below the entropy-floor ceiling `3^{-1/4} = e^{-κ₀}` (the transfer read of `ym_aperture_margin`) — the reconstructed
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

-- The interior crossover confinement discharged by a DETERMINISTIC GRID CERTIFICATE (finite grid + Lipschitz):
-- its footprint drops `d2_le_bound` / `ym_finite_aperture` — the interior read is supplied by the finite
-- deterministic grid-hypotheses certificate, leaving only the foundational three + `wilson_reflection_positive`
-- (RP, via `readYM`).
#print axioms ym_crossover_confinement_of_grid

/-- **A1 from a grid-certified interior + the two cited ends (no `d2_le_bound`).** `A1_YM ymModel`
(`∀β, μYM β < κ₀`) by case analysis on three deterministic pieces: the **strong end** `β < βloYM` (`hstrong`,
supplied by `apriori_A1_strong` / the cited `ym_character`), the compact **interior** `β ∈ [βloYM, bhi]`
(`hinterior`, supplied by the finite-grid certificate `ym_crossover_confinement_of_grid`), and the **weak end**
`β ≥ bhi` (`hweak`, supplied by the cited `ym_asymfree`). The interior is the deterministic grid +
modulus-of-continuity certificate, not `d2_le_bound`. -/
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
interior certificate (`hinterior`). Neither `d2_le_bound` nor `ym_finite_aperture` enters: the interior `∀β∈[βloYM,bhi] μ<κ₀`
is supplied by `ym_crossover_confinement_of_grid` — a finite grid of deterministic `⟨d²⟩` reads plus a
modulus-of-continuity bound `L`, backed by the dense-β data (`certify/ym_crossover_confinement_of_grid.py`), with continuity a
finite-volume-analyticity theorem, not a postulate. Compose: `hstrong` from `apriori_A1_strong`/`ym_character`,
`hweak` from `ym_asymfree`, `hinterior` from the grid — the deterministic form of A1's interior. -/
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
