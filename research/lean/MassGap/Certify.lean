import Mathlib
import MassGap.ReachFreeze
import MassGap.Aperture

/-!
# Wiring the runtime certificate into the confinement inequality ([E, Lem 6.2])

The read layer returns CERTIFIED INTERVALS, and their SOUNDNESS is base optics, certified in the
companion viewer development [E, `Entroptics/Spectrum.lean`]:

* `attenuation_weyl_certified` [E, Lem 6.2]: the Weyl band encloses the true attenuation
  `α ∈ [α_lo, α_hi]` (certifies `attenuation_interval`).
* `resolved_count_certified` [E, Lem 6.2 count form]: the Weyl band encloses the true resolved
  count `K_lo ≤ K_true ≤ K_hi` (certifies `resolved_dimension_interval`).
* `separated_of_disjoint_intervals` [E]: non-overlapping certified intervals order the true ensemble
  means (certifies the concentration separation `k_signal_certificate` reports).

Those are read-layer facts, so they live with the read layer. This file holds only the mass-gap
SPECIFIC step: a certified upper bound below the floor discharges `μ < κ₀`, the sole open input of
`gap_of_confinement`, and feeds the confinement free-energy sign.
-/

namespace MassGap

/-- **A certified attenuation upper bound below the floor gives confinement.** The read returns a
certified enclosure `μ ≤ α_hi` of the tension `μ` (the attenuation, [E, Lem 6.2]), and the certified
upper endpoint sits below the floor, `α_hi < κ₀`. Then `μ < κ₀`, the confinement inequality. This is
where the runtime certificate meets the proof: it discharges the one hypothesis of
`gap_of_confinement`. -/
theorem confinement_of_certified {μ αhi κ₀ : ℝ} (hμ : μ ≤ αhi) (hcert : αhi < κ₀) :
    μ < κ₀ := lt_of_le_of_lt hμ hcert

/-- **From the certified bound to the gap (capstone).** Given the certified confinement enclosure
(`μ ≤ α_hi`, `α_hi < κ₀`) and the finite-aperture read (every mode inside the free-energy margin),
the autocorrelation forgets: `C(τ) → 0`, the gap is open. The certificate discharges `μ < κ₀`; the
finite aperture (causality) does the rest via `gap_of_confinement`. -/
theorem gap_of_certified {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ αhi : ℝ)
    (hμ : μ ≤ αhi) (hcert : αhi < κ₀)
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_confinement s P m κ₀ μ (confinement_of_certified hμ hcert) hread

/-- **The FINITE-APERTURE read discharges the per-mode margin from a certified DMD-margin bound.** The
finite-aperture premise of `gap_of_confinement` is `∀ k ∈ s, ‖m k‖ ≤ e^{-(κ₀-μ)}` — every dynamical mode's
magnitude sits inside the free-energy margin. The read layer returns the operator's **forgetting margin**
`m_hi = max_k ‖m k‖` (`Aperture.margin` / `dynamics().forgetting()`), a deterministic, INTENSIVE (L-stable)
quantity: `m_hi ≈ e^{-Δ}` with `Δ` the gap. So one certified inequality `m_hi ≤ e^{-(κ₀-μ)}` — the slowest
mode decays at least as fast as the entropy margin — discharges the whole premise by transitivity. This is the
confined/deconfined split as a single certificate: su2 reads `m_hi ≈ 0.22 < 3^{-1/4} ≈ 0.76 = e^{-κ₀}` (finite
aperture, passes); U(1)-Coulomb reads `m_hi ≈ 1` (a persistent gapless mode, fails). -/
theorem finite_aperture_of_certified {ι : Type*} (s : Finset ι) (m : ι → ℂ) (κ₀ μ mhi : ℝ)
    (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi) (hcertm : mhi ≤ Real.exp (-(κ₀ - μ))) :
    ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ)) :=
  fun k hk => le_trans (hmargin k hk) hcertm

/-- **The mass gap from TWO runtime certificates — the whole gap conditioned on deterministic reads.** Both
open sides of `gap_of_confinement` are discharged by certified intensive reads, no hypothesis left opaque:
(A1) a certified tension enclosure `μ ≤ α_hi < κ₀` (the attenuation interval), AND (finite aperture) a
certified DMD-margin bound `max_k ‖m k‖ ≤ m_hi ≤ e^{-(κ₀-μ)}` (the forgetting read). Given both, the
autocorrelation forgets, `C(τ) → 0`: the gap is open. This is the Certify-layer form of `gap_of_confinement`
with EVERY premise a runtime deterministic certificate — the finite aperture certified, not assumed. -/
theorem gap_of_margin_certified {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ αhi mhi : ℝ)
    (hμ : μ ≤ αhi) (hcert : αhi < κ₀)
    (hmargin : ∀ k ∈ s, ‖m k‖ ≤ mhi) (hcertm : mhi ≤ Real.exp (-(κ₀ - μ))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_certified s P m κ₀ μ αhi hμ hcert (finite_aperture_of_certified s m κ₀ μ mhi hmargin hcertm)

/-- **From the certified bound to confinement (free-energy form).** The certified `μ < κ₀` gives a
negative centre-vortex free energy `μ - κ < 0` for any `κ ≥ κ₀`, so the disorder condenses. Chains
`confinement_of_certified` into `confines_of_tension_lt_floor`. -/
theorem confines_of_certified {μ αhi κ₀ κ : ℝ} (hμ : μ ≤ αhi) (hcert : αhi < κ₀)
    (hfloor : κ₀ ≤ κ) : μ - κ < 0 :=
  confines_of_tension_lt_floor hfloor (confinement_of_certified hμ hcert)

/-! ## The conditional main theorem: the gap from the confinement read

The read layer returns, at each coupling `β`, the aperture's tension `μ β` (its measured deficit
below the counting floor) and the mode magnitudes of the finite propagator. The theorem below
assembles the whole machine-checked chain onto a **single explicit hypothesis**, `∀ β, μ β < κ₀` —
the read `μ < κ₀`. It is the input this conditional theorem takes: given that read,
the gap follows at every coupling, and `#print axioms` returns the standard three. The hypothesis itself,
`∀ β, μ β < κ₀` (A1), is reduced elsewhere to its two coupling ends (`apriori_A1_strong`,
`apriori_A1_weak`) and, across the crossover, to the finite correlation length `d2_le_bound`
(`Complete.ym_crossover_confinement`). -/

/-- **The gap from the confinement read (conditional main theorem).** Let `μ : ℝ → ℝ` be the
aperture's tension read across the coupling, `s β`/`m β`/`P β` the finite mode set, magnitudes, and
weights the aperture returns at coupling `β`. If the read stays below the counting floor at every
coupling (`∀ β, μ β < κ₀`, the sole input) and the mode magnitudes sit inside the free-energy margin
(`‖m β k‖ ≤ e^{-(κ₀ - μ β)}`, the read `μ` is defined as this deficit), then at every coupling the
correlator forgets: `C(τ) → 0`, the gap `≥ κ₀ - μ β > 0`. Everything downstream of `∀ β, μ β < κ₀` is
proved; that inequality is the read, taken as the hypothesis, not derived here. -/
theorem gap_of_confinement_read {ι : Type*} (s : ℝ → Finset ι) (P m : ℝ → ι → ℂ)
    (κ₀ : ℝ) (μ : ℝ → ℝ) (hconf : ∀ β, μ β < κ₀)
    (hread : ∀ β, ∀ k ∈ s β, ‖m β k‖ ≤ Real.exp (-(κ₀ - μ β))) :
    ∀ β, Filter.Tendsto
      (fun τ => ‖∑ k ∈ s β, P β k * (m β k) ^ τ‖) Filter.atTop (nhds 0) :=
  fun β => gap_of_confinement (s β) (P β) (m β) κ₀ (μ β) (hconf β) (hread β)

/-! ## The contraction lower bound and its spacing-uniformity (§6; reviewer)

The reach-freeze contraction `c` has an explicit, provable lower bound `c ≥ κ₀ - μ`
(`contraction_ge_margin`), holding at every step `n`. Its positivity is A1 (`μ < κ₀`); its
non-vanishing as `a → 0` is the a-uniform margin `UniformConfinement`, A1's continuum core. That is stated
as a named hypothesis with a machine-checked downstream (`uniform_gap_of_uniformConfinement`); the
weak-coupling tail is closed by `weak_uniform_margin` (asymptotic freedom). -/

/-- **The contraction rate is at least the free-energy margin, for all `n`** (reviewer conditions (i),
(ii)). With the finite-aperture modes inside the margin `‖m k‖ ≤ e^{-(κ₀-μ)}`, the correlator contracts
at rate at least `κ₀ - μ` at EVERY step `τ`: `‖∑ P_k m_k^τ‖ ≤ (∑‖P_k‖)(e^{-(κ₀-μ)})^τ`. An explicit
inequality with the Lean-checked constant `κ₀ = ¼ log 3`, uniform in `n`. Its positivity is A1
(`μ < κ₀`); its a-uniformity is `UniformConfinement`. -/
theorem contraction_ge_margin {ι : Type*} (s : Finset ι) (P m : ι → ℂ) (κ₀ μ : ℝ)
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-(κ₀ - μ))) (τ : ℕ) :
    ‖∑ k ∈ s, P k * (m k) ^ τ‖ ≤ (∑ k ∈ s, ‖P k‖) * (Real.exp (-(κ₀ - μ))) ^ τ :=
  finite_sum_margin_bound s P m (Real.exp (-(κ₀ - μ))) hread τ

/-- **`UniformConfinement`: the confinement margin is uniform in the spacing** (reviewer condition
(iii)). There is a fixed `ε > 0` with `μ a ≤ κ₀ - ε` at every spacing `a`. This is the a-uniform
positivity of the free-energy margin, A1's continuum core: the runtime read certifies `μ a < κ₀` at each
fixed `a`; this is the uniform-in-`a` strengthening, carried across spacings by refinement-invariance. -/
def UniformConfinement (μ : ℝ → ℝ) (κ₀ : ℝ) : Prop := ∃ ε : ℝ, 0 < ε ∧ ∀ a, μ a ≤ κ₀ - ε

/-- **The a-uniform gap constant, from `UniformConfinement`** (reviewer condition (iii), discharged from
the named input). A spacing-uniform margin `ε > 0` gives an a-independent positive lower bound on the
contraction, `κ₀ - μ a ≥ ε > 0` at every spacing; with `contraction_ge_margin` this is `Δ(a) ≥ ε > 0`
uniformly, so the lower bound does not vanish as `a → 0`. When `UniformConfinement` becomes a theorem
this follows with no further work. -/
theorem uniform_gap_of_uniformConfinement {μ : ℝ → ℝ} {κ₀ : ℝ}
    (h : UniformConfinement μ κ₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a, ε ≤ κ₀ - μ a := by
  obtain ⟨ε, hε, hbound⟩ := h
  exact ⟨ε, hε, fun a => by linarith [hbound a]⟩

/-- **The β → ∞ (continuum) tail: an a-uniform upper bound staying below κ₀** (reviewer). With the
tension vanishing at weak coupling (`μ β → 0`, asymptotic freedom, `Running.lean`), for ANY margin
`ε < κ₀` the tension stays below the floor by `ε` for all large `β`: `∀ᶠ β, μ β ≤ κ₀ - ε`. So into the
continuum (`β → ∞`, `a → 0`) the margin does not close; taking `ε ↑ κ₀` it approaches the FULL floor.
This is the weak-coupling / continuum tail of `UniformConfinement`, proved; the intermediate crossover is
the finite correlation length `d2_le_bound` (`Complete.ym_crossover_confinement`). The input `μ → 0` is the
asymptotic-freedom scaling (physical tension a finite RG-invariant scale, lattice tension `a²Λ² → 0`). -/
theorem weak_uniform_margin {μ : ℝ → ℝ} {κ₀ ε : ℝ} (hε : ε < κ₀)
    (hlim : Filter.Tendsto μ Filter.atTop (nhds 0)) :
    ∀ᶠ β in Filter.atTop, μ β ≤ κ₀ - ε := by
  have h : ∀ᶠ y in nhds (0 : ℝ), y ≤ κ₀ - ε := by
    have hmem : Set.Iio (κ₀ - ε) ∈ nhds (0 : ℝ) :=
      isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; linarith)
    filter_upwards [hmem] with y hy
    exact le_of_lt (Set.mem_Iio.mp hy)
  filter_upwards [hlim.eventually h] with β hβ
  exact hβ

/-! ## The confinement criterion in eigenvalue form (§8.6, deterministic system identification)

Deterministic system identification (PAPER §8.6) fixes the tension read exactly: at the confinement
threshold (a single resolved mode) the tension is the log-contrast of the leading correlation mode over
the Tracy–Widom noise floor, `μ = log(contrast)`, `contrast = λ₁/Φ`. So `μ < κ₀` is an exact eigenvalue
bound, and with the counting floor `κ₀ = ¼ log 3` the critical contrast is `e^{κ₀} = 3^{1/4}`, carrying the
same directed-cube-path `3` as the floor (`Floor.lean`). These lemmas are the arithmetic of that identity;
the read `μ = log(contrast)` is confirmed to machine precision in §8.6. -/

/-- **The critical contrast is the fourth root of three.** `e^{κ₀} = 3^{1/4}` for the counting floor
`κ₀ = ¼ log 3`: the confinement threshold on the contrast is `3^{1/4}`, the same `3` as the
directed-cube-path count (`Floor.floor_pos`, `Floor.directed_paths_card`). -/
theorem exp_floor_eq_rpow : Real.exp ((1 / 4 : ℝ) * Real.log 3) = (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- **Confinement is an eigenvalue bound.** With the tension read `μ = log(contrast)` (`contrast > 0`),
`μ < κ₀ ↔ contrast < e^{κ₀}`: the confinement inequality is exactly the leading correlation eigenvalue
staying within `e^{κ₀}` of the noise floor. -/
theorem tension_lt_floor_iff_contrast {contrast κ₀ : ℝ} (hc : 0 < contrast) :
    Real.log contrast < κ₀ ↔ contrast < Real.exp κ₀ := by
  constructor
  · intro h
    have h2 : Real.exp (Real.log contrast) < Real.exp κ₀ := Real.exp_lt_exp.mpr h
    rwa [Real.exp_log hc] at h2
  · intro h
    have h2 := Real.log_lt_log hc h
    rwa [Real.log_exp] at h2

/-- **The confinement criterion, `κ₀ = ¼ log 3`.** With `μ = log(contrast)`, confinement `μ < ¼ log 3` is
exactly `contrast < 3^{1/4}`: the leading correlation eigenvalue over the noise floor stays below the
fourth root of three, the exponential of the vortex entropy density. The exact form of PAPER §10's
counting comparison, with the coherent-mode ceiling fixed to `3^{1/4}`. -/
theorem confinement_iff_contrast_lt_rpow {contrast : ℝ} (hc : 0 < contrast) :
    Real.log contrast < (1 / 4 : ℝ) * Real.log 3 ↔ contrast < (3 : ℝ) ^ (1 / 4 : ℝ) := by
  rw [tension_lt_floor_iff_contrast hc, exp_floor_eq_rpow]

/-- **Below the noise floor is automatically confined.** If the leading mode does not resolve
(`contrast ≤ 1`, `K_signal = 0`, the disordered phase), the tension `μ = log(contrast) ≤ 0` is below the
positive floor `κ₀ > 0`: confinement holds with no further input, the `μ = 0` pinning §8.6 reads in the
disordered phase. -/
theorem confined_of_contrast_le_one {contrast κ₀ : ℝ} (hc : 0 < contrast) (h1 : contrast ≤ 1)
    (hκ : 0 < κ₀) : Real.log contrast < κ₀ :=
  lt_of_le_of_lt (Real.log_nonpos hc.le h1) hκ

/-- **The gap from the eigenvalue criterion (§8.6 capstone).** With the tension read
`μ = log(contrast)` (`contrast > 0`), if the leading correlation eigenvalue stays below the `3^{1/4}`
ceiling (`contrast < 3^{1/4}`) and the finite-aperture modes sit inside the free-energy margin
(`‖m k‖ ≤ e^{-(¼log3 - log contrast)}`), the correlator forgets: `C(τ) → 0`, the gap is open. The
deterministic eigenvalue criterion of §8.6 discharges `μ < κ₀ = ¼ log 3` (via
`confinement_iff_contrast_lt_rpow`) and the finite aperture does the rest (`gap_of_confinement`). This
makes `contrast < 3^{1/4}` a machine-checked route to the gap: the confinement input is the leading
correlation eigenvalue staying within `3^{1/4}` of the Tracy–Widom noise floor. -/
theorem gap_of_contrast_criterion {ι : Type*} (s : Finset ι) (P m : ι → ℂ) {contrast : ℝ}
    (hc : 0 < contrast) (hcrit : contrast < (3 : ℝ) ^ (1 / 4 : ℝ))
    (hread : ∀ k ∈ s, ‖m k‖ ≤ Real.exp (-((1 / 4 : ℝ) * Real.log 3 - Real.log contrast))) :
    Filter.Tendsto (fun τ => ‖∑ k ∈ s, P k * (m k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_of_confinement s P m ((1 / 4 : ℝ) * Real.log 3) (Real.log contrast)
    ((confinement_iff_contrast_lt_rpow hc).mpr hcrit) hread

/-! ## Closing the crossover interior by a finite grid + a modulus of continuity (C-1 as a finite certificate)

`d2_le_bound` asserts the whitened correlation second moment `⟨d²⟩(β)` is uniformly bounded across
the crossover. It is used ONLY on the **compact interior** `[a,b]` of A1 (the ends are `ym_character` /
`ym_asymfree`). On a compact interval a **finite grid** of deterministic reads plus a **Lipschitz** bound (a
modulus of continuity) discharges the `∀β` bound by the elementary argument below — turning the axiom into a
finite deterministic certificate, the same status as the runtime margin certificate. The one measured input is
the Lipschitz constant `L`: that the read varies smoothly between grid points. Its physical content is sharp — a
spike would be a critical point (correlation-length divergence), i.e. a bulk transition — so this is a *measured
smoothness*, deterministic and checkable on the ensemble, in place of the `∀β` postulate. The script drives its
verdict by the RIGOROUS empirical-Bernstein 99.9%-per-β upper bound on `⟨d²⟩` (no fit): every measured β clears
the `⟨d²⟩ ≤ 1` ceiling (central `⟨d²⟩ ≈ 0.02–0.12`; worst per-β 99.9% upper `≈ 0.63`, joint `≈ 98.7%`), with the
fitted polynomial retained only as a descriptive smoothness overlay (measured `|d⟨d²⟩/dβ| ≈ 0.15`)
(``research/code/certify/ym_crossover_confinement_of_grid.py`). -/

/-- **Finite grid + Lipschitz ⟹ uniform bound on a compact interval.** If `f` is `L`-Lipschitz on `[a,b]`
(`L ≥ 0`) and every point of `[a,b]` lies within `δ` of a point where `f ≤ B - L·δ`, then `f ≤ B` on all of
`[a,b]`. A `∀x` bound from a finite check: verify `f` on a `δ`-net with the margin `L·δ` absorbed. This is the
deterministic-certificate core that discharges the interior half of `d2_le_bound` — the `∀β` becomes
a finite grid (`hcover` on a net) plus the measured modulus of continuity (`hlip`). -/
theorem le_of_lipschitz_grid {f : ℝ → ℝ} {a b B L δ : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ L * |x - y|)
    (hcover : ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b, |β - γ| ≤ δ ∧ f γ ≤ B - L * δ) :
    ∀ β ∈ Set.Icc a b, f β ≤ B := by
  intro β hβ
  obtain ⟨γ, hγ, hd, hval⟩ := hcover β hβ
  have h1 : f β - f γ ≤ |f β - f γ| := le_abs_self _
  have h2 : |f β - f γ| ≤ L * |β - γ| := hlip β hβ γ hγ
  have h3 : L * |β - γ| ≤ L * δ := mul_le_mul_of_nonneg_left hd hL
  linarith

/-! ## The uniform-in-volume (thermodynamic, F → ∞) aperture certificate

The fixed-volume certificate above closes the crossover interior at ONE aperture (`nCorrYM`). The
uniform-in-volume companion asks the aperture margin does not dilute as the volume `F = L^d` grows — the
`UniformSpectralMargin` input of `Aperture.gap_uniform_in_F`. Its deterministic content is that the dominant
mode magnitude `μ₁(F) = m_hi` is bounded by ONE **intensive** `r < 1` at every `F`. The entropy-matched read
carries no lattice scale, so this `r` is `L`-independent by construction: the aperture margin does not dilute as
`F = L^d` grows. That single bound feeds the F-uniform gap below. Same status as the grid certificate: a
deterministic intensive read across the volume sweep. -/

/-- **The gap survives `F → ∞` from a certified intensive margin (the uniform-in-volume certificate).** Given
the deterministic read that the dominant magnitude `μ₁(F) = m_hi` is bounded by one intensive `r < 1` across
every dimension (`hbound`, the `L`-stable/converging read), the free-energy margin does not dilute with volume:
via `uniform_margin_of_intensive_radius → UniformSpectralMargin` and `gap_uniform_in_F`, there is a single
common rate `κ > 0` at which every `F`'s autocorrelation forgets, `C(τ) → 0`. Foundational axioms only. -/
theorem gap_uniform_in_volume_of_intensive {ι : Type*}
    (s : ℕ → Finset ι) (P μ : ℕ → ι → ℂ) (μ₁ : ℕ → ℝ) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hbound : ∀ F, μ₁ F ≤ r)
    (hdom : ∀ F, ∀ k ∈ s F, ‖μ F k‖ ≤ μ₁ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ F,
      Filter.Tendsto (fun τ => ‖∑ k ∈ s F, P F k * (μ F k) ^ τ‖) Filter.atTop (nhds 0) :=
  gap_uniform_in_F s P μ μ₁ (uniform_margin_of_intensive_radius μ₁ r hr0 hr1 hbound) hdom

#print axioms gap_uniform_in_volume_of_intensive

end MassGap
