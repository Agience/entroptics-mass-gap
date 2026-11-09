import Mathlib
import MassGap.SelfSimilarStep

/-!
# MassGap.CasimirStep — the window coupling is the finite-size free energy, and the crossover is a Casimir law

The window coupling `g β w = windowCoupling N β w = 16 log Z_{2^w} − log Z_{2^{w+1}}` (`CouplingTower` §1) reads
only partition functions of periodic Wilson tori. Written with the free energy per site `f_w = log Z_{2^w} / 16^w`
of the torus of side `2^w`, it is the finite-size difference of free energies times the volume of the doubled torus,
`g β w = 16^{w+1} (f_w − f_{w+1})`. This module proves what that reading says about the self-similar step of
`SelfSimilarStep` and about the crossover. Declarations are in the namespace `MassGap.CasimirStep`.

## 1. Dyadic defect and finite-size residue (proved, abstract)

For a sequence `x : ℕ → ℝ` (`log Z` along the dyadic sides) and a candidate bulk free energy `f∞`:

* `dyadicDefect x w = 16 x_w − x_{w+1}`, `density x w = x_w / 16^w`, `residue x f∞ w = 16^w (density x w − f∞)`:
  the finite-size part of `log Z` in units of the volume, `residue_eq : residue = x_w − 16^w f∞`.
* `defect_eq_density`: `dyadicDefect x w = 16^{w+1} (density_w − density_{w+1})`.
* `defect_eq_residue`: `dyadicDefect x w = 16 residue_w − residue_{w+1}`, for every `f∞`.
* `defect_succ_le_iff`: the defect decreases at `w` iff
  `16 (density_{w+1} − density_{w+2}) ≤ density_w − density_{w+1}`: each finite-size free-energy difference is at
  most `1/16` of the previous one, i.e. the finite-size correction decays at least as fast as `1/volume` at that
  step.
* `tendsto_defect_of_residue` (the Casimir law): if `residue → c` (a finite-size correction `c / volume`, the
  Casimir term of a massless or degenerate reading), the defect tends to `15 c`.
* `exists_residue_tendsto_zero`: if the defect vanishes, some `f∞` has `residue → 0` (it is
  `f∞ = x₀ − Σ_i defect_i / 16^{i+1}`), and `tendsto_density_of_residue` makes it the limit of the densities.
* `defect_tendsto_zero_iff`: the defect vanishes iff the finite-size correction is `o(1/volume)`.

## 2. The Wilson torus (proved)

`logZ N β w = log ZR(2^w, 2^w, 2^w, 2^w)`, `NoCasimirAt N β`: some `f∞` with
`16^w (log Z_{2^w}/16^w − f∞) → 0`. `NoCasimir N`: `NoCasimirAt N β` at every `β ≥ 0`.

* `windowCoupling_eq`: `windowCoupling N β w = dyadicDefect (logZ N β) w`, no hypothesis.
* `windowCoupling_eq_freeEnergy`: `windowCoupling N β w = 16^{w+1} (f_w − f_{w+1})`.
* `windowCoupling_succ_le_iff`: one step of the self-similar decrease is the `1/volume` inequality of free
  energies.
* `vanishing_iff_noCasimirAt`: the window coupling vanishes at `β` iff `NoCasimirAt N β`. No hypothesis on `N`
  or `β`: it is algebra on the dyadic `log Z`.
* `strongEnd_iff_frequently_noCasimir`: `StrongEnd N ↔ ∃ᶠ β in atTop, NoCasimirAt N β`, for `N ≠ 0`.
* `windowGap_of_noCasimirAt`: `NoCasimirAt N β` gives the periodic Clay gap at `β`, for `2 ≤ N`, `β ≥ 0`.
* `noCasimir_of_wilsonSelfSimilar`: `WilsonSelfSimilar N → NoCasimir N`.
* `casimir_nonneg`: a Casimir coefficient `c` of the Wilson torus at `β ≥ 0` is `≥ 0` (from
  `windowCoupling_nonneg`, i.e. from transfer positivity).
* `not_wilsonSelfSimilar_of_casimir` (the Casimir obstruction): a Casimir coefficient `c ≠ 0` at one `β ≥ 0`
  excludes `WilsonSelfSimilar N`.

## 3. Second-order transfer positivity along one direction (proved), and why it cannot close the crossover

* `powSum_cube_le`: for a nonnegative finite spectrum, `(Tr K^{2m})³ ≤ (Tr K^m)² Tr K^{4m}` (two Cauchy–Schwarz
  steps; the log-convexity of `m ↦ Tr K^m` at `m, 2m, 4m`).
* `defect_double_le`: hence the one-direction defect does not increase when the extent in that direction
  doubles: `defect(2m) ≤ defect(m)`, at every value, not only in the basin.
* `LineSpectral x`: along every direction and from every corner, the whole dyadic line of `x` is `log` of the
  traces of one nonnegative finite spectrum. `p_succ_le_of_lineSpectral`: it gives `p x μ (v + e_μ) ≤ p x μ v`.
* `mixed x μ ν v = x(v+e_μ+e_ν) − 2x(v+e_μ) − 2x(v+e_ν) + 4x(v)`, the mixed second difference;
  `mixed_eq_two_p_sub`: `mixed = 2 p_μ(v) − p_μ(v+e_ν)`, so `0 ≤ mixed` says a transverse doubling at most
  doubles a directional defect.
* `lineSpectral_const`, `mixed_const`, `Δ_const`, `residue_const`: the constant corner function `log 2` (two
  exactly degenerate levels, the flux degeneracy of a deconfined centre) is line-spectral, has `mixed = log 2 ≥ 0`
  and defect `15 log 2` at every corner: it is the pure Casimir reading `c = log 2`.
* `not_vanishing_of_lineSpectral` (no-go): no argument that uses only one-direction spectral representations
  (all orders of one-direction reflection positivity, including the second-order inequality above) together
  with `0 ≤ mixed` forces the defect along the diagonal corners to vanish. The Wilson corner function carries
  the trace facts `DoublingPower.FactRep` (`DoublingWilson.factRep`); its line form with the full transfer
  spectrum is the transfer-matrix representation, not formalized here. The no-go is about the method: the same
  inequalities hold for every reflection-positive reading, a degenerate or massless one included.

So the crossover is not a consequence of positivity along directions: the obstruction is a positive Casimir
coefficient, and the input of the self-similar route is `NoCasimir N`, the finite-size free energy of the periodic Wilson
torus being `o(1/volume)` at every `β ≥ 0`.

DERIVED (module-wide): `16 = 2⁴` the copies of the side-`2^w` torus in the side-`2^{w+1}` torus and the volume
ratio; `15 = 16 − 1`; `2` the doubling and the multiplicity of the degenerate pair; `3` and `4` the exponents of
the second-order inequality (`3·2m = 2·m + 4m`); `0` the limit, the signs and the trivial point; `1` the least
window index and the step. Proof-internal: `1/16` the geometric ratio of the residue series and `1/15` its sum.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.CasimirStep

open Filter Topology Real
open MassGap.CouplingTower (windowCoupling StrongEnd windowCoupling_nonneg)
open MassGap.SelfSimilarStep (WilsonSelfSimilar vanishing_of_wilsonSelfSimilar)

/-! ## 1. Dyadic defect and finite-size residue -/

section Abstract

variable (x : ℕ → ℝ)

/-- **The dyadic defect** `16 x_w − x_{w+1}`. DERIVED: `16 = 2⁴`; `1` the step. -/
def dyadicDefect (w : ℕ) : ℝ := 16 * x w - x (w + 1)

/-- **The density** `x_w / 16^w`: the free energy per site of the torus of side `2^w`. DERIVED: `16 = 2⁴`. -/
def density (w : ℕ) : ℝ := x w / 16 ^ w

/-- **The finite-size residue** `16^w (density_w − f∞)`: the finite-size part of `log Z` in units of the
volume. DERIVED: `16 = 2⁴`. -/
def residue (f : ℝ) (w : ℕ) : ℝ := 16 ^ w * (density x w - f)

/-- DERIVED: `16 = 2⁴`. -/
theorem residue_eq (f : ℝ) (w : ℕ) : residue x f w = x w - 16 ^ w * f := by
  unfold residue density
  have : (16 : ℝ) ^ w ≠ 0 := by positivity
  field_simp

/-- **The defect is the doubled volume times the free-energy difference.** DERIVED: `16 = 2⁴`; `1` the step. -/
theorem defect_eq_density (w : ℕ) :
    dyadicDefect x w = 16 ^ (w + 1) * (density x w - density x (w + 1)) := by
  unfold dyadicDefect density
  have : (16 : ℝ) ^ w ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- **The defect in residues**, for every candidate bulk value. DERIVED: `16 = 2⁴`; `1` the step. -/
theorem defect_eq_residue (f : ℝ) (w : ℕ) :
    dyadicDefect x w = 16 * residue x f w - residue x f (w + 1) := by
  rw [residue_eq, residue_eq]
  unfold dyadicDefect
  rw [pow_succ]
  ring

/-- **One step of decrease is the `1/volume` inequality of free energies.** DERIVED: `16 = 2⁴`; `1`, `2` the
steps. -/
theorem defect_succ_le_iff (w : ℕ) :
    dyadicDefect x (w + 1) ≤ dyadicDefect x w ↔
      16 * (density x (w + 1) - density x (w + 2)) ≤ density x w - density x (w + 1) := by
  rw [defect_eq_density, defect_eq_density]
  have hp : (0 : ℝ) < 16 ^ (w + 1) := by positivity
  rw [show w + 1 + 1 = w + 2 by omega, show (16 : ℝ) ^ (w + 2) = 16 ^ (w + 1) * 16 by ring, mul_assoc]
  exact mul_le_mul_iff_of_pos_left hp

/-- **The Casimir law**: a finite-size correction `c / volume` gives the defect `15 c` in the limit.
DERIVED: `15 = 16 − 1`; `1` the step. -/
theorem tendsto_defect_of_residue {f c : ℝ} (h : Tendsto (residue x f) atTop (𝓝 c)) :
    Tendsto (dyadicDefect x) atTop (𝓝 (15 * c)) := by
  have h1 : Tendsto (fun w => residue x f (w + 1)) atTop (𝓝 c) := h.comp (tendsto_add_atTop_nat 1)
  have h2 := (h.const_mul 16).sub h1
  rw [show 15 * c = 16 * c - c by ring]
  refine h2.congr fun w => ?_
  rw [defect_eq_residue x f w]

/-- **A vanishing residue fixes the bulk value**: the densities converge to `f`. DERIVED: `0` the limit.
Proof-internal: `1/16` the ratio of the volumes. -/
theorem tendsto_density_of_residue {f : ℝ} (h : Tendsto (residue x f) atTop (𝓝 0)) :
    Tendsto (density x) atTop (𝓝 f) := by
  have hg : Tendsto (fun w : ℕ => (1 / 16 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hp := h.mul hg
  rw [mul_zero] at hp
  have hs : Tendsto (fun w => residue x f w * (1 / 16) ^ w + f) atTop (𝓝 (0 + f)) := hp.add_const f
  rw [zero_add] at hs
  refine hs.congr fun w => ?_
  unfold residue
  have : (16 : ℝ) ^ w * (1 / 16) ^ w = 1 := by rw [← mul_pow]; norm_num
  calc 16 ^ w * (density x w - f) * (1 / 16) ^ w + f
      = (16 ^ w * (1 / 16) ^ w) * (density x w - f) + f := by ring
    _ = density x w := by rw [this]; ring

/-- **A vanishing defect has a vanishing residue**: some bulk value `f` makes the finite-size correction
`o(1/volume)`. DERIVED: `0` the limit; `1` the step. Proof-internal: `1/16` the ratio of the series, `1/15` its
sum. -/
theorem exists_residue_tendsto_zero (h : Tendsto (dyadicDefect x) atTop (𝓝 0)) :
    ∃ f : ℝ, Tendsto (residue x f) atTop (𝓝 0) := by
  set g := dyadicDefect x with hgdef
  obtain ⟨C, hC⟩ := (h.abs).bddAbove_range
  have hCb : ∀ w, |g w| ≤ C := fun w => hC ⟨w, rfl⟩
  have hgeo : Summable fun i : ℕ => (1 / 16 : ℝ) ^ (i + 1) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective (add_left_injective 1)
  have hterm : ∀ (w i : ℕ), |g (w + i) / 16 ^ (i + 1)| = |g (w + i)| * (1 / 16) ^ (i + 1) := by
    intro w i
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 16 ^ (i + 1)), div_eq_mul_one_div, one_div_pow]
  have hsum : ∀ w, Summable fun i : ℕ => g (w + i) / 16 ^ (i + 1) := by
    intro w
    refine Summable.of_norm_bounded (hgeo.mul_left C) fun i => ?_
    rw [Real.norm_eq_abs, hterm]
    exact mul_le_mul_of_nonneg_right (hCb _) (by positivity)
  set E : ℕ → ℝ := fun w => ∑' i : ℕ, g (w + i) / 16 ^ (i + 1) with hEdef
  -- the residue recursion: `16 E_w = g_w + E_{w+1}`
  have hrec : ∀ w, E (w + 1) = 16 * E w - g w := by
    intro w
    have e0 := (hsum w).tsum_eq_zero_add
    have e1 : ∑' i : ℕ, g (w + (i + 1)) / 16 ^ (i + 1 + 1)
        = (∑' i : ℕ, g (w + 1 + i) / 16 ^ (i + 1)) / 16 := by
      rw [← tsum_div_const]
      congr 1
      funext i
      rw [show w + (i + 1) = w + 1 + i by omega, pow_succ]
      field_simp
    simp only [hEdef]
    rw [e0, e1]
    simp only [add_zero, zero_add, pow_one]
    ring
  refine ⟨x 0 - E 0, ?_⟩
  have hres : ∀ w, residue x (x 0 - E 0) w = E w := by
    intro w
    induction w with
    | zero => rw [residue_eq]; simp
    | succ w ih =>
      rw [hrec w, ← ih, residue_eq, residue_eq]
      simp only [hgdef, dyadicDefect]
      rw [pow_succ]
      ring
  have hEt : Tendsto E atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨W, hW⟩ := (Metric.tendsto_atTop.mp h) (ε / 2) (by positivity)
    refine ⟨W, fun w hw => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have hb : ∀ i : ℕ, |g (w + i) / 16 ^ (i + 1)| ≤ ε / 2 * (1 / 16) ^ (i + 1) := by
      intro i
      rw [hterm]
      have := hW (w + i) (by omega)
      rw [Real.dist_eq, sub_zero] at this
      exact mul_le_mul_of_nonneg_right this.le (by positivity)
    have hn : Summable fun i : ℕ => ‖g (w + i) / 16 ^ (i + 1)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun i => by rw [Real.norm_eq_abs]; exact hb i) (hgeo.mul_left (ε / 2))
    have h1 : |E w| ≤ ∑' i : ℕ, ‖g (w + i) / 16 ^ (i + 1)‖ := by
      rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hn
    have h2 : ∑' i : ℕ, ‖g (w + i) / 16 ^ (i + 1)‖ ≤ ∑' i : ℕ, ε / 2 * (1 / 16 : ℝ) ^ (i + 1) :=
      hn.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact hb i) (hgeo.mul_left (ε / 2))
    have h3 : ∑' i : ℕ, ε / 2 * (1 / 16 : ℝ) ^ (i + 1) = ε / 30 := by
      rw [tsum_mul_left]
      have : ∑' i : ℕ, (1 / 16 : ℝ) ^ (i + 1) = 1 / 15 := by
        simp_rw [pow_succ]
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
      rw [this]; ring
    linarith
  exact hEt.congr fun w => (hres w).symm

/-- **The defect vanishes iff the finite-size correction is `o(1/volume)`.** DERIVED: `0` the limit;
`15 · 0 = 0`. -/
theorem defect_tendsto_zero_iff :
    Tendsto (dyadicDefect x) atTop (𝓝 0) ↔ ∃ f : ℝ, Tendsto (residue x f) atTop (𝓝 0) := by
  refine ⟨exists_residue_tendsto_zero x, fun ⟨f, hf⟩ => ?_⟩
  have := tendsto_defect_of_residue x hf
  rwa [mul_zero] at this

end Abstract

/-! ## 2. The Wilson torus -/

variable {N : ℕ}

/-- **`log Z` on the periodic Wilson torus of side `2^w`.** DERIVED: `2` the doubling. -/
def logZ (N : ℕ) (β : ℝ) (w : ℕ) : ℝ := Real.log (RectWilson.ZR (fun _ => 2 ^ w) N β)

/-- **No Casimir term at `β`**: some bulk free energy `f∞` makes the finite-size correction of the dyadic tori
`o(1/volume)`. DERIVED: `0` the limit. -/
def NoCasimirAt (N : ℕ) (β : ℝ) : Prop := ∃ f : ℝ, Tendsto (residue (logZ N β) f) atTop (𝓝 0)

/-- **No Casimir term at any `β ≥ 0`** (the named input). DERIVED: `0` the sign. -/
def NoCasimir (N : ℕ) : Prop := ∀ β : ℝ, 0 ≤ β → NoCasimirAt N β

/-- **The window coupling is the dyadic defect of `log Z`.** DERIVED: `2` the doubling; `16 = 2⁴`. -/
theorem windowCoupling_eq (N : ℕ) (β : ℝ) (w : ℕ) :
    windowCoupling N β w = dyadicDefect (logZ N β) w := by
  unfold windowCoupling ZoomSelfScale.defectW dyadicDefect logZ
  rw [show (fun _ : Fin 4 => 2 * 2 ^ w) = fun _ => 2 ^ (w + 1) by funext; ring]

/-- **The window coupling is the doubled volume times the free-energy difference.** DERIVED: `16 = 2⁴`; `1`
the step. -/
theorem windowCoupling_eq_freeEnergy (N : ℕ) (β : ℝ) (w : ℕ) :
    windowCoupling N β w = 16 ^ (w + 1) * (density (logZ N β) w - density (logZ N β) (w + 1)) := by
  rw [windowCoupling_eq, defect_eq_density]

/-- **One self-similar decrease is the `1/volume` inequality of free energies.** DERIVED: `16 = 2⁴`; `1`, `2`
the steps. -/
theorem windowCoupling_succ_le_iff (N : ℕ) (β : ℝ) (w : ℕ) :
    windowCoupling N β (w + 1) ≤ windowCoupling N β w ↔
      16 * (density (logZ N β) (w + 1) - density (logZ N β) (w + 2))
        ≤ density (logZ N β) w - density (logZ N β) (w + 1) := by
  rw [windowCoupling_eq, windowCoupling_eq]
  exact defect_succ_le_iff _ w

/-- **The window coupling vanishes at `β` iff there is no Casimir term at `β`.** DERIVED: `0` the limit. -/
theorem vanishing_iff_noCasimirAt (N : ℕ) (β : ℝ) :
    Tendsto (windowCoupling N β) atTop (𝓝 0) ↔ NoCasimirAt N β := by
  have e : windowCoupling N β = dyadicDefect (logZ N β) := funext (windowCoupling_eq N β)
  rw [e]
  exact defect_tendsto_zero_iff _

/-- **The strong end is "no Casimir term", frequently in `β`.** DERIVED: `0` the excluded rank. -/
theorem strongEnd_iff_frequently_noCasimir (hN : N ≠ 0) :
    StrongEnd N ↔ ∃ᶠ β in atTop, NoCasimirAt N β := by
  rw [StrongEndVanishing.strongEnd_iff_vanishing hN]
  simp only [vanishing_iff_noCasimirAt]

/-- **No Casimir term at `β` gives the periodic Clay gap at `β`.** DERIVED: `2` the least rank; `0` the plane,
the time axis and the signs; `1` the upper end of the rate interval. -/
theorem windowGap_of_noCasimirAt (hN2 : 2 ≤ N) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (h : NoCasimirAt N β) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 hN β r :=
  StrongEndVanishing.windowGap_of_vanishing hN2 hN hβ ((vanishing_iff_noCasimirAt N β).mpr h)

/-- **The self-similar step gives no Casimir term.** DERIVED: `0` the excluded rank. -/
theorem noCasimir_of_wilsonSelfSimilar (hN : N ≠ 0) (h : WilsonSelfSimilar N) : NoCasimir N :=
  fun _ hβ => (vanishing_iff_noCasimirAt N _).mp (vanishing_of_wilsonSelfSimilar hN h hβ)

/-- **A Casimir coefficient of the Wilson torus is nonnegative** (transfer positivity).
DERIVED: `0` the sign; `1` the least window index; `15 = 16 − 1`. -/
theorem casimir_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {f c : ℝ}
    (h : Tendsto (residue (logZ N β) f) atTop (𝓝 c)) : 0 ≤ c := by
  have ht := tendsto_defect_of_residue _ h
  have hle : 0 ≤ 15 * c := by
    refine ge_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop 1] with w hw
    rw [← windowCoupling_eq]
    exact windowCoupling_nonneg hN hβ hw
  linarith

/-- **The Casimir obstruction**: a nonzero Casimir coefficient at one `β ≥ 0` excludes the self-similar step.
DERIVED: `0` the sign and the excluded coefficient; `15 = 16 − 1`. -/
theorem not_wilsonSelfSimilar_of_casimir (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {f c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (residue (logZ N β) f) atTop (𝓝 c)) : ¬ WilsonSelfSimilar N := by
  intro hS
  have h1 := tendsto_defect_of_residue _ h
  have h0 := vanishing_of_wilsonSelfSimilar hN hS hβ
  rw [show windowCoupling N β = dyadicDefect (logZ N β) from funext (windowCoupling_eq N β)] at h0
  have := tendsto_nhds_unique h1 h0
  exact hc (by linarith)

/-! ## 3. Second-order transfer positivity along one direction -/

open MassGap.DoublingRecursion

section Spectrum

variable {ι : Type} [DecidableEq ι] {s : Finset ι} {w : ι → ℝ}

/-- **Second-order positivity**: `(Tr K^{2m})³ ≤ (Tr K^m)² Tr K^{4m}` for a nonnegative finite spectrum.
DERIVED: `2`, `3`, `4` the exponents, `3 · 2m = 2 · m + 4m`. -/
theorem powSum_cube_le (hw : ∀ i ∈ s, 0 ≤ w i) (m : ℕ) :
    powSum s w (2 * m) ^ 3 ≤ powSum s w m ^ 2 * powSum s w (2 * (2 * m)) := by
  set u : ι → ℝ := fun i => w i ^ m with hu
  have hu0 : ∀ i ∈ s, 0 ≤ u i := fun i hi => pow_nonneg (hw i hi) m
  have e : ∀ k : ℕ, powSum s w (k * m) = ∑ i ∈ s, u i ^ k := by
    intro k; unfold powSum; refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu]; simp only; rw [← pow_mul, mul_comm]
  have eA : powSum s w m = ∑ i ∈ s, u i ^ 1 := by rw [← e 1, one_mul]
  have eB : powSum s w (2 * m) = ∑ i ∈ s, u i ^ 2 := e 2
  have eD : powSum s w (2 * (2 * m)) = ∑ i ∈ s, u i ^ 4 := by rw [← e 4]; ring_nf
  set A := ∑ i ∈ s, u i ^ 1
  set B := ∑ i ∈ s, u i ^ 2
  set C := ∑ i ∈ s, u i ^ 3
  set D := ∑ i ∈ s, u i ^ 4
  have hA : 0 ≤ A := Finset.sum_nonneg fun i hi => pow_nonneg (hu0 i hi) _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i hi => pow_nonneg (hu0 i hi) _
  have hC : 0 ≤ C := Finset.sum_nonneg fun i hi => pow_nonneg (hu0 i hi) _
  have hD : 0 ≤ D := Finset.sum_nonneg fun i hi => pow_nonneg (hu0 i hi) _
  have cs1 : B ^ 2 ≤ A * C :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i hi => pow_nonneg (hu0 i hi) _)
      (fun i hi => pow_nonneg (hu0 i hi) _) (fun i _ => by ring_nf; exact le_rfl)
  have cs2 : C ^ 2 ≤ B * D :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i hi => pow_nonneg (hu0 i hi) _)
      (fun i hi => pow_nonneg (hu0 i hi) _) (fun i _ => by ring_nf; exact le_rfl)
  rw [eA, eB, eD]
  have h4 : B ^ 4 ≤ A ^ 2 * (B * D) := by
    have : (B ^ 2) ^ 2 ≤ (A * C) ^ 2 := pow_le_pow_left₀ (sq_nonneg B) cs1 2
    calc B ^ 4 = (B ^ 2) ^ 2 := by ring
      _ ≤ (A * C) ^ 2 := this
      _ = A ^ 2 * C ^ 2 := by ring
      _ ≤ A ^ 2 * (B * D) := mul_le_mul_of_nonneg_left cs2 (sq_nonneg A)
  rcases hB.eq_or_lt with hB0 | hBp
  · rw [← hB0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg A) hD
  · have : B * B ^ 3 ≤ B * (A ^ 2 * D) := by nlinarith
    exact le_of_mul_le_mul_left this hBp

/-- **The one-direction defect does not increase when its extent doubles**, at every value.
DERIVED: `2` the doubling. -/
theorem defect_double_le {i₀ : ι} (h : Top s w i₀) (m : ℕ) : defect s w (2 * m) ≤ defect s w m := by
  have hA := powSum_pos h m
  have hB := powSum_pos h (2 * m)
  have hD := powSum_pos h (2 * (2 * m))
  have hc := powSum_cube_le h.nonneg m
  have hl := Real.log_le_log (by positivity) hc
  rw [Real.log_pow, Real.log_mul (by positivity) hD.ne', Real.log_pow] at hl
  unfold defect
  push_cast at hl
  linarith

end Spectrum

/-- **Line-spectral corner function**: along every direction and from every corner, the dyadic line of `x` is
`log` of the traces of one nonnegative finite spectrum. DERIVED: `2` the doubling. -/
def LineSpectral (x : Pt → ℝ) : Prop :=
  ∀ (μ : Fin 4) (v : Pt), ∃ (s : Finset ℕ) (w : ℕ → ℝ) (i₀ m : ℕ), Top s w i₀ ∧
    ∀ j : ℕ, x (v + j • E μ) = Real.log (powSum s w (2 ^ j * m))

/-- **Along its own direction, a line-spectral defect does not increase.** DERIVED: `1`, `2` the steps. -/
theorem p_succ_le_of_lineSpectral {x : Pt → ℝ} (hx : LineSpectral x) (μ : Fin 4) (v : Pt) :
    p x μ (v + E μ) ≤ p x μ v := by
  obtain ⟨s, w, i₀, m, hT, hl⟩ := hx μ v
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  simp only [zero_smul, add_zero, pow_zero, one_mul, one_smul, pow_one] at h0 h1 h2
  rw [two_smul, ← add_assoc, show 2 ^ 2 * m = 2 * (2 * m) by ring] at h2
  have := defect_double_le hT m
  unfold p
  unfold defect at this
  rw [h0, h1, h2]
  linarith

/-- **The mixed second difference** of a corner function in directions `μ`, `ν`. DERIVED: `2`, `4` the
coefficients of the second difference under doubling. -/
def mixed (x : Pt → ℝ) (μ ν : Fin 4) (v : Pt) : ℝ :=
  x (v + E μ + E ν) - 2 * x (v + E μ) - 2 * x (v + E ν) + 4 * x v

/-- **`0 ≤ mixed` says a transverse doubling at most doubles a directional defect.** DERIVED: `2` the
doubling. -/
theorem mixed_eq_two_p_sub (x : Pt → ℝ) (μ ν : Fin 4) (v : Pt) :
    mixed x μ ν v = 2 * p x μ v - p x μ (v + E ν) := by
  unfold mixed p
  rw [add_right_comm v (E μ) (E ν)]
  ring

/-- The degenerate pair: two levels of weight `1`. DERIVED: `2` the multiplicity; `0`, `1` the two level
labels and the weight. -/
theorem powSum_pair (k : ℕ) : powSum ({0, 1} : Finset ℕ) (fun _ => (1 : ℝ)) k = 2 := by
  unfold powSum
  rw [Finset.sum_pair (by norm_num)]
  norm_num

/-- **The constant `log 2` is line-spectral**: two exactly degenerate levels. DERIVED: `2` the multiplicity. -/
theorem lineSpectral_const : LineSpectral fun _ => Real.log 2 := by
  intro μ v
  refine ⟨{0, 1}, fun _ => 1, 0, 1, ⟨by simp, one_pos, fun _ _ => zero_le_one, fun _ _ => le_rfl⟩,
    fun j => ?_⟩
  rw [powSum_pair]

/-- DERIVED: `2` the multiplicity; `4 − 2 − 2 + 1 = 1`. -/
theorem mixed_const (μ ν : Fin 4) (v : Pt) : mixed (fun _ => Real.log 2) μ ν v = Real.log 2 := by
  unfold mixed; ring

/-- DERIVED: `15 = 16 − 1`; `2` the multiplicity. -/
theorem Δ_const (k : ℕ) : Δ (fun _ => Real.log 2) (corner k) = 15 * Real.log 2 := by
  unfold Δ; ring

/-- **The degenerate pair is the pure Casimir reading** `c = log 2` with bulk value `0`. DERIVED: `2` the
multiplicity. -/
theorem residue_const (w : ℕ) : residue (fun _ => Real.log 2) 0 w = Real.log 2 := by
  rw [residue_eq]; ring

/-- **No-go for one-direction positivity**: no argument from line spectra (every order of one-direction
transfer positivity) and nonnegative mixed differences makes the diagonal defect vanish. DERIVED: `0` the
limit and the sign. Proof-internal: `15` and `2` from `Δ_const`, the counterexample. -/
theorem not_vanishing_of_lineSpectral :
    ¬ ∀ x : Pt → ℝ, LineSpectral x → (∀ μ ν v, 0 ≤ mixed x μ ν v) →
      Tendsto (fun k => Δ x (corner k)) atTop (𝓝 0) := by
  intro h
  have ht := h _ lineSpectral_const (fun μ ν v => by
    rw [mixed_const]; exact (Real.log_pos one_lt_two).le)
  simp only [Δ_const] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  have hl := Real.log_pos one_lt_two
  linarith

end MassGap.CasimirStep

#print axioms MassGap.CasimirStep.residue_eq
#print axioms MassGap.CasimirStep.defect_eq_density
#print axioms MassGap.CasimirStep.defect_eq_residue
#print axioms MassGap.CasimirStep.defect_succ_le_iff
#print axioms MassGap.CasimirStep.tendsto_defect_of_residue
#print axioms MassGap.CasimirStep.tendsto_density_of_residue
#print axioms MassGap.CasimirStep.exists_residue_tendsto_zero
#print axioms MassGap.CasimirStep.defect_tendsto_zero_iff
#print axioms MassGap.CasimirStep.windowCoupling_eq
#print axioms MassGap.CasimirStep.windowCoupling_eq_freeEnergy
#print axioms MassGap.CasimirStep.windowCoupling_succ_le_iff
#print axioms MassGap.CasimirStep.vanishing_iff_noCasimirAt
#print axioms MassGap.CasimirStep.strongEnd_iff_frequently_noCasimir
#print axioms MassGap.CasimirStep.windowGap_of_noCasimirAt
#print axioms MassGap.CasimirStep.noCasimir_of_wilsonSelfSimilar
#print axioms MassGap.CasimirStep.casimir_nonneg
#print axioms MassGap.CasimirStep.not_wilsonSelfSimilar_of_casimir
#print axioms MassGap.CasimirStep.powSum_cube_le
#print axioms MassGap.CasimirStep.defect_double_le
#print axioms MassGap.CasimirStep.p_succ_le_of_lineSpectral
#print axioms MassGap.CasimirStep.mixed_eq_two_p_sub
#print axioms MassGap.CasimirStep.powSum_pair
#print axioms MassGap.CasimirStep.lineSpectral_const
#print axioms MassGap.CasimirStep.mixed_const
#print axioms MassGap.CasimirStep.Δ_const
#print axioms MassGap.CasimirStep.residue_const
#print axioms MassGap.CasimirStep.not_vanishing_of_lineSpectral
