import Mathlib
import MassGap.RectTorusState

/-!
# MassGap.SectorDoubling — the two sector reads under doubling the side

`CentreSectorSeedN` writes the torus defect `defectW N β n` as `8p₀ + 4p₁ + 2p₂ + p₃`, each `pᵢ` the doubling
defect of the half-time transfer `halfKN N β n i` on the slice of corner step `i`, and splits each step into the flux
share `fluxShareN N β n i` and the zero-flux defect `trivialDefectN N β n i`. This module proves how the pair moves
when the side `n` is doubled, at one coupling `β`, and restates the open input `SubstrateFluxRead.SectorSeedMeasured`
as an onset at one side. Declarations are in the namespace `MassGap.SectorDoubling`.

## Where the recursion lives

The slice of step `i` at side `n` has transverse extents `Tr n i = tr (ext n (pathV i)) i`, and `ext n v j = 2^{v j} n`.
At side `2n` every transverse extent doubles, so `halfKN N β (2n) i` is a kernel on a different configuration space,
not a kernel squaring of `halfKN N β n i`. The kernel squaring that the tree does
prove, `conv (halfKN) (halfKN)`, doubles the time direction on the same slice
(`CentreSectorSeedN.fluxShareDoubledN`, `fluxShareDoubled_leN`: the flux odds square at the cost
`exp(trivialDefectN)`); `FluxShareSquaring` records that the steps of a cubic doubling moving a direction transverse
to a twisted plane are not of that form. The side doubling is carried only by the full torus partition function:
`DoublingSharp.rec_sharp` at the corner `0`, `defectW(2n) ≤ 250 · defectW(n)²` when `defectW(n) ≤ 1/1000`. The
recursion here is that sharp step, read through the sufficiency and necessity of the sector split.

## Proved

* `dd_le_five`: at one step, flux share and zero-flux defect at most `ε ≤ 1/2` give step defect at most `5ε`;
  `defectW_le_of_sectors_eps`: at every step, `defectW ≤ 75ε`.
* `defectW_nonneg`, `defectW_double_le`: `0 ≤ defectW(n)` and, when `defectW(n) ≤ 1/1000`,
  `defectW(2n) ≤ 250 · defectW(n)²` (`DoublingSharp.rec_sharp` at the corner `0`, `WDeltaRun.Δ_corner`).
* **`sectors_double`** (the recursion): at `β ≥ 0`, even `n ≥ 2`, and `0 ≤ ε ≤ ε₀(N)`, if at every step `i`
  `fluxShareN N β n i ≤ ε` and `trivialDefectN N β n i ≤ ε`, then at every step
  `fluxShareN N β (2n) i ≤ q_N(ε)` and `trivialDefectN N β (2n) i ≤ q_N(ε)`, with

      ε₀(N) = 1 / (2812500 (N³ + 4)),      q_N(ε) = 1406250 (N³ + 4) ε² / 2.

  `qStep_le`: `q_N(ε) ≤ ε/4` on `0 ≤ ε ≤ ε₀(N)`, so the map contracts quadratically.
* **`sectors_pow`**: by induction, both reads are at most `ε / 4ᵏ` at side `2ᵏ n`, every `k`.
* Tests. `eventually_onset_strong`: at `0 ≤ β ≤ 2^{-16}` the hypothesis of the recursion holds at `ε₀(N)` at every
  large even side, from `SubstrateFluxRead.sectors_strong`; `eventually_climb_strong`: there the conclusion of
  `sectors_pow` holds. The hypothesis is therefore satisfiable on the Wilson family at `0 ≤ β ≤ 2^{-16}`. These are
  fixed-coupling tests of the recursion; they say nothing about `SectorOnset`, which is eventually in `β → ∞`.
* No constant of `sectors_double` or `sectors_pow` depends on `n` or `β`: `eps0` and `qStep` depend on `N` only
  (through `N³ = |Z_N³|`), and the floors `kTmin^{n/2}` enter only the positivity of traces.
* The recursion is a theorem for the Wilson family at every `β ≥ 0` (the statement of `sectors_double`).
* `sectorSeedMeasured_of_onset` (`ε₀(N) ≤ 1/80000`, `eps0_le`); `onset_of_sectorSeedMeasured` (with the window
  constant `C` replaced by `2ᵏ C` for a `k` depending on `N` only, `exists_climb`: the sharp squarings
  `CentreSectorSeedN.defectW_sharp` and necessity `sectors_of_defectWN`); `sectorOnset_iff`:
  `SectorOnset N hN ↔ SectorSeedMeasured hN`. `runSeed_of_sectorOnset`: with `UnitTracksRun`, `RunSeed N`.
  `sectorSeedRead_capR_iff_onset` (`N ≥ 2`): the capture form on the Wilson family `capR` is the onset.
* `climb_of_onset`: the onset gives, at the same window side `n`, both reads at most `ε₀(N)/4ᵏ` at every side
  `2ᵏ n`.

## Assumed

* `SectorOnset N hN`: `SectorSeedMeasured` with the threshold `ε₀(N)` in place of `1/80000`. It is a restatement,
  not a weaker input: `sectorOnset_iff` proves it equivalent to `SectorSeedMeasured`, with `C` rescaled by `2ᵏ`,
  `k` depending on `N` only.

## What is gained, and what is not

The recursion is proved content: one side with both reads at most `ε₀(N)` gives every dyadic side above it, with a
quadratic contraction, uniformly in `β` and `n`. It does not shrink the open input. `SectorSeedMeasured` already asks
the reads at one side, and its window clause `n · m′ ≤ C` is an upper bound on that side, and the recursion only
moves a witness upward, to sides `2ᵏn` that the window already allows only when `2ᵏn · m′ ≤ C`; it never produces a
side below `n`, so it adds nothing: `sectorOnset_iff` is an equivalence at the cost of the fixed factor `2ᵏ` in
`C`. The onset is already at a fixed physical scale (side at most `C/m′`). Moving it below the window would need a
downward step, the reads at `n` from the reads at `2n`, and no such step can be iterated down to `n · m′ ≪ 1`
(argued: at weak coupling and `n · m′ ≪ 1` the flux sectors are nearly degenerate with the zero-flux sector, so the
flux share is near `1 − N⁻³`, while at `n · m′ ≫ 1` it is small), so the onset cannot be pushed below the window.
At a fixed aperture a downward step along the chain exists, `RelayChain.relayOdds_down` (chain index `2m` to `m`),
anchored on the one-hop odds `o(0)` at the cost of the zero-flux ratio `κ(0,m)`; it leaves the aperture fixed, so it
is not the step `n ← 2n`. `RelayChain.CoarseReadsFine` (assumed) relates aperture `2T` to `T` upward, and gives no
downward step.
The `∀ k` form that `climb_of_onset` gives is a corollary of the one-side form, so the "every scale" statement is
free once one scale holds.

## Argued, not proved

* A deconfined theory (4D `Z₂` at weak coupling) is not the `SU(N)` Wilson family and is not built; on it the
  flux clause fails at every side, so the hypothesis of `sectors_double` is never met there, and the recursion makes
  no claim about it. No example in the tree has the hypothesis and fails the conclusion.
* At `β = 0` both reads vanish at every even side `n ≥ 2` (`sectors_strong` with `β = 0`), the degenerate case of
  the recursion at `ε = 0`.

## Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every statement | shared, in the substrate; fixed in `sectors_double`, `sectors_pow` |
| `n` (side) | `sectors_double`, `sectors_pow` | the side of one onset; even, `≥ 2`; no constant depends on it |
| `k` (doublings) | `sectors_pow`, `climb_of_onset` | swept over all |
| `ε` | `sectors_double`, `sectors_pow` | chosen: any value in `[0, ε₀(N)]` |
| `ε₀(N)`, `q_N` | `eps0`, `qStep` | derived from `250` (`rec_sharp`), `75 = 15 · 5`, `4 + N⁶ ≤ (N³ + 4)²`; depend on `N` only |
| `C`, `m′` | `SectorOnset` | measured: as in `SectorSeedMeasured`; `C` rescaled by `2ᵏ`, `k` depending on `N` only |
| `aRun`, `c₁` | `UnitTracksRun` only | shared: supplied spacing, met only to reach `RunSeed` |
| `N` | the type | shared with the substrate; not measured |

DERIVED (module-wide): `5 = 1 + 2 · 2` (zero-flux defect plus twice the log of the inverse zero-flux share, which
is at most `2ε` at a share of at least `1/2`); `75 = (8 + 4 + 2 + 1) · 5` the corner-path weights; `250` and `1/1000`
are `DoublingSharp.rec_sharp`'s; `1406250 = 250 · 75²`, `2812500 = 2 · 1406250`; `N³ + 4` bounds both outputs
`N³ δ/2` and `2δ` of `sectors_of_defectWN` and `√(4 + N⁶)`; `4` in `ε/4` is the contraction at `ε ≤ ε₀`,
`q_N(ε)/ε = 1406250 (N³ + 4) ε/2 ≤ 1406250/(2 · 2812500) = 1/4`; `1/80000` is `SectorSeedMeasured`'s threshold; `65536 = 2^{16}` is `sectors_strong`'s.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.SectorDoubling

open Filter Topology
open scoped ENNReal NNReal
open MassGap.KernelPower MassGap.SectorDefect
open MassGap.DoublingRecursion (Δ corner corner_succ)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN trivKN hSN halfKN hs_halfKN_pos hs_trivKN_pos
  dd_le_trivKN defectW_eqN defectW_le_of_sectorsN sectors_of_defectWN defectW_sharp)
open MassGap.SubstrateFluxRead (SectorSeedMeasured runSeed_of_sectorSeedMeasured)
open MassGap.SubstrateDecode (measMassOf tensorEnergy UnitTracksRun)
open MassGap.PeriodicState (periodicState)
open MassGap.ZoomSelfScale (defectW)

variable {N : ℕ}

/-! ## 1. The constants -/

/-- **The threshold of the recursion**, `ε₀(N) = 1/(2812500 (N³ + 4))`. DERIVED: `2812500 = 2 · 250 · 75²`;
`4` from `4 + N⁶ ≤ (N³ + 4)²`. -/
def eps0 (N : ℕ) : ℝ := 1 / (2812500 * ((N : ℝ) ^ 3 + 4))

/-- **The step map**, `q_N(ε) = 1406250 (N³ + 4) ε²/2`. DERIVED: `1406250 = 250 · 75²`; `2` from `N³δ/2`. -/
def qStep (N : ℕ) (ε : ℝ) : ℝ := 1406250 * ((N : ℝ) ^ 3 + 4) * ε ^ 2 / 2

/-- DERIVED: no numeral. -/
theorem eps0_pos (N : ℕ) : 0 < eps0 N := by unfold eps0; positivity

/-- **The threshold is below the seed threshold.** DERIVED: `1/80000`. -/
theorem eps0_le (N : ℕ) : eps0 N ≤ 1 / 80000 := by
  unfold eps0
  have hc : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- DERIVED: `2812500`, `4`; `3` in `N³ = |Z_N³|`, the spatial directions of a time slice. -/
theorem mul_le_one_of_le_eps0 {ε : ℝ} (hε : ε ≤ eps0 N) :
    2812500 * ((N : ℝ) ^ 3 + 4) * ε ≤ 1 := by
  have hp : (0 : ℝ) < 2812500 * ((N : ℝ) ^ 3 + 4) := by positivity
  unfold eps0 at hε
  rw [le_div_iff₀ hp] at hε
  linarith

/-- **The step map contracts below the threshold**: `q_N(ε) ≤ ε/4`. DERIVED: `4`. -/
theorem qStep_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ eps0 N) : qStep N ε ≤ ε / 4 := by
  have hu := mul_le_one_of_le_eps0 hε
  unfold qStep
  nlinarith [mul_le_mul_of_nonneg_left hu hε0]

/-! ## 2. Sufficiency at a general threshold -/

section Wilson

variable [NeZero N]

/-- **One step**: flux share and zero-flux defect at most `ε ≤ 1/2` give step defect at most `5ε`.
DERIVED: `5 = 1 + 2 · 2`; `1/2` the least zero-flux share at which `(A − B)/B ≤ 2 (A − B)/A`. -/
theorem dd_le_five {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hf : fluxShareN N β n i ≤ ε) (ht : trivialDefectN N β n i ≤ ε) :
    dd (hSN N n i) (halfKN N β n i) ≤ 5 * ε := by
  set A := hs (hSN N n i) (halfKN N β n i) with hAdef
  set B := hs (hSN N n i) (trivKN N β n i) with hBdef
  have hA : 0 < A := hs_halfKN_pos hβ n i
  have hB : 0 < B := hs_trivKN_pos hβ n i
  have h1 : A - B ≤ ε * A := by
    have := (div_le_iff₀ hA).mp hf
    linarith
  have hA2B : A ≤ 2 * B := by
    have : ε * A ≤ 1 / 2 * A := mul_le_mul_of_nonneg_right hε hA.le
    linarith
  have h1' : A - B ≤ 2 * ε * B := by
    have : ε * A ≤ ε * (2 * B) := mul_le_mul_of_nonneg_left hA2B hε0
    linarith
  have h2 : Real.log A - Real.log B ≤ (A - B) / B := by
    rw [← Real.log_div hA.ne' hB.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hA hB)
    have e : (A - B) / B = A / B - 1 := by rw [sub_div, div_self hB.ne']
    linarith
  have h3 : (A - B) / B ≤ 2 * ε := by
    rw [div_le_iff₀ hB]
    linarith
  have hdd := dd_le_trivKN (N := N) hβ n i
  linarith

/-- **Sufficiency at threshold `ε`**: both reads at most `ε ≤ 1/2` at every step give `defectW ≤ 75ε`.
DERIVED: `75 = 15 · 5`, `15 = 8 + 4 + 2 + 1`. -/
theorem defectW_le_of_sectors_eps {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : ∀ i : Fin 4, fluxShareN N β n i ≤ ε ∧ trivialDefectN N β n i ≤ ε) :
    defectW N β n ≤ 75 * ε := by
  have hs := fun i => dd_le_five (N := N) hβ n i hε0 hε (h i).1 (h i).2
  rw [defectW_eqN hβ hn he]
  linarith [hs 0, hs 1, hs 2, hs 3]

/-! ## 3. The sharp doubling of the torus defect -/

/-- **The torus defect is non-negative.** DERIVED: `0` the corner. -/
theorem defectW_nonneg {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    0 ≤ defectW N β n := by
  have hp := DoublingWilson.positive (NeZero.ne N) hβ hn he
  have h := DoublingRecursion.Δ_nonneg hp (corner 0)
  rw [WDeltaRun.Δ_corner] at h
  simpa using h

/-- **One sharp doubling of the side**: `defectW(2n) ≤ 250 · defectW(n)²` when `defectW(n) ≤ 1/1000`.
DERIVED: `250`, `1/1000` from `DoublingSharp.rec_sharp`. -/
theorem defectW_double_le {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (h : defectW N β n ≤ 1 / 1000) : defectW N β (2 * n) ≤ 250 * defectW N β n ^ 2 := by
  have hx := DoublingSharp.positiveS_of_facts (DoublingWilson.factRep (NeZero.ne N) hβ hn he)
  have h0 : Δ (DoublingWilson.xW N n β) (corner 0) ≤ 1 / 1000 := by
    rw [WDeltaRun.Δ_corner]; simpa using h
  have hr := DoublingSharp.rec_sharp hx (corner 0) h0
  rw [← corner_succ, WDeltaRun.Δ_corner, WDeltaRun.Δ_corner] at hr
  simpa using hr

/-! ## 4. The recursion -/

/-- **The two sector reads under doubling the side.** At `β ≥ 0`, even `n ≥ 2` and `0 ≤ ε ≤ ε₀(N)`: both reads
at most `ε` at every step of side `n` give both reads at most `q_N(ε)` at every step of side `2n`.
DERIVED: `1406250 = 250 · 75²`; `1/1000`, `75`, `1/2` as above; `2`, `4`, `6` the side doubling and the powers
of `sectors_of_defectWN`'s condition. -/
theorem sectors_double {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ eps0 N)
    (h : ∀ i : Fin 4, fluxShareN N β n i ≤ ε ∧ trivialDefectN N β n i ≤ ε) (i : Fin 4) :
    fluxShareN N β (2 * n) i ≤ qStep N ε ∧ trivialDefectN N β (2 * n) i ≤ qStep N ε := by
  have hc : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hu := mul_le_one_of_le_eps0 hε
  have hcε := mul_nonneg hc hε0
  have hε1 : ε ≤ 1 / 11250000 := by nlinarith
  have hd5 : defectW N β n ≤ 75 * ε := defectW_le_of_sectors_eps hβ hn he hε0 (by linarith) h
  have hd0 := defectW_nonneg (N := N) hβ hn he
  have hdd := defectW_double_le (N := N) hβ hn he (by linarith)
  have hsq : defectW N β n ^ 2 ≤ (75 * ε) ^ 2 := pow_le_pow_left₀ hd0 hd5 2
  have h2n : defectW N β (2 * n) ≤ 1406250 * ε ^ 2 := by nlinarith
  have hn2 : 2 ≤ 2 * n := by omega
  have he2 : Even (2 * n) := even_two_mul n
  have hδ0 : 0 ≤ 1406250 * ε ^ 2 := by positivity
  have hcond : (4 + (N : ℝ) ^ 6) * (1406250 * ε ^ 2) ≤ 2 := by
    have hsq6 : ((N : ℝ) ^ 3 + 4) ^ 2 = (N : ℝ) ^ 6 + 8 * (N : ℝ) ^ 3 + 16 := by ring
    have h6 : 4 + (N : ℝ) ^ 6 ≤ ((N : ℝ) ^ 3 + 4) ^ 2 := by rw [hsq6]; linarith
    have hv0 : 0 ≤ ((N : ℝ) ^ 3 + 4) * ε := by positivity
    have hv : 2812500 * (((N : ℝ) ^ 3 + 4) * ε) ≤ 1 := by linarith
    have hv2 : 1406250 * (((N : ℝ) ^ 3 + 4) * ε) ^ 2 ≤ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hv hv0]
    calc (4 + (N : ℝ) ^ 6) * (1406250 * ε ^ 2)
        ≤ ((N : ℝ) ^ 3 + 4) ^ 2 * (1406250 * ε ^ 2) := mul_le_mul_of_nonneg_right h6 hδ0
      _ = 1406250 * (((N : ℝ) ^ 3 + 4) * ε) ^ 2 := by ring
      _ ≤ 2 := hv2
  obtain ⟨hf, ht⟩ := sectors_of_defectWN hβ hn2 he2 hδ0 hcond h2n i
  have he2' : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hq1 : (N : ℝ) ^ 3 * (1406250 * ε ^ 2) / 2 ≤ qStep N ε := by
    unfold qStep; nlinarith
  have hq2 : 2 * (1406250 * ε ^ 2) ≤ qStep N ε := by
    unfold qStep; nlinarith [mul_nonneg hc he2']
  exact ⟨hf.trans hq1, ht.trans hq2⟩

/-- **Every dyadic side above an onset**: both reads at most `ε ≤ ε₀(N)` at side `n` give both reads at most
`ε/4ᵏ` at side `2ᵏ n`, every `k`. DERIVED: `4` from `qStep_le`; `2` the doubling. -/
theorem sectors_pow {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ eps0 N)
    (h : ∀ i : Fin 4, fluxShareN N β n i ≤ ε ∧ trivialDefectN N β n i ≤ ε) (k : ℕ) :
    ∀ i : Fin 4, fluxShareN N β (2 ^ k * n) i ≤ ε / 4 ^ k ∧
      trivialDefectN N β (2 ^ k * n) i ≤ ε / 4 ^ k := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hn' : 2 ≤ 2 ^ k * n := by nlinarith
    have he' : Even (2 ^ k * n) := he.mul_left _
    have hεk0 : 0 ≤ ε / 4 ^ k := by positivity
    have hεk : ε / 4 ^ k ≤ eps0 N :=
      (div_le_self hε0 (one_le_pow₀ (by norm_num))).trans hε
    intro i
    obtain ⟨hf, ht⟩ := sectors_double hβ hn' he' hεk0 hεk ih i
    have hq := qStep_le hεk0 hεk
    have e : ε / 4 ^ k / 4 = ε / 4 ^ (k + 1) := by rw [pow_succ, div_div]
    have hside : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
    rw [hside, ← e]
    exact ⟨hf.trans hq, ht.trans hq⟩

/-! ## 5. Tests at strong coupling -/

/-- **The hypothesis of the recursion is met at strong coupling**: at `0 ≤ β ≤ 2^{-16}` both reads are at most
`ε₀(N)` at every step of every large even side. DERIVED: `65536 = 2^{16}`; `2` the least side and the `2δ` of
`sectors_strong`. -/
theorem eventually_onset_strong {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    ∀ᶠ n : ℕ in atTop, Even n → ∀ i : Fin 4,
      fluxShareN N β n i ≤ eps0 N ∧ trivialDefectN N β n i ≤ eps0 N := by
  have h1 := SubstrateFluxRead.eventually_sector_condition (N := N) β
  have h2 := (tendsto_order.mp (SubstrateFluxRead.tendsto_fluxBound (N := N) β)).2 (eps0 N) (eps0_pos N)
  have h3 : ∀ᶠ n : ℕ in atTop, 2 * (β * StrongFiniteSize.strongBound n) < eps0 N := by
    have h := (StrongFiniteSize.tendsto_strongBound.const_mul β).const_mul 2
    rw [mul_zero, mul_zero] at h
    exact (tendsto_order.mp h).2 _ (eps0_pos N)
  filter_upwards [h1, h2, h3, eventually_ge_atTop 2] with n hn1 hn2 hn3 hn4 he i
  obtain ⟨hf, hd⟩ := SubstrateFluxRead.sectors_strong (N := N) hβ0 hβ hn4 he hn1 i
  exact ⟨hf.trans hn2.le, hd.trans hn3.le⟩

/-- **The recursion at strong coupling**: from every large even side the reads climb every dyadic side, at most
`ε₀(N)/4ᵏ`. DERIVED: `65536 = 2^{16}`; `2` the least side. -/
theorem eventually_climb_strong {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    ∀ᶠ n : ℕ in atTop, Even n → ∀ k : ℕ, ∀ i : Fin 4,
      fluxShareN N β (2 ^ k * n) i ≤ eps0 N / 4 ^ k ∧
        trivialDefectN N β (2 ^ k * n) i ≤ eps0 N / 4 ^ k := by
  filter_upwards [eventually_onset_strong (N := N) hβ0 hβ, eventually_ge_atTop 2] with n h hn he k
  exact sectors_pow hβ0 hn he (eps0_pos N).le le_rfl (h he) k

/-! ## 6. The open input as an onset -/

/-- Some number `k` of sharp squarings brings the defect below `ε₀(N)/(N³ + 4)`. DERIVED: `250`, `1/4` from
`DoublingSharp.iterate_sharp`; `3` in `N³ = |Z_N³|`, the spatial directions of a time slice; `4` in `N³ + 4`
the bound of `sectors_of_defectWN`'s outputs. -/
theorem exists_climb (N : ℕ) :
    ∃ k : ℕ, ((1 : ℝ) / 4) ^ (2 ^ k) ≤ 250 * (eps0 N / ((N : ℝ) ^ 3 + 4)) := by
  have hpos : (0 : ℝ) < 250 * (eps0 N / ((N : ℝ) ^ 3 + 4)) := by
    have := eps0_pos N; positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (show (1 / 4 : ℝ) < 1 by norm_num)
  refine ⟨m, le_trans ?_ hm.le⟩
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_two_pow_self (n := m)).le

/-- A defect at most `ε₀(N)/(N³ + 4)` gives both reads at most `ε₀(N)` at every step (necessity).
DERIVED: `4`, `6`, `2` from `sectors_of_defectWN`; `2812500` from `eps0`; `3` in `N³ = |Z_N³|`, the spatial
directions of a time slice. -/
theorem sectors_of_defect_climb {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (hd : defectW N β n ≤ eps0 N / ((N : ℝ) ^ 3 + 4)) (i : Fin 4) :
    fluxShareN N β n i ≤ eps0 N ∧ trivialDefectN N β n i ≤ eps0 N := by
  have hc : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hc4 : (0 : ℝ) < (N : ℝ) ^ 3 + 4 := by positivity
  have he0 := eps0_pos N
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = eps0 N / ((N : ℝ) ^ 3 + 4) := ⟨_, rfl⟩
  rw [← hδdef] at hd
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδe : δ * ((N : ℝ) ^ 3 + 4) = eps0 N := by rw [hδdef, div_mul_cancel₀ _ hc4.ne']
  have hu : 2812500 * ((N : ℝ) ^ 3 + 4) * eps0 N ≤ 1 := mul_le_one_of_le_eps0 le_rfl
  have hcond : (4 + (N : ℝ) ^ 6) * δ ≤ 2 := by
    have hsq6 : ((N : ℝ) ^ 3 + 4) ^ 2 = (N : ℝ) ^ 6 + 8 * (N : ℝ) ^ 3 + 16 := by ring
    have h6 : 4 + (N : ℝ) ^ 6 ≤ ((N : ℝ) ^ 3 + 4) ^ 2 := by rw [hsq6]; linarith
    have e : ((N : ℝ) ^ 3 + 4) ^ 2 * δ = ((N : ℝ) ^ 3 + 4) * eps0 N := by rw [← hδe]; ring
    have h7 : ((N : ℝ) ^ 3 + 4) * eps0 N ≤ 2 := by
      nlinarith [mul_nonneg hc he0.le]
    calc (4 + (N : ℝ) ^ 6) * δ ≤ ((N : ℝ) ^ 3 + 4) ^ 2 * δ := mul_le_mul_of_nonneg_right h6 hδ0
      _ = ((N : ℝ) ^ 3 + 4) * eps0 N := e
      _ ≤ 2 := h7
  obtain ⟨hf, ht⟩ := sectors_of_defectWN hβ hn he hδ0 hcond hd i
  have hcδ := mul_nonneg hc hδ0
  refine ⟨hf.trans ?_, ht.trans ?_⟩
  · nlinarith
  · nlinarith

variable (N) in
/-- **The sector onset** (assumed): `SectorSeedMeasured` at the recursion threshold. There is `C > 0` such that,
eventually in `β`, the unit channel locks (`0 < m′`) and some power of two `n ≥ 2` with `n · m′ ≤ C` has both reads
at most `ε₀(N)` at every step. It is a restatement, not a weaker input: `sectorOnset_iff` proves it equivalent to
`SectorSeedMeasured`, with `C` rescaled by `2ᵏ`, `k` depending on `N` only. DERIVED: `2` the least side. -/
def SectorOnset (hN : N ≠ 0) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, 0 < measMassOf (periodicState hN β) tensorEnergy ∧
    ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ≤ ENNReal.ofReal C ∧
      ∀ i : Fin 4, fluxShareN N β n i ≤ eps0 N ∧ trivialDefectN N β n i ≤ eps0 N

/-- **The onset gives the measured seed** (`ε₀(N) ≤ 1/80000`). DERIVED: no numeral. -/
theorem sectorSeedMeasured_of_onset (hN : N ≠ 0) (h : SectorOnset N hN) : SectorSeedMeasured hN := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with β hβS
  obtain ⟨hm, n, hp, hn2, hnm, hs⟩ := hβS
  exact ⟨hm, n, hp, hn2, hnm, fun i => ⟨(hs i).1.trans (eps0_le N), (hs i).2.trans (eps0_le N)⟩⟩

/-- **The measured seed gives the onset**, `k` sides further up (`exists_climb`), the window constant multiplied by
`2ᵏ`. DERIVED: `0` the threshold of the eventual coupling; `2` the doubling. -/
theorem onset_of_sectorSeedMeasured (hN : N ≠ 0) (h : SectorSeedMeasured hN) : SectorOnset N hN := by
  obtain ⟨k, hk⟩ := exists_climb N
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨2 ^ k * C, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβS hβ
  obtain ⟨hm, n, hp, hn2, hnm, hs⟩ := hβS
  have he : Even n := FluxDuality.even_of_pow2 hp hn2
  have hd := defectW_le_of_sectorsN hβ hn2 he hs
  have hsh := defectW_sharp hβ hn2 he hd k
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hn' : 2 ≤ 2 ^ k * n := by nlinarith
  have he' : Even (2 ^ k * n) := he.mul_left _
  have hdk : defectW N β (2 ^ k * n) ≤ eps0 N / ((N : ℝ) ^ 3 + 4) := by linarith
  refine ⟨hm, 2 ^ k * n, ?_, hn', ?_, fun i => sectors_of_defect_climb hβ hn' he' hdk i⟩
  · obtain ⟨b, rfl⟩ := hp
    exact ⟨k + b, by rw [pow_add]⟩
  · have e1 : ENNReal.ofReal (2 ^ k * C) = 2 ^ k * ENNReal.ofReal C := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    rw [e1]
    push_cast
    rw [mul_assoc]
    gcongr

/-- **The onset is the measured seed.** DERIVED: no numeral. -/
theorem sectorOnset_iff (hN : N ≠ 0) : SectorOnset N hN ↔ SectorSeedMeasured hN :=
  ⟨sectorSeedMeasured_of_onset hN, onset_of_sectorSeedMeasured hN⟩

/-- **The onset, with the unit tracking the run, gives the run seed.** DERIVED: no numeral. -/
theorem runSeed_of_sectorOnset (hN : N ≠ 0) (h : SectorOnset N hN) (hU : UnitTracksRun hN) :
    WDeltaRun.RunSeed N :=
  runSeed_of_sectorSeedMeasured hN (sectorSeedMeasured_of_onset hN h) hU

/-- **On the Wilson family the capture read is the onset** (`N ≥ 2`). DERIVED: `2` the least rank. -/
theorem sectorSeedRead_capR_iff_onset (hN : N ≠ 0) (hN2 : 2 ≤ N) :
    FluxDuality.SectorSeedRead hN (RectTorusState.capR hN) ↔ SectorOnset N hN :=
  (RectTorusState.sectorSeedRead_capR_iff hN hN2).trans (sectorOnset_iff hN).symm

/-- **The onset climbs**: at the same window side `n`, both reads are at most `ε₀(N)/4ᵏ` at every side `2ᵏ n`.
DERIVED: `0` the threshold of the eventual coupling; `2`, `4` as in `sectors_pow`. -/
theorem climb_of_onset (hN : N ≠ 0) (h : SectorOnset N hN) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, 0 < measMassOf (periodicState hN β) tensorEnergy ∧
      ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
        (n : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ≤ ENNReal.ofReal C ∧
        ∀ k : ℕ, ∀ i : Fin 4, fluxShareN N β (2 ^ k * n) i ≤ eps0 N / 4 ^ k ∧
          trivialDefectN N β (2 ^ k * n) i ≤ eps0 N / 4 ^ k := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβS hβ
  obtain ⟨hm, n, hp, hn2, hnm, hs⟩ := hβS
  exact ⟨hm, n, hp, hn2, hnm,
    sectors_pow hβ hn2 (FluxDuality.even_of_pow2 hp hn2) (eps0_pos N).le le_rfl hs⟩

end Wilson

end MassGap.SectorDoubling

end

#print axioms MassGap.SectorDoubling.eps0_le
#print axioms MassGap.SectorDoubling.qStep_le
#print axioms MassGap.SectorDoubling.dd_le_five
#print axioms MassGap.SectorDoubling.defectW_le_of_sectors_eps
#print axioms MassGap.SectorDoubling.defectW_nonneg
#print axioms MassGap.SectorDoubling.defectW_double_le
#print axioms MassGap.SectorDoubling.sectors_double
#print axioms MassGap.SectorDoubling.sectors_pow
#print axioms MassGap.SectorDoubling.eventually_onset_strong
#print axioms MassGap.SectorDoubling.eventually_climb_strong
#print axioms MassGap.SectorDoubling.exists_climb
#print axioms MassGap.SectorDoubling.sectors_of_defect_climb
#print axioms MassGap.SectorDoubling.sectorOnset_iff
#print axioms MassGap.SectorDoubling.runSeed_of_sectorOnset
#print axioms MassGap.SectorDoubling.sectorSeedRead_capR_iff_onset
#print axioms MassGap.SectorDoubling.climb_of_onset
