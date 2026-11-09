import Mathlib
import MassGap.MeasuredSpacing

/-!
# MassGap.ContractionReads — the strong-coupling reads from one contraction, and the window contraction

Every theorem of the tree at the threshold `|β| ≤ 2^{-16}` uses the small coupling in one place (the strong-coupling
routes with other thresholds, `StrongCoupling`, `VortexStrong` and their consumers, are not of this form): the
Dobrushin row sum of the single-link specification is below a rate `θ < 1`, which gives a kernel-near
bound (boundary influence on a box kernel decays geometrically in the depth). Everything after that uses
only the kernel-near bound. This module names that bound for a general rate and block side, restates the
consumers with it as the hypothesis, recovers the strong-coupling theorems listed in §3 as instances, and states the
window-scale input in measured units. Declarations are in the namespace `MassGap.ContractionReads`.

## 1. Where small `β` enters (traced)

* `StrongKernelNear.kernel_near_strong` (StrongKernelNear.lean:551) assumes `64 · c0 β < θ`: the
  single-link influence `infl β i j = 2(e^{2K_{ij}} − 1)` (:245) is at most `c0 β = 2(e^{64|β|} − 1)` (:248),
  a link has at most `64` neighbours (`card_nbr_le`, :216), so `64 · c0 β` is the Dobrushin row sum. It is consumed in `qrate_mem` (:534) and in `kernel_near_strong` itself (:595, :606, the sign of `θ − 64 · c0 β`);
`sum_upd_le` (:467) supplies that term without assuming its sign. `kernelNear_strong` (:659) is the Wilson instance.
* `row_le_quarter` (:671) turns `|β| ≤ 1/65536` into `64 · c0 β ≤ 1/4`; its one use is inside
  `kernelNear_strong_explicit` (:693), at `θ = 1/2`.
* Every downstream theorem reaches `|β| ≤ 2^{-16}` only through `kernelNear_strong_explicit`, called at
  `StrongFiniteSize.torusState_sub_le` (StrongFiniteSize.lean:216) and `ObserverBlockReading.cov_sep_strong`
  (ObserverBlockReading.lean:649, then `BoxFocusTest.cov_le_of_kernelNear` at :665, which uses only DLR
  consistency). The rest pass the hypothesis on: `plaq_sub_le`, `bareRead_sub_le`, `finiteSize_decay_strong`,
  `abs_bareDelta_le` (StrongFiniteSize.lean:303, :324, :370, :397); `torusState_sub_le_reach`
  (StrongLocalFiniteSize.lean:192); `blockCov_strong`, `pairDecay_strong` (ObserverBlockReading.lean:750,
  :796); `decaysAt_strong` (SubstrateDecode.lean:243); `sectors_strong` (SubstrateFluxRead.lean:738);
  `trivialDefectN_strong` (ZeroFluxGap.lean:591, :593).
* One exception to "one coupling": `defectW N β n = ∫₀^β bareDelta` (`FlowComp.integral_bareDelta`), so
  `integral_bareDelta_strong_le` (StrongFiniteSize.lean:407) uses the contraction at every `x ∈ [0, β]`.
  The proved route to the sector bounds inherits this: it needs the contraction along the coupling path, not at `β`
alone.

## 2. The carrier (defined; instances proved)

**`KernelDecayAt hN β b K θ`**: `1 ≤ K`, `0 < θ ≤ 1`, and for every centre `c`, every `σ ≤ ρ`, every link set
`A` within sup-distance `b σ` of `c` and every test `X` with `|X| ≤ 1` local on `A`,
`KernelNear hN β (cbox c (b ρ)) X (K · min(|A|, 4(2σ + 1)⁴) · θ^{ρ − σ})`. The box kernel of the fine Wilson
specification forgets its boundary at rate `θ` per block of side `b` of depth. At `b = 1` it is the
lattice-unit form of the single-link sweep; at `b > 1` it is a block-scale form on all bounded tests; `StrongKernelNear` §4 and `BlockDobrushin` §3 item 3
argue that total variation fails at fixed lattice block side as `β → ∞`, and this form escapes that reading only
because `b` grows with `1/m′` and every test sits at least one block deep (§5).

* `kernelDecayAt_of_row`: `64 · c0 β < θ ≤ 1` and `2θ ≤ K` give `KernelDecayAt hN β 1 K θ`.
* `kernelDecayAt_strong`: `|β| ≤ 2^{-16}` gives `KernelDecayAt hN β 1 1 (1/2)`.

## 3. The consumers, restated (proved), and the strong-coupling theorems as instances (proved)

| restated (contraction `K`, `θ`) | constant | strong instance, same statement as |
|---|---|---|
| `cov_sep_of` (any block side `b`) | `2 K min(|A|, 4(2σ+1)⁴) θ^{ρ−σ} BF BH` | `ObserverBlockReading.cov_sep_strong` (`cov_sep_strong_rec`) |
| `torusState_sub_le_of` | `2 K min(|A|, …) θ^{R−s}` | `StrongFiniteSize.torusState_sub_le` (`torusState_sub_le_rec`) |
| `torusState_sub_le_reach_of` | `8 K (2r+1)⁴ B θ^{R−r}` | `StrongLocalFiniteSize.torusState_sub_le_reach` (`…_reach_rec`) |
| `doubling_sub_le_of`, `tendsto_doubling_of` | `8 K (2r+1)⁴ B θ^{⌊(n−3)/2⌋ − r}`; `→ 0` at `θ < 1` | |
| `bareRead_sub_le_of`, `bareRead_doubling_of` | `128 K θ^{R−1}`; `doubleBound K θ n` | `bareRead_sub_le`, `finiteSize_decay_strong` (`…_rec`) |
| `abs_defectW_le_of_path` (contraction on `[0, β]`) | `β · pathBound K θ n` | |
| `sectors_of_path` | `N³ β pathBound/2`, `2 β pathBound` | `sectors_strong`, `trivialDefectN_strong` (`…_rec`) |
| `blockCov_of`, `pairDecay_of` | `contQ K θ b ρ`, rate `θ^b` | `pairDecay_strong` (`pairDecay_strong_rec`, via `contQ_strong`) |
| `decaysAt_of`, `measMass_of` | `DecaysAt … siteEnergy (−log θ)`, `measMass ≥ −log θ` | `decaysAt_strong`, `measMass_strong` (`…_rec`) |
| `decaysAt_of_scale`, `tensorLock_of_scale` (block side `b`) | rate `−log θ / b` for any bounded reading of reach `r` | |

`contQ K θ b ρ = 8K(2(b + ρ) + 1)⁴ θ^{−(2(b+ρ)+1)}` (`contQ 1 (1/2) = strongQ`), `doubleBound K θ n =
128 K θ^{⌊(n−3)/2⌋−1}` at `n ≥ 5` and `64` below, `pathBound K θ n = 16 n⁴ doubleBound K θ n`
(`pathBound 1 (1/2) n ≤ StrongFiniteSize.strongBound n`, `pathBound_strong_le`).

## 4. The window input, one Prop (assumed)

**`WindowContraction hN`**: there are `C > 0`, `K`, `θ < 1` such that, eventually in `β`, some block side
`b ≥ 1` with `b · m′ ≤ C` (`m′ = measMassOf (periodicState hN β) tensorEnergy`, the measured unit) has
`KernelDecayAt hN β b K θ`. The block is at most `C` measured lengths; `C`, `K`, `θ` are fixed before `β`, and
inside `KernelDecayAt` before the centre, the depths, the test set and the test, so before any block set.

### What it gives (proved)

* (a) The positivity of the unit (the second clause of `MeasuredTower.UnitLockG`; not the first, `m′ → 0`). `decaysAt_of_scale` / `tensorLock_of_scale`: a contraction at block side `b` gives decay of the
  fine tensor reading at rate `−log θ / b`, so `m′ ≥ −log θ / b > 0`. `window_lock`: eventually
  `0 < m′ < ∞` (finiteness from `b m′ ≤ C`); `window_lock_toReal`: `0 < m′.toReal`, the lock clause of `ZeroFluxReadsMass` (`window_lock` gives that of `CoarseReadsFine`; `LongChainRead` has no lock
clause, its clauses being vacuous at `m′ = 0`); `window_towerLock`: along every `βs → ∞` (on a measured tower this is already given by the band),
  eventually `0 < mUG (SU N) (βs k) < ∞`. `window_rate`: in measured units the block rate obeys
  `−log θ ≤ b m′ ≤ C`, so the Prop forces `−log θ ≤ C`.
* The pair piece at block scale. `blockCov_window`, `pairDecay_window`, `window_pairDecay`: eventually in `β`,
  for every flow whose step range is at most `b`, the pinned block reading `blockRead W k b` has
  `PairDecay (periodicState hN β) (blockRead W k b) (windowQ K θ) θ`, `windowQ K θ = 5000 K θ^{−5}`: rate `θ` per
  block, constant independent of `b`. The strong witness `strongQ b ρ` grows like `2^{2b}` in lattice units;
  this one does not.

### What it does not give (argued)

* (b) None of the three reads. `CoarseReadsFine`, `LongChainRead`, `ZeroFluxReadsMass` `CoarseReadsFine` and `ZeroFluxReadsMass` are a lock clause (given, `window_lock`) plus, and `LongChainRead` is only,
a clause on the transfer of the rectangular tori at aperture `Tr n i`: relay flux
  odds (twisted partition-function ratios), the zero-flux eigenpair and remainder norm of `K₀`, and the excited
  zero-flux weight. Those quantities are expectations of observables that wrap the torus: a twist is
  `exp(−β ΔS_g)` over a full transverse plane, a slice function reads a whole time slice. Box conditioning
  reaches a torus state only through `torusState_dlr`, which needs reduction modulo the extent to be injective on the test support, the box and its boundary (for a
centred box of radius `R`, `2(R + 1) < M + 1` suffices); a wrapping observable is local in no such box. The bound
  of `KernelDecayAt` also carries the prefactor `min(|A|, 4(2σ+1)⁴)`, which for a slice of aperture `n` is of
  order `(n/b)⁴`, extensive in the aperture.
* (c) Which and why. Not given: the flux-odds clause of `CoarseReadsFine` (a ratio across apertures `2T`, `T` of
  wrapping traces), the exponential odds clause of `LongChainRead` (same), the gap and anchor clauses of
  `ZeroFluxReadsMass` (a finite-volume spectral statement on slice functions). The sector route
  (`sectors_of_path`) is the one proved path from a contraction to torus sector bounds, and it needs the
  contraction at lattice scale at every coupling in `[0, β]` (`defectW` is an integral over the coupling), which
  a statement at one `β → ∞` does not supply. Not given either: `m′ → 0`, the band `c a_k ≤ m′ ≤ 2c a_k`,
  `MeasSweepG`. Every consequence above is pointwise in `β`, and a contraction is a lower bound on decay, so it
  bounds `m′` from below only; the strong point `|β| ≤ 2^{-16}` meets the kernel clause at `b = 1`
  (`kernelDecayAt_strong`) with `m′` fixed in lattice units.

### The block-to-fine bridge (stated)

`KernelDecayAt` is a statement about the fine specification with depth counted in blocks, so its tests are
fine local observables and the fine reads (`siteEnergy`, `tensorEnergy`) are tests of it directly
(`siteEnergy_local`, `tensorEnergy_local`: reach `1`). No read needs to be a function of block variables. A
contraction stated on the blocked measure through the scalar block reading (`ObserverBlockReading.ObsRegimeUnif`,
`PairDecay` of `blockRead`) would not reach `m′`: `tensorEnergy x` is not a function of the block energies
(argued: the block energy is the mean over all six planes, so it does not see the exchange of the planes `(0,1)`
and `(2,3)`, under which the tensor reading changes sign), and the three reads are not functions of any local
reading.
In the other direction the fine form gives the block-reading pair piece (`pairDecay_window`).

## 5. Tests of `WindowContraction`

1. Vacuity: constants fixed before the block set (proved). `kernelNear_one`: every bounded test meets
   `KernelNear` at `δ = 1` in every box at every `β`. `clause_of_K_after_box`: with `K` chosen after the
   centre, depths and test set, every clause of `KernelDecayAt` holds at every `β`, the analogue of
   `ObserverBlockReading.obsRegimeW_of_bounded`. The Prop quantifies `K`, `θ` before `∀ c σ ρ A X`, so this
   witness is not available.
2. Asked at measured geometry; the tests are all bounded fine observables (proved where named). `clause_depth_zero`: at zero block depth (`ρ = σ`) every
   clause holds at every `β` and every `b` (`K ≥ 1` makes the bound at least `1` for a nonempty test set). A
   clause has content only at depth `ρ − σ ≥ 1` block, at least `b` lattice units with `b ≤ C/m′`, and only once
   `K min(|A|, 4(2σ+1)⁴) θ^{ρ−σ} < 1`. The single-link
   condition (depth `1` lattice unit, `b = 1`) is the instance the Prop does not ask at weak coupling: it asks
   some `b ≤ C/m′`, and the single-link coefficient tends to `1` as `β → ∞` (`StrongKernelNear` §4).
3. Free fields (argued). Massless: boundary influence on a box kernel decays by a power of the depth, so no
   `θ < 1` fixed before the depth exists, and `tensorLock_of_scale` would give `m′ > 0`, which is false; the Prop
   fails, as it must. Massive Gaussian: with blocks of side `b ≫ 1/m` the influence per block is `≈ e^{−m b}`, but
   the sup over boundary conditions is infinite for unbounded spins (the conditional mean is linear in the
   boundary field), so the uniform form holds only for compact spins; the compact gauge group makes the sup
   finite here. The test discriminates the massless case and shows the uniform-in-boundary form is specific to
   compact fields.
4. Restatement against reduction. It is a reduction for the lock and the block pair piece (both proved
   consequences, and neither implies it: a decay of the state's correlations does not give boundary
   independence of every box kernel, as at a phase-coexistence point; argued). It is not a reduction of any of
   the three reads (§4). The nearest object in the tree is `ScaleControl.BlockContract` (`SU(2)`): one
   observable at one box, a block Dobrushin operator of row sum `α` applied `m` times, giving
   `KernelNear Δ X (B αᵐ V D)` (`kernelNear_of_blockContract`) with `B` the block count of the box. Read at every
   box with `m = ρ − σ`, it would give a clause of this form with a prefactor growing like the box's block count
   (`ρ⁴`); `KernelDecayAt` has a prefactor in the test region only (`σ`), as the single-link sweep has
   (`StrongKernelNear`, prefactor `|A|`). The uniform family over centres, depths and tests is not stated
   elsewhere.
5. Satisfiability (open; argued escape). No instance of the whole Prop is built: at strong coupling the kernel
   clause holds at `(b, K, θ) = (1, 1, 1/2)` (`kernelDecayAt_strong`), but `m′ < ∞` is not proved there, and the Prop
   is asked only as `β → ∞`. `KernelDecayAt` ranges over all bounded tests, a total-variation statement, and
   `StrongKernelNear` §4 and `BlockDobrushin` §3 item 3 argue that total variation fails at fixed lattice block
   side as `β → ∞`. The Prop escapes that reading only because `b` grows with `1/m′` and every test sits at least
   one block deep (argued).
6. Degenerate cases. `m′ = ⊤` is excluded by `b m′ ≤ C` with `b ≥ 1`; `m′ = 0` is excluded by the conclusion of
   `window_lock`. `θ = 1` is excluded (`θ < 1`); `b = 0` is excluded (`1 ≤ b`).

## 6. Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: the statements of §4 marked argued (why the three reads, `m′ → 0` and the band do not follow; the
  plane-swap witness for the bridge), and the free-field and phase-coexistence readings of §5.
* Assumed: `WindowContraction hN`, only in the theorems named `window_*`.

## 7. Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | `KernelDecayAt`, the states | shared, in the substrate; `WindowContraction` is read along `β → ∞` |
| `b` (block side) | `KernelDecayAt`, `WindowContraction` | existential, at most `C/m′`: measured |
| `K`, `θ` | `KernelDecayAt` | constants of the contraction; in `WindowContraction` fixed before `β` and every box |
| `C` | `WindowContraction` | existential, in measured lengths (`b m′ ≤ C`) |
| `c`, `σ`, `ρ`, `A`, `X` | `KernelDecayAt` | swept over all; `σ`, `ρ` in blocks |
| `R`, `s`, `r`, `M`, `M′`, `n` | the torus consumers | swept; lattice units, at `b = 1` |
| `W`, `k`, `ρ` (flow, step, range) | the pair consumers | chosen by the observer; range `≤ b` in the window |
| `m′` | `WindowContraction`, the lock theorems | measured: `measMassOf (periodicState hN β) tensorEnergy` |
| `N` | the type | shared with the substrate |

DERIVED (module-wide): `1`, `2` the lattice block side, the range of the plaquette density and the two sides of a
constant; `4` the dimension and the directions of `cbox`; `2σ + 1` the sites of `[−σ, σ]`; `64`, `65536 = 2^{16}`,
`1/2` the row-sum count, the strong threshold and its rate (`StrongKernelNear`); `3`, `5` the least side with
`1 ≤ ⌊(n − 3)/2⌋`; `16`, `128 = 16 · 8`, `64 = 2 · 32` the planes and the bound of `bareRead`; `8 = 2 · 4` the
kernel bound's `2` times the directions; `2500 = 4 · 5⁴` the test region of a block reading at range `≤ b`
(`σ = 2`); `5000 = 2 · 2500`; `5 = σ + 3` the least separating block distance; `1024`, `32768` from `strongBound`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ContractionReads

open Filter Topology
open scoped ENNReal NNReal
open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.FocusZoom (stateCov)
open MassGap.SUN (SU)
open MassGap.ContinuumSchwinger (Cfg)
open MassGap.ContinuumFlow (ConfFlow)
open MassGap.ObserverEnergyMoments (plaqField)
open MassGap.StrongKernelNear (IsLocalOn nbr c0 row_le_quarter kernelNear_strong)
open MassGap.StrongFiniteSize (snorm snorm_le_iff ilinks_base box mem_box box_coord bplaq_coord
  bdLinks_coord linkMod_injOn plaqMod_injOn plaqDev plaqDev_apply abs_bareRead_le exp_half_le strongBound)
open MassGap.StrongLocalFiniteSize (HasReach card_box)
open MassGap.PeriodicState (periodicState torusState)
open MassGap.PeriodicStateDLR (wspec torusState_dlr)
open MassGap.BoxFocusTest (KernelNear cov_le_of_near_const cov_le_of_kernelNear)
open MassGap.ObserverBlockReading (cbox mem_cbox card_cbox snorm_sub_nbr snorm_tri stateCov_affine
  stateCov_sub_const_right blockRead blockEnergy blockEnergy_mem blockRead_local not_mem_cbox_of_sep
  PairDecay strongQ plaqField_apply)
open MassGap.SubstrateDecode (DecaysAt measMassOf measMass siteEnergy siteEnergy_apply tensorEnergy
  le_measMassOf)
open MassGap.ObserverFlowSeed (bareRead bareDelta)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two)

variable {N : ℕ}

/-! ## 1. The carrier -/

/-- **The contraction at block side `b`**: the box kernel of the fine Wilson specification forgets its boundary
at rate `θ` per block of depth, with prefactor `K` times the test's link count capped at the block count of its
region. DERIVED: `1` the least prefactor; `4` the directions; `2σ + 1` the blocks of `[−σ, σ]`. -/
def KernelDecayAt (hN : N ≠ 0) (β : ℝ) (b : ℕ) (K θ : ℝ) : Prop :=
  1 ≤ K ∧ 0 < θ ∧ θ ≤ 1 ∧
    ∀ (c : ISite) (σ ρ : ℕ) (A : Finset ILink), σ ≤ ρ → (∀ l ∈ A, snorm (l.2 - c) ≤ b * σ) →
      ∀ X : C(Cfg N, ℝ), (∀ ω, |X ω| ≤ 1) → IsLocalOn A ⇑X →
        KernelNear hN β (cbox c (b * ρ)) X
          (K * min (A.card : ℝ) (4 * (2 * (σ : ℝ) + 1) ^ 4) * θ ^ (ρ - σ))

/-- DERIVED: no numeral. -/
theorem kernelNear_mono {hN : N ≠ 0} {β : ℝ} {Δ : Finset ILink} {X : C(Cfg N, ℝ)} {δ δ' : ℝ}
    (h : KernelNear hN β Δ X δ) (hδ : δ ≤ δ') : KernelNear hN β Δ X δ' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun ω => (hc ω).trans hδ⟩

/-- **The Dobrushin row gives the carrier at the lattice scale.** `64 · c0 β < θ ≤ 1`, `2θ ≤ K`, `1 ≤ K`.
DERIVED: `64` the row-sum count; `2` the kernel bound's two sides; `1` the lattice block and the depth offset. -/
theorem kernelDecayAt_of_row (hN : N ≠ 0) {β θ K : ℝ} (hθ1 : θ ≤ 1) (hrow : 64 * c0 β < θ)
    (hK1 : 1 ≤ K) (hK : 2 * θ ≤ K) : KernelDecayAt hN β 1 K θ := by
  have hθ0 : 0 < θ :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) (MassGap.StrongKernelNear.c0_nonneg β)) hrow
  refine ⟨hK1, hθ0, hθ1, fun c σ ρ A hσρ hA X hX1 hXloc => ?_⟩
  simp only [one_mul] at hA ⊢
  have hAΔ : A ⊆ cbox c ρ := fun l hl => mem_cbox.mpr ((hA l hl).trans hσρ)
  have hKN := kernelNear_strong hN β (cbox c ρ) A hAΔ X hX1 hXloc hθ0 hθ1 hrow
    (fun l => ρ + 1 - snorm (l.2 - c))
    (fun l hl => by
      have := mt mem_cbox.mpr hl
      show ρ + 1 - snorm (l.2 - c) = 0
      omega)
    (fun i _ j hj => by
      have := snorm_sub_nbr c hj
      show ρ + 1 - snorm (i.2 - c) ≤ ρ + 1 - snorm (j.2 - c) + 1
      omega)
  refine kernelNear_mono hKN ?_
  have hs : ∑ l ∈ A, θ ^ (ρ + 1 - snorm (l.2 - c)) ≤ A.card * θ ^ (ρ + 1 - σ) := by
    calc ∑ l ∈ A, θ ^ (ρ + 1 - snorm (l.2 - c)) ≤ ∑ _l ∈ A, θ ^ (ρ + 1 - σ) :=
          Finset.sum_le_sum fun l hl =>
            pow_le_pow_of_le_one hθ0.le hθ1 (by have := hA l hl; omega)
      _ = A.card * θ ^ (ρ + 1 - σ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (A.card : ℝ) ≤ 4 * (2 * (σ : ℝ) + 1) ^ 4 := by
    have h1 : A.card ≤ (cbox c σ).card := Finset.card_le_card fun l hl => mem_cbox.mpr (hA l hl)
    rw [card_cbox] at h1
    exact_mod_cast h1
  rw [min_eq_left hcard]
  have e : ρ + 1 - σ = (ρ - σ) + 1 := by omega
  calc 2 * ∑ l ∈ A, θ ^ (ρ + 1 - snorm (l.2 - c)) ≤ 2 * (A.card * θ ^ (ρ + 1 - σ)) := by linarith
    _ = (2 * θ) * A.card * θ ^ (ρ - σ) := by rw [e, pow_succ]; ring
    _ ≤ K * A.card * θ ^ (ρ - σ) := by gcongr

/-- **The strong-coupling instance**: `|β| ≤ 2^{-16}` gives the carrier at `b = 1`, `K = 1`, `θ = 1/2`.
DERIVED: `65536 = 2^{16}`; `1/2` the rate; `1` the lattice block and the prefactor. -/
theorem kernelDecayAt_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) :
    KernelDecayAt hN β 1 1 (1 / 2) :=
  kernelDecayAt_of_row hN (by norm_num) (by linarith [row_le_quarter hβ]) le_rfl (by norm_num)

/-! ### Vacuity witnesses -/

/-- A box kernel of a test bounded by `1` is bounded by `1`. DERIVED: `1` the bound; `2` the range of the
density. -/
theorem abs_wspec_le (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X : C(Cfg N, ℝ))
    (hX1 : ∀ ω, |X ω| ≤ 1) (ω : Cfg N) : |wspec hN β Λ X ω| ≤ 1 := by
  rw [MassGap.PeriodicStateDLR.wspec_apply]
  exact abs_spec_le MassGap.WilsonAction.measurable_wilsonDensity (wilsonDensity_nonneg hN)
    (wilsonDensity_le_two hN) β Λ (MassGap.CompactGauge.probHaar (SU N)) X.continuous.measurable hX1 ω

/-- **Every bounded test meets `KernelNear` at `δ = 1`**, in every box at every coupling. DERIVED: `0` the
constant; `1` the bound. -/
theorem kernelNear_one (hN : N ≠ 0) (β : ℝ) (Λ : Finset ILink) (X : C(Cfg N, ℝ))
    (hX1 : ∀ ω, |X ω| ≤ 1) : KernelNear hN β Λ X 1 :=
  ⟨0, fun ω => by rw [sub_zero]; exact abs_wspec_le hN β Λ X hX1 ω⟩

/-- **With `K` chosen after the box every clause holds**, at every coupling: the constants of the carrier must
be fixed before the centre, the depths and the test set. DERIVED: `1` the least prefactor. -/
theorem clause_of_K_after_box (hN : N ≠ 0) (β : ℝ) (b : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (c : ISite)
    (σ ρ : ℕ) (A : Finset ILink) (hA : A.Nonempty) (X : C(Cfg N, ℝ)) (hX1 : ∀ ω, |X ω| ≤ 1) :
    ∃ K : ℝ, 1 ≤ K ∧ KernelNear hN β (cbox c (b * ρ)) X
      (K * min (A.card : ℝ) (4 * (2 * (σ : ℝ) + 1) ^ 4) * θ ^ (ρ - σ)) := by
  set q := min (A.card : ℝ) (4 * (2 * (σ : ℝ) + 1) ^ 4) * θ ^ (ρ - σ) with hq
  have hq0 : 0 < q := by
    have h1 : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
    exact mul_pos (lt_min h1 (by positivity)) (pow_pos hθ0 _)
  refine ⟨max 1 q⁻¹, le_max_left _ _, kernelNear_mono (kernelNear_one hN β _ X hX1) ?_⟩
  rw [mul_assoc, ← hq]
  calc (1 : ℝ) = q⁻¹ * q := (inv_mul_cancel₀ hq0.ne').symm
    _ ≤ max 1 q⁻¹ * q := mul_le_mul_of_nonneg_right (le_max_right _ _) hq0.le

/-- **At zero block depth every clause holds**, at every coupling and every block side: the carrier asks
nothing of a box with no margin. DERIVED: `1` the least prefactor and the least count; `4`, `2σ + 1`. -/
theorem clause_depth_zero (hN : N ≠ 0) (β : ℝ) (b : ℕ) {K θ : ℝ} (hK1 : 1 ≤ K) (c : ISite) (σ : ℕ)
    (A : Finset ILink) (hA : A.Nonempty) (X : C(Cfg N, ℝ)) (hX1 : ∀ ω, |X ω| ≤ 1) :
    KernelNear hN β (cbox c (b * σ)) X
      (K * min (A.card : ℝ) (4 * (2 * (σ : ℝ) + 1) ^ 4) * θ ^ (σ - σ)) := by
  refine kernelNear_mono (kernelNear_one hN β _ X hX1) ?_
  rw [Nat.sub_self, pow_zero, mul_one]
  have h1 : (1 : ℝ) ≤ A.card := Nat.one_le_cast.mpr hA.card_pos
  have h2 : (1 : ℝ) ≤ 4 * (2 * (σ : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ (2 * (σ : ℝ) + 1) ^ 4 :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg σ : (0 : ℝ) ≤ σ)])
    linarith
  calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ K * min (A.card : ℝ) (4 * (2 * (σ : ℝ) + 1) ^ 4) :=
        mul_le_mul hK1 (le_min h1 h2) zero_le_one (by linarith)

/-! ## 2. Separated covariance -/

/-- **Separated covariance from the contraction**, at any block side. `F` local on `A` within `b σ` of `c` and
within `BF` of a constant; `H` not reading `cbox c (b ρ)` and within `BH` of a constant.
DERIVED: `2` the kernel bound's two sides. -/
theorem cov_sep_of {hN : N ≠ 0} {β : ℝ} {b : ℕ} {K θ : ℝ} (hK : KernelDecayAt hN β b K θ) (c : ISite)
    {σ ρ : ℕ} (hσρ : σ ≤ ρ) (A : Finset ILink) (hA : ∀ l ∈ A, snorm (l.2 - c) ≤ b * σ)
    (F H : C(Cfg N, ℝ)) {a a' BF BH : ℝ} (hBF : 0 ≤ BF) (hFloc : IsLocalOn A ⇑F)
    (hFb : ∀ U, |F U - a| ≤ BF)
    (hHoff : ∀ (u : VConf (SU N) (cbox c (b * ρ))) (ω : Cfg N),
      H (splice (cbox c (b * ρ)) u ω) = H ω)
    (hHb : ∀ U, |H U - a'| ≤ BH) :
    |stateCov (periodicState hN β) F H|
      ≤ 2 * (K * min (A.card : ℝ) (4 * (2 * (σ : ℝ) + 1) ^ 4) * θ ^ (ρ - σ)) * BF * BH := by
  set H' : C(Cfg N, ℝ) := H - a' • (1 : C(Cfg N, ℝ)) with hH'
  have hH'v : ∀ U, H' U = H U - a' := fun U => by simp [hH']
  have hH'b : ∀ U, |H' U| ≤ BH := fun U => by rw [hH'v]; exact hHb U
  have hcovH : stateCov (periodicState hN β) F H' = stateCov (periodicState hN β) F H :=
    stateCov_sub_const_right _ F H a'
  rcases eq_or_lt_of_le hBF with h0 | hpos
  · subst h0
    have hc := cov_le_of_near_const (periodicState hN β) F H' (c := a) (δ := 0) hFb hH'b
    rw [hcovH, mul_zero] at hc
    exact hc.trans (le_of_eq (by ring))
  · set X : C(Cfg N, ℝ) := BF⁻¹ • (F - a • (1 : C(Cfg N, ℝ))) with hX
    have hXv : ∀ U, X U = BF⁻¹ * (F U - a) := fun U => by simp [hX]
    have hX1 : ∀ U, |X U| ≤ 1 := fun U => by
      rw [hXv, abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos, mul_one]
      exact hFb U
    have hXloc : IsLocalOn A ⇑X := fun η η' h => by rw [hXv, hXv, hFloc η η' h]
    have hKN := hK.2.2.2 c σ ρ A hσρ hA X hX1 hXloc
    have hY : ∀ (u : VConf (SU N) (cbox c (b * ρ))) (ω : Cfg N),
        H' (splice (cbox c (b * ρ)) u ω) = H' ω :=
      fun u ω => by rw [hH'v, hH'v, hHoff u ω]
    have hc := cov_le_of_kernelNear hN β (cbox c (b * ρ)) X H' hY hH'b hKN
    have hlin : stateCov (periodicState hN β) X H' = BF⁻¹ * stateCov (periodicState hN β) F H :=
      stateCov_affine _ F H BF⁻¹ a a'
    rw [hlin, abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos] at hc
    calc _ ≤ BF * (2 * BH * (K * min (A.card : ℝ) (4 * (2 * (σ : ℝ) + 1) ^ 4) * θ ^ (ρ - σ))) := hc
      _ = _ := by ring

/-- **`ObserverBlockReading.cov_sep_strong`, recovered.** DERIVED: `4 = 2 · 2`; `65536 = 2^{16}`; `1/2`;
`1` the depth offset. -/
theorem cov_sep_strong_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (c : ISite) {s R : ℕ}
    (hsR : s ≤ R) (F H : C(Cfg N, ℝ)) {a a' BF BH : ℝ} (hBF : 0 ≤ BF)
    (hFloc : IsLocalOn (cbox c s) ⇑F) (hFb : ∀ U, |F U - a| ≤ BF)
    (hHoff : ∀ (u : VConf (SU N) (cbox c R)) (ω : Cfg N), H (splice (cbox c R) u ω) = H ω)
    (hHb : ∀ U, |H U - a'| ≤ BH) :
    |stateCov (periodicState hN β) F H| ≤ 4 * (cbox c s).card * (1 / 2) ^ (R + 1 - s) * BF * BH := by
  have h := cov_sep_of (kernelDecayAt_strong hN hβ) c hsR (cbox c s)
    (fun l hl => by rw [one_mul]; exact mem_cbox.mp hl) F H hBF hFloc hFb
    (by rw [one_mul]; exact hHoff) hHb
  have hc : ((cbox c s).card : ℝ) = 4 * (2 * (s : ℝ) + 1) ^ 4 := by rw [card_cbox]; push_cast; ring
  rw [hc, min_self] at h
  have e : R + 1 - s = (R - s) + 1 := by omega
  rw [hc, e, pow_succ (1 / 2 : ℝ) (R - s)]
  calc _ ≤ _ := h
    _ = _ := by ring

/-! ## 3. Finite size -/

/-- DERIVED: `0` the origin. -/
theorem cbox_zero (R : ℕ) : cbox 0 R = box R := by
  ext l
  rw [mem_cbox, mem_box, sub_zero]

/-- **Two tori read a local observable alike, from the contraction.** DERIVED: `2` the two tori; `1` the
lattice block. -/
theorem torusState_sub_le_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) {R s M M' : ℕ}
    (F : C(Cfg N, ℝ)) (A : Finset ILink) (hF1 : ∀ ω, |F ω| ≤ 1) (hloc : IsLocalOn A ⇑F)
    (hA : ∀ l ∈ A, snorm l.2 ≤ s) (hsR : s ≤ R) (hM : 2 * (R + 1) < M + 1)
    (hM' : 2 * (R + 1) < M' + 1) :
    |torusState hN M β F - torusState hN M' β F|
      ≤ 2 * (K * min (A.card : ℝ) (4 * (2 * (s : ℝ) + 1) ^ 4) * θ ^ (R - s)) := by
  have hAΔ : A ⊆ box R := fun l hl => mem_box.mpr ((hA l hl).trans hsR)
  have hKN := hK.2.2.2 0 s R A hsR (fun l hl => by rw [sub_zero, one_mul]; exact hA l hl) F hF1 hloc
  rw [one_mul, cbox_zero] at hKN
  obtain ⟨c, hc⟩ := hKN
  have hδ0 : 0 ≤ K * min (A.card : ℝ) (4 * (2 * (s : ℝ) + 1) ^ 4) * θ ^ (R - s) :=
    mul_nonneg (mul_nonneg (by linarith [hK.1]) (le_min (Nat.cast_nonneg _) (by positivity)))
      (pow_nonneg hK.2.1.le _)
  have key : ∀ M₀ : ℕ, 2 * (R + 1) < M₀ + 1 →
      |torusState hN M₀ β F - c| ≤ K * min (A.card : ℝ) (4 * (2 * (s : ℝ) + 1) ^ 4) * θ ^ (R - s) := by
    intro M₀ hM₀
    have hT : ∀ l ∈ A ∪ box R ∪ MassGap.WilsonDLR.bdLinks (box R), ∀ i,
        -((R + 1 : ℕ) : ℤ) ≤ l.2 i ∧ l.2 i ≤ ((R + 1 : ℕ) : ℤ) := by
      intro l hl i
      push_cast
      rcases Finset.mem_union.mp hl with h | h
      · rcases Finset.mem_union.mp h with h | h
        · have := box_coord (hAΔ h) i
          omega
        · have := box_coord h i
          omega
      · exact bdLinks_coord h i
    have hP : ∀ q ∈ boundaryPlaqs (box R), ∀ i,
        -((R + 1 : ℕ) : ℤ) ≤ q.2 i ∧ q.2 i ≤ ((R + 1 : ℕ) : ℤ) := by
      intro q hq i
      push_cast
      have := bplaq_coord hq i
      omega
    have hdlr := torusState_dlr hN M₀ β (box R) A F (fun U V h => hloc U V h)
      (linkMod_injOn hM₀ hT) (plaqMod_injOn hM₀ hP)
    have hone : torusState hN M₀ β (c • (1 : C(Cfg N, ℝ))) = c := by
      rw [MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_one, mul_one]
    rw [← hdlr]
    calc |torusState hN M₀ β (wspec hN β (box R) F) - c|
        = |torusState hN M₀ β (wspec hN β (box R) F)
            - torusState hN M₀ β (c • (1 : C(Cfg N, ℝ)))| := by rw [hone]
      _ ≤ ‖wspec hN β (box R) F - c • (1 : C(Cfg N, ℝ))‖ :=
          (torusState hN M₀ β).abs_sub_le _ _
      _ ≤ _ :=
          (ContinuousMap.norm_le _ hδ0).mpr fun ω => by
            rw [Real.norm_eq_abs, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
              ContinuousMap.one_apply, smul_eq_mul, mul_one]
            exact hc ω
  have h1 := key M hM
  have h2 := key M' hM'
  have h3 := abs_sub_le (torusState hN M β F) c (torusState hN M' β F)
  rw [abs_sub_comm c] at h3
  linarith

/-- **`StrongFiniteSize.torusState_sub_le`, recovered.** DERIVED: `4 = 2 · 2`; `65536 = 2^{16}`; `1/2`. -/
theorem torusState_sub_le_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {R s M M' : ℕ}
    (F : C(Cfg N, ℝ)) (A : Finset ILink) (hF1 : ∀ ω, |F ω| ≤ 1) (hloc : IsLocalOn A ⇑F)
    (hA : ∀ l ∈ A, snorm l.2 ≤ s) (hsR : s ≤ R) (hM : 2 * (R + 1) < M + 1)
    (hM' : 2 * (R + 1) < M' + 1) :
    |torusState hN M β F - torusState hN M' β F| ≤ 4 * A.card * (1 / 2) ^ (R + 1 - s) := by
  have h := torusState_sub_le_of (kernelDecayAt_strong hN hβ) F A hF1 hloc hA hsR hM hM'
  have hm : min (A.card : ℝ) (4 * (2 * (s : ℝ) + 1) ^ 4) ≤ A.card := min_le_left _ _
  have e : R + 1 - s = (R - s) + 1 := by omega
  have hp : (0 : ℝ) ≤ (1 / 2) ^ (R - s) := by positivity
  rw [e, pow_succ]
  linarith [mul_le_mul_of_nonneg_right hm hp]

/-- **An observable of reach `r`, from the contraction**: `8 K (2r+1)⁴ B θ^{R−r}`. DERIVED: `8 = 2 · 4`, the
two tori and the directions of `box r`. -/
theorem torusState_sub_le_reach_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ)
    {r R M M' : ℕ} {B : ℝ} (F : C(Cfg N, ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F)
    (hrR : r ≤ R) (hM : 2 * (R + 1) < M + 1) (hM' : 2 * (R + 1) < M' + 1) :
    |torusState hN M β F - torusState hN M' β F| ≤ 8 * K * (2 * r + 1) ^ 4 * B * θ ^ (R - r) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB fun _ => 1)
  have hK0 : 0 ≤ K := by linarith [hK.1]
  have hθ0 := hK.2.1
  rcases hB0.eq_or_lt with hB | hB
  · have h1 := MassGap.StrongLocalFiniteSize.abs_torusState_le hN M β F hFB
    have h2 := MassGap.StrongLocalFiniteSize.abs_torusState_le hN M' β F hFB
    have h3 := abs_sub (torusState hN M β F) (torusState hN M' β F)
    rw [← hB] at h1 h2 ⊢
    rw [mul_zero, zero_mul]
    linarith
  · set G : C(Cfg N, ℝ) := B⁻¹ • F with hG
    have hG1 : ∀ ω, |G ω| ≤ 1 := fun ω => by
      rw [hG, ContinuousMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hB)]
      calc B⁻¹ * |F ω| ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hFB ω) (inv_pos.mpr hB).le
        _ = 1 := inv_mul_cancel₀ hB.ne'
    have hGloc : IsLocalOn (box r) ⇑G := fun η η' h => by
      show B⁻¹ * F η = B⁻¹ * F η'
      rw [hF η η' h]
    have h := torusState_sub_le_of hK G (box r) hG1 hGloc (fun l hl => mem_box.mp hl) hrR hM hM'
    rw [hG, MassGap.DLRLimit.State.map_smul, MassGap.DLRLimit.State.map_smul, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hB)] at h
    have hmin : min ((box r).card : ℝ) (4 * (2 * (r : ℝ) + 1) ^ 4) ≤ 4 * (2 * (r : ℝ) + 1) ^ 4 :=
      min_le_right _ _
    calc |torusState hN M β F - torusState hN M' β F|
        = B * (B⁻¹ * |torusState hN M β F - torusState hN M' β F|) := by
          rw [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
      _ ≤ B * (2 * (K * min ((box r).card : ℝ) (4 * (2 * (r : ℝ) + 1) ^ 4) * θ ^ (R - r))) :=
          mul_le_mul_of_nonneg_left h hB.le
      _ ≤ B * (2 * (K * (4 * (2 * (r : ℝ) + 1) ^ 4) * θ ^ (R - r))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin hK0) (pow_nonneg hθ0.le _)) (by norm_num)) hB.le
      _ = 8 * K * (2 * r + 1) ^ 4 * B * θ ^ (R - r) := by ring

/-- **`StrongLocalFiniteSize.torusState_sub_le_reach`, recovered.** DERIVED: `16 = 8 · 2`; `65536 = 2^{16}`;
`1/2`. -/
theorem torusState_sub_le_reach_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {r R M M' : ℕ} {B : ℝ}
    (F : C(Cfg N, ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) (hrR : r ≤ R)
    (hM : 2 * (R + 1) < M + 1) (hM' : 2 * (R + 1) < M' + 1) :
    |torusState hN M β F - torusState hN M' β F| ≤ 16 * (2 * r + 1) ^ 4 * B * (1 / 2) ^ (R + 1 - r) := by
  have h := torusState_sub_le_reach_of (kernelDecayAt_strong hN hβ) F hFB hF hrR hM hM'
  have e : R + 1 - r = (R - r) + 1 := by omega
  rw [e, pow_succ (1 / 2 : ℝ) (R - r)]
  linarith

/-- **The doubling change of an observable of reach `r`, from the contraction**, at `n ≥ 2r + 5`.
DERIVED: `3`, `5` the least side with `1 ≤ ⌊(n − 3)/2⌋`; `2` the doubling. -/
theorem doubling_sub_le_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) (r n : ℕ)
    (hn : 2 * r + 5 ≤ n) {B : ℝ} (F : C(Cfg N, ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) :
    |torusState hN (2 * n - 1) β F - torusState hN (n - 1) β F|
      ≤ 8 * K * (2 * r + 1) ^ 4 * B * θ ^ ((n - 3) / 2 - r) :=
  torusState_sub_le_reach_of hK F hFB hF (by omega) (by omega) (by omega)

/-- **At `θ < 1` the doubling change tends to `0`.** DERIVED: `3`, `5`, `2` as above. -/
theorem tendsto_doubling_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) (hθ1 : θ < 1)
    (r : ℕ) {B : ℝ} (F : C(Cfg N, ℝ)) (hFB : ∀ ω, |F ω| ≤ B) (hF : HasReach r ⇑F) :
    Tendsto (fun n : ℕ => torusState hN (2 * n - 1) β F - torusState hN (n - 1) β F) atTop (𝓝 0) := by
  have hf : Tendsto (fun n : ℕ => (n - 3) / 2 - r) atTop atTop :=
    tendsto_atTop_atTop.mpr fun m => ⟨2 * (m + r) + 3, fun n hn => by omega⟩
  have hg := ((tendsto_pow_atTop_nhds_zero_of_lt_one hK.2.1.le hθ1).comp hf).const_mul
    (8 * K * (2 * (r : ℝ) + 1) ^ 4 * B)
  rw [mul_zero] at hg
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop (2 * r + 5)] with n hn
  rw [Real.norm_eq_abs]
  exact doubling_sub_le_of hK r n hn F hFB hF

/-- **The plaquette density, from the contraction**: `8 K θ^{R−1}`. DERIVED: `8 = 2 · 4`, the two tori and the
links of a plaquette; `1` the plaquette's sup-radius. -/
theorem plaq_sub_le_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) {R M M' : ℕ}
    (hR : 1 ≤ R) (hM : 2 * (R + 1) < M + 1) (hM' : 2 * (R + 1) < M' + 1) (p : Fin 4 × Fin 4) :
    |torusState hN M β (plaqField (N := N) (p, 0)).1 - torusState hN M' β (plaqField (N := N) (p, 0)).1|
      ≤ 8 * K * θ ^ (R - 1) := by
  have hF1 : ∀ ω, |plaqDev (N := N) p ω| ≤ 1 := fun ω => by
    rw [plaqDev_apply]
    have h0 := wilsonDensity_nonneg hN (ihol (p, 0) ω)
    have h2 := wilsonDensity_le_two hN (ihol (p, 0) ω)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hloc : IsLocalOn (ilinks (p, (0 : ISite))).toFinset ⇑(plaqDev (N := N) p) := fun η η' h => by
    rw [plaqDev_apply, plaqDev_apply,
      ihol_congr (p, 0) η η' (fun l hl => h l (List.mem_toFinset.mpr hl))]
  have hA : ∀ l ∈ (ilinks (p, (0 : ISite))).toFinset, snorm l.2 ≤ 1 := fun l hl => by
    rw [snorm_le_iff]
    intro i
    have := ilinks_base (List.mem_toFinset.mp hl) i
    dsimp only [Pi.zero_apply] at this
    push_cast
    omega
  have hcard : ((ilinks (p, (0 : ISite))).toFinset.card : ℝ) ≤ 4 := by
    have : (ilinks (p, (0 : ISite))).toFinset.card ≤ 4 := (List.toFinset_card_le _).trans le_rfl
    exact_mod_cast this
  have h := torusState_sub_le_of hK (plaqDev (N := N) p) _ hF1 hloc hA hR hM hM'
  rw [plaqDev, MassGap.DLRLimit.State.map_sub, MassGap.DLRLimit.State.map_sub,
    MassGap.DLRLimit.State.map_one, MassGap.DLRLimit.State.map_one] at h
  have he : ∀ a b : ℝ, a - 1 - (b - 1) = a - b := fun a b => by ring
  rw [he] at h
  have hK0 : 0 ≤ K := by linarith [hK.1]
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((min_le_left _ (4 * (2 * ((1 : ℕ) : ℝ) + 1) ^ 4)).trans hcard) hK0)
    (pow_nonneg hK.2.1.le (R - 1))
  refine h.trans ?_
  linarith [hm]

/-- **The doubling change of the torus energy reading, from the contraction**: `128 K θ^{R−1}`.
DERIVED: `128 = 16 · 8`, the ordered planes. -/
theorem bareRead_sub_le_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) {n R : ℕ}
    (hR : 1 ≤ R) (hn : 2 * (R + 1) < n) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ 128 * K * θ ^ (R - 1) := by
  unfold bareRead
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ p : Fin 4 × Fin 4, |torusState hN (2 * n - 1) β (plaqField (N := N) (p, 0)).1
          - torusState hN (n - 1) β (plaqField (N := N) (p, 0)).1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin 4 × Fin 4, 8 * K * θ ^ (R - 1) :=
        Finset.sum_le_sum fun p _ => plaq_sub_le_of hK hR (by omega) (by omega) p
    _ = 128 * K * θ ^ (R - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **`StrongFiniteSize.bareRead_sub_le`, recovered.** DERIVED: `256 = 128 · 2`; `65536 = 2^{16}`; `1/2`. -/
theorem bareRead_sub_le_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) {n R : ℕ} (hR : 1 ≤ R)
    (hn : 2 * (R + 1) < n) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ 256 * (1 / 2) ^ R := by
  have h := bareRead_sub_le_of (kernelDecayAt_strong hN hβ) hR hn
  have hp : (1 / 2 : ℝ) ^ R = (1 / 2) ^ (R - 1) * (1 / 2) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  linarith

/-- The doubling bound: `128 K θ^{⌊(n−3)/2⌋ − 1}` at `n ≥ 5`, the trivial `64` below.
DERIVED: `128` from `bareRead_sub_le_of`; `3`, `5` the least side with `1 ≤ ⌊(n−3)/2⌋`; `64 = 2 · 32`. -/
def doubleBound (K θ : ℝ) (n : ℕ) : ℝ := if 5 ≤ n then 128 * K * θ ^ ((n - 3) / 2 - 1) else 64

/-- The integrand bound of the defect. DERIVED: `16 = 2⁴`; `4` the dimension. -/
def pathBound (K θ : ℝ) (n : ℕ) : ℝ := 16 * (n : ℝ) ^ 4 * doubleBound K θ n

/-- DERIVED: `0`. -/
theorem doubleBound_nonneg {K θ : ℝ} (hK : 0 ≤ K) (hθ : 0 ≤ θ) (n : ℕ) : 0 ≤ doubleBound K θ n := by
  unfold doubleBound
  split_ifs
  · exact mul_nonneg (mul_nonneg (by norm_num) hK) (pow_nonneg hθ _)
  · norm_num

/-- **The doubling change at every side, from the contraction.** DERIVED: as `doubleBound`. -/
theorem bareRead_doubling_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) (n : ℕ) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ doubleBound K θ n := by
  unfold doubleBound
  split_ifs with hn
  · exact bareRead_sub_le_of hK (R := (n - 3) / 2) (by omega) (by omega)
  · have ha := abs_bareRead_le hN (2 * n) β
    have hb := abs_bareRead_le hN n β
    have hab := abs_sub (bareRead hN (2 * n) β) (bareRead hN n β)
    linarith

/-- **The strong doubling bound is below `1024 e^{−(log 2/2) n}`.** DERIVED: `1024 = 128 · 8`; `3`, `2` the
shifts of `exp_half_le`; `64 ≤ 1024/4`. -/
theorem doubleBound_strong_le (n : ℕ) :
    doubleBound 1 (1 / 2) n ≤ 1024 * Real.exp (-(Real.log 2 / 2) * n) := by
  have hE : 0 < Real.exp (Real.log 2 / 2 * n) := Real.exp_pos _
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  unfold doubleBound
  split_ifs with hn
  · obtain ⟨j, hj⟩ : ∃ j, (n - 3) / 2 - 1 = j := ⟨_, rfl⟩
    rw [hj]
    have h2 := exp_half_le (n := n) (k := j + 3) (by omega)
    have h3 : (128 : ℝ) * 1 * (1 / 2) ^ j = 1024 / 2 ^ (j + 3) := by
      rw [one_div_pow, pow_add]
      field_simp
      norm_num
    rw [h3]
    exact div_le_div_of_nonneg_left (by norm_num) hE h2
  · have h2 := exp_half_le (n := n) (k := 2) (by omega)
    calc (64 : ℝ) ≤ 1024 / 2 ^ 2 := by norm_num
      _ ≤ 1024 / Real.exp (Real.log 2 / 2 * n) := div_le_div_of_nonneg_left (by norm_num) hE h2

/-- **`StrongFiniteSize.finiteSize_decay_strong`, recovered.** DERIVED: `65536 = 2^{16}`; `1024`. -/
theorem finiteSize_decay_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (n : ℕ) :
    |bareRead hN (2 * n) β - bareRead hN n β| ≤ 1024 * Real.exp (-(Real.log 2 / 2) * n) :=
  (bareRead_doubling_of (kernelDecayAt_strong hN hβ) n).trans (doubleBound_strong_le n)

/-- DERIVED: `16`, `4` as in `strongBound`. -/
theorem pathBound_strong_le (n : ℕ) : pathBound 1 (1 / 2) n ≤ strongBound n := by
  unfold pathBound strongBound
  exact mul_le_mul_of_nonneg_left (doubleBound_strong_le n) (by positivity)

/-- **The integrand of the defect, from the contraction at one coupling.** DERIVED: `16`, `4`. -/
theorem abs_bareDelta_le_of {hN : N ≠ 0} {x K θ : ℝ} (hK : KernelDecayAt hN x 1 K θ) (n : ℕ) :
    |bareDelta hN n x| ≤ pathBound K θ n := by
  unfold bareDelta pathBound
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 4)]
  exact mul_le_mul_of_nonneg_left (bareRead_doubling_of hK n) (by positivity)

/-- **The torus defect from the contraction along the coupling path `[0, β]`.** `defectW` is an integral over
the coupling, so the contraction is asked at every `x ∈ [0, β]` with one `K`, `θ`. DERIVED: `0` the lower
coupling. -/
theorem abs_defectW_le_of_path (hN : N ≠ 0) {K θ β : ℝ} {n : ℕ} (hn : n ≠ 0) (hβ0 : 0 ≤ β)
    (hpath : ∀ x : ℝ, 0 ≤ x → x ≤ β → KernelDecayAt hN x 1 K θ) :
    |MassGap.ZoomSelfScale.defectW N β n| ≤ β * pathBound K θ n := by
  rw [← MassGap.FlowComp.integral_bareDelta hN hn β]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := β)
    (f := fun x => bareDelta hN n x) (C := pathBound K θ n) (fun x hx => by
      rw [Set.uIoc_of_le hβ0] at hx
      rw [Real.norm_eq_abs]
      exact abs_bareDelta_le_of (hpath x hx.1.le hx.2) n)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hβ0] at h
  linarith

/-! ## 4. The sector bounds -/

section Sectors

variable [NeZero N]

open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN sectors_of_defectWN)

/-- **The sector bounds from the contraction along `[0, β]`.** DERIVED: `4 + N⁶`, `N³/2`, `2` from
`sectors_of_defectWN`; `3` the spatial directions of a time slice, `N³ = |Z_N³|`; `6 = 2 · 3`, `N⁶` the
square of `N³`. -/
theorem sectors_of_path {K θ β : ℝ} (hβ0 : 0 ≤ β)
    (hpath : ∀ x : ℝ, 0 ≤ x → x ≤ β → KernelDecayAt (NeZero.ne N) x 1 K θ) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (hδ : (4 + (N : ℝ) ^ 6) * (β * pathBound K θ n) ≤ 2) (i : Fin 4) :
    fluxShareN N β n i ≤ (N : ℝ) ^ 3 * (β * pathBound K θ n) / 2 ∧
      trivialDefectN N β n i ≤ 2 * (β * pathBound K θ n) := by
  have h0 := hpath 0 le_rfl hβ0
  have hP : 0 ≤ pathBound K θ n :=
    mul_nonneg (by positivity) (doubleBound_nonneg (by linarith [h0.1]) h0.2.1.le n)
  exact sectors_of_defectWN hβ0 hn he (mul_nonneg hβ0 hP) hδ
    ((le_abs_self _).trans (abs_defectW_le_of_path (NeZero.ne N) (by omega) hβ0 hpath)) i

/-- **`SubstrateFluxRead.sectors_strong`, recovered.** DERIVED: `65536 = 2^{16}`; `4 + N⁶`, `N³/2`, `2`;
`3` the spatial directions of a time slice, `N³ = |Z_N³|`; `6 = 2 · 3`, `N⁶` the square of `N³`. -/
theorem sectors_strong_rec {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (hδ : (4 + (N : ℝ) ^ 6) * (β * strongBound n) ≤ 2) (i : Fin 4) :
    fluxShareN N β n i ≤ (N : ℝ) ^ 3 * (β * strongBound n) / 2 ∧
      trivialDefectN N β n i ≤ 2 * (β * strongBound n) := by
  have hpath : ∀ x : ℝ, 0 ≤ x → x ≤ β → KernelDecayAt (NeZero.ne N) x 1 1 (1 / 2) := fun x hx0 hx =>
    kernelDecayAt_strong (NeZero.ne N) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hd := abs_defectW_le_of_path (NeZero.ne N) (n := n) (by omega) hβ0 hpath
  exact sectors_of_defectWN hβ0 hn he (mul_nonneg hβ0 (MassGap.SubstrateFluxRead.strongBound_nonneg n)) hδ
    ((le_abs_self _).trans (hd.trans (mul_le_mul_of_nonneg_left (pathBound_strong_le n) hβ0))) i

end Sectors

/-! ## 5. Pair decay and the lattice-unit lock -/

/-- The pair constant of the contraction: `8 K (2(b + ρ) + 1)⁴ θ^{−(2(b+ρ)+1)}`. DERIVED: `8 = 2 · 4`; `2`, `1`
the read box side and the strict margin. -/
def contQ (K θ : ℝ) (b ρ : ℕ) : ℝ := 8 * K * (2 * ((b : ℝ) + ρ) + 1) ^ 4 * (θ ^ (2 * (b + ρ) + 1))⁻¹

/-- **At the strong instance the pair constant is `strongQ`.** DERIVED: `1/2`, `2`. -/
theorem contQ_strong (b ρ : ℕ) : contQ 1 (1 / 2) b ρ = strongQ b ρ := by
  unfold contQ strongQ
  rw [one_div, inv_pow, inv_inv, pow_succ]
  ring

/-- **Block covariances from the contraction at the lattice scale.** DERIVED: `1` the centre of `[0, 2]` and
the lattice block; `2` the depth shift. -/
theorem blockCov_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) (W : ConfFlow N)
    (k b ρ : ℕ) (hρ : W.range k ≤ ρ) (z z' : ISite) {f h : ℝ → ℝ} {Lf Lh : ℝ} (hLf : 0 ≤ Lf)
    (hLh : 0 ≤ Lh) (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|) (hh : ∀ x y, |h x - h y| ≤ Lh * |x - y|)
    (F H : C(Cfg N, ℝ)) (hF : ∀ U, F U = f (blockRead W k b U z))
    (hH : ∀ U, H U = h (blockRead W k b U z')) :
    |stateCov (periodicState hN β) F H| ≤ contQ K θ b ρ * Lf * Lh * (θ ^ b) ^ snorm (z' - z) := by
  have hK1 := hK.1
  have hK0 : 0 ≤ K := by linarith
  have hθ0 := hK.2.1
  have hθ1 := hK.2.2.1
  have hnear : ∀ (g : ℝ → ℝ) (Lg : ℝ), 0 ≤ Lg → (∀ x y, |g x - g y| ≤ Lg * |x - y|) → ∀ w U,
      |g (blockRead W k b U w) - g 1| ≤ Lg := by
    intro g Lg hLg hg w U
    obtain ⟨h0, h2⟩ := blockEnergy_mem hN b (W.V k U) w
    calc |g (blockRead W k b U w) - g 1| ≤ Lg * |blockRead W k b U w - 1| := hg _ _
      _ ≤ Lg * 1 := mul_le_mul_of_nonneg_left
          (abs_le.mpr ⟨by unfold blockRead; linarith, by unfold blockRead; linarith⟩) hLg
      _ = Lg := mul_one _
  have hFb : ∀ U, |F U - f 1| ≤ Lf := fun U => by rw [hF]; exact hnear f Lf hLf hf z U
  have hHb : ∀ U, |H U - h 1| ≤ Lh := fun U => by rw [hH]; exact hnear h Lh hLh hh z' U
  rw [← pow_mul]
  by_cases hsep : 2 * (b + ρ) + 1 ≤ b * snorm (z' - z)
  · obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = b * snorm (z' - z) - (b + ρ) - 1 := ⟨_, rfl⟩
    have hsR : b + ρ ≤ R := by omega
    have hRsep : R + 1 + (b + ρ) ≤ b * snorm (z' - z) := by omega
    have hc := cov_sep_of hK (fun i => (b : ℤ) * z i) hsR (cbox (fun i => (b : ℤ) * z i) (b + ρ))
      (fun l hl => by rw [one_mul]; exact mem_cbox.mp hl) F H (a := f 1) (a' := h 1) hLf
      (fun η η' hη => by rw [hF, hF]; exact congrArg f (blockRead_local W k b ρ hρ z η η' hη)) hFb
      (fun u ω => by
        rw [hH, hH]
        exact congrArg h (blockRead_local W k b ρ hρ z' _ _ fun l hl =>
          splice_not_mem (by rw [one_mul]; exact not_mem_cbox_of_sep hRsep hl)))
      hHb
    have hm : min ((cbox (fun i => (b : ℤ) * z i) (b + ρ)).card : ℝ)
        (4 * (2 * (((b + ρ : ℕ)) : ℝ) + 1) ^ 4) ≤ 4 * (2 * ((b : ℝ) + ρ) + 1) ^ 4 :=
      (min_le_right _ _).trans (le_of_eq (by push_cast; ring))
    have hpow : θ ^ (R - (b + ρ)) = θ ^ (b * snorm (z' - z)) * (θ ^ (2 * (b + ρ) + 1))⁻¹ := by
      have e : b * snorm (z' - z) = (R - (b + ρ)) + (2 * (b + ρ) + 1) := by omega
      rw [e, pow_add, mul_inv_cancel_right₀ (pow_ne_zero _ hθ0.ne')]
    refine hc.trans ?_
    calc 2 * (K * min ((cbox (fun i => (b : ℤ) * z i) (b + ρ)).card : ℝ)
            (4 * (2 * (((b + ρ : ℕ)) : ℝ) + 1) ^ 4) * θ ^ (R - (b + ρ))) * Lf * Lh
        ≤ 2 * (K * (4 * (2 * ((b : ℝ) + ρ) + 1) ^ 4) * θ ^ (R - (b + ρ))) * Lf * Lh :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK0) (pow_nonneg hθ0.le _))
            (by norm_num)) hLf) hLh
      _ = contQ K θ b ρ * Lf * Lh * θ ^ (b * snorm (z' - z)) := by rw [hpow]; unfold contQ; ring
  · have hc := cov_le_of_near_const (periodicState hN β) F (H - h 1 • (1 : C(Cfg N, ℝ))) hFb
      (fun U => by
        simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
          smul_eq_mul, mul_one]
        exact hHb U)
    rw [stateCov_sub_const_right] at hc
    have hge : 1 ≤ θ ^ (b * snorm (z' - z)) * (θ ^ (2 * (b + ρ) + 1))⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (pow_pos hθ0 _)]
      exact pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    have hP : (1 : ℝ) ≤ (2 * ((b : ℝ) + ρ) + 1) ^ 4 :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b), (Nat.cast_nonneg ρ : (0 : ℝ) ≤ ρ)])
    have h1 : 1 ≤ K * (2 * ((b : ℝ) + ρ) + 1) ^ 4 *
        (θ ^ (b * snorm (z' - z)) * (θ ^ (2 * (b + ρ) + 1))⁻¹) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 hP) hge
    have hQ : contQ K θ b ρ * θ ^ (b * snorm (z' - z)) = 8 * (K * (2 * ((b : ℝ) + ρ) + 1) ^ 4 *
        (θ ^ (b * snorm (z' - z)) * (θ ^ (2 * (b + ρ) + 1))⁻¹)) := by unfold contQ; ring
    have hLL : 0 ≤ Lf * Lh := mul_nonneg hLf hLh
    have h8 : 8 * (Lf * Lh) ≤ contQ K θ b ρ * θ ^ (b * snorm (z' - z)) * (Lf * Lh) := by
      rw [hQ]; nlinarith
    calc |stateCov (periodicState hN β) F H| ≤ 2 * Lh * Lf := hc
      _ ≤ contQ K θ b ρ * Lf * Lh * θ ^ (b * snorm (z' - z)) := by nlinarith

/-- **Pair decay of the block reading from the contraction.** DERIVED: no numeral. -/
theorem pairDecay_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) (W : ConfFlow N)
    (k b ρ : ℕ) (hρ : W.range k ≤ ρ) :
    PairDecay (periodicState hN β) (blockRead W k b) (contQ K θ b ρ) (θ ^ b) :=
  fun z z' _ _ _ _ hLf hLh hf hh F H hF hH => blockCov_of hK W k b ρ hρ z z' hLf hLh hf hh F H hF hH

/-- **`ObserverBlockReading.pairDecay_strong`, recovered.** DERIVED: `65536 = 2^{16}`; `1/2`. -/
theorem pairDecay_strong_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (W : ConfFlow N) (k b ρ : ℕ)
    (hρ : W.range k ≤ ρ) :
    PairDecay (periodicState hN β) (blockRead W k b) (strongQ b ρ) ((1 / 2 : ℝ) ^ b) := by
  rw [← contQ_strong]
  exact pairDecay_of (kernelDecayAt_strong hN hβ) W k b ρ hρ

/-- `θ^n = e^{−(−log θ) n}`. DERIVED: no numeral. -/
theorem pow_eq_exp {θ : ℝ} (hθ : 0 < θ) (n : ℕ) : θ ^ n = Real.exp (-(-Real.log θ * n)) := by
  rw [neg_mul, neg_neg, ← Real.rpow_natCast, Real.rpow_def_of_pos hθ]

/-- **The action density decays at rate `−log θ`**, with prefactor `contQ K θ 1 0`. DERIVED: `1` the block
side; `0` the range and the step. -/
theorem decaysAt_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) :
    DecaysAt (periodicState hN β) siteEnergy (-Real.log θ) := by
  refine ⟨contQ K θ 1 0, fun x z => ?_⟩
  have h := blockCov_of hK (ConfFlow.identity N) 0 1 0 le_rfl x (x + z) (f := id) (h := id) zero_le_one
    zero_le_one (fun a b => by simp) (fun a b => by simp) (siteEnergy x) (siteEnergy (x + z))
    (fun U => siteEnergy_apply x U) (fun U => siteEnergy_apply (x + z) U)
  rw [add_sub_cancel_left, pow_one, mul_one, mul_one, pow_eq_exp hK.2.1] at h
  exact h

/-- **The measured mass is at least `−log θ`.** DERIVED: `0` the sign. -/
theorem measMass_of {hN : N ≠ 0} {β K θ : ℝ} (hK : KernelDecayAt hN β 1 K θ) :
    ENNReal.ofReal (-Real.log θ) ≤ measMass (periodicState hN β) :=
  le_measMassOf (neg_nonneg.mpr (Real.log_nonpos hK.2.1.le hK.2.2.1)) (decaysAt_of hK)

/-- **`SubstrateDecode.decaysAt_strong`, recovered** (prefactor `contQ 1 (1/2) 1 0 = strongQ 1 0 = 5184`).
DERIVED: `65536 = 2^{16}`; `log 2 = −log(1/2)`. -/
theorem decaysAt_strong_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) :
    DecaysAt (periodicState hN β) siteEnergy (Real.log 2) := by
  have h := decaysAt_of (kernelDecayAt_strong hN hβ)
  rwa [one_div, Real.log_inv, neg_neg] at h

/-- **`SubstrateDecode.measMass_strong`, recovered.** DERIVED: `65536 = 2^{16}`; `log 2`. -/
theorem measMass_strong_rec (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) :
    ENNReal.ofReal (Real.log 2) ≤ measMass (periodicState hN β) := by
  have h := measMass_of (kernelDecayAt_strong hN hβ)
  rwa [one_div, Real.log_inv, neg_neg] at h

section ZeroFlux

variable [NeZero N]

open MassGap.CentreSectorSeedN (trivialDefectN)

/-- **`ZeroFluxGap.trivialDefectN_strong`, recovered.** DERIVED: `32768 = 2 · 16 · 1024`; `65536 = 2^{16}`;
`4 + N⁶` from `sectors_of_defectWN`, `6 = 2 · 3`, `N⁶` the square of `N³ = |Z_N³|`. -/
theorem trivialDefectN_strong_rec {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (hδ : (4 + (N : ℝ) ^ 6) * (β * strongBound n) ≤ 2) (i : Fin 4) :
    ENNReal.ofReal (Real.log 2) ≤ measMass (periodicState (NeZero.ne N) β) ∧
      trivialDefectN N β n i ≤ (32768 * β * (n : ℝ) ^ 4) * Real.exp (-(Real.log 2 / 2) * n) := by
  refine ⟨measMass_strong_rec (NeZero.ne N) (abs_le.mpr ⟨by linarith, hβ⟩), ?_⟩
  calc trivialDefectN N β n i ≤ 2 * (β * strongBound n) := (sectors_strong_rec hβ0 hβ hn he hδ i).2
    _ = _ := by unfold strongBound; ring

end ZeroFlux

/-! ## 6. Decay at a block side, and the tensor lock -/

/-- The sup-norm is symmetric. DERIVED: no numeral. -/
theorem snorm_sub_comm (a b : ISite) : snorm (a - b) = snorm (b - a) := by
  unfold snorm
  congr 1
  funext i
  rw [Pi.sub_apply, Pi.sub_apply, ← Int.natAbs_neg, neg_sub]

/-- A plaquette density reads only links within sup-distance `1` of its base. DERIVED: `1` the unit step. -/
theorem plaqField_local (q : IPlaq) : IsLocalOn (cbox q.2 1) ⇑(plaqField (N := N) q).1 := by
  intro η η' h
  rw [plaqField_apply, plaqField_apply, ihol_congr q η η' fun l hl => h l (mem_cbox.mpr
    (snorm_le_iff.mpr fun i => by
      have := ilinks_base hl i
      simp only [Pi.sub_apply]
      push_cast
      omega))]

/-- **The tensor reading has reach `1`.** DERIVED: `1` the unit step; `0`, `1`, `2`, `3` the planes. -/
theorem tensorEnergy_local (x : ISite) : IsLocalOn (cbox x 1) ⇑(tensorEnergy (N := N) x) := by
  intro η η' h
  simp only [tensorEnergy, ContinuousMap.sub_apply]
  rw [plaqField_local (N := N) (((0 : Fin 4), (1 : Fin 4)), x) η η' h,
    plaqField_local (N := N) (((2 : Fin 4), (3 : Fin 4)), x) η η' h]

/-- DERIVED: `2` the range of the density; `0`, `1`, `2`, `3` the planes. -/
theorem tensorEnergy_bound (hN : N ≠ 0) (x : ISite) (U : Cfg N) : |tensorEnergy (N := N) x U - 0| ≤ 2 := by
  rw [sub_zero]
  simp only [tensorEnergy, ContinuousMap.sub_apply, plaqField_apply]
  have h1 := wilsonDensity_nonneg hN (ihol (((0 : Fin 4), (1 : Fin 4)), x) U)
  have h2 := wilsonDensity_le_two hN (ihol (((0 : Fin 4), (1 : Fin 4)), x) U)
  have h3 := wilsonDensity_nonneg hN (ihol (((2 : Fin 4), (3 : Fin 4)), x) U)
  have h4 := wilsonDensity_le_two hN (ihol (((2 : Fin 4), (3 : Fin 4)), x) U)
  rw [abs_le]
  constructor <;> linarith

/-- **The action density has reach `1`.** DERIVED: `1` the site block; `0` the step and the range. -/
theorem siteEnergy_local (x : ISite) : IsLocalOn (cbox x 1) ⇑(siteEnergy (N := N) x) := by
  intro η η' hη
  rw [siteEnergy_apply, siteEnergy_apply]
  have h := blockRead_local (ConfFlow.identity N) 0 1 0 le_rfl x
  exact h η η' fun l hl => hη l (by simpa using hl)

/-- DERIVED: `1` the centre of `[0, 2]`. -/
theorem siteEnergy_bound (hN : N ≠ 0) (x : ISite) (U : Cfg N) : |siteEnergy (N := N) x U - 1| ≤ 1 := by
  rw [siteEnergy_apply]
  obtain ⟨h0, h2⟩ := blockEnergy_mem hN 1 U x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Decay at a block side**: a contraction at block side `b` gives decay of every reading of reach `r`
bounded about a constant, at rate `−log θ / b` per lattice unit. DERIVED: `1` the strict margin and the depth
offset; `2` the two sides of a constant; `4` the directions. -/
theorem decaysAt_of_scale {hN : N ≠ 0} {β K θ : ℝ} {b : ℕ} (hK : KernelDecayAt hN β b K θ) (hb : 1 ≤ b)
    {E : ISite → C(Cfg N, ℝ)} {r : ℕ} {a B : ℝ} (hB : 0 ≤ B)
    (hloc : ∀ x, IsLocalOn (cbox x r) ⇑(E x)) (hbd : ∀ x U, |E x U - a| ≤ B) :
    DecaysAt (periodicState hN β) E (-Real.log θ / b) := by
  have hK0 : 0 ≤ K := by linarith [hK.1]
  have hθ0 := hK.2.1
  have hθ1 := hK.2.2.1
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog : Real.log θ ≤ 0 := Real.log_nonpos hθ0.le hθ1
  set m : ℝ := -Real.log θ / b with hm
  have hm0 : 0 ≤ m := div_nonneg (by linarith) hb'.le
  set P : ℝ := 4 * (2 * (r : ℝ) + 1) ^ 4 with hP
  have hP0 : 0 ≤ P := by positivity
  set C₁ : ℝ := 2 * K * P * B * B * Real.exp (Real.log θ * (-(((r : ℝ) + 1) / b) - 1 - r)) with hC₁
  set D₀ : ℝ := (b : ℝ) * r + r + 1 with hD₀
  set C₂ : ℝ := 2 * B * B * Real.exp (m * D₀) with hC₂
  have hC₁0 : 0 ≤ C₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) hP0) hB) hB)
      (Real.exp_pos _).le
  have hC₂0 : 0 ≤ C₂ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hB) (Real.exp_pos _).le
  have hrb : r ≤ b * r := Nat.le_mul_of_pos_left r (by omega)
  refine ⟨C₁ + C₂, fun x z => ?_⟩
  have hE0 : 0 < Real.exp (-(m * (snorm z : ℝ))) := Real.exp_pos _
  by_cases hs : r + 1 ≤ snorm z ∧ r ≤ (snorm z - r - 1) / b
  · obtain ⟨hD1, hρ⟩ := hs
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℕ, ρ = (snorm z - r - 1) / b := ⟨_, rfl⟩
    rw [← hρdef] at hρ
    have hdm := Nat.div_add_mod (snorm z - r - 1) b
    have hmod := Nat.mod_lt (snorm z - r - 1) (by omega : b > 0)
    rw [← hρdef] at hdm
    have hsepN : b * ρ + r + 1 ≤ snorm z := by omega
    have hHoff : ∀ (u : VConf (SU N) (cbox x (b * ρ))) (ω : Cfg N),
        E (x + z) (splice (cbox x (b * ρ)) u ω) = E (x + z) ω := fun u ω =>
      hloc (x + z) _ _ fun l hl => splice_not_mem fun hl2 => by
        have h1 := mem_cbox.mp hl
        have h2 := mem_cbox.mp hl2
        have h3 := snorm_tri x l.2 (x + z)
        rw [add_sub_cancel_left, snorm_sub_comm (x + z) l.2] at h3
        omega
    have hc := cov_sep_of hK x hρ (cbox x r) (fun l hl => (mem_cbox.mp hl).trans hrb)
      (E x) (E (x + z)) (a := a) (a' := a) hB (hloc x) (hbd x) hHoff (hbd (x + z))
    -- the depth in blocks against the separation
    have hdmR : (b : ℝ) * ρ + (((snorm z - r - 1) % b : ℕ) : ℝ) = ((snorm z - r - 1 : ℕ) : ℝ) := by
      exact_mod_cast hdm
    have hmodR : (((snorm z - r - 1) % b : ℕ) : ℝ) < b := by exact_mod_cast hmod
    have hcast : ((snorm z - r - 1 : ℕ) : ℝ) + r + 1 = (snorm z : ℝ) := by
      have : snorm z - r - 1 + r + 1 = snorm z := by omega
      exact_mod_cast this
    have hlt : ((snorm z : ℝ) - r - 1) / b < ρ + 1 := by
      rw [div_lt_iff₀ hb']
      nlinarith
    have hρr : ((ρ - r : ℕ) : ℝ) = (ρ : ℝ) - r := Nat.cast_sub hρ
    have hpow : θ ^ (ρ - r) ≤ Real.exp (-(m * (snorm z : ℝ)))
        * Real.exp (Real.log θ * (-(((r : ℝ) + 1) / b) - 1 - r)) := by
      rw [← Real.exp_add, ← Real.rpow_natCast, Real.rpow_def_of_pos hθ0, hρr]
      apply Real.exp_le_exp.mpr
      have ht : ((snorm z : ℝ) - r - 1) / b - 1 - r ≤ (ρ : ℝ) - r := by linarith
      have e : -(m * (snorm z : ℝ)) + Real.log θ * (-(((r : ℝ) + 1) / b) - 1 - r)
          = Real.log θ * (((snorm z : ℝ) - r - 1) / b - 1 - r) := by
        rw [hm]; field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonpos_left ht hlog
    have hmin : min ((cbox x r).card : ℝ) (4 * (2 * (r : ℝ) + 1) ^ 4) ≤ P := min_le_right _ _
    calc |stateCov (periodicState hN β) (E x) (E (x + z))|
        ≤ 2 * (K * min ((cbox x r).card : ℝ) (4 * (2 * (r : ℝ) + 1) ^ 4) * θ ^ (ρ - r)) * B * B := hc
      _ ≤ 2 * (K * P * θ ^ (ρ - r)) * B * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hK0) (pow_nonneg hθ0.le _))
            (by norm_num)) hB) hB
      _ ≤ 2 * (K * P * (Real.exp (-(m * (snorm z : ℝ)))
            * Real.exp (Real.log θ * (-(((r : ℝ) + 1) / b) - 1 - r)))) * B * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK0 hP0)) (by norm_num)) hB) hB
      _ = C₁ * Real.exp (-(m * (snorm z : ℝ))) := by rw [hC₁]; ring
      _ ≤ (C₁ + C₂) * Real.exp (-(m * (snorm z : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂0) hE0.le
  · have hDle : (snorm z : ℝ) ≤ D₀ := by
      have : snorm z ≤ b * r + r + 1 := by
        rcases not_and_or.mp hs with h | h
        · omega
        · have h' := (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).mp (not_le.mp h)
          have hcomm : r * b = b * r := Nat.mul_comm r b
          omega
      rw [hD₀]
      exact_mod_cast this
    have hc := cov_le_of_near_const (periodicState hN β) (E x) (E (x + z) - a • (1 : C(Cfg N, ℝ)))
      (c := a) (δ := B) (M := B) (hbd x) (fun U => by
        simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
          smul_eq_mul, mul_one]
        exact hbd (x + z) U)
    rw [stateCov_sub_const_right] at hc
    have hge : 1 ≤ Real.exp (m * D₀) * Real.exp (-(m * (snorm z : ℝ))) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_le_mul_of_nonneg_left hDle hm0])
    have hBB : 0 ≤ 2 * B * B := mul_nonneg (mul_nonneg (by norm_num) hB) hB
    have h2 := mul_le_mul_of_nonneg_left hge hBB
    calc |stateCov (periodicState hN β) (E x) (E (x + z))| ≤ 2 * B * B := hc
      _ ≤ C₂ * Real.exp (-(m * (snorm z : ℝ))) := by rw [hC₂]; nlinarith
      _ ≤ (C₁ + C₂) * Real.exp (-(m * (snorm z : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁0) hE0.le

/-- **The tensor reading decays at rate `−log θ / b`.** DERIVED: `1` the reach; `0`, `2` the centre and the
bound. -/
theorem tensorDecay_of_scale {hN : N ≠ 0} {β K θ : ℝ} {b : ℕ} (hK : KernelDecayAt hN β b K θ)
    (hb : 1 ≤ b) : DecaysAt (periodicState hN β) tensorEnergy (-Real.log θ / b) :=
  decaysAt_of_scale hK hb (r := 1) (a := 0) (B := 2) (by norm_num) tensorEnergy_local
    (fun x U => tensorEnergy_bound hN x U)

/-- **The tensor lock from a contraction at block side `b`**: `m′ ≥ −log θ / b > 0`. DERIVED: `0` the
threshold. -/
theorem tensorLock_of_scale {hN : N ≠ 0} {β K θ : ℝ} {b : ℕ} (hK : KernelDecayAt hN β b K θ)
    (hb : 1 ≤ b) (hθ1 : θ < 1) :
    ENNReal.ofReal (-Real.log θ / b) ≤ measMassOf (periodicState hN β) tensorEnergy ∧
      0 < measMassOf (periodicState hN β) tensorEnergy := by
  have hm : 0 < -Real.log θ / b :=
    div_pos (neg_pos.mpr (Real.log_neg hK.2.1 hθ1)) (by exact_mod_cast hb)
  have hd := tensorDecay_of_scale hK hb
  exact ⟨le_measMassOf hm.le hd, lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hm) (le_measMassOf hm.le hd)⟩

/-! ## 7. The block pair piece at the window scale -/

/-- The pair constant at the window scale: `5000 K θ^{−5}`, independent of the block side.
DERIVED: `5000 = 2 · 4 · 5⁴`; `5` the least separating block distance. -/
def windowQ (K θ : ℝ) : ℝ := 5000 * K * (θ ^ 5)⁻¹

/-- **Block covariances at the window scale**: with the contraction at block side `b` and a flow of step range
at most `b`, the pinned block reading decorrelates at rate `θ` per block with constant `windowQ K θ`.
DERIVED: `2` the test region in blocks; `3`, `5` the separation margin; `2500 = 4 · 5⁴`. -/
theorem blockCov_window {hN : N ≠ 0} {β K θ : ℝ} {b : ℕ} (hK : KernelDecayAt hN β b K θ) (hb : 1 ≤ b)
    (W : ConfFlow N) (k : ℕ) (hρ : W.range k ≤ b) (z z' : ISite) {f h : ℝ → ℝ} {Lf Lh : ℝ}
    (hLf : 0 ≤ Lf) (hLh : 0 ≤ Lh) (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|)
    (hh : ∀ x y, |h x - h y| ≤ Lh * |x - y|) (F H : C(Cfg N, ℝ)) (hF : ∀ U, F U = f (blockRead W k b U z))
    (hH : ∀ U, H U = h (blockRead W k b U z')) :
    |stateCov (periodicState hN β) F H| ≤ windowQ K θ * Lf * Lh * θ ^ snorm (z' - z) := by
  have hK1 := hK.1
  have hK0 : 0 ≤ K := by linarith
  have hθ0 := hK.2.1
  have hθ1 := hK.2.2.1
  have hnear : ∀ (g : ℝ → ℝ) (Lg : ℝ), 0 ≤ Lg → (∀ x y, |g x - g y| ≤ Lg * |x - y|) → ∀ w U,
      |g (blockRead W k b U w) - g 1| ≤ Lg := by
    intro g Lg hLg hg w U
    obtain ⟨h0, h2⟩ := blockEnergy_mem hN b (W.V k U) w
    calc |g (blockRead W k b U w) - g 1| ≤ Lg * |blockRead W k b U w - 1| := hg _ _
      _ ≤ Lg * 1 := mul_le_mul_of_nonneg_left
          (abs_le.mpr ⟨by unfold blockRead; linarith, by unfold blockRead; linarith⟩) hLg
      _ = Lg := mul_one _
  have hFb : ∀ U, |F U - f 1| ≤ Lf := fun U => by rw [hF]; exact hnear f Lf hLf hf z U
  have hHb : ∀ U, |H U - h 1| ≤ Lh := fun U => by rw [hH]; exact hnear h Lh hLh hh z' U
  by_cases hsep : 5 ≤ snorm (z' - z)
  · obtain ⟨e, he⟩ : ∃ e, snorm (z' - z) = e + 5 := ⟨snorm (z' - z) - 5, by omega⟩
    have hRsep : b * (e + 2) + 1 + (b + b) ≤ b * snorm (z' - z) := by
      have hm : b * (e + 5) = b * (e + 2) + 3 * b := by ring
      rw [he, hm]
      omega
    have hc := cov_sep_of hK (fun i => (b : ℤ) * z i) (σ := 2) (ρ := e + 2) (by omega)
      (cbox (fun i => (b : ℤ) * z i) (b + b)) (fun l hl => (mem_cbox.mp hl).trans (by omega))
      F H (a := f 1) (a' := h 1) hLf
      (fun η η' hη => by rw [hF, hF]; exact congrArg f (blockRead_local W k b b hρ z η η' hη)) hFb
      (fun u ω => by
        rw [hH, hH]
        exact congrArg h (blockRead_local W k b b hρ z' _ _ fun l hl =>
          splice_not_mem (not_mem_cbox_of_sep hRsep hl)))
      hHb
    have hm : ∀ q : ℝ, min q (4 * (2 * ((2 : ℕ) : ℝ) + 1) ^ 4) ≤ 2500 :=
      fun q => (min_le_right _ _).trans (by norm_num)
    refine hc.trans ?_
    rw [Nat.add_sub_cancel]
    refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hm _) hK0) (pow_nonneg hθ0.le _))
      (by norm_num)) hLf) hLh) (le_of_eq ?_)
    rw [he, windowQ, pow_add]
    field_simp
    ring
  · have hc := cov_le_of_near_const (periodicState hN β) F (H - h 1 • (1 : C(Cfg N, ℝ))) hFb
      (fun U => by
        simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
          smul_eq_mul, mul_one]
        exact hHb U)
    rw [stateCov_sub_const_right] at hc
    have hge : 1 ≤ θ ^ snorm (z' - z) * (θ ^ 5)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (pow_pos hθ0 _)]
      exact pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    have h1 : 1 ≤ K * (θ ^ snorm (z' - z) * (θ ^ 5)⁻¹) := one_le_mul_of_one_le_of_one_le hK1 hge
    have hQ : windowQ K θ * θ ^ snorm (z' - z) = 5000 * (K * (θ ^ snorm (z' - z) * (θ ^ 5)⁻¹)) := by
      unfold windowQ; ring
    have hLL : 0 ≤ Lf * Lh := mul_nonneg hLf hLh
    have h8 : 5000 * (Lf * Lh) ≤ windowQ K θ * θ ^ snorm (z' - z) * (Lf * Lh) := by
      rw [hQ]; nlinarith
    calc |stateCov (periodicState hN β) F H| ≤ 2 * Lh * Lf := hc
      _ ≤ windowQ K θ * Lf * Lh * θ ^ snorm (z' - z) := by nlinarith

/-- **Pair decay of the block reading at the window scale.** DERIVED: no numeral. -/
theorem pairDecay_window {hN : N ≠ 0} {β K θ : ℝ} {b : ℕ} (hK : KernelDecayAt hN β b K θ) (hb : 1 ≤ b)
    (W : ConfFlow N) (k : ℕ) (hρ : W.range k ≤ b) :
    PairDecay (periodicState hN β) (blockRead W k b) (windowQ K θ) θ :=
  fun z z' _ _ _ _ hLf hLh hf hh F H hF hH => blockCov_window hK hb W k hρ z z' hLf hLh hf hh F H hF hH

/-! ## 8. The window input -/

/-- **The window contraction** (assumed): there are `C > 0`, `K`, `θ < 1` such that, eventually in `β`, some
block side `b ≥ 1` of at most `C` measured lengths (`b · m′ ≤ C`, `m′` the tensor mass) has
`KernelDecayAt hN β b K θ`. Every constant is fixed before `β` and before any block set. DERIVED: `0` the sign;
`1` the least block side. -/
def WindowContraction (hN : N ≠ 0) : Prop :=
  ∃ C K θ : ℝ, 0 < C ∧ θ < 1 ∧ ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧
    (b : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ≤ ENNReal.ofReal C ∧
    KernelDecayAt hN β b K θ

/-- **(a) The window gives the lock**: eventually `0 < m′ < ∞`. DERIVED: `0`. -/
theorem window_lock {hN : N ≠ 0} (h : WindowContraction hN) :
    ∀ᶠ β in atTop, 0 < measMassOf (periodicState hN β) tensorEnergy ∧
      measMassOf (periodicState hN β) tensorEnergy ≠ ⊤ := by
  obtain ⟨C, K, θ, hC, hθ1, hev⟩ := h
  filter_upwards [hev] with β ⟨b, hb, hbm, hK⟩
  refine ⟨(tensorLock_of_scale hK hb hθ1).2, fun htop => ?_⟩
  rw [htop, ENNReal.mul_top (Nat.cast_ne_zero.mpr (by omega))] at hbm
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hbm)

/-- **The lock clause of `ZeroFluxReadsMass` and `LongChainRead`**: eventually `0 < m′.toReal`.
DERIVED: `0`. -/
theorem window_lock_toReal {hN : N ≠ 0} (h : WindowContraction hN) :
    ∀ᶠ β in atTop, 0 < (measMassOf (periodicState hN β) tensorEnergy).toReal :=
  (window_lock h).mono fun _ hβ => ENNReal.toReal_pos hβ.1.ne' hβ.2

/-- **The window rate in measured units**: `−log θ ≤ b m′ ≤ C` eventually, so `−log θ ≤ C`.
DERIVED: `0`, `1`. -/
theorem window_rate {hN : N ≠ 0} (h : WindowContraction hN) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ -Real.log θ ≤ C ∧ ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧
      ENNReal.ofReal (-Real.log θ) ≤ (b : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ∧
      (b : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ≤ ENNReal.ofReal C := by
  obtain ⟨C, K, θ, hC, hθ1, hev⟩ := h
  have hev' : ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧
      ENNReal.ofReal (-Real.log θ) ≤ (b : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ∧
      (b : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ≤ ENNReal.ofReal C ∧ 0 < θ := by
    filter_upwards [hev] with β ⟨b, hb, hbm, hK⟩
    refine ⟨b, hb, ?_, hbm, hK.2.1⟩
    have h1 := (tensorLock_of_scale hK hb hθ1).1
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have e : (b : ℝ) * (-Real.log θ / b) = -Real.log θ := by field_simp
    calc ENNReal.ofReal (-Real.log θ) = (b : ℝ≥0∞) * ENNReal.ofReal (-Real.log θ / b) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hb'.le, e]
      _ ≤ (b : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy := by gcongr
  obtain ⟨β, b, hb, h1, h2, hθ0⟩ := hev'.exists
  refine ⟨C, θ, hC, hθ0, hθ1, ?_, hev'.mono fun _ ⟨b, hb, h1, h2, _⟩ => ⟨b, hb, h1, h2⟩⟩
  exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp (h1.trans h2)

/-- **The tower lock**: along every coupling sequence tending to infinity (in particular every measured tower),
eventually `0 < mUG (SU N) (βs k) < ∞`. DERIVED: no numeral. -/
theorem window_towerLock [NeZero N] (h : WindowContraction (NeZero.ne N)) {βs : ℕ → ℝ}
    (hβs : Tendsto βs atTop atTop) :
    ∀ᶠ k in atTop, 0 < MeasuredTower.mUG (SU N) (βs k) ∧ MeasuredTower.mUG (SU N) (βs k) ≠ ⊤ := by
  filter_upwards [hβs.eventually (window_lock h)] with k hk
  rw [MeasuredSpacing.mUG_SU]
  exact hk

/-- **The window gives the block pair piece with constants independent of the block side.**
DERIVED: `0`, `1`. -/
theorem window_pairDecay {hN : N ≠ 0} (h : WindowContraction hN) :
    ∃ K θ : ℝ, 1 ≤ K ∧ 0 < θ ∧ θ < 1 ∧ ∀ᶠ β in atTop, ∃ b : ℕ, 1 ≤ b ∧
      ∀ (W : ConfFlow N) (k : ℕ), W.range k ≤ b →
        PairDecay (periodicState hN β) (blockRead W k b) (windowQ K θ) θ := by
  obtain ⟨C, K, θ, hC, hθ1, hev⟩ := h
  obtain ⟨β₀, b₀, -, -, hK₀⟩ := hev.exists
  refine ⟨K, θ, hK₀.1, hK₀.2.1, hθ1, ?_⟩
  filter_upwards [hev] with β ⟨b, hb, _, hK⟩
  exact ⟨b, hb, fun W k hρ => pairDecay_window hK hb W k hρ⟩

end MassGap.ContractionReads

end

#print axioms MassGap.ContractionReads.kernelDecayAt_of_row
#print axioms MassGap.ContractionReads.kernelDecayAt_strong
#print axioms MassGap.ContractionReads.kernelNear_one
#print axioms MassGap.ContractionReads.clause_of_K_after_box
#print axioms MassGap.ContractionReads.clause_depth_zero
#print axioms MassGap.ContractionReads.cov_sep_of
#print axioms MassGap.ContractionReads.cov_sep_strong_rec
#print axioms MassGap.ContractionReads.torusState_sub_le_of
#print axioms MassGap.ContractionReads.torusState_sub_le_rec
#print axioms MassGap.ContractionReads.torusState_sub_le_reach_of
#print axioms MassGap.ContractionReads.torusState_sub_le_reach_rec
#print axioms MassGap.ContractionReads.doubling_sub_le_of
#print axioms MassGap.ContractionReads.tendsto_doubling_of
#print axioms MassGap.ContractionReads.plaq_sub_le_of
#print axioms MassGap.ContractionReads.bareRead_sub_le_of
#print axioms MassGap.ContractionReads.bareRead_sub_le_rec
#print axioms MassGap.ContractionReads.bareRead_doubling_of
#print axioms MassGap.ContractionReads.doubleBound_strong_le
#print axioms MassGap.ContractionReads.finiteSize_decay_rec
#print axioms MassGap.ContractionReads.abs_defectW_le_of_path
#print axioms MassGap.ContractionReads.sectors_of_path
#print axioms MassGap.ContractionReads.sectors_strong_rec
#print axioms MassGap.ContractionReads.contQ_strong
#print axioms MassGap.ContractionReads.blockCov_of
#print axioms MassGap.ContractionReads.pairDecay_of
#print axioms MassGap.ContractionReads.pairDecay_strong_rec
#print axioms MassGap.ContractionReads.decaysAt_of
#print axioms MassGap.ContractionReads.measMass_of
#print axioms MassGap.ContractionReads.decaysAt_strong_rec
#print axioms MassGap.ContractionReads.measMass_strong_rec
#print axioms MassGap.ContractionReads.trivialDefectN_strong_rec
#print axioms MassGap.ContractionReads.tensorEnergy_local
#print axioms MassGap.ContractionReads.siteEnergy_local
#print axioms MassGap.ContractionReads.decaysAt_of_scale
#print axioms MassGap.ContractionReads.tensorLock_of_scale
#print axioms MassGap.ContractionReads.blockCov_window
#print axioms MassGap.ContractionReads.pairDecay_window
#print axioms MassGap.ContractionReads.window_lock
#print axioms MassGap.ContractionReads.window_lock_toReal
#print axioms MassGap.ContractionReads.window_rate
#print axioms MassGap.ContractionReads.window_towerLock
#print axioms MassGap.ContractionReads.window_pairDecay
