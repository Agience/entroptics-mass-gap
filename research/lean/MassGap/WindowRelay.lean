import Mathlib
import MassGap.UniformRelayStrong
import MassGap.GapSideExactDecimation

/-!
# MassGap.WindowRelay — the relay gap of a weight with small oscillation, carried through decimation to the window

The frame: the observer is part of the substrate and reads it through a fixed aperture at its own measured
scale, where the theory should look strongly coupled. This module asks how far the strong-coupling relay gap
of `UniformRelayStrong` travels toward that statement. Declarations are in the namespace
`MassGap.WindowRelay`.

## 1. The relay gap with the activity as the input (proved, except the cluster bound of a general weight)

`StrongCoupling` writes each plaquette factor as `1 + ρ_p` and bounds `|ρ_p| ≤ e^{2|β|} − 1`. For a weight
`e^{−Ψ}` with `Ψ` in `[m, m + ε]` the same bound reads `|e^{−(Ψ − m)} − 1| ≤ e^{ε} − 1` (`osc_activity`); the
Wilson weight is the case `Ψ = β φ_W`, `ε = 2β` (`wilson_activity`). The rate of the expansion as a function
of the activity is `actRate K ε = coreRate K (ε/2) = 4 (K + 1)² (e^{ε} − 1) e^{2Kε}` (`actRate_eq`,
`coreRate_eq_actRate`), below one for `0 ≤ ε ≤ ε₀` (`exists_actRate_lt_one`).

The relay layer of `UniformRelayStrong` restated with the cluster bound as its input:

* `ClusterBound μ k r`: for every continuous slice test `u` the two-slice connected read of `k^{∗(j+1)}` is at
  most `G_u r^{j+2−U_u}` once `U_u ≤ j + 2`. This is the shape `UniformRelayStrong.slice_pair_cluster` produces:
  the prefactor and the anchor size depend on the test and the aperture, the rate does not.
* `pairDecay_of_clusterBound`, then `relayGap_of_pairDecay`: any continuous symmetric kernel with a floor
  `a > 0` and ceiling `1` and a cluster bound at a rate `r ≤ ρ` has a positive top `λ` (the witness is `‖K‖`;
  the statement records only `λ > 0`) with a positive eigenfunction and `‖K − λ φ⊗φ‖ ≤ λ ρ` (`JentzschKT.exists_pos_eigen`,
  `UniformRelayStrong.gap_of_pairDecay`). No coupling enters.
* `clusterBound_kT`, `wilson_relay_generic`: the Wilson slice transfer is an instance.

The slice transfer of a general weight (`spW`, `tpW`, `gkW`, `kTW`): the definitions of `RectTransfer` with
the Wilson density replaced by a weight `Ψ`. For a `ClassWeight Ψ ε` (continuous, conjugation invariant,
inversion invariant, values in `[0, ε]`) the kernel is symmetric (`kTW_symm`; inversion invariance is what
the reflection `A ↦ A⁻¹` needs, and it is not automatic for a real class function on `SU(N)`, `N ≥ 3`),
jointly continuous (`continuous_kTW`), at most `1` (`kTW_le_one`) and above the floor `kTWmin > 0`
(`kTW_lower`). These are the three properties the bootstrap reads. `kTW_wilson`: at `Ψ = β φ_W` it is
`RectTransfer.kT` itself. `classWeight_wilson`: `β φ_W` is a class weight of oscillation `2β`.

`WeightCluster N Ψ r` (assumed): the cluster bound of the slice transfer of `Ψ` at every aperture with
positive extents. `relayGapW`, `relayGap_of_osc`: a class weight of oscillation `ε` with
`WeightCluster N Ψ (actRate 64 ε)` and `actRate 64 ε ≤ ρ ≤ 1` has the relay gap `λ ρ` at every aperture,
uniformly. `weightCluster_wilson` (proved): the Wilson weight satisfies `WeightCluster` at
`actRate 64 (2β) = coreRate 64 β`; `wilson_relayGap_via_weight` runs the Wilson case through the general
statement.

Why `WeightCluster` stays an input (argued). `StrongCoupling`'s proof reads the plaquette density only
through `measurable_wilsonDensity` (6 call sites), `wilsonDensity_nonneg` (8) and `wilsonDensity_le_two` (7),
and `RectTorusState.rectState_pairObs` reads it through `RectWilson.sysR`. With the density a parameter
`f : SU(N) → [0, 2]`, every statement holds verbatim, and a class weight of oscillation `ε` is the case
`f = 2Ψ/ε` at coupling `ε/2`. The density is fixed to `wilsonDensity` on about 180 lines of `StrongCoupling`
(the dependency cone of `wilsonCorrConnObs_abs_le_of_not_mem_ball` is most of its 8400 lines, estimated), so the
general statement is an edit of that module, not a separate one.

## 2. Transport through decimation

* **In time (proved, exact).** A window hop of `j + 1` fine hops is the kernel `K^{∗(j+1)}`, with top
  `λ^{j+1}` and remainder `R^{∗(j+1)}` (`rem_iter_eq`, from `KernelPower.iter_decomp`), and
  `(kernelCLM r)^{j+1} = kernelCLM (r^{∗(j+1)})` (`kernelCLM_pow`). For a symmetric operator
  `‖A^b‖ ≤ ρ^b` gives `‖A‖ ≤ ρ` (`norm_le_of_norm_pow_le`: per-vector decay at rate `ρ`, then
  `StrongTransferGap.opNorm_le_of_decay`). So a window-hop gap at rate `ρ₀` relative to the top is a
  one-hop gap at rate `ρ₀^{1/(j+1)}` (`gap_of_hop_gap`, `transferGapAt_of_windowHop`), and conversely
  (`hop_of_gap`, `windowHop_of_transferGapAt`). Were there a coarse slice transfer (there is not, obstruction 2
  below), two fine hops per coarse hop would make a coarse rate `ρ` a fine rate `ρ^{1/2}`.
* **The skeleton (proved, exact).** For any measure-preserving parametrization `glue : Ωc × Ωr → Ωf` with a
  coarse projection `π ∘ glue = fst` (for `GapSideExactDecimation.glueStep` the coarse projection is the
  product of the two fine links on each coarse line; this `π` and its identity `π ∘ glueStep = fst` are not
  defined in Lean), every observable that reads the fine configuration through `π` has the same integral
  against the fine density and against the effective density (`integral_skeleton`), and the same normalized
  expectation (`expect_skeleton`). In particular every two-slice connected read of skeleton observables is the
  same number on the fine torus and on the coarse one.
* **In space (does not hold as a transport of the gap; argued).** Three obstructions, in order of depth.
  1. The bootstrap needs `PairDecay` for every continuous test on the fine slice (density in `L²` is how
     `gap_step` passes from vectors to the operator). The exact decimation identifies only the skeleton
     algebra `π^* C(Ω_c)`, a proper closed subalgebra. A fine kernel `K_c ⊗ M` on `Ω_c × Y`, with `M` of gap
     close to one, has skeleton reads that decay at the rate of `K_c` and a fine relay gap no better than
     that of `M`. The missing input is that the fine slice modes orthogonal to the skeleton are forgotten
     within one window hop: `‖R^{∗b}(1 − P_skel)‖ ≤ δ`, with `‖R^{∗b} P_skel‖² = sup ⟨v, R^{∗2b} v⟩` over unit
     skeleton vectors `v`, which is a skeleton read.
  2. The effective measure is not a nearest-neighbour chain in coarse time. The fine chain is Markov in fine
     time with the full fine slice as its state; its image under `π` is a hidden Markov chain, so the
     effective density has no coarse slice transfer whose gap could be asked.
  3. The effective density is not a plaquette weight. At leading order of the character expansion of the
     integrated fine links, two coarse plaquettes sharing a coarse link enter through the character of the
     product of their holonomies, which is not a function of the two conjugacy classes separately; a product
     of class functions of single coarse plaquettes cannot produce it. The exact effective action is
     non-local at every `β > 0` and every `k ≥ 1`.
  The carrier differs as well: the exact decimation is built on the cubic `SU(2)` torus `TLink 4 n`, the
  relay on the rectangular `SU(N)` torus of `RectWilson`.

## 3. The window input

`WindowStrong ε₀ a C` (assumed): eventually in `β`, `m′ > 0`, and at the window `k` with
`C ≤ 2^k m′ ≤ 2C` (blocks of about `C/m′` fine sites), past the crossover of the zoom from `k` on (`PastPeak`,
§4), the `k`-step exact effective density of the `SU(2)` Wilson torus has, at every coarse side `n ≥ 1`, a
quasi-local representation (`QuasiLocalAt`):

    ρ_eff(V) = Z exp(−Σ_q Ψ(hol_q V) + Σ_X R_X(V)),

with `Ψ` a class weight of oscillation `ε₀`, `R_X` reading only the links of `X`, `|R_X| ≤ D_X` and
`Σ_{X ∋ q} D_X e^{a|X|} ≤ ε₀` at every plaquette `q`. `ε₀`, `a > 0` and `C` are fixed before `β`. The decay
weight `e^{a|X|}` is required: without it, pair polymers `{q, q′}` with `D ∝ ε₀ |q − q′|^{−s}`, `s > 4`, satisfy
the per-plaquette sum and give power-law decay of the two-point read, so no fixed-rate cluster bound could
follow. The plaquette part is the
strong-coupling weight; the polymer part carries the non-locality of §2.3. It is the statement that the
observer sees strong coupling at its own scale.

What it gives (proved):

* `window_plaquette_relay`: with `OscCluster ε₀` (the cluster bound of §1 for every class weight of
  oscillation `ε₀`, assumed) and `actRate 64 ε₀ ≤ ρ ≤ 1`, the plaquette weight `Ψ` of the representation that
  `WindowStrong` supplies has the uniform relay gap `λ ρ` at every aperture. `Ψ` is not determined by the
  density: moving it into single-plaquette polymers gives a representation with `Ψ = 0` at oscillation
  `3ε₀/2`, whose slice transfer is constant, so this statement carries no information about the window density
  by itself (argued).
* `window_Z_exact`: the window density is reached in one exact decimation; its partition function at every
  background is the fine one at the pulled-back background, with no control at intermediate steps.
* `transferGapMeasured_of_windowHop`: `WindowHopMeasured N hN C ρ₀` (a fine window-hop gap at fixed rate `ρ₀`
  at a window `(j + 1) m′ ≤ C`, with the anchor at `c = −log ρ₀ / C`) gives
  `SliceTransferGap.TransferGapMeasured N hN` with that `c`.

Missing links (named): (L1) `PolymerCluster`, the cluster bound of the plaquette weight dressed with the
polymer factor `e^{Σ R_X}` (the subset expansion of `StrongCoupling` with the extra activities `e^{R_X} − 1`);
(L2) the coarse-to-fine step of §2.1–2.2 (skeleton reads to every fine slice mode, and a coarse slice transfer)
together with a rectangular `SU(N)` decimation; (L3) the anchor clause of `TransferGapMeasured`, about which a gap statement says nothing (`SliceTransferGap.no_hop_from_gap`). The observer's gap consumer
(`ClayGFinal.observerOSDataSLinkedGN`, input `hg`) does not read (L3). For that consumer `ObserverSkeleton` replaces the
coarse-to-fine part of (L2) by an observer-skeleton condition (`SkeletonReads`, `SkeletonCluster`) or a uniform-angle
condition (`gap_of_angle`). Neither is shown to hold at the target and both are argued to fail there. The carrier
part of (L2), a decimation of the target's state over `G`, remains. Without (L1)–(L3), `WindowStrong` gives
neither a relay gap of the fine slice transfer nor `TransferGapMeasured`.

## 4. The supercritical crossover of the zoom

The coupling axis. `SupercriticalPath`, `SupercriticalRate`, `TorusRate` and `ConstantPhysics` (`latMass`,
`LatticeGapEvery`, `LatMassContinuousFrom`) are in this repository's git history, not in the live
tree. Their conditions on the choice-free torus rate, from some `β₁` on, are (S1) a gap, (S2) continuity, (S3)
`torusRate → 1` at `β = ∞`. The `SU(2)` Wilson axis passes the endpoint of the first-order line of the
fundamental–adjoint mixed action without touching it (read from Bhanot–Creutz and Heller, not proved): a
supercritical path, with the strong-coupling and the weak-coupling regimes one phase (as in Fradkin–Shenker and
Osterwalder–Seiler complementarity), joined by a crossover near `β ≈ 2.2` where the plaquette susceptibility
peaks.

The zoom. Along the exact decimation at fixed fine `β` the effective theory moves from the weak-coupling side
(blocks much smaller than `1/m′`) to the strong-coupling side (blocks much larger). It crosses the image of
that crossover, a Widom-type line, where the block is comparable to the correlation length: `2^k m′` of order
one. There the fluctuations of the coarse reads and their response peak, the effective density's oscillation is
not small, and the measured read loses its cliff and its lock. No strong-coupling control holds there, and none
is asked.

(a) Where the window sits. The crossover read is `coarseSusc β k n`, the coarse plaquette susceptibility: the
variance of the summed coarse plaquette action under the normalized `k`-step effective density, per plaquette.
It is the specific-heat read (the action variance is the second `β`-derivative of `log Z`;
`EffectiveCoupling.hasDerivAt_logZR` gives the first), whose peak marks the crossover of the coupling axis. It
is the variance of the summed fine Wilson loops of side `2^k` on the fine torus of side `2^k n`, per loop
(argued: it needs the coarse projection of `glueStep` composed over `k` steps, together with
`integral_skeleton`, and none of that is built); a read of the fine theory at block scale `2^k m′`, in measured
units. A single-loop variance is not used: in 2D it is `1/4 + (3/4) a_1^A − a_{1/2}^{2A}` with
`a_1 < a_{1/2}²` (Turán), which rises to the Haar value from below, so it has no peak to pass; in 4D the
perimeter-law adjoint loop can put it above `1/4`. Whether `coarseSusc` peaks along the zoom is itself open
(argued from the coupling axis, not proved). `PastPeak β k`: from step `k` on the read does not rise under any
further step, at every coarse side `n ≥ 2` (side `1` is excluded: there a plaquette is a commutator of wrapping
lines), so the peak lies at or before `k`. No proved statement of this module reads `PastPeak`. `WindowStrong` asks for a window `k` with `C ≤ 2^k m′ ≤ 2C` and `PastPeak β k`: the window is
on the confined side of the crossover, at a block side of `C` correlation lengths, past the measured peak.

(b) What is not claimed. No oscillation bound is asked at any step `j < k`, and in particular none through the
crossover region; `PastPeak` is a monotonicity of one read, not a bound on any density.

(c) The transport through the crossover. The exact decimation needs no control at any intermediate step:
`effIter k` is `k` exact integrations, and `window_Z_exact` (through `GapSideExactDecimation.effIter_spec`)
gives the window partition function at every background from continuity of the fine weight alone; the skeleton
identities of §2 hold for any measure-preserving parametrization, so the `k` steps compose to one
measure-preserving parametrization of the fine links by the window skeleton and the rest (argued: a composition
of measure-preserving maps; the composite parametrization is not built as one `glue`). The decimation to the
window is one exact integration, and every claim of this module reads only its result. What does need control
step by step is any route that bounds `effIter (j + 1)` from a bound on `effIter j` (a renormalization-group
iteration): that route fails at the crossover, and it is not used.

Test (argued). At or before the crossover (`2^k m′ ≲ 1`) the clause of `WindowStrong` fails: on the weak side the
effective weight concentrates near the identity, so `osc Ψ` is large; at the crossover the coarse plaquette
susceptibility is at its peak and the polymer activities of any quasi-local representation are of order one. Such a
placement is excluded twice: `C` is fixed large before `β`, so `2^k m′ ≥ C` puts the block at `C` correlation
lengths; and `PastPeak β k` fails at a window placed before the peak of the read, since the read rises from
there. At `β = 0` there is no crossover: the read is the same Haar value at every scale and every step is past the
peak (`pastPeak_zero_coupling`, proved).

## 5. Tests of `WindowStrong`

1. `β = 0` (proved, `quasiLocal_zero_coupling`): the fine density is `1`, every exact step keeps it `1`
   (`effIter_one`), and the clause holds at every `k`, `n` with `Ψ = 0`, `R = 0`, for every `ε₀ ≥ 0` and `a`.
2. Strong coupling (proved, `quasiLocal_zero_steps`): with zero decimation steps the clause is the fine
   Wilson weight itself, `Ψ = β φ_W`, `R = 0`, and holds when `2β ≤ ε₀`. At strong coupling `m′` is large in
   lattice units, the window sits at `k = 0` when `C ≤ m′ ≤ 2C`, and does not exist when `m′ > 2C`; and the input is the strong-coupling bound already proved. The
   Prop is read along `β → ∞`, so neither is an instance of it.
3. Vacuity (proved and argued). `ε₀`, `a` and `C` are fixed before `β`, the side and the direction. A class weight
   forces `ε₀ ≥ 0` (`ClassWeight.eps_nonneg`). The one-polymer representation (`X = univ`) is always available,
   but it asks `sup |log ρ_eff + Σ Ψ − log Z| ≤ ε₀`, an extensive quantity, so the per-plaquette clause is not
   met by bookkeeping. The empty polymer is constant (locality with an empty support), so no content can be
   hidden in it. The window pins `k` up to one doubling.
4. At the lattice scale (argued). With `k` fixed along `β → ∞` the clause asks a fixed lattice block of a
   weak-coupling theory to be strongly coupled; by asymptotic freedom the effective coupling of a fixed block
   goes to zero and the effective weight concentrates near the identity, so `osc Ψ → ∞`: false. The input is
   asked only where the blocks are `C/m′` sites, a measured length.
5. Restatement or reduction. The time part is a restatement: a window-hop gap is a one-hop gap
   (`transferGapAt_of_windowHop`, `windowHop_of_transferGapAt`, both proved). `WindowStrong` itself is not a gap
   statement: it is a pointwise bound on one density at one scale, from which the gap would follow through
   (L1), §1, (L2) and, for `TransferGapMeasured`, (L3); none of the three is proved. It is a reduction in the sense that its content is local and finite-volume uniform; it is not
   proved to be weaker than the gap, and (L2) is a gap-like statement about the fine scale (that fine modes
   decorrelate within one window hop).

Plausibility (argued). In plaquette-product form (`R = 0`) the clause is false at every `β > 0`, `k ≥ 1`
(§2.3). In the quasi-local form it is the expected behaviour beyond the correlation length: a coarse link is
the product of `2^k ≈ C/m′` fine links along a line, so about `C` correlation lengths of fine randomness enter
it, and its conditional law given the rest of the skeleton should be close to Haar for every boundary datum
once `C` is large; the coarse Wilson loops are fine loops of area `(C/m′)²`, deep in the area-law regime. That
the polymer activities of the exact effective action are summable with a small per-plaquette sum is the
strong-coupling counterpart of Bałaban's small-field bounds; no published result gives it at the window scale.
The clause is a sup over all coarse configurations (an absolute bound), which is stronger than a bound in the
reading's own form `⟨x, x⟩`. It runs against the principle that nothing is absolute: errors are measured in
the reading's form `⟨x, x⟩`, never in sup norm. A form version, asked of typical configurations, is the
natural variant; it is not built here.

## 6. Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: why `WeightCluster` is not built (§1); the three spatial obstructions and the carrier mismatch
  (§2); the reading of the coupling axis and of the zoom crossover, the composite parametrization in (c) and the
  crossover test (§4); the plausibility paragraph and tests 3 (the extensive one-polymer bound), 4 and 5 (§5).
* Assumed: `WeightCluster N Ψ r` in `relayGapW`, `relayGap_of_osc`; `OscCluster ε₀` and `WindowStrong ε₀ a C` in
  `window_plaquette_relay`; `WindowHopMeasured N hN C ρ₀` in `transferGapMeasured_of_windowHop`.

## 7. Parameters

| argument | where | status |
|---|---|---|
| `β` | every lattice read | shared, in the substrate; `WindowStrong` is read along `β → ∞` |
| `Ψ` | class weights, `kTW` | a plaquette weight `SU(N) → [0, ε]`; existential in `QuasiLocalAt` |
| `ε`, `ε₀` | `ClassWeight`, `actRate`, `WindowStrong` | the oscillation; `ε₀` fixed before `β` |
| `K = 16 · 4` | `actRate` | derived: the touch degree of the rectangular torus (`touchDeg_rbd_le`) |
| `r`, `ρ` | `ClusterBound`, the gap theorems | `r` the cluster rate; `ρ ≥ r` the gap rate, `0 < ρ ≤ 1` |
| `G`, `U` | `ClusterBound` | existential per test: the prefactor and the anchor size |
| `a` | `relayGap_of_pairDecay` | the floor of the kernel; `kTWmin` for a class weight |
| `a` | `QuasiLocalWith`, `WindowStrong` | the polymer decay weight `e^{a|X|}`, fixed before `β` |
| `λ`, `φ` | `GapPair` | existential: a positive top and its positive eigenfunction |
| `i`, `T` | slice lemmas | chosen; every aperture with positive extents |
| `j` | the hop lemmas | `j + 1` fine hops per window hop |
| `ρ₀` | `WindowHopGap`, `WindowHopMeasured` | the window-hop rate relative to the top, fixed |
| `C` | `WindowStrong`, `WindowHopMeasured` | a measured length: the window `2^k m′ ∈ [C, 2C]`, `(j + 1) m′ ≤ C` |
| `c = −log ρ₀ / C` | `transferGapMeasured_of_windowHop` | derived: the gap per hop in units of `m′` |
| `D` | `WindowHopMeasured` | existential, a measured length: the least side |
| `k`, `n` | `WindowStrong` | `k` the steps to the window, existential per `β`; `n` the coarse side, swept |
| `Z`, `R`, `D_X` | `QuasiLocalAt` | existential: normalization, polymer field, polymer bounds |
| `k′`, `n` | `PastPeak`, `coarseSusc` | `k′ ≥ k` swept; `n ≥ 2` the coarse side |
| `glue`, `π`, `E`, `ζ` | the skeleton lemmas | any measure-preserving parametrization and coarse projection |
| `m′` | the measured Props | measured: `(measMassOf (periodicState hN β) tensorEnergy).toReal` |

DERIVED (module-wide): `2` the Wilson density's range (so `ε = 2β`), the doubling of the window and the
square of the top; `16 · 4` the touch degree; `1` the kernel ceiling, the hop and the unit eigenfunction;
`4` the dimension and the quarter side of the anchor; `0` the degenerate coupling and the lower ends.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.WindowRelay

open MeasureTheory Filter Topology
open MassGap MassGap.RectWilson MassGap.RectTransfer MassGap.KernelPower MassGap.SlabKernelOperator
open MassGap.SubstrateDecode (measMassOf tensorEnergy)
open MassGap.PeriodicState (periodicState)
open MassGap.RelayChain (relayZ0)

/-! ## 1. The activity of a weight of oscillation `ε` -/

section Activity

/-- **A weight of oscillation `ε` has activity at most `e^{ε} − 1`**: for `m ≤ x ≤ m + ε`,
`|e^{−(x − m)} − 1| ≤ e^{ε} − 1`. DERIVED: `1` the factor at the minimum; `2` the sum `e^{ε} + e^{−ε} ≥ 2`. -/
theorem osc_activity {x m ε : ℝ} (hlo : m ≤ x) (hhi : x ≤ m + ε) :
    |Real.exp (-(x - m)) - 1| ≤ Real.exp ε - 1 := by
  have ha : Real.exp (-(x - m)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb : Real.exp (-ε) ≤ Real.exp (-(x - m)) := Real.exp_le_exp.mpr (by linarith)
  have hprod : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos ε
  have hposn := Real.exp_pos (-ε)
  have hsum : 2 ≤ Real.exp ε + Real.exp (-ε) := by
    nlinarith [sq_nonneg (Real.exp ε - 1)]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **The Wilson activity is the case `ε = 2β`**: `|e^{−β φ_W(g)} − 1| ≤ e^{2β} − 1` at `0 ≤ β`.
DERIVED: `2` the upper end of the Wilson density. -/
theorem wilson_activity {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (g : SUN.SU N) :
    |Real.exp (-(β * WilsonAction.wilsonDensity g)) - 1| ≤ Real.exp (2 * β) - 1 := by
  have h0 := WilsonAction.wilsonDensity_nonneg hN g
  have h2 := WilsonAction.wilsonDensity_le_two hN g
  have h := osc_activity (x := β * WilsonAction.wilsonDensity g) (m := 0) (ε := 2 * β)
    (by nlinarith) (by nlinarith)
  simpa using h

/-- **The cluster rate as a function of the activity's oscillation**: `actRate K ε = coreRate K (ε/2)`.
DERIVED: `2` the Wilson density's range. -/
def actRate (K : ℕ) (ε : ℝ) : ℝ := StrongCoupling.coreRate K (ε / 2)

/-- `actRate K ε = 4 (K + 1)² (e^{ε} − 1) e^{2Kε}`. DERIVED: `4`, `1`, `2` those of `coreRate`. -/
theorem actRate_eq (K : ℕ) (ε : ℝ) :
    actRate K ε = 4 * ((K : ℝ) + 1) ^ 2 * (Real.exp ε - 1) * Real.exp (2 * ε * K) := by
  unfold actRate StrongCoupling.coreRate
  rw [show 2 * (ε / 2) = ε by ring, show 4 * (ε / 2) * (K : ℝ) = 2 * ε * K by ring]

/-- **The Wilson rate is the activity rate at `ε = 2β`.** DERIVED: `2` the Wilson density's range. -/
theorem coreRate_eq_actRate (K : ℕ) (β : ℝ) :
    StrongCoupling.coreRate K β = actRate K (2 * β) := by
  unfold actRate
  congr 1
  ring

/-- `0 ≤ actRate K ε` at `0 ≤ ε`. DERIVED: `0`. -/
theorem actRate_nonneg (K : ℕ) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ actRate K ε :=
  StrongCoupling.coreRate_nonneg K (by linarith)

/-- **A fixed oscillation below which the rate is under one** on the rectangular torus.
DERIVED: `16 · 4` the touch degree. -/
theorem exists_actRate_lt_one :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → actRate (16 * 4) ε < 1 := by
  obtain ⟨b, hb, h⟩ := StrongCoupling.core_rate_lt_one_of_small_hypercubic 4
  exact ⟨b, hb, fun ε h0 h1 => h _ (by linarith) (by linarith)⟩

end Activity

/-! ## 2. The relay layer with the cluster bound as its input -/

section Generic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]

variable (μ) in
/-- **The cluster bound of a slice kernel at rate `r`**: for every continuous test `u` the two-slice
connected read of `k^{∗(j+1)}` is at most `G r^{j+2−U}` once `U ≤ j + 2`, with `G ≥ 0` and `U` depending on
`u`. DERIVED: `2` the two base plaquettes of the read. -/
def ClusterBound (k : X → X → ℝ) (r : ℝ) : Prop :=
  ∀ u : C(X, ℝ), ∃ G : ℝ, 0 ≤ G ∧ ∃ U : ℕ, ∀ j : ℕ, U ≤ j + 2 →
    |FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1 * u p.2)
        - FluxDuality.pairExp μ (iter μ k j) (fun p => u p.1)
          * FluxDuality.pairExp μ (iter μ k j) (fun p => u p.2)| ≤ G * r ^ (j + 2 - U)

variable (μ) in
/-- **A gapped top pair**: `λ > 0`, a bounded measurable unit eigenfunction `φ ≥ c₀ > 0` at `λ`, and the
remainder `k − λ φ⊗φ` of operator norm at most `ρ`. DERIVED: `1` the normalization; `0` the signs. -/
def GapPair (k : X → X → ℝ) (lam : ℝ) (φ : X → ℝ) (ρ : ℝ) : Prop :=
  0 < lam ∧ Measurable φ ∧ (∃ B : ℝ, ∀ x, |φ x| ≤ B) ∧ (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x, c₀ ≤ φ x) ∧
    ∫ x, φ x ^ 2 ∂μ = 1 ∧ (∀ z, ∫ y, k z y * φ y ∂μ = lam * φ z) ∧
    ∃ C : ℝ, ∃ hm : Measurable (Function.uncurry (rem k lam φ)), ∃ hC0 : 0 ≤ C,
      ∃ hb : ∀ x y, |rem k lam φ x y| ≤ C, ‖kernelCLM (rem k lam φ) C hm hC0 hb μ μ‖ ≤ ρ

/-- **The cluster bound gives two-slice decay** at every rate `ρ ≥ r`, `ρ > 0`. DERIVED: `1`, `2` the power
offsets. -/
theorem pairDecay_of_clusterBound {k : X → X → ℝ} {r ρ : ℝ} (hr0 : 0 ≤ r) (hrρ : r ≤ ρ)
    (hρ0 : 0 < ρ) (h : ClusterBound μ k r) : UniformRelayStrong.PairDecay μ k ρ := by
  intro u
  obtain ⟨G, hG0, U, hU⟩ := h u
  refine ⟨G * (ρ / ρ ^ U), U, fun j hj => ?_⟩
  refine (hU j (by omega)).trans ?_
  have hpow : r ^ (j + 2 - U) ≤ ρ ^ (j + 2 - U) := pow_le_pow_left₀ hr0 hrρ _
  have hρU : 0 < ρ ^ U := pow_pos hρ0 _
  have e : ρ ^ (j + 2 - U) = ρ ^ (j + 1) * (ρ / ρ ^ U) := by
    rw [eq_comm, mul_div_assoc', div_eq_iff hρU.ne', ← pow_succ, ← pow_add]
    congr 1; omega
  calc G * r ^ (j + 2 - U) ≤ G * ρ ^ (j + 2 - U) := mul_le_mul_of_nonneg_left hpow hG0
    _ = G * (ρ / ρ ^ U) * ρ ^ (j + 1) := by rw [e]; ring

/-- **The relay gap of any floored symmetric continuous kernel with two-slice decay at rate `ρ`**: a positive
top `λ` (the witness is `‖K‖`; the statement records only `λ > 0`) with a positive eigenfunction, and `‖K − λ φ⊗φ‖ ≤ λ ρ`. No coupling enters.
DERIVED: `1` the ceiling of the kernel. -/
theorem relayGap_of_pairDecay {k : X → X → ℝ} (hkc : Continuous (Function.uncurry k))
    (hsym : ∀ x y, k x y = k y x) {a : ℝ} (ha : 0 < a) (hlo : ∀ x y, a ≤ k x y)
    (hhi : ∀ x y, k x y ≤ 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hdec : UniformRelayStrong.PairDecay μ k ρ) :
    ∃ lam : ℝ, ∃ φ : X → ℝ, GapPair μ k lam φ (lam * ρ) := by
  have hk1 : ∀ x y, |k x y| ≤ 1 := fun x y => by
    rw [abs_le]; exact ⟨by linarith [hlo x y], hhi x y⟩
  obtain ⟨hpos, φ, hφm, hφb, ⟨c₀, hc₀, hlow⟩, hφ1, heig⟩ :=
    JentzschKT.exists_pos_eigen (μ := μ) hkc zero_le_one hk1 hsym ha hlo
  set lam := ‖kernelCLM k 1 hkc.measurable zero_le_one hk1 μ μ‖ with hlam
  have hk : Bdd k := ⟨hkc.measurable, 1, hk1⟩
  have hbr := Bdd.rem hk hφm hφb (c := lam)
  obtain ⟨Cr, hrb⟩ := hbr.bdd
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hrb x₀ x₀)
  have hgap := UniformRelayStrong.gap_of_pairDecay (μ := μ) hk hsym hφm hφb hφ1 heig hkc ha hlo hhi
    hc₀ hlow hpos hρ0 hρ1 hdec hbr.meas hCr0 hrb
  exact ⟨lam, φ, hpos, hφm, ⟨_, hφb⟩, ⟨c₀, hc₀, hlow⟩, hφ1, heig, Cr, hbr.meas, hCr0, hrb, hgap⟩

end Generic

section WilsonInstance

variable {N : ℕ} [NeZero N]

/-- **The Wilson slice transfer satisfies the cluster bound** at `coreRate 64 β`, at every aperture with
positive extents (`UniformRelayStrong.slice_pair_cluster`). DERIVED: `16 · 4` the touch degree; `64 |TT|` the
anchor size. -/
theorem clusterBound_kT {β : ℝ} (hβ : 0 ≤ β) (hr : StrongCoupling.coreRate (16 * 4) β < 1) (i : Fin 4)
    (T : {k : Fin 4 // k ≠ i} → ℕ) (hT : ∀ k, 0 < T k) :
    ClusterBound (hS i T N) (kT i T N β) (StrongCoupling.coreRate (16 * 4) β) := by
  intro u
  refine ⟨StrongCoupling.coreConstG (2 * (‖u‖ * ‖u‖)) (16 * 4) β (64 * Fintype.card (TT i T)), ?_,
    64 * Fintype.card (TT i T), fun j hj => ?_⟩
  · unfold StrongCoupling.coreConstG StrongCoupling.corePrefactorG
    have : (0 : ℝ) < 1 - StrongCoupling.coreRate (16 * 4) β := by linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)) this.le
  · exact UniformRelayStrong.slice_pair_cluster (NeZero.ne N) hβ hr i T hT j u hj

/-- **The Wilson relay gap through the general statement**: `clusterBound_kT`, `pairDecay_of_clusterBound`
and `relayGap_of_pairDecay` give `TransferGapAt` at `|λ| ρ` for every `coreRate 64 β ≤ ρ < 1`.
DERIVED: `16 · 4` the touch degree. -/
theorem wilson_relay_generic {β : ℝ} (hβ : 0 ≤ β) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hrβ : StrongCoupling.coreRate (16 * 4) β ≤ ρ) (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ)
    (hT : ∀ k, 0 < T k) :
    ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i T N → ℝ,
      SliceTransferGap.TransferGapAt N i T β lam φ (|lam| * ρ) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨lam, φ, hpos, hφm, hφb, -, hφ1, heig, C, hm, hC0, hb, hR⟩ :=
    relayGap_of_pairDecay (μ := hS i T N) (continuous_kT β) (kT_symm β) (kTmin_pos β)
      (kT_lower hN hβ) (kT_le_one hN hβ) hρ0 hρ1.le
      (pairDecay_of_clusterBound (StrongCoupling.coreRate_nonneg _ hβ) hrβ hρ0
        (clusterBound_kT hβ (lt_of_le_of_lt hrβ hρ1) i T hT))
  exact ⟨lam, φ, hφm, hφb, hφ1, hpos.ne', heig, C, hm, hC0, hb, by rwa [abs_of_pos hpos]⟩

end WilsonInstance

/-! ## 3. The slice transfer of a general plaquette weight -/

/-- **A class weight of oscillation `ε`**: continuous, invariant under conjugation and inversion, with values
in `[0, ε]`. DERIVED: `0` the shifted minimum. -/
structure ClassWeight {N : ℕ} (Ψ : SUN.SU N → ℝ) (ε : ℝ) : Prop where
  cont : Continuous Ψ
  conj : ∀ h g : SUN.SU N, Ψ (h * g * h⁻¹) = Ψ g
  inv : ∀ g : SUN.SU N, Ψ g⁻¹ = Ψ g
  nonneg : ∀ g, 0 ≤ Ψ g
  le : ∀ g, Ψ g ≤ ε

/-- A larger oscillation bound. DERIVED: no numeral. -/
theorem ClassWeight.mono {N : ℕ} {Ψ : SUN.SU N → ℝ} {ε ε' : ℝ} (hw : ClassWeight Ψ ε) (h : ε ≤ ε') :
    ClassWeight Ψ ε' :=
  ⟨hw.cont, hw.conj, hw.inv, hw.nonneg, fun g => (hw.le g).trans h⟩

/-- The oscillation bound of a class weight is nonnegative. DERIVED: `0`, `1` the identity element. -/
theorem ClassWeight.eps_nonneg {N : ℕ} {Ψ : SUN.SU N → ℝ} {ε : ℝ} (hw : ClassWeight Ψ ε) : 0 ≤ ε :=
  (hw.nonneg 1).trans (hw.le 1)

/-- **The Wilson weight `β φ_W` is a class weight of oscillation `2β`.** DERIVED: `2` the Wilson density's
range. -/
theorem classWeight_wilson {N : ℕ} (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    ClassWeight (fun g : SUN.SU N => β * WilsonAction.wilsonDensity g) (2 * β) where
  cont := continuous_const.mul WilsonAction.continuous_wilsonDensity
  conj h g := by simp only [WilsonAction.wilsonDensity_conj]
  inv g := by simp only [RectWilson.wilsonDensity_inv]
  nonneg g := mul_nonneg hβ (WilsonAction.wilsonDensity_nonneg hN g)
  le g := by
    show β * WilsonAction.wilsonDensity g ≤ 2 * β
    nlinarith [WilsonAction.wilsonDensity_le_two hN g, WilsonAction.wilsonDensity_nonneg hN g]

/-- The zero weight. DERIVED: `0`. -/
theorem classWeight_zero {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε) : ClassWeight (fun _ : SUN.SU N => (0 : ℝ)) ε :=
  ⟨continuous_const, fun _ _ => rfl, fun _ => rfl, fun _ => le_rfl, fun _ => hε⟩

section Weight

variable {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {N : ℕ} {Ψ : SUN.SU N → ℝ} {ε : ℝ}

variable (i T N) in
/-- The spatial action of one slice for the weight `Ψ`. DERIVED: no numeral. -/
def spW (Ψ : SUN.SU N → ℝ) (V : SpT i T → SUN.SU N) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ i}, ∑ ν' : {j : Fin 4 // j ≠ i}, ∑ y : TT i T,
    Ψ (V (ν, y) * V (ν', tsh i T ν y) * (V (ν, tsh i T ν' y))⁻¹ * (V (ν', y))⁻¹)

variable (i T N) in
/-- The temporal action between two slices for the weight `Ψ`, at the axis links `A`. DERIVED: no numeral. -/
def tpW (Ψ : SUN.SU N → ℝ) (A : TT i T → SUN.SU N) (V V' : SpT i T → SUN.SU N) : ℝ :=
  ∑ ν : {j : Fin 4 // j ≠ i}, ∑ y : TT i T,
    Ψ (A y * V' (ν, y) * (A (tsh i T ν y))⁻¹ * (V (ν, y))⁻¹)

variable (i T N) in
/-- The axis-integrated temporal factor for the weight `Ψ`. DERIVED: `2` the two orientations of a temporal
plaquette, as in `RectTransfer.gk`. -/
def gkW (Ψ : SUN.SU N → ℝ) (V V' : SpT i T → SUN.SU N) : ℝ :=
  ∫ A, Real.exp (-(2 * tpW i T N Ψ A V V')) ∂(hA i T N)

variable (i T N) in
/-- **The symmetric slice transfer of the weight `Ψ`.** DERIVED: `2` the half spatial action on each side. -/
def kTW (Ψ : SUN.SU N → ℝ) (V V' : SpT i T → SUN.SU N) : ℝ :=
  Real.exp (-(spW i T N Ψ V) / 2) * gkW i T N Ψ V V' * Real.exp (-(spW i T N Ψ V') / 2)

theorem continuous_tpW (hΨ : Continuous Ψ) {Y : Type*} [TopologicalSpace Y] {f : Y → TT i T → SUN.SU N}
    {g h : Y → SpT i T → SUN.SU N} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun q => tpW i T N Ψ (f q) (g q) (h q) := by
  unfold tpW
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun y _ => ?_
  refine hΨ.comp ?_
  have e1 : Continuous fun q => f q y := (continuous_apply y).comp hf
  have e2 : Continuous fun q => h q (ν, y) := (continuous_apply (ν, y)).comp hh
  have e3 : Continuous fun q => f q (tsh i T ν y) := (continuous_apply _).comp hf
  have e4 : Continuous fun q => g q (ν, y) := (continuous_apply (ν, y)).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_spW (hΨ : Continuous Ψ) {Y : Type*} [TopologicalSpace Y] {g : Y → SpT i T → SUN.SU N}
    (hg : Continuous g) : Continuous fun q => spW i T N Ψ (g q) := by
  unfold spW
  refine continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun ν' _ =>
    continuous_finsetSum _ fun y _ => ?_
  refine hΨ.comp ?_
  have e1 : Continuous fun q => g q (ν, y) := (continuous_apply _).comp hg
  have e2 : Continuous fun q => g q (ν', tsh i T ν y) := (continuous_apply _).comp hg
  have e3 : Continuous fun q => g q (ν, tsh i T ν' y) := (continuous_apply _).comp hg
  have e4 : Continuous fun q => g q (ν', y) := (continuous_apply _).comp hg
  exact ((e1.mul e2).mul e3.inv).mul e4.inv

theorem continuous_gkW (hΨ : Continuous Ψ) : Continuous (Function.uncurry (gkW i T N Ψ)) := by
  have hf0 : Continuous fun q : ((SpT i T → SUN.SU N) × (SpT i T → SUN.SU N)) × (TT i T → SUN.SU N) =>
      Real.exp (-(2 * tpW i T N Ψ q.2 q.1.1 q.1.2)) :=
    Real.continuous_exp.comp ((continuous_const.mul
      (continuous_tpW hΨ continuous_snd continuous_fst.fst continuous_fst.snd)).neg)
  have hf : Continuous (Function.uncurry fun (p : (SpT i T → SUN.SU N) × (SpT i T → SUN.SU N))
      (A : TT i T → SUN.SU N) => Real.exp (-(2 * tpW i T N Ψ A p.1 p.2))) := hf0
  have h := continuous_parametric_integral_of_continuous (μ := hA i T N) hf isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

/-- **The slice transfer of a continuous weight is jointly continuous.** DERIVED: `2` the halves. -/
theorem continuous_kTW (hΨ : Continuous Ψ) : Continuous (Function.uncurry (kTW i T N Ψ)) := by
  unfold kTW
  have h1 : Continuous fun p : (SpT i T → SUN.SU N) × (SpT i T → SUN.SU N) =>
      Real.exp (-(spW i T N Ψ p.1) / 2) :=
    Real.continuous_exp.comp ((continuous_spW hΨ continuous_fst).neg.div_const _)
  have h2 : Continuous fun p : (SpT i T → SUN.SU N) × (SpT i T → SUN.SU N) =>
      Real.exp (-(spW i T N Ψ p.2) / 2) :=
    Real.continuous_exp.comp ((continuous_spW hΨ continuous_snd).neg.div_const _)
  exact (h1.mul (continuous_gkW hΨ)).mul h2

/-- The reflection `A ↦ A⁻¹` exchanges the two slices of the temporal action; it uses conjugation and
inversion invariance of `Ψ`. DERIVED: no numeral. -/
theorem tpW_inv (hw : ClassWeight Ψ ε) (A : TT i T → SUN.SU N) (V V' : SpT i T → SUN.SU N) :
    tpW i T N Ψ (fun y => (A y)⁻¹) V' V = tpW i T N Ψ A V V' := by
  unfold tpW
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun y _ => ?_
  set a := A y
  set b := A (tsh i T ν y)
  set v := V (ν, y)
  set w := V' (ν, y)
  have e : a⁻¹ * v * (b⁻¹)⁻¹ * w⁻¹ = a⁻¹ * (a * w * b⁻¹ * v⁻¹)⁻¹ * a⁻¹⁻¹ := by group
  rw [e, hw.conj, hw.inv]

theorem gkW_symm (hw : ClassWeight Ψ ε) (V V' : SpT i T → SUN.SU N) :
    gkW i T N Ψ V V' = gkW i T N Ψ V' V := by
  set e := MeasurableEquiv.piCongrRight (fun _ : TT i T => MeasurableEquiv.inv (SUN.SU N))
  have hmp : MeasurePreserving e (hA i T N) (hA i T N) := measurePreserving_invAx
  unfold gkW
  rw [← hmp.integral_comp' (fun A => Real.exp (-(2 * tpW i T N Ψ A V' V)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  have hA' : (e A) = fun y => (A y)⁻¹ := rfl
  show Real.exp (-(2 * tpW i T N Ψ A V V')) = Real.exp (-(2 * tpW i T N Ψ (e A) V' V))
  rw [hA', tpW_inv hw]

/-- **The slice transfer of a class weight is symmetric.** DERIVED: no numeral. -/
theorem kTW_symm (hw : ClassWeight Ψ ε) (V V' : SpT i T → SUN.SU N) :
    kTW i T N Ψ V V' = kTW i T N Ψ V' V := by
  unfold kTW; rw [gkW_symm hw]; ring

theorem tpW_nonneg (hw : ClassWeight Ψ ε) (A : TT i T → SUN.SU N) (V V' : SpT i T → SUN.SU N) :
    0 ≤ tpW i T N Ψ A V V' :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hw.nonneg _

theorem spW_nonneg (hw : ClassWeight Ψ ε) (V : SpT i T → SUN.SU N) : 0 ≤ spW i T N Ψ V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hw.nonneg _

variable (i T) in
/-- A bound for `tpW`. DERIVED: no numeral. -/
def tpMaxW (ε : ℝ) : ℝ := ε * (Fintype.card {j : Fin 4 // j ≠ i} * Fintype.card (TT i T))

variable (i T) in
/-- A bound for `spW`. DERIVED: no numeral. -/
def spMaxW (ε : ℝ) : ℝ :=
  ε * (Fintype.card {j : Fin 4 // j ≠ i} * Fintype.card {j : Fin 4 // j ≠ i} * Fintype.card (TT i T))

theorem tpW_le (hw : ClassWeight Ψ ε) (A : TT i T → SUN.SU N) (V V' : SpT i T → SUN.SU N) :
    tpW i T N Ψ A V V' ≤ tpMaxW i T ε := by
  unfold tpW tpMaxW
  calc _ ≤ ∑ _ν : {j : Fin 4 // j ≠ i}, ∑ _y : TT i T, ε :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hw.le _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem spW_le (hw : ClassWeight Ψ ε) (V : SpT i T → SUN.SU N) : spW i T N Ψ V ≤ spMaxW i T ε := by
  unfold spW spMaxW
  calc _ ≤ ∑ _ν : {j : Fin 4 // j ≠ i}, ∑ _ν' : {j : Fin 4 // j ≠ i}, ∑ _y : TT i T, ε :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hw.le _
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem gkW_le_one (hw : ClassWeight Ψ ε) (V V' : SpT i T → SUN.SU N) : gkW i T N Ψ V V' ≤ 1 := by
  unfold gkW
  calc _ ≤ ∫ _A, (1 : ℝ) ∂(hA i T N) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun A => (Real.exp_pos _).le)
          (integrable_const _) (Filter.Eventually.of_forall fun A => ?_)
        rw [Real.exp_le_one_iff]
        have := tpW_nonneg hw A V V'
        linarith
    _ = 1 := by simp

theorem gkW_ge (hw : ClassWeight Ψ ε) (V V' : SpT i T → SUN.SU N) :
    Real.exp (-(2 * tpMaxW i T ε)) ≤ gkW i T N Ψ V V' := by
  unfold gkW
  have hm : Measurable fun A : TT i T → SUN.SU N => Real.exp (-(2 * tpW i T N Ψ A V V')) :=
    (Real.continuous_exp.comp ((continuous_const.mul
      (continuous_tpW hw.cont continuous_id continuous_const continuous_const)).neg)).measurable
  calc Real.exp (-(2 * tpMaxW i T ε)) = ∫ _A, Real.exp (-(2 * tpMaxW i T ε)) ∂(hA i T N) := by simp
    _ ≤ _ := by
        refine integral_mono (integrable_const _) ?_ (fun A => ?_)
        · exact integrable_of_bdd hm (C := 1) (fun A => by
            rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
            have := tpW_nonneg hw A V V'; linarith)
        · rw [Real.exp_le_exp]
          have := tpW_le hw A V V'
          linarith

/-- **The slice transfer of a nonnegative weight is at most `1`.** DERIVED: `1` the ceiling. -/
theorem kTW_le_one (hw : ClassWeight Ψ ε) (V V' : SpT i T → SUN.SU N) : kTW i T N Ψ V V' ≤ 1 := by
  unfold kTW
  have h1 : Real.exp (-(spW i T N Ψ V) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := spW_nonneg hw V; linarith
  have h2 : Real.exp (-(spW i T N Ψ V') / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := spW_nonneg hw V'; linarith
  have h3 := gkW_le_one hw V V'
  have h0 : 0 ≤ gkW i T N Ψ V V' := (Real.exp_pos _).le.trans (gkW_ge hw V V')
  exact mul_le_one₀ (mul_le_one₀ h1 h0 h3) (Real.exp_pos _).le h2

variable (i T) in
/-- The floor of the slice transfer of a weight of oscillation `ε`. DERIVED: `2` the halves and the
orientations. -/
def kTWmin (ε : ℝ) : ℝ :=
  Real.exp (-(spMaxW i T ε) / 2) * Real.exp (-(2 * tpMaxW i T ε)) * Real.exp (-(spMaxW i T ε) / 2)

theorem kTWmin_pos (ε : ℝ) : 0 < kTWmin i T ε := by unfold kTWmin; positivity

/-- **The slice transfer of a bounded weight has a positive floor.** DERIVED: no numeral. -/
theorem kTW_lower (hw : ClassWeight Ψ ε) (V V' : SpT i T → SUN.SU N) : kTWmin i T ε ≤ kTW i T N Ψ V V' := by
  unfold kTW kTWmin
  have h1 : Real.exp (-(spMaxW i T ε) / 2) ≤ Real.exp (-(spW i T N Ψ V) / 2) := by
    rw [Real.exp_le_exp]; have := spW_le hw V; linarith
  have h2 : Real.exp (-(spMaxW i T ε) / 2) ≤ Real.exp (-(spW i T N Ψ V') / 2) := by
    rw [Real.exp_le_exp]; have := spW_le hw V'; linarith
  have h3 := gkW_ge hw V V'
  have h0 : 0 ≤ Real.exp (-(2 * tpMaxW i T ε)) := (Real.exp_pos _).le
  exact mul_le_mul (mul_le_mul h1 h3 h0 (Real.exp_pos _).le) h2 (Real.exp_pos _).le
    (mul_nonneg (Real.exp_pos _).le (h0.trans h3))

theorem spW_wilson (β : ℝ) (V : SpT i T → SUN.SU N) :
    spW i T N (fun g => β * WilsonAction.wilsonDensity g) V = β * spT i T V := by
  unfold spW spT; simp only [Finset.mul_sum]

theorem tpW_wilson (β : ℝ) (A : TT i T → SUN.SU N) (V V' : SpT i T → SUN.SU N) :
    tpW i T N (fun g => β * WilsonAction.wilsonDensity g) A V V' = β * tpT i T A V V' := by
  unfold tpW tpT; simp only [Finset.mul_sum]

/-- **At `Ψ = β φ_W` the slice transfer of the weight is the Wilson slice transfer.** DERIVED: `2` the
halves and the orientations. -/
theorem kTW_wilson (β : ℝ) (V V' : SpT i T → SUN.SU N) :
    kTW i T N (fun g => β * WilsonAction.wilsonDensity g) V V' = kT i T N β V V' := by
  have hg : gkW i T N (fun g => β * WilsonAction.wilsonDensity g) V V' = gk i T N β V V' := by
    unfold gkW gk
    congr 1
    funext A
    rw [tpW_wilson]
    congr 1
    ring
  unfold kTW kT
  rw [hg, spW_wilson, spW_wilson]
  have e1 : -(β * spT i T V) / 2 = -β * spT i T V / 2 := by ring
  have e2 : -(β * spT i T V') / 2 = -β * spT i T V' / 2 := by ring
  rw [e1, e2]

variable (N) in
/-- **The cluster bound of the slice transfer of `Ψ`** at rate `r`, at every aperture with positive extents
(assumed for a general weight; proved for the Wilson weight, `weightCluster_wilson`). DERIVED: `0` the
extent bound. -/
def WeightCluster (Ψ : SUN.SU N → ℝ) (r : ℝ) : Prop :=
  ∀ (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ), (∀ k, 0 < T k) →
    ClusterBound (hS i T N) (kTW i T N Ψ) r

/-- **The relay gap of a class weight from its cluster bound**, at every aperture, with one rate.
DERIVED: `1` the ceiling of the rate. -/
theorem relayGapW (hw : ClassWeight Ψ ε) {r ρ : ℝ} (hr0 : 0 ≤ r) (hrρ : r ≤ ρ) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hcl : WeightCluster N Ψ r) (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ)
    (hT : ∀ k, 0 < T k) :
    ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i T N → ℝ, GapPair (hS i T N) (kTW i T N Ψ) lam φ (lam * ρ) :=
  relayGap_of_pairDecay (continuous_kTW hw.cont) (kTW_symm hw) (kTWmin_pos (i := i) (T := T) ε)
    (kTW_lower hw) (kTW_le_one hw) hρ0 hρ1 (pairDecay_of_clusterBound hr0 hrρ hρ0 (hcl i T hT))

/-- **The relay gap of a weight of oscillation `ε`** at every rate `ρ ≥ actRate 64 ε`, from the cluster bound
at the activity rate. DERIVED: `16 · 4` the touch degree. -/
theorem relayGap_of_osc (hw : ClassWeight Ψ ε) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hact : actRate (16 * 4) ε ≤ ρ) (hcl : WeightCluster N Ψ (actRate (16 * 4) ε)) (i : Fin 4)
    (T : {k : Fin 4 // k ≠ i} → ℕ) (hT : ∀ k, 0 < T k) :
    ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i T N → ℝ, GapPair (hS i T N) (kTW i T N Ψ) lam φ (lam * ρ) :=
  relayGapW hw (actRate_nonneg _ hw.eps_nonneg) hact hρ0 hρ1 hcl i T hT

/-- **The Wilson weight satisfies `WeightCluster`** at `actRate 64 (2β) = coreRate 64 β`. DERIVED: `16 · 4`
the touch degree; `2` the Wilson density's range. -/
theorem weightCluster_wilson [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hr : StrongCoupling.coreRate (16 * 4) β < 1) :
    WeightCluster N (fun g => β * WilsonAction.wilsonDensity g) (actRate (16 * 4) (2 * β)) := by
  intro i T hT
  have e : kTW i T N (fun g => β * WilsonAction.wilsonDensity g) = kT i T N β :=
    funext fun V => funext fun V' => kTW_wilson β V V'
  rw [e, ← coreRate_eq_actRate]
  exact clusterBound_kT hβ hr i T hT

/-- **The Wilson case as an instance of the general statement**: `classWeight_wilson`,
`weightCluster_wilson` and `relayGap_of_osc` give the Wilson relay gap at every `coreRate 64 β ≤ ρ < 1`.
DERIVED: `16 · 4` the touch degree; `2` the Wilson density's range. -/
theorem wilson_relayGap_via_weight [NeZero N] {β : ℝ} (hβ : 0 ≤ β) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hrβ : StrongCoupling.coreRate (16 * 4) β ≤ ρ) (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ)
    (hT : ∀ k, 0 < T k) :
    ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i T N → ℝ, GapPair (hS i T N) (kT i T N β) lam φ (lam * ρ) := by
  have e : kTW i T N (fun g => β * WilsonAction.wilsonDensity g) = kT i T N β :=
    funext fun V => funext fun V' => kTW_wilson β V V'
  have h := relayGap_of_osc (classWeight_wilson (NeZero.ne N) hβ) hρ0 hρ1.le
    (by rw [← coreRate_eq_actRate]; exact hrβ)
    (weightCluster_wilson hβ (lt_of_le_of_lt hrβ hρ1)) i T hT
  rwa [e] at h

end Weight

/-! ## 4. Transport in time: a window hop of `j + 1` fine hops -/

section Hop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A bound on a power of a symmetric operator bounds the operator**: `‖A^b‖ ≤ ρ^b`, `b ≥ 1`, `ρ > 0` give
`‖A‖ ≤ ρ`. Each vector decays at rate `ρ` (`t = r + b q`, `‖A^t f‖ ≤ ‖A‖^r ρ^{bq} ‖f‖`), and
`StrongTransferGap.opNorm_le_of_decay` turns per-vector decay into the operator bound. DERIVED: `1` the least
power. -/
theorem norm_le_of_norm_pow_le {A : E →L[ℝ] E} (hA : ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    {b : ℕ} (hb : 1 ≤ b) {ρ : ℝ} (hρ : 0 < ρ) (h : ‖A ^ b‖ ≤ ρ ^ b) : ‖A‖ ≤ ρ := by
  refine StrongTransferGap.opNorm_le_of_decay hA hρ.le fun f => ?_
  set M := max 1 (‖A‖ / ρ) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hAM : ‖A‖ ≤ M * ρ := (div_le_iff₀ hρ).mp (le_max_right _ _)
  refine ⟨M ^ b * ‖f‖, fun t => ?_⟩
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < b ∧ t = r + b * q :=
    ⟨t / b, t % b, Nat.mod_lt _ (by omega), (Nat.mod_add_div t b).symm⟩
  have e : A ^ (r + b * q) = A ^ r * (A ^ b) ^ q := by rw [pow_add, pow_mul]
  rw [e, mul_apply_eq_comp]
  have h1 := StrongTransferGap.norm_pow_apply_le A (((A ^ b) ^ q) f) r
  have h2 := StrongTransferGap.norm_pow_apply_le (A ^ b) f q
  have h3 : ‖A ^ b‖ ^ q ≤ (ρ ^ b) ^ q := pow_le_pow_left₀ (norm_nonneg _) h q
  have h4 : ‖A‖ ^ r ≤ M ^ b * ρ ^ r := by
    calc ‖A‖ ^ r ≤ (M * ρ) ^ r := pow_le_pow_left₀ (norm_nonneg _) hAM r
      _ = M ^ r * ρ ^ r := mul_pow _ _ _
      _ ≤ M ^ b * ρ ^ r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hr.le) (pow_nonneg hρ.le _)
  have hMb : 0 ≤ M ^ b * ρ ^ r := mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hρ.le _)
  calc ‖(A ^ r) (((A ^ b) ^ q) f)‖ ≤ ‖A‖ ^ r * ‖((A ^ b) ^ q) f‖ := h1
    _ ≤ (M ^ b * ρ ^ r) * ((ρ ^ b) ^ q * ‖f‖) :=
        mul_le_mul h4 (h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))) (norm_nonneg _) hMb
    _ = M ^ b * ‖f‖ * ρ ^ (r + b * q) := by rw [pow_add, pow_mul]; ring

end Hop

section KernelHop

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The `(j+1)`-th power of a kernel operator is the operator of the iterated kernel.** DERIVED: `1` the
first power. -/
theorem kernelCLM_pow {r : X → X → ℝ} (hr : Bdd r) {C : ℝ} (hm : Measurable (Function.uncurry r))
    (hC0 : 0 ≤ C) (hb : ∀ x y, |r x y| ≤ C) (j : ℕ) {C' : ℝ}
    (hm' : Measurable (Function.uncurry (iter μ r j))) (hC0' : 0 ≤ C')
    (hb' : ∀ x y, |iter μ r j x y| ≤ C') :
    (kernelCLM r C hm hC0 hb μ μ) ^ (j + 1) = kernelCLM (iter μ r j) C' hm' hC0' hb' μ μ := by
  ext1 f
  apply Lp.ext
  filter_upwards [UniformRelayStrong.pow_apply_ae hr hm hC0 hb f j,
    coeFn_kernelCLM (iter μ r j) C' hm' hC0' hb' μ μ f] with x h1 h2
  rw [h1, h2]
  rfl

variable {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
  {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B)
  (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z)

include hk hsym hφm hφb hφ1 heig in
/-- **The remainder of the window hop is the window hop of the remainder**:
`K^{∗(j+1)} − c^{j+1} φ⊗φ = R^{∗(j+1)}` (`KernelPower.iter_decomp`). DERIVED: `1` the hop. -/
theorem rem_iter_eq (j : ℕ) : rem (iter μ k j) (c ^ (j + 1)) φ = iter μ (rem k c φ) j := by
  funext x z
  show iter μ k j x z - c ^ (j + 1) * φ x * φ z = iter μ (rem k c φ) j x z
  rw [iter_decomp hk hsym hφm hφb hφ1 heig j x z]
  ring

include hk hsym hφm hφb hφ1 heig in
/-- **A window-hop gap is a one-hop gap**: if the remainder of `K^{∗(j+1)}` has operator norm at most
`ρ^{j+1}`, the remainder of `K` has operator norm at most `ρ`. Exact; no rate is lost. DERIVED: `1` the hop. -/
theorem gap_of_hop_gap {C : ℝ} (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C)
    (hb : ∀ x y, |rem k c φ x y| ≤ C) (j : ℕ) {C' : ℝ}
    (hm' : Measurable (Function.uncurry (rem (iter μ k j) (c ^ (j + 1)) φ))) (hC0' : 0 ≤ C')
    (hb' : ∀ x y, |rem (iter μ k j) (c ^ (j + 1)) φ x y| ≤ C') {ρ : ℝ} (hρ : 0 < ρ)
    (hhop : ‖kernelCLM (rem (iter μ k j) (c ^ (j + 1)) φ) C' hm' hC0' hb' μ μ‖ ≤ ρ ^ (j + 1)) :
    ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ := by
  have hrsym : ∀ x y, rem k c φ x y = rem k c φ y x := by
    intro x y
    simp only [MassGap.KernelPower.rem]
    rw [hsym x y]
    ring
  have hA : ∀ u v, inner ℝ (kernelCLM (rem k c φ) C hm hC0 hb μ μ u) v
      = inner ℝ u (kernelCLM (rem k c φ) C hm hC0 hb μ μ v) :=
    fun u v => (SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm _ C hm hC0 hb μ hrsym).isSymmetric u v
  have hbr := Bdd.rem hk hφm hφb (c := c)
  have key : ∀ K : X → X → ℝ, K = iter μ (rem k c φ) j →
      ∀ (hmK : Measurable (Function.uncurry K)) (hbK : ∀ x y, |K x y| ≤ C'),
      ‖kernelCLM K C' hmK hC0' hbK μ μ‖ ≤ ρ ^ (j + 1) → ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ := by
    intro K hK hmK hbK hK'
    subst hK
    rw [← kernelCLM_pow hbr hm hC0 hb j hmK hC0' hbK] at hK'
    exact norm_le_of_norm_pow_le hA (Nat.le_add_left 1 j) hρ hK'
  exact key _ (rem_iter_eq hk hsym hφm hφb hφ1 heig j) hm' hb' hhop

include hk hsym hφm hφb hφ1 heig in
/-- **A one-hop gap is a window-hop gap**: `‖R‖ ≤ ρ` gives `‖R^{∗(j+1)}‖ ≤ ρ^{j+1}`. DERIVED: `1` the hop. -/
theorem hop_of_gap {C : ℝ} (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C)
    (hb : ∀ x y, |rem k c φ x y| ≤ C) (j : ℕ) {C' : ℝ}
    (hm' : Measurable (Function.uncurry (rem (iter μ k j) (c ^ (j + 1)) φ))) (hC0' : 0 ≤ C')
    (hb' : ∀ x y, |rem (iter μ k j) (c ^ (j + 1)) φ x y| ≤ C') {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hgap : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ) :
    ‖kernelCLM (rem (iter μ k j) (c ^ (j + 1)) φ) C' hm' hC0' hb' μ μ‖ ≤ ρ ^ (j + 1) := by
  have hbr := Bdd.rem hk hφm hφb (c := c)
  have key : ∀ K : X → X → ℝ, K = iter μ (rem k c φ) j →
      ∀ (hmK : Measurable (Function.uncurry K)) (hbK : ∀ x y, |K x y| ≤ C'),
      ‖kernelCLM K C' hmK hC0' hbK μ μ‖ ≤ ρ ^ (j + 1) := by
    intro K hK hmK hbK
    subst hK
    rw [← kernelCLM_pow hbr hm hC0 hb j hmK hC0' hbK]
    refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hρ _) fun f => ?_
    refine (StrongTransferGap.norm_pow_apply_le _ f (j + 1)).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hgap _) (norm_nonneg _)
  exact key _ (rem_iter_eq hk hsym hφm hφb hφ1 heig j) hm' hb'

end KernelHop

section WindowHop

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The window-hop gap**: `φ` is a bounded measurable unit eigenfunction of the slice transfer at `λ ≠ 0`, and
the remainder of the window hop `K^{∗(j+1)}` (top `λ^{j+1}`) has operator norm at most `|λ|^{j+1} ρ₀`.
DERIVED: `1` the hop and the normalization. -/
def WindowHopGap (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) (lam : ℝ)
    (φ : SliceCentreAction.Cfg i T N → ℝ) (ρ₀ : ℝ) : Prop :=
  Measurable φ ∧ (∃ B : ℝ, ∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂(hS i T N) = 1 ∧ lam ≠ 0 ∧
    (∀ z, ∫ y, kT i T N β z y * φ y ∂(hS i T N) = lam * φ z) ∧
    ∃ C : ℝ, ∃ hm : Measurable (Function.uncurry (rem (iter (hS i T N) (kT i T N β) j) (lam ^ (j + 1)) φ)),
      ∃ hC0 : 0 ≤ C, ∃ hb : ∀ x y, |rem (iter (hS i T N) (kT i T N β) j) (lam ^ (j + 1)) φ x y| ≤ C,
        ‖kernelCLM (rem (iter (hS i T N) (kT i T N β) j) (lam ^ (j + 1)) φ) C hm hC0 hb
          (hS i T N) (hS i T N)‖ ≤ |lam| ^ (j + 1) * ρ₀

/-- **The window-hop gap gives the one-hop transfer gap**: `ρ₀ ≤ q^{j+1}`, `q > 0` give `TransferGapAt` at
`|λ| q`. DERIVED: `1` the hop. -/
theorem transferGapAt_of_windowHop {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {j : ℕ} {lam : ℝ} {φ : SliceCentreAction.Cfg i T N → ℝ} {ρ₀ : ℝ}
    (h : WindowHopGap N i T β j lam φ ρ₀) {q : ℝ} (hq : 0 < q) (hρq : ρ₀ ≤ q ^ (j + 1)) :
    SliceTransferGap.TransferGapAt N i T β lam φ (|lam| * q) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hl0, heig, C', hm', hC0', hb', hhop⟩ := h
  have hk := bdd_kT (μ := i) (T := T) hN hβ
  have hbr := Bdd.rem hk hφm hφb (c := lam)
  obtain ⟨Cr, hrb⟩ := hbr.bdd
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (hS i T N)
  have hCr0 : 0 ≤ Cr := (abs_nonneg _).trans (hrb x₀ x₀)
  have hl : 0 < |lam| := abs_pos.mpr hl0
  have hhop' : ‖kernelCLM (rem (iter (hS i T N) (kT i T N β) j) (lam ^ (j + 1)) φ) C' hm' hC0' hb'
      (hS i T N) (hS i T N)‖ ≤ (|lam| * q) ^ (j + 1) := by
    refine hhop.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hρq (pow_nonneg hl.le _)
  refine ⟨hφm, ⟨B, hφb⟩, hφ1, hl0, heig, Cr, hbr.meas, hCr0, hrb, ?_⟩
  exact gap_of_hop_gap hk (kT_symm β) hφm hφb hφ1 heig hbr.meas hCr0 hrb j hm' hC0' hb'
    (mul_pos hl hq) hhop'

/-- **The one-hop transfer gap gives the window-hop gap** (the converse: the time window is a restatement).
DERIVED: `1` the hop. -/
theorem windowHop_of_transferGapAt {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ} (hβ : 0 ≤ β)
    {lam : ℝ} {φ : SliceCentreAction.Cfg i T N → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (h : SliceTransferGap.TransferGapAt N i T β lam φ (|lam| * q)) (j : ℕ) :
    WindowHopGap N i T β j lam φ (q ^ (j + 1)) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hl0, heig, C, hm, hC0, hb, hR⟩ := h
  have hk := bdd_kT (μ := i) (T := T) hN hβ
  have hbj := Bdd.rem (hk.iter (μ := hS i T N) j) hφm hφb (c := lam ^ (j + 1))
  obtain ⟨Cj, hCj⟩ := hbj.bdd
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (hS i T N)
  have hCj0 : 0 ≤ Cj := (abs_nonneg _).trans (hCj x₀ x₀)
  refine ⟨hφm, ⟨B, hφb⟩, hφ1, hl0, heig, Cj, hbj.meas, hCj0, hCj, ?_⟩
  have h' := hop_of_gap hk (kT_symm β) hφm hφb hφ1 heig hm hC0 hb j hbj.meas hCj0 hCj
    (mul_nonneg (abs_nonneg _) hq) hR
  rwa [mul_pow] at h'

/-- **The window arithmetic**: at `(j + 1) m ≤ C`, `C > 0`, `0 < ρ₀ < 1`, the rate `ρ₀` per window hop is at
least the rate `e^{−c m}` per fine hop with `c = −log ρ₀ / C`. DERIVED: `1` the hop. -/
theorem rate_of_window {m C ρ₀ : ℝ} {b : ℕ} (hC : 0 < C) (hbm : (b : ℝ) * m ≤ C) (hρ0 : 0 < ρ₀)
    (hρ1 : ρ₀ < 1) : ρ₀ ≤ (Real.exp (-((-Real.log ρ₀ / C) * m))) ^ b := by
  rw [← Real.exp_nat_mul]
  conv_lhs => rw [← Real.exp_log hρ0]
  rw [Real.exp_le_exp]
  have hl : Real.log ρ₀ < 0 := Real.log_neg hρ0 hρ1
  have ht : (b : ℝ) * m / C ≤ 1 := (div_le_one hC).mpr hbm
  have e : (b : ℝ) * -((-Real.log ρ₀ / C) * m) = Real.log ρ₀ * ((b : ℝ) * m / C) := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonpos_left ht hl.le
  linarith

/-- The measured mass in lattice units. DERIVED: no numeral. -/
abbrev mprime {M : ℕ} (hM : M ≠ 0) (β : ℝ) : ℝ := (measMassOf (periodicState hM β) tensorEnergy).toReal

variable (N) in
/-- **The window-hop gap along the measured tower** (assumed): there is a measured length `D > 0` such that,
eventually in `β`, `m′ > 0`, and at every power-of-two side `n ≥ 2` with `D ≤ n m′` and every direction, some
window of `j + 1` hops with `(j + 1) m′ ≤ C` has the window-hop gap at the fixed rate `ρ₀`, and an anchor at
`c = −log ρ₀ / C`. DERIVED: `2` the least side and the square of the top; `4` the quarter side; `1` the hop. -/
def WindowHopMeasured (hN : N ≠ 0) (C ρ₀ : ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ᶠ β in atTop, 0 < mprime hN β ∧
    ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n → D ≤ (n : ℝ) * mprime hN β → ∀ i : Fin 4,
      ∃ j : ℕ, ((j + 1 : ℕ) : ℝ) * mprime hN β ≤ C ∧
        ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i (CentreSectorSeed.Tr n i) N → ℝ, ∃ j₀ : ℕ,
          WindowHopGap N i (CentreSectorSeed.Tr n i) β j lam φ ρ₀ ∧ 4 * (j₀ + 1) ≤ n ∧
          lam ^ 2 * relayZ0 N i (CentreSectorSeed.Tr n i) β j₀
            ≤ Real.exp ((-Real.log ρ₀ / C) * mprime hN β) * relayZ0 N i (CentreSectorSeed.Tr n i) β (j₀ + 1)

/-- **The window-hop gap along the measured tower gives `TransferGapMeasured`**, with `c = −log ρ₀ / C`.
DERIVED: `1` the hop. -/
theorem transferGapMeasured_of_windowHop (hN : N ≠ 0) {C ρ₀ : ℝ} (hC : 0 < C) (hρ0 : 0 < ρ₀)
    (hρ1 : ρ₀ < 1) (h : WindowHopMeasured N hN C ρ₀) : SliceTransferGap.TransferGapMeasured N hN := by
  obtain ⟨D, hD, hev⟩ := h
  have hc : 0 < -Real.log ρ₀ / C := div_pos (neg_pos.mpr (Real.log_neg hρ0 hρ1)) hC
  refine ⟨-Real.log ρ₀ / C, hc, D, hD, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβ hβ0
  refine ⟨hβ.1, fun n hn h2 hDn i => ?_⟩
  obtain ⟨j, hjm, lam, φ, j₀, hhop, hj₀, hanc⟩ := hβ.2 n hn h2 hDn i
  have hρq := rate_of_window (b := j + 1) hC hjm hρ0 hρ1
  refine ⟨lam, φ, |lam| * Real.exp (-((-Real.log ρ₀ / C) * mprime hN β)), j₀,
    transferGapAt_of_windowHop hβ0 hhop (Real.exp_pos _) hρq, le_rfl, hj₀, hanc⟩

end WindowHop

/-! ## 5. Transport in space: the skeleton reads are exact -/

section Skeleton

variable {Ωf Ωc Ωr Bf Bc : Type*} [MeasurableSpace Ωf] [MeasurableSpace Ωc] [MeasurableSpace Ωr]
  {μf : Measure Ωf} {μc : Measure Ωc} {μr : Measure Ωr} [SFinite μc] [SFinite μr]
  {glue : Ωc × Ωr → Ωf}

/-- **A skeleton observable has the same integral against the fine density and the effective density**:
for a measure-preserving `glue` with a coarse projection `π ∘ glue = fst`,
`∫ F(π U) ρ(E ζ, U) dμf = ∫ F(V) ρ_eff(ζ, V) dμc`. DERIVED: no numeral. -/
theorem integral_skeleton (hg : MeasurePreserving glue (μc.prod μr) μf) {π : Ωf → Ωc}
    (hπ : ∀ V R, π (glue (V, R)) = V) (E : Bc → Bf) (ρ : Bf → Ωf → ℝ) (ζ : Bc) (F : Ωc → ℝ)
    (hint : Integrable (fun U => F (π U) * ρ (E ζ) U) μf) :
    ∫ U, F (π U) * ρ (E ζ) U ∂μf
      = ∫ V, F V * GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc := by
  rw [← GapSideExactDecimation.integral_glue hg hint]
  congr 1
  funext V
  simp only [hπ]
  unfold GapSideExactDecimation.effDens
  exact integral_const_mul _ _

/-- **The normalized expectation of a skeleton observable is the effective one.** In particular every
two-slice connected read of skeleton observables is the same on the fine torus and on the coarse one.
DERIVED: no numeral. -/
theorem expect_skeleton (hg : MeasurePreserving glue (μc.prod μr) μf) {π : Ωf → Ωc}
    (hπ : ∀ V R, π (glue (V, R)) = V) (E : Bc → Bf) (ρ : Bf → Ωf → ℝ) (ζ : Bc) (F : Ωc → ℝ)
    (hint : Integrable (fun U => F (π U) * ρ (E ζ) U) μf) (hρ : Integrable (ρ (E ζ)) μf) :
    (∫ U, F (π U) * ρ (E ζ) U ∂μf) / (∫ U, ρ (E ζ) U ∂μf)
      = (∫ V, F V * GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc)
        / (∫ V, GapSideExactDecimation.effDens μr glue E ρ ζ V ∂μc) := by
  rw [integral_skeleton hg hπ E ρ ζ F hint, ← GapSideExactDecimation.Z_effDens hg ρ E ζ hρ]

end Skeleton

/-! ## 6. The window input -/

section Window

/-- The fine Wilson weight `β φ_W` on `SU(2)`. DERIVED: no numeral. -/
def wilsonW (β : ℝ) : SUN.SU 2 → ℝ := fun g => β * WilsonAction.wilsonDensity g

/-- **A quasi-local representation of a coarse density around the plaquette weight `Ψ`**:
`ρ(V) = Z exp(−Σ_q Ψ(hol_q V) + Σ_X R_X(V))` with `R_X` reading only the links of `X`, `|R_X| ≤ D_X` and
the size-weighted sum `Σ_{X ∋ q} D_X e^{a|X|} ≤ ε₀` at every plaquette. The weight `e^{a|X|}` excludes polymers
whose bounds fall only as a power of their extent, which would allow power-law decay of the two-point read.
DERIVED: `4` the dimension. -/
def QuasiLocalWith {n : ℕ} (Ψ : SUN.SU 2 → ℝ) (ρ : (TorusDoubling.TLink 4 n → SUN.SU 2) → ℝ)
    (ε₀ a : ℝ) : Prop :=
  ∃ Z : ℝ, 0 < Z ∧
    ∃ R : Finset (TorusDoubling.TPlaq 4 n) → (TorusDoubling.TLink 4 n → SUN.SU 2) → ℝ,
    ∃ Dp : Finset (TorusDoubling.TPlaq 4 n) → ℝ,
      (∀ X V V', (∀ q ∈ X, ∀ l ∈ (TorusDoubling.tbd 4 n q).map Prod.fst, V l = V' l) → R X V = R X V') ∧
      (∀ X V, |R X V| ≤ Dp X) ∧
      (∀ q, ∑ X ∈ Finset.univ.filter (fun X => q ∈ X), Dp X * Real.exp (a * X.card) ≤ ε₀) ∧
      ∀ V, ρ V = Z * Real.exp (-(∑ q, Ψ (HolderBondMoving.thol q V)) + ∑ X, R X V)

/-- **A quasi-local representation of a coarse density with small oscillation**: `QuasiLocalWith` around some
class weight `Ψ` of oscillation `ε₀`, polymer decay weight `a`. DERIVED: `4` the dimension. -/
def QuasiLocalAt {n : ℕ} (ρ : (TorusDoubling.TLink 4 n → SUN.SU 2) → ℝ) (ε₀ a : ℝ) : Prop :=
  ∃ Ψ : SUN.SU 2 → ℝ, ClassWeight Ψ ε₀ ∧ QuasiLocalWith Ψ ρ ε₀ a

/-- The summed coarse plaquette action `Σ_q φ_W(hol_q V)` on the side-`n` torus. DERIVED: no numeral. -/
def coarseAction {n : ℕ} (V : TorusDoubling.TLink 4 n → SUN.SU 2) : ℝ :=
  ∑ q : TorusDoubling.TPlaq 4 n, WilsonAction.wilsonDensity (HolderBondMoving.thol q V)

/-- **The crossover read: the coarse plaquette susceptibility.** The variance of the summed coarse plaquette
action under the normalized `k`-step effective density of the `SU(2)` Wilson torus at `β`, on the coarse torus
of side `n`, per coarse plaquette. It is the specific-heat read of the coarse theory: at fixed weight the
variance of the action is the second `β`-derivative of `log Z` (`EffectiveCoupling.hasDerivAt_logZR` gives the
first, `d/dβ log Z = −⟨S⟩`), and its peak is where the crossover of the coupling axis sits. Read through the
coarse projection of `glueStep` composed over `k` steps and `integral_skeleton` (argued, not built), it is the
variance of the summed fine Wilson loops of side `2^k` on the fine torus of side `2^k n`, per loop: a read of
the fine theory at block scale `2^k m′`, in measured units. DERIVED: `2` the square; `1` the trivial
background. -/
def coarseSusc (β : ℝ) (k n : ℕ) : ℝ :=
  let ρ := GapSideExactDecimation.effIter k n (GapSideExactDecimation.fineDens (wilsonW β)) (fun _ => 1)
  ((∫ V, coarseAction V ^ 2 * ρ V ∂(GapSideExactDecimation.piL n)) / (∫ V, ρ V ∂(GapSideExactDecimation.piL n))
    - ((∫ V, coarseAction V * ρ V ∂(GapSideExactDecimation.piL n))
        / (∫ V, ρ V ∂(GapSideExactDecimation.piL n))) ^ 2)
    / (Fintype.card (TorusDoubling.TPlaq 4 n) : ℝ)

/-- **The zoom is past the crossover from step `k` on**: at every coarse side `n ≥ 2`, the coarse plaquette
susceptibility does not rise under any further exact step. The peak of the read (the Widom-type line of the
zoom, where fluctuation and response are largest relative to the block) lies at or before step `k`. Side `1` is
excluded: there every plaquette is a commutator of wrapping lines. DERIVED: `1` the step; `2` the least side. -/
def PastPeak (β : ℝ) (k : ℕ) : Prop :=
  ∀ n k' : ℕ, 2 ≤ n → k ≤ k' → coarseSusc β (k' + 1) n ≤ coarseSusc β k' n

/-- **`WindowStrong ε₀ a C`: the observer sees strong coupling at its own scale, beyond the crossover**
(assumed). Eventually in `β`, `m′ > 0`, and there is a window `k` with `C ≤ 2^k m′ ≤ 2C` such that the zoom is
past the crossover from `k` on (`PastPeak`) and the `k`-step exact effective density of the `SU(2)` Wilson
torus has, at every coarse side `n ≥ 1`, a quasi-local representation with oscillation `ε₀` and polymer decay
weight `a`. `ε₀`, `a` and `C` are fixed before `β`. Nothing is asked at any step before `k`. DERIVED: `2` the
doubling of the window and the gauge group; `1` the trivial background. -/
def WindowStrong (ε₀ a C : ℝ) : Prop :=
  ∀ᶠ β in atTop, 0 < mprime (M := 2) two_ne_zero β ∧ ∃ k : ℕ,
    C ≤ (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ∧
    (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ≤ 2 * C ∧ PastPeak β k ∧
    ∀ n : ℕ, 0 < n →
      QuasiLocalAt (GapSideExactDecimation.effIter k n (GapSideExactDecimation.fineDens (wilsonW β))
        (fun _ => 1)) ε₀ a

/-- **The window density is reached in one exact decimation, with no control at intermediate steps**: its
partition function at every background is that of the fine Wilson torus at the pulled-back background. The
only input is continuity of the fine weight; no bound on `effIter j` for `j < k` enters, so the steps through
the crossover need no control. DERIVED: `1` the trivial background. -/
theorem window_Z_exact (β : ℝ) (k n : ℕ) (ζ : TorusDoubling.TPlaq 4 n → SUN.SU 2) :
    GapSideExactDecimation.ZE (GapSideExactDecimation.effIter k n
        (GapSideExactDecimation.fineDens (wilsonW β))) ζ
      = GapSideExactDecimation.ZE (GapSideExactDecimation.fineDens (wilsonW β))
          (GapSideExactDecimation.pullIter k n ζ) :=
  (GapSideExactDecimation.effIter_spec k n _ (fun ζ' => GapSideExactDecimation.integrable_fineDens
    (continuous_const.mul WilsonAction.continuous_wilsonDensity) ζ') ζ).2

/-- **The cluster bound for every class weight of oscillation `ε₀`** at the activity rate (assumed; the Wilson
weights are `weightCluster_wilson`). DERIVED: `16 · 4` the touch degree; `2` the gauge group. -/
def OscCluster (ε₀ : ℝ) : Prop :=
  ∀ Ψ : SUN.SU 2 → ℝ, ClassWeight Ψ ε₀ → WeightCluster 2 Ψ (actRate (16 * 4) ε₀)

/-- **What `WindowStrong` gives through the plaquette weight**: with `OscCluster ε₀` and
`actRate 64 ε₀ ≤ ρ ≤ 1`, eventually in `β`, at the window, at every coarse side, the plaquette weight `Ψ` of the
representation that `WindowStrong` supplies has the uniform relay gap `λ ρ` at every aperture. `Ψ` is not
determined by the density (argued, module docstring §3), so this carries no information about the window
density by itself. DERIVED: `16 · 4` the touch degree; `2` the
window's doubling and the gauge group. -/
theorem window_plaquette_relay {ε₀ a C ρ : ℝ} (h : WindowStrong ε₀ a C) (hcl : OscCluster ε₀)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hact : actRate (16 * 4) ε₀ ≤ ρ) :
    ∀ᶠ β in atTop, ∃ k : ℕ, C ≤ (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ∧
      (2 : ℝ) ^ k * mprime (M := 2) two_ne_zero β ≤ 2 * C ∧ ∀ n : ℕ, 0 < n →
      ∃ Ψ : SUN.SU 2 → ℝ, ClassWeight Ψ ε₀ ∧
        QuasiLocalWith Ψ (GapSideExactDecimation.effIter k n
          (GapSideExactDecimation.fineDens (wilsonW β)) (fun _ => 1)) ε₀ a ∧
        ∀ (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ), (∀ k, 0 < T k) →
          ∃ lam : ℝ, ∃ φ : SliceCentreAction.Cfg i T 2 → ℝ,
            GapPair (hS i T 2) (kTW i T 2 Ψ) lam φ (lam * ρ) := by
  filter_upwards [h] with β hβ
  obtain ⟨-, k, hk1, hk2, -, hn⟩ := hβ
  refine ⟨k, hk1, hk2, fun n hn0 => ?_⟩
  obtain ⟨Ψ, hw, hq⟩ := hn n hn0
  exact ⟨Ψ, hw, hq, fun i T hT => relayGap_of_osc hw hρ0 hρ1 hact (hcl Ψ hw) i T hT⟩

/-- **Every exact step keeps the constant density `1`.** DERIVED: `1` the constant; `2` the doubling. -/
theorem effIter_one : ∀ k n : ℕ,
    GapSideExactDecimation.effIter k n (fun _ _ => (1 : ℝ)) = fun _ _ => 1
  | 0, _ => rfl
  | k + 1, n => by
    show GapSideExactDecimation.effStep n
      (GapSideExactDecimation.effIter k (2 * n) (fun _ _ => (1 : ℝ))) = _
    rw [effIter_one k (2 * n)]
    funext ζ V
    simp [GapSideExactDecimation.effStep, GapSideExactDecimation.effDens]

/-- The fine Wilson density at `β = 0` is `1`. DERIVED: `0` the coupling. -/
theorem fineDens_wilsonW_zero (N : ℕ) :
    GapSideExactDecimation.fineDens (N := N) (wilsonW 0) = fun _ _ => 1 := by
  funext ζ U
  simp [GapSideExactDecimation.fineDens, wilsonW, HolderBondMoving.fAct]

/-- **Test at `β = 0`**: the clause of `WindowStrong` holds at every `k`, every coarse side and every
`ε₀ ≥ 0`, with `Ψ = 0`, `R = 0`, `Z = 1`. DERIVED: `0` the coupling; `1` the normalization. -/
theorem quasiLocal_zero_coupling (k n : ℕ) {ε₀ : ℝ} (hε : 0 ≤ ε₀) (a : ℝ) :
    QuasiLocalAt (GapSideExactDecimation.effIter k n (GapSideExactDecimation.fineDens (wilsonW 0))
      (fun _ => 1)) ε₀ a := by
  rw [fineDens_wilsonW_zero, effIter_one]
  refine ⟨fun _ => 0, classWeight_zero hε, 1, one_pos, fun _ _ => 0, fun _ => 0,
    fun _ _ _ _ => rfl, fun _ _ => by simp, fun _ => by simpa using hε, fun V => by simp⟩

/-- **Test with zero decimation steps**: the clause is the fine Wilson weight, `Ψ = β φ_W`, `R = 0`, and holds
when `2β ≤ ε₀`. DERIVED: `2` the Wilson density's range; `1` the trivial background. -/
theorem quasiLocal_zero_steps (n : ℕ) {β ε₀ : ℝ} (hβ : 0 ≤ β) (hε : 2 * β ≤ ε₀) (a : ℝ) :
    QuasiLocalAt (GapSideExactDecimation.effIter 0 n (GapSideExactDecimation.fineDens (wilsonW β))
      (fun _ => 1)) ε₀ a := by
  have hw : ClassWeight (wilsonW β) ε₀ := (classWeight_wilson two_ne_zero hβ).mono hε
  have hε0 : 0 ≤ ε₀ := hw.eps_nonneg
  refine ⟨wilsonW β, hw, 1, one_pos, fun _ _ => 0, fun _ => 0,
    fun _ _ _ _ => rfl, fun _ _ => by simp, fun _ => by simpa using hε0, fun V => ?_⟩
  show GapSideExactDecimation.fineDens (wilsonW β) (fun _ => 1) V = _
  simp [GapSideExactDecimation.fineDens, HolderBondMoving.fAct]

/-- **Test of the crossover read at `β = 0`**: the effective density is `1` at every step, the read is the
Haar variance at every block scale, and every step is past the peak (there is no crossover to pass).
DERIVED: `0` the coupling. -/
theorem pastPeak_zero_coupling (k : ℕ) : PastPeak 0 k := by
  intro n k' _ _
  simp only [coarseSusc, fineDens_wilsonW_zero, effIter_one, le_refl]

end Window

end MassGap.WindowRelay

end

#print axioms MassGap.WindowRelay.osc_activity
#print axioms MassGap.WindowRelay.wilson_activity
#print axioms MassGap.WindowRelay.actRate_eq
#print axioms MassGap.WindowRelay.coreRate_eq_actRate
#print axioms MassGap.WindowRelay.actRate_nonneg
#print axioms MassGap.WindowRelay.exists_actRate_lt_one
#print axioms MassGap.WindowRelay.pairDecay_of_clusterBound
#print axioms MassGap.WindowRelay.relayGap_of_pairDecay
#print axioms MassGap.WindowRelay.clusterBound_kT
#print axioms MassGap.WindowRelay.wilson_relay_generic
#print axioms MassGap.WindowRelay.ClassWeight.mono
#print axioms MassGap.WindowRelay.ClassWeight.eps_nonneg
#print axioms MassGap.WindowRelay.classWeight_wilson
#print axioms MassGap.WindowRelay.classWeight_zero
#print axioms MassGap.WindowRelay.continuous_tpW
#print axioms MassGap.WindowRelay.continuous_spW
#print axioms MassGap.WindowRelay.continuous_gkW
#print axioms MassGap.WindowRelay.continuous_kTW
#print axioms MassGap.WindowRelay.tpW_inv
#print axioms MassGap.WindowRelay.gkW_symm
#print axioms MassGap.WindowRelay.kTW_symm
#print axioms MassGap.WindowRelay.tpW_nonneg
#print axioms MassGap.WindowRelay.spW_nonneg
#print axioms MassGap.WindowRelay.tpW_le
#print axioms MassGap.WindowRelay.spW_le
#print axioms MassGap.WindowRelay.gkW_le_one
#print axioms MassGap.WindowRelay.gkW_ge
#print axioms MassGap.WindowRelay.kTW_le_one
#print axioms MassGap.WindowRelay.kTWmin_pos
#print axioms MassGap.WindowRelay.kTW_lower
#print axioms MassGap.WindowRelay.spW_wilson
#print axioms MassGap.WindowRelay.tpW_wilson
#print axioms MassGap.WindowRelay.kTW_wilson
#print axioms MassGap.WindowRelay.relayGapW
#print axioms MassGap.WindowRelay.relayGap_of_osc
#print axioms MassGap.WindowRelay.weightCluster_wilson
#print axioms MassGap.WindowRelay.wilson_relayGap_via_weight
#print axioms MassGap.WindowRelay.norm_le_of_norm_pow_le
#print axioms MassGap.WindowRelay.kernelCLM_pow
#print axioms MassGap.WindowRelay.rem_iter_eq
#print axioms MassGap.WindowRelay.gap_of_hop_gap
#print axioms MassGap.WindowRelay.hop_of_gap
#print axioms MassGap.WindowRelay.transferGapAt_of_windowHop
#print axioms MassGap.WindowRelay.windowHop_of_transferGapAt
#print axioms MassGap.WindowRelay.rate_of_window
#print axioms MassGap.WindowRelay.transferGapMeasured_of_windowHop
#print axioms MassGap.WindowRelay.integral_skeleton
#print axioms MassGap.WindowRelay.expect_skeleton
#print axioms MassGap.WindowRelay.window_plaquette_relay
#print axioms MassGap.WindowRelay.effIter_one
#print axioms MassGap.WindowRelay.fineDens_wilsonW_zero
#print axioms MassGap.WindowRelay.quasiLocal_zero_coupling
#print axioms MassGap.WindowRelay.quasiLocal_zero_steps
#print axioms MassGap.WindowRelay.window_Z_exact
#print axioms MassGap.WindowRelay.pastPeak_zero_coupling
