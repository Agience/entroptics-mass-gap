import Mathlib
import MassGap.MeasuredSpacing
import MassGap.FluxShareSquaring

/-!
# MassGap.TorusContraction — the wrapping part of the reads: a flux-sector hop gap on the relay transfer

`ContractionReads` shows that a local kernel-near contraction gives the lock and the block pair decay but none of
the three reads, because the reads wrap the torus. This module names what wraps, states one torus-level
contraction in measured units, and proves that it gives `GapFromReads.LongChainRead` and the flux clause of
`SubstrateFluxRead.SectorSeedMeasured` at every large measured side, so that with `ZeroFluxGap.ZeroFluxReadsMass`
alone it gives the sector seed and the observer's gap; `RelayChain.CoarseReadsFine` is not used. Declarations are
in the namespace `MassGap.TorusContraction`.

## 1. Which wrapping observable each read needs (analysis)

On the slice transverse to `i` with aperture `T`, `K = kT i T N β` is the one-hop transfer and the centre
`Z_N³ = Cen i N` acts by `act g`: it multiplies the links of direction `ν` at `ν`-coordinate `0` by `e(g_ν)`. The
chain reads at index `j` are traces of `K^{2(j+1)}`:

* `Z = relayZ = Tr K^{2(j+1)}`, the partition function of the torus with time extent `2(j + 1)` and aperture `T`;
* `Z_g = relayTwist g = Tr (K^{2(j+1)} act g)`, the same torus with `act g` inserted at one time slice;
* `Z₀ = relayZ0 = N⁻³ Σ_g Z_g` (`ZeroFluxSector.hs_zk_eq_mean`) and the flux trace `F = Z − Z₀` (`fluxTrace`).

The three reads use them as follows.

* `CoarseReadsFine`: the flux odds `F/Z₀` at the two tori `(2T, j)` and `(T, 2j + 1)`, so all `Z_g` on both tori.
  It compares two twisted partition functions whose winding-direction-by-time areas are equal.
* `LongChainRead`: the flux odds `F/Z₀` at the corner aperture `Tr n i`, over all chain lengths. These are the same
  twisted partition functions, at one aperture.
* `ZeroFluxReadsMass`: the zero-flux kernel `K₀ = zk K` (`zk` averages `K(x, act g y)` over the centre), an
  eigenfunction `φ` of a whole slice, the remainder norm and the excited weight. These are functions of the full
  slice configuration, so they wrap the three transverse directions, and they use the centre average but no flux
  sector.

Every one of these is a function of a whole time slice, or a trace that closes the time direction. None is
local in a box whose reduction modulo the extents is injective, so `PeriodicStateDLR.torusState_dlr` does not
reach any of them (`ContractionReads` §4 (b)).

## 2. The interface picture, and its direction (analysis; one part proved)

The joint twist `(x, y) ↦ (act g x, act g y)` leaves the transfer unchanged (`SliceCentreAction.kT_act`), as the
time-slice twist leaves the Wilson action and Haar unchanged (`MeasureN.action_twist`, `MeasureN.EW_twist`). It is
a symmetry. The relative twist `(x, y) ↦ (x, act g y)` is not. `Z_g/Z` is the partition function with a centre
twist across the planes `(i, ν)`, an 't Hooft twist, relative to the untwisted one, and `F_g = −log(Z_g/Z) ≥ 0`
(`relayTwist_le`) is its free energy. `FluxDuality.fluxShareN_isLeast` reads `1 − fluxShare` as the least mean affinity (an `IsLeast`) of the two-slice law with its image under the relative twist.

The direction needs care. A small flux share means the twist costs little, not much:

* `relayShare_eq_meanCost` (proved): `relayShare = N⁻³ Σ_g (1 − Z_g/Z)`, with every term nonnegative (`twistCost_nonneg`); each is also below `1` because `Z_g > 0` from the kernel floor
(not proved here);
* `twistCost_le` (proved): `1 − Z_g/Z ≤ N³ · relayShare` for every `g`.

So the flux share is small iff every 't Hooft twist free energy `F_g` is small. This is 't Hooft's criterion: in
the confined phase the twist (a centre vortex sheet) is free, and `VortexStrong.vortexR_le_card` bounds this free energy for `SU(2)` at small `β` on the rectangular tori, which
`GapSideVortexRect.twist_iter_eq_ZRtw` and `ZRtw_single` identify with `relayTwist` at `N = 2`. The free energy that must be large is that of the Fourier dual. The
electric flux sectors `Z_e = N⁻³ Σ_g χ_e(g) Z_g` have `relayOdds = Σ_{e ≠ 0} Z_e/Z₀`, and the cost of `e ≠ 0` is
that of a flux sheet spanning the winding direction `ν` and the time extent (argued). So "the flux share is small
iff the interface free energy is large" is right with "interface" read as the electric flux sheet, whose free
energy should grow with its area
`T_ν · 2(j + 1)` in measured units (argued). It is reversed if "interface" is read as the 't Hooft twist, whose
free energy must vanish.

The area cost splits into a cost per hop (the sheet's width `T_ν` times one lattice time step) and a count (the
`T_k T_l` transverse positions and the momenta of the sheet). The count is extensive in the aperture. That is why
the odds form of a decay carries an aperture-dependent prefactor (`LongChainRead`'s `B` per band), and why
`KernelDecayAt` carries the factor `min(|A|, 4(2σ+1)⁴)`. The Prop below asks only for the per-hop cost. The count
enters once, at an anchor, where the proved sector bound `relayOdds_le_card` caps it by `N³ − 1`.

Comparison. `CoarseReadsFine` is argued as `E(2T) ≥ 2E(T)` for the flux energy per hop, a superadditivity across
apertures. `LongChainRead` is a decay in chain length at a bounded measured aperture with a band-dependent
prefactor. The hop gap below is a lower bound `E(T) ≥ s m′` per hop at every aperture with `T m′ ≥ D`, compared
with the zero-flux rate at an anchor. It asks no comparison across apertures.

## 3. The hop gap (assumed)

A slab, one time slice wrapped in all three transverse directions, conditioned on its two neighbours, is one hop
`K`. So a contraction of the torus specification conditioned on whole slices is a statement about `K`. Its flux
part is `fk(K^{∗ k}) = K^{∗ k} − zk(K^{∗ k})` (`RelayChain.fk`), whose trace is `F`. Two hop rates are
monotone along the chain by log-convexity (for `F` where it is positive) (`ratio_mono`, from `relayZ0_sq_le` and `relayFlux_sq_le`). The flux
rate `F(k+1)/F(k)` increases to the top flux eigenvalue squared, and the zero-flux rate `Z₀(k+1)/Z₀(k)` increases
to the top zero-flux eigenvalue squared (spectral reading argued; no module computes a spectrum of `kT`).

**`HopClause N i T β j₀ q`**: `∀ k ≥ j₀, F(k+1) · Z₀(j₀) ≤ q · F(k) · Z₀(j₀+1)`. The flux hop rate at every
`k ≥ j₀` is at most `q` times the zero-flux hop rate at the anchor `j₀`.

**`FluxHopGap N hN`**: there are `s > 0` and `D > 0` such that, eventually in `β`, at every power-of-two side
`n ≥ 2` with `D ≤ n m′` and every direction `i`, some anchor `j₀` with `4(j₀ + 1) ≤ n` has
`HopClause N i (Tr n i) β j₀ (e^{−2 s m′})`. Here `m′ = (measMassOf (periodicState hN β) tensorEnergy).toReal`.

In measured units: one chain index adds two lattice time steps to the trace (`2(j + 1)`), that is `2m′` measured
lengths, and the flux sector loses at least the factor `e^{−s · 2m′}` per index, relative to the zero-flux sector
at the anchor. `s` and `D` are fixed before `β`, the side and the direction; the anchor sits within half the cubic chain
(`2(j₀ + 1) ≤ n/2`).

`hopClause_of_eventually` (proved): if the inequality holds for all large `k`, it holds for all `k`. So the clause
reads one number of the flux sector, the asymptotic hop rate (by log-convexity of `F`), against one number of
the zero-flux sector, the hop rate at `j₀`. It is a gap of the twisted transfer relative to the untwisted one.

## 4. What it gives (proved)

* `relayOdds_le_hop`: `HopClause … j₀ q` gives `relayOdds j ≤ q^{j − j₀} (N³ − 1)` for `j ≥ j₀`, from `odds_decay`
  (zero-flux log-convexity turns the anchor comparison into `o(k+1) ≤ q o(k)` for every `k ≥ j₀`) and the anchor
  bound `relayOdds_le_card`.
* `relayOdds_le_of_hop`: at `q = e^{−2 s m}`, for every `j`,
  `relayOdds j ≤ (N³ − 1) e^{s (2(j₀+1) m − 2(j+1) m)}`.
* **`longChainRead_of_hopGap`**: `FluxHopGap → LongChainRead`, with the same `s`, `D` and
  `B = (N³ − 1) e^{s D′/2}` on the band `D′`.
* `fluxShareN_le_of_hop`: at an even side `n` with `s n m′ ≥ 2 log(80000 N³)`, the hop clause at `Tr n i` gives
  `fluxShareN N β n i ≤ 1/80000`, the flux clause of `SectorSeedMeasured` at that side, with no doubling and no
  across-aperture step.
* **`sectorSeedMeasured_of_hopGap`**: `FluxHopGap → ZeroFluxReadsMass → SectorSeedMeasured`. The seed side is a
  power of two in `[X, max(2X, 2C₀)]` measured, `X = max(D, C_z, 2 log(80000 N³)/s)`.
* **`observerGap_of_hopGap`**: with a measured tower, the observer's transfer gap
  (`MeasuredSpacing.observerGap_of_sectorSeed`). The route's inputs are `FluxHopGap` and `ZeroFluxReadsMass`.

`FluxHopGap` is pointwise in `β`: no step uses the coupling path `[0, β]` that `ContractionReads.sectors_of_path`
needs.

## 5. Strong coupling (what is missing)

No instance of the whole Prop is built. It is asked along `β → ∞`, and an instance at small `β` would not be one.
The per-coupling clause at small `β` is also not proved. `hopClause_of_growth` (proved) says what would give it:
if `F > 0` and, for each `k ≥ j₀`, some `t ≥ 1` has `F(k + t) ≤ (q Z₀(j₀+1)/Z₀(j₀))^t F(k)`, the clause holds
(log-convexity: `(F(k+1)/F(k))^t ≤ F(k+t)/F(k)`, `hopRate_pow_le`, `rate_le_of_growth`). Three bounds are needed
and the tree has none of them in this form:

1. a lower bound on the flux trace `F(k)`, that is, a lower bound on the 't Hooft twist cost `1 − Z_g/Z`
   (equivalently an upper bound on the electric flux free energy). The tree proves only upper bounds on the
   sector reads (`SubstrateFluxRead.sectors_strong`, `VortexStrong.vortexR_le_card`), and Cauchy–Schwarz with the measure-preserving twist gives `Z_g ≤ Z` (`relayTwist_le`), which is only the lower
bound `0` on the cost;
2. an upper bound on `F(k + t)` relative to `F(k)` at a fixed aperture over growing `t`, a sheet-tension estimate
   per hop. `sectors_strong` bounds the share only at the chain length tied to the side (`n/2 − 1` at `Tr n i`);
3. a lower bound on the zero-flux hop rate `Z₀(j₀+1)/Z₀(j₀)` against the asymptotic flux rate. The tree has only
   the pointwise floor `kTmin^{j+1} ≤ K^{∗(j+1)}` (`RelayChain.low_iterK`), which gives `Z₀ ≥ kTmin^{2(j+1)}` and no
   comparison with `F`.

At leading order in the character expansion (argued) item 1 is the single-sheet term `≈ T_k T_l u^{T_ν · 2(j+1)}`
and item 2 is the factor `u^{2T_ν}` per two hops, so in lattice units the clause holds at `q ≈ u^{2 min_ν T_ν}`, at most `u^{2n}` (the transverse extents of `Tr n i`
are `n` or `2n`), with `u`
the fundamental character coefficient. The strong-coupling rate is that of `LongChainRead`'s test 2.

## 6. Tests

1. Degenerate coupling (proved). `hopClause_zero_coupling`: at `β = 0` the flux trace is `0` at every index
   (`fluxTrace_zero_coupling`, from `RelayChain.relayOdds_zero_coupling`), so the clause holds at every `q`; the
   Prop is read along `β → ∞`, so this tests the per-coupling clause only.
2. Vacuity (proved and argued). `not_hopClause_of_floor` (proved): if the odds do not fall below some `ε > 0`
   along the chain, no anchor and no `q < 1` satisfy the clause. At a finite slice the floor is never met (argued: `K` has a strictly positive kernel, so by Jentzsch its top
eigenvector is simple and centre-invariant, `|λ_F| < λ₀` and the odds tend to `0`; under a gap `ρ < |λ|` (`SliceTransferGap.TransferGapAt`, `β ≥ 0`) the top
is simple and centre-invariant: `SliceTransferGap.top_of_gap`, `SliceTransferGap.phi_act_kT`); at each `(β, T)` the clause
holds at some `q < 1` for a large anchor. The content of `FluxHopGap` is the uniform rate `q = e^{−2 s m′}` at every
side with `D ≤ n m′` and the anchor cap `4(j₀ + 1) ≤ n`; in a deconfined regime `λ_F/λ₀ → 1` as the aperture grows
(argued), and that uniform clause fails. `D > 0` is needed: at `m′ = 0`
   no side meets `D ≤ n m′`, so the Prop says nothing there. The lock comes from `ZeroFluxReadsMass`
   (`sectorSeedMeasured_of_hopGap`). `s` is per measured length, `D` is a measured length, and `q = e^{−2 s m′}`
   tends to `1` as `m′ → 0`, so the clause is never asked at a fixed lattice-unit rate.
3. Restatement against reduction. It is a reduction of `LongChainRead` (proved: `longChainRead_of_hopGap`) and of
   the flux clause at every large measured side (proved: `fluxShareN_le_of_hop`), so with `ZeroFluxReadsMass` it
   replaces `CoarseReadsFine` and `LongChainRead` in the sector seed. It is not their restatement:
   `LongChainRead` bounds the odds on bounded measured bands with a band-dependent prefactor, which allows the
   odds to rise and fall along the chain, while the hop clause asks the flux hop rate (one number, by
   `hopClause_of_eventually`) against one zero-flux hop rate at every aperture with `T m′ ≥ D` (argued: `LongChainRead` does not imply it, since it allows a prefactor growing faster than `e^{s D′/2}` and says
nothing of the zero-flux rate at the anchor; the converse is `longChainRead_of_hopGap`. Against `CoarseReadsFine`,
neither implies the other (argued).). It says nothing about the zero-flux clause: `trivialDefectN` is not a function of the
   hop rates' comparison (argued: bounding it by the zero-flux rates alone leaves the extensive `log Z₀(0)`).
4. The aperture count (argued). The anchor absorbs the transverse count. For a dilute glueball gas in the slice,
   `Z₀(j₀+1)/Z₀(j₀)` falls short of its limit by a factor `≈ exp(−c m (T m)³ e^{−2(j₀+1) m})`, so the anchor must
   sit at `2(j₀ + 1) m ≳ 3 log(T m)`. That is below `n m/2` once `n m` is large, which the clause `4(j₀+1) ≤ n`
   allows, and above any fixed measured length. So an anchor fixed in measured units before the side would fail
   at large `T m`, and the Prop does not ask for one.
5. Trivial centre (argued). At `N = 1` the centre `Z_1³` is trivial, `Z₀ = Z` and `F = 0`; the clause holds at
   every `q` and the Prop gives only what the zero-flux input gives.

## 7. Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: the Jentzsch reading (at a finite slice the top eigenvector is simple and centre-invariant, so the
  flux odds tend to `0` and the content of `FluxHopGap` is the uniform measured rate); the spectral reading of the hop rates, the electric-sheet reading of `relayOdds`, the leading-order
  strong-coupling values, the aperture count of test 4, and the "neither implies the other" of test 3.
* Assumed: `FluxHopGap N hN`, only in `longChainRead_of_hopGap`, `sectorSeedMeasured_of_hopGap` and
  `observerGap_of_hopGap`; `ZeroFluxReadsMass` in the last two.

## 8. Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every read | shared, in the substrate; `FluxHopGap` is read along `β → ∞` |
| `i` (direction), `T` (aperture) | `fluxTrace`, `HopClause` | chosen; `T = Tr n i` in `FluxHopGap` |
| `n` (side) | `FluxHopGap`, `fluxShareN_le_of_hop` | swept: every power of two `≥ 2` with `D ≤ n m′` |
| `j₀` (anchor) | `HopClause`, `FluxHopGap` | existential per `(β, n, i)`, at most `n/4 − 1` hops |
| `k`, `j`, `t` (chain indices) | `HopClause`, the decay lemmas | swept |
| `q` (hop factor) | `HopClause` | `e^{−2 s m′}` in `FluxHopGap`; chosen in the lemmas |
| `s`, `D` | `FluxHopGap` | existential, fixed before `β`; `s` per measured length, `D` a measured length |
| `D′`, `B` | `longChainRead_of_hopGap` | `D′` swept (band), `B = (N³ − 1) e^{s D′/2}` derived |
| `X`, `C` | `sectorSeedMeasured_of_hopGap` | derived: `X = max(D, C_z, 2 log(80000 N³)/s)`, `C = max(2X, 2C₀)` |
| `g` (centre element) | `relayTwist`, the twist-cost lemmas | swept over `Z_N³` |
| `ε` | `not_hopClause_of_floor` | chosen: any floor on the odds |
| `m′` | `FluxHopGap`, the seed | measured: `(measMassOf (periodicState hN β) tensorEnergy).toReal` |
| `N` | the type | shared with the substrate |

DERIVED (module-wide): `1` the hop and the zero-flux trace's normalization; `2` the two time directions of a hop
in `2(j + 1)`, the square of log-convexity, the half cubic chain and the doubling base of the window; `4` the
quarter side, `2(j₀ + 1) ≤ n/2`; `3` in `N³ = |Z_N³|` (`SliceCentreAction.card_cen`); `N³ − 1` the largest
odds; `80000`, `1/80000` the threshold of `SectorSeedMeasured`; `0` the degenerate coupling.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.TorusContraction

open Filter Topology
open scoped ENNReal NNReal
open MassGap.RelayChain (relayZ relayZ0 relayTwist relayShare relayOdds relayZ0_pos relayZ0_le relayZ_pos
  relayOdds_le_card relayShare_le_odds relayShare_eq_mean relayZ0_sq_le relayFlux_sq_le relayOdds_zero_coupling
  fluxShareN_eq_relay bdd_iterK)
open MassGap.ZeroFluxGap (ZeroFluxReadsMass zeroFluxClause_of_reads)
open MassGap.SubstrateFluxRead (SectorSeedMeasured)
open MassGap.SubstrateDecode (measMassOf tensorEnergy)
open MassGap.PeriodicState (periodicState)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)
open MassGap.SliceCentreAction (Cen act centreAction card_cen)

/-! ## 1. Sequences with log-convex traces -/

section Real

variable {F Z : ℕ → ℝ}

/-- **The hop rate of a log-convex positive sequence increases**: `Z(j₀+1) Z(k) ≤ Z(j₀) Z(k+1)` for `k ≥ j₀`.
DERIVED: `1` the hop; `2` the square of log-convexity. -/
theorem ratio_mono (hZ : ∀ k, 0 < Z k) (hlc : ∀ k, Z (k + 1) ^ 2 ≤ Z k * Z (k + 1 + 1)) (j₀ : ℕ) :
    ∀ k, j₀ ≤ k → Z (j₀ + 1) * Z k ≤ Z j₀ * Z (k + 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_of_eq (mul_comm _ _)
  | succ k hk ih =>
    have h1 : Z (j₀ + 1) * Z (k + 1) * Z (k + 1) ≤ Z j₀ * Z (k + 1 + 1) * Z (k + 1) := by
      calc Z (j₀ + 1) * Z (k + 1) * Z (k + 1) = Z (j₀ + 1) * Z (k + 1) ^ 2 := by ring
        _ ≤ Z (j₀ + 1) * (Z k * Z (k + 1 + 1)) := mul_le_mul_of_nonneg_left (hlc k) (hZ _).le
        _ = (Z (j₀ + 1) * Z k) * Z (k + 1 + 1) := by ring
        _ ≤ (Z j₀ * Z (k + 1)) * Z (k + 1 + 1) := mul_le_mul_of_nonneg_right ih (hZ _).le
        _ = Z j₀ * Z (k + 1 + 1) * Z (k + 1) := by ring
    exact le_of_mul_le_mul_right h1 (hZ (k + 1))

/-- **One hop of the odds**: the anchor comparison and the increasing zero-flux rate give
`F(k+1)/Z(k+1) ≤ q · F(k)/Z(k)`. DERIVED: `1` the hop. -/
theorem odds_step (hZ : ∀ k, 0 < Z k) {j₀ k : ℕ} {q : ℝ} (hq : 0 ≤ q) (hF : 0 ≤ F k)
    (hH : F (k + 1) * Z j₀ ≤ q * F k * Z (j₀ + 1)) (hr : Z (j₀ + 1) * Z k ≤ Z j₀ * Z (k + 1)) :
    F (k + 1) / Z (k + 1) ≤ q * (F k / Z k) := by
  have key : F (k + 1) * Z k * Z j₀ ≤ q * F k * Z (k + 1) * Z j₀ :=
    calc F (k + 1) * Z k * Z j₀ = (F (k + 1) * Z j₀) * Z k := by ring
      _ ≤ (q * F k * Z (j₀ + 1)) * Z k := mul_le_mul_of_nonneg_right hH (hZ k).le
      _ = (q * F k) * (Z (j₀ + 1) * Z k) := by ring
      _ ≤ (q * F k) * (Z j₀ * Z (k + 1)) := mul_le_mul_of_nonneg_left hr (mul_nonneg hq hF)
      _ = q * F k * Z (k + 1) * Z j₀ := by ring
  have k2 := le_of_mul_le_mul_right key (hZ j₀)
  have h := (div_le_div_iff₀ (hZ (k + 1)) (hZ k)).mpr k2
  rwa [mul_div_assoc] at h

/-- **The odds decay from the anchor**: `F(j)/Z(j) ≤ q^{j − j₀} F(j₀)/Z(j₀)` for `j ≥ j₀`.
DERIVED: `1` the hop; `0` the empty power. -/
theorem odds_decay (hZ : ∀ k, 0 < Z k) (hF : ∀ k, 0 ≤ F k)
    (hlc : ∀ k, Z (k + 1) ^ 2 ≤ Z k * Z (k + 1 + 1)) {j₀ : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hH : ∀ k, j₀ ≤ k → F (k + 1) * Z j₀ ≤ q * F k * Z (j₀ + 1)) :
    ∀ j, j₀ ≤ j → F j / Z j ≤ q ^ (j - j₀) * (F j₀ / Z j₀) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rw [Nat.sub_self, pow_zero, one_mul]
  | succ k hk ih =>
    have hs := odds_step hZ hq (hF k) (hH k hk) (ratio_mono hZ hlc j₀ k hk)
    have e : k + 1 - j₀ = (k - j₀) + 1 := by omega
    calc F (k + 1) / Z (k + 1) ≤ q * (F k / Z k) := hs
      _ ≤ q * (q ^ (k - j₀) * (F j₀ / Z j₀)) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (k + 1 - j₀) * (F j₀ / Z j₀) := by rw [e, pow_succ]; ring

/-- **One step down**: for a nonnegative log-convex `F`, the hop inequality at `k + 1` gives it at `k`.
DERIVED: `1` the hop; `2` the square. -/
theorem hop_step_down (hF : ∀ k, 0 ≤ F k) (hlcF : ∀ k, F (k + 1) ^ 2 ≤ F k * F (k + 1 + 1))
    {c₀ c₁ q : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hq : 0 ≤ q) {k : ℕ}
    (h : F (k + 1 + 1) * c₀ ≤ q * F (k + 1) * c₁) : F (k + 1) * c₀ ≤ q * F k * c₁ := by
  rcases (hF (k + 1)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact mul_nonneg (mul_nonneg hq (hF k)) hc₁
  · have h1 : F (k + 1) * c₀ * F (k + 1) ≤ q * F k * c₁ * F (k + 1) := by
      calc F (k + 1) * c₀ * F (k + 1) = F (k + 1) ^ 2 * c₀ := by ring
        _ ≤ (F k * F (k + 1 + 1)) * c₀ := mul_le_mul_of_nonneg_right (hlcF k) hc₀
        _ = F k * (F (k + 1 + 1) * c₀) := by ring
        _ ≤ F k * (q * F (k + 1) * c₁) := mul_le_mul_of_nonneg_left h (hF k)
        _ = q * F k * c₁ * F (k + 1) := by ring
    exact le_of_mul_le_mul_right h1 hpos

/-- **The hop inequality eventually gives it everywhere**: it reads only the asymptotic hop rate of `F`.
DERIVED: `1` the hop. -/
theorem hop_all_of_eventually (hF : ∀ k, 0 ≤ F k) (hlcF : ∀ k, F (k + 1) ^ 2 ≤ F k * F (k + 1 + 1))
    {c₀ c₁ q : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hq : 0 ≤ q) {K : ℕ}
    (h : ∀ k, K ≤ k → F (k + 1) * c₀ ≤ q * F k * c₁) : ∀ k, F (k + 1) * c₀ ≤ q * F k * c₁ := by
  have key : ∀ d k, K ≤ k + d → F (k + 1) * c₀ ≤ q * F k * c₁ := by
    intro d
    induction d with
    | zero => intro k hk; exact h k (by omega)
    | succ d ih =>
      intro k hk
      exact hop_step_down hF hlcF hc₀ hc₁ hq (ih (k + 1) (by omega))
  exact fun k => key K k (by omega)

/-- **The hop rate to a power is below the growth**: `F(k) (F(k+1)/F(k))^t ≤ F(k+t)`.
DERIVED: `1` the hop; `0` the empty power. -/
theorem hopRate_pow_le (hF : ∀ k, 0 < F k) (hlcF : ∀ k, F (k + 1) ^ 2 ≤ F k * F (k + 1 + 1)) (k t : ℕ) :
    F k * (F (k + 1) / F k) ^ t ≤ F (k + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hr := ratio_mono hF hlcF k (k + t) (by omega)
    have hr' : F (k + t) * (F (k + 1) / F k) ≤ F (k + t + 1) := by
      rw [mul_div_assoc', div_le_iff₀ (hF k)]
      calc F (k + t) * F (k + 1) = F (k + 1) * F (k + t) := mul_comm _ _
        _ ≤ F k * F (k + t + 1) := hr
        _ = F (k + t + 1) * F k := mul_comm _ _
    calc F k * (F (k + 1) / F k) ^ (t + 1) = (F k * (F (k + 1) / F k) ^ t) * (F (k + 1) / F k) := by ring
      _ ≤ F (k + t) * (F (k + 1) / F k) :=
          mul_le_mul_of_nonneg_right ih (div_nonneg (hF _).le (hF _).le)
      _ ≤ F (k + t + 1) := hr'
      _ = F (k + (t + 1)) := by rw [Nat.add_assoc]

/-- **A growth bound bounds the hop rate**: `F(k+t) ≤ ρ^t F(k)` with `t ≠ 0` gives `F(k+1) ≤ ρ F(k)`.
DERIVED: `1` the hop; `0` the excluded power. -/
theorem rate_le_of_growth (hF : ∀ k, 0 < F k) (hlcF : ∀ k, F (k + 1) ^ 2 ≤ F k * F (k + 1 + 1)) {k t : ℕ}
    (ht : t ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) (hg : F (k + t) ≤ ρ ^ t * F k) : F (k + 1) ≤ ρ * F k := by
  have h1 := hopRate_pow_le hF hlcF k t
  have h2 : (F (k + 1) / F k) ^ t ≤ ρ ^ t := by
    have : F k * (F (k + 1) / F k) ^ t ≤ F k * ρ ^ t :=
      h1.trans (hg.trans (le_of_eq (mul_comm _ _)))
    exact le_of_mul_le_mul_left this (hF k)
  have h3 := le_of_pow_le_pow_left₀ ht hρ h2
  rwa [div_le_iff₀ (hF k)] at h3

end Real

/-! ## 2. The flux trace and the hop clause -/

section Lattice

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The flux trace** `F = Z − Z₀` at chain index `j`: the part of `Tr K^{2(j+1)}` carried by the non-zero
electric flux sectors. DERIVED: no numeral. -/
def fluxTrace (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  relayZ N i T β j - relayZ0 N i T β j

variable (N) in
/-- **The hop clause** at anchor `j₀` and factor `q`: for every `k ≥ j₀`, the flux hop rate `F(k+1)/F(k)` is at
most `q` times the zero-flux hop rate `Z₀(j₀+1)/Z₀(j₀)` at the anchor. DERIVED: `1` the hop. -/
def HopClause (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j₀ : ℕ) (q : ℝ) : Prop :=
  ∀ k : ℕ, j₀ ≤ k →
    fluxTrace N i T β (k + 1) * relayZ0 N i T β j₀ ≤ q * fluxTrace N i T β k * relayZ0 N i T β (j₀ + 1)

variable (N) in
/-- **The flux-sector hop gap in measured units** (assumed): there are `s > 0` per measured length and a measured
length `D > 0` such that, eventually in `β`, at every power-of-two side `n ≥ 2` with `D ≤ n m′` and every
direction `i`, some anchor `j₀` with `4(j₀ + 1) ≤ n` has the hop clause at the corner aperture `Tr n i` with factor
`e^{−2 s m′}`. DERIVED: `2` the least side and the two-hop time step; `4` the quarter side; `1` the hop. -/
def FluxHopGap (hN : N ≠ 0) : Prop :=
  ∃ s D : ℝ, 0 < s ∧ 0 < D ∧ ∀ᶠ β in atTop,
    ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
      D ≤ (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal →
      ∀ i : Fin 4, ∃ j₀ : ℕ, 4 * (j₀ + 1) ≤ n ∧
        HopClause N i (CentreSectorSeed.Tr n i) β j₀
          (Real.exp (-(2 * s * (measMassOf (periodicState hN β) tensorEnergy).toReal)))

/-- DERIVED: `3`, `1`. -/
theorem nsub_cube_nonneg : 0 ≤ (N : ℝ) ^ 3 - 1 := by
  have h1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ h1
  linarith

/-- DERIVED: `3`. -/
theorem cube_pos : (0 : ℝ) < (N : ℝ) ^ 3 :=
  pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))) 3

section Facts

variable {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ}

/-- DERIVED: no numeral. -/
theorem fluxTrace_nonneg (hβ : 0 ≤ β) (j : ℕ) : 0 ≤ fluxTrace N i T β j :=
  sub_nonneg.mpr (relayZ0_le hβ j)

/-- **The zero-flux trace is log-convex in the form used here.** DERIVED: `1`, `2`. -/
theorem relayZ0_lc (hβ : 0 ≤ β) (k : ℕ) :
    relayZ0 N i T β (k + 1) ^ 2 ≤ relayZ0 N i T β k * relayZ0 N i T β (k + 1 + 1) := by
  have h := relayZ0_sq_le (N := N) (i := i) (T := T) hβ k 1
  rwa [show k + 2 * 1 = k + 1 + 1 by ring] at h

/-- **The flux trace is log-convex.** DERIVED: `1`, `2`. -/
theorem fluxTrace_lc (hβ : 0 ≤ β) (k : ℕ) :
    fluxTrace N i T β (k + 1) ^ 2 ≤ fluxTrace N i T β k * fluxTrace N i T β (k + 1 + 1) := by
  have h := relayFlux_sq_le (N := N) (i := i) (T := T) hβ k 1
  rw [show k + 2 * 1 = k + 1 + 1 by ring] at h
  exact h

/-- **The hop clause decays the odds**: `relayOdds j ≤ q^{j − j₀} (N³ − 1)` for `j ≥ j₀`.
DERIVED: `3`, `1` the anchor bound. -/
theorem relayOdds_le_hop (hβ : 0 ≤ β) {j₀ : ℕ} {q : ℝ} (hq : 0 ≤ q) (hH : HopClause N i T β j₀ q) :
    ∀ j, j₀ ≤ j → relayOdds N i T β j ≤ q ^ (j - j₀) * ((N : ℝ) ^ 3 - 1) := by
  intro j hj
  have h := odds_decay (F := fluxTrace N i T β) (Z := relayZ0 N i T β) (relayZ0_pos hβ)
    (fluxTrace_nonneg hβ) (relayZ0_lc hβ) hq hH j hj
  have h0 : fluxTrace N i T β j₀ / relayZ0 N i T β j₀ ≤ (N : ℝ) ^ 3 - 1 := by
    have := relayOdds_le_card (N := N) (i := i) (T := T) hβ j₀
    exact this
  calc relayOdds N i T β j = fluxTrace N i T β j / relayZ0 N i T β j := rfl
    _ ≤ q ^ (j - j₀) * (fluxTrace N i T β j₀ / relayZ0 N i T β j₀) := h
    _ ≤ q ^ (j - j₀) * ((N : ℝ) ^ 3 - 1) := mul_le_mul_of_nonneg_left h0 (pow_nonneg hq _)

/-- **The hop clause at a measured rate bounds the odds at every chain index**:
`relayOdds j ≤ (N³ − 1) e^{s (2(j₀+1) m − 2(j+1) m)}`. Below the anchor the exponent is nonnegative and the bound
is the sector bound. DERIVED: `2` the two-hop time step; `3`, `1` the anchor bound. -/
theorem relayOdds_le_of_hop (hβ : 0 ≤ β) {j₀ : ℕ} {s m : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ m)
    (hH : HopClause N i T β j₀ (Real.exp (-(2 * s * m)))) (j : ℕ) :
    relayOdds N i T β j
      ≤ ((N : ℝ) ^ 3 - 1) * Real.exp (s * (2 * ((j₀ : ℝ) + 1) * m - 2 * ((j : ℝ) + 1) * m)) := by
  have hN3 := nsub_cube_nonneg (N := N)
  rcases le_or_gt j₀ j with hj | hj
  · have h := relayOdds_le_hop hβ (Real.exp_pos _).le hH j hj
    have e : Real.exp (-(2 * s * m)) ^ (j - j₀)
        = Real.exp (s * (2 * ((j₀ : ℝ) + 1) * m - 2 * ((j : ℝ) + 1) * m)) := by
      rw [← Real.exp_nat_mul, Nat.cast_sub hj]
      congr 1
      ring
    rw [e] at h
    calc relayOdds N i T β j ≤ _ := h
      _ = _ := mul_comm _ _
  · have hexp : 1 ≤ Real.exp (s * (2 * ((j₀ : ℝ) + 1) * m - 2 * ((j : ℝ) + 1) * m)) := by
      apply Real.one_le_exp
      have hjj : (j : ℝ) ≤ j₀ := by exact_mod_cast hj.le
      have h2 : 0 ≤ 2 * ((j₀ : ℝ) + 1) * m - 2 * ((j : ℝ) + 1) * m := by
        nlinarith [mul_nonneg hm (sub_nonneg.mpr hjj)]
      exact mul_nonneg hs h2
    calc relayOdds N i T β j ≤ (N : ℝ) ^ 3 - 1 := relayOdds_le_card hβ j
      _ = ((N : ℝ) ^ 3 - 1) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp hN3

/-- **The hop clause eventually is the hop clause**: if the inequality holds for all `k ≥ K`, it holds for all
`k ≥ j₀` (indeed all `k`). The clause reads the asymptotic flux hop rate against the zero-flux rate at the
anchor. DERIVED: `1` the hop. -/
theorem hopClause_of_eventually (hβ : 0 ≤ β) {j₀ : ℕ} {q : ℝ} (hq : 0 ≤ q) {K : ℕ}
    (h : ∀ k, K ≤ k →
      fluxTrace N i T β (k + 1) * relayZ0 N i T β j₀ ≤ q * fluxTrace N i T β k * relayZ0 N i T β (j₀ + 1)) :
    HopClause N i T β j₀ q :=
  fun k _ => hop_all_of_eventually (fluxTrace_nonneg hβ) (fluxTrace_lc hβ) (relayZ0_pos hβ j₀).le
    (relayZ0_pos hβ (j₀ + 1)).le hq h k

/-- **The hop clause from a growth bound** (the form a strong-coupling witness would take): if the flux
trace is positive and, for each `k ≥ j₀`, some `t ≥ 1` has `F(k + t) ≤ (q Z₀(j₀+1)/Z₀(j₀))^t F(k)`, the clause
holds. DERIVED: `1` the hop; `0` the excluded power. -/
theorem hopClause_of_growth (hβ : 0 ≤ β) {j₀ : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hpos : ∀ k, 0 < fluxTrace N i T β k)
    (hg : ∀ k, j₀ ≤ k → ∃ t : ℕ, t ≠ 0 ∧ fluxTrace N i T β (k + t)
      ≤ (q * relayZ0 N i T β (j₀ + 1) / relayZ0 N i T β j₀) ^ t * fluxTrace N i T β k) :
    HopClause N i T β j₀ q := by
  intro k hk
  obtain ⟨t, ht, hkt⟩ := hg k hk
  have hZ0 := relayZ0_pos (N := N) (i := i) (T := T) hβ j₀
  have hZ1 := relayZ0_pos (N := N) (i := i) (T := T) hβ (j₀ + 1)
  have hρ : 0 ≤ q * relayZ0 N i T β (j₀ + 1) / relayZ0 N i T β j₀ :=
    div_nonneg (mul_nonneg hq hZ1.le) hZ0.le
  have h := rate_le_of_growth hpos (fluxTrace_lc hβ) ht hρ hkt
  rw [div_mul_eq_mul_div, le_div_iff₀ hZ0] at h
  calc fluxTrace N i T β (k + 1) * relayZ0 N i T β j₀
      ≤ q * relayZ0 N i T β (j₀ + 1) * fluxTrace N i T β k := h
    _ = q * fluxTrace N i T β k * relayZ0 N i T β (j₀ + 1) := by ring

/-! ### The twist cost -/

/-- **A twisted trace is at most the trace**: `Z_g ≤ Z`. DERIVED: no numeral. -/
theorem relayTwist_le (hβ : 0 ≤ β) (j : ℕ) (g : Cen i N) : relayTwist N i T β j g ≤ relayZ N i T β j := by
  unfold relayTwist relayZ
  exact MassGap.FluxShareSquaring.twist_le_hs (bdd_iterK hβ j)
    ((centreAction (μ := i) (T := T) (N := N)).mp g)

/-- **The twist cost is in `[0, 1]`**: `0 ≤ 1 − Z_g/Z`. DERIVED: `0`, `1`. -/
theorem twistCost_nonneg (hβ : 0 ≤ β) (j : ℕ) (g : Cen i N) :
    0 ≤ 1 - relayTwist N i T β j g / relayZ N i T β j := by
  have hZ := relayZ_pos (N := N) (i := i) (T := T) hβ j
  rw [sub_nonneg, div_le_one hZ]
  exact relayTwist_le hβ j g

/-- **The flux share is the mean twist cost**: `relayShare = N⁻³ Σ_g (1 − Z_g/Z)`. DERIVED: `3` in `N³`; `1`. -/
theorem relayShare_eq_meanCost (hβ : 0 ≤ β) (j : ℕ) :
    relayShare N i T β j
      = ((N : ℝ) ^ 3)⁻¹ * ∑ g : Cen i N, (1 - relayTwist N i T β j g / relayZ N i T β j) := by
  have hN0 : (N : ℝ) ^ 3 ≠ 0 := (cube_pos (N := N)).ne'
  rw [relayShare_eq_mean hβ j, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_cen,
    nsmul_eq_mul, mul_one, mul_sub]
  push_cast
  rw [inv_mul_cancel₀ hN0]

/-- **Every twist cost is at most `N³` times the flux share**: `1 − Z_g/Z ≤ N³ · relayShare`. A small flux share
means every 't Hooft twist is nearly free. DERIVED: `3` in `N³`. -/
theorem twistCost_le (hβ : 0 ≤ β) (j : ℕ) (g : Cen i N) :
    1 - relayTwist N i T β j g / relayZ N i T β j ≤ (N : ℝ) ^ 3 * relayShare N i T β j := by
  have hN0 : (N : ℝ) ^ 3 ≠ 0 := (cube_pos (N := N)).ne'
  rw [relayShare_eq_meanCost hβ j, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  exact Finset.single_le_sum (f := fun g => 1 - relayTwist N i T β j g / relayZ N i T β j)
    (fun g _ => twistCost_nonneg hβ j g) (Finset.mem_univ g)

/-! ### Tests -/

/-- **At `β = 0` the flux trace is `0`.** DERIVED: `0`. -/
theorem fluxTrace_zero_coupling (j : ℕ) : fluxTrace N i T 0 j = 0 := by
  have h := relayOdds_zero_coupling (N := N) i T j
  have hp := relayZ0_pos (N := N) (i := i) (T := T) (le_refl (0 : ℝ)) j
  unfold relayOdds at h
  rcases div_eq_zero_iff.mp h with h1 | h1
  · exact h1
  · exact absurd h1 hp.ne'

/-- **At `β = 0` the hop clause holds at every anchor and factor.** DERIVED: `0`. -/
theorem hopClause_zero_coupling (j₀ : ℕ) (q : ℝ) : HopClause N i T 0 j₀ q := by
  intro k _
  simp [fluxTrace_zero_coupling]

/-- **The hop clause is not implied by the sector bound**: if the odds stay at least `ε > 0` at arbitrarily long
chains, no anchor and no `q < 1` meet the clause. DERIVED: `3`, `1` the sector bound; `0` the floor. -/
theorem not_hopClause_of_floor (hβ : 0 ≤ β) {j₀ : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {ε : ℝ}
    (hε : 0 < ε) (hfl : ∀ J : ℕ, ∃ j, J ≤ j ∧ ε ≤ relayOdds N i T β j) : ¬ HopClause N i T β j₀ q := by
  intro hH
  have hN0 := cube_pos (N := N)
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (div_pos hε hN0) hq1
  obtain ⟨j, hjJ, hεj⟩ := hfl (j₀ + t)
  have hb := relayOdds_le_hop hβ hq0 hH j (by omega)
  have hmono : q ^ (j - j₀) ≤ q ^ t := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have h1 : q ^ t * ((N : ℝ) ^ 3 - 1) ≤ q ^ t * (N : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hq0 t)
  have h2 : q ^ t * (N : ℝ) ^ 3 < ε := by rwa [lt_div_iff₀ hN0] at ht
  have h3 : q ^ (j - j₀) * ((N : ℝ) ^ 3 - 1) ≤ q ^ t * ((N : ℝ) ^ 3 - 1) :=
    mul_le_mul_of_nonneg_right hmono nsub_cube_nonneg
  linarith

end Facts

/-! ## 3. The flux clause at a large measured side -/

/-- **The flux clause of the seed from the hop clause**: at an even side `n ≥ 2` with an anchor in the first
quarter and `s n m ≥ 2 log(80000 N³)`, `fluxShareN N β n i ≤ 1/80000`. DERIVED: `2` the half side and the
two-hop step; `4` the quarter; `80000`, `1/80000` the threshold; `3` in `N³`. -/
theorem fluxShareN_le_of_hop {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (he : Even n) (i : Fin 4) {j₀ : ℕ}
    (hj₀ : 4 * (j₀ + 1) ≤ n) {s m : ℝ} (hs : 0 < s) (hm : 0 ≤ m)
    (hH : HopClause N i (CentreSectorSeed.Tr n i) β j₀ (Real.exp (-(2 * s * m))))
    (hw : 2 * Real.log (80000 * (N : ℝ) ^ 3) / s ≤ n * m) :
    fluxShareN N β n i ≤ 1 / 80000 := by
  have h := relayOdds_le_of_hop hβ hs.le hm hH (n / 2 - 1)
  have hj : ((n / 2 - 1 : ℕ) : ℝ) + 1 = (n : ℝ) / 2 := by
    obtain ⟨p, rfl⟩ := he
    have hp1 : 1 ≤ p := by omega
    have e : (p + p) / 2 - 1 + 1 = p := by omega
    have : (((p + p) / 2 - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by exact_mod_cast e
    rw [this]
    push_cast
    ring
  have hj0 : 2 * ((j₀ : ℝ) + 1) * m ≤ (n : ℝ) * m / 2 := by
    have h4 : 4 * ((j₀ : ℝ) + 1) ≤ n := by exact_mod_cast hj₀
    nlinarith [mul_le_mul_of_nonneg_right h4 hm]
  rw [hj] at h
  have hN0 := cube_pos (N := N)
  have hL : 2 * Real.log (80000 * (N : ℝ) ^ 3) ≤ s * (n * m) := by
    rw [div_le_iff₀ hs] at hw
    linarith
  have hx : s * (2 * ((j₀ : ℝ) + 1) * m - 2 * ((n : ℝ) / 2) * m) ≤ -Real.log (80000 * (N : ℝ) ^ 3) := by
    nlinarith [mul_le_mul_of_nonneg_left hj0 hs.le]
  have hexp : Real.exp (s * (2 * ((j₀ : ℝ) + 1) * m - 2 * ((n : ℝ) / 2) * m))
      ≤ (80000 * (N : ℝ) ^ 3)⁻¹ := by
    calc Real.exp (s * (2 * ((j₀ : ℝ) + 1) * m - 2 * ((n : ℝ) / 2) * m))
        ≤ Real.exp (-Real.log (80000 * (N : ℝ) ^ 3)) := Real.exp_le_exp.mpr hx
      _ = (80000 * (N : ℝ) ^ 3)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
  calc fluxShareN N β n i = relayShare N i (CentreSectorSeed.Tr n i) β (n / 2 - 1) :=
        fluxShareN_eq_relay β n i
    _ ≤ relayOdds N i (CentreSectorSeed.Tr n i) β (n / 2 - 1) := relayShare_le_odds hβ _
    _ ≤ ((N : ℝ) ^ 3 - 1) * Real.exp (s * (2 * ((j₀ : ℝ) + 1) * m - 2 * ((n : ℝ) / 2) * m)) := h
    _ ≤ (N : ℝ) ^ 3 * (80000 * (N : ℝ) ^ 3)⁻¹ :=
        mul_le_mul (by linarith) hexp (Real.exp_pos _).le hN0.le
    _ = 1 / 80000 := by
        rw [mul_inv, ← mul_assoc, mul_comm ((N : ℝ) ^ 3), mul_assoc, mul_inv_cancel₀ hN0.ne', mul_one,
          one_div]

/-! ## 4. The reads from the hop gap -/

/-- **The hop gap gives the long-chain read**, with the same rate and window and `B = (N³ − 1) e^{s D′/2}` on the
band `D′`. DERIVED: `2` the half band and the two-hop step; `4` the quarter; `3`, `1` the sector bound. -/
theorem longChainRead_of_hopGap (hN : N ≠ 0) (hG : FluxHopGap N hN) : GapFromReads.LongChainRead N hN := by
  obtain ⟨s, D, hs, hD, hev⟩ := hG
  refine ⟨s, D, hs, hD, fun D' => ⟨((N : ℝ) ^ 3 - 1) * Real.exp (s * (D' / 2)), ?_⟩⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβG hβ n hp hn hDn hnD' i j _
  set m := (measMassOf (periodicState hN β) tensorEnergy).toReal with hmdef
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  obtain ⟨j₀, hj₀, hH⟩ := hβG n hp hn hDn i
  have h := relayOdds_le_of_hop hβ hs.le hm hH j
  have hj0m : 2 * ((j₀ : ℝ) + 1) * m ≤ D' / 2 := by
    have h4 : 4 * ((j₀ : ℝ) + 1) ≤ n := by exact_mod_cast hj₀
    nlinarith [mul_le_mul_of_nonneg_right h4 hm]
  calc relayOdds N i (CentreSectorSeed.Tr n i) β j ≤ _ := h
    _ = ((N : ℝ) ^ 3 - 1) * Real.exp (s * (2 * ((j₀ : ℝ) + 1) * m))
          * Real.exp (-(s * ((2 * ((j : ℝ) + 1)) * m))) := by
        rw [mul_assoc ((N : ℝ) ^ 3 - 1), ← Real.exp_add]
        congr 2
        ring
    _ ≤ ((N : ℝ) ^ 3 - 1) * Real.exp (s * (D' / 2)) * Real.exp (-(s * ((2 * ((j : ℝ) + 1)) * m))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hj0m hs.le)) nsub_cube_nonneg)
          (Real.exp_pos _).le

/-- **The hop gap and the zero-flux read give the sector seed**, without the across-aperture exchange and the
long-chain read. The seed side is a power of two `n` with `X ≤ n m′ ≤ max(2X, 2C₀)`,
`X = max(D, C_z, 2 log(80000 N³)/s)`. DERIVED: `2` the least side and the window's doubling; `80000`, `1/80000`
the threshold; `3` in `N³`; `1` the least exponent. -/
theorem sectorSeedMeasured_of_hopGap (hN : N ≠ 0) (hG : FluxHopGap N hN) (hZ : ZeroFluxReadsMass N hN) :
    SectorSeedMeasured hN := by
  obtain ⟨s, D, hs, hD, hGev⟩ := hG
  obtain ⟨Cz, hZev⟩ := zeroFluxClause_of_reads hN hZ
  obtain ⟨C₀, hC₀, hAev⟩ := GapFromReads.measMass_le_of_reads hN hZ
  set X := max D (max Cz (2 * Real.log (80000 * (N : ℝ) ^ 3) / s)) with hX
  have hX0 : 0 < X := lt_max_of_lt_left hD
  refine ⟨max (2 * X) (2 * C₀), lt_max_of_lt_left (by linarith), ?_⟩
  filter_upwards [hGev, hZev, hAev, eventually_ge_atTop (0 : ℝ)] with β hGβ hZβ hAβ hβ
  obtain ⟨hm, hZβ⟩ := hZβ
  have hMpos := ENNReal.toReal_pos_iff.mp hm
  set M := measMassOf (periodicState hN β) tensorEnergy with hMdef
  set m := M.toReal with hmdef
  obtain ⟨b, hb1, hbl, hbu⟩ := GapFromReads.exists_pow_two_window (D := X) hm
  have hn2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  have hen : Even (2 ^ b) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hcast : ((2 ^ b : ℕ) : ℝ) = (2 : ℝ) ^ b := by push_cast; ring
  have hlo : X ≤ ((2 ^ b : ℕ) : ℝ) * m := by rw [hcast]; exact hbl
  refine ⟨hMpos.1, 2 ^ b, ⟨b, rfl⟩, hn2, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [GapFromReads.ofReal_window hMpos.2.ne]
    apply ENNReal.ofReal_le_ofReal
    rw [hcast]
    exact hbu.trans (max_le_max le_rfl (by linarith))
  · obtain ⟨j₀, hj₀, hH⟩ := hGβ (2 ^ b) ⟨b, rfl⟩ hn2 ((le_max_left _ _).trans hlo) i
    exact fluxShareN_le_of_hop hβ hen i hj₀ hs ENNReal.toReal_nonneg hH
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlo))
  · exact hZβ (2 ^ b) hn2 hen ((le_max_left _ _).trans ((le_max_right _ _).trans hlo)) i

end Lattice

/-! ## 5. The observer's gap from the hop gap -/

section GapSU

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG
  MassGap.FlowClusterG MassGap.MeasuredTower MassGap.MeasuredSpacing

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The hop gap, the zero-flux read and a measured tower give the observer's gap at the tower's schedule.**
DERIVED: `0` the plane. -/
theorem observerGap_of_hopGap (hG : FluxHopGap N (NeZero.ne N))
    (hZ : ZeroFluxGap.ZeroFluxReadsMass N (NeZero.ne N))
    {βs : ℕ → ℝ} (hT : MeasTowerG (MassGap.SUN.SU N) βs) (Φ : GFlow (MassGap.SUN.SU N))
    (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) {r : ℝ} (hphys : Φ.PhysRange (schedAlongG _ βs) r)
    (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (transferNG (schedAlongG _ βs) (schedOS_alongG _ βs) Φ hB 0 hphys m0) ρ :=
  observerGap_of_sectorSeed (sectorSeedMeasured_of_hopGap (NeZero.ne N) hG hZ) hT Φ hB hphys m0

end GapSU

end MassGap.TorusContraction

end

#print axioms MassGap.TorusContraction.ratio_mono
#print axioms MassGap.TorusContraction.odds_step
#print axioms MassGap.TorusContraction.odds_decay
#print axioms MassGap.TorusContraction.hop_step_down
#print axioms MassGap.TorusContraction.hop_all_of_eventually
#print axioms MassGap.TorusContraction.hopRate_pow_le
#print axioms MassGap.TorusContraction.rate_le_of_growth
#print axioms MassGap.TorusContraction.fluxTrace_lc
#print axioms MassGap.TorusContraction.relayOdds_le_hop
#print axioms MassGap.TorusContraction.relayOdds_le_of_hop
#print axioms MassGap.TorusContraction.hopClause_of_eventually
#print axioms MassGap.TorusContraction.hopClause_of_growth
#print axioms MassGap.TorusContraction.relayTwist_le
#print axioms MassGap.TorusContraction.twistCost_nonneg
#print axioms MassGap.TorusContraction.relayShare_eq_meanCost
#print axioms MassGap.TorusContraction.twistCost_le
#print axioms MassGap.TorusContraction.fluxTrace_zero_coupling
#print axioms MassGap.TorusContraction.hopClause_zero_coupling
#print axioms MassGap.TorusContraction.not_hopClause_of_floor
#print axioms MassGap.TorusContraction.fluxShareN_le_of_hop
#print axioms MassGap.TorusContraction.longChainRead_of_hopGap
#print axioms MassGap.TorusContraction.sectorSeedMeasured_of_hopGap
#print axioms MassGap.TorusContraction.observerGap_of_hopGap
