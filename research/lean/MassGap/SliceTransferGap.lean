import Mathlib
import MassGap.TorusContraction
import MassGap.JentzschKT

/-!
# MassGap.SliceTransferGap — one gap of the whole slice transfer, in measured units

On the measured target the sector seed, and with a measured tower the observer's SU(N) gap, follow from two inputs, `TorusContraction.FluxHopGap` (the flux sector)
and `ZeroFluxGap.ZeroFluxReadsMass` (the zero-flux sector). Both are spectral statements about one symmetric,
positive, centre-invariant kernel, the slice transfer `K = kT i T N β`: the one hop of the observer's relay
through its fixed aperture. This module states one input on `K` with no sector selected, proves that it gives the
flux-sector hop gap, the long-chain read, the sector seed, the observer's gap and the run seed, and places it
against the gap itself. Declarations are in the namespace `MassGap.SliceTransferGap`. Throughout,
`m′ = (measMassOf (periodicState hN β) tensorEnergy).toReal`, `R = K − λ φ⊗φ` (`KernelPower.rem`),
`Z₀(j) = relayZ0` and `F(j) = TorusContraction.fluxTrace = Z(j) − Z₀(j)`.

## 1. The input (assumed)

**`TransferGapAt N i T β λ φ ρ`**: `φ` is a bounded measurable unit eigenfunction of `K` with eigenvalue
`λ ≠ 0`, and `‖R‖ ≤ ρ` in `L²` operator norm. This is `ZeroFluxGap.ZeroFluxGapAt` with `K` in place of
`K₀ = zk K`.

**`TransferGapMeasured N hN`**: there are `c > 0` (dimensionless) and `D > 0` (a measured length) such that,
eventually in `β`, `0 < m′`, and at every power-of-two side `n ≥ 2` with `D ≤ n m′` and every direction `i`
there are `λ, φ, ρ, j₀` with

* `TransferGapAt N i (Tr n i) β λ φ ρ` and `ρ ≤ |λ| e^{−c m′}` (the gap: `c m′` per hop, relative to the top);
* `4(j₀ + 1) ≤ n` and `λ² Z₀(j₀) ≤ e^{c m′} Z₀(j₀ + 1)` (the anchor: at one index in the first quarter of the
  cubic chain, the zero-flux hop rate is within `e^{−c m′}` of the top's rate `λ²`).

`c` and `D` are fixed before `β`, the side and the direction.

Why the anchor. The flux clause compares the flux hop rate with the zero-flux hop rate at an anchor. The gap
bounds the first: `F(k+1) ≤ ρ² F(k) ≤ λ² e^{−2 c m′} F(k)` (`flux_step`). It does not bound the second from
below: `Z₀(j+1)/Z₀(j) = λ² (1 + x₀(j+1))/(1 + x₀(j))`, `x₀` the excited zero-flux weight, and a large weight
at the gap edge brings this rate down to `ρ²`. `no_hop_from_gap` (proved real-number lemma, reading argued) gives,
for every `q < 1` and anchor, a multiplicity at which the hop clause fails while the remainder norm stays put.
The anchor clause asks that shortfall be at most `e^{c m′}` at one anchor. With the gap it also bounds the
excited weight there, `x₀(j₀) ≤ e^{c m′}` (`zeroRem_anchor`), which is what the zero-flux clause needs.
It is a measured-scale clause (argued): in measured energies `e_k` and measured time `τ = 2(j₀ + 1) m′`, the
shortfall is about `2 m′ Σ w_k e_k e^{−τ e_k}/(1 + x₀)`, so the clause asks that the excited weight at some `τ ≤ n m′/2` be of order one, a statement of the theory at the measured scale. A clause `x₀(j₀) ≤ ε` with a fixed
`ε` would be a lattice-unit statement: the excited weight at fixed `n m′` does not fall as `m′ → 0`.

## 2. Centre invariance of the top (proved)

* `top_unique`: a gapped unit eigenpair `(c, φ)` with `‖R‖ ≤ ρ`, and any unit eigenpair `(d, ψ)` with `ρ² < d²`,
  have `⟨ψ, φ⟩² = 1`, `d = c` and `ψ = ⟨ψ, φ⟩ φ` almost everywhere. `R` sends `ψ − ⟨ψ, φ⟩ φ` to
  `d ψ − c ⟨ψ, φ⟩ φ`, whose square integral is `d²(1 − a²) + a²(d − c)²`; `sq_apply_le` bounds it by
  `ρ²(1 − a²)`.
* `top_of_gap`: if `ρ² < λ²`, then `λ = ‖K‖` and `∫ φ ≠ 0`. The strictly positive eigenfunction of
  `JentzschKT.exists_pos_eigen_kT` has eigenvalue `‖K‖ ≥ |λ|` (`sq_apply_le` on `K`), so `top_unique` applies.
* `phi_act_of_gap`, `phi_act_kT`: then `φ (act g x) = φ x` at every `x`. `φ ∘ act g` is a unit eigenfunction at
  `λ` because `K` commutes with the joint twist (`SliceCentreAction.kT_act`) and Haar is invariant;
  `top_unique` makes it `±φ` almost everywhere; `∫ φ ≠ 0` fixes the sign; the eigen equation makes it pointwise.

So the gapped pair is the Jentzsch top and carries no flux; no sector hypothesis is assumed.

## 3. Both sectors from one remainder (proved)

* `fk_iter_eq`: for a centre-invariant `φ`, `fk(K^{∗(j+1)}) = fk(R^{∗(j+1)})`; with `RelayChain.hs_fk`,
  `F(j) = hs(fk(R^{∗(j+1)}))` (`fluxTrace_eq_rem`). The flux sector lies in the remainder.
* `relayZ0_eq_rem`: `Z₀(j) = λ^{2(j+1)} + hs(zk(R^{∗(j+1)}))` (from `KernelPower.hs_iter_decomp` and `hs_fk`
  twice). The zero-flux remainder is the zero-flux part of the full remainder.
* `zk_left_conv`, `fk_left_conv`: both projections commute with a hop on the left, with no invariance; with
  `KernelPower.hs_conv_le_norm`, `flux_step` (`F(k+1) ≤ ρ² F(k)`) and `zeroRem_step` (the zero-flux remainder
  falls by `ρ²` per hop).

## 4. What it gives (proved)

* `hopClause_of_gapAt`: the gap and the anchor give `TorusContraction.HopClause` at `j₀` with factor
  `e^{−c m′}`.
* `relayDefect_le_of_gapAt`: `relayDefect(j₀ + t) ≤ 2 e^{c m′ − 2 c m′ t}` (from `zeroRem_anchor`,
  `zeroRem_step` and `ZeroFluxGap.defect_split_le`).
* **`fluxHopGap_of_transferGap`**: `TransferGapMeasured → FluxHopGap`, with `s = c/2` and the same `D`.
* `longChainRead_of_transferGap`: `→ GapFromReads.LongChainRead`.
* `measMass_lt_of_transferGap`: `→` eventually `2 m′ < D` (the clause at side `2` has no anchor).
* **`sectorSeedMeasured_of_transferGap`**: `→ SectorSeedMeasured`, both clauses at one power of two `n` with
  `X ≤ n m′ ≤ 2X`, `X = max(D, 4 log 160000/c, 4 log(80000 N³)/c)`. The flux clause is
  `TorusContraction.fluxShareN_le_of_hop`; the zero-flux clause is `relayDefect_le_of_gapAt` at
  `t = n/2 − 1 − j₀ ≥ n/4`.
* **`observerGap_of_transferGap`**: with a measured tower, the observer's transfer gap.
  `runSeed_of_transferGap`: with `UnitTracksRun`, `WDeltaRun.RunSeed`.

It does not give `ZeroFluxReadsMass` (argued). That Prop is asked at every even side and bounds the excited weight at an index within a bounded number `C₀` of
measured lengths; here the sides are powers of two, the weight is bounded only at an anchor in the first quarter of
the chain, and the gap does not bound it at earlier indices. The operator bound is not the obstruction: `zk R` is
`R` followed by the centre average, so `‖zk R‖ ≤ ‖R‖` (not built here). `sectorSeedMeasured_of_hopGap` uses
`ZeroFluxReadsMass` for the zero-flux clause and for the bound on `m′`; here both come from the input.

## 5. The converse (argued)

It is not a restatement of the two inputs.

* `SectorSeedMeasured` does not give it: the seed is two numbers at one side; the input is a spectral statement
  at every side with `n m′ ≥ D`.
* `FluxHopGap` and `ZeroFluxReadsMass` together do not give it. They give a gap of `K₀` and an asymptotic flux
  rate below `e^{−2 s m′}` times the zero-flux rate at an anchor. Their gap parts would bound `‖R‖` at rate `min(c, s)` through `‖R‖ = max(‖zk R‖, |λ_F|)` (the spectral theorem on
the sector decomposition, not built for `kT`); what they do not give is the anchor: the anchor of `ZeroFluxReadsMass` (weight at most `A e^{c n m′/2}` at a bounded measured index) gives at the
  quarter chain only a bounded weight `A e^{2 c C₀}`, not the shortfall `e^{c m′}`.

What it adds: one remainder bound for both sectors, so the flux sector's gap is the zero-flux gap; and the anchor
shortfall at the quarter chain.

## 6. Where it sits relative to the gap

`TransferGapMeasured` is the mass gap of the finite slice transfer, the one-hop relay through a fixed aperture,
at every window with `n m′ ≥ D`, uniform in the window, in units of the measured mass, together with an anchor.
It is a gap statement. A single input that is the gap is not a reduction of the gap.

| compared with | `TransferGapMeasured` gives it | it gives `TransferGapMeasured` |
|---|---|---|
| `SectorSeedMeasured` | proved | no (argued, §5) |
| `RunSeed` | proved, with `UnitTracksRun` | no (argued: one defect number at one side) |
| `FluxHopGap` | proved | no (argued: says nothing of the zero-flux gap) |
| `ZeroFluxReadsMass` | not proved (argued, §4) | no (argued: says nothing of the flux sector) |
| the observer's gap at the tower's schedule (the clustering gap clause there, by `MeasuredSpacing.flowClusterAbs_iff_gapAtG`) | proved, with a measured tower | no (argued: a continuum gap does not fix the finite lattice transfer at every large `β` and every window, nor the anchor) |

So it is stronger than `SectorSeedMeasured`, than `FluxHopGap`, than `RunSeed` (with `UnitTracksRun`) and than the
observer's gap (with a measured tower); against `ZeroFluxReadsMass` neither implies the other (argued). It is
equivalent to none. It is not `RunSeed` restated: `RunSeed` is weaker. What the single input buys: one input instead of two; every constant measured (`c` a ratio of rates, `D` a measured length); one
spectral object (one kernel, one remainder) instead of two sector statements; centre invariance proved rather
than assumed; and the input is observer-side, a gap of the one hop the observer relays. What it does not buy:
any part of the gap.

## 7. Tests

1. Degenerate coupling (proved). `transferGapAt_zero_coupling`: at `β = 0`, `K = 1`, `φ = 1`, `λ = 1`, `ρ = 0`.
   `relayZ0_zero_coupling`, `anchor_zero_coupling`: `Z₀ ≡ 1` and the anchor holds at every index.
   `reads_zero_coupling`: both reads follow there at every rate. The Prop is read along `β → ∞`, so these test
   the per-aperture clause, not an instance of the Prop.
2. Strong coupling (proved in `StrongTransferGap` per slice and in `UniformRelayStrong` uniformly). `strong_gap_half`: at each slice and
   `0 ≤ β ≤ β₀(T) = log(3/2)/(2(30|TT| + 1))`, the Jentzsch top has `‖K − λ φ⊗φ‖ ≤ |λ|/2`; `β₀(T) → 0` with the
   slice; the uniform-in-`T` statement `StrongTransferGap.UniformRelayGap` holds at a fixed `β₀ > 0` and rate
`e^{−m} = coreRate 64 β₀` (`UniformRelayStrong.uniformRelayGap`). An instance at small
   `β` would not be one of the Prop in any case.
3. Vacuity (proved and argued). `c > 0` and `D > 0` are fixed before `β` and the side; the lock `0 < m′` is
   asked. `measMass_lt_of_transferGap`: the clause at side `2` is unsatisfiable, so the Prop forces `2 m′ < D`
   eventually, consistent with `m′ → 0`. With `c m′ > 0` the gap gives `ρ < |λ|`, so by `top_of_gap` the pair
   cannot be a lower eigenpair. `no_hop_from_gap`: the anchor is load-bearing. The rate `e^{−c m′}` tends to `1`
   as `m′ → 0`, so no fixed lattice-unit rate is asked.
4. Measured scales only. The clause is asked only at sides with `n m′ ≥ D`; the anchor sits at measured time
   `2(j₀ + 1) m′ ≤ n m′/2`. At a fixed lattice side it would ask a lattice-scale gap per hop of a fixed size along
   `β → ∞` (argued: false in the scaling regime).
5. Trivial centre (argued). At `N = 1`, `F = 0` and the input asks only the zero-flux gap and anchor.

## 8. Proved, argued, assumed

* Proved: every theorem of the module, with standard axioms only.
* Argued: the measured reading of the anchor (§1), the reading of `no_hop_from_gap`, that the input does not give
  `ZeroFluxReadsMass` (§4), the converse non-implications (§5) and the right-hand column of §6, tests 4 and 5.
* Assumed: `TransferGapMeasured N hN`, only in `fluxHopGap_of_transferGap`, `longChainRead_of_transferGap`,
  `measMass_lt_of_transferGap`, `sectorSeedMeasured_of_transferGap`, `observerGap_of_transferGap` and
  `runSeed_of_transferGap`; `UnitTracksRun` in the last; the measured tower, `UniformBoundFG` and `PhysRange` in `observerGap_of_transferGap`.

## 9. Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every lattice read | shared, in the substrate; the Prop is read along `β → ∞` |
| `i` (direction), `T` (aperture) | `TransferGapAt`, the slice lemmas | chosen; `T = Tr n i` in the Prop |
| `n` (side) | `TransferGapMeasured`, the seed | swept: every power of two `≥ 2` with `D ≤ n m′` |
| `λ`, `φ` | `TransferGapAt` | existential: a unit eigenpair of `K`; proved to be the Jentzsch top |
| `ρ` | `TransferGapAt` | existential: a bound on `‖K − λ φ⊗φ‖` |
| `j₀` (anchor) | the Prop, the read lemmas | existential per `(β, n, i)`, at most `n/4 − 1` |
| `k`, `t`, `j` (chain indices) | the step and read lemmas | swept |
| `c` | the Prop | existential, dimensionless: the gap per hop in units of `m′` |
| `D` | the Prop | existential, a measured length: the least window |
| `s = c/2` | `fluxHopGap_of_transferGap` | derived |
| `X`, `2X` | `sectorSeedMeasured_of_transferGap` | derived: `X = max(D, 4 log 160000/c, 4 log(80000 N³)/c)` |
| `g` (centre element) | the invariance lemmas | swept over `Z_N³` |
| `ψ`, `d`, `a` | `top_unique` | a second unit eigenpair and its overlap with `φ` |
| `r`, `q`, `M` | `no_hop_from_gap` | `r`, `q` chosen; `M` existential |
| `l2, L, E, E', u, v, r2` | `anchor_real` | local to the real-number step |
| `m′` | the Prop, the reads | measured: `(measMassOf (periodicState hN β) tensorEnergy).toReal` |
| `N` | the type | shared with the substrate |

DERIVED (module-wide): `1` the hop and the normalization; `2` the square, the two time directions of a hop and
the window's doubling; `4` the quarter side; `0` the degenerate coupling; `3` in `N³ = |Z_N³|`; `80000`,
`1/80000` the threshold of `SectorSeedMeasured`; `160000 = 2 · 80000` the factor of the defect bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.SliceTransferGap

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.FluxSectorFourier MassGap.ZeroFluxSector
  MassGap.SlabKernelOperator MassGap.RelayChain
open MassGap.SliceCentreAction (Cen act centreAction kT_act)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)
open MassGap.SubstrateDecode (measMassOf tensorEnergy)
open MassGap.PeriodicState (periodicState)
open MassGap.SubstrateFluxRead (SectorSeedMeasured)
open MassGap.TorusContraction (fluxTrace HopClause FluxHopGap fluxShareN_le_of_hop fluxTrace_nonneg)

/-! ## 1. A gapped eigenpair is the top, and is unique -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- **The operator norm bounds one application**: `∫ (k f)² ≤ ‖K‖² ∫ f²` for bounded measurable `f`.
DERIVED: `2` the square. -/
theorem sq_apply_le {k : X → X → ℝ} {C : ℝ} (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C)
    (hkb : ∀ x y, |k x y| ≤ C) {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hfb : ∀ x, |f x| ≤ B) :
    ∫ x, (∫ y, k x y * f y ∂μ) ^ 2 ∂μ ≤ ‖kernelCLM k C hkm hC0 hkb μ μ‖ ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  have hc : Bdd (fun (y : X) (_ : X) => f y) := ⟨hf.comp measurable_fst, B, fun y _ => hfb y⟩
  have h := hs_conv_le_norm (μ := μ) hkm hC0 hkb hc
  have e1 : hs μ (conv μ k (fun (y : X) (_ : X) => f y)) = ∫ x, (∫ y, k x y * f y ∂μ) ^ 2 ∂μ := by
    simp [hs, conv]
  have e2 : hs μ (fun (y : X) (_ : X) => f y) = ∫ x, f x ^ 2 ∂μ := by
    simp [hs]
  rwa [e1, e2] at h

/-- The square of a combination of two bounded functions. DERIVED: `2` the square and the cross term. -/
theorem int_sq_comb {φ ψ : X → ℝ} (hφm : Measurable φ) (hψm : Measurable ψ) {Bφ Bψ : ℝ}
    (hφb : ∀ x, |φ x| ≤ Bφ) (hψb : ∀ x, |ψ x| ≤ Bψ) (α β : ℝ) :
    ∫ x, (α * ψ x + β * φ x) ^ 2 ∂μ
      = α ^ 2 * ∫ x, ψ x ^ 2 ∂μ + 2 * α * β * ∫ x, ψ x * φ x ∂μ + β ^ 2 * ∫ x, φ x ^ 2 ∂μ := by
  have i1 : Integrable (fun x => ψ x * ψ x) μ := integrable_mul_of_bdd hψm hψm hψb hψb
  have i2 : Integrable (fun x => ψ x * φ x) μ := integrable_mul_of_bdd hψm hφm hψb hφb
  have i3 : Integrable (fun x => φ x * φ x) μ := integrable_mul_of_bdd hφm hφm hφb hφb
  have s1 : ∫ x, ψ x ^ 2 ∂μ = ∫ x, ψ x * ψ x ∂μ := by congr 1; funext x; ring
  have s3 : ∫ x, φ x ^ 2 ∂μ = ∫ x, φ x * φ x ∂μ := by congr 1; funext x; ring
  have e : (fun x => (α * ψ x + β * φ x) ^ 2)
      = fun x => α ^ 2 * (ψ x * ψ x) + ((2 * α * β) * (ψ x * φ x) + β ^ 2 * (φ x * φ x)) := by
    funext x; ring
  have j1 : Integrable (fun x => α ^ 2 * (ψ x * ψ x)) μ := i1.const_mul _
  have j2 : Integrable (fun x => (2 * α * β) * (ψ x * φ x)) μ := i2.const_mul _
  have j3 : Integrable (fun x => β ^ 2 * (φ x * φ x)) μ := i3.const_mul _
  have j23 : Integrable (fun x => (2 * α * β) * (ψ x * φ x) + β ^ 2 * (φ x * φ x)) μ := j2.add j3
  rw [e, integral_add j1 j23, integral_add j2 j3, integral_const_mul, integral_const_mul,
    integral_const_mul, s1, s3]
  ring

/-- **A gapped eigenpair is the only eigenvector strictly above its gap**: if `φ` is a unit eigenfunction of `k`
with eigenvalue `c` and remainder norm at most `ρ`, and `ψ` is a unit eigenfunction with eigenvalue `d`,
`ρ² < d²`, then `⟨ψ, φ⟩² = 1`, `d = c`, and `ψ − ⟨ψ, φ⟩ φ` has zero `L²` norm. The remainder sends
`u = ψ − ⟨ψ, φ⟩ φ` to `d ψ − c ⟨ψ, φ⟩ φ`, whose square integral is `d²(1 − a²) + a²(d − c)²`.
DERIVED: `1` the normalization; `2` the square. -/
theorem top_unique {k : X → X → ℝ} (hk : Bdd k) {φ : X → ℝ} (hφm : Measurable φ) {Bφ : ℝ}
    (hφb : ∀ x, |φ x| ≤ Bφ) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ}
    (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) {C : ℝ}
    (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C) (hb : ∀ x y, |rem k c φ x y| ≤ C)
    {ρ : ℝ} (hR : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ)
    {ψ : X → ℝ} (hψm : Measurable ψ) {Bψ : ℝ} (hψb : ∀ x, |ψ x| ≤ Bψ) (hψ1 : ∫ x, ψ x ^ 2 ∂μ = 1)
    {d : ℝ} (heigψ : ∀ z, ∫ y, k z y * ψ y ∂μ = d * ψ z) (hρd : ρ ^ 2 < d ^ 2) :
    (∫ x, ψ x * φ x ∂μ) ^ 2 = 1 ∧ d = c ∧
      ∫ x, (ψ x - (∫ x, ψ x * φ x ∂μ) * φ x) ^ 2 ∂μ = 0 := by
  set a := ∫ x, ψ x * φ x ∂μ with ha
  obtain ⟨Ck, hCk⟩ := hk.bdd
  have hr := Bdd.rem hk hφm hφb (c := c)
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hRu : ∀ z, ∫ y, rem k c φ z y * (ψ y - a * φ y) ∂μ = d * ψ z + (-(c * a)) * φ z := by
    intro z
    have hRφ := rem_row_orth (μ := μ) hk hφm hφb hφ1 heig z
    have i1 : Integrable (fun y => rem k c φ z y * ψ y) μ :=
      integrable_mul_of_bdd (hr.row z) hψm (hCr z) hψb
    have i2 : Integrable (fun y => rem k c φ z y * φ y) μ :=
      integrable_mul_of_bdd (hr.row z) hφm (hCr z) hφb
    have e : (fun y => rem k c φ z y * (ψ y - a * φ y))
        = fun y => rem k c φ z y * ψ y - a * (rem k c φ z y * φ y) := by funext y; ring
    rw [e, integral_sub i1 (i2.const_mul a), integral_const_mul, hRφ, mul_zero, sub_zero]
    have ik : Integrable (fun y => k z y * ψ y) μ := integrable_mul_of_bdd (hk.row z) hψm (hCk z) hψb
    have iψφ : Integrable (fun y => ψ y * φ y) μ := integrable_mul_of_bdd hψm hφm hψb hφb
    have e2 : (fun y => rem k c φ z y * ψ y) = fun y => k z y * ψ y - (c * φ z) * (ψ y * φ y) := by
      funext y; simp only [MassGap.KernelPower.rem]; ring
    rw [e2, integral_sub ik (iψφ.const_mul _), integral_const_mul, heigψ z]
    ring
  have hum : Measurable (fun y => ψ y - a * φ y) := hψm.sub (measurable_const.mul hφm)
  have hub : ∀ y, |ψ y - a * φ y| ≤ Bψ + |a| * Bφ := fun y =>
    (abs_sub _ _).trans (add_le_add (hψb y)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb y) (abs_nonneg a)))
  have hsq := sq_apply_le (μ := μ) hm hC0 hb hum hub
  simp_rw [hRu] at hsq
  have eu : ∫ x, (ψ x - a * φ x) ^ 2 ∂μ = ∫ x, (1 * ψ x + (-a) * φ x) ^ 2 ∂μ := by
    congr 1; funext x; ring
  rw [eu, int_sq_comb hφm hψm hφb hψb, int_sq_comb hφm hψm hφb hψb, hφ1, hψ1, ← ha] at hsq
  have hu0 : 0 ≤ 1 - a ^ 2 := by
    have h0 : 0 ≤ ∫ x, (1 * ψ x + (-a) * φ x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    rw [int_sq_comb hφm hψm hφb hψb, hφ1, hψ1, ← ha] at h0
    calc (0 : ℝ) ≤ _ := h0
      _ = 1 - a ^ 2 := by ring
  have hK2 : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ^ 2 ≤ ρ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hR 2
  have key : d ^ 2 * (1 - a ^ 2) + a ^ 2 * (d - c) ^ 2 ≤ ρ ^ 2 * (1 - a ^ 2) := by
    calc d ^ 2 * (1 - a ^ 2) + a ^ 2 * (d - c) ^ 2
        = d ^ 2 * 1 + 2 * d * -(c * a) * a + (-(c * a)) ^ 2 * 1 := by ring
      _ ≤ ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ^ 2 * (1 ^ 2 * 1 + 2 * 1 * -a * a + (-a) ^ 2 * 1) := hsq
      _ = ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ^ 2 * (1 - a ^ 2) := by ring
      _ ≤ ρ ^ 2 * (1 - a ^ 2) := mul_le_mul_of_nonneg_right hK2 hu0
  have hs0 : 1 - a ^ 2 ≤ 0 := by
    refine not_lt.mp fun hcon => ?_
    have := mul_pos (sub_pos.mpr hρd) hcon
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (d - c))]
  have ha2 : a ^ 2 = 1 := by linarith
  have hdc : (d - c) ^ 2 ≤ 0 := by
    rw [ha2] at key; nlinarith
  have hdc0 : d - c = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp (le_antisymm hdc (sq_nonneg _))
  refine ⟨ha2, by linarith, ?_⟩
  rw [eu, int_sq_comb hφm hψm hφb hψb, hφ1, hψ1, ← ha]
  linear_combination (-1 : ℝ) * ha2

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {ac : G → X → X}

/-- **A gapped eigenfunction with nonzero mean is centre-invariant**: if `k` commutes with a measure-preserving
action, `φ` is a gapped unit eigenfunction (`ρ² < c²`) and `∫ φ ≠ 0`, then `φ (g · x) = φ x` at every `x`.
`φ ∘ g` is a unit eigenfunction with the same eigenvalue, so `top_unique` makes it `±φ` almost everywhere; the
mean fixes the sign; the eigen equation turns the almost-everywhere equality into a pointwise one.
DERIVED: `1` the normalization and the sign. -/
theorem phi_act_of_gap {k : X → X → ℝ} (hk : Bdd k) (hA : CentreAction μ ac)
    (hinv : ∀ g x y, k (ac g x) (ac g y) = k x y) {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ}
    (hφb : ∀ x, |φ x| ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ}
    (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (hc : c ≠ 0) {C : ℝ}
    (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C) (hb : ∀ x y, |rem k c φ x y| ≤ C)
    {ρ : ℝ} (hR : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ) (hρc : ρ ^ 2 < c ^ 2)
    (hint : ∫ x, φ x ∂μ ≠ 0) (g : G) (z : X) : φ (ac g z) = φ z := by
  set ψ : X → ℝ := fun x => φ (ac g x) with hψ
  have hψm : Measurable ψ := hφm.comp (hA.meas g)
  have hψb : ∀ x, |ψ x| ≤ B := fun x => hφb _
  have hψ1 : ∫ x, ψ x ^ 2 ∂μ = 1 := (hA.integral_comp g (fun x => φ x ^ 2)).trans hφ1
  have heigψ : ∀ z, ∫ y, k z y * ψ y ∂μ = c * ψ z := by
    intro z
    have h1 := heig (ac g z)
    rw [← hA.integral_comp g (fun y => k (ac g z) y * φ y)] at h1
    simp only [hinv] at h1
    exact h1
  obtain ⟨-, -, hu0⟩ := top_unique hk hφm hφb hφ1 heig hm hC0 hb hR hψm hψb hψ1 heigψ hρc
  set a := ∫ x, ψ x * φ x ∂μ with ha
  have hint2 : Integrable (fun x => (ψ x - a * φ x) ^ 2) μ :=
    integrable_of_bdd ((hψm.sub (measurable_const.mul hφm)).pow_const 2) (C := (B + |a| * B) ^ 2)
      (fun x => by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        exact (abs_sub _ _).trans (add_le_add (hψb x)
          (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb x) (abs_nonneg a))))
  have hae2 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint2).mp hu0
  have hae : ∀ᵐ x ∂μ, ψ x = a * φ x := by
    filter_upwards [hae2] with x hx
    have : (ψ x - a * φ x) ^ 2 = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  have hmean : ∫ x, ψ x ∂μ = a * ∫ x, φ x ∂μ := by
    rw [← integral_const_mul]; exact integral_congr_ae hae
  have hmean' : ∫ x, ψ x ∂μ = ∫ x, φ x ∂μ := hA.integral_comp g φ
  have ha1 : a = 1 := by
    have h0 : (a - 1) * ∫ x, φ x ∂μ = 0 := by rw [sub_mul, ← hmean, hmean', one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · exact absurd h1 hint
  have hae' : ψ =ᵐ[μ] φ := by
    filter_upwards [hae] with x hx
    rw [hx, ha1, one_mul]
  have h3 := heigψ z
  have h4 : ∫ y, k z y * ψ y ∂μ = ∫ y, k z y * φ y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae'] with y hy
    rw [hy]
  rw [h4, heig z] at h3
  exact (mul_left_cancel₀ hc h3).symm

/-! ## 2. The trace split, and the remainder along the chain -/

/-- **The zero-flux projection commutes with a hop on the left**: `zk(a ∗ f) = a ∗ zk f`. No invariance is used:
`zk` averages the second variable, the hop acts on the first. DERIVED: `|G|⁻¹` the average. -/
theorem zk_left_conv {a f : X → X → ℝ} (ha : Bdd a) (hf : Bdd f) :
    zk (conv μ a f) ac = conv μ a (zk f ac) := by
  obtain ⟨Ca, hCa0, hCa⟩ := bdd_nonneg_bound ha
  obtain ⟨Cf, hCf0, hCf⟩ := bdd_nonneg_bound hf
  funext x z
  have hint : ∀ g, Integrable (fun y => a x y * f y (ac g z)) μ := fun g =>
    int_mul2 (ha.row x) (hf.col (ac g z)) (hCa x) (fun y => hCf y _)
  show (Fintype.card G : ℝ)⁻¹ * ∑ g, conv μ a f x (ac g z) = ∫ y, a x y * zk f ac y z ∂μ
  have e : (fun y => a x y * zk f ac y z)
      = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, a x y * f y (ac g z) := by
    funext y
    show a x y * ((Fintype.card G : ℝ)⁻¹ * ∑ g, f y (ac g z)) = _
    rw [mul_left_comm, Finset.mul_sum]
  rw [e, integral_const_mul, integral_finsetSum _ fun g _ => hint g]
  rfl

/-- **The flux block commutes with a hop on the left**: `fk(a ∗ f) = a ∗ fk f`. DERIVED: no numeral. -/
theorem fk_left_conv {a f : X → X → ℝ} (ha : Bdd a) (hf : Bdd f) (hA : CentreAction μ ac) :
    fk (conv μ a f) ac = conv μ a (fk f ac) := by
  obtain ⟨Ca, hCa0, hCa⟩ := bdd_nonneg_bound ha
  obtain ⟨Cf, hCf0, hCf⟩ := bdd_nonneg_bound hf
  have bz := bdd_zk hf hA
  have hz := zk_left_conv (ac := ac) (μ := μ) ha hf
  funext x z
  show conv μ a f x z - zk (conv μ a f) ac x z = ∫ y, a x y * fk f ac y z ∂μ
  rw [hz]
  show (∫ y, a x y * f y z ∂μ) - (∫ y, a x y * zk f ac y z ∂μ)
    = ∫ y, a x y * (f y z - zk f ac y z) ∂μ
  rw [← integral_sub (int_mul2 (ha.row x) (hf.col z) (hCa x) (fun y => hCf y z))
    (int_mul2 (ha.row x) (bz.col z) (hCa x) (fun y => abs_zk_le hCf y z))]
  congr 1; funext y; ring

/-- **The remainder's zero-flux trace falls by `‖R‖²` per hop.** DERIVED: `1` the hop; `2` the square. -/
theorem hs_zk_rem_step {r : X → X → ℝ} {C : ℝ} (hrm : Measurable (Function.uncurry r)) (hC0 : 0 ≤ C)
    (hrb : ∀ x y, |r x y| ≤ C) (hA : CentreAction μ ac) (j : ℕ) :
    hs μ (zk (iter μ r (j + 1)) ac) ≤ ‖kernelCLM r C hrm hC0 hrb μ μ‖ ^ 2 * hs μ (zk (iter μ r j) ac) := by
  have hr : Bdd r := ⟨hrm, C, hrb⟩
  show hs μ (zk (conv μ r (iter μ r j)) ac) ≤ _
  rw [zk_left_conv hr (hr.iter j)]
  exact hs_conv_le_norm hrm hC0 hrb (bdd_zk (hr.iter j) hA)

/-- **The remainder's flux trace falls by `‖R‖²` per hop.** DERIVED: `1` the hop; `2` the square. -/
theorem hs_fk_rem_step {r : X → X → ℝ} {C : ℝ} (hrm : Measurable (Function.uncurry r)) (hC0 : 0 ≤ C)
    (hrb : ∀ x y, |r x y| ≤ C) (hA : CentreAction μ ac) (j : ℕ) :
    hs μ (fk (iter μ r (j + 1)) ac) ≤ ‖kernelCLM r C hrm hC0 hrb μ μ‖ ^ 2 * hs μ (fk (iter μ r j) ac) := by
  have hr : Bdd r := ⟨hrm, C, hrb⟩
  show hs μ (fk (conv μ r (iter μ r j)) ac) ≤ _
  rw [fk_left_conv hr (hr.iter j) hA]
  exact hs_conv_le_norm hrm hC0 hrb (bdd_fk (hr.iter j) hA)

/-- **The top state carries no flux**: for a centre-invariant eigenfunction, the flux block of `k^{∗(j+1)}`
is the flux block of the remainder's power, `fk(k^{∗(j+1)}) = fk(R^{∗(j+1)})`. DERIVED: `|G|⁻¹ · |G| = 1`. -/
theorem fk_iter_eq {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x) {φ : X → ℝ}
    (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1) {c : ℝ}
    (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (hφinv : ∀ g x, φ (ac g x) = φ x) (j : ℕ) :
    fk (iter μ k j) ac = fk (iter μ (rem k c φ) j) ac := by
  funext x y
  show iter μ k j x y - (Fintype.card G : ℝ)⁻¹ * ∑ g, iter μ k j x (ac g y)
    = iter μ (rem k c φ) j x y - (Fintype.card G : ℝ)⁻¹ * ∑ g, iter μ (rem k c φ) j x (ac g y)
  have e : ∀ g, iter μ k j x (ac g y) = c ^ (j + 1) * φ x * φ y + iter μ (rem k c φ) j x (ac g y) :=
    fun g => by rw [iter_decomp hk hsym hφm hφb hφ1 heig j x (ac g y), hφinv]
  rw [Finset.sum_congr rfl (fun g _ => e g), iter_decomp hk hsym hφm hφb hφ1 heig j x y,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
    ← mul_assoc ((Fintype.card G : ℝ)⁻¹), inv_mul_cancel₀ (card_pos_real (G := G)).ne', one_mul]
  ring

end Generic

/-! ## 3. On the slice -/

section Lattice

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The transfer gap at one aperture**: `φ` is a bounded measurable unit eigenfunction of the whole slice
transfer `K = kT` with eigenvalue `c ≠ 0`, and the remainder `K − c φ⊗φ` has `L²` operator norm at most `ρ`.
No sector is selected. DERIVED: `1` the normalization; `0`. -/
def TransferGapAt (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β c : ℝ)
    (φ : MassGap.SliceCentreAction.Cfg i T N → ℝ) (ρ : ℝ) : Prop :=
  Measurable φ ∧ (∃ B : ℝ, ∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂(hS i T N) = 1 ∧ c ≠ 0 ∧
    (∀ z, ∫ y, kT i T N β z y * φ y ∂(hS i T N) = c * φ z) ∧
    ∃ C : ℝ, ∃ hm : Measurable (Function.uncurry (rem (kT i T N β) c φ)), ∃ hC0 : 0 ≤ C,
      ∃ hb : ∀ x y, |rem (kT i T N β) c φ x y| ≤ C,
        ‖kernelCLM (rem (kT i T N β) c φ) C hm hC0 hb (hS i T N) (hS i T N)‖ ≤ ρ

variable (N) in
/-- **The transfer gap reads the measured mass** (assumed): there are a dimensionless `c > 0` and a measured
length `D > 0` such that, eventually in `β`, the unit reads a positive mass `m′`, and at every power-of-two
side `n ≥ 2` with `D ≤ n m′` and every direction `i` the whole slice transfer at aperture `Tr n i` has an
eigenpair whose remainder norm is at most `|λ| e^{−c m′}`, and an anchor `j₀` with `4(j₀ + 1) ≤ n` at which
the zero-flux hop rate is within `e^{−c m′}` of the top: `λ² Z₀(j₀) ≤ e^{c m′} Z₀(j₀ + 1)`.
DERIVED: `2` the least side and the square of the top; `4` the quarter side; `1` the hop. -/
def TransferGapMeasured (hN : N ≠ 0) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ D : ℝ, 0 < D ∧ ∀ᶠ β in atTop,
    0 < (measMassOf (periodicState hN β) tensorEnergy).toReal ∧
    ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
      D ≤ (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal → ∀ i : Fin 4,
      ∃ lam : ℝ, ∃ φ : MassGap.SliceCentreAction.Cfg i (CentreSectorSeed.Tr n i) N → ℝ, ∃ ρ : ℝ,
        ∃ j₀ : ℕ,
        TransferGapAt N i (CentreSectorSeed.Tr n i) β lam φ ρ ∧
        ρ ≤ |lam| * Real.exp (-(c * (measMassOf (periodicState hN β) tensorEnergy).toReal)) ∧
        4 * (j₀ + 1) ≤ n ∧
        lam ^ 2 * relayZ0 N i (CentreSectorSeed.Tr n i) β j₀
          ≤ Real.exp (c * (measMassOf (periodicState hN β) tensorEnergy).toReal)
            * relayZ0 N i (CentreSectorSeed.Tr n i) β (j₀ + 1)

variable {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ}

/-- **A gapped eigenpair of the slice transfer is the Jentzsch top**: if `ρ² < λ²`, then `λ = ‖K‖` and
`∫ φ ≠ 0`. The strictly positive top eigenfunction `φ₀` of `JentzschKT.exists_pos_eigen_kT` has eigenvalue
`‖K‖ ≥ |λ|`, so `top_unique` gives `‖K‖ = λ` and `φ₀ = ±φ` almost everywhere, and `∫ φ₀ > 0`.
DERIVED: `1` the kernel bound and the normalization; `0` the mean. -/
theorem top_of_gap (hβ : 0 ≤ β) {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ^ 2 < lam ^ 2) :
    ∫ x, φ x ∂(hS i T N) ≠ 0 ∧
      lam = ‖kernelCLM (kT i T N β) 1 (continuous_kT β).measurable zero_le_one
        (abs_kT_le (NeZero.ne N) hβ) (hS i T N) (hS i T N)‖ := by
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hl, heig, C, hm, hC0, hb, hR⟩ := h
  obtain ⟨-, φ₀, hφ₀m, hφ₀b, ⟨c₀, hc₀, hφ₀low⟩, hφ₀1, heig₀⟩ :=
    JentzschKT.exists_pos_eigen_kT (μ := i) (T := T) (N := N) (NeZero.ne N) hβ
  set K1 := ‖kernelCLM (kT i T N β) 1 (continuous_kT β).measurable zero_le_one
    (abs_kT_le (NeZero.ne N) hβ) (hS i T N) (hS i T N)‖ with hK1
  have hlamK : lam ^ 2 ≤ K1 ^ 2 := by
    have h1 := sq_apply_le (μ := hS i T N) (continuous_kT β).measurable zero_le_one
      (abs_kT_le (NeZero.ne N) hβ) hφm hφb
    simp_rw [heig, mul_pow] at h1
    rw [integral_const_mul, hφ1, mul_one, mul_one] at h1
    exact h1
  have hk : Bdd (kT i T N β) := bdd_kT (NeZero.ne N) hβ
  obtain ⟨ha2, hdc, hu0⟩ := top_unique hk hφm hφb hφ1 heig hm hC0 hb hR hφ₀m hφ₀b hφ₀1 heig₀
    (lt_of_lt_of_le hρ hlamK)
  refine ⟨fun h0 => ?_, hdc.symm⟩
  set a := ∫ x, φ₀ x * φ x ∂(hS i T N) with ha
  have hint2 : Integrable (fun x => (φ₀ x - a * φ x) ^ 2) (hS i T N) :=
    integrable_of_bdd ((hφ₀m.sub (measurable_const.mul hφm)).pow_const 2)
      (C := (1 / K1 + |a| * B) ^ 2)
      (fun x => by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        exact (abs_sub _ _).trans (add_le_add (hφ₀b x)
          (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hφb x) (abs_nonneg a))))
  have hae2 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint2).mp hu0
  have hae : ∀ᵐ x ∂(hS i T N), φ₀ x = a * φ x := by
    filter_upwards [hae2] with x hx
    have : (φ₀ x - a * φ x) ^ 2 = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  have hmean : ∫ x, φ₀ x ∂(hS i T N) = a * ∫ x, φ x ∂(hS i T N) := by
    rw [← integral_const_mul]; exact integral_congr_ae hae
  rw [h0, mul_zero] at hmean
  have hpos : c₀ ≤ ∫ x, φ₀ x ∂(hS i T N) := by
    have hi : Integrable φ₀ (hS i T N) := integrable_of_bdd hφ₀m hφ₀b
    have := integral_mono (integrable_const c₀) hi (fun x => hφ₀low x)
    simpa using this
  linarith

/-- **The top eigenfunction of a gapped slice transfer is centre-invariant**: `φ (act g x) = φ x`.
DERIVED: no numeral. -/
theorem phi_act_kT (hβ : 0 ≤ β) {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ^ 2 < lam ^ 2) (g : Cen i N)
    (x : MassGap.SliceCentreAction.Cfg i T N) : φ (act g x) = φ x := by
  have hint := (top_of_gap hβ h hρ).1
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hl, heig, C, hm, hC0, hb, hR⟩ := h
  exact phi_act_of_gap (bdd_kT (NeZero.ne N) hβ) centreAction (fun g x y => kT_act g β x y) hφm hφb hφ1
    heig hl hm hC0 hb hR hρ hint g x

/-- The square of the gap bound. DERIVED: `2` the square. -/
theorem sq_le_of_gap {lam ρ e : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ |lam| * e) : ρ ^ 2 ≤ lam ^ 2 * e ^ 2 := by
  have := pow_le_pow_left₀ hρ0 hρ 2
  rwa [mul_pow, sq_abs] at this

/-- `ρ² < λ²` from a measured gap. DERIVED: `2` the square. -/
theorem sq_lt_of_gap {lam ρ x : ℝ} (hl : lam ≠ 0) (hρ0 : 0 ≤ ρ) (hx : 0 < x)
    (hρ : ρ ≤ |lam| * Real.exp (-x)) : ρ ^ 2 < lam ^ 2 := by
  have h1 := sq_le_of_gap hρ0 hρ
  have he : Real.exp (-x) ^ 2 < 1 := by
    have : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-x)]
  have hl2 : 0 < lam ^ 2 := by positivity
  nlinarith

/-- The data of a gapped slice, unpacked with the invariance. DERIVED: no numeral. -/
theorem gap_data (hβ : 0 ≤ β) {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ^ 2 < lam ^ 2) :
    ∃ B C : ℝ, ∃ hm : Measurable (Function.uncurry (rem (kT i T N β) lam φ)), ∃ hC0 : 0 ≤ C,
      ∃ hb : ∀ x y, |rem (kT i T N β) lam φ x y| ≤ C,
      Measurable φ ∧ (∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂(hS i T N) = 1 ∧ lam ≠ 0 ∧
      (∀ z, ∫ y, kT i T N β z y * φ y ∂(hS i T N) = lam * φ z) ∧
      ‖kernelCLM (rem (kT i T N β) lam φ) C hm hC0 hb (hS i T N) (hS i T N)‖ ≤ ρ ∧
      (∀ g x, φ (act g x) = φ x) := by
  have hinv := phi_act_kT hβ h hρ
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hl, heig, C, hm, hC0, hb, hR⟩ := h
  exact ⟨B, C, hm, hC0, hb, hφm, hφb, hφ1, hl, heig, hR, hinv⟩

/-- The remainder norm bound is nonnegative. DERIVED: `0`. -/
theorem rho_nonneg {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) : 0 ≤ ρ := by
  obtain ⟨-, -, -, -, -, C, hm, hC0, hb, hR⟩ := h
  exact (norm_nonneg _).trans hR

variable (N) in
/-- **The remainder's zero-flux trace** at chain index `j`: `hs(zk(R^{∗(j+1)}))`, `R = K − λ φ⊗φ`.
DERIVED: no numeral. -/
def zeroRem (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β lam : ℝ)
    (φ : MassGap.SliceCentreAction.Cfg i T N → ℝ) (j : ℕ) : ℝ :=
  hs (hS i T N) (zk (iter (hS i T N) (rem (kT i T N β) lam φ) j) (act (μ := i) (T := T) (N := N)))

/-- **The flux trace is the remainder's flux trace**: `F(j) = hs(fk(R^{∗(j+1)}))`. DERIVED: no numeral. -/
theorem fluxTrace_eq_rem (hβ : 0 ≤ β) {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ^ 2 < lam ^ 2) (j : ℕ) :
    fluxTrace N i T β j
      = hs (hS i T N) (fk (iter (hS i T N) (rem (kT i T N β) lam φ) j) (act (μ := i) (T := T) (N := N))) := by
  obtain ⟨B, C, hm, hC0, hb, hφm, hφb, hφ1, hl, heig, hR, hinv⟩ := gap_data hβ h hρ
  unfold fluxTrace relayZ relayZ0
  rw [← hs_fk (bdd_iterK (N := N) (i := i) (T := T) hβ j) (centreAction (μ := i) (T := T) (N := N)),
    fk_iter_eq (bdd_kT (μ := i) (T := T) (NeZero.ne N) hβ) (kT_symm β) hφm hφb hφ1 heig hinv j]

/-- **The zero-flux trace splits into the top and the remainder's zero-flux trace**:
`Z₀(j) = λ^{2(j+1)} + hs(zk(R^{∗(j+1)}))`. DERIVED: `2`, `1`. -/
theorem relayZ0_eq_rem (hβ : 0 ≤ β) {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ^ 2 < lam ^ 2) (j : ℕ) :
    relayZ0 N i T β j = lam ^ (2 * (j + 1)) + zeroRem N i T β lam φ j := by
  have hF := fluxTrace_eq_rem hβ h hρ j
  obtain ⟨B, C, hm, hC0, hb, hφm, hφb, hφ1, hl, heig, hR, hinv⟩ := gap_data hβ h hρ
  have hk := bdd_kT (N := N) (μ := i) (T := T) (NeZero.ne N) hβ
  have hr := (Bdd.rem hk hφm hφb (c := lam)).iter (μ := hS i T N) j
  have hZ : relayZ N i T β j
      = lam ^ (2 * (j + 1)) + hs (hS i T N) (iter (hS i T N) (rem (kT i T N β) lam φ) j) :=
    hs_iter_decomp hk (kT_symm β) hφm hφb hφ1 heig j
  have hfr := hs_fk (μ := hS i T N) hr (centreAction (μ := i) (T := T) (N := N))
  unfold fluxTrace at hF
  unfold zeroRem
  linarith

/-- **The flux trace falls by `ρ²` per hop**: the flux sector lies in the remainder. DERIVED: `1`, `2`. -/
theorem flux_step (hβ : 0 ≤ β) {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ^ 2 < lam ^ 2) (k : ℕ) :
    fluxTrace N i T β (k + 1) ≤ ρ ^ 2 * fluxTrace N i T β k := by
  rw [fluxTrace_eq_rem hβ h hρ (k + 1), fluxTrace_eq_rem hβ h hρ k]
  obtain ⟨B, C, hm, hC0, hb, hφm, hφb, hφ1, hl, heig, hR, hinv⟩ := gap_data hβ h hρ
  refine (hs_fk_rem_step hm hC0 hb (centreAction (μ := i) (T := T) (N := N)) k).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR 2) (hs_nonneg _)

/-- **The zero-flux remainder falls by `ρ²` per hop.** DERIVED: `1`, `2`. -/
theorem zeroRem_step (hβ : 0 ≤ β) {lam ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hρ : ρ ^ 2 < lam ^ 2) (j₀ : ℕ) :
    ∀ t : ℕ, zeroRem N i T β lam φ (j₀ + t) ≤ (ρ ^ 2) ^ t * zeroRem N i T β lam φ j₀ := by
  obtain ⟨B, C, hm, hC0, hb, hφm, hφb, hφ1, hl, heig, hR, hinv⟩ := gap_data hβ h hρ
  have hK2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    have hs1 : zeroRem N i T β lam φ (j₀ + t + 1)
        ≤ ‖kernelCLM (rem (kT i T N β) lam φ) C hm hC0 hb (hS i T N) (hS i T N)‖ ^ 2
          * zeroRem N i T β lam φ (j₀ + t) :=
      hs_zk_rem_step hm hC0 hb (centreAction (μ := i) (T := T) (N := N)) (j₀ + t)
    have hz0 : 0 ≤ zeroRem N i T β lam φ (j₀ + t) := hs_nonneg _
    calc zeroRem N i T β lam φ (j₀ + (t + 1)) = zeroRem N i T β lam φ (j₀ + t + 1) := rfl
      _ ≤ ‖kernelCLM (rem (kT i T N β) lam φ) C hm hC0 hb (hS i T N) (hS i T N)‖ ^ 2
          * zeroRem N i T β lam φ (j₀ + t) := hs1
      _ ≤ ρ ^ 2 * zeroRem N i T β lam φ (j₀ + t) := mul_le_mul_of_nonneg_right hK2 hz0
      _ ≤ ρ ^ 2 * ((ρ ^ 2) ^ t * zeroRem N i T β lam φ j₀) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = (ρ ^ 2) ^ (t + 1) * zeroRem N i T β lam φ j₀ := by rw [pow_succ]; ring

/-! ## 4. The two reads from one gap -/

/-- **The hop clause from the transfer gap and the anchor**: with `ρ ≤ |λ| e^{−c m}` and
`λ² Z₀(j₀) ≤ e^{c m} Z₀(j₀ + 1)`, the flux hop rate is at most `e^{−c m}` times the zero-flux rate at `j₀`.
DERIVED: `2` the square of the top. -/
theorem hopClause_of_gapAt (hβ : 0 ≤ β) {lam ρ c m : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hcm : 0 < c * m) (hρ : ρ ≤ |lam| * Real.exp (-(c * m)))
    {j₀ : ℕ} (hanc : lam ^ 2 * relayZ0 N i T β j₀ ≤ Real.exp (c * m) * relayZ0 N i T β (j₀ + 1)) :
    HopClause N i T β j₀ (Real.exp (-(c * m))) := by
  have hρ0 := rho_nonneg h
  have hρ2 := sq_lt_of_gap h.2.2.2.1 hρ0 hcm hρ
  have hsq := sq_le_of_gap hρ0 hρ
  intro k _
  have hE : Real.exp (-(c * m)) * Real.exp (c * m) = 1 := by rw [← Real.exp_add]; simp
  have hF := flux_step hβ h hρ2 k
  have hFk := fluxTrace_nonneg (N := N) (i := i) (T := T) hβ k
  have hZ0 := relayZ0_pos (N := N) (i := i) (T := T) hβ j₀
  calc fluxTrace N i T β (k + 1) * relayZ0 N i T β j₀
      ≤ (ρ ^ 2 * fluxTrace N i T β k) * relayZ0 N i T β j₀ := mul_le_mul_of_nonneg_right hF hZ0.le
    _ ≤ (lam ^ 2 * Real.exp (-(c * m)) ^ 2 * fluxTrace N i T β k) * relayZ0 N i T β j₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hFk) hZ0.le
    _ = Real.exp (-(c * m)) ^ 2 * fluxTrace N i T β k * (lam ^ 2 * relayZ0 N i T β j₀) := by ring
    _ ≤ Real.exp (-(c * m)) ^ 2 * fluxTrace N i T β k * (Real.exp (c * m) * relayZ0 N i T β (j₀ + 1)) :=
        mul_le_mul_of_nonneg_left hanc (mul_nonneg (sq_nonneg _) hFk)
    _ = Real.exp (-(c * m)) * fluxTrace N i T β k * relayZ0 N i T β (j₀ + 1)
          * (Real.exp (-(c * m)) * Real.exp (c * m)) := by ring
    _ = Real.exp (-(c * m)) * fluxTrace N i T β k * relayZ0 N i T β (j₀ + 1) := by rw [hE, mul_one]

/-- The real-number step of the anchor: `l² (L + E) ≤ u (l² L + E')`, `E' ≤ l² v² E`, `u v = 1`, `v < 1`
give `E ≤ u L`. DERIVED: `1`, `2`. -/
theorem anchor_real {l2 L E E' u v r2 : ℝ} (hl2 : 0 < l2) (hE0 : 0 ≤ E) (hu0 : 0 < u) (huv : u * v = 1)
    (hv1 : v < 1) (hstep : E' ≤ r2 * E) (hsq : r2 ≤ l2 * v ^ 2)
    (hanc : l2 * (L + E) ≤ u * (l2 * L + E')) : E ≤ u * L := by
  have hE'b : E' ≤ l2 * v ^ 2 * E := hstep.trans (mul_le_mul_of_nonneg_right hsq hE0)
  have h1 : l2 * (L + E) ≤ l2 * (u * L + v * E) := by
    calc l2 * (L + E) ≤ u * (l2 * L + E') := hanc
      _ ≤ u * (l2 * L + l2 * v ^ 2 * E) := mul_le_mul_of_nonneg_left (by linarith) hu0.le
      _ = l2 * (u * L + (u * v) * v * E) := by ring
      _ = l2 * (u * L + v * E) := by rw [huv, one_mul]
  have h2 : L + E ≤ u * L + v * E := le_of_mul_le_mul_left h1 hl2
  have h3 : E * (1 - v) ≤ (u * L) * (1 - v) := by
    have e : u * L * (1 - v) = u * L - (u * v) * L := by ring
    rw [e, huv]; linarith
  exact le_of_mul_le_mul_right h3 (by linarith)

/-- **The anchor bounds the zero-flux excited weight at `j₀`**: with the gap, `λ² Z₀(j₀) ≤ e^{c m} Z₀(j₀ + 1)`
gives `hs(zk(R^{∗(j₀+1)})) ≤ e^{c m} λ^{2(j₀+1)}`. DERIVED: `2`, `1`. -/
theorem zeroRem_anchor (hβ : 0 ≤ β) {lam ρ c m : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hcm : 0 < c * m) (hρ : ρ ≤ |lam| * Real.exp (-(c * m)))
    {j₀ : ℕ} (hanc : lam ^ 2 * relayZ0 N i T β j₀ ≤ Real.exp (c * m) * relayZ0 N i T β (j₀ + 1)) :
    zeroRem N i T β lam φ j₀ ≤ Real.exp (c * m) * lam ^ (2 * (j₀ + 1)) := by
  have hρ0 := rho_nonneg h
  have hl := h.2.2.2.1
  have hρ2 := sq_lt_of_gap hl hρ0 hcm hρ
  have hsq := sq_le_of_gap hρ0 hρ
  have hstep : zeroRem N i T β lam φ (j₀ + 1) ≤ ρ ^ 2 * zeroRem N i T β lam φ j₀ := by
    have := zeroRem_step hβ h hρ2 j₀ 1
    rwa [pow_one] at this
  rw [relayZ0_eq_rem hβ h hρ2 j₀, relayZ0_eq_rem hβ h hρ2 (j₀ + 1)] at hanc
  have hLb : lam ^ (2 * (j₀ + 1 + 1)) = lam ^ 2 * lam ^ (2 * (j₀ + 1)) := by
    rw [← pow_add]; congr 1; ring
  rw [hLb] at hanc
  have huv : Real.exp (c * m) * Real.exp (-(c * m)) = 1 := by rw [← Real.exp_add]; simp
  have hv1 : Real.exp (-(c * m)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hl2 : 0 < lam ^ 2 := by positivity
  exact anchor_real (E := zeroRem N i T β lam φ j₀) hl2 (hs_nonneg _) (Real.exp_pos _) huv hv1 hstep hsq hanc

/-- **The zero-flux defect from the gap and the anchor**: for every `t`,
`relayDefect(j₀ + t) ≤ 2 e^{c m − 2 c m t}`. DERIVED: `2` the factor of the defect bound and the square. -/
theorem relayDefect_le_of_gapAt (hβ : 0 ≤ β) {lam ρ c m : ℝ}
    {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : TransferGapAt N i T β lam φ ρ) (hcm : 0 < c * m) (hρ : ρ ≤ |lam| * Real.exp (-(c * m)))
    {j₀ : ℕ} (hanc : lam ^ 2 * relayZ0 N i T β j₀ ≤ Real.exp (c * m) * relayZ0 N i T β (j₀ + 1))
    (t : ℕ) : relayDefect N i T β (j₀ + t) ≤ 2 * Real.exp (c * m - 2 * (c * m) * t) := by
  have hρ0 := rho_nonneg h
  have hl := h.2.2.2.1
  have hρ2 := sq_lt_of_gap hl hρ0 hcm hρ
  have hsq := sq_le_of_gap hρ0 hρ
  have hA := zeroRem_anchor hβ h hcm hρ hanc
  have hS1 := zeroRem_step hβ h hρ2 j₀ t
  have hLj0 : 0 < lam ^ (2 * (j₀ + t + 1)) := ZeroFluxGap.pow_two_mul_pos hl _
  have hρt : (ρ ^ 2) ^ t ≤ (lam ^ 2 * Real.exp (-(c * m)) ^ 2) ^ t :=
    pow_le_pow_left₀ (sq_nonneg _) hsq t
  have e1 : (lam ^ 2 * Real.exp (-(c * m)) ^ 2) ^ t * (Real.exp (c * m) * lam ^ (2 * (j₀ + 1)))
      = lam ^ (2 * (j₀ + t + 1)) * Real.exp (c * m - 2 * (c * m) * t) := by
    have hval : Real.exp (-(c * m)) ^ (2 * t) * Real.exp (c * m)
        = Real.exp (c * m - 2 * (c * m) * t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [← hval, mul_pow, ← pow_mul, ← pow_mul]
    have : 2 * (j₀ + t + 1) = 2 * t + 2 * (j₀ + 1) := by ring
    rw [this, pow_add]; ring
  have hx : zeroRem N i T β lam φ (j₀ + t)
      ≤ lam ^ (2 * (j₀ + t + 1)) * Real.exp (c * m - 2 * (c * m) * t) := by
    rw [← e1]
    exact hS1.trans (mul_le_mul hρt hA (hs_nonneg _) (pow_nonneg (by positivity) _))
  rw [relayDefect_eq hβ, relayZ0_eq_rem hβ h hρ2 (j₀ + t), relayZ0_eq_rem hβ h hρ2 (2 * (j₀ + t) + 1)]
  have e2 : lam ^ (2 * (2 * (j₀ + t) + 1 + 1)) = (lam ^ (2 * (j₀ + t + 1))) ^ 2 := by
    rw [← pow_mul]; congr 1; ring
  rw [e2]
  have hE0 : 0 ≤ zeroRem N i T β lam φ (j₀ + t) := hs_nonneg _
  have hF0 : 0 ≤ zeroRem N i T β lam φ (2 * (j₀ + t) + 1) := hs_nonneg _
  have hd := ZeroFluxGap.defect_split_le hLj0 hE0 hF0
  have hlog := ZeroFluxGap.log_one_add_le (div_nonneg hE0 hLj0.le)
  have hdiv : zeroRem N i T β lam φ (j₀ + t) / lam ^ (2 * (j₀ + t + 1))
      ≤ Real.exp (c * m - 2 * (c * m) * t) := by
    rw [div_le_iff₀ hLj0]; linarith
  linarith

/-! ## 5. What the transfer gap gives -/

/-- **The transfer gap gives the flux-sector hop gap**, with `s = c/2` and the same `D`.
DERIVED: `2` in `s = c/2`. -/
theorem fluxHopGap_of_transferGap (hN : N ≠ 0) (h : TransferGapMeasured N hN) : FluxHopGap N hN := by
  obtain ⟨c, hc, D, hD, hev⟩ := h
  refine ⟨c / 2, D, half_pos hc, hD, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβev hβ n hp hn hDn i
  obtain ⟨hm, hall⟩ := hβev
  obtain ⟨lam, φ, ρ, j₀, hG, hρ, hj, hanc⟩ := hall n hp hn hDn i
  refine ⟨j₀, hj, ?_⟩
  have e : 2 * (c / 2) * (measMassOf (periodicState hN β) tensorEnergy).toReal
      = c * (measMassOf (periodicState hN β) tensorEnergy).toReal := by ring
  rw [e]
  exact hopClause_of_gapAt hβ hG (mul_pos hc hm) hρ hanc

/-- **The transfer gap gives the long-chain read.** DERIVED: no numeral. -/
theorem longChainRead_of_transferGap (hN : N ≠ 0) (h : TransferGapMeasured N hN) :
    GapFromReads.LongChainRead N hN :=
  TorusContraction.longChainRead_of_hopGap hN (fluxHopGap_of_transferGap hN h)

/-- **The transfer gap forces the measured mass below `D/2`**: at side `2` no anchor has `4(j₀ + 1) ≤ 2`, so the
clause is never asked there. DERIVED: `2` the least side; `4` the quarter side. -/
theorem measMass_lt_of_transferGap (hN : N ≠ 0) (h : TransferGapMeasured N hN) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ β in atTop, 2 * (measMassOf (periodicState hN β) tensorEnergy).toReal < D := by
  obtain ⟨_c, _hc, D, hD, hev⟩ := h
  refine ⟨D, hD, ?_⟩
  filter_upwards [hev] with β hβev
  obtain ⟨-, hall⟩ := hβev
  refine not_le.mp fun hcon => ?_
  obtain ⟨-, -, -, j₀, -, -, hj, -⟩ := hall 2 ⟨1, rfl⟩ le_rfl (by push_cast; linarith) 0
  omega

/-- **The transfer gap gives the sector seed in measured units**, both clauses from one gap. The seed side is a
power of two `n` with `X ≤ n m′ ≤ 2X`, `X = max(D, 4 log 160000/c, 4 log(80000 N³)/c)`.
DERIVED: `2` the window's doubling and `s = c/2`; `4` the quarter side; `80000`, `1/80000` the threshold;
`160000 = 2 · 80000`; `3` in `N³`. -/
theorem sectorSeedMeasured_of_transferGap (hN : N ≠ 0) (h : TransferGapMeasured N hN) :
    SectorSeedMeasured hN := by
  obtain ⟨c, hc, D, hD, hev⟩ := h
  set X := max D (max (4 * Real.log 160000 / c) (2 * Real.log (80000 * (N : ℝ) ^ 3) / (c / 2))) with hX
  have hX0 : 0 < X := lt_max_of_lt_left hD
  refine ⟨2 * X, by linarith, ?_⟩
  -- the measured mass is below `D/2` by the side-2 test with the same `D`
  have hlt2 : ∀ᶠ β in atTop, 2 * (measMassOf (periodicState hN β) tensorEnergy).toReal < D := by
    filter_upwards [hev] with β hβev
    obtain ⟨-, hall⟩ := hβev
    refine not_le.mp fun hcon => ?_
    obtain ⟨-, -, -, j₀, -, -, hj, -⟩ := hall 2 ⟨1, rfl⟩ le_rfl (by push_cast; linarith) 0
    omega
  filter_upwards [hev, hlt2, eventually_ge_atTop (0 : ℝ)] with β hβev hmD hβ
  obtain ⟨hm, hall⟩ := hβev
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
  have hup : ((2 ^ b : ℕ) : ℝ) * m ≤ 2 * X := by
    rw [hcast]
    refine hbu.trans (max_le le_rfl ?_)
    have : D ≤ X := le_max_left _ _
    linarith
  have hDn : D ≤ ((2 ^ b : ℕ) : ℝ) * m := (le_max_left _ _).trans hlo
  have hcm : 0 < c * m := mul_pos hc hm
  refine ⟨hMpos.1, 2 ^ b, ⟨b, rfl⟩, hn2, ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [GapFromReads.ofReal_window hMpos.2.ne]
    exact ENNReal.ofReal_le_ofReal hup
  · obtain ⟨lam, φ, ρ, j₀, hG, hρ, hj, hanc⟩ := hall (2 ^ b) ⟨b, rfl⟩ hn2 hDn i
    have hH := hopClause_of_gapAt hβ hG hcm hρ hanc
    have e : Real.exp (-(c * m)) = Real.exp (-(2 * (c / 2) * m)) := by congr 2; ring
    rw [e] at hH
    exact fluxShareN_le_of_hop hβ hen i hj (half_pos hc) ENNReal.toReal_nonneg hH
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlo))
  · obtain ⟨lam, φ, ρ, j₀, hG, hρ, hj, hanc⟩ := hall (2 ^ b) ⟨b, rfl⟩ hn2 hDn i
    set n := 2 ^ b with hn
    have hjn : j₀ ≤ n / 2 - 1 := by omega
    have ht4 : n ≤ 4 * (n / 2 - 1 - j₀) := by
      obtain ⟨p, hp⟩ := hen
      omega
    have hn4 : 4 ≤ n := by omega
    have hd := relayDefect_le_of_gapAt hβ hG hcm hρ hanc (n / 2 - 1 - j₀)
    rw [Nat.add_sub_cancel' hjn] at hd
    rw [RelayChain.trivialDefectN_eq_relay]
    -- the exponent: c m − 2 c m t ≤ −c n m / 4 ≤ −log 160000
    have ht4r : (n : ℝ) ≤ 4 * ((n / 2 - 1 - j₀ : ℕ) : ℝ) := by exact_mod_cast ht4
    have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hlogX : 4 * Real.log 160000 / c ≤ (n : ℝ) * m :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hlo)
    have hlog : Real.log 160000 ≤ c * ((n : ℝ) * m) / 4 := by
      rw [div_le_iff₀ hc] at hlogX
      linarith
    have hexp : c * m - 2 * (c * m) * ((n / 2 - 1 - j₀ : ℕ) : ℝ) ≤ -Real.log 160000 := by
      have h1 : c * m * 4 ≤ c * m * n := mul_le_mul_of_nonneg_left hn4r hcm.le
      have h2 : c * m * n ≤ c * m * (4 * ((n / 2 - 1 - j₀ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ht4r hcm.le
      nlinarith
    calc relayDefect N i (CentreSectorSeed.Tr n i) β (n / 2 - 1)
        ≤ 2 * Real.exp (c * m - 2 * (c * m) * ((n / 2 - 1 - j₀ : ℕ) : ℝ)) := hd
      _ ≤ 2 * Real.exp (-Real.log 160000) := by gcongr
      _ = 1 / 80000 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

end Lattice

/-! ## 6. The observer's gap -/

section GapSU

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayTreeG MassGap.FlowG MassGap.TimeGroupG MassGap.PeriodicReduceG
  MassGap.FlowClusterG MassGap.MeasuredTower MassGap.MeasuredSpacing

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

/-- **The transfer gap and a measured tower give the observer's gap at the tower's schedule.**
DERIVED: `0` the plane. -/
theorem observerGap_of_transferGap (h : TransferGapMeasured N (NeZero.ne N))
    {βs : ℕ → ℝ} (hT : MeasTowerG (MassGap.SUN.SU N) βs) (Φ : GFlow (MassGap.SUN.SU N))
    (hB : UniformBoundFG (schedAlongG _ βs) Φ.map) {r : ℝ} (hphys : Φ.PhysRange (schedAlongG _ βs) r)
    (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (transferNG (schedAlongG _ βs) (schedOS_alongG _ βs) Φ hB 0 hphys m0) ρ :=
  observerGap_of_sectorSeed (sectorSeedMeasured_of_transferGap (NeZero.ne N) h) hT Φ hB hphys m0

/-- **The transfer gap and the unit tracking the run give the run seed.** DERIVED: no numeral. -/
theorem runSeed_of_transferGap (h : TransferGapMeasured N (NeZero.ne N))
    (hU : SubstrateDecode.UnitTracksRun (N := N) (NeZero.ne N)) : WDeltaRun.RunSeed N :=
  SubstrateFluxRead.runSeed_of_sectorSeedMeasured (NeZero.ne N)
    (sectorSeedMeasured_of_transferGap (NeZero.ne N) h) hU

end GapSU

/-! ## 7. Tests -/

section Tests

variable {N : ℕ} [NeZero N] {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ}

/-- At `β = 0` the remainder of `(1, 1)` is `0`. DERIVED: `0`, `1`. -/
theorem rem_one_zero_coupling :
    rem (kT i T N 0) 1 (fun _ : MassGap.SliceCentreAction.Cfg i T N => (1 : ℝ)) = fun _ _ => 0 := by
  rw [kT_zero]
  funext x y
  simp [rem]

/-- **At `β = 0` the slice transfer is gapped with `ρ = 0`**: `K = 1`, `φ = 1`, `λ = 1`, remainder `0`.
DERIVED: `0`, `1`. -/
theorem transferGapAt_zero_coupling : TransferGapAt N i T 0 1 (fun _ => 1) 0 := by
  have hr := rem_one_zero_coupling (N := N) (i := i) (T := T)
  have hm : Measurable (Function.uncurry
      (rem (kT i T N 0) 1 (fun _ : MassGap.SliceCentreAction.Cfg i T N => (1 : ℝ)))) := by
    rw [hr]; exact measurable_const
  have hb : ∀ x y, |rem (kT i T N 0) 1 (fun _ : MassGap.SliceCentreAction.Cfg i T N => (1 : ℝ)) x y| ≤ 0 := by
    intro x y; rw [hr]; simp
  refine ⟨measurable_const, ⟨1, fun _ => by simp⟩, by simp, one_ne_zero, fun z => ?_,
    0, hm, le_rfl, hb, norm_kernelCLM_le _ _ _ _ _ _ _⟩
  rw [kT_zero]
  simp

/-- **At `β = 0` the zero-flux trace is `1` at every index.** DERIVED: `0`, `1`. -/
theorem relayZ0_zero_coupling (j : ℕ) : relayZ0 N i T 0 j = 1 := by
  have hz : zk (fun _ _ => (1 : ℝ)) (act (μ := i) (T := T) (N := N)) = fun _ _ => 1 := by
    funext x y
    simp only [zk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (card_pos_real (G := Cen i N)).ne'
  unfold relayZ0
  rw [kT_zero, iter_one, hz]
  simp [hs]

/-- **At `β = 0` the anchor clause holds at every index and every `c m ≥ 0`.** DERIVED: `0`, `1`. -/
theorem anchor_zero_coupling (j₀ : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ) ^ 2 * relayZ0 N i T 0 j₀ ≤ Real.exp x * relayZ0 N i T 0 (j₀ + 1) := by
  rw [relayZ0_zero_coupling, relayZ0_zero_coupling]
  simpa using Real.one_le_exp hx

/-- **At `β = 0` both reads follow from the per-aperture clause**: the hop clause at rate `e^{−x}` and the defect
bound, for every `x > 0` and anchor. DERIVED: `0`, `1`, `2`. -/
theorem reads_zero_coupling (j₀ t : ℕ) {x : ℝ} (hx : 0 < x) :
    HopClause N i T 0 j₀ (Real.exp (-x)) ∧ relayDefect N i T 0 (j₀ + t) ≤ 2 * Real.exp (x - 2 * x * t) := by
  have hρ : (0 : ℝ) ≤ |(1 : ℝ)| * Real.exp (-(x * 1)) := by positivity
  have hanc := anchor_zero_coupling (N := N) (i := i) (T := T) j₀ (by positivity : 0 ≤ x * 1)
  have h1 := hopClause_of_gapAt le_rfl transferGapAt_zero_coupling (by simpa using hx) hρ hanc
  have h2 := relayDefect_le_of_gapAt le_rfl transferGapAt_zero_coupling (by simpa using hx) hρ hanc t
  simp only [mul_one] at h1 h2
  exact ⟨h1, h2⟩

/-- **The gap alone does not give the hop clause** (real-number lemma; reading argued): for every `0 < r`, every
`q < 1` and every anchor `j₀` there is a multiplicity `M` with `q (1 + M r^{2(j₀+2)}) < r² (1 + M r^{2(j₀+1)})`.
Reading: top `1`, zero-flux excited level `r` with multiplicity `M`, flux level `r`; the remainder norm is `r`
whatever `M` is and the flux hop rate is `r²`. With `Z₀(j) = 1 + M r^{2(j+1)}` the hop clause at `j₀` and factor
`q` asks `r² Z₀(j₀) ≤ q Z₀(j₀ + 1)`, and the inequality is its strict negation. The anchor clause of
`TransferGapMeasured` excludes this. DERIVED: `2`, `1` the hop. -/
theorem no_hop_from_gap {r q : ℝ} (hr0 : 0 < r) (hq1 : q < 1) (j₀ : ℕ) :
    ∃ M : ℕ, q * (1 + M * r ^ (2 * (j₀ + 2))) < r ^ 2 * (1 + M * r ^ (2 * (j₀ + 1))) := by
  have ha : 0 < r ^ (2 * (j₀ + 2)) := pow_pos hr0 _
  have hpos : 0 < r ^ (2 * (j₀ + 2)) * (1 - q) := mul_pos ha (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt ((q - r ^ 2) / (r ^ (2 * (j₀ + 2)) * (1 - q)))
  refine ⟨M, ?_⟩
  have e : r ^ 2 * r ^ (2 * (j₀ + 1)) = r ^ (2 * (j₀ + 2)) := by rw [← pow_add]; congr 1; ring
  have hM' : q - r ^ 2 < M * (r ^ (2 * (j₀ + 2)) * (1 - q)) := by
    rwa [div_lt_iff₀ hpos] at hM
  have : r ^ 2 * (1 + M * r ^ (2 * (j₀ + 1))) = r ^ 2 + M * (r ^ 2 * r ^ (2 * (j₀ + 1))) := by ring
  rw [this, e]
  nlinarith

end Tests

end MassGap.SliceTransferGap

end

#print axioms MassGap.SliceTransferGap.sq_apply_le
#print axioms MassGap.SliceTransferGap.int_sq_comb
#print axioms MassGap.SliceTransferGap.top_unique
#print axioms MassGap.SliceTransferGap.phi_act_of_gap
#print axioms MassGap.SliceTransferGap.zk_left_conv
#print axioms MassGap.SliceTransferGap.fk_left_conv
#print axioms MassGap.SliceTransferGap.hs_zk_rem_step
#print axioms MassGap.SliceTransferGap.hs_fk_rem_step
#print axioms MassGap.SliceTransferGap.fk_iter_eq
#print axioms MassGap.SliceTransferGap.top_of_gap
#print axioms MassGap.SliceTransferGap.phi_act_kT
#print axioms MassGap.SliceTransferGap.sq_le_of_gap
#print axioms MassGap.SliceTransferGap.sq_lt_of_gap
#print axioms MassGap.SliceTransferGap.gap_data
#print axioms MassGap.SliceTransferGap.rho_nonneg
#print axioms MassGap.SliceTransferGap.anchor_real
#print axioms MassGap.SliceTransferGap.fluxTrace_eq_rem
#print axioms MassGap.SliceTransferGap.relayZ0_eq_rem
#print axioms MassGap.SliceTransferGap.flux_step
#print axioms MassGap.SliceTransferGap.zeroRem_step
#print axioms MassGap.SliceTransferGap.hopClause_of_gapAt
#print axioms MassGap.SliceTransferGap.zeroRem_anchor
#print axioms MassGap.SliceTransferGap.relayDefect_le_of_gapAt
#print axioms MassGap.SliceTransferGap.fluxHopGap_of_transferGap
#print axioms MassGap.SliceTransferGap.longChainRead_of_transferGap
#print axioms MassGap.SliceTransferGap.measMass_lt_of_transferGap
#print axioms MassGap.SliceTransferGap.sectorSeedMeasured_of_transferGap
#print axioms MassGap.SliceTransferGap.observerGap_of_transferGap
#print axioms MassGap.SliceTransferGap.runSeed_of_transferGap
#print axioms MassGap.SliceTransferGap.rem_one_zero_coupling
#print axioms MassGap.SliceTransferGap.transferGapAt_zero_coupling
#print axioms MassGap.SliceTransferGap.relayZ0_zero_coupling
#print axioms MassGap.SliceTransferGap.anchor_zero_coupling
#print axioms MassGap.SliceTransferGap.reads_zero_coupling
#print axioms MassGap.SliceTransferGap.no_hop_from_gap
