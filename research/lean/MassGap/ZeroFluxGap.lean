import Mathlib
import MassGap.RelayChain
import MassGap.SubstrateFluxRead

/-!
# MassGap.ZeroFluxGap — the zero-flux defect read through the zero-flux transfer gap at a fixed aperture

The zero-flux clause of `SubstrateFluxRead.SectorSeedMeasured` is `trivialDefectN N β n i ≤ 1/80000`. By
`RelayChain.trivialDefectN_eq_relay` and `RelayChain.relayDefect_eq` it is the log-convexity defect
`d(j) = 2 log Z₀(j) − log Z₀(2j + 1)` of the zero-flux chain trace at aperture `Tr n i` and chain index
`j = n/2 − 1`, with `Z₀(j) = Tr₀ K^{2(j+1)}`. This module reads that defect through the zero-flux one-hop kernel
`K₀ = zk K` (`K = kT i T N β`): its top state, the operator norm of its remainder on the complement of that state,
and the trace of that remainder. Declarations are in the namespace `MassGap.ZeroFluxGap`.

## The zero-flux chain is the chain of the zero-flux kernel (proved)

* `conv_zk_right`: for a kernel `f` invariant on the right under the centre action and an invariant `K`,
  `f ∗ zk K = f ∗ K`. `iter_zk`: `iter (zk K) j = zk (iter K j)`: the zero-flux part of `K^{j+1}` is `K₀^{j+1}`.
* `relayZ0_eq_K0`, `relayDefect_eq_chain`: `Z₀(j) = hs(K₀^{∗(j+1)})` and `relayDefect j = chainDefect K₀ j`,
  `chainDefect k j = 2 log hs(k^{∗(j+1)}) − log hs(k^{∗(2j+2)})`.

## The defect is pinned by the excited zero-flux weight (proved)

`ZeroFluxGapAt N i T β λ φ ρ`: `φ` is a bounded measurable, normalized (`∫ φ² = 1`) eigenfunction of `K₀` with
eigenvalue `λ ≠ 0`, and the remainder `R = K₀ − λ φ⊗φ` (`KernelPower.rem`) has `L²` operator norm at most `ρ`.
`excitedW … k = hs(R^{∗(k+1)}) / λ^{2(k+1)} = Z₀(k)/λ^{2(k+1)} − 1` (`KernelPower.hs_iter_decomp`) is the share of
the zero-flux trace at chain index `k` not carried by `φ`: the excited zero-flux weight.

* **Upper** (`defect_le_excess`, from the eigenpair alone, no gap):  `d(j) ≤ 2 log(1 + x(j))`, `x = excitedW`.
* **Lower** (`log_excess_le_defect`, with `ρ ≤ |λ|`):            `log(1 + x(j)) ≤ d(j)`.
  The two give `relayDefect_two_sided`: the defect is the excited weight's `log(1 + x)` within a factor `2`.
  The lower bound uses `hs(R^{∗(2j+2)}) ≤ ‖R‖^{2(j+1)} hs(R^{∗(j+1)})` (`KernelPower.hs_iter_le`).
* **Gap decay** (`excess_add_le`): `x(a + l) ≤ x(a) · (ρ/|λ|)^{2l}`.
* **(a): the defect from the relative gap** (`defect_le_gap`, `defect_le_rate`, `relayDefect_le_gap`):
  if `ρ ≤ |λ| e^{−m}` (the zero-flux connected correlations decay at rate `m` per hop relative to the top), then

      d(a + l) ≤ 2 · x(a) · e^{−2 m l}        for every anchor index a and every l.

  `trivialDefectN_le_gap`: at window side `n` and anchor index `k ≤ n/2 − 1`,
  `trivialDefectN N β n i ≤ 2 · x(k) · e^{−2 m (n/2 − 1 − k)}`.
  The anchor is `A = x(k) = Z₀(k)/λ^{2(k+1)} − 1`, the zero-flux trace at chain index `k` over the top's share.
  At `k = 0` it is `Tr₀(K²)/λ₀² − 1`, the one-hop anchor of the same kind as `RelayChain.relayCost`. The bound
  is the trace and Cauchy–Schwarz argument of `RelayChain` and `KernelPower`; no spectral theorem enters.

## The anchor is not controlled by the rate (real-number lemma proved; its reading argued)

`no_defect_from_rate`: for every `0 < x < 1` there is `q ∈ ℕ` with `2 log(1 + q x) − log(1 + q x²) ≥ log(4/3)`,
and `log_four_thirds_gt`: `1/80000 < log(4/3)`. The lemma contains no kernel. Argued: its reading is the
zero-flux spectrum `{1} ∪ {r × q}` (top `1`, `q` states at `r`), `x = r^{2(j+1)}`; then `x(j) = q x` and the defect
at index `j` is the left side. The rate `m = −log r` and the chain length are fixed by `x`; the multiplicity `q`
is free, and at `q = ⌈1/x⌉` the clause fails. So no bound on the defect follows from the rate and the chain length
alone: the anchor (here `q r²` at one hop) carries the rest. The anchor at one hop counts zero-flux states at the
lattice scale and is extensive in the aperture volume (argued: `Tr₀ K²/λ₀²` is a ratio of partition functions of
time extent `2`), so an anchor at index `0` is not bounded along growing windows.

## The degenerate coupling (proved)

`zeroFluxGapAt_zero_coupling`, `excitedW_zero_coupling`: at `β = 0` the hop is `1`, `K₀ = 1`, `φ = 1` with `λ = 1`,
the remainder is `0`, `ZeroFluxGapAt` holds with `ρ = 0`, and the excited weight is `0` at every index.

## Strong coupling (proved bound; reading argued)

`trivialDefectN_strong`: at `0 ≤ β ≤ 2^{−16}`, even `n ≥ 2`, under the condition of `sectors_strong`,
`trivialDefectN N β n i ≤ 32768 β n⁴ · e^{−(log 2/2) n}`, and the measured mass of the action density
(`SubstrateDecode.measMass`, not the tensor reading `m′`) is at least `log 2`. This is the
shape of `trivialDefectN_le_gap` with rate `log 2/2` per unit side (`log 2` per two-hop step of the chain index)
and anchor `32768 β n⁴`, polynomial in the side. Argued: the polynomial anchor is the extensive count of
excitations, and it is the witness that the anchor is not bounded uniformly in `n` even where the gap is large.
The tree has no lower bound on the zero-flux relative gap at any coupling `β > 0` (at `β = 0` it holds with
`ρ = 0`, section 5), so no instance of `ZeroFluxGapAt` is proved at strong coupling; `trivialDefectN_strong`
matches only the shape of its consequence.

## What remains, as one Prop (assumed)

**`ZeroFluxReadsMass hN`**: there are `c > 0`, `C₀ ≥ 0`, `A ≥ 0`, `C₂ ≥ 0` such that, eventually in `β`, the
unit reads a positive finite mass `m′ = (measMassOf (periodicState hN β) tensorEnergy).toReal > 0`, and at every
even side `n ≥ 2` with `C₂ ≤ n m′` and every direction `i` the zero-flux one-hop kernel at aperture `Tr n i` has
an eigenpair `(λ, φ)` with remainder norm `ρ ≤ |λ| e^{−c m′}` (relative zero-flux gap per hop at least `c m′`),
and an anchor index `k ≤ n/2 − 1` with `(k + 1) m′ ≤ C₀` (at most `C₀` measured lengths) whose excited weight is
at most `A e^{c n m′/2}`. The clauses are asked only at sides with `n m′ ≥ C₂`: at a fixed lattice side the
anchor clause would fail along `β → ∞` (argued: at `n = 2` the anchor index is `0` and the clause asks
`Tr₀K²/λ₀² − 1` bounded).

`zeroFluxClause_of_reads` (proved): `ZeroFluxReadsMass hN` gives `C₁` such that, eventually in `β`, at every
even side `n ≥ 2` with `max C₁ C₂ ≤ n m′` and every `i`, `trivialDefectN N β n i ≤ 1/80000`, with
`C₁ = (2/c) log(160000 A e^{2 c C₀} + 1)`.

So the zero-flux clause reduces to "measured mass × window side large" (`n m′ ≥ max C₁ C₂`) plus two inputs: the zero-flux
relative gap at the window's aperture is at least a fixed multiple of the measured mass, and the anchor (the excited
zero-flux weight after a bounded number of measured lengths) grows at most like `e^{c n m′/2}` in the window side.
The anchor is not the one-hop read: at index `0` it is lattice-scale and extensive (above); at an index of `C₀/m′`
hops it is a quantity of the theory at the measured scale (argued: by asymptotic scaling it reads the number of
zero-flux states below `≈ m′/C₀` in a box of measured side `n m′`, polynomial in `n m′`).

The conclusion holds at every even side with `n m′ ≥ max C₁ C₂`; `SectorSeedMeasured` asks one power of two
`n ≥ 2` with `n m′ ≤ C`. Since `(k + 1) m′ ≤ C₀` forces `m′ ≤ C₀`, a power of two with
`max C₁ C₂ ≤ n m′ ≤ max(2 max C₁ C₂, 2C₀)` exists, so the zero-flux clause of `SectorSeedMeasured` follows with
that `C`; the flux clause is not touched. The join with the flux clause is `GapFromReads.sectorSeedMeasured_of_reads`, which places the seed at `2^l n₀`
with `n₀` in `[max(C_f, D), max(2 max(C_f, D), 2C₀)]` measured and `l` doublings fixed by the constants, rather
than in the window above.

Tests of `ZeroFluxReadsMass`.

1. Degenerate case: at `β = 0` the per-aperture clause holds with `ρ = 0` and anchor `0`
   (`zeroFluxGapAt_zero_coupling`, `excitedW_zero_coupling`); the Prop is read along `β → ∞`, so this is a test
   of the per-aperture clause, not an instance of the Prop.
2. Strong coupling (proved shape, argued reading): `trivialDefectN_strong` has exactly the reduced form with a
   polynomial anchor; no instance of the Prop, since the Prop is read along `β → ∞`.
3. Vacuity (a constant fixed before a growing quantity). `c` is a ratio of two rates (dimensionless); `C₀` is in
   measured lengths; `A` multiplies `e^{c n m′/2}`, which grows with the window in measured units. No constant is
   in lattice units. The anchor and gap clauses are asked only at sides with `n m′ ≥ C₂`: at a fixed lattice side
   the anchor index is capped at `n/2 − 1` and the anchor is a lattice-scale count that grows as `β → ∞`
   (argued); the anchor at index `0` is extensive, which is why the anchor index is placed at `C₀/m′` hops. The
   lock clause
   `0 < m′` excludes `m′ = 0` (where `(k + 1) m′ ≤ C₀` would hold for every `k` and the rate clause would be
   empty) and `m′ = ∞` (`toReal ⊤ = 0`).
4. Restatement against reduction. It is a reduction: it assumes a spectral statement at every even side (gap and
   anchor), and the clause follows only at sides with `n m′ ≥ C₁` (`zeroFluxClause_of_reads`). It is not implied
   by the clause, which is one number at one side. It is not a restatement of `CoarseReadsFine` (that one is about
   flux odds across apertures). It reduces the clause; it proves neither of its two halves: the gap tie
   `ρ ≤ |λ| e^{−c m′}`, which compares a finite-aperture zero-flux gap with an infinite-volume local decay rate,
   and the anchor clause, which bounds the excited zero-flux weight at a measured index.
5. Where the gap tie could fail (argued): a zero-flux state invisible to the local channel (the mechanism of
   `RelativeGap.hidden_coarse`), or small apertures, `n m′ ≪ 1`, where the finite-volume spectrum is not the
   infinite-volume one. The clauses are asked only at sides with `n m′ ≥ C₂`; at fixed lattice sides the anchor
   clause would fail along `β → ∞` (argued: at `n = 2` it asks `Tr₀K²/λ₀² − 1` bounded).

## Proved, argued, assumed

* Proved: every theorem of the module (sections 1 to 6), with standard axioms only.
* Argued: the spectral readings (`x(j) = Σ_{k≥1} (λ_k/λ₀)^{2(j+1)}`, the multiplicity reading of
  `no_defect_from_rate`, the extensivity of the one-hop anchor, the polynomial anchor at a measured index), that
  `ρ ≤ |λ|` forces `|λ|` to be the top of the zero-flux spectrum in modulus (possibly tied when `ρ = |λ|`), and the link between the relative gap `−log(ρ/|λ|)`
  and the decay rate of zero-flux slice correlations on the rectangular tori (`RelayChain.relayTorus_twoSlice`).
  No module computes a spectrum of `kT`; the existence of an eigenpair of `K₀` is not proved here
  (`JentzschKT.exists_pos_eigen_kT` gives one for `K`, not for `K₀`).
* Assumed: `ZeroFluxReadsMass hN`, only in `zeroFluxClause_of_reads`.

## Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every lattice read | shared, in the substrate; fixed in each inequality; the Prop is read along `β → ∞` |
| `i` (direction), `T` (aperture) | `K0`, `ZeroFluxGapAt`, `excitedW` | chosen; the slice geometry, fixed along the chain |
| `n` (side) | `trivialDefectN_le_gap`, `ZeroFluxReadsMass`, `zeroFluxClause_of_reads` | swept: every even `n ≥ 2`; aperture `Tr n i`, chain index `n/2 − 1` |
| `λ`, `φ` | `ZeroFluxGapAt` | existential: an eigenpair of `K₀` |
| `ρ` | `ZeroFluxGapAt` | existential: a bound on the remainder's operator norm |
| `m` | `defect_le_rate`, `relayDefect_le_gap` | chosen: a rate per hop with `ρ ≤ |λ| e^{−m}` |
| `a`, `k` (anchor index), `l`, `j` | the chain theorems | swept over all; `k ≤ n/2 − 1` at side `n` |
| `c`, `C₀`, `A` | `ZeroFluxReadsMass` | existential; `c` dimensionless, `C₀` in measured lengths, `A` a count |
| `m′` | `ZeroFluxReadsMass` | measured: `(measMassOf (periodicState hN β) tensorEnergy).toReal` |
| `C₂` | `ZeroFluxReadsMass` | existential, in measured lengths: the least measured side at which the clauses are asked |
| `C₁` | `zeroFluxClause_of_reads` | derived: `(2/c) log(160000 A e^{2 c C₀} + 1)`; the conclusion holds at `n m′ ≥ max C₁ C₂` |
| `x`, `q` | `no_defect_from_rate` | `x` chosen in `(0, 1)`; `q` existential |
| `L, E, F, d, x, p` | the real-number lemmas | local to the real-number lemmas |
| `N` | the type | shared with the substrate; not measured |

DERIVED (module-wide): `2` the square in `hs`, the doubled chain `2j + 1`, `2(j + 1)` hops and the factor of the
two-sided bound; `1` the hop shift and the top's normalization; `0` the anchor index of the one-hop read and the
degenerate coupling; `4/3` the ratio of the bounds `(1 + q x)² ≥ 4` and `1 + q x² < 3` at `q = ⌈1/x⌉`; `1/80000` the
threshold of `SectorSeedMeasured`; `160000 = 2 · 80000`; `32768 = 2 · 16 · 1024` from `strongBound`;
`65536 = 2^{16}` the strong-coupling threshold; `log 2/2` the rate of `strongBound`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.ZeroFluxGap

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.SectorDefect MassGap.FluxSectorFourier MassGap.ZeroFluxSector
  MassGap.SlabKernelOperator MassGap.RelayChain
open MassGap.SliceCentreAction (Cen act centreAction kT_act)
open MassGap.CentreSectorSeedN (trivialDefectN)
open MassGap.SubstrateDecode (measMassOf tensorEnergy)
open MassGap.PeriodicState (periodicState)

/-! ## 1. Real-number steps -/

/-- **The defect above the excited weight**: `2 log(L + E) − log(L² + F) ≤ 2 log(1 + E/L)`.
DERIVED: `2` the square. -/
theorem defect_split_le {L E F : ℝ} (hL : 0 < L) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    2 * Real.log (L + E) - Real.log (L ^ 2 + F) ≤ 2 * Real.log (1 + E / L) := by
  have h1 : Real.log (L ^ 2) ≤ Real.log (L ^ 2 + F) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_pow] at h1
  have e : 1 + E / L = (L + E) / L := by field_simp
  rw [e, Real.log_div (by linarith) hL.ne']
  push_cast at h1
  linarith

/-- **The defect below the excited weight**: if `F ≤ L E`, `log(1 + E/L) ≤ 2 log(L + E) − log(L² + F)`.
DERIVED: `2` the square. -/
theorem defect_split_ge {L E F : ℝ} (hL : 0 < L) (hE : 0 ≤ E) (hF : 0 ≤ F) (hFE : F ≤ L * E) :
    Real.log (1 + E / L) ≤ 2 * Real.log (L + E) - Real.log (L ^ 2 + F) := by
  have hLE : 0 < L + E := by linarith
  have h1 : Real.log (L ^ 2 + F) ≤ Real.log (L * (L + E)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_mul hL.ne' hLE.ne'] at h1
  have e : 1 + E / L = (L + E) / L := by field_simp
  rw [e, Real.log_div hLE.ne' hL.ne']
  linarith

/-- `log(1 + x) ≤ x` for `x ≥ 0`. DERIVED: `1`. -/
theorem log_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
  linarith

/-- **No defect bound from the rate alone**: for every `0 < x < 1` there is a multiplicity `q` with
`2 log(1 + q x) − log(1 + q x²) ≥ log(4/3)`. Argued reading: zero-flux spectrum `{1} ∪ {r × q}`, `x = r^{2(j+1)}`; the
left side is the defect at chain index `j`, `q x` the excited weight. DERIVED: `4/3` from `(1 + q x)² ≥ 4` and
`1 + q x² < 3` at `q = ⌈1/x⌉`. -/
theorem no_defect_from_rate (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ q : ℕ, Real.log (4 / 3) ≤ 2 * Real.log (1 + q * x) - Real.log (1 + q * x ^ 2) := by
  refine ⟨⌈1 / x⌉₊, ?_⟩
  set q : ℝ := (⌈1 / x⌉₊ : ℝ) with hq
  have hq1 : 1 / x ≤ q := Nat.le_ceil _
  have hq2 : q < 1 / x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hqx1 : 1 ≤ q * x := by
    have := mul_le_mul_of_nonneg_right hq1 hx0.le
    rwa [one_div, inv_mul_cancel₀ hx0.ne'] at this
  have hqx2 : q * x ^ 2 < 2 := by
    have h := mul_lt_mul_of_pos_right hq2 (by positivity : (0 : ℝ) < x ^ 2)
    have e : (1 / x + 1) * x ^ 2 = x + x ^ 2 := by field_simp
    rw [e] at h
    nlinarith
  have hq0 : 0 ≤ q * x ^ 2 := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    positivity
  have h4 : Real.log 4 ≤ 2 * Real.log (1 + q * x) := by
    rw [← Real.log_rpow (by linarith), show ((1 + q * x) ^ (2 : ℝ)) = (1 + q * x) ^ 2 by norm_cast]
    exact Real.log_le_log (by norm_num) (by nlinarith)
  have h3 : Real.log (1 + q * x ^ 2) ≤ Real.log 3 := Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_div (by norm_num) (by norm_num)]
  linarith

/-- `1/80000 < log(4/3)`. DERIVED: `1 − 3/4 = 1/4 ≤ log(4/3)`; Inherited: `1/80000` the threshold of
`SectorSeedMeasured` (CHOSEN in `CentreSectorSeed` so that `15 · 5/80000 ≤ 1/1000`). -/
theorem log_four_thirds_gt : (1 : ℝ) / 80000 < Real.log (4 / 3) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  norm_num at h ⊢
  linarith

/-- **The window arithmetic**: a defect bounded by twice an anchor times the gap decay, with the anchor at most
`A e^{c (2p) m/2}` and the anchor index within `C₀` measured lengths, is at most `1/80000` once
`(2/c) log(160000 A e^{2 c C₀} + 1) ≤ 2 p m`. DERIVED: `160000 = 2 · 80000`; `2` the two hops per index. -/
theorem small_of_window {c m C₀ A x d p k : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hd : d ≤ 2 * x * Real.exp (-(2 * (c * m) * (p - 1 - k))))
    (hx : x ≤ A * Real.exp (c * ((p + p) * m) / 2))
    (hk : (k + 1) * m ≤ C₀)
    (hC1 : 2 / c * Real.log (160000 * (A * Real.exp (2 * c * C₀)) + 1) ≤ (p + p) * m) :
    d ≤ 1 / 80000 := by
  set Q := A * Real.exp (2 * c * C₀) with hQdef
  have hQ : 0 ≤ Q := mul_nonneg hA (Real.exp_pos _).le
  have hpos : 0 < 160000 * Q + 1 := by linarith
  have hkc : 2 * c * ((k + 1) * m) ≤ 2 * c * C₀ := mul_le_mul_of_nonneg_left hk (by linarith)
  have h1 : 2 * x * Real.exp (-(2 * (c * m) * (p - 1 - k))) ≤ 2 * Q * Real.exp (-(c * p * m)) := by
    calc 2 * x * Real.exp (-(2 * (c * m) * (p - 1 - k)))
        ≤ 2 * (A * Real.exp (c * ((p + p) * m) / 2)) * Real.exp (-(2 * (c * m) * (p - 1 - k))) := by
          gcongr
      _ = 2 * A * Real.exp (-(c * p * m) + 2 * c * ((k + 1) * m)) := by
          have e : -(c * p * m) + 2 * c * ((k + 1) * m)
              = c * ((p + p) * m) / 2 + -(2 * (c * m) * (p - 1 - k)) := by ring
          rw [e, Real.exp_add]; ring
      _ ≤ 2 * A * Real.exp (-(c * p * m) + 2 * c * C₀) := by
          gcongr
      _ = 2 * Q * Real.exp (-(c * p * m)) := by
          rw [hQdef, Real.exp_add]; ring
  have hL : Real.log (160000 * Q + 1) ≤ c * p * m := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hC1
    nlinarith
  have hE : Real.exp (-(c * p * m)) ≤ (160000 * Q + 1)⁻¹ := by
    have := Real.exp_le_exp.mpr (neg_le_neg hL)
    rwa [Real.exp_neg (Real.log _), Real.exp_log hpos] at this
  have h2 : 2 * Q * Real.exp (-(c * p * m)) ≤ 2 * Q * (160000 * Q + 1)⁻¹ :=
    mul_le_mul_of_nonneg_left hE (by linarith)
  have h3 : 2 * Q * (160000 * Q + 1)⁻¹ ≤ 1 / 80000 := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]
    linarith
  linarith

/-! ## 2. The zero-flux chain is the chain of the zero-flux kernel -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {ac : G → X → X}

/-- **A right-invariant kernel does not see the zero-flux projection of the hop**: `f ∗ zk K = f ∗ K` when
`f x (g·y) = f x y` and `K` is invariant. DERIVED: `|G|⁻¹ · |G| = 1`. -/
theorem conv_zk_right {f K : X → X → ℝ} (hf : Bdd f) (hK : Bdd K) (hA : CentreAction μ ac)
    (hinv : ∀ g x y, K (ac g x) (ac g y) = K x y) (hfr : ∀ g x y, f x (ac g y) = f x y) :
    conv μ f (zk K ac) = conv μ f K := by
  obtain ⟨Cf, hCf0, hCf⟩ := bdd_nonneg_bound hf
  obtain ⟨CK, hCK0, hCK⟩ := bdd_nonneg_bound hK
  funext x z
  have hterm : ∀ g, ∫ y, f x y * K y (ac g z) ∂μ = ∫ y, f x y * K y z ∂μ := by
    intro g
    have h := hA.integral_comp g (fun y => f x y * K y (ac g z))
    rw [← h]
    congr 1; funext y
    simp only [hfr, hinv]
  have hint : ∀ g, Integrable (fun y => f x y * K y (ac g z)) μ := fun g =>
    int_mul2 (hf.row x) (hK.col (ac g z)) (fun y => hCf x y) (fun y => hCK y _)
  show ∫ y, f x y * zk K ac y z ∂μ = ∫ y, f x y * K y z ∂μ
  have e : (fun y => f x y * zk K ac y z)
      = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, f x y * K y (ac g z) := by
    funext y
    show f x y * ((Fintype.card G : ℝ)⁻¹ * ∑ g, K y (ac g z)) = _
    rw [mul_left_comm, Finset.mul_sum]
  rw [e, integral_const_mul, integral_finsetSum _ fun g _ => hint g]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (card_pos_real (G := G)).ne', one_mul]

/-- **The zero-flux part of `K^{j+1}` is `(zk K)^{j+1}`.** DERIVED: `0`, `1` the hop. -/
theorem iter_zk {K : X → X → ℝ} (hK : Bdd K) (hA : CentreAction μ ac)
    (hinv : ∀ g x y, K (ac g x) (ac g y) = K x y) : ∀ j, iter μ (zk K ac) j = zk (iter μ K j) ac
  | 0 => rfl
  | j + 1 => by
    rw [iter_succ_right (bdd_zk hK hA) j, iter_zk hK hA hinv j,
      conv_zk_right (bdd_zk (hK.iter j) hA) hK hA hinv (fun g x y => zk_act_right hA g x y),
      ← zk_conv_right (hK.iter j) hK hA hinv, ← iter_succ_right hK j]

/-! ## 3. The defect against the excited weight -/

variable (μ) in
/-- **The chain defect** of a kernel at chain index `j`: `2 log hs(k^{∗(j+1)}) − log hs(k^{∗(2j+2)})`.
DERIVED: `2`, `1` the doubled chain. -/
def chainDefect (k : X → X → ℝ) (j : ℕ) : ℝ :=
  2 * Real.log (hs μ (iter μ k j)) - Real.log (hs μ (iter μ k (2 * j + 1)))

variable (μ) in
/-- **The excited weight** at chain index `j`: `hs(R^{∗(j+1)})/c^{2(j+1)}`, `R = k − c φ⊗φ`.
DERIVED: `2`, `1`. -/
def excess (k : X → X → ℝ) (c : ℝ) (φ : X → ℝ) (j : ℕ) : ℝ :=
  hs μ (iter μ (rem k c φ) j) / c ^ (2 * (j + 1))

/-- DERIVED: `2` the even power. -/
theorem pow_two_mul_pos {c : ℝ} (hc : c ≠ 0) (n : ℕ) : 0 < c ^ (2 * n) := by
  rw [pow_mul]
  exact pow_pos (lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc))) _

/-- DERIVED: `2` the even power. -/
theorem abs_pow_two_mul (c : ℝ) (n : ℕ) : |c| ^ (2 * n) = c ^ (2 * n) := by
  rw [pow_mul, pow_mul, sq_abs]

theorem excess_nonneg {k : X → X → ℝ} {c : ℝ} {φ : X → ℝ} (hc : c ≠ 0) (j : ℕ) :
    0 ≤ excess μ k c φ j :=
  div_nonneg (hs_nonneg _) (pow_two_mul_pos hc _).le

/-- **The defect is at most twice `log(1 + x)`**, from the eigenpair alone. DERIVED: `2`. -/
theorem defect_le_excess {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
    {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)
    {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (hc : c ≠ 0) (j : ℕ) :
    chainDefect μ k j ≤ 2 * Real.log (1 + excess μ k c φ j) := by
  unfold chainDefect excess
  rw [hs_iter_decomp (μ := μ) hk hsym hφm hφb hφ1 heig j,
    hs_iter_decomp (μ := μ) hk hsym hφm hφb hφ1 heig (2 * j + 1)]
  have e : c ^ (2 * (2 * j + 1 + 1)) = (c ^ (2 * (j + 1))) ^ 2 := by
    rw [← pow_mul]; congr 1; ring
  rw [e]
  exact defect_split_le (pow_two_mul_pos hc _) (hs_nonneg _) (hs_nonneg _)

/-- **The doubled excess**: `hs(R^{∗(2j+2)}) ≤ ‖R‖^{2(j+1)} hs(R^{∗(j+1)})`. DERIVED: `2`, `1`. -/
theorem excess_double_le {k : X → X → ℝ} {c : ℝ} {φ : X → ℝ} {C : ℝ}
    (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C) (hb : ∀ x y, |rem k c φ x y| ≤ C)
    (j : ℕ) :
    hs μ (iter μ (rem k c φ) (2 * j + 1))
      ≤ ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ^ (2 * (j + 1)) * hs μ (iter μ (rem k c φ) j) := by
  have h := hs_iter_le (μ := μ) hm hC0 hb j (j + 1)
  rwa [show j + (j + 1) = 2 * j + 1 by ring] at h

/-- **The defect is at least `log(1 + x)`** when the remainder's norm is at most `|c|`. DERIVED: `1`, `2`. -/
theorem log_excess_le_defect {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
    {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)
    {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (hc : c ≠ 0) {C : ℝ}
    (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C) (hb : ∀ x y, |rem k c φ x y| ≤ C)
    (hR : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ |c|) (j : ℕ) :
    Real.log (1 + excess μ k c φ j) ≤ chainDefect μ k j := by
  unfold chainDefect excess
  rw [hs_iter_decomp (μ := μ) hk hsym hφm hφb hφ1 heig j,
    hs_iter_decomp (μ := μ) hk hsym hφm hφb hφ1 heig (2 * j + 1)]
  have e : c ^ (2 * (2 * j + 1 + 1)) = (c ^ (2 * (j + 1))) ^ 2 := by
    rw [← pow_mul]; congr 1; ring
  rw [e]
  refine defect_split_ge (pow_two_mul_pos hc _) (hs_nonneg _) (hs_nonneg _) ?_
  calc hs μ (iter μ (rem k c φ) (2 * j + 1))
      ≤ ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ^ (2 * (j + 1)) * hs μ (iter μ (rem k c φ) j) :=
        excess_double_le hm hC0 hb j
    _ ≤ |c| ^ (2 * (j + 1)) * hs μ (iter μ (rem k c φ) j) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR _) (hs_nonneg _)
    _ = c ^ (2 * (j + 1)) * hs μ (iter μ (rem k c φ) j) := by rw [abs_pow_two_mul]

/-- **The excited weight decays with the relative gap**: `x(a + l) ≤ x(a) (ρ/|c|)^{2l}`. DERIVED: `2`. -/
theorem excess_add_le {k : X → X → ℝ} {c : ℝ} {φ : X → ℝ} (hc : c ≠ 0) {C : ℝ}
    (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C) (hb : ∀ x y, |rem k c φ x y| ≤ C)
    {ρ : ℝ} (hR : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ) (a l : ℕ) :
    excess μ k c φ (a + l) ≤ excess μ k c φ a * (ρ / |c|) ^ (2 * l) := by
  unfold excess
  have h := hs_iter_le (μ := μ) hm hC0 hb a l
  have h2 : hs μ (iter μ (rem k c φ) (a + l)) ≤ ρ ^ (2 * l) * hs μ (iter μ (rem k c φ) a) :=
    h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR _) (hs_nonneg _))
  rw [div_pow, abs_pow_two_mul c l]
  have e : c ^ (2 * (a + l + 1)) = c ^ (2 * (a + 1)) * c ^ (2 * l) := by
    rw [← pow_add]; congr 1; ring
  rw [e, div_mul_div_comm]
  apply div_le_div_of_nonneg_right _ (mul_pos (pow_two_mul_pos hc _) (pow_two_mul_pos hc _)).le
  linarith

/-- **(a) The defect from the relative gap**: `d(a + l) ≤ 2 x(a) (ρ/|c|)^{2l}`. DERIVED: `2`. -/
theorem defect_le_gap {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
    {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)
    {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (hc : c ≠ 0) {C : ℝ}
    (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C) (hb : ∀ x y, |rem k c φ x y| ≤ C)
    {ρ : ℝ} (hR : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ) (a l : ℕ) :
    chainDefect μ k (a + l) ≤ 2 * excess μ k c φ a * (ρ / |c|) ^ (2 * l) := by
  have h1 := defect_le_excess hk hsym hφm hφb hφ1 heig hc (a + l)
  have h2 := excess_add_le hc hm hC0 hb hR a l
  have h3 := log_one_add_le (excess_nonneg (μ := μ) (k := k) (φ := φ) hc (a + l))
  nlinarith

/-- **(a) in rate form**: if `ρ ≤ |c| e^{−m}`, `d(a + l) ≤ 2 x(a) e^{−2 m l}`. DERIVED: `2`. -/
theorem defect_le_rate {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x)
    {φ : X → ℝ} (hφm : Measurable φ) {B : ℝ} (hφb : ∀ x, |φ x| ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂μ = 1)
    {c : ℝ} (heig : ∀ z, ∫ y, k z y * φ y ∂μ = c * φ z) (hc : c ≠ 0) {C : ℝ}
    (hm : Measurable (Function.uncurry (rem k c φ))) (hC0 : 0 ≤ C) (hb : ∀ x y, |rem k c φ x y| ≤ C)
    {ρ : ℝ} (hR : ‖kernelCLM (rem k c φ) C hm hC0 hb μ μ‖ ≤ ρ) {m : ℝ} (hρm : ρ ≤ |c| * Real.exp (-m))
    (a l : ℕ) :
    chainDefect μ k (a + l) ≤ 2 * excess μ k c φ a * Real.exp (-(2 * m * l)) := by
  have hc' : 0 < |c| := abs_pos.mpr hc
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hR
  have hq : ρ / |c| ≤ Real.exp (-m) := by
    rw [div_le_iff₀ hc']; linarith
  have hq2 : (ρ / |c|) ^ (2 * l) ≤ Real.exp (-(2 * m * l)) := by
    calc (ρ / |c|) ^ (2 * l) ≤ Real.exp (-m) ^ (2 * l) :=
          pow_le_pow_left₀ (div_nonneg hρ0 hc'.le) hq _
      _ = Real.exp (-(2 * m * l)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc chainDefect μ k (a + l) ≤ 2 * excess μ k c φ a * (ρ / |c|) ^ (2 * l) :=
        defect_le_gap hk hsym hφm hφb hφ1 heig hc hm hC0 hb hR a l
    _ ≤ 2 * excess μ k c φ a * Real.exp (-(2 * m * l)) :=
        mul_le_mul_of_nonneg_left hq2 (by have := excess_nonneg (μ := μ) (k := k) (φ := φ) hc a; linarith)

end Generic

/-! ## 4. On the slice -/

section Lattice

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The zero-flux one-hop kernel** `K₀ = zk K` on the slice of direction `i` with aperture `T`.
DERIVED: no numeral. -/
def K0 (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) :
    MassGap.SliceCentreAction.Cfg i T N → MassGap.SliceCentreAction.Cfg i T N → ℝ :=
  zk (kT i T N β) (act (μ := i) (T := T) (N := N))

variable (N) in
/-- **The zero-flux gap at one aperture**: `φ` is a bounded measurable normalized eigenfunction of `K₀` with
eigenvalue `c ≠ 0`, and the remainder `K₀ − c φ⊗φ` has `L²` operator norm at most `ρ`. DERIVED: `1` the
normalization; `0`. -/
def ZeroFluxGapAt (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β c : ℝ)
    (φ : MassGap.SliceCentreAction.Cfg i T N → ℝ) (ρ : ℝ) : Prop :=
  Measurable φ ∧ (∃ B : ℝ, ∀ x, |φ x| ≤ B) ∧ ∫ x, φ x ^ 2 ∂(hS i T N) = 1 ∧ c ≠ 0 ∧
    (∀ z, ∫ y, K0 N i T β z y * φ y ∂(hS i T N) = c * φ z) ∧
    ∃ C : ℝ, ∃ hm : Measurable (Function.uncurry (rem (K0 N i T β) c φ)), ∃ hC0 : 0 ≤ C,
      ∃ hb : ∀ x y, |rem (K0 N i T β) c φ x y| ≤ C,
        ‖kernelCLM (rem (K0 N i T β) c φ) C hm hC0 hb (hS i T N) (hS i T N)‖ ≤ ρ

variable (N) in
/-- **The excited zero-flux weight** at chain index `k`. DERIVED: no numeral. -/
def excitedW (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β c : ℝ)
    (φ : MassGap.SliceCentreAction.Cfg i T N → ℝ) (k : ℕ) : ℝ :=
  excess (hS i T N) (K0 N i T β) c φ k

variable {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ}

theorem bdd_K0 (hβ : 0 ≤ β) : Bdd (K0 N i T β) :=
  bdd_zk (bdd_kT (NeZero.ne N) hβ) centreAction

theorem K0_symm (β : ℝ) : ∀ x y, K0 N i T β x y = K0 N i T β y x :=
  zk_symm centreAction (kT_symm β) (fun g x y => kT_act g β x y)

/-- **The zero-flux chain trace is the trace of the zero-flux chain.** DERIVED: no numeral. -/
theorem relayZ0_eq_K0 (hβ : 0 ≤ β) (j : ℕ) :
    relayZ0 N i T β j = hs (hS i T N) (iter (hS i T N) (K0 N i T β) j) := by
  unfold relayZ0 K0
  rw [iter_zk (bdd_kT (NeZero.ne N) hβ) centreAction (fun g x y => kT_act g β x y) j]

/-- **The relay defect is the chain defect of `K₀`.** DERIVED: no numeral. -/
theorem relayDefect_eq_chain (hβ : 0 ≤ β) (j : ℕ) :
    relayDefect N i T β j = chainDefect (hS i T N) (K0 N i T β) j := by
  rw [relayDefect_eq hβ j, relayZ0_eq_K0 hβ, relayZ0_eq_K0 hβ]
  rfl

/-- **(b) The defect is pinned by the excited weight**: `log(1 + x(j)) ≤ d(j) ≤ 2 log(1 + x(j))`.
DERIVED: `1`, `2`. -/
theorem relayDefect_two_sided (hβ : 0 ≤ β) {c ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : ZeroFluxGapAt N i T β c φ ρ) (hρ : ρ ≤ |c|) (j : ℕ) :
    Real.log (1 + excitedW N i T β c φ j) ≤ relayDefect N i T β j ∧
      relayDefect N i T β j ≤ 2 * Real.log (1 + excitedW N i T β c φ j) := by
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hc, heig, C, hm, hC0, hb, hR⟩ := h
  rw [relayDefect_eq_chain hβ]
  exact ⟨log_excess_le_defect (bdd_K0 hβ) (K0_symm β) hφm hφb hφ1 heig hc hm hC0 hb (hR.trans hρ) j,
    defect_le_excess (bdd_K0 hβ) (K0_symm β) hφm hφb hφ1 heig hc j⟩

/-- **(a) on the slice**: if `ρ ≤ |c| e^{−m}`, `d(a + l) ≤ 2 x(a) e^{−2 m l}`. DERIVED: `2`. -/
theorem relayDefect_le_gap (hβ : 0 ≤ β) {c ρ : ℝ} {φ : MassGap.SliceCentreAction.Cfg i T N → ℝ}
    (h : ZeroFluxGapAt N i T β c φ ρ) {m : ℝ} (hρm : ρ ≤ |c| * Real.exp (-m)) (a l : ℕ) :
    relayDefect N i T β (a + l) ≤ 2 * excitedW N i T β c φ a * Real.exp (-(2 * m * l)) := by
  obtain ⟨hφm, ⟨B, hφb⟩, hφ1, hc, heig, C, hm, hC0, hb, hR⟩ := h
  rw [relayDefect_eq_chain hβ]
  exact defect_le_rate (bdd_K0 hβ) (K0_symm β) hφm hφb hφ1 heig hc hm hC0 hb hR hρm a l

/-- **The zero-flux clause from the gap at a window side**: with the anchor at chain index `k ≤ n/2 − 1`,
`trivialDefectN N β n i ≤ 2 x(k) e^{−2 m (n/2 − 1 − k)}`. DERIVED: `2`, `1` the half side. -/
theorem trivialDefectN_le_gap (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) {c ρ : ℝ}
    {φ : MassGap.SliceCentreAction.Cfg i (CentreSectorSeed.Tr n i) N → ℝ}
    (h : ZeroFluxGapAt N i (CentreSectorSeed.Tr n i) β c φ ρ) {m : ℝ} (hρm : ρ ≤ |c| * Real.exp (-m))
    {k : ℕ} (hk : k ≤ n / 2 - 1) :
    trivialDefectN N β n i
      ≤ 2 * excitedW N i (CentreSectorSeed.Tr n i) β c φ k
        * Real.exp (-(2 * m * ((n / 2 - 1 - k : ℕ) : ℝ))) := by
  rw [trivialDefectN_eq_relay]
  have h1 := relayDefect_le_gap hβ h hρm k (n / 2 - 1 - k)
  rwa [Nat.add_sub_cancel' hk] at h1

/-! ## 5. The degenerate coupling -/

theorem K0_zero_coupling : K0 N i T 0 = fun _ _ => 1 := by
  unfold K0
  rw [kT_zero]
  funext x y
  simp only [zk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (card_pos_real (G := Cen i N)).ne'

theorem rem_zero_coupling :
    rem (K0 N i T 0) 1 (fun _ : MassGap.SliceCentreAction.Cfg i T N => (1 : ℝ)) = fun _ _ => 0 := by
  rw [K0_zero_coupling]
  funext x y
  simp [rem]

omit [NeZero N] in
theorem iter_zero_kernel {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    ∀ j, iter μ (fun _ _ : X => (0 : ℝ)) j = fun _ _ => 0
  | 0 => rfl
  | j + 1 => by
    show conv μ (fun _ _ => (0 : ℝ)) (iter μ (fun _ _ => (0 : ℝ)) j) = _
    rw [iter_zero_kernel μ j]
    funext x z
    simp [conv]

/-- **At `β = 0` the zero-flux gap holds with `ρ = 0`**: `K₀ = 1`, `φ = 1`, `λ = 1`, remainder `0`.
DERIVED: `0`, `1`. -/
theorem zeroFluxGapAt_zero_coupling :
    ZeroFluxGapAt N i T 0 1 (fun _ => 1) 0 := by
  have hr := rem_zero_coupling (N := N) (i := i) (T := T)
  have hm : Measurable (Function.uncurry
      (rem (K0 N i T 0) 1 (fun _ : MassGap.SliceCentreAction.Cfg i T N => (1 : ℝ)))) := by
    rw [hr]; exact measurable_const
  have hb : ∀ x y, |rem (K0 N i T 0) 1 (fun _ : MassGap.SliceCentreAction.Cfg i T N => (1 : ℝ)) x y| ≤ 0 := by
    intro x y; rw [hr]; simp
  refine ⟨measurable_const, ⟨1, fun _ => by simp⟩, by simp, one_ne_zero, fun z => ?_,
    0, hm, le_rfl, hb, norm_kernelCLM_le _ _ _ _ _ _ _⟩
  rw [K0_zero_coupling]
  simp

/-- **At `β = 0` the excited weight is `0` at every index.** DERIVED: `0`. -/
theorem excitedW_zero_coupling (k : ℕ) :
    excitedW N i T 0 1 (fun _ => 1) k = 0 := by
  unfold excitedW excess
  rw [rem_zero_coupling, iter_zero_kernel]
  simp [hs]

/-! ## 6. Strong coupling, and the remaining input -/

/-- **The zero-flux defect at strong coupling has the reduced shape**: rate `log 2/2` per unit side, anchor
`32768 β n⁴`; the measured mass of the action density (`SubstrateDecode.measMass`, not the tensor reading `m′`)
is at least `log 2`. It is not an instance of `ZeroFluxGapAt`; no eigenpair or gap enters.
DERIVED: `32768 = 2 · 16 · 1024`; `65536 = 2^{16}`; `4 + N⁶`, `2` from `sectors_strong`, whose exponent
`6` this is. -/
theorem trivialDefectN_strong {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) (hδ : (4 + (N : ℝ) ^ 6) * (β * MassGap.StrongFiniteSize.strongBound n) ≤ 2)
    (i : Fin 4) :
    ENNReal.ofReal (Real.log 2) ≤ SubstrateDecode.measMass (periodicState (NeZero.ne N) β) ∧
      trivialDefectN N β n i ≤ (32768 * β * (n : ℝ) ^ 4) * Real.exp (-(Real.log 2 / 2) * n) := by
  refine ⟨SubstrateDecode.measMass_strong (NeZero.ne N) (abs_le.mpr ⟨by linarith, hβ⟩), ?_⟩
  calc trivialDefectN N β n i ≤ 2 * (β * MassGap.StrongFiniteSize.strongBound n) :=
        (SubstrateFluxRead.sectors_strong hβ0 hβ hn he hδ i).2
    _ = (32768 * β * (n : ℝ) ^ 4) * Real.exp (-(Real.log 2 / 2) * n) := by
        unfold MassGap.StrongFiniteSize.strongBound; ring

variable (N) in
/-- **The zero-flux gap reads the measured mass** (assumed): eventually in `β` the unit reads a positive finite
mass `m′`, and at every even side `n ≥ 2` with `C₂ ≤ n m′` and every direction `i` the zero-flux kernel at aperture `Tr n i` has an
eigenpair whose remainder norm is at most `|λ| e^{−c m′}`, with an anchor index `k` within `C₀` measured lengths
whose excited weight is at most `A e^{c n m′/2}`. `C₂` is in measured lengths: at a fixed lattice side the
anchor clause would fail along `β → ∞` (argued). DERIVED: `2` the least side and the half rate; `1` the hop. -/
def ZeroFluxReadsMass (hN : N ≠ 0) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ᶠ β in atTop,
    0 < (measMassOf (periodicState hN β) tensorEnergy).toReal ∧
    ∀ n : ℕ, 2 ≤ n → Even n →
      C₂ ≤ (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal → ∀ i : Fin 4,
      ∃ lam : ℝ, ∃ φ : MassGap.SliceCentreAction.Cfg i (CentreSectorSeed.Tr n i) N → ℝ, ∃ ρ : ℝ, ∃ k : ℕ,
        ZeroFluxGapAt N i (CentreSectorSeed.Tr n i) β lam φ ρ ∧
        ρ ≤ |lam| * Real.exp (-(c * (measMassOf (periodicState hN β) tensorEnergy).toReal)) ∧
        k ≤ n / 2 - 1 ∧
        ((k : ℝ) + 1) * (measMassOf (periodicState hN β) tensorEnergy).toReal ≤ C₀ ∧
        excitedW N i (CentreSectorSeed.Tr n i) β lam φ k
          ≤ A * Real.exp (c * ((n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal) / 2)

/-- **The zero-flux clause at every large measured window**: from `ZeroFluxReadsMass`, with
`C₁ = (2/c) log(160000 A e^{2 c C₀} + 1)`, eventually in `β`, at every even side `n ≥ 2` with
`max C₁ C₂ ≤ n m′`, `trivialDefectN N β n i ≤ 1/80000`.
DERIVED: `1/80000` the threshold of `SectorSeedMeasured`; `160000 = 2 · 80000`; `2`. -/
theorem zeroFluxClause_of_reads (hN : N ≠ 0) (h : ZeroFluxReadsMass N hN) :
    ∃ C₁ : ℝ, ∀ᶠ β in atTop, 0 < (measMassOf (periodicState hN β) tensorEnergy).toReal ∧
      ∀ n : ℕ, 2 ≤ n → Even n →
        C₁ ≤ (n : ℝ) * (measMassOf (periodicState hN β) tensorEnergy).toReal →
        ∀ i : Fin 4, trivialDefectN N β n i ≤ 1 / 80000 := by
  obtain ⟨c, hc, C₀, hC₀, A, hA, C₂, hC₂, hev⟩ := h
  refine ⟨max (2 / c * Real.log (160000 * (A * Real.exp (2 * c * C₀)) + 1)) C₂, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβev hβ
  obtain ⟨hm, hall⟩ := hβev
  refine ⟨hm, fun n hn he hCm i => ?_⟩
  have hC1 := (le_max_left _ _).trans hCm
  obtain ⟨lam, φ, ρ, k, hG, hρ, hk, hkm, hx⟩ := hall n hn he ((le_max_right _ _).trans hCm) i
  set m := (measMassOf (periodicState hN β) tensorEnergy).toReal with hmdef
  have hd := trivialDefectN_le_gap hβ n i hG hρ hk
  obtain ⟨p, rfl⟩ := he
  have hp2 : (p + p) / 2 = p := by omega
  have hp1 : 1 ≤ p := by omega
  rw [hp2] at hk hd
  have hcast : (((p - 1 - k : ℕ)) : ℝ) = (p : ℝ) - 1 - k := by
    rw [Nat.cast_sub hk, Nat.cast_sub hp1]
    simp
  rw [hcast] at hd
  push_cast at hx hC1
  exact small_of_window hc hA hd hx hkm hC1

end Lattice

end MassGap.ZeroFluxGap

end

#print axioms MassGap.ZeroFluxGap.no_defect_from_rate
#print axioms MassGap.ZeroFluxGap.log_four_thirds_gt
#print axioms MassGap.ZeroFluxGap.iter_zk
#print axioms MassGap.ZeroFluxGap.defect_le_excess
#print axioms MassGap.ZeroFluxGap.log_excess_le_defect
#print axioms MassGap.ZeroFluxGap.defect_le_rate
#print axioms MassGap.ZeroFluxGap.relayDefect_eq_chain
#print axioms MassGap.ZeroFluxGap.relayDefect_two_sided
#print axioms MassGap.ZeroFluxGap.relayDefect_le_gap
#print axioms MassGap.ZeroFluxGap.trivialDefectN_le_gap
#print axioms MassGap.ZeroFluxGap.zeroFluxGapAt_zero_coupling
#print axioms MassGap.ZeroFluxGap.excitedW_zero_coupling
#print axioms MassGap.ZeroFluxGap.trivialDefectN_strong
#print axioms MassGap.ZeroFluxGap.zeroFluxClause_of_reads
