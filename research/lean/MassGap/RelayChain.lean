import Mathlib
import MassGap.SectorDoubling

/-!
# MassGap.RelayChain — the fixed-aperture relay chain, upward and downward

An observer is part of the substrate: it reads one hop through a fixed aperture and re-emits, and the next
observer reads that. On the lattice the aperture is one slice, the slice of direction `i` with transverse extents
`T`, and one hop is the symmetric positive transfer kernel `K = kT i T N β` on it. A chain of `j + 1` relays is the
kernel `K^{∗(j+1)} = iter K j`, and the reads of the chain are those of a torus of time extent `2(j + 1)` with the
same aperture. Declarations are in the namespace `MassGap.RelayChain`.

## The reads at chain index `j`

* `relayZ N i T β j = hs(iter K j)`, the trace `Tr K^{2(j+1)}`;
* `relayZ0 N i T β j = hs(zk(iter K j))`, the zero-flux trace (`ZeroFluxSector.zk`, averaged over the centre
  `Z_N³`); `relayTwist N i T β j g = twist(iter K j, act g)`, the twisted traces `Z_g`;
* `relayShare = (Z − Z₀)/Z`, the flux share, and `relayShare_eq_mean`: `relayShare = 1 − N⁻³ Σ_g Z_g/Z`;
* `relayOdds = (Z − Z₀)/Z₀`, the flux odds; `relayDefect = dd(zk(iter K j))`, the zero-flux defect, and
  `relayDefect_eq`: `relayDefect j = 2 log Z₀(j) − log Z₀(2j + 1)`.

`fluxShareN_eq_relay`, `trivialDefectN_eq_relay` (both `rfl`): the cubic reads of `SubstrateFluxRead.SectorSeedMeasured`
at side `n` are the relay reads at aperture `Tr n i` and chain index `n/2 − 1`.

## Proved

* **Log-convexity along the chain** (`hs_family_sq_le`). For a symmetric bounded `K` and a family `h` of bounded
  kernels with `h (a + 1) = h a ∗ K`, the pairing `∫∫ h a · h b` depends on `a + b` only (`kpair_family`), and
  Cauchy–Schwarz on `μ ⊗ μ` (`kpair_sq_le`) gives `hs(h (a + s))² ≤ hs(h a) · hs(h (a + 2s))`. Three families
  satisfy the step: `iter K`, `zk ∘ iter K` (`zk_conv_right`: `zk(f ∗ K) = zk f ∗ K` for invariant `K`), and the
  flux block `fk ∘ iter K`, `fk h = h − zk h` (`fk_conv_right`), whose trace is `hs h − hs(zk h)` (`hs_fk`). On the
  lattice, for every `a`, `s`:

      Z(a+s)²            ≤ Z(a) · Z(a+2s)                                   (relayZ_sq_le)
      Z₀(a+s)²           ≤ Z₀(a) · Z₀(a+2s)                                 (relayZ0_sq_le)
      (Z − Z₀)(a+s)²     ≤ (Z − Z₀)(a) · (Z − Z₀)(a+2s)                     (relayFlux_sq_le)

  Direction: each bounds a middle read from above by the two ends. None bounds a shorter read by a longer one
  alone; the shorter end `a` is always present.
* **The odds at the midpoint** (`relayOdds_mid`):
  `o(a+s)² ≤ o(a) · o(a+2s) · κ(a,s)`, `κ(a,s) = Z₀(a) Z₀(a+2s) / Z₀(a+s)²`, and `1 ≤ κ` (`relayCost_ge_one`).
  `κ` is the zero-flux log-convexity defect, the analogue of `exp(trivialDefectN)` in the upward step.
* **The downward step** (`relayOdds_down`, `relayOdds_down_sector`): with `a = 0`, `s = m`, if
  `o(2m) ≤ δ` then `o(m) ≤ √(o(0) · κ(0,m) · δ) ≤ √((N³ − 1) · κ(0,m) · δ)`. The anchor `o(0)` is the one-hop
  read and is at most `N³ − 1` (`relayOdds_le_card`). The step lands at `ε` from `o(2m) ≤ ε²/((N³ − 1) κ(0,m))`
  (`N ≥ 2`).
* **Its degradation** (`down_not_contracting`): for `0 ≤ δ ≤ 1` and `1 ≤ c`, `δ ≤ √(c δ)`. The downward map
  `δ ↦ √(c δ)` never returns a bound below its input on `[0, 1]`; it runs the upward squaring
  `CentreSectorSeedN.fluxShareDoubled_leN` (index `m → 2m + 1`) the other way, from index `2m` to `m`; the two
  index pairs differ by one hop. `k` downward halvings return `c^{1 − 2^{−k}} δ^{2^{−k}}` (argued: iterate the
  map), so the long read enters only through its `2^k`-th root.
* **No `κ`-free downward map** (`no_downward_from_traces`). Proved: the real-number lemma
  `no_downward_from_traces`: for every `S ≥ 0` and `δ > 0` there are `q ∈ ℕ` and `0 < x < 1` with
  `S q x/(1 + q x) = S/2`, `S q x²/(1 + q x²) ≤ δ`, and `S q y/(1 + q y) ≤ S` for every `y ≥ 0`. It contains no
  kernel, spectrum, trace, `κ` or log-convexity. Argued: its reading as zero-flux spectrum `{1} ∪ {r × q}` and flux
  spectrum `{r × S q}` with `S = N³ − 1` (an integer, as the multiplicity reading needs), `x = r^{2t}`; that these
  spectra are log-convex and meet `relayOdds_le_card` and (argued) the three log-convexities; the `κ` lower bound
  `κ(0, ·) ≥ (1 + q^{1 − 1/t})/4`, with `q ≥ S/δ`, unbounded as `δ → 0` at `t ≥ 2` and `S > 0`; the transfer from
  hop pairs `(t, 2t)` to the index pair `(m, 2m)` of `relayOdds_down`; and realizability by `kT`. Read so, no `f`
  with `f(δ) → 0` bounds `o(t)` by `f(o(2t))`: once the anchor is bounded by `N³ − 1`, the obstruction is `κ`. A
  `κ`-free midpoint would need the endpoint at chain length `0`, the identity, whose trace is the dimension of the
  slice space, which is infinite; `κ` depends on `T` and `β`, so no `T`-, `β`-free `f` exists (argued).
* **Zero-flux defect along the chain** (`relayDefect_eq`, `relayDefect_le_anchor`):
  `relayDefect j ≤ log Z₀(0) + log Z₀(2j) − log Z₀(2j+1)`: anchored the same way.
* **Fixed aperture, any chain length, on the Wilson family** (`exists_relayTorus`, `relayTorus_twoSlice`): for
  every aperture `T` with positive extents and every `j` there is a rectangular torus `L` with `L i = 2j + 2` and
  transverse extents `T` whose Wilson state (`RectTorusState.rectState`) has the two-slice law `a²/hs(a)`,
  `a = iter K j` (`RectTorusState.rectState_pairObs`). The rectangular family varies the chain length with the
  aperture fixed, and the two-slice bridge holds on every member. `relayTorus_twoSlice` is a thin wrapper:
  `RectTorusState.rectState_pairObs` is already general in `L`, and this module adds only `exists_relayTorus`.
  `twoSliceLaw_rectState` itself is stated only on the corner tori `ext n (pathV i)`, where time extent and
  aperture are tied.
* `Tr_two_pow_mul`: the corner aperture at side `2^l n` is `2^l` times the aperture at side `n`, at every step.
* **The degenerate coupling** (`relayOdds_zero_coupling`): at `β = 0` the hop is `1`, every chain read has odds `0`.

## The across-aperture step

The relay never changes the aperture, and `SectorSeedMeasured`'s window clause `n · m′ ≤ C` bounds the aperture.
What relates aperture `T` to `2T` is named once:

* **`CoarseReadsFine hN`** (assumed): there are `c ≥ 1` and `C₀ > 0` such that, eventually in `β`, the unit locks
  (`0 < m′`) and at every aperture whose extents are all at least `C₀/m′`, over every chain whose coarse time
  extent `2(j + 1)` is at least `C₀/m′`, the coarse observer's odds over `j` hops are at most `c` times the fine
  observer's odds over the relayed chain of `2j + 1` hops: `o(2T, j) ≤ c · o(T, 2j + 1)`. Each
  winding-direction-by-time area is the same on the two tori (their 4-volumes differ by a factor of `4`).
* `odds_doubling_iter`, `fluxShareN_le_of_exchange` (proved): under the exchange at one coupling, for apertures in a
  class closed under doubling and chains in a class closed upward, the cubic flux share at side `2^l n` is at most
  `c^l · o(Tr n i, 4^l (n/2) − 1)`, the relay read at the base aperture over a chain `4^l` times as long. The
  iteration applies the exchange only at chain index `2^l (j + 1) − 1 ≥ j`. `fluxShareN_le_of_coarseReadsFine`:
  from `CoarseReadsFine`, eventually in `β`, at every even side `n ≥ 2` with `C₀ ≤ n m′`; there the coarse time
  extent is `2^l n ≥ n`, so the side condition supplies the time clause.

Tests of `CoarseReadsFine`.

1. Degenerate case: at `β = 0` both sides are `0` (`exchange_zero_coupling`); at `N = 1` the centre is trivial and
   both sides are `0` (argued).
2. Strong coupling (argued, leading order): a flux sheet winding direction `k` costs `u^{T_k · time}` and sits at
   `T_l T_m` transverse places, so `o(2T, j) ≈ 4 · o(T, 2j+1)`, the same exponent with the factor `2²` of the two
   co-transverse directions; `c ≥ 4` is needed and no `T` enters. The tree proves only upper bounds on the reads
   at strong coupling (`SubstrateFluxRead.sectors_strong`), so this test is not a theorem.
3. Long chains (argued): with flux energy `E(T)` per hop, over unbounded chains the Prop asks `E(2T) ≥ 2E(T)`
   exactly, with `c` absorbing only the prefactors; linear confinement `E = σT` is the margin, and the sign of the
   string correction decides it; a closed flux tube has `E(T) = σT − π/(3T) + …`, so `E(2T) − 2E(T) = π/(2T) > 0`, consistent. It fails where
   `E` is sub-additive, which is small volume, `T m′ ≪ 1`, where `E ∝ g²/T`; the clause `C₀ ≤ T m′` excludes that.
4. Vacuity: the lock clause `0 < m′` is required (at `m′ = 0` no aperture meets `C₀ ≤ T m′` and the Prop would be
   empty); an aperture with an extent `0` never meets the clause, since `0 · m′ = 0`. The inequality is not implied
   by the proved bound `o ≤ N³ − 1`.
5. Restatement against reduction: `CoarseReadsFine` is neither. It assumes the lock `0 < m′` as well, and it
   reduces the flux clause of the onset at window sides `2^l n` (for fixed `l`; the window constant becomes
   `2^{l+1} C₀`) to a fixed-aperture long-chain read at the base aperture (`fluxShareN_le_of_coarseReadsFine`), a
   read the rectangular tori realize (`relayTorus_twoSlice`); it says nothing about the zero-flux clause
   (`trivialDefectN`), and it does not bound the long-chain read. It is not implied by `SectorSeedMeasured`, which
   speaks of one side, not of all apertures above `C₀/m′`.
6. Short chains (argued): below the deconfinement time extent the coarse torus is deconfined while the fine one
   is confined; the clause `C₀ ≤ 2(j + 1) m′` excludes it.

## What the relay gives for the open input, and what it does not

It gives both chain directions as inequalities: upward by squaring at cost
`exp(dd)`, downward by a square root at cost `o(0) κ(0,m)`. It does not give the cubic downward step `n ← 2n`:
that halves the aperture as well, and on the cubic torus the time extent and aperture are tied. The downward
relay's anchor is the one-hop read; `κ(0,m)` is the effective number of zero-flux states over one hop relative to
`m` hops, a lattice-scale quantity that grows without bound as `β → ∞` (argued), so the downward relay does not
carry a bound from long chains down to the window at weak coupling. `SectorSeedMeasured` follows from `CoarseReadsFine`, `GapFromReads.LongChainRead` and
`ZeroFluxGap.ZeroFluxReadsMass` (`GapFromReads.sectorSeedMeasured_of_reads`); it is open without them.

## Argued, not proved

The spectral reading of `κ`, the leading-order strong-coupling exchange factor `4`, the flux-tube energies in
test 3, and the growth of `κ(0,m)` at weak coupling. No module computes a spectrum of `kT`.

## Assumed

`CoarseReadsFine hN` only, and only in `fluxShareN_le_of_coarseReadsFine`; every other theorem is proved; the
spectral reading of `no_downward_from_traces` and the tests are argued.

## Parameters

| argument | where | status |
|---|---|---|
| `β` (coupling) | every read | shared, in the substrate; fixed in each inequality |
| `i` (direction), `T` (aperture) | every read | chosen; the slice geometry, fixed along the chain |
| `j`, `a`, `s`, `m` (chain indices) | the reads, `relayZ_sq_le`, `relayOdds_mid`, `relayOdds_down` | swept over all |
| `δ` | `relayOdds_down`, `down_not_contracting` | chosen: any bound on the read at `2m` |
| `κ(a,s)` | `relayCost` | measured: a ratio of zero-flux traces of the same slice |
| `c`, `C₀` | `CoarseReadsFine` | existential; `c` shared (no `T`, `β`, `j`), `C₀` in units of the measured length `1/m′` |
| `l` (doublings) | `odds_doubling_iter`, `fluxShareN_le_of_exchange` | swept over all |
| `n` (side) | `fluxShareN_le_of_*` | chosen: even, `≥ 2`, `C₀ ≤ n m′` |
| `m′` | `CoarseReadsFine` | measured: `measMassOf (periodicState) tensorEnergy` |
| `S`, `δ`, `q`, `t` | `no_downward_from_traces` | `S` chosen (`N³ − 1` in the reading), `δ` chosen, `q` existential, `t` the hop length of the reading |
| `N` | the type | shared with the substrate; not measured |

DERIVED (module-wide): `2` the square of Cauchy–Schwarz and in `2s`, `2j + 1`, `2(j + 1)`; `1` the one-hop shift
`h (a+1) = h a ∗ K` and the lower bound of `κ`; `0` the one-hop anchor `iter K 0 = K`; `N³ = |Z_N³|`
(`SliceCentreAction.card_cen`) and `N³ − 1` the largest flux odds; `4 = 2²` the co-transverse factor and
`4^l = 2^l · 2^l`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.RelayChain

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate
open MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.KernelPower MassGap.SectorDefect MassGap.FluxSectorFourier MassGap.ZeroFluxSector
open MassGap.SliceCentreAction (Cen act centreAction card_cen iter_act kT_act)
open MassGap.CentreSectorSeedN (fluxShareN trivialDefectN)
open MassGap.SubstrateDecode (measMassOf tensorEnergy)
open MassGap.PeriodicState (periodicState)

/-! ## 1. The pairing along a relayed family -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

variable (μ) in
/-- **The pairing of two kernels**, `∫∫ a(x, z) c(x, z)`. DERIVED: no numeral. -/
def kpair (a c : X → X → ℝ) : ℝ := ∫ x, ∫ z, a x z * c x z ∂μ ∂μ

/-- `hs` is the pairing of a kernel with itself. DERIVED: `2` the square. -/
theorem hs_eq_kpair (h : X → X → ℝ) : hs μ h = kpair μ h h := by
  unfold hs kpair
  congr 1; funext x; congr 1; funext z; ring

/-- A bounded kernel has a nonnegative bound. DERIVED: `0`. -/
theorem bdd_nonneg_bound {h : X → X → ℝ} (hh : Bdd h) : ∃ C, 0 ≤ C ∧ ∀ x y, |h x y| ≤ C := by
  obtain ⟨C, hC⟩ := hh.bdd
  exact ⟨|C|, abs_nonneg _, fun x y => (hC x y).trans (le_abs_self C)⟩

/-- A product of two bounded measurable functions is integrable. DERIVED: no numeral. -/
theorem int_mul2 {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {Cf Cg : ℝ}
    (hfC : ∀ y, |f y| ≤ Cf) (hgC : ∀ y, |g y| ≤ Cg) : Integrable (fun y => f y * g y) μ :=
  integrable_of_bdd (hf.mul hg) (C := Cf * Cg) (fun y => by
    rw [abs_mul]; exact mul_le_mul (hfC y) (hgC y) (abs_nonneg _) ((abs_nonneg _).trans (hfC y)))

/-- **One hop moves across the pairing**: for a symmetric `K`, `⟨u ∗ K, v⟩ = ⟨u, v ∗ K⟩`.
DERIVED: no numeral. -/
theorem kpair_conv_shift {u v K : X → X → ℝ} (hu : Bdd u) (hv : Bdd v) (hK : Bdd K)
    (hsym : ∀ x y, K x y = K y x) :
    kpair μ (conv μ u K) v = kpair μ u (conv μ v K) := by
  obtain ⟨Cu, hCu0, hCu⟩ := bdd_nonneg_bound hu
  obtain ⟨Cv, hCv0, hCv⟩ := bdd_nonneg_bound hv
  obtain ⟨CK, hCK0, hCK⟩ := bdd_nonneg_bound hK
  unfold kpair
  congr 1; funext x
  have hF : Measurable (Function.uncurry (fun z y => u x y * K y z * v x z)) :=
    (((hu.row x).comp measurable_snd).mul (hK.meas.comp (measurable_snd.prodMk measurable_fst))).mul
      ((hv.row x).comp measurable_fst)
  have hFb : ∀ z y, |u x y * K y z * v x z| ≤ Cu * CK * Cv := by
    intro z y
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hCu x y) (hCK y z) (abs_nonneg _) hCu0) (hCv x z) (abs_nonneg _)
      (mul_nonneg hCu0 hCK0)
  calc ∫ z, conv μ u K x z * v x z ∂μ
      = ∫ z, ∫ y, u x y * K y z * v x z ∂μ ∂μ := by
        congr 1; funext z
        show (∫ y, u x y * K y z ∂μ) * v x z = _
        rw [← integral_mul_const]
    _ = ∫ y, ∫ z, u x y * K y z * v x z ∂μ ∂μ := swap_bdd hF hFb
    _ = ∫ y, u x y * conv μ v K x y ∂μ := by
        congr 1; funext y
        show _ = u x y * ∫ z, v x z * K z y ∂μ
        rw [← integral_const_mul]
        congr 1; funext z
        rw [hsym z y]; ring

/-- **Cauchy–Schwarz for the pairing**: `⟨f, g⟩² ≤ hs f · hs g`, on `μ ⊗ μ`. DERIVED: `2` the square. -/
theorem kpair_sq_le {f g : X → X → ℝ} (hf : Bdd f) (hg : Bdd g) :
    kpair μ f g ^ 2 ≤ hs μ f * hs μ g := by
  obtain ⟨Cf, hCf0, hCf⟩ := bdd_nonneg_bound hf
  obtain ⟨Cg, hCg0, hCg⟩ := bdd_nonneg_bound hg
  have iF2 : Integrable (fun p : X × X => f p.1 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hf.meas.pow_const 2) (C := Cf ^ 2) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCf _ _) 2
  have iG2 : Integrable (fun p : X × X => g p.1 p.2 ^ 2) (μ.prod μ) :=
    integrable_of_bdd (hg.meas.pow_const 2) (C := Cg ^ 2) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCg _ _) 2
  have iFG : Integrable (fun p : X × X => f p.1 p.2 * g p.1 p.2) (μ.prod μ) :=
    integrable_of_bdd (hf.meas.mul hg.meas) (C := Cf * Cg) fun p => by
      rw [abs_mul]; exact mul_le_mul (hCf _ _) (hCg _ _) (abs_nonneg _) hCf0
  have e1 : kpair μ f g = ∫ p, f p.1 p.2 * g p.1 p.2 ∂(μ.prod μ) := (integral_prod _ iFG).symm
  have e2 : hs μ f = ∫ p, f p.1 p.2 ^ 2 ∂(μ.prod μ) := (integral_prod _ iF2).symm
  have e3 : hs μ g = ∫ p, g p.1 p.2 ^ 2 ∂(μ.prod μ) := (integral_prod _ iG2).symm
  rw [e1, e2, e3]
  exact sq_integral_mul_le iF2 iG2 iFG

/-- **The pairing along a relayed family depends on the total length**: if `h (a + 1) = h a ∗ K`,
`⟨h a, h (a + 2s)⟩ = hs(h (a + s))`. DERIVED: `2` the two ends; `1` the hop. -/
theorem kpair_family {K : X → X → ℝ} (hK : Bdd K) (hsym : ∀ x y, K x y = K y x)
    {h : ℕ → X → X → ℝ} (hb : ∀ a, Bdd (h a)) (hstep : ∀ a, h (a + 1) = conv μ (h a) K) :
    ∀ a s, kpair μ (h a) (h (a + 2 * s)) = hs μ (h (a + s)) := by
  intro a s
  induction s generalizing a with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact (hs_eq_kpair _).symm
  | succ s ih =>
    have e1 : a + 2 * (s + 1) = (a + 2 * s + 1) + 1 := by ring
    have e2 : a + (s + 1) = (a + 1) + s := by ring
    have e3 : a + 1 + 2 * s = a + 2 * s + 1 := by ring
    rw [e1, e2, ← ih (a + 1), e3, hstep (a + 2 * s + 1), hstep a]
    exact (kpair_conv_shift (hb a) (hb _) hK hsym).symm

/-- **Log-convexity along a relayed family**: `hs(h (a + s))² ≤ hs(h a) · hs(h (a + 2s))`.
DERIVED: `2` the square and the two ends. -/
theorem hs_family_sq_le {K : X → X → ℝ} (hK : Bdd K) (hsym : ∀ x y, K x y = K y x)
    {h : ℕ → X → X → ℝ} (hb : ∀ a, Bdd (h a)) (hstep : ∀ a, h (a + 1) = conv μ (h a) K) (a s : ℕ) :
    hs μ (h (a + s)) ^ 2 ≤ hs μ (h a) * hs μ (h (a + 2 * s)) := by
  rw [← kpair_family hK hsym hb hstep a s]
  exact kpair_sq_le (hb a) (hb _)

/-- One more hop on the right: `iter K (a + 1) = iter K a ∗ K`. DERIVED: `0`, `1`. -/
theorem iter_succ_right {k : X → X → ℝ} (hk : Bdd k) (a : ℕ) :
    iter μ k (a + 1) = conv μ (iter μ k a) k := by
  have h := iter_add (μ := μ) hk a 0
  rw [Nat.add_zero] at h
  exact h

/-- **Log-convexity of the trace along the chain.** DERIVED: `2`. -/
theorem hs_iter_sq_le {K : X → X → ℝ} (hK : Bdd K) (hsym : ∀ x y, K x y = K y x) (a s : ℕ) :
    hs μ (iter μ K (a + s)) ^ 2 ≤ hs μ (iter μ K a) * hs μ (iter μ K (a + 2 * s)) :=
  hs_family_sq_le hK hsym (fun a => hK.iter a) (iter_succ_right hK) a s

/-! ## 2. The zero-flux and flux blocks along the chain -/

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {act : G → X → X}

/-- **The zero-flux projection commutes with one more hop**: `zk(f ∗ K) = zk f ∗ K` for an invariant `K`.
DERIVED: `-g` the inverse element. -/
theorem zk_conv_right {f K : X → X → ℝ} (hf : Bdd f) (hK : Bdd K) (hA : CentreAction μ act)
    (hinv : ∀ g x y, K (act g x) (act g y) = K x y) :
    zk (conv μ f K) act = conv μ (zk f act) K := by
  obtain ⟨Cf, hCf0, hCf⟩ := bdd_nonneg_bound hf
  obtain ⟨CK, hCK0, hCK⟩ := bdd_nonneg_bound hK
  funext x z
  have hterm : ∀ g, ∫ y, f x (act g y) * K y z ∂μ = ∫ y, f x y * K y (act g z) ∂μ := by
    intro g
    have h := hA.integral_comp (-g) (fun y => f x (act g y) * K y z)
    rw [← h]
    congr 1; funext y
    have h1 : act g (act (-g) y) = y := by rw [← hA.add, add_neg_cancel, hA.zero]
    have h2 : K (act (-g) y) z = K y (act g z) := by
      rw [← hinv g (act (-g) y) z, h1]
    simp only [h1, h2]
  have hint : ∀ g, Integrable (fun y => f x (act g y) * K y z) μ := fun g =>
    int_mul2 ((hf.row x).comp (hA.meas g)) (hK.col z) (fun y => hCf _ _) (fun y => hCK _ _)
  show (Fintype.card G : ℝ)⁻¹ * ∑ g, conv μ f K x (act g z) = ∫ y, zk f act x y * K y z ∂μ
  have e : (fun y => zk f act x y * K y z)
      = fun y => (Fintype.card G : ℝ)⁻¹ * ∑ g, f x (act g y) * K y z := by
    funext y
    show (Fintype.card G : ℝ)⁻¹ * (∑ g, f x (act g y)) * K y z = _
    rw [mul_assoc, Finset.sum_mul]
  rw [e, integral_const_mul, integral_finsetSum _ fun g _ => hint g]
  simp_rw [hterm]
  rfl

/-- **The flux block** `fk h = h − zk h`: the part of `h` carried by the non-trivial centre characters.
DERIVED: no numeral. -/
def fk (h : X → X → ℝ) (act : G → X → X) : X → X → ℝ := fun x y => h x y - zk h act x y

theorem bdd_fk {h : X → X → ℝ} (hh : Bdd h) (hA : CentreAction μ act) : Bdd (fk h act) := by
  obtain ⟨C, hC0, hC⟩ := bdd_nonneg_bound hh
  refine ⟨hh.meas.sub (measurable_zk hh hA), C + C, fun x y => ?_⟩
  have t := abs_add_le (h x y) (-zk h act x y)
  rw [abs_neg, ← sub_eq_add_neg] at t
  exact t.trans (add_le_add (hC x y) (abs_zk_le hC x y))

/-- **The flux block commutes with one more hop**: `fk(f ∗ K) = fk f ∗ K`. DERIVED: no numeral. -/
theorem fk_conv_right {f K : X → X → ℝ} (hf : Bdd f) (hK : Bdd K) (hA : CentreAction μ act)
    (hinv : ∀ g x y, K (act g x) (act g y) = K x y) :
    fk (conv μ f K) act = conv μ (fk f act) K := by
  obtain ⟨Cf, hCf0, hCf⟩ := bdd_nonneg_bound hf
  obtain ⟨CK, hCK0, hCK⟩ := bdd_nonneg_bound hK
  have bz := bdd_zk hf hA
  have hz := zk_conv_right hf hK hA hinv
  funext x z
  show conv μ f K x z - zk (conv μ f K) act x z = ∫ y, fk f act x y * K y z ∂μ
  rw [hz]
  show (∫ y, f x y * K y z ∂μ) - (∫ y, zk f act x y * K y z ∂μ) = ∫ y, (f x y - zk f act x y) * K y z ∂μ
  rw [← integral_sub (int_mul2 (hf.row x) (hK.col z) (hCf x) (fun y => hCK y z))
    (int_mul2 (bz.row x) (hK.col z) (abs_zk_le hCf x) (fun y => hCK y z))]
  congr 1; funext y; ring

/-- The row pairing of a kernel with its zero-flux part is the zero-flux row square. DERIVED: `1` the trivial
character; `2` the square. -/
theorem integral_mul_zk {h : X → X → ℝ} (hh : Bdd h) (hA : CentreAction μ act) (x : X) :
    ∫ z, h x z * zk h act x z ∂μ = ∫ z, zk h act x z ^ 2 ∂μ := by
  have h1 := integral_a_mul_conj_sec hh hA (1 : AddChar G ℂ) x x
  rw [gramC_diag, secDiag_one] at h1
  simp_rw [sec_one, Complex.conj_ofReal, ← Complex.ofReal_mul] at h1
  rw [integral_complex_ofReal] at h1
  exact_mod_cast h1

/-- **The trace of the flux block is the flux trace**: `hs(fk h) = hs h − hs(zk h)`. DERIVED: `2` the square
and the cross term. -/
theorem hs_fk {h : X → X → ℝ} (hh : Bdd h) (hA : CentreAction μ act) :
    hs μ (fk h act) = hs μ h - hs μ (zk h act) := by
  obtain ⟨C, hC0, hC⟩ := bdd_nonneg_bound hh
  have bz := bdd_zk hh hA
  have hrow : ∀ x, ∫ z, fk h act x z ^ 2 ∂μ = ∫ z, h x z ^ 2 ∂μ - ∫ z, zk h act x z ^ 2 ∂μ := by
    intro x
    have i1 : Integrable (fun z => h x z ^ 2) μ :=
      integrable_of_bdd ((hh.row x).pow_const 2) (C := C ^ 2) fun z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC x z) 2
    have i2 : Integrable (fun z => zk h act x z ^ 2) μ :=
      integrable_of_bdd ((bz.row x).pow_const 2) (C := C ^ 2) fun z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_zk_le hC x z) 2
    have i3 : Integrable (fun z => h x z * zk h act x z) μ :=
      int_mul2 (hh.row x) (bz.row x) (hC x) (abs_zk_le hC x)
    have i12 : Integrable (fun z => h x z ^ 2 + zk h act x z ^ 2) μ := i1.add i2
    have i3' : Integrable (fun z => 2 * (h x z * zk h act x z)) μ := i3.const_mul 2
    have e : (fun z => fk h act x z ^ 2)
        = fun z => (h x z ^ 2 + zk h act x z ^ 2) - 2 * (h x z * zk h act x z) := by
      funext z; show (h x z - zk h act x z) ^ 2 = _; ring
    rw [e, integral_sub i12 i3', integral_add i1 i2, integral_const_mul, integral_mul_zk hh hA x]
    ring
  unfold hs
  simp_rw [hrow]
  exact integral_sub (int_row (bdd_sq hh)) (int_row (bdd_sq bz))

/-- **Log-convexity of the zero-flux trace along the chain.** DERIVED: `2`. -/
theorem hs_zk_iter_sq_le {K : X → X → ℝ} (hK : Bdd K) (hsym : ∀ x y, K x y = K y x)
    (hA : CentreAction μ act) (hinv : ∀ g x y, K (act g x) (act g y) = K x y) (a s : ℕ) :
    hs μ (zk (iter μ K (a + s)) act) ^ 2
      ≤ hs μ (zk (iter μ K a) act) * hs μ (zk (iter μ K (a + 2 * s)) act) :=
  hs_family_sq_le (h := fun a => zk (iter μ K a) act) hK hsym (fun a => bdd_zk (hK.iter a) hA)
    (fun a => by
      show zk (iter μ K (a + 1)) act = conv μ (zk (iter μ K a) act) K
      rw [iter_succ_right hK a]
      exact zk_conv_right (hK.iter a) hK hA hinv) a s

/-- **Log-convexity of the flux trace along the chain.** DERIVED: `2`. -/
theorem hs_fk_iter_sq_le {K : X → X → ℝ} (hK : Bdd K) (hsym : ∀ x y, K x y = K y x)
    (hA : CentreAction μ act) (hinv : ∀ g x y, K (act g x) (act g y) = K x y) (a s : ℕ) :
    hs μ (fk (iter μ K (a + s)) act) ^ 2
      ≤ hs μ (fk (iter μ K a) act) * hs μ (fk (iter μ K (a + 2 * s)) act) :=
  hs_family_sq_le (h := fun a => fk (iter μ K a) act) hK hsym (fun a => bdd_fk (hK.iter a) hA)
    (fun a => by
      show fk (iter μ K (a + 1)) act = conv μ (fk (iter μ K a) act) K
      rw [iter_succ_right hK a]
      exact fk_conv_right (hK.iter a) hK hA hinv) a s

end Generic

/-! ## 3. Real-number steps -/

/-- The odds at the midpoint from the flux and zero-flux log-convexities. DERIVED: `2` the square. -/
theorem odds_mid_real {Fa Fm Fb Ba Bm Bb : ℝ} (hBa : 0 < Ba) (hBm : 0 < Bm) (hBb : 0 < Bb)
    (h : Fm ^ 2 ≤ Fa * Fb) :
    (Fm / Bm) ^ 2 ≤ (Fa / Ba) * (Fb / Bb) * (Ba * Bb / Bm ^ 2) := by
  have e : (Fa / Ba) * (Fb / Bb) * (Ba * Bb / Bm ^ 2) = Fa * Fb / Bm ^ 2 := by
    field_simp
  rw [e, div_pow]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- **The downward map does not contract on `[0, 1]`**: `δ ≤ √(c δ)` for `0 ≤ δ ≤ 1 ≤ c`.
DERIVED: `0`, `1` the interval; `2` the square root. -/
theorem down_not_contracting {δ c : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hc : 1 ≤ c) : δ ≤ Real.sqrt (c * δ) := by
  calc δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (c * δ) := Real.sqrt_le_sqrt (by nlinarith)

/-- **No `κ`-free downward map on sector spectra**: for every `S ≥ 0` and `δ > 0` there are a multiplicity `q`
and `0 < x < 1` with odds `S q x/(1 + q x) = S/2`, odds `S q x²/(1 + q x²) ≤ δ`, and odds at most `S` at every
`y ≥ 0`. Read: zero-flux spectrum `{1} ∪ {r × q}`, flux spectrum `{r × S q}`, `x = r^{2t}`; the odds at length `t`
are `S/2`, at length `2t` at most `δ`, and at no length above the sector bound `S = N³ − 1`. With the
one-hop anchor `r²`, `κ = (1 + q r²)(1 + q x²)/(1 + q x)² ≥ (1 + q r²)/4`, and `q r² = q^{1 − 1/t}`. DERIVED: `2` the half share and the square; `1` the zero-flux top;
`S/δ` the least multiplicity. -/
theorem no_downward_from_traces (S δ : ℝ) (hS : 0 ≤ S) (hδ : 0 < δ) :
    ∃ q : ℕ, ∃ x : ℝ, 0 < x ∧ x < 1 ∧
      S * q * x / (1 + q * x) = S / 2 ∧
      S * q * x ^ 2 / (1 + q * x ^ 2) ≤ δ ∧
      ∀ y : ℝ, 0 ≤ y → S * q * y / (1 + q * y) ≤ S := by
  have hc : (0 : ℝ) ≤ ⌈S / δ⌉₊ := Nat.cast_nonneg _
  have hq : ((⌈S / δ⌉₊ + 2 : ℕ) : ℝ) = (⌈S / δ⌉₊ : ℝ) + 2 := by push_cast; ring
  set q : ℕ := ⌈S / δ⌉₊ + 2 with hqdef
  have hq2 : (2 : ℝ) ≤ q := by rw [hq]; linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have h1 : (q : ℝ) * (1 / q) = 1 := mul_one_div_cancel hq0.ne'
  refine ⟨q, 1 / q, by positivity, by rw [div_lt_one hq0]; linarith, ?_, ?_, ?_⟩
  · rw [mul_assoc, h1, mul_one]; norm_num
  · have e : S * q * (1 / q) ^ 2 / (1 + q * (1 / q) ^ 2) = S / (q + 1) := by
      field_simp
    rw [e, div_le_iff₀ (by linarith)]
    have hSq : S / δ ≤ ⌈S / δ⌉₊ := Nat.le_ceil _
    have h3 : S ≤ δ * ⌈S / δ⌉₊ := by rw [div_le_iff₀ hδ] at hSq; linarith
    rw [hq]
    nlinarith
  · intro y hy
    rw [div_le_iff₀ (by positivity)]
    have e : S * (1 + q * y) = S + S * q * y := by ring
    linarith

/-! ## 4. The relay reads on one slice -/

section Lattice

variable {N : ℕ} [NeZero N]

variable (N) in
/-- **The chain trace** at chain index `j`: `Tr K^{2(j+1)} = hs(iter K j)` on the slice of direction `i` with
aperture `T`. DERIVED: no numeral. -/
def relayZ (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  hs (hS i T N) (iter (hS i T N) (kT i T N β) j)

variable (N) in
/-- **The zero-flux chain trace.** DERIVED: no numeral. -/
def relayZ0 (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  hs (hS i T N) (zk (iter (hS i T N) (kT i T N β) j) (act (μ := i) (T := T) (N := N)))

variable (N) in
/-- **The twisted chain trace** `Z_g`. DERIVED: no numeral. -/
def relayTwist (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) (g : Cen i N) : ℝ :=
  FluxSectorBound.twist (hS i T N) (iter (hS i T N) (kT i T N β) j) (act (T := T) g)

variable (N) in
/-- **The flux share at chain index `j`.** DERIVED: no numeral. -/
def relayShare (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  (relayZ N i T β j - relayZ0 N i T β j) / relayZ N i T β j

variable (N) in
/-- **The flux odds at chain index `j`.** DERIVED: no numeral. -/
def relayOdds (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  (relayZ N i T β j - relayZ0 N i T β j) / relayZ0 N i T β j

variable (N) in
/-- **The zero-flux defect at chain index `j`.** DERIVED: no numeral. -/
def relayDefect (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (j : ℕ) : ℝ :=
  dd (hS i T N) (zk (iter (hS i T N) (kT i T N β) j) (act (μ := i) (T := T) (N := N)))

variable (N) in
/-- **The cost of the midpoint**, `κ(a, s) = Z₀(a) Z₀(a+2s) / Z₀(a+s)²`. DERIVED: `2` the square and the two
ends. -/
def relayCost (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (β : ℝ) (a s : ℕ) : ℝ :=
  relayZ0 N i T β a * relayZ0 N i T β (a + 2 * s) / relayZ0 N i T β (a + s) ^ 2

/-- **The cubic flux share is the relay share** at aperture `Tr n i`, chain index `n/2 − 1`.
DERIVED: `2`, `1` the half side. -/
theorem fluxShareN_eq_relay (β : ℝ) (n : ℕ) (i : Fin 4) :
    fluxShareN N β n i = relayShare N i (CentreSectorSeed.Tr n i) β (n / 2 - 1) := rfl

/-- **The cubic zero-flux defect is the relay defect.** DERIVED: `2`, `1` the half side. -/
theorem trivialDefectN_eq_relay (β : ℝ) (n : ℕ) (i : Fin 4) :
    trivialDefectN N β n i = relayDefect N i (CentreSectorSeed.Tr n i) β (n / 2 - 1) := rfl

section Facts

variable {i : Fin 4} {T : {k : Fin 4 // k ≠ i} → ℕ} {β : ℝ}

theorem bdd_iterK (hβ : 0 ≤ β) (j : ℕ) : Bdd (iter (hS i T N) (kT i T N β) j) :=
  (bdd_kT (NeZero.ne N) hβ).iter j

theorem low_iterK (hβ : 0 ≤ β) (j : ℕ) :
    ∀ x y, kTmin i T β ^ (j + 1) ≤ iter (hS i T N) (kT i T N β) j x y :=
  iter_low (bdd_kT (NeZero.ne N) hβ) (kTmin_pos β).le (kT_lower (NeZero.ne N) hβ) j

theorem relayZ_pos (hβ : 0 ≤ β) (j : ℕ) : 0 < relayZ N i T β j := by
  have hc : 0 < kTmin i T β ^ (j + 1) := pow_pos (kTmin_pos β) _
  have := sq_le_hs (μ := hS i T N) (bdd_iterK hβ j) hc.le (low_iterK hβ j)
  unfold relayZ
  nlinarith

theorem relayZ0_pos (hβ : 0 ≤ β) (j : ℕ) : 0 < relayZ0 N i T β j :=
  hs_zk_pos (pow_pos (kTmin_pos β) (j + 1)) (bdd_iterK hβ j) centreAction (low_iterK hβ j)

theorem relayZ0_le (hβ : 0 ≤ β) (j : ℕ) : relayZ0 N i T β j ≤ relayZ N i T β j :=
  hs_zk_le (bdd_iterK hβ j) centreAction

/-- The zero-flux trace carries at least `N⁻³` of the chain trace. DERIVED: `3`. -/
theorem relayZ_le_card (hβ : 0 ≤ β) (j : ℕ) : relayZ N i T β j ≤ (N : ℝ) ^ 3 * relayZ0 N i T β j := by
  have h := hs_div_card_le_hs_zk (bdd_iterK hβ j)
    (fun x y => (pow_pos (kTmin_pos β) (j + 1)).le.trans (low_iterK hβ j x y))
    (centreAction (μ := i) (T := T) (N := N))
  rw [card_cen] at h
  have hM : (0 : ℝ) < (N : ℝ) ^ 3 := by
    have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    positivity
  push_cast at h
  have := (div_le_iff₀ hM).mp h
  unfold relayZ relayZ0
  linarith

theorem relayOdds_nonneg (hβ : 0 ≤ β) (j : ℕ) : 0 ≤ relayOdds N i T β j :=
  div_nonneg (by linarith [relayZ0_le (N := N) (i := i) (T := T) hβ j]) (relayZ0_pos hβ j).le

/-- **The flux odds are at most `N³ − 1`.** DERIVED: `3`, `1`. -/
theorem relayOdds_le_card (hβ : 0 ≤ β) (j : ℕ) : relayOdds N i T β j ≤ (N : ℝ) ^ 3 - 1 := by
  have hB := relayZ0_pos (N := N) (i := i) (T := T) hβ j
  unfold relayOdds
  rw [div_le_iff₀ hB]
  have := relayZ_le_card (N := N) (i := i) (T := T) hβ j
  linarith

/-- The share is at most the odds. DERIVED: no numeral. -/
theorem relayShare_le_odds (hβ : 0 ≤ β) (j : ℕ) : relayShare N i T β j ≤ relayOdds N i T β j :=
  div_le_div_of_nonneg_left (by linarith [relayZ0_le (N := N) (i := i) (T := T) hβ j])
    (relayZ0_pos hβ j) (relayZ0_le hβ j)

/-- **The flux share is one minus the mean twisted ratio**: `relayShare = 1 − N⁻³ Σ_g Z_g/Z`.
DERIVED: `3`. -/
theorem relayShare_eq_mean (hβ : 0 ≤ β) (j : ℕ) :
    relayShare N i T β j = 1 - ((N : ℝ) ^ 3)⁻¹ * ∑ g, relayTwist N i T β j g / relayZ N i T β j := by
  have hA := relayZ_pos (N := N) (i := i) (T := T) hβ j
  have hB := hs_zk_eq_mean (bdd_iterK (N := N) (i := i) (T := T) hβ j)
    (centreAction (μ := i) (T := T) (N := N))
  rw [card_cen] at hB
  push_cast at hB
  unfold relayShare relayZ0 relayTwist
  rw [hB, ← Finset.sum_div, sub_div, div_self hA.ne']
  unfold relayZ
  ring

/-! ### Log-convexity on the slice -/

/-- **The chain trace is log-convex**: `Z(a+s)² ≤ Z(a) Z(a+2s)`. DERIVED: `2`. -/
theorem relayZ_sq_le (hβ : 0 ≤ β) (a s : ℕ) :
    relayZ N i T β (a + s) ^ 2 ≤ relayZ N i T β a * relayZ N i T β (a + 2 * s) :=
  hs_iter_sq_le (bdd_kT (NeZero.ne N) hβ) (kT_symm β) a s

/-- **The zero-flux chain trace is log-convex**: `Z₀(a+s)² ≤ Z₀(a) Z₀(a+2s)`. DERIVED: `2`. -/
theorem relayZ0_sq_le (hβ : 0 ≤ β) (a s : ℕ) :
    relayZ0 N i T β (a + s) ^ 2 ≤ relayZ0 N i T β a * relayZ0 N i T β (a + 2 * s) :=
  hs_zk_iter_sq_le (bdd_kT (NeZero.ne N) hβ) (kT_symm β) centreAction (fun g x y => kT_act g β x y) a s

/-- **The flux chain trace is log-convex**: `(Z − Z₀)(a+s)² ≤ (Z − Z₀)(a) · (Z − Z₀)(a+2s)`. DERIVED: `2`. -/
theorem relayFlux_sq_le (hβ : 0 ≤ β) (a s : ℕ) :
    (relayZ N i T β (a + s) - relayZ0 N i T β (a + s)) ^ 2
      ≤ (relayZ N i T β a - relayZ0 N i T β a)
        * (relayZ N i T β (a + 2 * s) - relayZ0 N i T β (a + 2 * s)) := by
  have h := hs_fk_iter_sq_le (bdd_kT (NeZero.ne N) hβ) (kT_symm β)
    (centreAction (μ := i) (T := T) (N := N)) (fun g x y => kT_act g β x y) a s
  have e : ∀ j, hs (hS i T N) (fk (iter (hS i T N) (kT i T N β) j) (act (μ := i) (T := T) (N := N)))
      = relayZ N i T β j - relayZ0 N i T β j := fun j =>
    hs_fk (bdd_iterK hβ j) centreAction
  rw [e, e, e] at h
  exact h

/-- **The midpoint cost is at least one.** DERIVED: `1`, `2`. -/
theorem relayCost_ge_one (hβ : 0 ≤ β) (a s : ℕ) : 1 ≤ relayCost N i T β a s := by
  unfold relayCost
  rw [one_le_div (pow_pos (relayZ0_pos hβ (a + s)) 2)]
  exact relayZ0_sq_le hβ a s

/-- **The odds at the midpoint**: `o(a+s)² ≤ o(a) · o(a+2s) · κ(a,s)`. DERIVED: `2`. -/
theorem relayOdds_mid (hβ : 0 ≤ β) (a s : ℕ) :
    relayOdds N i T β (a + s) ^ 2
      ≤ relayOdds N i T β a * relayOdds N i T β (a + 2 * s) * relayCost N i T β a s :=
  odds_mid_real (relayZ0_pos hβ a) (relayZ0_pos hβ (a + s)) (relayZ0_pos hβ (a + 2 * s))
    (relayFlux_sq_le hβ a s)

/-- **The downward step along the chain**: if the odds at chain index `2m` are at most `δ`, the odds at `m` are at
most `√(o(0) · κ(0,m) · δ)`. DERIVED: `2` the halving and the square root; `0` the one-hop anchor. -/
theorem relayOdds_down (hβ : 0 ≤ β) (m : ℕ) {δ : ℝ} (hδ : relayOdds N i T β (2 * m) ≤ δ) :
    relayOdds N i T β m ≤ Real.sqrt (relayOdds N i T β 0 * relayCost N i T β 0 m * δ) := by
  have h := relayOdds_mid (N := N) (i := i) (T := T) hβ 0 m
  simp only [zero_add] at h
  have ho0 := relayOdds_nonneg (N := N) (i := i) (T := T) hβ 0
  have hκ : 0 ≤ relayCost N i T β 0 m := le_trans zero_le_one (relayCost_ge_one hβ 0 m)
  have h2 : relayOdds N i T β m ^ 2 ≤ relayOdds N i T β 0 * relayCost N i T β 0 m * δ := by
    calc relayOdds N i T β m ^ 2
        ≤ relayOdds N i T β 0 * relayOdds N i T β (2 * m) * relayCost N i T β 0 m := h
      _ = relayOdds N i T β 0 * relayCost N i T β 0 m * relayOdds N i T β (2 * m) := by ring
      _ ≤ relayOdds N i T β 0 * relayCost N i T β 0 m * δ :=
          mul_le_mul_of_nonneg_left hδ (mul_nonneg ho0 hκ)
  calc relayOdds N i T β m = Real.sqrt (relayOdds N i T β m ^ 2) :=
        (Real.sqrt_sq (relayOdds_nonneg hβ m)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h2

/-- **The downward step with the anchor bounded**: `o(m) ≤ √((N³ − 1) · κ(0,m) · δ)`. DERIVED: `3`, `1`, `2`. -/
theorem relayOdds_down_sector (hβ : 0 ≤ β) (m : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : relayOdds N i T β (2 * m) ≤ δ) :
    relayOdds N i T β m ≤ Real.sqrt (((N : ℝ) ^ 3 - 1) * relayCost N i T β 0 m * δ) := by
  refine (relayOdds_down hβ m hδ).trans (Real.sqrt_le_sqrt ?_)
  have hκ : 0 ≤ relayCost N i T β 0 m := le_trans zero_le_one (relayCost_ge_one hβ 0 m)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (relayOdds_le_card hβ 0) hκ) hδ0

/-- **The zero-flux defect along the chain**: `relayDefect j = 2 log Z₀(j) − log Z₀(2j + 1)`.
DERIVED: `2`, `1` the doubled chain. -/
theorem relayDefect_eq (hβ : 0 ≤ β) (j : ℕ) :
    relayDefect N i T β j = 2 * Real.log (relayZ0 N i T β j) - Real.log (relayZ0 N i T β (2 * j + 1)) := by
  unfold relayDefect dd relayZ0
  rw [← zk_conv (bdd_iterK hβ j) centreAction (fun g x y => iter_act β j g x y),
    ← iter_add (bdd_kT (NeZero.ne N) hβ) j j]
  have e : 2 * j + 1 = j + j + 1 := by ring
  rw [e]

/-- **The zero-flux defect is anchored**: `relayDefect j ≤ log Z₀(0) + log Z₀(2j) − log Z₀(2j + 1)`.
DERIVED: `2`, `0` the anchor. -/
theorem relayDefect_le_anchor (hβ : 0 ≤ β) (j : ℕ) :
    relayDefect N i T β j
      ≤ Real.log (relayZ0 N i T β 0) + Real.log (relayZ0 N i T β (2 * j))
        - Real.log (relayZ0 N i T β (2 * j + 1)) := by
  rw [relayDefect_eq hβ j]
  have h := relayZ0_sq_le (N := N) (i := i) (T := T) hβ 0 j
  simp only [zero_add] at h
  have hj := relayZ0_pos (N := N) (i := i) (T := T) hβ j
  have h0 := relayZ0_pos (N := N) (i := i) (T := T) hβ 0
  have h2 := relayZ0_pos (N := N) (i := i) (T := T) hβ (2 * j)
  have hl := Real.log_le_log (pow_pos hj 2) h
  rw [Real.log_pow, Real.log_mul h0.ne' h2.ne'] at hl
  push_cast at hl
  linarith

end Facts

/-! ## 5. The degenerate coupling -/

omit [NeZero N] in
/-- At `β = 0` the hop is the constant `1`. DERIVED: `0`, `1`. -/
theorem kT_zero (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) : kT i T N 0 = fun _ _ => 1 := by
  funext V V'
  simp [kT, gk]

omit [NeZero N] in
/-- The relayed constant `1` is `1`. DERIVED: `1`. -/
theorem iter_one (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) :
    ∀ j, iter (hS i T N) (fun _ _ => (1 : ℝ)) j = fun _ _ => 1
  | 0 => rfl
  | j + 1 => by
    show conv (hS i T N) (fun _ _ => (1 : ℝ)) (iter (hS i T N) (fun _ _ => (1 : ℝ)) j) = _
    rw [iter_one i T j]
    funext x z
    simp [conv]

/-- **At `β = 0` every chain read has flux odds `0`.** DERIVED: `0`. -/
theorem relayOdds_zero_coupling (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (j : ℕ) :
    relayOdds N i T 0 j = 0 := by
  have hz : zk (fun _ _ => (1 : ℝ)) (act (μ := i) (T := T) (N := N)) = fun _ _ => 1 := by
    funext x y
    simp only [zk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (card_pos_real (G := Cen i N)).ne'
  unfold relayOdds relayZ relayZ0
  rw [kT_zero, iter_one, hz, sub_self, zero_div]

/-! ## 6. Fixed aperture, any chain length, on the Wilson family -/

omit [NeZero N] in
/-- **A torus for every chain at a fixed aperture**: for every aperture `T` with positive extents and every `j`,
some extents `L` have time extent `2j + 2` along `i` and transverse extents `T`. DERIVED: `2j + 2` the time
extent of `j + 1` hops each way. -/
theorem exists_relayTorus (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (hT : ∀ k, 0 < T k) (j : ℕ) :
    ∃ L : Fin 4 → ℕ, L i = j + 1 + j + 1 ∧ (∀ k, 0 < L k) ∧ tr L i = T := by
  refine ⟨fun k => if h : k = i then j + 1 + j + 1 else T ⟨k, h⟩, ?_, fun k => ?_, ?_⟩
  · show (if h : i = i then j + 1 + j + 1 else T ⟨i, h⟩) = _
    rw [dif_pos rfl]
  · show 0 < (if h : k = i then j + 1 + j + 1 else T ⟨k, h⟩)
    split_ifs with h
    · omega
    · exact hT _
  · funext k
    show (if h : k.1 = i then j + 1 + j + 1 else T ⟨k.1, h⟩) = T k
    rw [dif_neg k.2]

omit [NeZero N] in
/-- **The relay read at a fixed aperture is a Wilson two-slice law at every chain length**: the rectangular
Wilson torus with aperture `T` and time extent `2j + 2` reads the slice pair at distance `j + 1` with density
`a²/hs(a)`, `a = iter K j`. DERIVED: `j + 1` the half time extent. -/
theorem relayTorus_twoSlice (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ)
    (hT : ∀ k, 0 < T k) (j : ℕ) :
    ∃ L : Fin 4 → ℕ, L i = j + 1 + j + 1 ∧ (∀ k, 0 < L k) ∧ ∃ _ : tr L i = T,
      ∀ h : C(RectTorusState.SlR i T N × RectTorusState.SlR i T N, ℝ),
        RectTorusState.rectState hN L β (RectTorusState.pairObsR i T (j + 1) h)
          = FluxDuality.pairExp (hS i T N) (iter (hS i T N) (kT i T N β) j) ⇑h := by
  obtain ⟨L, hL, hpos, e⟩ := exists_relayTorus i T hT j
  refine ⟨L, hL, hpos, e, ?_⟩
  subst e
  intro h
  exact RectTorusState.rectState_pairObs hN hβ j hL hpos h

omit [NeZero N] in
/-- **The corner aperture scales with the side**: `Tr (2^l n) i = 2^l · Tr n i`. DERIVED: `2` the doubling base. -/
theorem Tr_two_pow_mul (l n : ℕ) (i : Fin 4) :
    CentreSectorSeed.Tr (2 ^ l * n) i = fun k => 2 ^ l * CentreSectorSeed.Tr n i k := by
  funext k
  show 2 ^ (CentreSectorSeed.pathV i k.1) * (2 ^ l * n) = 2 ^ l * (2 ^ (CentreSectorSeed.pathV i k.1) * n)
  ring

omit [NeZero N] in
/-- Every corner aperture extent is at least the side. DERIVED: `1`, `2`. -/
theorem le_Tr (n : ℕ) (i : Fin 4) (k : {k : Fin 4 // k ≠ i}) : n ≤ CentreSectorSeed.Tr n i k := by
  show n ≤ 2 ^ (CentreSectorSeed.pathV i k.1) * n
  calc n = 1 * n := (one_mul n).symm
    _ ≤ 2 ^ (CentreSectorSeed.pathV i k.1) * n := Nat.mul_le_mul_right n Nat.one_le_two_pow

/-! ## 7. The across-aperture step -/

/-- **Iterating the exchange**: if at one coupling, for every aperture in a class closed under doubling and every
chain index in a class `R` closed upward, `o(2T, j) ≤ c · o(T, 2j + 1)`, then for `j` in `R` `o(2^l T, j) ≤ c^l · o(T, 2^l (j + 1) − 1)`. DERIVED: `2` the doubling;
`1` the hop. -/
theorem odds_doubling_iter {β c : ℝ} (hc : 0 ≤ c) {Q : ∀ i : Fin 4, ({k : Fin 4 // k ≠ i} → ℕ) → Prop}
    (hQ2 : ∀ i T, Q i T → Q i (fun k => 2 * T k)) {R : ℕ → Prop} (hR : ∀ j j', j ≤ j' → R j → R j')
    (H : ∀ i T, Q i T → ∀ j, R j →
      relayOdds N i (fun k => 2 * T k) β j ≤ c * relayOdds N i T β (2 * j + 1)) :
    ∀ l i T, Q i T → ∀ j, R j →
      relayOdds N i (fun k => 2 ^ l * T k) β j ≤ c ^ l * relayOdds N i T β (2 ^ l * (j + 1) - 1) := by
  intro l
  induction l with
  | zero =>
    intro i T _ j _
    simp only [pow_zero, one_mul, Nat.add_sub_cancel]
    exact le_rfl
  | succ l ih =>
    intro i T hQ j hRj
    have e : (fun k => 2 ^ (l + 1) * T k) = fun k => 2 ^ l * (fun k => 2 * T k) k := by
      funext k; ring
    rw [e]
    have h1 := ih i (fun k => 2 * T k) (hQ2 i T hQ) j hRj
    set P := 2 ^ l * (j + 1) with hP
    have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hjP : j + 1 ≤ P := by
      rw [hP]; exact Nat.le_mul_of_pos_left (j + 1) (Nat.two_pow_pos l)
    have h2 := H i T hQ (P - 1) (hR j (P - 1) (by omega) hRj)
    have e2 : 2 * (P - 1) + 1 = 2 ^ (l + 1) * (j + 1) - 1 := by
      have : 2 ^ (l + 1) * (j + 1) = 2 * P := by rw [hP, pow_succ]; ring
      rw [this]; omega
    rw [e2] at h2
    calc relayOdds N i (fun k => 2 ^ l * (fun k => 2 * T k) k) β j
        ≤ c ^ l * relayOdds N i (fun k => 2 * T k) β (P - 1) := h1
      _ ≤ c ^ l * (c * relayOdds N i T β (2 ^ (l + 1) * (j + 1) - 1)) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hc l)
      _ = c ^ (l + 1) * relayOdds N i T β (2 ^ (l + 1) * (j + 1) - 1) := by ring

/-- **The cubic flux share under the exchange**: at side `2^l n` it is at most `c^l` times the relay odds at the
base aperture `Tr n i` over chain index `4^l (n/2) − 1`. DERIVED: `2` the side doubling and halving; `4 = 2²`;
`1` the hop. -/
theorem fluxShareN_le_of_exchange {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c)
    {Q : ∀ i : Fin 4, ({k : Fin 4 // k ≠ i} → ℕ) → Prop}
    (hQ2 : ∀ i T, Q i T → Q i (fun k => 2 * T k)) {R : ℕ → Prop} (hR : ∀ j j', j ≤ j' → R j → R j')
    (H : ∀ i T, Q i T → ∀ j, R j →
      relayOdds N i (fun k => 2 * T k) β j ≤ c * relayOdds N i T β (2 * j + 1))
    {n : ℕ} (hn : 2 ≤ n) (he : Even n) (i : Fin 4) (hQn : Q i (CentreSectorSeed.Tr n i))
    (hRn : R (n / 2 - 1)) (l : ℕ) :
    fluxShareN N β (2 ^ l * n) i
      ≤ c ^ l * relayOdds N i (CentreSectorSeed.Tr n i) β (4 ^ l * (n / 2) - 1) := by
  obtain ⟨p, rfl⟩ := he
  have hp : 1 ≤ p := by omega
  have hhalf : 2 ^ l * (p + p) / 2 = 2 ^ l * p := by
    rw [show 2 ^ l * (p + p) = 2 * (2 ^ l * p) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hpp : (p + p) / 2 = p := by omega
  have hP1 : 1 ≤ 2 ^ l * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [fluxShareN_eq_relay, Tr_two_pow_mul, hhalf, hpp]
  refine (relayShare_le_odds hβ _).trans ?_
  rw [hpp] at hRn
  have hpl : p ≤ 2 ^ l * p := Nat.le_mul_of_pos_left p (Nat.two_pow_pos l)
  have h := odds_doubling_iter hc hQ2 hR H l i (CentreSectorSeed.Tr (p + p) i) hQn (2 ^ l * p - 1)
    (hR (p - 1) (2 ^ l * p - 1) (by omega) hRn)
  have e : 2 ^ l * (2 ^ l * p - 1 + 1) - 1 = 4 ^ l * p - 1 := by
    rw [Nat.sub_add_cancel hP1, ← mul_assoc, ← mul_pow]
    norm_num
  rw [e] at h
  exact h

variable (N) in
/-- **The coarse observer reads the fine one** (assumed). There are `c ≥ 1` and `C₀ > 0` such that, eventually
in `β`, the unit locks and at every aperture whose extents are all at least `C₀/m′`, over every chain whose
coarse time extent `2(j + 1)` is at least `C₀/m′`, the flux odds over `j` hops at the doubled aperture are at
most `c` times the flux odds over `2j + 1` hops at the aperture: `o(2T, j) ≤ c · o(T, 2j + 1)`. DERIVED: `2` the
aperture doubling, the relayed chain `2j + 1` and the time extent `2(j + 1)`; `1` the least `c` and the hop;
`0` the threshold of the eventual coupling. -/
def CoarseReadsFine (hN : N ≠ 0) : Prop :=
  ∃ c C₀ : ℝ, 1 ≤ c ∧ 0 < C₀ ∧ ∀ᶠ β in atTop, 0 < measMassOf (periodicState hN β) tensorEnergy ∧
    ∀ (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ),
      (∀ k, ENNReal.ofReal C₀ ≤ (T k : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy) →
      ∀ j : ℕ, ENNReal.ofReal C₀
          ≤ ((2 * (j + 1) : ℕ) : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy →
        relayOdds N i (fun k => 2 * T k) β j ≤ c * relayOdds N i T β (2 * j + 1)

/-- **The exchange holds at the degenerate coupling**: at `β = 0` both sides are `0`. DERIVED: `0`, `2`, `1`. -/
theorem exchange_zero_coupling (c : ℝ) (i : Fin 4) (T : {k : Fin 4 // k ≠ i} → ℕ) (j : ℕ) :
    relayOdds N i (fun k => 2 * T k) 0 j ≤ c * relayOdds N i T 0 (2 * j + 1) := by
  rw [relayOdds_zero_coupling, relayOdds_zero_coupling, mul_zero]

/-- **The across-aperture step reduces the flux clause to a fixed-aperture read**: under `CoarseReadsFine`,
eventually in `β`, at every even side `n ≥ 2` with `C₀ ≤ n m′`, every step `i` and every `l`, the cubic flux share
at side `2^l n` is at most `c^l` times the relay odds at the base aperture `Tr n i` over chain index
`4^l (n/2) − 1`. DERIVED: `2`, `4 = 2²`, `1` as in `fluxShareN_le_of_exchange`; `0` the coupling threshold. -/
theorem fluxShareN_le_of_coarseReadsFine (hN : N ≠ 0) (h : CoarseReadsFine N hN) :
    ∃ c C₀ : ℝ, 1 ≤ c ∧ 0 < C₀ ∧ ∀ᶠ β in atTop, ∀ n : ℕ, 2 ≤ n → Even n →
      ENNReal.ofReal C₀ ≤ (n : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy →
      ∀ (i : Fin 4) (l : ℕ), fluxShareN N β (2 ^ l * n) i
        ≤ c ^ l * relayOdds N i (CentreSectorSeed.Tr n i) β (4 ^ l * (n / 2) - 1) := by
  obtain ⟨c, C₀, hc, hC₀, hev⟩ := h
  refine ⟨c, C₀, hc, hC₀, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β ⟨_, hH⟩ hβ n hn he hnm i l
  set m := measMassOf (periodicState hN β) tensorEnergy
  let Q : ∀ i : Fin 4, ({k : Fin 4 // k ≠ i} → ℕ) → Prop :=
    fun _ T => ∀ k, ENNReal.ofReal C₀ ≤ (T k : ℝ≥0∞) * m
  have hQ2 : ∀ i T, Q i T → Q i (fun k => 2 * T k) := by
    intro i T hT k
    refine (hT k).trans (mul_le_mul_left ?_ m)
    exact_mod_cast Nat.le_mul_of_pos_left (T k) (by norm_num)
  have hQn : Q i (CentreSectorSeed.Tr n i) := fun k =>
    hnm.trans (mul_le_mul_left (by exact_mod_cast le_Tr n i k) m)
  let R : ℕ → Prop := fun j => ENNReal.ofReal C₀ ≤ ((2 * (j + 1) : ℕ) : ℝ≥0∞) * m
  have hR : ∀ j j', j ≤ j' → R j → R j' := by
    intro j j' hjj' hj
    refine hj.trans (mul_le_mul_left ?_ m)
    exact_mod_cast (show 2 * (j + 1) ≤ 2 * (j' + 1) by omega)
  have hRn : R (n / 2 - 1) := by
    have e : 2 * (n / 2 - 1 + 1) = n := by obtain ⟨p, rfl⟩ := he; omega
    show ENNReal.ofReal C₀ ≤ ((2 * (n / 2 - 1 + 1) : ℕ) : ℝ≥0∞) * m
    rw [e]; exact hnm
  exact fluxShareN_le_of_exchange hβ (by linarith) hQ2 hR (fun i T hT j hj => hH i T hT j hj) hn he i hQn
    hRn l

end Lattice

end MassGap.RelayChain

end

#print axioms MassGap.RelayChain.kpair_conv_shift
#print axioms MassGap.RelayChain.kpair_sq_le
#print axioms MassGap.RelayChain.kpair_family
#print axioms MassGap.RelayChain.hs_family_sq_le
#print axioms MassGap.RelayChain.zk_conv_right
#print axioms MassGap.RelayChain.fk_conv_right
#print axioms MassGap.RelayChain.hs_fk
#print axioms MassGap.RelayChain.down_not_contracting
#print axioms MassGap.RelayChain.no_downward_from_traces
#print axioms MassGap.RelayChain.fluxShareN_eq_relay
#print axioms MassGap.RelayChain.trivialDefectN_eq_relay
#print axioms MassGap.RelayChain.relayOdds_le_card
#print axioms MassGap.RelayChain.relayShare_eq_mean
#print axioms MassGap.RelayChain.relayZ_sq_le
#print axioms MassGap.RelayChain.relayZ0_sq_le
#print axioms MassGap.RelayChain.relayFlux_sq_le
#print axioms MassGap.RelayChain.relayCost_ge_one
#print axioms MassGap.RelayChain.relayOdds_mid
#print axioms MassGap.RelayChain.relayOdds_down
#print axioms MassGap.RelayChain.relayOdds_down_sector
#print axioms MassGap.RelayChain.relayDefect_eq
#print axioms MassGap.RelayChain.relayDefect_le_anchor
#print axioms MassGap.RelayChain.relayOdds_zero_coupling
#print axioms MassGap.RelayChain.relayTorus_twoSlice
#print axioms MassGap.RelayChain.Tr_two_pow_mul
#print axioms MassGap.RelayChain.odds_doubling_iter
#print axioms MassGap.RelayChain.fluxShareN_le_of_exchange
#print axioms MassGap.RelayChain.exchange_zero_coupling
#print axioms MassGap.RelayChain.fluxShareN_le_of_coarseReadsFine
