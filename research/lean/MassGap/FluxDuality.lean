import Mathlib
import MassGap.SubstrateFluxRead
import MassGap.SliceKernelPower

/-!
# MassGap.FluxDuality — the two sector clauses as readings of the capture's two-slice law

`SubstrateFluxRead.SectorSeedMeasured` carries two sector clauses at each corner step `i` and side `n`:
`CentreSectorSeedN.fluxShareN N β n i ≤ 1/80000` and `CentreSectorSeedN.trivialDefectN N β n i ≤ 1/80000`. Both are
written through the transfer kernel, which carries `β`. This module writes both as readings of the capture: the
observer is given a state `ν` on configurations and reads, from `ν` alone, expectations of continuous functions of
two slices. Declarations are in the namespace `MassGap.FluxDuality`.

## 1. What `fluxShareN` is

On the slice transverse to `i` (spatial links `V`, extents `Tr n i`, product Haar `hSN N n i`) let
`a = halfKN N β n i = kT^{∗(n/2)}`, the transfer over half the time extent `n`, and `A = hs(a) = ∫∫ a(x,y)²`, the trace
of the transfer over the whole extent (even `n`; `GapSideTwistBridge.hs_halfKN_eq`). The centre `Z_N³` acts on a slice by `SliceCentreAction.act`: `g` multiplies
the links of direction `ν` whose `ν`-coordinate is `0` by `e(g_ν)`. The zero-flux kernel is
`zk a act = N⁻³ Σ_g a(·, g·)`, and

    fluxShareN = (hs(a) − hs(zk a act)) / hs(a) = 1 − N⁻³ Σ_g Z_g / Z,   Z_g = ∫∫ a(x,y) a(x, g y),

the share of the trace carried by non-zero electric flux (`CentreSectorSeedN.fluxShareN_eq_mean`). `Z_g` is the
partition function with the centre twist `g` inserted at one time slice (`GapSideTwistBridge.twist_halfKN_eq`).

## 2. The two-slice law (defined; the identification with the torus state proved at step `0`, at steps `1–3` in `RectTorusState`)

Let `p(x, y) = a(x, y)² / A` on slice pairs. Under the Wilson measure of the torus of extent `n` along `i`, the
spatial links at time `0` and at time `n/2` have joint density `p` against product Haar: integrating the other
`n − 2` slices leaves `a(x, y) a(y, x) / Z`, and `a` is symmetric. This is the transfer representation of
`RectTransfer.ZR_eq_cyc` with an observable of the two slices inserted. At step `0` it is proved for
`PeriodicState.torusState hN (n − 1) β` (`MassGap.TwoSliceBridge.twoSliceLaw_torusState`, downstream of this
module); at steps `1–3` the torus is rectangular and it is proved for `RectTorusState.rectState`
(`twoSliceLaw_rectState`), downstream.

* **`slicePair n i`**: the continuous map `Cfg N → Slice × Slice` reading the spatial links of step `i` at times
  `0` and `n/2` (`siteOf`, `readSlice`).
* **`TwoSliceLaw ν β n i`** (the bridge; proved for `torusState hN (n − 1) β` at step `0`, assumed for the captures and at steps `1–3`): for every continuous `h` on slice pairs,
  `ν (h ∘ slicePair n i) = pairExp h = (∫∫ a² h) / A`. The reads below never use it; only the transfer from a read
  to the kernel clause of `SectorSeedMeasured` does.

## 3. One minus the flux share is a Hellinger affinity of the two-slice law (proved)

For a test `f > 0` on slice pairs and `g ∈ Z_N³`, the affinity read is

    affRead g f = ( E[f(x, y)] + E[f(x, g y)⁻¹] ) / 2,

an expectation under the two-slice law, and `meanAff f = N⁻³ Σ_g affRead g (f g)`.

* `le_affRead`: `Z_{−g}/Z ≤ affRead g f` for every test (arithmetic–geometric mean,
  `2uv ≤ u²t + v²/t`, after moving the shift `g` onto the second slice by Haar invariance).
* `affRead_opt`: at `f = opt g = a(x, (−g) y) / a(x, y)` the read is `(Z_{−g} + Z_g) / (2Z)`.
* **`isLeast_meanAff`** (generic) and **`fluxShareN_isLeast`** (lattice): `1 − fluxShareN N β n i` is the least
  value of `meanAff` over measurable tests bounded between two positive constants, and it is attained. With `p` the
  two-slice density this is `N⁻³ Σ_g ∫∫ √(p(x,y) p(x, g y))`: the flux share is the mean squared Hellinger distance
  (with the convention `H² = 1 − BC`) between the two-slice law and its image under a relative centre twist of the
  two slices. No `β` appears in the capture read `FluxReadOf` (`meanAff` of `halfKN` does contain `β`).

## 4. The clauses in capture form (proved, given the bridge)

* **`FluxReadOf ν n i ε`**: for every family of positive continuous tests `f g` on slice pairs,
  `1 − ε ≤ N⁻³ Σ_g (ν(f g ∘ slicePair) + ν((f g ∘ (id × g))⁻¹ ∘ slicePair)) / 2`. A Prop over `ν`; it reads `ν` on
  continuous functions of two slices and nothing else.
* **`fluxReadOf_iff`**: under `TwoSliceLaw ν β n i` (`β ≥ 0`), `FluxReadOf ν n i ε ↔ fluxShareN N β n i ≤ ε`.
* **`DefectReadOf ν n i ε`**: the two-slice law of `ν` has a continuous density `ρ ≥ 0` against product Haar
  (`ν (h ∘ slicePair) = ∫∫ ρ h` for continuous `h`; unique by `density_unique`) and `dd(zk(√ρ)) ≤ ε`. A Prop over
  `ν`.
* `dd_root`: `dd(zk(√p)) = dd(zk a)`: the doubling defect is unchanged by the scale `√A`, and `√p = a/√A`.
  `density_unique`: a continuous density is unique (Haar charges every open set). **`defectReadOf_iff`**: under
  `TwoSliceLaw`, `DefectReadOf ν n i ε ↔ trivialDefectN N β n i ≤ ε`. So the zero-flux clause is also a reading of
  the two-slice law: its doubled trace `hs(zk ∗ zk)` is computed from `p` by integration, without a second capture.
* **`SectorSeedRead hN cap`** (assumed): `SectorSeedMeasured` with the side tied to the measured period of the step-`0`
  capture (`measPeriod (cap β n 0) = n`) and both clauses written as `FluxReadOf` and `DefectReadOf` of the
  captures `cap β n i`. `FluxReadMeasured ν ε`: the step-`0` flux read at the side `measPeriod ν`.
* **`sectorSeedMeasured_of_read`** (proved): `CapturesReadTorus cap → SectorSeedRead hN cap → SectorSeedMeasured hN`
  (`CapturesReadTorus`, assumed here; discharged for the Wilson family by `RectTorusState.capturesReadTorus_capR`: `TwoSliceLaw` at every `β ≥ 0` and even side `n ≥ 2`), and
  **`runSeed_of_sectorSeedRead`** adds `UnitTracksRun` to reach `WDeltaRun.RunSeed N`.
  `sectorSeedRead_of_measured`: conversely, given the bridge and the period tie, `SectorSeedMeasured` gives
  `SectorSeedRead`.

## 5. Which input still reads `β`

Neither clause does: both are readings of the two-slice law of the capture. What carries `β` is the bridge
`CapturesReadTorus cap`: that the capture at `(β, n, i)` has the two-slice law of the Wilson torus of extents
`ext n (pathV i)` at coupling `β`. For `i = 0` that torus is `torusState hN (n − 1) β`, and the bridge holds for it
(`TwoSliceBridge.twoSliceLaw_torusState`); for `i = 1, 2, 3` it is
the rectangular state `RectTorusState.rectState`, and the bridge holds there too (`twoSliceLaw_rectState`). The bridge is an identification of the capture with
the substrate, not a reading of it; with it, each clause is equivalent to the kernel clause (`fluxReadOf_iff`,
`defectReadOf_iff`), so the reads restate the clauses in capture coordinates and discharge neither. This places the
`β`-dependence of the two sector clauses in one named identification of the captures with the substrate; `β` still
indexes the family `cap β` and the unit channel `periodicState hN β`. Without the bridge `SectorSeedRead` says nothing
about the Wilson substrate: the product-Haar torus family of `β = 0` satisfies both reads at every side, so the bridge
carries the identity of the capture, not only `β`.

## 6. Tests

* Non-vacuity (proved): `capState` builds a state from any continuous probability density on slice pairs
  (`embedPair` places the two slices into a configuration, `slicePair_embed`). `capTorus hβ n i` is a state whose
  two-slice law has density `a²/A` (the torus's: proved at step `0` in `TwoSliceBridge`, at steps `1–3` in `RectTorusState`), `twoSliceLaw_capTorus` proves the bridge for
  it, and `capturesReadTorus_capFamily` shows the bridge hypothesis is satisfiable for a whole family. `capTorus` is not
  periodic (links outside the box are `1`), so `measPeriod (capTorus hβ n 0)` is not `n` and `capFamily` does not
  witness `SectorSeedRead`. **`reads_strong`** and
  **`eventually_reads_strong`**: at `0 ≤ β ≤ 2^{-16}`, at every large even side, both reads hold at `1/80000` on
  `capTorus` (`SubstrateFluxRead.sectors_strong`). The witness carries the kernel's two-slice law `a²/A`, not a degenerate one; it is built from that law, so it
shows the bridge is satisfiable. `torusState hN (n − 1) β` meets the bridge at step `0`
(`TwoSliceBridge.twoSliceLaw_torusState`), and `TwoSliceBridge.reads_strong_torus` and
`eventually_reads_strong_torus` are the step-`0` witness on the Wilson torus itself.
* Growing quantities (argued): the read is normalized, `1 − fluxShareN ∈ [N⁻³, 1]` (`hs_trivKN_ge`, `hs_trivKN_le`), the threshold
  `1/80000` and the group size `N³` are fixed before the side, and the tests are quantified universally; no count
  grows with `n`. At `β = 0` the kernel is the constant `1`, the two-slice law is product Haar, every affinity is `1`
  and both clauses hold with value `0` (argued): the free theory satisfies the reads, as it should.
* Restatement against reduction: the reads are exactly equivalent to the kernel clauses under the bridge (both
  directions proved), so `SectorSeedRead` with `CapturesReadTorus` is `SectorSeedMeasured` with the period tie. It
  places the `β`-dependence of the clauses in one named identification of the captures with the substrate (`β` still
  indexes the family and the unit channel); it proves neither clause.
* The centre on the winding (argued): `act g` multiplies by `e(g_ν)` exactly the links of direction `ν` with
  `ν`-coordinate `0`, and a winding line of `T_ν` links in direction `ν` crosses that coordinate once, so the
  winding holonomy is multiplied by the central `e(g_ν)`. The relative twist `(x, y) ↦ (x, g y)` is therefore a
  relative centre rotation of the Polyakov holonomies of the two slices, and the affinity measures how far the
  two-slice law is from invariant under it. The read uses the full two-slice law, not only `tr P` correlators: a
  bound of the flux share by the `fluxCov` correlators alone would need the Polyakov operator to overlap every flux
  state, which is not true in general.

## 7. Parameters

| argument | where | status |
|---|---|---|
| `ν`, `cap β n i` (the captures) | every read | measured: the input |
| `n` (side) | `slicePair`, reads | measured at step 0: `measPeriod (cap β n 0) = n` in `SectorSeedRead`; steps 1–3 share it by index; `measPeriod ν` in `FluxReadMeasured`; an argument of `FluxReadOf` |
| `n / 2` (slice separation) | `slicePair` | measured: half the side |
| `i` (corner step) | reads | chosen: swept over all four |
| `g ∈ Z_N³` | `FluxReadOf` | chosen: swept over the group |
| `f` (tests) | `FluxReadOf` | chosen: swept over all positive continuous families |
| `ρ` (two-slice density) | `DefectReadOf` | measured: existential, unique when it exists (`density_unique`) |
| `hSN N n i` (product Haar) | `DefectReadOf`, `pairExp` | shared: the reference measure of the configuration space |
| `N` (colour count) | the type | shared |
| `β` (coupling) | `TwoSliceLaw`, `CapturesReadTorus`, `capTorus`; the index of `cap β` and the unit channel `periodicState hN β` in `SectorSeedRead` | shared: in the substrate, the bridge and the unit channel; neither sector read uses it |
| `1/80000` | `SectorSeedRead` | chosen: the threshold of `defectW_le_of_sectorsN` |
| `C`, `m'` | `SectorSeedRead` | measured: as in `SectorSeedMeasured` |
| `aRun`, `c₁` | `UnitTracksRun` only | shared: supplied spacing, met only to reach `RunSeed` |

DERIVED (module-wide): `0` the first slice and the identity of the centre; `2` the square in the density, the mean of
the two affinity terms and the least side; `n / 2` the half-time separation of `halfKN`; `N³ = |Z_N³|`
(`SliceCentreAction.card_cen`); `1/80000`, `65536`, `4 + N⁶`, `N³/2` the constants of `CentreSectorSeedN` and
`SubstrateFluxRead.sectors_strong`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.FluxDuality

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open MassGap.KernelPower (hs conv Bdd hs_nonneg)
open MassGap.ZeroFluxSector (zk hs_zk_eq_mean)
open MassGap.FluxSectorFourier (CentreAction)

/-! ## 1. The affinity read on a generic kernel -/

section Generic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {σ : G → X → X} {a : X → X → ℝ}

variable (μ) in
/-- **The two-slice expectation**: `E[h] = (∫∫ a² h) / hs(a)`, the law of density `a² / hs(a)`.
DERIVED: `2` the square. -/
def pairExp (a : X → X → ℝ) (h : X × X → ℝ) : ℝ := (∫ x, ∫ y, a x y ^ 2 * h (x, y) ∂μ ∂μ) / hs μ a

variable (μ) in
/-- **The affinity read** of a test `f` at a twist `g`: `(E[f] + E[(f ∘ (id × g))⁻¹]) / 2`.
DERIVED: `2` the mean of the two terms. -/
def affRead (a : X → X → ℝ) (σ : G → X → X) (g : G) (f : X × X → ℝ) : ℝ :=
  (pairExp μ a f + pairExp μ a (fun p => (f (p.1, σ g p.2))⁻¹)) / 2

variable (μ) in
/-- **The mean affinity read** over the group. DERIVED: no numeral. -/
def meanAff (a : X → X → ℝ) (σ : G → X → X) (f : G → X × X → ℝ) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, affRead μ a σ g (f g)

variable (μ) in
/-- **The flux share** of a kernel: `(hs(a) − hs(zk a)) / hs(a)`. DERIVED: no numeral. -/
def share (a : X → X → ℝ) (σ : G → X → X) : ℝ := (hs μ a - hs μ (zk a σ)) / hs μ a

/-- **A test**: measurable, bounded, bounded below by a positive constant. DERIVED: `0` the threshold. -/
def Test (f : X × X → ℝ) : Prop := Measurable f ∧ ∃ c C : ℝ, 0 < c ∧ ∀ p, c ≤ f p ∧ f p ≤ C

/-- **The optimal test** at `g`: `a(x, (−g) y) / a(x, y)`. DERIVED: no numeral. -/
def opt (a : X → X → ℝ) (σ : G → X → X) (g : G) : X × X → ℝ := fun p => a p.1 (σ (-g) p.2) / a p.1 p.2

omit [IsProbabilityMeasure μ] [Fintype G] [DecidableEq G] in
/-- DERIVED: `0` the identity of the group. -/
theorem act_neg_act (hA : CentreAction μ σ) (g : G) (y : X) : σ (-g) (σ g y) = y := by
  rw [← hA.add, neg_add_cancel, hA.zero]

/-- **Arithmetic–geometric mean**: `2uv ≤ u²t + v²/t` for `t > 0`. DERIVED: `2` the square. -/
theorem amgm {u v t : ℝ} (ht : 0 < t) : 2 * (u * v) ≤ u ^ 2 * t + v ^ 2 * t⁻¹ := by
  have hts : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have e : u ^ 2 * t + v ^ 2 * t⁻¹ - 2 * (u * v) = (u * t - v) ^ 2 * t⁻¹ := by
    linear_combination (2 * u * v - u ^ 2 * t) * hts
  nlinarith [mul_nonneg (sq_nonneg (u * t - v)) (inv_nonneg.mpr ht.le)]

/-- **Every test reads at least the reversed twisted ratio**: `Z_{−g}/Z ≤ affRead g f`. DERIVED: `0`, `2`. -/
theorem le_affRead (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y) (hA : CentreAction μ σ) (hpos : 0 < hs μ a)
    {f : X × X → ℝ} (hf : Test f) (g : G) :
    FluxSectorBound.twist μ a (σ (-g)) / hs μ a ≤ affRead μ a σ g f := by
  obtain ⟨hm, c, C, hc, hb⟩ := hf
  obtain ⟨Ca, hCa⟩ := ha.bdd
  have hfpos : ∀ p, 0 < f p := fun p => hc.trans_le (hb p).1
  have hmf : Measurable fun p : X × X => f (p.1, p.2) := hm.comp (measurable_fst.prodMk measurable_snd)
  have hma' : Measurable fun p : X × X => a p.1 (σ (-g) p.2) :=
    ha.meas.comp (measurable_fst.prodMk ((hA.meas (-g)).comp measurable_snd))
  have b1 : Bdd fun x y => a x y ^ 2 * f (x, y) :=
    ⟨(ha.meas.pow_const 2).mul hmf, Ca ^ 2 * C, fun x y => by
      rw [abs_mul, abs_pow, abs_of_pos (hfpos _)]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hCa x y) 2) (hb _).2 (hfpos _).le (sq_nonneg _)⟩
  have b2 : Bdd fun x y => a x (σ (-g) y) ^ 2 * (f (x, y))⁻¹ :=
    ⟨(hma'.pow_const 2).mul hmf.inv, Ca ^ 2 * c⁻¹, fun x y => by
      rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr (hfpos _))]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hCa _ _) 2) (inv_anti₀ hc (hb _).1)
        (inv_pos.mpr (hfpos _)).le (sq_nonneg _)⟩
  have hI2 : ∫ x, ∫ y, a x y ^ 2 * (f (x, σ g y))⁻¹ ∂μ ∂μ
      = ∫ x, ∫ y, a x (σ (-g) y) ^ 2 * (f (x, y))⁻¹ ∂μ ∂μ := by
    congr 1; funext x
    rw [← hA.integral_comp g (fun y => a x (σ (-g) y) ^ 2 * (f (x, y))⁻¹)]
    simp only [act_neg_act hA]
  have hsum : 2 * FluxSectorBound.twist μ a (σ (-g))
      ≤ (∫ x, ∫ y, a x y ^ 2 * f (x, y) ∂μ ∂μ) + ∫ x, ∫ y, a x (σ (-g) y) ^ 2 * (f (x, y))⁻¹ ∂μ ∂μ := by
    unfold FluxSectorBound.twist
    rw [← integral_const_mul, ← integral_add (SectorDefect.int_row (μ := μ) b1)
      (SectorDefect.int_row (μ := μ) b2)]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_)
      ((SectorDefect.int_row (μ := μ) b1).add (SectorDefect.int_row (μ := μ) b2))
      (Eventually.of_forall fun x => ?_)
    · exact mul_nonneg zero_le_two (integral_nonneg fun y => mul_nonneg (ha0 _ _) (ha0 _ _))
    · dsimp only
      rw [← integral_const_mul, ← integral_add (FluxSectorBound.irow (μ := μ) b1 x)
        (FluxSectorBound.irow (μ := μ) b2 x)]
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => ?_)
        ((FluxSectorBound.irow (μ := μ) b1 x).add (FluxSectorBound.irow (μ := μ) b2 x))
        (Eventually.of_forall fun y => ?_)
      · exact mul_nonneg zero_le_two (mul_nonneg (ha0 _ _) (ha0 _ _))
      · exact amgm (hfpos _)
  unfold affRead pairExp
  dsimp only
  rw [hI2]
  generalize FluxSectorBound.twist μ a (σ (-g)) = t at hsum ⊢
  generalize (∫ x, ∫ y, a x y ^ 2 * f (x, y) ∂μ ∂μ) = P at hsum ⊢
  generalize (∫ x, ∫ y, a x (σ (-g) y) ^ 2 * (f (x, y))⁻¹ ∂μ ∂μ) = Q at hsum ⊢
  have e : (P / hs μ a + Q / hs μ a) / 2 = (P + Q) / 2 / hs μ a := by ring
  rw [e, div_le_div_iff_of_pos_right hpos]
  linarith

omit [IsProbabilityMeasure μ] [Fintype G] [DecidableEq G] in
/-- **The optimal test reads the twisted ratios**: `affRead g (opt g) = (Z_{−g}/Z + Z_g/Z) / 2`.
DERIVED: `2` the mean. -/
theorem affRead_opt (hA : CentreAction μ σ) (hlow : ∀ x y, 0 < a x y) (g : G) :
    affRead μ a σ g (opt a σ g)
      = (FluxSectorBound.twist μ a (σ (-g)) / hs μ a + FluxSectorBound.twist μ a (σ g) / hs μ a) / 2 := by
  unfold affRead pairExp opt
  dsimp only
  have h1 : ∫ x, ∫ y, a x y ^ 2 * (a x (σ (-g) y) / a x y) ∂μ ∂μ = FluxSectorBound.twist μ a (σ (-g)) := by
    unfold FluxSectorBound.twist; congr 1; funext x; congr 1; funext y
    have h0 := (hlow x y).ne'
    calc a x y ^ 2 * (a x (σ (-g) y) / a x y) = a x y * a x (σ (-g) y) * (a x y / a x y) := by ring
      _ = a x y * a x (σ (-g) y) := by rw [div_self h0, mul_one]
  have h2 : ∫ x, ∫ y, a x y ^ 2 * (a x (σ (-g) (σ g y)) / a x (σ g y))⁻¹ ∂μ ∂μ
      = FluxSectorBound.twist μ a (σ g) := by
    unfold FluxSectorBound.twist; congr 1; funext x; congr 1; funext y
    rw [act_neg_act hA, inv_div]
    have h0 := (hlow x y).ne'
    calc a x y ^ 2 * (a x (σ g y) / a x y) = a x y * a x (σ g y) * (a x y / a x y) := by ring
      _ = a x y * a x (σ g y) := by rw [div_self h0, mul_one]
  rw [h1, h2]

/-- **One minus the share is the mean twisted ratio.** DERIVED: `1`. -/
theorem one_sub_share (ha : Bdd a) (hA : CentreAction μ σ) (hpos : 0 < hs μ a) :
    1 - share μ a σ = (Fintype.card G : ℝ)⁻¹ * ∑ g, FluxSectorBound.twist μ a (σ g) / hs μ a := by
  unfold share
  rw [hs_zk_eq_mean ha hA, ← Finset.sum_div, sub_div, div_self hpos.ne']
  ring

/-- **The optimal tests read one minus the share.** DERIVED: `2` the mean. -/
theorem meanAff_opt (ha : Bdd a) (hA : CentreAction μ σ) (hlow : ∀ x y, 0 < a x y) (hpos : 0 < hs μ a) :
    meanAff μ a σ (opt a σ) = 1 - share μ a σ := by
  rw [one_sub_share ha hA hpos]
  unfold meanAff
  simp only [affRead_opt hA hlow]
  congr 1
  have h : ∑ g, FluxSectorBound.twist μ a (σ (-g)) / hs μ a
      = ∑ g, FluxSectorBound.twist μ a (σ g) / hs μ a :=
    Fintype.sum_equiv (Equiv.neg G) _ _ (fun _ => rfl)
  calc ∑ g, (FluxSectorBound.twist μ a (σ (-g)) / hs μ a + FluxSectorBound.twist μ a (σ g) / hs μ a) / 2
      = (∑ g, FluxSectorBound.twist μ a (σ (-g)) / hs μ a
          + ∑ g, FluxSectorBound.twist μ a (σ g) / hs μ a) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ g, FluxSectorBound.twist μ a (σ g) / hs μ a := by rw [h]; ring

/-- **Every family of tests reads at least one minus the share.** DERIVED: no numeral. -/
theorem one_sub_share_le (ha : Bdd a) (ha0 : ∀ x y, 0 ≤ a x y) (hA : CentreAction μ σ)
    (hpos : 0 < hs μ a) {f : G → X × X → ℝ} (hf : ∀ g, Test (f g)) :
    1 - share μ a σ ≤ meanAff μ a σ f := by
  rw [one_sub_share ha hA hpos]
  unfold meanAff
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have h : ∑ g, FluxSectorBound.twist μ a (σ (-g)) / hs μ a
      = ∑ g, FluxSectorBound.twist μ a (σ g) / hs μ a :=
    Fintype.sum_equiv (Equiv.neg G) _ _ (fun _ => rfl)
  rw [← h]
  exact Finset.sum_le_sum fun g _ => le_affRead ha ha0 hA hpos (hf g) g

omit [IsProbabilityMeasure μ] [Fintype G] [DecidableEq G] in
/-- **The optimal test is a test** when the kernel has a positive floor. DERIVED: `0`. -/
theorem test_opt (ha : Bdd a) (hA : CentreAction μ σ) {c0 : ℝ} (hc0 : 0 < c0) (hlow : ∀ x y, c0 ≤ a x y)
    (g : G) : Test (opt a σ g) := by
  obtain ⟨Ca, hCa⟩ := ha.bdd
  set C' := max Ca c0 with hC'def
  have hC' : 0 < C' := hc0.trans_le (le_max_right _ _)
  have hup : ∀ x y, a x y ≤ C' := fun x y => ((le_abs_self _).trans (hCa x y)).trans (le_max_left _ _)
  have hp : ∀ x y, 0 < a x y := fun x y => hc0.trans_le (hlow x y)
  refine ⟨(ha.meas.comp (measurable_fst.prodMk ((hA.meas (-g)).comp measurable_snd))).div ha.meas,
    c0 / C', C' / c0, div_pos hc0 hC', fun p => ⟨?_, ?_⟩⟩
  · show c0 / C' ≤ a p.1 (σ (-g) p.2) / a p.1 p.2
    rw [div_le_div_iff₀ hC' (hp _ _)]
    nlinarith [hlow p.1 (σ (-g) p.2), hup p.1 p.2, hp p.1 p.2]
  · show a p.1 (σ (-g) p.2) / a p.1 p.2 ≤ C' / c0
    rw [div_le_div_iff₀ (hp _ _) hc0]
    nlinarith [hup p.1 (σ (-g) p.2), hlow p.1 p.2, hp p.1 (σ (-g) p.2)]

/-- **The flux share as a least affinity**: `1 − share` is the least mean affinity read over tests, attained
at the optimal tests. DERIVED: no numeral. -/
theorem isLeast_meanAff (ha : Bdd a) (hA : CentreAction μ σ) {c0 : ℝ} (hc0 : 0 < c0)
    (hlow : ∀ x y, c0 ≤ a x y) (hpos : 0 < hs μ a) :
    IsLeast {r | ∃ f : G → X × X → ℝ, (∀ g, Test (f g)) ∧ meanAff μ a σ f = r} (1 - share μ a σ) := by
  have hp : ∀ x y, 0 < a x y := fun x y => hc0.trans_le (hlow x y)
  refine ⟨⟨opt a σ, fun g => test_opt ha hA hc0 hlow g, meanAff_opt ha hA hp hpos⟩, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact one_sub_share_le ha (fun x y => (hp x y).le) hA hpos hf

omit [IsProbabilityMeasure μ] in
/-- The two-slice expectation with the normalization inside. DERIVED: `2` the square. -/
theorem pairExp_eq (a : X → X → ℝ) (h : X × X → ℝ) :
    pairExp μ a h = ∫ x, ∫ y, a x y ^ 2 / hs μ a * h (x, y) ∂μ ∂μ := by
  unfold pairExp
  rw [← integral_div]
  congr 1; funext x
  rw [← integral_div]
  congr 1; funext y
  ring

/-! ## 2. The doubling defect is scale-free -/

omit [IsProbabilityMeasure μ] [DecidableEq G] in
/-- DERIVED: `2` the square. -/
theorem hs_const_mul (k : X → X → ℝ) (c : ℝ) : hs μ (fun x y => c * k x y) = c ^ 2 * hs μ k := by
  unfold hs
  simp_rw [mul_pow, integral_const_mul]

omit [IsProbabilityMeasure μ] [DecidableEq G] in
/-- DERIVED: `2` the square. -/
theorem conv_const_mul (k : X → X → ℝ) (c : ℝ) :
    conv μ (fun x y => c * k x y) (fun x y => c * k x y) = fun x z => c ^ 2 * conv μ k k x z := by
  funext x z
  unfold conv
  rw [← integral_const_mul]
  congr 1; funext y
  show c * k x y * (c * k y z) = c ^ 2 * (k x y * k y z)
  ring

omit [IsProbabilityMeasure μ] [DecidableEq G] in
/-- **The doubling defect does not see a scale.** DERIVED: `2` the square and the doubling. -/
theorem dd_const_mul (k : X → X → ℝ) {c : ℝ} (hc : c ≠ 0) (h1 : 0 < hs μ k)
    (h2 : 0 < hs μ (conv μ k k)) : SectorDefect.dd μ (fun x y => c * k x y) = SectorDefect.dd μ k := by
  unfold SectorDefect.dd
  rw [conv_const_mul, hs_const_mul k, hs_const_mul (conv μ k k)]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [Real.log_mul hc2 h1.ne', Real.log_mul (pow_ne_zero 2 hc2) h2.ne']
  simp only [Real.log_pow]
  push_cast
  ring

omit [MeasurableSpace X] [IsProbabilityMeasure μ] [AddCommGroup G] [DecidableEq G] in
/-- DERIVED: no numeral. -/
theorem zk_const_mul (k : X → X → ℝ) (c : ℝ) :
    zk (fun x y => c * k x y) σ = fun x y => c * zk k σ x y := by
  funext x y
  unfold zk
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

omit [IsProbabilityMeasure μ] [Fintype G] [DecidableEq G] in
/-- **The root of the two-slice density is the kernel over `√hs`.** DERIVED: `2` the square. -/
theorem sqrt_pairDensity (ha0 : ∀ x y, 0 ≤ a x y) (x y : X) :
    Real.sqrt (a x y ^ 2 / hs μ a) = (Real.sqrt (hs μ a))⁻¹ * a x y := by
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (ha0 x y), div_eq_inv_mul]

omit [IsProbabilityMeasure μ] [AddCommGroup G] [DecidableEq G] in
/-- **The zero-flux defect read from the root density**: `dd(zk(√p)) = dd(zk a)`, `p = a²/hs(a)`.
DERIVED: `2` the square. -/
theorem dd_root (ha0 : ∀ x y, 0 ≤ a x y) (hpos : 0 < hs μ a) (h1 : 0 < hs μ (zk a σ))
    (h2 : 0 < hs μ (conv μ (zk a σ) (zk a σ))) :
    SectorDefect.dd μ (zk (fun x y => Real.sqrt (a x y ^ 2 / hs μ a)) σ) = SectorDefect.dd μ (zk a σ) := by
  have e : (fun x y => Real.sqrt (a x y ^ 2 / hs μ a)) = fun x y => (Real.sqrt (hs μ a))⁻¹ * a x y := by
    funext x y; exact sqrt_pairDensity ha0 x y
  rw [e, zk_const_mul, dd_const_mul _ (inv_ne_zero (Real.sqrt_pos.mpr hpos).ne') h1 h2]

end Generic

/-! ## 3. The lattice: slices, captures and the two reads -/

section Lattice

open MassGap.RectWilson (SpT TT)
open MassGap.CentreSectorSeed (Tr)
open MassGap.CentreSectorSeedN (hSN halfKN trivKN fluxShareN trivialDefectN bdd_halfKN low_halfKN
  nonneg_halfKN hs_halfKN_pos hs_trivKN_pos hs_conv_trivKN_pos)
open MassGap.SliceCentreAction (Cen centreAction)
open MassGap.DLRLimit (State)
open MassGap.ContinuumSchwinger (Cfg)
open MassGap.PeriodicState (periodicState)
open MassGap.StrongFiniteSize (strongBound)
open MassGap.SubstrateDecode (measMassOf tensorEnergy twoPhase UnitTracksRun)
open MassGap.SubstrateFluxRead (measPeriod SectorSeedMeasured runSeed_of_sectorSeedMeasured sectors_strong
  eventually_sector_condition tendsto_fluxBound)

/-- **The slice configurations of step `i` at side `n`.** DERIVED: no numeral. -/
abbrev Slice (N n : ℕ) (i : Fin 4) : Type := SpT i (Tr n i) → SUN.SU N

variable {N : ℕ} [NeZero N]

/-- The centre action on the slice of step `i` at side `n`. DERIVED: no numeral. -/
abbrev cact (n : ℕ) (i : Fin 4) : Cen i N → Slice N n i → Slice N n i :=
  SliceCentreAction.act (μ := i) (T := Tr n i) (N := N)

omit [NeZero N] in
/-- **The site of a slice point at time `t`.** DERIVED: no numeral. -/
def siteOf (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) (y : TT i T) : Fin 4 → ℤ :=
  fun j => if h : j = i then t else ((y ⟨j, h⟩ : ℕ) : ℤ)

omit [NeZero N] in
/-- DERIVED: no numeral. -/
theorem siteOf_self (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) (y : TT i T) : siteOf i t y i = t := by
  simp [siteOf]

omit [NeZero N] in
/-- DERIVED: no numeral. -/
theorem siteOf_ne (i : Fin 4) {T : {j : Fin 4 // j ≠ i} → ℕ} (t : ℤ) (y : TT i T)
    (j : {j : Fin 4 // j ≠ i}) : siteOf i t y j.1 = ((y j : ℕ) : ℤ) := by
  simp [siteOf, j.2]

omit [NeZero N] in
/-- **The spatial links of step `i` at time `t`, read from a configuration.** DERIVED: no numeral. -/
def readSlice (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) (t : ℤ) : C(Cfg N, SpT i T → SUN.SU N) :=
  ⟨fun U l => U (l.1.1, siteOf i t l.2), continuous_pi fun _ => continuous_apply _⟩

omit [NeZero N] in
/-- **The two slices of step `i`**: times `0` and `n/2`. DERIVED: `0` the first slice; `n/2` half the side. -/
def slicePair (n : ℕ) (i : Fin 4) : C(Cfg N, Slice N n i × Slice N n i) :=
  (readSlice i (Tr n i) 0).prodMk (readSlice i (Tr n i) ((n / 2 : ℕ) : ℤ))

/-- **The bridge**: the capture's two-slice law is the torus's, density `a² / hs(a)` against product Haar.
DERIVED: no numeral. -/
def TwoSliceLaw (ν : State (Cfg N)) (β : ℝ) (n : ℕ) (i : Fin 4) : Prop :=
  ∀ h : C(Slice N n i × Slice N n i, ℝ), ν (h.comp (slicePair n i)) = pairExp (hSN N n i) (halfKN N β n i) ⇑h

/-- DERIVED: no numeral. -/
theorem continuous_cact (n : ℕ) (i : Fin 4) (g : Cen i N) : Continuous (cact (N := N) n i g) := by
  unfold cact SliceCentreAction.act
  exact continuous_pi fun l => continuous_const.mul (continuous_apply l)

/-- **The twisted inverse of a positive test**, `(f ∘ (id × g))⁻¹`, as a continuous function.
DERIVED: no numeral. -/
def invTw {n : ℕ} {i : Fin 4} (f : C(Slice N n i × Slice N n i, ℝ)) (hf : ∀ p, 0 < f p) (g : Cen i N) :
    C(Slice N n i × Slice N n i, ℝ) :=
  ⟨fun p => (f (p.1, cact n i g p.2))⁻¹,
    (f.continuous.comp (continuous_fst.prodMk ((continuous_cact n i g).comp continuous_snd))).inv₀
      fun _ => (hf _).ne'⟩

/-- **The flux read of a capture** at side `n`, step `i`: every positive continuous family of tests has mean
affinity read at least `1 − ε`. DERIVED: `2` the mean of the two terms. -/
def FluxReadOf (ν : State (Cfg N)) (n : ℕ) (i : Fin 4) (ε : ℝ) : Prop :=
  ∀ (f : Cen i N → C(Slice N n i × Slice N n i, ℝ)) (hf : ∀ g p, 0 < f g p),
    1 - ε ≤ (Fintype.card (Cen i N) : ℝ)⁻¹ *
      ∑ g, (ν ((f g).comp (slicePair n i)) + ν ((invTw (f g) (hf g) g).comp (slicePair n i))) / 2

/-- **The step-`0` flux read at the measured period.** DERIVED: `0` the step. -/
def FluxReadMeasured (ν : State (Cfg N)) (ε : ℝ) : Prop := FluxReadOf ν (measPeriod ν) 0 ε

/-- DERIVED: `0`. -/
theorem fluxReadMeasured_iff {ν : State (Cfg N)} {n : ℕ} (hn : measPeriod ν = n) (ε : ℝ) :
    FluxReadMeasured ν ε ↔ FluxReadOf ν n 0 ε := by
  unfold FluxReadMeasured; rw [hn]

/-- **The zero-flux read of a capture**: the capture's two-slice law has a continuous density `ρ ≥ 0` against
product Haar (unique by `density_unique`) and `dd(zk(√ρ)) ≤ ε`. DERIVED: `0` the sign of a density. -/
def DefectReadOf (ν : State (Cfg N)) (n : ℕ) (i : Fin 4) (ε : ℝ) : Prop :=
  ∃ ρ : Slice N n i → Slice N n i → ℝ, Continuous (Function.uncurry ρ) ∧ (∀ x y, 0 ≤ ρ x y) ∧
    (∀ h : C(Slice N n i × Slice N n i, ℝ),
      ν (h.comp (slicePair n i)) = ∫ x, ∫ y, ρ x y * h (x, y) ∂hSN N n i ∂hSN N n i) ∧
    SectorDefect.dd (hSN N n i) (zk (fun x y => Real.sqrt (ρ x y)) (cact n i)) ≤ ε

/-! ### Kernel facts on the slice -/

omit [NeZero N] in
/-- DERIVED: no numeral. -/
theorem continuous_halfKN (β : ℝ) (n : ℕ) (i : Fin 4) :
    Continuous (Function.uncurry (halfKN N β n i)) := by
  unfold halfKN
  exact SliceKernelPower.continuous_iter (μ := i) (T := Tr n i) (N := N) β (n / 2 - 1)

omit [NeZero N] in
/-- **A continuous kernel on the slice is bounded.** DERIVED: no numeral. -/
theorem bdd_of_continuous {n : ℕ} {i : Fin 4} {F : Slice N n i → Slice N n i → ℝ}
    (hF : Continuous (Function.uncurry F)) : Bdd F := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨hF.measurable, C, fun x y => by simpa [Real.norm_eq_abs] using hC (x, y) (Set.mem_univ _)⟩

omit [NeZero N] in
/-- **A continuous function on slice pairs is integrable.** DERIVED: no numeral. -/
theorem integrable_of_continuous {n : ℕ} {i : Fin 4} {F : Slice N n i × Slice N n i → ℝ}
    (hF : Continuous F) : Integrable F ((hSN N n i).prod (hSN N n i)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact Integrable.of_bound hF.measurable.aestronglyMeasurable C
    (Eventually.of_forall fun p => hC p (Set.mem_univ p))

omit [NeZero N] in
/-- **A positive continuous function on slice pairs is a test.** DERIVED: `0`. -/
theorem test_of_continuous {n : ℕ} {i : Fin 4} (f : C(Slice N n i × Slice N n i, ℝ)) (hf : ∀ p, 0 < f p) :
    Test (⇑f) := by
  obtain ⟨p0, -, hp0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty f.continuous.continuousOn
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  refine ⟨f.continuous.measurable, f p0, C, hf p0, fun p => ⟨isMinOn_iff.mp hp0 p (Set.mem_univ p), ?_⟩⟩
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC p (Set.mem_univ p))

/-- **The optimal test on the slice**, continuous. DERIVED: no numeral. -/
def optC {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (g : Cen i N) : C(Slice N n i × Slice N n i, ℝ) :=
  ⟨opt (halfKN N β n i) (cact n i) g, by
    unfold opt
    exact ((continuous_halfKN β n i).comp
      (continuous_fst.prodMk ((continuous_cact n i (-g)).comp continuous_snd))).div
      (continuous_halfKN β n i) fun p =>
        ((CentreSectorSeed.floor_pos β n i).trans_le (low_halfKN hβ n i p.1 p.2)).ne'⟩

theorem optC_pos {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) (g : Cen i N) (p : Slice N n i × Slice N n i) :
    0 < optC (N := N) hβ n i g p :=
  div_pos ((CentreSectorSeed.floor_pos β n i).trans_le (low_halfKN hβ n i _ _))
    ((CentreSectorSeed.floor_pos β n i).trans_le (low_halfKN hβ n i _ _))

/-- **`1 − fluxShareN` is the least mean affinity of the two-slice law.** DERIVED: no numeral. -/
theorem fluxShareN_isLeast {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    IsLeast {r | ∃ f : Cen i N → Slice N n i × Slice N n i → ℝ, (∀ g, Test (f g)) ∧
      meanAff (hSN N n i) (halfKN N β n i) (cact n i) f = r} (1 - fluxShareN N β n i) :=
  isLeast_meanAff (bdd_halfKN hβ n i) centreAction (CentreSectorSeed.floor_pos β n i) (low_halfKN hβ n i)
    (hs_halfKN_pos hβ n i)

/-- The flux read of a capture with the bridge is the mean affinity of the torus's two-slice law.
DERIVED: no numeral. -/
theorem read_eq {ν : State (Cfg N)} {β : ℝ} {n : ℕ} {i : Fin 4} (hν : TwoSliceLaw ν β n i)
    (f : Cen i N → C(Slice N n i × Slice N n i, ℝ)) (hf : ∀ g p, 0 < f g p) :
    (Fintype.card (Cen i N) : ℝ)⁻¹ *
      ∑ g, (ν ((f g).comp (slicePair n i)) + ν ((invTw (f g) (hf g) g).comp (slicePair n i))) / 2
      = meanAff (hSN N n i) (halfKN N β n i) (cact n i) (fun g => ⇑(f g)) := by
  unfold TwoSliceLaw at hν
  unfold meanAff affRead
  simp only [hν]
  rfl

/-- **The flux clause is the flux read**, given the bridge. DERIVED: no numeral. -/
theorem fluxReadOf_iff {ν : State (Cfg N)} {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {i : Fin 4}
    (hν : TwoSliceLaw ν β n i) {ε : ℝ} : FluxReadOf ν n i ε ↔ fluxShareN N β n i ≤ ε := by
  have ha := bdd_halfKN (N := N) hβ n i
  have hA := centreAction (μ := i) (T := Tr n i) (N := N)
  have hpos := hs_halfKN_pos (N := N) hβ n i
  have hlow' : ∀ x y, 0 < halfKN N β n i x y := fun x y =>
    (CentreSectorSeed.floor_pos β n i).trans_le (low_halfKN hβ n i x y)
  have hshare : share (hSN N n i) (halfKN N β n i) (cact n i) = fluxShareN N β n i := rfl
  constructor
  · intro h
    have hopt := h (optC hβ n i) (optC_pos hβ n i)
    rw [read_eq hν (optC hβ n i) (optC_pos hβ n i)] at hopt
    have e : meanAff (hSN N n i) (halfKN N β n i) (cact n i) (fun g => ⇑(optC hβ n i g))
        = 1 - share (hSN N n i) (halfKN N β n i) (cact n i) :=
      meanAff_opt ha hA hlow' hpos
    rw [e, hshare] at hopt
    linarith
  · intro h f hf
    rw [read_eq hν f hf]
    have := one_sub_share_le ha (fun x y => (hlow' x y).le) hA hpos (f := fun g => ⇑(f g))
      (fun g => test_of_continuous (f g) (hf g))
    rw [hshare] at this
    linarith

omit [NeZero N] in
/-- **A continuous density of a two-slice law is unique.** DERIVED: `2` the square. -/
theorem density_unique {n : ℕ} {i : Fin 4} {ρ ρ' : Slice N n i → Slice N n i → ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hρ' : Continuous (Function.uncurry ρ'))
    (h : ∀ k : C(Slice N n i × Slice N n i, ℝ),
      ∫ x, ∫ y, ρ x y * k (x, y) ∂hSN N n i ∂hSN N n i = ∫ x, ∫ y, ρ' x y * k (x, y) ∂hSN N n i ∂hSN N n i) :
    ρ = ρ' := by
  set D : C(Slice N n i × Slice N n i, ℝ) := ⟨fun p => ρ p.1 p.2 - ρ' p.1 p.2, hρ.sub hρ'⟩ with hD
  have b1 : Bdd fun x y => ρ x y * D (x, y) := bdd_of_continuous (hρ.mul D.continuous)
  have b2 : Bdd fun x y => ρ' x y * D (x, y) := bdd_of_continuous (hρ'.mul D.continuous)
  have hsq : ∫ x, ∫ y, D (x, y) ^ 2 ∂hSN N n i ∂hSN N n i = 0 := by
    have e : ∀ x, ∫ y, D (x, y) ^ 2 ∂hSN N n i
        = ∫ y, ρ x y * D (x, y) ∂hSN N n i - ∫ y, ρ' x y * D (x, y) ∂hSN N n i := by
      intro x
      rw [← integral_sub (FluxSectorBound.irow (μ := hSN N n i) b1 x)
        (FluxSectorBound.irow (μ := hSN N n i) b2 x)]
      congr 1; funext y
      show (ρ x y - ρ' x y) ^ 2 = ρ x y * (ρ x y - ρ' x y) - ρ' x y * (ρ x y - ρ' x y)
      ring
    simp_rw [e]
    rw [integral_sub (SectorDefect.int_row (μ := hSN N n i) b1) (SectorDefect.int_row (μ := hSN N n i) b2),
      h D, sub_self]
  have hD2c : Continuous fun p => D p ^ 2 := D.continuous.pow 2
  have hint := integrable_of_continuous hD2c
  have hprod : ∫ p, D p ^ 2 ∂((hSN N n i).prod (hSN N n i)) = 0 := by
    rw [integral_prod _ hint]; exact hsq
  have hae := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg (D p)) hint).mp hprod
  have hzero : (fun p => D p ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq ((hSN N n i).prod (hSN N n i)) hD2c continuous_zero).mp hae
  funext x y
  have h0 := congrFun hzero (x, y)
  have h1 : (ρ x y - ρ' x y) ^ 2 = 0 := h0
  have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  linarith

/-- **The zero-flux clause is the zero-flux read**, given the bridge. DERIVED: `2` the square. -/
theorem defectReadOf_iff {ν : State (Cfg N)} {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {i : Fin 4}
    (hν : TwoSliceLaw ν β n i) {ε : ℝ} : DefectReadOf ν n i ε ↔ trivialDefectN N β n i ≤ ε := by
  have hpos := hs_halfKN_pos (N := N) hβ n i
  have hρc : Continuous (Function.uncurry fun x y => halfKN N β n i x y ^ 2 / hs (hSN N n i) (halfKN N β n i)) :=
    ((continuous_halfKN β n i).pow 2).div_const _
  have hρ0 : ∀ x y, 0 ≤ halfKN N β n i x y ^ 2 / hs (hSN N n i) (halfKN N β n i) := fun x y =>
    div_nonneg (sq_nonneg _) hpos.le
  have hρν : ∀ h : C(Slice N n i × Slice N n i, ℝ), ν (h.comp (slicePair n i))
      = ∫ x, ∫ y, halfKN N β n i x y ^ 2 / hs (hSN N n i) (halfKN N β n i) * h (x, y) ∂hSN N n i ∂hSN N n i :=
    fun h => by rw [hν h, pairExp_eq]
  have hdd : SectorDefect.dd (hSN N n i)
      (zk (fun x y => Real.sqrt (halfKN N β n i x y ^ 2 / hs (hSN N n i) (halfKN N β n i))) (cact n i))
      = trivialDefectN N β n i :=
    dd_root (nonneg_halfKN hβ n i) hpos (hs_trivKN_pos hβ n i) (hs_conv_trivKN_pos hβ n i)
  constructor
  · rintro ⟨ρ, hρ, -, hρν', h⟩
    have e : ρ = fun x y => halfKN N β n i x y ^ 2 / hs (hSN N n i) (halfKN N β n i) :=
      density_unique hρ hρc fun k => by rw [← hρν' k, ← hρν k]
    subst e
    exact (le_of_eq hdd.symm).trans h
  · intro h
    exact ⟨_, hρc, hρ0, hρν, (le_of_eq hdd).trans h⟩

/-! ### The seed in capture form -/

/-- **The sector seed read from the captures** (assumed): `SectorSeedMeasured` with the side the measured period
of the step-`0` capture and both clauses read from the captures. DERIVED: `0` the step; `2` the least side;
`1/80000` the threshold of `defectW_le_of_sectorsN`. -/
def SectorSeedRead (hN : N ≠ 0) (cap : ℝ → ℕ → Fin 4 → State (Cfg N)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in atTop, 0 < measMassOf (periodicState hN β) tensorEnergy ∧
    ∃ n : ℕ, PeriodicState.IsPow2 n ∧ 2 ≤ n ∧
      (n : ℝ≥0∞) * measMassOf (periodicState hN β) tensorEnergy ≤ ENNReal.ofReal C ∧
      measPeriod (cap β n 0) = n ∧
      ∀ i : Fin 4, FluxReadOf (cap β n i) n i (1 / 80000) ∧ DefectReadOf (cap β n i) n i (1 / 80000)

/-- **The bridge along a family** (assumed; discharged for the Wilson family by
`RectTorusState.capturesReadTorus_capR`; its step-`0` instance holds for `torusState hN (n − 1) β` by
`TwoSliceBridge.twoSliceLaw_torusState`): at every `β ≥ 0` and even side `n ≥ 2` the
capture at step `i` has the two-slice law of the corner torus. DERIVED: `0`, `2`. -/
def CapturesReadTorus (cap : ℝ → ℕ → Fin 4 → State (Cfg N)) : Prop :=
  ∀ β : ℝ, 0 ≤ β → ∀ n : ℕ, 2 ≤ n → Even n → ∀ i : Fin 4, TwoSliceLaw (cap β n i) β n i

omit [NeZero N] in
/-- DERIVED: `2`. -/
theorem even_of_pow2 {n : ℕ} (hp : PeriodicState.IsPow2 n) (hn2 : 2 ≤ n) : Even n := by
  obtain ⟨b, hb⟩ := hp
  have hb0 : b ≠ 0 := by rintro rfl; rw [hb] at hn2; norm_num at hn2
  rw [hb]; exact Nat.even_pow.mpr ⟨even_two, hb0⟩

/-- **The read seed gives the measured seed.** DERIVED: `0`. -/
theorem sectorSeedMeasured_of_read (hN : N ≠ 0) {cap : ℝ → ℕ → Fin 4 → State (Cfg N)}
    (hcap : CapturesReadTorus cap) (h : SectorSeedRead hN cap) : SectorSeedMeasured hN := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβS hβ
  obtain ⟨hm, n, hp, hn2, hnm, -, hcl⟩ := hβS
  have he := even_of_pow2 hp hn2
  exact ⟨hm, n, hp, hn2, hnm, fun i =>
    ⟨(fluxReadOf_iff hβ (hcap β hβ n hn2 he i)).mp (hcl i).1,
      (defectReadOf_iff hβ (hcap β hβ n hn2 he i)).mp (hcl i).2⟩⟩

/-- **The measured seed gives the read seed**, given the bridge and the period tie. DERIVED: `0`. -/
theorem sectorSeedRead_of_measured (hN : N ≠ 0) {cap : ℝ → ℕ → Fin 4 → State (Cfg N)}
    (hcap : CapturesReadTorus cap) (hper : ∀ β n, measPeriod (cap β n 0) = n) (h : SectorSeedMeasured hN) :
    SectorSeedRead hN cap := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with β hβS hβ
  obtain ⟨hm, n, hp, hn2, hnm, hcl⟩ := hβS
  have he := even_of_pow2 hp hn2
  exact ⟨hm, n, hp, hn2, hnm, hper β n, fun i =>
    ⟨(fluxReadOf_iff hβ (hcap β hβ n hn2 he i)).mpr (hcl i).1,
      (defectReadOf_iff hβ (hcap β hβ n hn2 he i)).mpr (hcl i).2⟩⟩

/-- **The read seed, with the unit tracking the run, gives the run seed.** DERIVED: no numeral. -/
theorem runSeed_of_sectorSeedRead (hN : N ≠ 0) {cap : ℝ → ℕ → Fin 4 → State (Cfg N)}
    (hcap : CapturesReadTorus cap) (h : SectorSeedRead hN cap) (hU : UnitTracksRun hN) :
    WDeltaRun.RunSeed N :=
  runSeed_of_sectorSeedMeasured hN (sectorSeedMeasured_of_read hN hcap h) hU

/-! ## 4. A capture carrying the torus's two-slice law -/

omit [NeZero N] in
/-- DERIVED: `0`. -/
theorem toNat_lt {z : ℤ} {m : ℕ} (h0 : 0 ≤ z) (h : z < m) : z.toNat < m := by omega

omit [NeZero N] in
/-- **Two slices placed into a configuration**: the links of step `i` at transverse coordinates inside the
extents read the second slice at time `n/2` and the first elsewhere; every other link is `1`. DERIVED: `1` the
identity; `n/2` half the side. -/
def embedPair (n : ℕ) (i : Fin 4) (p : Slice N n i × Slice N n i) : Cfg N := fun l =>
  if hd : l.1 = i then 1 else
    if hb : ∀ j : {j : Fin 4 // j ≠ i}, 0 ≤ l.2 j.1 ∧ l.2 j.1 < (Tr n i j : ℤ) then
      (if l.2 i = ((n / 2 : ℕ) : ℤ) then p.2 else p.1)
        (⟨l.1, hd⟩, fun j => ⟨(l.2 j.1).toNat, toNat_lt (hb j).1 (hb j).2⟩)
    else 1

omit [NeZero N] in
/-- DERIVED: no numeral. -/
theorem continuous_embedPair (n : ℕ) (i : Fin 4) : Continuous (embedPair (N := N) n i) := by
  refine continuous_pi fun l => ?_
  by_cases hd : l.1 = i
  · simp only [embedPair, dif_pos hd]; exact continuous_const
  · by_cases hb : ∀ j : {j : Fin 4 // j ≠ i}, 0 ≤ l.2 j.1 ∧ l.2 j.1 < (Tr n i j : ℤ)
    · by_cases ht : l.2 i = ((n / 2 : ℕ) : ℤ)
      · simp only [embedPair, dif_neg hd, dif_pos hb, if_pos ht]
        exact (continuous_apply _).comp continuous_snd
      · simp only [embedPair, dif_neg hd, dif_pos hb, if_neg ht]
        exact (continuous_apply _).comp continuous_fst
    · simp only [embedPair, dif_neg hd, dif_neg hb]; exact continuous_const

omit [NeZero N] in
/-- **Reading the placed slices returns them.** DERIVED: `2` the least side; `0`, `n/2` the two times. -/
theorem slicePair_embed {n : ℕ} (hn : 2 ≤ n) (i : Fin 4) (p : Slice N n i × Slice N n i) :
    slicePair n i (embedPair n i p) = p := by
  have key : ∀ (t : ℤ) (l : SpT i (Tr n i)),
      embedPair n i p (l.1.1, siteOf i t l.2) = (if t = ((n / 2 : ℕ) : ℤ) then p.2 else p.1) l := by
    intro t l
    have hd : l.1.1 ≠ i := l.1.2
    have hb : ∀ j : {j : Fin 4 // j ≠ i}, 0 ≤ siteOf i t l.2 j.1 ∧ siteOf i t l.2 j.1 < (Tr n i j : ℤ) :=
      fun j => by rw [siteOf_ne]; exact ⟨Int.natCast_nonneg _, by exact_mod_cast (l.2 j).2⟩
    unfold embedPair
    dsimp only
    rw [dif_neg hd, dif_pos hb]
    simp only [siteOf_self]
    have harg : ((⟨l.1.1, hd⟩ : {j : Fin 4 // j ≠ i}),
        fun j : {j : Fin 4 // j ≠ i} =>
          (⟨(siteOf i t l.2 j.1).toNat, toNat_lt (hb j).1 (hb j).2⟩ : Fin (Tr n i j))) = l := by
      apply Prod.ext
      · rfl
      · funext j
        apply Fin.ext
        show (siteOf i t l.2 j.1).toNat = (l.2 j : ℕ)
        rw [siteOf_ne, Int.toNat_natCast]
    rw [harg]
  have h0 : (0 : ℤ) ≠ ((n / 2 : ℕ) : ℤ) := by
    have : 1 ≤ n / 2 := by omega
    omega
  apply Prod.ext
  · funext l
    show embedPair n i p (l.1.1, siteOf i 0 l.2) = p.1 l
    rw [key, if_neg h0]
  · funext l
    show embedPair n i p (l.1.1, siteOf i ((n / 2 : ℕ) : ℤ) l.2) = p.2 l
    rw [key, if_pos rfl]

omit [NeZero N] in
/-- **A capture from a continuous probability density on slice pairs.** DERIVED: `1` the total mass. -/
def capState (n : ℕ) (i : Fin 4) (w : Slice N n i × Slice N n i → ℝ) (hw : Continuous w)
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∫ p, w p ∂((hSN N n i).prod (hSN N n i)) = 1) : State (Cfg N) where
  toFun H := ∫ p, w p * H (embedPair n i p) ∂((hSN N n i).prod (hSN N n i))
  map_add' H K := by
    simp only [ContinuousMap.add_apply, mul_add]
    exact integral_add (integrable_of_continuous (hw.mul (H.continuous.comp (continuous_embedPair n i))))
      (integrable_of_continuous (hw.mul (K.continuous.comp (continuous_embedPair n i))))
  map_smul' c H := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext p; ring
  nonneg' H hH := integral_nonneg fun p => mul_nonneg (hw0 p) (hH _)
  one' := by simp only [ContinuousMap.one_apply, mul_one]; exact hw1

omit [NeZero N] in
/-- DERIVED: no numeral. -/
theorem capState_apply (n : ℕ) (i : Fin 4) (w : Slice N n i × Slice N n i → ℝ) (hw : Continuous w)
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∫ p, w p ∂((hSN N n i).prod (hSN N n i)) = 1) (H : C(Cfg N, ℝ)) :
    capState n i w hw hw0 hw1 H = ∫ p, w p * H (embedPair n i p) ∂((hSN N n i).prod (hSN N n i)) := rfl

/-- **The torus's two-slice density integrates to `1`.** DERIVED: `1`, `2`. -/
theorem integral_pairDensity {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) :
    ∫ p, halfKN N β n i p.1 p.2 ^ 2 / hs (hSN N n i) (halfKN N β n i) ∂((hSN N n i).prod (hSN N n i)) = 1 := by
  rw [integral_prod (fun p : Slice N n i × Slice N n i =>
      halfKN N β n i p.1 p.2 ^ 2 / hs (hSN N n i) (halfKN N β n i))
    (integrable_of_continuous (((continuous_halfKN β n i).pow 2).div_const _))]
  have e : ∫ x, ∫ y, halfKN N β n i x y ^ 2 / hs (hSN N n i) (halfKN N β n i) ∂hSN N n i ∂hSN N n i
      = (∫ x, ∫ y, halfKN N β n i x y ^ 2 ∂hSN N n i ∂hSN N n i) / hs (hSN N n i) (halfKN N β n i) := by
    rw [← integral_div]; congr 1; funext x; rw [integral_div]
  rw [e]
  exact div_self (hs_halfKN_pos hβ n i).ne'

/-- **The capture of the torus's two-slice law** at `(β, n, i)`. DERIVED: `2` the square. -/
def capTorus {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (i : Fin 4) : State (Cfg N) :=
  capState n i (fun p => halfKN N β n i p.1 p.2 ^ 2 / hs (hSN N n i) (halfKN N β n i))
    (((continuous_halfKN β n i).pow 2).div_const _) (fun _ => div_nonneg (sq_nonneg _) (hs_nonneg _))
    (integral_pairDensity hβ n i)

/-- **The bridge holds for the torus capture.** DERIVED: `2` the least side. -/
theorem twoSliceLaw_capTorus {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 2 ≤ n) (i : Fin 4) :
    TwoSliceLaw (capTorus (N := N) hβ n i) β n i := by
  unfold TwoSliceLaw
  intro h
  unfold capTorus
  rw [capState_apply]
  simp only [ContinuousMap.comp_apply, slicePair_embed hn]
  rw [integral_prod (fun p : Slice N n i × Slice N n i =>
      halfKN N β n i p.1 p.2 ^ 2 / hs (hSN N n i) (halfKN N β n i) * h p)
    (integrable_of_continuous ((((continuous_halfKN β n i).pow 2).div_const _).mul h.continuous)),
    pairExp_eq]

/-- **A family satisfying the bridge.** DERIVED: `1` the identity configuration. -/
def capFamily (β : ℝ) (n : ℕ) (i : Fin 4) : State (Cfg N) :=
  if hβ : 0 ≤ β then capTorus hβ n i else twoPhase (fun _ => (1 : SUN.SU N)) (fun _ => 1)

/-- **The bridge hypothesis is satisfiable along a whole family.** DERIVED: no numeral. -/
theorem capturesReadTorus_capFamily : CapturesReadTorus (capFamily (N := N)) := by
  intro β hβ n hn _ i
  unfold capFamily
  rw [dif_pos hβ]
  exact twoSliceLaw_capTorus hβ hn i

/-- **Both reads hold at strong coupling** on the torus capture. DERIVED: `65536 = 2^{16}`; `4 + N⁶`, `N³/2`, `2`
from `sectors_strong`; `3` the spatial directions of a time slice, `N³ = |Z_N³|`; `6 = 2 · 3`, `N⁶` the square
of `N³`. -/
theorem reads_strong {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (hδ : (4 + (N : ℝ) ^ 6) * (β * strongBound n) ≤ 2) (i : Fin 4) {ε : ℝ}
    (hεf : (N : ℝ) ^ 3 * (β * strongBound n) / 2 ≤ ε) (hεd : 2 * (β * strongBound n) ≤ ε) :
    FluxReadOf (capTorus (N := N) hβ0 n i) n i ε ∧ DefectReadOf (capTorus (N := N) hβ0 n i) n i ε := by
  obtain ⟨hf, hd⟩ := sectors_strong (N := N) hβ0 hβ hn he hδ i
  exact ⟨(fluxReadOf_iff hβ0 (twoSliceLaw_capTorus hβ0 hn i)).mpr (hf.trans hεf),
    (defectReadOf_iff hβ0 (twoSliceLaw_capTorus hβ0 hn i)).mpr (hd.trans hεd)⟩

/-- **At strong coupling both reads hold at `1/80000` at every large even side.** DERIVED: `2` the least side;
`1/80000` the threshold; `1/65536` the coupling ceiling of `reads_strong`, `65536 = 2^{16}`. -/
theorem eventually_reads_strong {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 65536) :
    ∀ᶠ n : ℕ in atTop, Even n → ∀ i : Fin 4,
      FluxReadOf (capTorus (N := N) hβ0 n i) n i (1 / 80000) ∧
        DefectReadOf (capTorus (N := N) hβ0 n i) n i (1 / 80000) := by
  have h1 := eventually_sector_condition (N := N) β
  have h2 := (tendsto_order.mp (tendsto_fluxBound (N := N) β)).2 (1 / 80000) (by norm_num)
  have h3 : ∀ᶠ n : ℕ in atTop, 2 * (β * strongBound n) < 1 / 80000 := by
    have h := (MassGap.StrongFiniteSize.tendsto_strongBound.const_mul β).const_mul 2
    rw [mul_zero, mul_zero] at h
    exact (tendsto_order.mp h).2 _ (by norm_num)
  filter_upwards [h1, h2, h3, eventually_ge_atTop 2] with n hn1 hn2 hn3 hn4 he i
  exact reads_strong hβ0 hβ hn4 he hn1 i hn2.le hn3.le

end Lattice

end MassGap.FluxDuality

end

#print axioms MassGap.FluxDuality.amgm
#print axioms MassGap.FluxDuality.le_affRead
#print axioms MassGap.FluxDuality.affRead_opt
#print axioms MassGap.FluxDuality.one_sub_share
#print axioms MassGap.FluxDuality.meanAff_opt
#print axioms MassGap.FluxDuality.one_sub_share_le
#print axioms MassGap.FluxDuality.test_opt
#print axioms MassGap.FluxDuality.isLeast_meanAff
#print axioms MassGap.FluxDuality.pairExp_eq
#print axioms MassGap.FluxDuality.dd_const_mul
#print axioms MassGap.FluxDuality.dd_root
#print axioms MassGap.FluxDuality.slicePair_embed
#print axioms MassGap.FluxDuality.fluxShareN_isLeast
#print axioms MassGap.FluxDuality.read_eq
#print axioms MassGap.FluxDuality.fluxReadOf_iff
#print axioms MassGap.FluxDuality.density_unique
#print axioms MassGap.FluxDuality.defectReadOf_iff
#print axioms MassGap.FluxDuality.fluxReadMeasured_iff
#print axioms MassGap.FluxDuality.sectorSeedMeasured_of_read
#print axioms MassGap.FluxDuality.sectorSeedRead_of_measured
#print axioms MassGap.FluxDuality.runSeed_of_sectorSeedRead
#print axioms MassGap.FluxDuality.twoSliceLaw_capTorus
#print axioms MassGap.FluxDuality.capturesReadTorus_capFamily
#print axioms MassGap.FluxDuality.reads_strong
#print axioms MassGap.FluxDuality.eventually_reads_strong
