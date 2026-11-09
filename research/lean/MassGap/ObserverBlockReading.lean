import Mathlib
import MassGap.ObserverOneInput
import MassGap.StrongLocalFiniteSize
import MassGap.ObserverEnergyMoments

/-!
# MassGap.ObserverBlockReading — the block reading pinned, and what `ObsRegimeW` asks of it

`ObserverRegime.ObsRegimeW` takes the block reading `R` as a free argument, and
`ObserverOneInput.obsRegimeW_const` shows it holds at a constant reading. This module pins the reading to a
function of the plaquette holonomies of the flowed configuration, shows that pinning alone does not give the
predicate content, states the form that has content, proves its pair piece at strong coupling, and proves the
short bridge from that piece to block-smeared energy readings. Declarations are in the namespace
`MassGap.ObserverBlockReading`.

## 1. The reading (defined; properties proved)

The reading is built from plaquette holonomies only. A plaquette holonomy is unitary, and the per-site gauge
rotation cancels in its conjugacy class; the class function `wilsonDensity g = 1 − Re tr g / N` reads that class.
No coupling, spacing or renormalization constant enters the reading.
* `planes`: the six planes `μ < ν`. `blockSites b z`: the sites `x` with `b z_i ≤ x_i < b z_i + b`, the cubic block
  of side `b` (lattice units) at block coordinate `z ∈ ℤ⁴`. `blockPlaqs b z`: the plaquettes based there.
* **`blockEnergy b U z`**: the mean of `wilsonDensity` of the plaquette holonomies of `U` over `blockPlaqs b z`.
  **`blockRead W k b U z = blockEnergy b (W.V k U) z`**: the observer's reading of its flowed configuration.
* `volDist b z U U'`: the volume-averaged block metric, the mean over the block's plaquettes of the change of the
  holonomy-class reading. `volDist_self`, `volDist_comm`, `volDist_triangle`: a pseudometric.
  `blockEnergy_lip`: the reading is `1`-Lipschitz from `volDist` to `ℝ`.
* `blockEnergy_mem`: the reading lies in `[0, 2]`. `blockRead_gauge`: gauge invariant (`ConfFlow.gauge` and the
  class-function property of `plaqField`).
* **`blockRead_separates`** (`N = 2`, `b ≥ 1`): for every flow whose step-`k` map fixes centre-valued
  configurations, the reading at block `0` is `0` on the trivial configuration and positive on
  `ObserverEnergyMoments.Utw` (one link at `−1`). The hypothesis holds at `ConfFlow.identity`
  (`identity_fixes_central`); `ObserverEnergyMoments.obsFlow_central` proves the same fixing for the APE flow map.
  `blockRead_nonconst`: so the reading is not constant. At `N = 1` the group is trivial and every reading is
  constant; separation needs `N ≥ 2`.

## 2. Pinning the reading does not give `ObsRegimeW` content (proved)

* `vacC d θ α i j = (α/|ι|) θ^{d(i,j)}`, `vacQ d θ α D = 2 D² |ι| / (α θ^{Σ d})`. `weightedRow_vacC`: the weighted
  row holds with value `α`.
* **`dobCompareW1_bounded`**: for every state, every finite block set, every reading into blocks of diameter
  `≤ D`, every block distance, every `θ ∈ (0, 1]` and `α ∈ (0, 1)`: `DobCompareW1 ν χ (vacC d θ α) (vacQ d θ α D)`.
  The covariance is at most `2 D² (Σ Lf)(Σ Lh)` (each test is within `D Σ L` of a constant), and
`Σ_n Cⁿ ≥ C ≥ (α/|ι|) θ^{Σ d}` entrywise, so the comparison side is at least the same quantity.
* **`obsRegimeW_of_bounded`**, **`obsRegimeW_blockRead_vacuous`**: `ObsRegimeW` holds for the pinned,
  gauge-invariant reading `blockEnergyIcc` of the flowed configuration (the reading in `[0, 2]`; non-constant at
  `N = 2` for flows that fix centre-valued configurations) on every finite block set, at `θ = α = 1/2`, at every
  flow `W`, every block side `b` and every step of the tower `stateK` (whose coupling tends to `∞`), with no input. On a fixed finite
  `ι`, `ObsRegimeW` has no content for any bounded reading: `Q` is chosen after the block set, and `vacQ` grows
  like `|ι| θ^{−Σ d}`. The content is in `Q`, `θ`, `α` being fixed before the block set.

## 3. The form with content, and its pair piece (defined; implications proved)

* **`ObsRegimeUnif hN W bk c Q θ α`**: `0 ≤ α < 1`, `0 < θ < 1`, `Q ≥ 0`, block side `bk k ≥ 1`, one
  translation-invariant interdependence kernel `c ≥ 0` on `ℤ⁴` with weighted row
  `Σ_{z'∈S} c(z' − z) θ^{−‖z' − z‖∞} ≤ α` on every finite `S`, and, eventually in the step, uniformly over every
  finite block set `S`, `DobCompareW1 (stateK hN k) (blockEnergyIcc … ∘ W.V k) (c(j − i)) Q`. Every constant is fixed
  before `S` and before `k`.
* `obsRegimeW_of_unif`: it gives `ObsRegimeW` on every `S` with the same constants.
* `PairDecay ν e Q θ`: for every pair of blocks `z, z'` and Lipschitz `f`, `h` on `ℝ`,
  `|Cov_ν(f ∘ e_z, h ∘ e_{z'})| ≤ Q Lf Lh θ^{‖z' − z‖∞}`. **`pairDecay_of_unif`**: `ObsRegimeUnif` gives
  `PairDecay (stateK hN k) (blockRead W k (bk k)) (Q/(1 − α)) θ` eventually in the step.

## 4. The strong-coupling witness of the pair piece (proved)

* `cbox c R`: links based in `c + [−R, R]⁴`; `card_cbox`: `4 (2R + 1)⁴`. `snorm_sub_nbr`: the depth
  `R + 1 − ‖l − c‖∞` drops by at most `1` along `StrongKernelNear.nbr`.
* `cov_sep_strong` (`|β| ≤ 2^{-16}`, any `N ≠ 0`): `F` local on `cbox c s` within `BF` of a constant, `H`
  not reading `cbox c R` and within `BH` of a constant, `s ≤ R`:
  `|Cov(F, H)| ≤ 4 |cbox c s| 2^{−(R + 1 − s)} BF BH` in `periodicState hN β`
  (`StrongKernelNear.kernelNear_strong_explicit` and `BoxFocusTest.cov_le_of_kernelNear`).
* `blockRead_local`: the step-`k` reading of block `z` reads only `cbox (b z) (b + ρ)` once `W.range k ≤ ρ`.
* **`blockCov_strong`**, **`pairDecay_strong`**: at `|β| ≤ 2^{-16}`, every `N ≠ 0`, every flow with
  `W.range k ≤ ρ`, every block side `b`:
  `PairDecay (periodicState hN β) (blockRead W k b) (strongQ b ρ) ((1/2)^b)`,
  `strongQ b ρ = 16 (2(b + ρ) + 1)⁴ 2^{2(b + ρ)}`. At `b ≥ 1`, `θ = 2^{−b} < 1`; `α = 0` (no comparison
  matrix is used). Uniform in the block positions, hence in any block count. `pairDecay_strong_along`: the same
  at every step of the constant tower `stateAlong hN (fun _ => β)`, given `W.range k ≤ ρ` for every `k`.
* **Why the eventually-in-the-step form cannot be met here.** `stateK_not_strong`: eventually in `k`,
  `|dyBeta k| > 2^{-16}`; the tower `stateK` leaves the strong-coupling range, so no statement proved at
  `|β| ≤ 2^{-16}` is about `stateK k` for large `k`. The fixed-coupling form replaces `stateK hN k` by the
  constant tower. It is also only the pair piece: tests of several blocks need a comparison theorem
  (`DobCompareW1` itself), and the single-link sweep gives a prefactor in the test's support size, not
  `Σ Lf_i D_ij Lh_j`. And `strongQ b ρ` grows with `b` and `ρ` in lattice units, which is the growing-quantity
  defect if `b`, `ρ` are read as physical lengths at `β → ∞`.

## 5. Clustering, not the gap (proved where named, argued otherwise)

* `stateCov_sum`: covariance is bilinear over finite weighted sums. **`smearedCov_le`**: `PairDecay` gives, for
  block-smeared readings `Σ_{z∈A} w_z e_z`, `Σ_{z'∈B} w'_{z'} e_{z'}` with `A`, `B` at block distance `≥ r`,
  `|Cov| ≤ Q θ^r (Σ|w|)(Σ|w'|)`. This is the proved bridge from the pair piece to linear block-smeared energy
  readings.
* Proved: `ObsRegimeUnif` gives clustering of the flowed energy reading (`pairDecay_of_unif`, then
`smearedCov_le`). Argued: it does not give `RunSeed`, which reads
  the torus free-energy defect `defectW` (`ObserverOneInput`: no module derives a torus free-energy bound from
  infinite-volume clustering). The gap clause in the clustering form is `FlowCapstone.FlowClusterAbs` (consumed
  by `FlowCapstone.flow_gap_of_abs_cluster`). The bridge from `ObsRegimeUnif` to it, not built, needs:
  (i) products of block readings (margin monomials are products), which need the multi-block tests of
  `ObsRegimeUnif`, not `PairDecay`; (ii) every margin monomial, not only energy-class ones, as a Lipschitz
  function of block readings, which the scalar energy reading does not supply (a vector reading of the block's
  holonomy classes would); (iii) a physical rate: block distance `r` against physical distance `d` needs
  `bk k · a_k ≤ b`, and `a_k` is a substrate parameter; (iv) the continuum limit along `kernF`, by
  `ObserverRegime.abs_le_of_tendsto`. The gap on the whole Hilbert space also needs cyclicity.

## 6. Tests of `ObsRegimeUnif` (argued)

1. Free field. For a massive Gaussian field the block energy (`:φ²:` averaged on a block) has connected
   correlations decaying like `e^{−2 m d}`; the pair piece holds with `θ ≈ e^{−2 m b}`, and the comparison form is
   the row-sum diagnostic of `ObserverRegime` §4 item 3, below `1` only when `m b` is large. Massless: the `:φ²:` correlator decays like `d^{−4}` (the action density `(∂φ)²`, like `F²` in the gauge
theory, like `d^{−8}`), so no `θ < 1` fixed before `S` exists, and the Prop fails, as
   it must for a theory with no gap. The test discriminates.
2. Growing quantity. `Q`, `θ`, `α`, `c` are fixed before the block set `S` and before `k`; that is the
   difference from `ObsRegimeW`, which §2 shows is met by every bounded reading because `Q` follows `|ι|`. The
   block side `bk k` and flow range grow in lattice units; nothing in the Prop is fixed in lattice units except
   `bk k ≥ 1`. The strong witness `strongQ` is fixed in lattice units, so it does not survive `β → ∞` at fixed
   physical block size.
3. Restatement against reduction. `ObsRegimeUnif` contains clustering of the flowed energy reading at every block
   distance (`pairDecay_of_unif`): for this reading it is the conclusion, stated with uniform constants. It is a
   reduction only through Dobrushin's comparison theorem (the W1 row at one scale implying decay at all scales),
   which is assumed in `DobCompareW1`, not proved. Read as an input, the content is the weighted row at one
   block scale beyond the crossover, uniformly in `β`; as stated, it is the decay.
4. Degenerate case. `bk k = 0` makes the reading constant (empty block); the Prop requires `bk k ≥ 1`. The reading is pinned, so the constant reading of `obsRegimeW_const` is not available; it separates
configurations for flows that fix centre-valued configurations (`blockRead_separates`, `N = 2`).
`ObsRegimeUnif` keeps `W` a free argument and does not require that property.

## 7. Parameters

Measured by the reading: none; the scale `b` (and `bk`) is supplied, not measured. Chosen by the observer: the
flow `W`, the block side `b` / `bk`, the block coordinates `z`, the tests `f`, `h` and their constants, the
block set `S`, the range bound `ρ`, the weights `w`. Shared with the substrate: the colour count `N` (the trace
normalization of `wilsonDensity`), the step index `k` (the flow's step and the coupling tower `stateK` share it),
and, in the witness only, the coupling `β` (in the state, not in the reading). `a_k` enters only the argued
physical-rate conversion of §5 item (iii).

DERIVED (module-wide): `0` signs, the origin block and the trivial reading; `1` the least block side, the unit
Lipschitz constant and the shell offset; `2` the range of `wilsonDensity`, the colour count of the separation and
the two sides of a constant; `4` the dimension and the directions of `cbox`; `16 = 4 · 4`; `65536 = 2^{16}` the
strong-coupling threshold of `StrongKernelNear`; `1/2` its contraction rate and the `θ`, `α` of the vacuity
witness.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverBlockReading

open Filter
open MassGap.GibbsSpec
open MassGap.DLRLimit (State)
open MassGap.FocusZoom (stateCov)
open MassGap.SUN (SU)
open MassGap.ContinuumSchwinger (Cfg stateK)
open MassGap.ContinuumFlow (ConfFlow)
open MassGap.ObserverEnergyMoments (plaqField)
open MassGap.StrongKernelNear (IsLocalOn nbr)
open MassGap.StrongFiniteSize (snorm snorm_le_iff ilinks_base)
open MassGap.PeriodicState (periodicState)
open MassGap.BoxFocusTest (cov_le_of_near_const cov_le_of_kernelNear)
open MassGap.WilsonAction (wilsonDensity wilsonDensity_nonneg wilsonDensity_le_two)
open MassGap.ObserverRegime (WeightedRow DobCompareW1 ObsRegimeW pow_entry_le coarse_cov_sep)
open MassGap.BlockLipschitz (BlockLip blockOsc_of_blockLip)
open MassGap.BlockDobrushin (exists_near_of_blockOsc)

/-! ## 0. Covariance algebra -/

section Cov

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Covariance of affine images**: `Cov(r (F − a), H − a') = r Cov(F, H)`. DERIVED: no numeral. -/
theorem stateCov_affine (ν : State X) (F H : C(X, ℝ)) (r a a' : ℝ) :
    stateCov ν (r • (F - a • (1 : C(X, ℝ)))) (H - a' • (1 : C(X, ℝ))) = r * stateCov ν F H := by
  unfold stateCov
  have e : (r • (F - a • (1 : C(X, ℝ)))) * (H - a' • (1 : C(X, ℝ)))
      = r • (F * H) - (r * a') • F - (r * a) • H + (r * a * a') • (1 : C(X, ℝ)) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [e]
  simp only [State.map_add, State.map_sub, State.map_smul, State.map_one]
  ring

/-- **A constant shift of the second observable leaves the covariance unchanged.** DERIVED: `1` the unit
scale; `0` the zero shift. -/
theorem stateCov_sub_const_right (ν : State X) (F H : C(X, ℝ)) (a' : ℝ) :
    stateCov ν F (H - a' • (1 : C(X, ℝ))) = stateCov ν F H := by
  have h := stateCov_affine ν F H 1 0 a'
  rwa [zero_smul, sub_zero, one_smul, one_mul] at h

/-- **Covariance is bilinear over finite weighted sums.** DERIVED: no numeral. -/
theorem stateCov_sum {α β : Type*} (ν : State X) (A : Finset α) (B : Finset β) (w : α → ℝ) (w' : β → ℝ)
    (E : α → C(X, ℝ)) (E' : β → C(X, ℝ)) :
    stateCov ν (∑ a ∈ A, w a • E a) (∑ b ∈ B, w' b • E' b)
      = ∑ a ∈ A, ∑ b ∈ B, w a * w' b * stateCov ν (E a) (E' b) := by
  unfold stateCov
  rw [Finset.sum_mul_sum, State.map_sum, State.map_sum, State.map_sum, Finset.sum_mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [State.map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_mul_smul_comm, State.map_smul, State.map_smul, State.map_smul]
  ring

end Cov

variable {N : ℕ}

/-! ## 1. The block reading -/

/-- The six planes `μ < ν`. DERIVED: `4` the dimension. -/
def planes : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun p => p.1 < p.2

/-- The sites of the cubic block of side `b` at block coordinate `z`. DERIVED: `4` the dimension. -/
def blockSites (b : ℕ) (z : ISite) : Finset ISite :=
  Fintype.piFinset fun i => Finset.Ico ((b : ℤ) * z i) ((b : ℤ) * z i + b)

/-- The plaquettes based in the block. DERIVED: no numeral. -/
def blockPlaqs (b : ℕ) (z : ISite) : Finset IPlaq := planes ×ˢ blockSites b z

/-- **The block energy**: the mean holonomy-class reading `wilsonDensity` over the block's plaquettes.
DERIVED: no numeral. -/
def blockEnergy (b : ℕ) (U : Cfg N) (z : ISite) : ℝ :=
  ((blockPlaqs b z).card : ℝ)⁻¹ * ∑ q ∈ blockPlaqs b z, (plaqField (N := N) q).1 U

/-- **The observer's block reading**: the block energy of the flowed configuration. DERIVED: no numeral. -/
def blockRead (W : ConfFlow N) (k b : ℕ) (U : Cfg N) (z : ISite) : ℝ := blockEnergy b (W.V k U) z

/-- **The volume-averaged block metric**: the mean change of the plaquette holonomy-class reading over the
block. DERIVED: no numeral. -/
def volDist (b : ℕ) (z : ISite) (U U' : Cfg N) : ℝ :=
  ((blockPlaqs b z).card : ℝ)⁻¹ *
    ∑ q ∈ blockPlaqs b z, |(plaqField (N := N) q).1 U - (plaqField (N := N) q).1 U'|

/-- DERIVED: no numeral. -/
theorem plaqField_apply (q : IPlaq) (U : Cfg N) :
    (plaqField (N := N) q).1 U = wilsonDensity (ihol q U) := rfl

/-- DERIVED: `0` the distance to itself. -/
theorem volDist_self (b : ℕ) (z : ISite) (U : Cfg N) : volDist b z U U = 0 := by
  simp [volDist]

/-- DERIVED: no numeral. -/
theorem volDist_comm (b : ℕ) (z : ISite) (U U' : Cfg N) : volDist b z U U' = volDist b z U' U := by
  unfold volDist
  congr 1
  exact Finset.sum_congr rfl fun q _ => abs_sub_comm _ _

/-- DERIVED: no numeral. -/
theorem volDist_triangle (b : ℕ) (z : ISite) (U U' U'' : Cfg N) :
    volDist b z U U'' ≤ volDist b z U U' + volDist b z U' U'' := by
  unfold volDist
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => abs_sub_le _ _ _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- **The reading is `1`-Lipschitz in the volume-averaged metric.** DERIVED: no numeral. -/
theorem blockEnergy_lip (b : ℕ) (z : ISite) (U U' : Cfg N) :
    |blockEnergy b U z - blockEnergy b U' z| ≤ volDist b z U U' := by
  unfold blockEnergy volDist
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- **The reading lies in `[0, 2]`.** DERIVED: `0`, `2` the range of `wilsonDensity`. -/
theorem blockEnergy_mem (hN : N ≠ 0) (b : ℕ) (U : Cfg N) (z : ISite) :
    0 ≤ blockEnergy b U z ∧ blockEnergy b U z ≤ 2 := by
  unfold blockEnergy
  have h0 : ∀ q, 0 ≤ (plaqField (N := N) q).1 U := fun q => by
    rw [plaqField_apply]; exact wilsonDensity_nonneg hN _
  have h2 : ∀ q, (plaqField (N := N) q).1 U ≤ 2 := fun q => by
    rw [plaqField_apply]; exact wilsonDensity_le_two hN _
  have hs : ∑ q ∈ blockPlaqs b z, (plaqField (N := N) q).1 U ≤ ((blockPlaqs b z).card : ℝ) * 2 := by
    calc ∑ q ∈ blockPlaqs b z, (plaqField (N := N) q).1 U ≤ ∑ _q ∈ blockPlaqs b z, (2 : ℝ) :=
          Finset.sum_le_sum fun q _ => h2 q
      _ = ((blockPlaqs b z).card : ℝ) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hs0 : 0 ≤ ∑ q ∈ blockPlaqs b z, (plaqField (N := N) q).1 U := Finset.sum_nonneg fun q _ => h0 q
  refine ⟨mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hs0, ?_⟩
  rcases eq_or_lt_of_le (Nat.cast_nonneg (blockPlaqs b z).card : (0 : ℝ) ≤ (blockPlaqs b z).card)
    with h | h
  · rw [← h, inv_zero, zero_mul]; norm_num
  · rw [inv_mul_le_iff₀ h]; linarith

/-- **The reading is gauge invariant.** DERIVED: no numeral. -/
theorem blockRead_gauge (W : ConfFlow N) (k b : ℕ) (g : ISite → SU N) (U : Cfg N) (z : ISite) :
    blockRead W k b (GaugeInvariantAlgebra.igaugeTransform g U) z = blockRead W k b U z := by
  unfold blockRead blockEnergy
  rw [W.gauge]
  congr 1
  exact Finset.sum_congr rfl fun q _ => (plaqField (N := N) q).2.2 g (W.V k U)

/-- The reference plaquette lies in block `0` at every side `b ≥ 1`. DERIVED: `0`, `1` the plane and the
origin; `1` the least side. -/
theorem q0_mem (b : ℕ) (hb : 1 ≤ b) : ObserverEnergyMoments.q0 ∈ blockPlaqs b 0 := by
  simp only [blockPlaqs, Finset.mem_product, planes, Finset.mem_filter, Finset.mem_univ, true_and,
    blockSites, Fintype.mem_piFinset, Finset.mem_Ico, ObserverEnergyMoments.q0]
  refine ⟨by decide, fun i => ?_⟩
  simp only [Pi.zero_apply, mul_zero, zero_add]
  exact ⟨le_rfl, by omega⟩

/-- **The trivial configuration reads `0`.** DERIVED: `0` the density of the identity; `1` the identity. -/
theorem blockEnergy_flat (hN : N ≠ 0) (b : ℕ) (z : ISite) :
    blockEnergy (N := N) b (fun _ => 1) z = 0 := by
  unfold blockEnergy
  rw [Finset.sum_eq_zero fun q _ => ?_, mul_zero]
  rw [plaqField_apply]
  have : ihol q (fun _ => (1 : SU N)) = 1 := by
    simp [ihol, MassGap.WilsonLattice.wilsonHol, ibd]
  rw [this]
  exact MassGap.WilsonAction.wilsonDensity_one hN

/-- **One link at `−1` gives a positive reading at block `0`.** DERIVED: `2` the colour count and the
density of `−1`; `0` the origin block; `1` the least side. -/
theorem blockEnergy_tw_pos (b : ℕ) (hb : 1 ≤ b) :
    0 < blockEnergy (N := 2) b ObserverEnergyMoments.Utw 0 := by
  unfold blockEnergy
  have hmem := q0_mem b hb
  have hcard : 0 < ((blockPlaqs b 0).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨_, hmem⟩)
  have hs : (plaqField (N := 2) ObserverEnergyMoments.q0).1 ObserverEnergyMoments.Utw
      ≤ ∑ q ∈ blockPlaqs b 0, (plaqField (N := 2) q).1 ObserverEnergyMoments.Utw :=
    Finset.single_le_sum (f := fun q => (plaqField (N := 2) q).1 ObserverEnergyMoments.Utw)
      (fun q _ => by rw [plaqField_apply]; exact wilsonDensity_nonneg (by norm_num) _) hmem
  rw [ObserverEnergyMoments.plaq_tw] at hs
  exact mul_pos (inv_pos.mpr hcard) (by linarith)

/-- **The reading separates two configurations** (`N = 2`, `b ≥ 1`) for every flow whose step-`k` map fixes
centre-valued configurations. DERIVED: `2` the colour count; `0` the origin block and the trivial reading;
`1` the least side and the identity. -/
theorem blockRead_separates (W : ConfFlow 2) (k b : ℕ) (hb : 1 ≤ b)
    (hcen : ∀ U : Cfg 2, (∀ l, ObserverEnergyMoments.IsCentral (U l)) → W.V k U = U) :
    blockRead W k b (fun _ => 1) 0 = 0 ∧ 0 < blockRead W k b ObserverEnergyMoments.Utw 0 := by
  unfold blockRead
  rw [hcen _ ObserverEnergyMoments.central_flat, hcen _ ObserverEnergyMoments.central_tw]
  exact ⟨blockEnergy_flat two_ne_zero b 0, blockEnergy_tw_pos b hb⟩

/-- The identity flow fixes centre-valued configurations: the separation hypothesis is satisfiable.
DERIVED: `2` the colour count. -/
theorem identity_fixes_central (k : ℕ) :
    ∀ U : Cfg 2, (∀ l, ObserverEnergyMoments.IsCentral (U l)) → (ConfFlow.identity 2).V k U = U :=
  fun _ _ => rfl

/-- **The reading is not constant.** DERIVED: `2` the colour count; `0` the origin block; `1` the least
side. -/
theorem blockRead_nonconst (W : ConfFlow 2) (k b : ℕ) (hb : 1 ≤ b)
    (hcen : ∀ U : Cfg 2, (∀ l, ObserverEnergyMoments.IsCentral (U l)) → W.V k U = U) :
    ∃ U U' : Cfg 2, blockRead W k b U 0 ≠ blockRead W k b U' 0 := by
  obtain ⟨h0, hpos⟩ := blockRead_separates W k b hb hcen
  exact ⟨fun _ => 1, ObserverEnergyMoments.Utw, by rw [h0]; exact hpos.ne⟩

/-- **The block energy in `[0, 2]`**, as a block datum with the subtype metric; `ObsRegimeW` applies it to the
flowed configuration `W.V k U`, which gives `blockRead`. DERIVED: `0`, `2` the range. -/
def blockEnergyIcc (hN : N ≠ 0) (b : ℕ) (V : Cfg N) (z : ISite) : Set.Icc (0 : ℝ) 2 :=
  ⟨blockEnergy b V z, blockEnergy_mem hN b V z⟩

/-- DERIVED: `2` the diameter of `[0, 2]`. -/
theorem dist_Icc_le (u v : Set.Icc (0 : ℝ) 2) : dist u v ≤ 2 := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  constructor <;> linarith [u.2.1, u.2.2, v.2.1, v.2.2]

/-! ## 2. Pinning the reading does not give `ObsRegimeW` content -/

section Vacuity

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  {ι : Type*} [Fintype ι] {Y : ι → Type*} [∀ i, PseudoMetricSpace (Y i)]

/-- The interdependence matrix of the vacuity witness. DERIVED: no numeral. -/
def vacC (d : ι → ι → ℕ) (θ α : ℝ) : Matrix ι ι ℝ := fun i j => α / Fintype.card ι * θ ^ d i j

/-- The spread constant of the vacuity witness. DERIVED: `2` the two sides of a constant. -/
def vacQ (d : ι → ι → ℕ) (θ α D : ℝ) : ℝ :=
  2 * D ^ 2 * Fintype.card ι / (α * θ ^ (∑ i, ∑ j, d i j))

/-- DERIVED: `0` the sign. -/
theorem weightedRow_vacC (d : ι → ι → ℕ) {θ α : ℝ} (hθ0 : 0 < θ) (hα : 0 ≤ α) :
    WeightedRow (vacC d θ α) d θ α := by
  refine ⟨fun i j => mul_nonneg (div_nonneg hα (Nat.cast_nonneg _)) (pow_nonneg hθ0.le _), fun i => ?_⟩
  haveI : Nonempty ι := ⟨i⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h : ∀ j, vacC d θ α i j * (θ ^ d i j)⁻¹ = α / Fintype.card ι := fun j => by
    unfold vacC
    rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hθ0.ne'), mul_one]
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e : (Fintype.card ι : ℝ) * (α / Fintype.card ι) = α := by field_simp
  rw [e]

/-- **Every bounded coarse field meets the W1 comparison bound on a finite block set**, at every `θ ∈ (0, 1]`
and `α ∈ (0, 1)`, with `Q = vacQ`. DERIVED: `1` the first power; `2` the two sides of a constant. -/
theorem dobCompareW1_bounded [DecidableEq ι] (ν : State X) (χ : X → ∀ i, Y i) {D : ℝ} (hD : ∀ i (u v : Y i), dist u v ≤ D)
    (d : ι → ι → ℕ) {θ α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hd0 : ∀ i, d i i = 0) (hdt : ∀ i k j, d i j ≤ d i k + d k j) :
    DobCompareW1 ν χ (vacC d θ α) (vacQ d θ α D) := by
  intro f h F H hF hH Lf Lh hLf hLh hf hh
  obtain ⟨c, hc⟩ := exists_near_of_blockOsc (blockOsc_of_blockLip hLf hD hf)
  obtain ⟨c', hc'⟩ := exists_near_of_blockOsc (blockOsc_of_blockLip hLh hD hh)
  have h1 : |stateCov ν F H| ≤ 2 * (∑ j, Lh j * D) * (∑ i, Lf i * D) := by
    rw [← stateCov_sub_const_right ν F H c']
    refine cov_le_of_near_const ν F (H - c' • (1 : C(X, ℝ))) (c := c) (fun x => ?_) (fun x => ?_)
    · rw [hF]; exact hc _
    · simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
        mul_one]
      rw [hH]; exact hc' _
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero] at h1 ⊢
    exact h1
  · have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    set κ : ℝ := α / Fintype.card ι * θ ^ (∑ i, ∑ j, d i j) with hκ
    have hW := weightedRow_vacC d hθ0 hα0.le
    have hb := pow_entry_le hθ0 hθ1 hα0.le hd0 hdt hW
    have hT : ∀ i j, κ ≤ ∑' m, (vacC d θ α ^ m) i j := by
      intro i j
      have hs : Summable fun m : ℕ => (vacC d θ α ^ m) i j :=
        Summable.of_nonneg_of_le (fun m => (hb m i j).1) (fun m => (hb m i j).2)
          ((summable_geometric_of_lt_one hα0.le hα1).mul_right _)
      have h1' : (vacC d θ α ^ 1) i j ≤ ∑' m, (vacC d θ α ^ m) i j :=
        hs.le_tsum 1 (fun m _ => (hb m i j).1)
      rw [pow_one] at h1'
      refine le_trans ?_ h1'
      have hdle : d i j ≤ ∑ i, ∑ j, d i j :=
        le_trans (Finset.single_le_sum (f := fun j => d i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
          (Finset.single_le_sum (f := fun i => ∑ j, d i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0.le hθ1 hdle) (div_nonneg hα0.le hn.le)
    have hsum : κ * ((∑ i, Lf i) * ∑ j, Lh j)
        ≤ ∑ i, ∑ j, Lf i * (∑' m, (vacC d θ α ^ m) i j) * Lh j := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      calc κ * (Lf i * Lh j) = Lf i * κ * Lh j := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT i j) (hLf i)) (hLh j)
    have hθS : 0 < θ ^ (∑ i, ∑ j, d i j) := pow_pos hθ0 _
    have hQ : vacQ d θ α D * κ = 2 * D ^ 2 := by
      unfold vacQ
      rw [hκ]
      field_simp
    have hQ0 : 0 ≤ vacQ d θ α D := div_nonneg (by positivity) (mul_pos hα0 hθS).le
    calc |stateCov ν F H| ≤ 2 * (∑ j, Lh j * D) * (∑ i, Lf i * D) := h1
      _ = vacQ d θ α D * κ * ((∑ i, Lf i) * ∑ j, Lh j) := by
          rw [hQ, ← Finset.sum_mul, ← Finset.sum_mul]; ring
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsum hQ0

/-- **`ObsRegimeW` holds for every bounded reading on a finite block set**, at every step of `stateK` (`dobCompareW1_bounded` holds in every state).
DERIVED: `0` the sign of `Q`. -/
theorem obsRegimeW_of_bounded [DecidableEq ι] (hN : N ≠ 0) (W : ConfFlow N) (R : ℕ → Cfg N → ∀ i, Y i) {D : ℝ}
    (hD : ∀ i (u v : Y i), dist u v ≤ D) (d : ι → ι → ℕ) {θ α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hα0 : 0 < α) (hα1 : α < 1) (hd0 : ∀ i, d i i = 0) (hdt : ∀ i k j, d i j ≤ d i k + d k j) :
    ObsRegimeW hN W R (vacC d θ α) (vacQ d θ α D) d θ α :=
  ⟨hα0.le, hα1, hθ0, hθ1, div_nonneg (by positivity) (mul_pos hα0 (pow_pos hθ0 _)).le, hd0, hdt,
    weightedRow_vacC d hθ0 hα0.le,
    Eventually.of_forall fun _ => dobCompareW1_bounded _ _ hD d hθ0 hθ1 hα0 hα1 hd0 hdt⟩

end Vacuity

/-- DERIVED: `0` the distance to itself. -/
theorem snorm_self (a : ISite) : snorm (a - a) = 0 := by
  rw [sub_self]
  exact Nat.le_zero.mp (snorm_le_iff.mpr fun i => by simp)

/-- The sup-distance triangle inequality. DERIVED: no numeral. -/
theorem snorm_tri (a b c : ISite) : snorm (c - a) ≤ snorm (b - a) + snorm (c - b) := by
  rw [snorm_le_iff]
  intro i
  have h1 := snorm_le_iff.mp (le_refl (snorm (b - a))) i
  have h2 := snorm_le_iff.mp (le_refl (snorm (c - b))) i
  simp only [Pi.sub_apply] at h1 h2 ⊢
  push_cast
  constructor <;> omega

/-- **The pinned block reading meets `ObsRegimeW` on every finite block set, at every step of `stateK`,
with no input.** DERIVED: `1/2` the `θ` and `α` of the witness; `2` the diameter of `[0, 2]`. -/
theorem obsRegimeW_blockRead_vacuous (hN : N ≠ 0) (W : ConfFlow N) (b : ℕ) (S : Finset ISite) :
    ObsRegimeW (ι := S) (Y := fun _ => Set.Icc (0 : ℝ) 2) hN W (fun _ V i => blockEnergyIcc hN b V i.1)
      (vacC (fun i j : S => snorm (j.1 - i.1)) (1 / 2) (1 / 2))
      (vacQ (fun i j : S => snorm (j.1 - i.1)) (1 / 2) (1 / 2) 2)
      (fun i j => snorm (j.1 - i.1)) (1 / 2) (1 / 2) :=
  obsRegimeW_of_bounded hN W _ (fun _ u v => dist_Icc_le u v) _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun _ => snorm_self _) (fun i k j => snorm_tri _ _ _)

/-! ## 3. The form with content, and its pair piece -/

/-- **The observer's regime, uniform over block sets** (the remaining Prop): one interdependence kernel `c` on
`ℤ⁴` with weighted row `α < 1` at rate `θ < 1`, one spread `Q`, block sides `bk k ≥ 1`, and, eventually in the
step, the W1 comparison bound for the pinned block reading on every finite block set, all constants fixed
before the set and the step. DERIVED: `0`, `1` the ranges; `2` the range of the reading. -/
def ObsRegimeUnif (hN : N ≠ 0) (W : ConfFlow N) (bk : ℕ → ℕ) (c : ISite → ℝ) (Q θ α : ℝ) : Prop :=
  0 ≤ α ∧ α < 1 ∧ 0 < θ ∧ θ < 1 ∧ 0 ≤ Q ∧ (∀ k, 1 ≤ bk k) ∧ (∀ x, 0 ≤ c x) ∧
    (∀ (S : Finset ISite) (z : ISite), ∑ z' ∈ S, c (z' - z) * (θ ^ snorm (z' - z))⁻¹ ≤ α) ∧
    ∀ᶠ k in atTop, ∀ S : Finset ISite,
      DobCompareW1 (ι := S) (Y := fun _ => Set.Icc (0 : ℝ) 2) (stateK hN k)
        (fun U i => blockEnergyIcc hN (bk k) (W.V k U) i.1) (Matrix.of fun i j : S => c (j.1 - i.1)) Q

/-- The weighted row of the restricted kernel on a finite block set. DERIVED: no numeral. -/
theorem weightedRow_of_kernel {c : ISite → ℝ} {θ α : ℝ} (hc : ∀ x, 0 ≤ c x)
    (hrow : ∀ (S : Finset ISite) (z : ISite), ∑ z' ∈ S, c (z' - z) * (θ ^ snorm (z' - z))⁻¹ ≤ α)
    (S : Finset ISite) :
    WeightedRow (Matrix.of fun i j : S => c (j.1 - i.1)) (fun i j : S => snorm (j.1 - i.1)) θ α := by
  refine ⟨fun i j => hc _, fun i => ?_⟩
  have h := hrow S i.1
  simpa only [Matrix.of_apply, Finset.sum_coe_sort S (fun z' => c (z' - i.1) * (θ ^ snorm (z' - i.1))⁻¹)]
    using h

/-- **`ObsRegimeUnif` gives `ObsRegimeW` on every finite block set with the same constants.**
DERIVED: no numeral. -/
theorem obsRegimeW_of_unif {hN : N ≠ 0} {W : ConfFlow N} {bk : ℕ → ℕ} {c : ISite → ℝ} {Q θ α : ℝ}
    (h : ObsRegimeUnif hN W bk c Q θ α) (S : Finset ISite) :
    ObsRegimeW (ι := S) (Y := fun _ => Set.Icc (0 : ℝ) 2) hN W
      (fun k V i => blockEnergyIcc hN (bk k) V i.1) (Matrix.of fun i j : S => c (j.1 - i.1)) Q
      (fun i j => snorm (j.1 - i.1)) θ α := by
  obtain ⟨hα, hα1, hθ0, hθ1, hQ, -, hc, hrow, hev⟩ := h
  exact ⟨hα, hα1, hθ0, hθ1.le, hQ, fun _ => snorm_self _, fun _ _ _ => snorm_tri _ _ _,
    weightedRow_of_kernel hc hrow S, hev.mono fun _ hk => hk S⟩

/-- **Pair decay of a block reading**: Lipschitz tests of single blocks `z`, `z'` decorrelate at rate `θ` per
block of sup-distance. DERIVED: `0` the signs. -/
def PairDecay (ν : State (Cfg N)) (e : Cfg N → ISite → ℝ) (Q θ : ℝ) : Prop :=
  ∀ (z z' : ISite) (f h : ℝ → ℝ) (Lf Lh : ℝ), 0 ≤ Lf → 0 ≤ Lh →
    (∀ x y, |f x - f y| ≤ Lf * |x - y|) → (∀ x y, |h x - h y| ≤ Lh * |x - y|) →
    ∀ F H : C(Cfg N, ℝ), (∀ U, F U = f (e U z)) → (∀ U, H U = h (e U z')) →
      |stateCov ν F H| ≤ Q * Lf * Lh * θ ^ snorm (z' - z)

/-- **`ObsRegimeUnif` contains pair decay of the block reading**, eventually in the step, with
`Q/(1 − α)`. DERIVED: `1` the geometric factor. -/
theorem pairDecay_of_unif {hN : N ≠ 0} {W : ConfFlow N} {bk : ℕ → ℕ} {c : ISite → ℝ} {Q θ α : ℝ}
    (h : ObsRegimeUnif hN W bk c Q θ α) :
    ∀ᶠ k in atTop, PairDecay (stateK hN k) (blockRead W k (bk k)) (Q * (1 - α)⁻¹) θ := by
  obtain ⟨hα, hα1, hθ0, hθ1, hQ, -, hc, hrow, hev⟩ := h
  filter_upwards [hev] with k hk
  intro z z' f g Lf Lg hLf hLg hf hg F H hF hH
  set S : Finset ISite := {z, z'} with hS
  have hz : z ∈ S := by simp [hS]
  have hz' : z' ∈ S := by simp [hS]
  set iz : S := ⟨z, hz⟩
  set iz' : S := ⟨z', hz'⟩
  let fS : (∀ _ : S, Set.Icc (0 : ℝ) 2) → ℝ := fun y => f (y iz)
  let gS : (∀ _ : S, Set.Icc (0 : ℝ) 2) → ℝ := fun y => g (y iz')
  let Lv : S → ℝ := fun i => if i = iz then Lf else 0
  let Lw : S → ℝ := fun i => if i = iz' then Lg else 0
  have hLv : ∀ i, 0 ≤ Lv i := fun i => by simp only [Lv]; split_ifs <;> simp [hLf]
  have hLw : ∀ i, 0 ≤ Lw i := fun i => by simp only [Lw]; split_ifs <;> simp [hLg]
  have hfS : BlockLip fS Lv := by
    intro j y y' hyy
    by_cases hj : j = iz
    · subst hj
      simp only [Lv, fS, if_pos rfl]
      rw [Subtype.dist_eq, Real.dist_eq]
      exact hf _ _
    · simp only [Lv, fS, if_neg hj, zero_mul]
      rw [hyy iz (Ne.symm hj), sub_self, abs_zero]
  have hgS : BlockLip gS Lw := by
    intro j y y' hyy
    by_cases hj : j = iz'
    · subst hj
      simp only [Lw, gS, if_pos rfl]
      rw [Subtype.dist_eq, Real.dist_eq]
      exact hg _ _
    · simp only [Lw, gS, if_neg hj, zero_mul]
      rw [hyy iz' (Ne.symm hj), sub_self, abs_zero]
  have hcs := coarse_cov_sep (dist := fun i j : S => snorm (j.1 - i.1)) hθ0 hθ1.le hα hα1
    (fun _ => snorm_self _) (fun _ _ _ => snorm_tri _ _ _) (weightedRow_of_kernel hc hrow S) hQ (hk S)
    (f := fS) (h := gS) (F := F) (H := H) (fun U => hF U) (fun U => hH U) hLv hLw hfS hgS
    (A := {iz}) (B := {iz'}) (r := snorm (z' - z))
    (fun i hi => by
      rw [Finset.mem_singleton] at hi
      simp only [Lv, if_neg hi])
    (fun j hj => by
      rw [Finset.mem_singleton] at hj
      simp only [Lw, if_neg hj])
    (fun i hi j hj => by
      rw [Finset.mem_singleton] at hi hj
      subst hi; subst hj
      exact le_rfl)
  have hsv : ∑ i, Lv i = Lf := by simp [Lv]
  have hsw : ∑ i, Lw i = Lg := by simp [Lw]
  rw [hsv, hsw] at hcs
  calc |stateCov (stateK hN k) F H| ≤ Q * (θ ^ snorm (z' - z) * (1 - α)⁻¹ * (Lf * Lg)) := hcs
    _ = Q * (1 - α)⁻¹ * Lf * Lg * θ ^ snorm (z' - z) := by ring

/-! ## 4. The strong-coupling witness of the pair piece -/

/-- The links based in `c + [−R, R]⁴`. DERIVED: `4` the dimension. -/
def cbox (c : ISite) (R : ℕ) : Finset ILink :=
  (Finset.univ : Finset (Fin 4)) ×ˢ Fintype.piFinset (fun i => Finset.Icc (c i - R) (c i + R))

/-- DERIVED: no numeral. -/
theorem mem_cbox {c : ISite} {R : ℕ} {l : ILink} : l ∈ cbox c R ↔ snorm (l.2 - c) ≤ R := by
  rw [snorm_le_iff]
  simp only [cbox, Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset, Finset.mem_Icc,
    Pi.sub_apply]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

/-- `|cbox c R| = 4 (2R + 1)⁴`. DERIVED: `4` the directions and the dimension; `2R + 1` the sites of
`[−R, R]`. -/
theorem card_cbox (c : ISite) (R : ℕ) : (cbox c R).card = 4 * (2 * R + 1) ^ 4 := by
  unfold cbox
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Fintype.card_piFinset]
  have h : ∀ i : Fin 4, (Finset.Icc (c i - R) (c i + R)).card = 2 * R + 1 := by
    intro i
    rw [Int.card_Icc]
    have : c i + R + 1 - (c i - R) = ((2 * R + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A link and a link of a plaquette through it are within sup-distance `1` of each other, about any centre.
DERIVED: `1` the unit step. -/
theorem snorm_sub_nbr (c : ISite) {i j : ILink} (h : j ∈ nbr i) : snorm (j.2 - c) ≤ snorm (i.2 - c) + 1 := by
  unfold nbr at h
  obtain ⟨q, hq, hj⟩ := Finset.mem_biUnion.mp h
  obtain ⟨l, hl, hli⟩ := mem_boundaryPlaqs.mp hq
  rw [Finset.mem_singleton] at hli
  rw [hli] at hl
  have hj' := List.mem_toFinset.mp hj
  rw [snorm_le_iff]
  intro m
  have h1 := ilinks_base hl m
  have h2 := ilinks_base hj' m
  have h3 := (snorm_le_iff.mp (le_refl (snorm (i.2 - c)))) m
  simp only [Pi.sub_apply] at h3 ⊢
  push_cast
  constructor <;> omega

/-- **Separated covariance at strong coupling**: `F` local on `cbox c s` within `BF` of a constant, `H` not
reading `cbox c R` and within `BH` of a constant, `s ≤ R`. DERIVED: `4 = 2 · 2` the kernel bound's `2` and the
two sides of a constant; `65536 = 2^{16}`; `1/2` the contraction rate; `1` the depth offset. -/
theorem cov_sep_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (c : ISite) {s R : ℕ} (hsR : s ≤ R)
    (F H : C(Cfg N, ℝ)) {a a' BF BH : ℝ} (hBF : 0 ≤ BF)
    (hFloc : IsLocalOn (cbox c s) ⇑F) (hFb : ∀ U, |F U - a| ≤ BF)
    (hHoff : ∀ (u : VConf (SU N) (cbox c R)) (ω : Cfg N), H (splice (cbox c R) u ω) = H ω)
    (hHb : ∀ U, |H U - a'| ≤ BH) :
    |stateCov (periodicState hN β) F H| ≤ 4 * (cbox c s).card * (1 / 2) ^ (R + 1 - s) * BF * BH := by
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
    have hXloc : IsLocalOn (cbox c s) ⇑X := fun η η' h => by rw [hXv, hXv, hFloc η η' h]
    have hsub : cbox c s ⊆ cbox c R := fun l hl => mem_cbox.mpr ((mem_cbox.mp hl).trans hsR)
    have hK := MassGap.StrongKernelNear.kernelNear_strong_explicit hN hβ (cbox c R) (cbox c s) hsub X hX1
      hXloc (fun l => R + 1 - snorm (l.2 - c))
      (fun l hl => by
        have := mt mem_cbox.mpr hl
        show R + 1 - snorm (l.2 - c) = 0
        omega)
      (fun i _ j hj => by
        have := snorm_sub_nbr c hj
        show R + 1 - snorm (i.2 - c) ≤ R + 1 - snorm (j.2 - c) + 1
        omega)
      (R + 1 - s) (fun l hl => by
        have := mem_cbox.mp hl
        show R + 1 - s ≤ R + 1 - snorm (l.2 - c)
        omega)
    have hY : ∀ (u : VConf (SU N) (cbox c R)) (ω : Cfg N), H' (splice (cbox c R) u ω) = H' ω :=
      fun u ω => by rw [hH'v, hH'v, hHoff u ω]
    have hc := cov_le_of_kernelNear hN β (cbox c R) X H' hY hH'b hK
    have hlin : stateCov (periodicState hN β) X H' = BF⁻¹ * stateCov (periodicState hN β) F H :=
      stateCov_affine _ F H BF⁻¹ a a'
    rw [hlin, abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos] at hc
    calc _ ≤ BF * (2 * BH * (2 * (cbox c s).card * (1 / 2) ^ (R + 1 - s))) := hc
      _ = _ := by ring

/-- **The step-`k` block reading is local**: it reads only links based within `b + ρ` of the block corner,
once `W.range k ≤ ρ`. DERIVED: `1` the plaquette's reach. -/
theorem blockRead_local (W : ConfFlow N) (k b ρ : ℕ) (hρ : W.range k ≤ ρ) (z : ISite) :
    IsLocalOn (cbox (fun i => (b : ℤ) * z i) (b + ρ)) (fun U : Cfg N => blockRead W k b U z) := by
  intro η η' h
  show blockEnergy b (W.V k η) z = blockEnergy b (W.V k η') z
  unfold blockEnergy
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  have hcong : ∀ l ∈ ilinks q, W.V k η l = W.V k η' l := by
    intro l hl
    obtain ⟨T, hT, hTl⟩ := W.local_V k l
    refine hTl η η' fun l' hl' => h l' (mem_cbox.mpr (snorm_le_iff.mpr fun i => ?_))
    have hq' := (Fintype.mem_piFinset.mp (Finset.mem_product.mp hq).2) i
    rw [Finset.mem_Ico] at hq'
    have h1 := ilinks_base hl i
    have h2 := abs_le.mp (hT l' hl' i)
    have h3 : (W.range k : ℤ) ≤ ρ := by exact_mod_cast hρ
    simp only [Pi.sub_apply]
    push_cast
    generalize (b : ℤ) * z i = A at hq' ⊢
    constructor <;> omega
  rw [plaqField_apply, plaqField_apply, ihol_congr q (W.V k η) (W.V k η') hcong]

/-- **Separated blocks have disjoint reads**: with `R + 1 + (b + ρ) ≤ b ‖z' − z‖∞`, the read of block `z'`
misses `cbox (b z) R`. DERIVED: `1` the strict margin. -/
theorem not_mem_cbox_of_sep {b ρ R : ℕ} {z z' : ISite} (hR : R + 1 + (b + ρ) ≤ b * snorm (z' - z))
    {l : ILink} (hl : l ∈ cbox (fun i => (b : ℤ) * z' i) (b + ρ)) :
    l ∉ cbox (fun i => (b : ℤ) * z i) R := by
  intro hl2
  rw [mem_cbox, snorm_le_iff] at hl hl2
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4)) Finset.univ_nonempty
    (fun i => ((z' - z) i).natAbs)
  have hs : snorm (z' - z) = ((z' - z) i).natAbs := hi
  have h1 := hl i
  have h2 := hl2 i
  simp only [Pi.sub_apply] at h1 h2 hs
  push_cast at h1 h2
  have hR' : (R : ℤ) + 1 + ((b : ℤ) + ρ) ≤ (b : ℤ) * (snorm (z' - z) : ℤ) := by exact_mod_cast hR
  rw [hs] at hR'
  have hD : (b : ℤ) * z' i - (b : ℤ) * z i = (b : ℤ) * (z' i - z i) := by ring
  rcases Int.natAbs_eq (z' i - z i) with he | he
  · rw [← he, ← hD] at hR'
    generalize (b : ℤ) * z' i = A' at h1 hR'
    generalize (b : ℤ) * z i = A at h2 hR'
    omega
  · have e2 : (((z' i - z i).natAbs : ℕ) : ℤ) = -(z' i - z i) := by linarith
    rw [e2, mul_neg, ← hD] at hR'
    generalize (b : ℤ) * z' i = A' at h1 hR'
    generalize (b : ℤ) * z i = A at h2 hR'
    omega

/-- The spread constant of the strong-coupling witness, `16 (2(b + ρ) + 1)⁴ 2^{2(b + ρ)}`.
DERIVED: `16 = 4 · 4` the kernel factor and the directions; `2` the box side and the depth shift. -/
def strongQ (b ρ : ℕ) : ℝ := 16 * (2 * ((b : ℝ) + ρ) + 1) ^ 4 * 2 ^ (2 * (b + ρ))

/-- **Block covariances decay at strong coupling**, uniformly in the block positions.
DERIVED: `65536 = 2^{16}`; `1/2` the contraction rate; `1` the centre of `[0, 2]`; `2` the depth shift. -/
theorem blockCov_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (W : ConfFlow N) (k b ρ : ℕ)
    (hρ : W.range k ≤ ρ) (z z' : ISite) {f h : ℝ → ℝ} {Lf Lh : ℝ} (hLf : 0 ≤ Lf) (hLh : 0 ≤ Lh)
    (hf : ∀ x y, |f x - f y| ≤ Lf * |x - y|) (hh : ∀ x y, |h x - h y| ≤ Lh * |x - y|)
    (F H : C(Cfg N, ℝ)) (hF : ∀ U, F U = f (blockRead W k b U z)) (hH : ∀ U, H U = h (blockRead W k b U z')) :
    |stateCov (periodicState hN β) F H| ≤ strongQ b ρ * Lf * Lh * ((1 / 2 : ℝ) ^ b) ^ snorm (z' - z) := by
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
    have hc := cov_sep_strong hN hβ (fun i => (b : ℤ) * z i) hsR F H (a := f 1) (a' := h 1) hLf
      (fun η η' hη => by rw [hF, hF]; exact congrArg f (blockRead_local W k b ρ hρ z η η' hη)) hFb
      (fun u ω => by
        rw [hH, hH]
        exact congrArg h (blockRead_local W k b ρ hρ z' _ _ fun l hl =>
          splice_not_mem (not_mem_cbox_of_sep hRsep hl)))
      hHb
    have he : b * snorm (z' - z) = (R + 1 - (b + ρ)) + 2 * (b + ρ) := by omega
    have h22 : (2 : ℝ) ^ (2 * (b + ρ)) * (1 / 2) ^ (2 * (b + ρ)) = 1 := by
      rw [← mul_pow]; norm_num
    have hp : (1 / 2 : ℝ) ^ (R + 1 - (b + ρ)) = 2 ^ (2 * (b + ρ)) * (1 / 2) ^ (b * snorm (z' - z)) := by
      rw [he, pow_add, mul_left_comm, h22, mul_one]
    calc |stateCov (periodicState hN β) F H|
        ≤ 4 * (cbox (fun i => (b : ℤ) * z i) (b + ρ)).card * (1 / 2) ^ (R + 1 - (b + ρ)) * Lf * Lh := hc
      _ = strongQ b ρ * Lf * Lh * (1 / 2) ^ (b * snorm (z' - z)) := by
          rw [card_cbox, hp]
          unfold strongQ
          push_cast
          ring
  · have hc := cov_le_of_near_const (periodicState hN β) F (H - h 1 • (1 : C(Cfg N, ℝ))) hFb
      (fun U => by
        simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
          mul_one]
        exact hHb U)
    rw [stateCov_sub_const_right] at hc
    have hge : 1 ≤ (2 : ℝ) ^ (2 * (b + ρ)) * (1 / 2) ^ (b * snorm (z' - z)) := by
      have h1 : (1 / 2 : ℝ) ^ (2 * (b + ρ)) ≤ (1 / 2) ^ (b * snorm (z' - z)) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ (2 * (b + ρ)) * (1 / 2) ^ (2 * (b + ρ)) = 1 := by
        rw [← mul_pow]; norm_num
      calc (1 : ℝ) = _ := h2.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hP : (1 : ℝ) ≤ (2 * ((b : ℝ) + ρ) + 1) ^ 4 := one_le_pow₀ (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b), (Nat.cast_nonneg ρ : (0 : ℝ) ≤ ρ)])
    have hLL : 0 ≤ Lf * Lh := mul_nonneg hLf hLh
    have hprod : 1 ≤ (2 * ((b : ℝ) + ρ) + 1) ^ 4 * ((2 : ℝ) ^ (2 * (b + ρ)) * (1 / 2) ^ (b * snorm (z' - z))) :=
      one_le_mul_of_one_le_of_one_le hP hge
    calc |stateCov (periodicState hN β) F H| ≤ 2 * Lh * Lf := hc
      _ ≤ 16 * ((2 * ((b : ℝ) + ρ) + 1) ^ 4 * ((2 : ℝ) ^ (2 * (b + ρ)) * (1 / 2) ^ (b * snorm (z' - z))))
            * (Lf * Lh) := by nlinarith
      _ = strongQ b ρ * Lf * Lh * (1 / 2) ^ (b * snorm (z' - z)) := by unfold strongQ; ring

/-- **The strong-coupling witness of the pair piece.** DERIVED: `65536 = 2^{16}`; `1/2` the contraction
rate. -/
theorem pairDecay_strong (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (W : ConfFlow N) (k b ρ : ℕ)
    (hρ : W.range k ≤ ρ) :
    PairDecay (periodicState hN β) (blockRead W k b) (strongQ b ρ) ((1 / 2 : ℝ) ^ b) :=
  fun z z' _ _ _ _ hLf hLh hf hh F H hF hH => blockCov_strong hN hβ W k b ρ hρ z z' hLf hLh hf hh F H hF hH

/-- **The witness at every step of the constant tower.** DERIVED: as `pairDecay_strong`: `65536 = 2^{16}`;
`1/2` the contraction rate. -/
theorem pairDecay_strong_along (hN : N ≠ 0) {β : ℝ} (hβ : |β| ≤ 1 / 65536) (W : ConfFlow N) (b ρ : ℕ)
    (hρ : ∀ k, W.range k ≤ ρ) (k : ℕ) :
    PairDecay (MassGap.ContinuumSchwinger.stateAlong hN (fun _ => β) k) (blockRead W k b) (strongQ b ρ)
      ((1 / 2 : ℝ) ^ b) :=
  pairDecay_strong hN hβ W k b ρ (hρ k)

/-- The rate of the witness is below `1` at every block side `b ≥ 1`. DERIVED: `1/2`, `1`. -/
theorem strong_rate_lt_one {b : ℕ} (hb : 1 ≤ b) : (1 / 2 : ℝ) ^ b < 1 :=
  pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

/-- **The tower `stateK` leaves the strong-coupling range**: eventually in the step, `|dyBeta k| > 2^{-16}`.
DERIVED: `65536 = 2^{16}`; `1` the least colour count. -/
theorem stateK_not_strong (h1 : 1 ≤ N) :
    ∀ᶠ k in atTop, 1 / 65536 < |MassGap.ContinuumSchwinger.dyBeta h1 k| :=
  ((MassGap.ContinuumSchwinger.tendsto_dyBeta h1).eventually_gt_atTop (1 / 65536)).mono
    fun _ hk => lt_of_lt_of_le hk (le_abs_self _)

/-! ## 5. The bridge to block-smeared readings -/

/-- **Pair decay gives decay of block-smeared readings**: weights on block sets `A`, `B` at block distance
`≥ r` give `|Cov| ≤ Q θ^r (Σ|w|)(Σ|w'|)`. DERIVED: `1` the Lipschitz constant of the identity. -/
theorem smearedCov_le {ν : State (Cfg N)} {e : Cfg N → ISite → ℝ} {Q θ : ℝ} (hP : PairDecay ν e Q θ)
    (hQ : 0 ≤ Q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (E : ISite → C(Cfg N, ℝ)) (hE : ∀ z U, E z U = e U z)
    (A B : Finset ISite) (w w' : ISite → ℝ) {r : ℕ} (hsep : ∀ z ∈ A, ∀ z' ∈ B, r ≤ snorm (z' - z)) :
    |stateCov ν (∑ z ∈ A, w z • E z) (∑ z' ∈ B, w' z' • E z')|
      ≤ Q * θ ^ r * ((∑ z ∈ A, |w z|) * ∑ z' ∈ B, |w' z'|) := by
  rw [stateCov_sum]
  have hpt : ∀ z ∈ A, ∀ z' ∈ B,
      |w z * w' z' * stateCov ν (E z) (E z')| ≤ |w z| * |w' z'| * (Q * θ ^ r) := by
    intro z hz z' hz'
    have h1 := hP z z' id id 1 1 zero_le_one zero_le_one (fun x y => by simp) (fun x y => by simp)
      (E z) (E z') (hE z) (hE z')
    have h2 : θ ^ snorm (z' - z) ≤ θ ^ r := pow_le_pow_of_le_one hθ0 hθ1 (hsep z hz z' hz')
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc |stateCov ν (E z) (E z')| ≤ Q * 1 * 1 * θ ^ snorm (z' - z) := h1
      _ ≤ Q * θ ^ r := by rw [mul_one, mul_one]; exact mul_le_mul_of_nonneg_left h2 hQ
  calc _ ≤ ∑ z ∈ A, |∑ z' ∈ B, w z * w' z' * stateCov ν (E z) (E z')| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ A, ∑ z' ∈ B, |w z| * |w' z'| * (Q * θ ^ r) :=
        Finset.sum_le_sum fun z hz =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z' hz' => hpt z hz z' hz')
    _ = Q * θ ^ r * ((∑ z ∈ A, |w z|) * ∑ z' ∈ B, |w' z'|) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z' _ => ?_
        ring

end MassGap.ObserverBlockReading

#print axioms MassGap.ObserverBlockReading.stateCov_affine
#print axioms MassGap.ObserverBlockReading.stateCov_sub_const_right
#print axioms MassGap.ObserverBlockReading.stateCov_sum
#print axioms MassGap.ObserverBlockReading.volDist_triangle
#print axioms MassGap.ObserverBlockReading.blockEnergy_lip
#print axioms MassGap.ObserverBlockReading.blockEnergy_mem
#print axioms MassGap.ObserverBlockReading.blockRead_gauge
#print axioms MassGap.ObserverBlockReading.blockRead_separates
#print axioms MassGap.ObserverBlockReading.blockRead_nonconst
#print axioms MassGap.ObserverBlockReading.dobCompareW1_bounded
#print axioms MassGap.ObserverBlockReading.obsRegimeW_of_bounded
#print axioms MassGap.ObserverBlockReading.obsRegimeW_blockRead_vacuous
#print axioms MassGap.ObserverBlockReading.obsRegimeW_of_unif
#print axioms MassGap.ObserverBlockReading.pairDecay_of_unif
#print axioms MassGap.ObserverBlockReading.card_cbox
#print axioms MassGap.ObserverBlockReading.cov_sep_strong
#print axioms MassGap.ObserverBlockReading.blockRead_local
#print axioms MassGap.ObserverBlockReading.not_mem_cbox_of_sep
#print axioms MassGap.ObserverBlockReading.blockCov_strong
#print axioms MassGap.ObserverBlockReading.pairDecay_strong
#print axioms MassGap.ObserverBlockReading.pairDecay_strong_along
#print axioms MassGap.ObserverBlockReading.strong_rate_lt_one
#print axioms MassGap.ObserverBlockReading.stateK_not_strong
#print axioms MassGap.ObserverBlockReading.smearedCov_le
