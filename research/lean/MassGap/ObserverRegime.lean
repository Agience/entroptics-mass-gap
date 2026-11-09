import Mathlib
import MassGap.BlockLipschitz
import MassGap.EdgeCost
import MassGap.ContinuumFlow

/-!
# MassGap.ObserverRegime — the observer's input shape: its own law at its own scale

`ExpandFam.clayStatement_of_narrowAtMinF` takes about ten inputs; one of them, `ObserverRunSeed.ObsRunSeedW`,
carries the gap. This module asks which single statement about the observer would make it work when the observer
is an object inside the substrate: a map `U ↦ R_k (W.V k U)` from the fine configuration to a coarse field, whose
law is the pushforward of the same Wilson state `stateK k`. Two kinds of observer are treated: a coarse one (a
block reading of the flowed configuration at one physical size `b`) and a fine one (a Higgs-like frame field at
the lattice scale). Declarations are in the namespace `MassGap.ObserverRegime`.

## 1. The coarse shape: Dobrushin's comparison bound in W1 form (defined; decay proved)

Blocks `ι` (a fixed finite type), block data `Y b` with a metric, the coarse field `χ : X → ∀ b, Y b`. Tests are
measured by per-block Lipschitz vectors (`BlockLipschitz.BlockLip`).
* `DobCompareW1 ν χ C Q`: for every pair of block tests `f`, `h` with Lipschitz vectors `Lf`, `Lh ≥ 0`,
  `|Cov_ν(f ∘ χ, h ∘ χ)| ≤ Q Σ_{i,j} Lf_i D_{ij} Lh_j`, `D = Σ_{n ≥ 0} Cⁿ` (`tsum`), `Q ≥ 0` a spread constant
  (a bound on the conditional second moments in the block metric). This is the conclusion of Dobrushin's
  comparison theorem in Kantorovich form when `C` is the W1 interdependence matrix of the coarse field's
  conditional laws (`C_{ij}` bounds the W1 distance of the conditional laws of block `i` per unit of block-`j`
  distance) and the row condition holds. **The comparison theorem itself is assumed here, not proved**:
  `DobCompareW1` is the hypothesis, and the identification of `C` with the coarse field's W1 interdependence
  matrix is argued, not formalised. The archive proves the finite-specification theorems:
  `DobrushinGeneral.cov_spatialS` (total variation, `SU(N)` spins), `DobrushinUnbounded.cov_spatialS` (total
  variation, general spins), `DobrushinW1.cov_spatialW` (W1, real interval spins, with a second-moment factor) and
  `ObserverEnergyCellCondW.cov_spatialWW` (W1 with a weighted row, the `CondW1RowW` form); none is in the live tree.
* **The total-variation form fails for flowed blocks** (argued). With `Y b` the gauge class of the flowed
  configuration on block `b`, the flowed field is smooth on its flow scale, which is many lattice spacings at large
  step; the conditional laws of a block for two different data on a face-sharing neighbour are then nearly
  mutually singular, so the TV entry tends to `1` for every face neighbour and the row sum is at least `8`. The TV
  row condition fails eventually at every `b`, the standard failure of TV Dobrushin for continuous
  high-dimensional block spins. The W1 form is used for that reason.
* `WeightedRow C dist θ α`: `C ≥ 0` and `Σ_j C_{ij} θ^{−dist(i,j)} ≤ α` at every block, for a block distance
  `dist : ι → ι → ℕ` with `dist(i,i) = 0` and the triangle inequality, and `0 < θ ≤ 1`.
* `pow_entry_le`: `0 ≤ (Cⁿ)_{ij} ≤ αⁿ θ^{dist(i,j)}`. `tsum_pow_entry_le`: `D_{ij} ≤ θ^{dist(i,j)}/(1 − α)`.
  `sum_sep_le`: the comparison sum of vectors on `A`, `B` at block distance at least `r` is at most
  `θ^r/(1 − α) · (Σ v)(Σ w)`. These are matrix facts, independent of the metric.
* **`coarse_cov_sep`**: tests whose Lipschitz vectors live on `A`, `B` at block distance at least `r` have
  `|Cov| ≤ Q θ^r/(1 − α) · (Σ Lf)(Σ Lh)`. The separation is geometric (block distance), not a free predicate.
* `ObsRegimeW hN W R C Q dist θ α`: `0 ≤ α < 1`, `Q ≥ 0`, `WeightedRow`, and eventually in the step
  `DobCompareW1 (stateK hN k) (R k ∘ W.V k) C Q`, with one block set, one `C`, `Q`, `θ` for every step.
  `ι` is a fixed finite set, so reaching a physical distance `d` needs a family of these over growing boxes with
  `C`, `Q`, `θ`, `α` uniform, and the eventually-in-the-step threshold may depend on the box. With `R` the flowed
  block gauge classes (§4 item 1; not fixed by the predicate) that is the form the gap clause reads, which takes
  the step to the limit pair by pair. With `R` free it holds at a constant reading
  (`ObserverOneInput.obsRegimeW_const`); on one fixed `ι` it holds for every bounded reading, with `Q` of order
  `|ι| θ^{−Σ dist}` (`ObserverBlockReading.obsRegimeW_of_bounded`), so its content lies only in a family over
  block sets with `Q`, `θ`, `α`, `C` fixed before the set (`ObserverBlockReading.ObsRegimeUnif`).
* **`obsRegimeW_cov`**: eventually in the step, the separated bound with constants fixed before the step (on one `ι`; the
  constants may depend on `ι`).
  `exp_shells_le` turns `r ≥ d/b − 1` shells of physical size `b` into `e^{κ} e^{−(κ/b) d}` (`θ = e^{−κ}`), a mass
  `κ/b` in physical units; `abs_le_of_tendsto` carries an eventual bound to a limit along any non-trivial filter
  (the continuum readings `contSF` are such limits).

## 2. A recorded no-go: the exact-screen form (proved)

* `ExactScreen ν χ K Far`: one operator `K` with `Cov(g ∘ χ, h) = Cov((K^[n] g) ∘ χ, h)` exactly, for every block
  test `g` and every `h` with `Far n h`. `ScreenRegime`: `ExactScreen` with `LipInfl K C`, `DobCond C α`.
* **`coarse_cov_eq_zero`**: under `ScreenRegime` with `α < 1`, every covariance with a `Far n` reading, `n ≥ 1`,
  is exactly `0` (iterate the screen `m` times; the bound `αⁿᵐ` tends to `0`). So that form is either vacuous
  (`Far` empty) or false at every correlated reading (free massive field, Wilson). The conditional expectation
  given the coarse field outside a shell depends on where `g` and `h` live and the coarse field is not Markov, so
  no single `K` exists; the comparison form of §1 replaces it.

## 3. What the coarse shape reaches (argued, except where named)

| bundle clause | reached? |
|---|---|
| gap (`ObsRunSeedW`, the role `FlowCapstone.FlowClusterAbs` plays in `ObserverReads`) | in form, argued: `FlowClusterAbs` is decay of the continuum connected kernel of margin monomials of the observer's flowed energy class at physical time separation `d`, one rate, constants free per pair. If the block datum `Y b` is the gauge class of the flowed configuration on block `b` with a volume-averaged metric (§4 item 1) and `b` is at least the flow's physical range, a smeared flowed monomial on a fixed physical region is Lipschitz on a fixed number of blocks with constants set by the smearing, and `obsRegimeW_cov`, over block sets with constants fixed before the set (`ObserverBlockReading.ObsRegimeUnif`; on one block set every bounded reading meets the predicate), with `abs_le_of_tendsto` gives the bound at rate `κ/b`. The reader step is not built. The TV form of the comparison cannot serve here (§1: its row sum is at least `8` for face-sharing flowed blocks). The gap on the whole Hilbert space also needs the coarse readings to be cyclic, which is the generation clause (`GenerationCyclic.ObserverCyclicCL`) |
| `ClusterPM`, `PointCluster` | no: tree-graph cumulant bounds at every flow scale `0 < s ≤ θc d`, `d ≤ 1`, with `s^{−λ}` factors; scales below `b` are not block tests with bounded oscillation vectors, and the bounds there are ultraviolet statements |
| `FinMom b Wf` | only for `s` at or above the block scale; `FinMom` asks every `s ∈ (0, b]` |
| `ExpandRF`, `FlowAF`, `FlowWard`, `FlowCovLim`, `ProxyNondeg` | no: short-distance (`s → 0`) statements |
| `FlowThreeLower` | no: the comparison bound is an upper bound on connected functions, never a lower bound |
| generation clause | no: a fixed-scale coarse observer does not generate the fine composites |

So the coarse shape replaces at most the gap clause. It does not imply most of the bundle.

## 4. Circularity and tests (argued)

1. **Not the conclusion; the gap at one scale, given a block datum that contracts.** `WeightedRow` is a
   condition on the W1 interdependence of the coarse field's conditional laws, blocks of physical size `~ b`, a sup
   over the conditioning configurations. Through the comparison theorem it implies decay at every distance. The
   gap (`ObserverReads.cluster_of_clayStatementAt`) does not imply it: a uniform bound over conditioning
   configurations is stronger than decay in the one infinite-volume state. Reading it as a finite-size mass
   criterion at scale `b`, uniformly in `β`, needs a block datum and metric for which the true W1 interdependence
   is a contraction; **that is the open point**. The choice of metric decides it. In the max-plaquette (sup)
   metric the layer of block `i` next to a face responds to a change of the neighbour's data by an amount of order
   that change, so `C_{ij}` is of order `1` per face neighbour and the row fails. In a volume-averaged metric (mean
   plaquette distance over the block) a massive theory with correlation length `ξ ≪ b` confines the response to a
   layer of thickness `~ ξ`, so `C_{ij} ≈ c ξ/b` and the row is `≈ 8 c ξ/b < 1` at large `b`; the tests must then
   be smeared over physical regions, since a single-plaquette test has Lipschitz constant `~ (b/a_k)⁴` in that
   metric, a quantity that grows with the step. The localisation of the response to a layer of thickness `ξ` is
   the mass itself, and the conditioning on the coarse field alone is non-Markov (the fine variables inside the
   blocks carry influence), so the W1 form is plausible at large `b` for a massive theory and is not derived:
   not circular as logic, and as hard as the mass at that scale.
2. **Growing-quantity test: fails on one block set, passes in form only uniformly over block sets.** `C`, `θ`,
   `α` and the block type are fixed before the step, but `Q` may follow `ι`, and every bounded reading meets the
   predicate with `Q` of order `|ι| θ^{−Σ dist}` (`ObserverBlockReading.obsRegimeW_of_bounded`). With `Q`, `θ`,
   `α` and a translation-invariant kernel fixed before the block set (`ObserverBlockReading.ObsRegimeUnif`), the
   prefactor counts blocks, a physical count, not fine sites. The fine-site sweep (`StrongKernelNear`) fails the
   same test: its row sum tends to `18` as `β → ∞`.
3. **Free field: the row sum only.** For a Gaussian field the block influence is the linear response, and the box
   average of the summed influence is the escape probability of the killed walk
   (`research/code/lab/ds_unit.py`): `1` when massless at every size, `≈ 5–6/(m b)` when massive. That is the
   row-sum diagnostic, not a check of `DobCompareW1` or of the weighted row for the Gaussian coarse field; on it, the
   row sum falls below `1` only when the field has a mass and `m b` is large.
4. **Weak coupling: expected only beyond the correlation length.** At `b` well below `1/m` the coarse theory is
   weakly coupled (asymptotic freedom), the coarse field responds linearly to its neighbours and the row is that of
   the massless Gaussian, `≈ 1`; the photon filter (`BlockLipschitz.not_contract_of_shift`) excludes a
   contraction for U(1) at every `b`. At `b` many correlation lengths the coarse theory is strongly coupled and
   `α < 1` is the expected regime. "The observer is strongly coupled at its own scale" is the statement that its
   scale is beyond the crossover; proving it uniformly in `β` is the crossover problem (`BlockLipschitz` §4
   items 4–6).

## 5. The fine shape: a Higgs-like frame built from the gauge field (proved)

A frame field built from `U` alone, covariant under the local gauge group, is what a Laplacian-gauge
(Vink–Wiese) or Landau frame would supply.
* `igauge_const_of_central`: a constant central gauge function fixes every configuration.
* **`covariant_fundamental_eq_zero`** (`N ≥ 2`): every map `φ : Cfg N → (sites → ℂᴺ)` with
  `φ(g·U)_x = g_x φ(U)_x` is identically `0`. The centre `ω · 1`, `ω = e^{2πi/N}`, fixes every configuration and
  multiplies every fundamental vector by `ω ≠ 1`. A fundamental frame (the lowest eigenvectors of the covariant
  Laplacian) is defined only up to a phase and is not a function of `U`.
* **`covariant_adjoint_trivial_commutes`**, **`covariant_adjoint_trivial_scalar`**: every map
  `Φ : Cfg N → (sites → Mat_N)` with `Φ(g·U)_x = g_x Φ(U)_x g_x*` takes a scalar value at the trivial
  configuration. An adjoint frame picks no direction at the classical vacuum. Argued from this: by continuity it
  picks none near it, and at weak coupling the field at the lattice scale is near pure gauge, so a lattice-scale
  frame's direction is fixed by fluctuations; a frame that carries a direction lives beyond the correlation length,
  a coarse object again, and "the frame has a finite correlation length" is clustering of the non-local
  gauge-invariant composites `Ω_x⁻¹ U Ω_y`: circular.
* **An auxiliary Higgs field** (argued). In a gauge–Higgs model `φ` is a variable of the measure, so
  `covariant_fundamental_eq_zero` does not apply. The convergent expansions cover the Higgs region (large `κ`) and
  the strong-coupling region (small `β`), connected for a fundamental Higgs (Fradkin–Shenker,
  Osterwalder–Seiler); the decoupling limit `κ → 0` at `β → ∞` lies in neither, and it is the pure gauge problem
  itself. An adjoint Higgs (Georgi–Glashow) has a massless Coulomb phase, so a property an adjoint observer has
  there cannot imply the gap.

## 6. The coarse shape and where its content lies

`ObsRegimeW`, with the block reading `R` a given argument, to be the gauge classes of the flowed blocks (the
predicate does not fix it, and it holds at a constant reading, `ObserverOneInput.obsRegimeW_const`): the weighted
Dobrushin row of the coarse field's W1 interdependence matrix at one physical block
scale `b` beyond the crossover, in a volume-averaged block metric, with the W1 comparison bound assumed. The TV
form is excluded for face-sharing flowed blocks (§1). Proved here: it gives geometric decay of coarse covariances
in block distance, uniformly in the step, on one block set with constants that may depend on it; on one block
set it holds for every bounded reading (`ObserverBlockReading.obsRegimeW_of_bounded`), so alone it has no
content. The form with content fixes `Q`, `θ`, `α` and the kernel before the block set
(`ObserverBlockReading.ObsRegimeUnif`); its pair piece is proved only at strong coupling
(`ObserverBlockReading.pairDecay_strong`). Open: a block datum and metric whose true W1 interdependence contracts
(§4 item 1). Argued: in the uniform form it passes the growing-quantity test for physically smeared tests and the
U(1) filter excludes it where it must; its free-field check is the row-sum diagnostic only; it reaches the gap
clause given cyclicity and the reader step; it reaches none of the short-distance clauses. The fine frame either
is not a function of `U` (fundamental), carries no direction at the vacuum (adjoint), or changes the theory
(auxiliary Higgs).

DERIVED (module-wide): `0` the signs, the zero vector and the diagonal distance; `1` the trivial configuration,
the identity power, the bound on `θ` and `α` and the shell offset; `2` the two sides of a constant and the least
colour count; `4` in `Fin 4` the spacetime dimension.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ObserverRegime

open Filter
open MassGap.DLRLimit (State)
open MassGap.FocusZoom (stateCov)
open MassGap.BoxFocusTest (cov_le_of_near_const)
open MassGap.CoarseBoundary (BlockOsc)
open MassGap.BlockDobrushin (DobCond)
open MassGap.BlockLipschitz (BlockLip LipInfl lip_near_const)
open MassGap.SUN (SU)
open MassGap.ContinuumSchwinger (Cfg stateK)
open MassGap.ContinuumFlow (ConfFlow)
open MassGap.GaugeInvariantAlgebra (igaugeTransform)

/-! ## 1. The comparison form -/

section Compare

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The weighted Dobrushin row**: `C ≥ 0` and `Σ_j C_{ij} θ^{−dist(i,j)} ≤ α` at every block.
DERIVED: `0` the sign. -/
def WeightedRow (C : Matrix ι ι ℝ) (dist : ι → ι → ℕ) (θ α : ℝ) : Prop :=
  (∀ i j, 0 ≤ C i j) ∧ ∀ i, ∑ j, C i j * (θ ^ dist i j)⁻¹ ≤ α

/-- **Powers of the interdependence matrix decay in block distance**: `0 ≤ (Cⁿ)_{ij} ≤ αⁿ θ^{dist(i,j)}`.
DERIVED: `0` the diagonal distance and the sign; `1` the identity power and the bound on `θ`. -/
theorem pow_entry_le {C : Matrix ι ι ℝ} {dist : ι → ι → ℕ} {θ α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hα : 0 ≤ α) (hd0 : ∀ i, dist i i = 0) (hdt : ∀ i k j, dist i j ≤ dist i k + dist k j)
    (hW : WeightedRow C dist θ α) : ∀ (n : ℕ) (i j : ι), 0 ≤ (C ^ n) i j ∧ (C ^ n) i j ≤ α ^ n * θ ^ dist i j := by
  intro n
  induction n with
  | zero =>
    intro i j
    rw [pow_zero, pow_zero, one_mul]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, hd0, pow_zero]; exact ⟨zero_le_one, le_rfl⟩
    · rw [Matrix.one_apply_ne hij]; exact ⟨le_rfl, pow_nonneg hθ0.le _⟩
  | succ n ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    refine ⟨Finset.sum_nonneg fun k _ => mul_nonneg (hW.1 i k) (ih k j).1, ?_⟩
    have key : ∀ k, C i k * (C ^ n) k j ≤ α ^ n * θ ^ dist i j * (C i k * (θ ^ dist i k)⁻¹) := by
      intro k
      have hpos : 0 < θ ^ dist i k := pow_pos hθ0 _
      have htri : θ ^ dist i k * θ ^ dist k j ≤ θ ^ dist i j := by
        rw [← pow_add]; exact pow_le_pow_of_le_one hθ0.le hθ1 (hdt i k j)
      have hkj : θ ^ dist k j ≤ θ ^ dist i j * (θ ^ dist i k)⁻¹ := by
        rw [le_mul_inv_iff₀ hpos, mul_comm]; exact htri
      calc C i k * (C ^ n) k j ≤ C i k * (α ^ n * θ ^ dist k j) :=
            mul_le_mul_of_nonneg_left (ih k j).2 (hW.1 i k)
        _ ≤ C i k * (α ^ n * (θ ^ dist i j * (θ ^ dist i k)⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkj (pow_nonneg hα _)) (hW.1 i k)
        _ = α ^ n * θ ^ dist i j * (C i k * (θ ^ dist i k)⁻¹) := by ring
    calc ∑ k, C i k * (C ^ n) k j ≤ ∑ k, α ^ n * θ ^ dist i j * (C i k * (θ ^ dist i k)⁻¹) :=
          Finset.sum_le_sum fun k _ => key k
      _ = α ^ n * θ ^ dist i j * ∑ k, C i k * (θ ^ dist i k)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ α ^ n * θ ^ dist i j * α :=
          mul_le_mul_of_nonneg_left (hW.2 i) (mul_nonneg (pow_nonneg hα _) (pow_nonneg hθ0.le _))
      _ = α ^ (n + 1) * θ ^ dist i j := by ring

/-- **The comparison matrix decays in block distance**: `Σ_n (Cⁿ)_{ij} ≤ θ^{dist(i,j)}/(1 − α)`.
DERIVED: `1` the geometric series. -/
theorem tsum_pow_entry_le {C : Matrix ι ι ℝ} {dist : ι → ι → ℕ} {θ α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hα : 0 ≤ α) (hα1 : α < 1) (hd0 : ∀ i, dist i i = 0) (hdt : ∀ i k j, dist i j ≤ dist i k + dist k j)
    (hW : WeightedRow C dist θ α) (i j : ι) :
    ∑' n, (C ^ n) i j ≤ θ ^ dist i j * (1 - α)⁻¹ := by
  have hb := pow_entry_le hθ0 hθ1 hα hd0 hdt hW
  have hg : Summable fun n : ℕ => α ^ n * θ ^ dist i j :=
    (summable_geometric_of_lt_one hα hα1).mul_right _
  have hs : Summable fun n : ℕ => (C ^ n) i j :=
    Summable.of_nonneg_of_le (fun n => (hb n i j).1) (fun n => (hb n i j).2) hg
  calc ∑' n, (C ^ n) i j ≤ ∑' n : ℕ, α ^ n * θ ^ dist i j :=
        Summable.tsum_le_tsum (fun n => (hb n i j).2) hs hg
    _ = θ ^ dist i j * (1 - α)⁻¹ := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hα hα1, mul_comm]

/-- **The separated comparison sum**: vectors supported on `A` and `B` at block distance at least `r` give
`Σ_{i,j} v_i (Σ_n Cⁿ)_{ij} w_j ≤ θ^r/(1 − α) · (Σ v)(Σ w)`. DERIVED: `0` the vectors off the supports. -/
theorem sum_sep_le {C : Matrix ι ι ℝ} {dist : ι → ι → ℕ} {θ α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hα : 0 ≤ α) (hα1 : α < 1) (hd0 : ∀ i, dist i i = 0) (hdt : ∀ i k j, dist i j ≤ dist i k + dist k j)
    (hW : WeightedRow C dist θ α) {vf vh : ι → ℝ} (hvf : ∀ i, 0 ≤ vf i) (hvh : ∀ j, 0 ≤ vh j)
    {A B : Finset ι} {r : ℕ} (hA : ∀ i, i ∉ A → vf i = 0) (hB : ∀ j, j ∉ B → vh j = 0)
    (hsep : ∀ i ∈ A, ∀ j ∈ B, r ≤ dist i j) :
    ∑ i, ∑ j, vf i * (∑' n, (C ^ n) i j) * vh j ≤ θ ^ r * (1 - α)⁻¹ * ((∑ i, vf i) * ∑ j, vh j) := by
  have hc0 : 0 ≤ (1 - α)⁻¹ := inv_nonneg.mpr (by linarith)
  have hterm : ∀ i j, vf i * (∑' n, (C ^ n) i j) * vh j ≤ vf i * (θ ^ r * (1 - α)⁻¹) * vh j := by
    intro i j
    by_cases hi : i ∈ A
    · by_cases hj : j ∈ B
      · have h1 := tsum_pow_entry_le hθ0 hθ1 hα hα1 hd0 hdt hW i j
        have h2 : θ ^ dist i j ≤ θ ^ r := pow_le_pow_of_le_one hθ0.le hθ1 (hsep i hi j hj)
        have h3 : ∑' n, (C ^ n) i j ≤ θ ^ r * (1 - α)⁻¹ :=
          h1.trans (mul_le_mul_of_nonneg_right h2 hc0)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (hvf i)) (hvh j)
      · rw [hB j hj, mul_zero, mul_zero]
    · rw [hA i hi]; simp
  calc ∑ i, ∑ j, vf i * (∑' n, (C ^ n) i j) * vh j
      ≤ ∑ i, ∑ j, vf i * (θ ^ r * (1 - α)⁻¹) * vh j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = θ ^ r * (1 - α)⁻¹ * ((∑ i, vf i) * ∑ j, vh j) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- **Dobrushin's comparison bound in Kantorovich (W1) form for a coarse field** (the hypothesis): every pair of
block tests with Lipschitz vectors `Lf`, `Lh ≥ 0` in the block metrics has
`|Cov(f ∘ χ, h ∘ χ)| ≤ Q Σ_{i,j} Lf_i (Σ_n Cⁿ)_{ij} Lh_j`, `Q ≥ 0` a fixed spread constant.
DERIVED: `0` the sign. -/
def DobCompareW1 {X : Type*} [TopologicalSpace X] [CompactSpace X] {Y : ι → Type*}
    [∀ b, PseudoMetricSpace (Y b)] (ν : State X) (χ : X → ∀ b, Y b) (C : Matrix ι ι ℝ) (Q : ℝ) : Prop :=
  ∀ (f h : (∀ b, Y b) → ℝ) (F H : C(X, ℝ)), (∀ x, F x = f (χ x)) → (∀ x, H x = h (χ x)) →
    ∀ (Lf Lh : ι → ℝ), (∀ i, 0 ≤ Lf i) → (∀ j, 0 ≤ Lh j) → BlockLip f Lf → BlockLip h Lh →
      |stateCov ν F H| ≤ Q * ∑ i, ∑ j, Lf i * (∑' n, (C ^ n) i j) * Lh j

/-- **Separated coarse tests decorrelate geometrically**: Lipschitz vectors on `A` and `B` at block distance
at least `r` give `|Cov| ≤ Q θ^r/(1 − α) · (Σ Lf)(Σ Lh)`. DERIVED: `0` the vectors off the supports. -/
theorem coarse_cov_sep {X : Type*} [TopologicalSpace X] [CompactSpace X] {Y : ι → Type*}
    [∀ b, PseudoMetricSpace (Y b)] {ν : State X} {χ : X → ∀ b, Y b} {C : Matrix ι ι ℝ} {Q : ℝ}
    {dist : ι → ι → ℕ} {θ α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hα : 0 ≤ α) (hα1 : α < 1)
    (hd0 : ∀ i, dist i i = 0) (hdt : ∀ i k j, dist i j ≤ dist i k + dist k j)
    (hW : WeightedRow C dist θ α) (hQ : 0 ≤ Q) (hD : DobCompareW1 ν χ C Q) {f h : (∀ b, Y b) → ℝ}
    {F H : C(X, ℝ)} (hF : ∀ x, F x = f (χ x)) (hH : ∀ x, H x = h (χ x)) {Lf Lh : ι → ℝ}
    (hLf : ∀ i, 0 ≤ Lf i) (hLh : ∀ j, 0 ≤ Lh j) (hf : BlockLip f Lf) (hh : BlockLip h Lh)
    {A B : Finset ι} {r : ℕ} (hA : ∀ i, i ∉ A → Lf i = 0) (hB : ∀ j, j ∉ B → Lh j = 0)
    (hsep : ∀ i ∈ A, ∀ j ∈ B, r ≤ dist i j) :
    |stateCov ν F H| ≤ Q * (θ ^ r * (1 - α)⁻¹ * ((∑ i, Lf i) * ∑ j, Lh j)) :=
  (hD f h F H hF hH Lf Lh hLf hLh hf hh).trans
    (mul_le_mul_of_nonneg_left (sum_sep_le hθ0 hθ1 hα hα1 hd0 hdt hW hLf hLh hA hB hsep) hQ)

end Compare

/-- **Shells to physical distance**: `n ≥ d/b − 1` shells of physical size `b` give
`e^{−κ n} ≤ e^{κ} e^{−(κ/b) d}`. DERIVED: `1` the shell offset. -/
theorem exp_shells_le {κ b d : ℝ} (hκ : 0 ≤ κ) (hb : 0 < b) {n : ℕ} (hn : d / b - 1 ≤ n) :
    Real.exp (-(κ * n)) ≤ Real.exp κ * Real.exp (-(κ / b * d)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : κ * (d / b - 1) ≤ κ * n := mul_le_mul_of_nonneg_left hn hκ
  have h2 : κ * (d / b - 1) = κ / b * d - κ := by field_simp
  linarith

/-- **An eventual bound passes to the limit** along any non-trivial filter. DERIVED: no numeral. -/
theorem abs_le_of_tendsto {α : Type*} {l : Filter α} [l.NeBot] {x : α → ℝ} {y B : ℝ}
    (hx : Tendsto x l (nhds y)) (hB : ∀ᶠ k in l, |x k| ≤ B) : |y| ≤ B :=
  le_of_tendsto ((continuous_abs.tendsto y).comp hx) hB

/-! ## 2. The observer's regime on the Wilson family -/

section Observer

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ b, PseudoMetricSpace (Y b)]

/-- **The observer's regime**: one finite block set `ι` with block metrics, one W1 interdependence bound `C` of
weighted row `α < 1` in one block distance, one spread constant `Q ≥ 0`, and, eventually in the step, the W1
comparison bound for the coarse field `R k ∘ W.V k` under `stateK hN k`.
DERIVED: `0`, `1` the ranges of `α` and `θ`; `0` the diagonal distance and the sign of `Q`. -/
def ObsRegimeW (hN : N ≠ 0) (W : ConfFlow N) (R : ℕ → Cfg N → ∀ b, Y b) (C : Matrix ι ι ℝ) (Q : ℝ)
    (dist : ι → ι → ℕ) (θ α : ℝ) : Prop :=
  0 ≤ α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ Q ∧ (∀ i, dist i i = 0) ∧
    (∀ i k j, dist i j ≤ dist i k + dist k j) ∧ WeightedRow C dist θ α ∧
      ∀ᶠ k in atTop, DobCompareW1 (stateK hN k) (fun U => R k (W.V k U)) C Q

/-- **The observer's separated coarse covariances decay geometrically, uniformly in the step.**
DERIVED: `0` the vectors off the supports. -/
theorem obsRegimeW_cov {hN : N ≠ 0} {W : ConfFlow N} {R : ℕ → Cfg N → ∀ b, Y b} {C : Matrix ι ι ℝ}
    {Q : ℝ} {dist : ι → ι → ℕ} {θ α : ℝ} (hO : ObsRegimeW hN W R C Q dist θ α) :
    ∀ᶠ k in atTop, ∀ (f h : (∀ b, Y b) → ℝ) (F H : C(Cfg N, ℝ)), (∀ U, F U = f (R k (W.V k U))) →
      (∀ U, H U = h (R k (W.V k U))) → ∀ (Lf Lh : ι → ℝ), (∀ i, 0 ≤ Lf i) → (∀ j, 0 ≤ Lh j) →
        BlockLip f Lf → BlockLip h Lh → ∀ (A B : Finset ι) (r : ℕ), (∀ i, i ∉ A → Lf i = 0) →
          (∀ j, j ∉ B → Lh j = 0) → (∀ i ∈ A, ∀ j ∈ B, r ≤ dist i j) →
            |stateCov (stateK hN k) F H| ≤ Q * (θ ^ r * (1 - α)⁻¹ * ((∑ i, Lf i) * ∑ j, Lh j)) := by
  obtain ⟨hα, hα1, hθ0, hθ1, hQ, hd0, hdt, hW, hev⟩ := hO
  filter_upwards [hev] with k hk f h F H hF hH Lf Lh hLf hLh hf hh A B r hA hB hsep
  exact coarse_cov_sep hθ0 hθ1 hα hα1 hd0 hdt hW hQ hk hF hH hLf hLh hf hh hA hB hsep

end Observer

/-! ## 3. The exact-screen form: a no-go -/

section Screen

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ b, PseudoMetricSpace (Y b)]

/-- **The exact screen**: one operator `K` with `Cov(g ∘ χ, h) = Cov((K^[n] g) ∘ χ, h)` for every block test
`g` and every `h` with `Far n h`. DERIVED: no numeral. -/
def ExactScreen (ν : State X) (χ : X → ∀ b, Y b) (K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ))
    (Far : ℕ → C(X, ℝ) → Prop) : Prop :=
  ∀ (g : (∀ b, Y b) → ℝ) (G : C(X, ℝ)), (∀ x, G x = g (χ x)) → ∀ (n : ℕ) (h : C(X, ℝ)), Far n h →
    ∃ F : C(X, ℝ), (∀ x, F x = K^[n] g (χ x)) ∧ stateCov ν G h = stateCov ν F h

/-- **The exact screen with a Lipschitz-Dobrushin kernel.** DERIVED: no numeral. -/
def ScreenRegime (ν : State X) (χ : X → ∀ b, Y b) (Far : ℕ → C(X, ℝ) → Prop) (α : ℝ) : Prop :=
  ∃ (K : ((∀ b, Y b) → ℝ) → ((∀ b, Y b) → ℝ)) (C : ι → ι → ℝ),
    LipInfl K C ∧ DobCond C α ∧ ExactScreen ν χ K Far

/-- **The exact screen forces exact decorrelation**: under `ScreenRegime` with `α < 1`, every covariance of a
block test with a `Far n` reading, `n ≥ 1`, is `0`. DERIVED: `0` the covariance; `1` the least shell count;
`2` the two sides of a constant. -/
theorem coarse_cov_eq_zero {ν : State X} {χ : X → ∀ b, Y b} {Far : ℕ → C(X, ℝ) → Prop} {α V D M : ℝ}
    (hR : ScreenRegime ν χ Far α) (hα : 0 ≤ α) (hα1 : α < 1) (hV0 : 0 ≤ V) (hD0 : 0 ≤ D)
    (hDiam : ∀ b (u v : Y b), dist u v ≤ D) {g : (∀ b, Y b) → ℝ} {L : ι → ℝ} (hL : ∀ j, 0 ≤ L j)
    (hLV : ∀ j, L j ≤ V) (hg : BlockLip g L) {G : C(X, ℝ)} (hG : ∀ x, G x = g (χ x)) {n : ℕ}
    (hn : 1 ≤ n) {h : C(X, ℝ)} (hFar : Far n h) (hM : ∀ x, |h x| ≤ M) :
    stateCov ν G h = 0 := by
  obtain ⟨K, C, hK, hDC, hS⟩ := hR
  have hit : ∀ m : ℕ, ∃ F : C(X, ℝ), (∀ x, F x = K^[m * n] g (χ x)) ∧
      stateCov ν G h = stateCov ν F h := by
    intro m
    induction m with
    | zero => exact ⟨G, fun x => by simpa using hG x, rfl⟩
    | succ m ih =>
      obtain ⟨F, hF, hc⟩ := ih
      obtain ⟨F', hF', hc'⟩ := hS (K^[m * n] g) F hF n h hFar
      refine ⟨F', fun x => ?_, hc.trans hc'⟩
      rw [hF', ← Function.iterate_add_apply, Nat.succ_mul, Nat.add_comm]
  have hb : ∀ m : ℕ, |stateCov ν G h| ≤ 2 * M * (Fintype.card ι * ((α ^ n) ^ m * V) * D) := by
    intro m
    obtain ⟨F, hF, hc⟩ := hit m
    obtain ⟨c, hcc⟩ := lip_near_const hK hDC hα hV0 hD0 hDiam hL hLV hg (m * n)
    rw [hc, ← pow_mul, Nat.mul_comm]
    exact cov_le_of_near_const ν F h (fun x => by rw [hF]; exact hcc _) hM
  have ht : Tendsto (fun m : ℕ => 2 * M * (Fintype.card ι * ((α ^ n) ^ m * V) * D)) atTop (nhds 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hα n)
      (pow_lt_one₀ hα hα1 (by omega))
    have := ((h0.mul_const V).const_mul (Fintype.card ι : ℝ)).mul_const D |>.const_mul (2 * M)
    simpa using this
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto' ht hb) (abs_nonneg _))

end Screen

/-! ## 4. The fine shape: frames built from the gauge field -/

section Frame

variable {N : ℕ}

/-- **A constant central gauge function fixes every configuration.** DERIVED: no numeral. -/
theorem igauge_const_of_central (z : SU N) (hz : ∀ g : SU N, z * g = g * z) (U : Cfg N) :
    igaugeTransform (fun _ => z) U = U := by
  funext l
  show z * U l * z⁻¹ = U l
  rw [hz, mul_inv_cancel_right]

/-- **No fundamental frame is a function of the gauge field** (`N ≥ 2`): a gauge-covariant fundamental field
built from `U` alone vanishes identically. DERIVED: `2` the least colour count; `0` the zero vector; `4` the
spacetime dimension. -/
theorem covariant_fundamental_eq_zero (hN : 2 ≤ N) (φ : Cfg N → (Fin 4 → ℤ) → (Fin N → ℂ))
    (hφ : ∀ (g : (Fin 4 → ℤ) → SU N) (U : Cfg N) (x : Fin 4 → ℤ),
      φ (igaugeTransform g U) x = Matrix.mulVec (g x : Matrix (Fin N) (Fin N) ℂ) (φ U x))
    (U : Cfg N) (x : Fin 4 → ℤ) : φ U x = 0 := by
  have hN0 : N ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp N hN0
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  have hne : ω ≠ 1 := hprim.ne_one (by omega)
  let z : SU N := ⟨ω • (1 : Matrix (Fin N) (Fin N) ℂ), EdgeCost.scalar_mem_SU hN0 hprim.pow_eq_one⟩
  have hz : ∀ g : SU N, z * g = g * z := fun g => Subtype.ext (by
    show (ω • (1 : Matrix (Fin N) (Fin N) ℂ)) * (g : Matrix (Fin N) (Fin N) ℂ)
      = (g : Matrix (Fin N) (Fin N) ℂ) * (ω • (1 : Matrix (Fin N) (Fin N) ℂ))
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one])
  have h := hφ (fun _ => z) U x
  rw [igauge_const_of_central z hz U] at h
  have h2 : φ U x = ω • φ U x := h.trans (EdgeCost.scalar_fundamental (N := N) ω (φ U x))
  have h0 : (ω - 1) • φ U x = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
  exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)

/-- **An adjoint frame commutes with every group element at the trivial configuration.** DERIVED: `1` the
trivial configuration; `4` the spacetime dimension. -/
theorem covariant_adjoint_trivial_commutes
    (Φ : Cfg N → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (hΦ : ∀ (g : (Fin 4 → ℤ) → SU N) (U : Cfg N) (x : Fin 4 → ℤ),
      Φ (igaugeTransform g U) x
        = (g x : Matrix (Fin N) (Fin N) ℂ) * Φ U x * star (g x : Matrix (Fin N) (Fin N) ℂ))
    (x : Fin 4 → ℤ) : NonAbelianForget.Commutes (Φ (fun _ => 1) x) := by
  intro A hA
  have h1 : igaugeTransform (fun _ => (⟨A, hA⟩ : SU N)) (fun _ => (1 : SU N)) = fun _ => 1 := by
    funext l
    show (⟨A, hA⟩ : SU N) * 1 * (⟨A, hA⟩ : SU N)⁻¹ = 1
    rw [mul_one, mul_inv_cancel]
  have h := hΦ (fun _ => ⟨A, hA⟩) (fun _ => 1) x
  rw [h1] at h
  have hu : star A * A = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp hA).1
  calc A * Φ (fun _ => 1) x = A * Φ (fun _ => 1) x * (star A * A) := by rw [hu, mul_one]
    _ = (A * Φ (fun _ => 1) x * star A) * A := (mul_assoc (A * Φ (fun _ => 1) x) (star A) A).symm
    _ = Φ (fun _ => 1) x * A := by rw [← h]

/-- **An adjoint frame is scalar at the trivial configuration**: it picks no direction at the classical
vacuum (`NonAbelianForget.commutant_SU`). DERIVED: `1` the trivial configuration; `0` the off-diagonal
entries; `4` the spacetime dimension. -/
theorem covariant_adjoint_trivial_scalar
    (Φ : Cfg N → (Fin 4 → ℤ) → Matrix (Fin N) (Fin N) ℂ)
    (hΦ : ∀ (g : (Fin 4 → ℤ) → SU N) (U : Cfg N) (x : Fin 4 → ℤ),
      Φ (igaugeTransform g U) x
        = (g x : Matrix (Fin N) (Fin N) ℂ) * Φ U x * star (g x : Matrix (Fin N) (Fin N) ℂ))
    (x : Fin 4 → ℤ) :
    (∀ i j, i ≠ j → Φ (fun _ => 1) x i j = 0) ∧ ∀ p q, Φ (fun _ => 1) x p p = Φ (fun _ => 1) x q q :=
  NonAbelianForget.commutant_SU (covariant_adjoint_trivial_commutes Φ hΦ x)

end Frame

end MassGap.ObserverRegime

#print axioms MassGap.ObserverRegime.pow_entry_le
#print axioms MassGap.ObserverRegime.tsum_pow_entry_le
#print axioms MassGap.ObserverRegime.sum_sep_le
#print axioms MassGap.ObserverRegime.coarse_cov_sep
#print axioms MassGap.ObserverRegime.obsRegimeW_cov
#print axioms MassGap.ObserverRegime.exp_shells_le
#print axioms MassGap.ObserverRegime.abs_le_of_tendsto
#print axioms MassGap.ObserverRegime.coarse_cov_eq_zero
#print axioms MassGap.ObserverRegime.igauge_const_of_central
#print axioms MassGap.ObserverRegime.covariant_fundamental_eq_zero
#print axioms MassGap.ObserverRegime.covariant_adjoint_trivial_commutes
#print axioms MassGap.ObserverRegime.covariant_adjoint_trivial_scalar
