import Mathlib
import MassGap.FineLinks
import MassGap.GaugeRunning

/-!
# MassGap.BalabanUV — a Bałaban-type hypothesis for the ultraviolet flow, and what follows from it

The owner's crossover reads "zoomed in it is fine, zoomed out it is coarse, one fixed length `r*`
between". Part 1 is the ultraviolet side: block-spin renormalisation of 4D `SU(N)` lattice gauge
theory keeps the effective action local and stable, with the effective coupling following the
asymptotically free running. That is Bałaban's programme (Commun. Math. Phys. 95, 96 (1984); 98, 99,
102 (1985); 109 (1987); 116 (1988); 119 (1988); 122 (1989)). This module states a hypothesis of that
type on the tree's objects, `BalabanShape`, proves what follows from it, and names what each consumer
still needs. **`BalabanShape` is not Bałaban's statement**: it is a compression of the shape of his
output, in places stronger than what he proved (section 2), and has not been checked against CMP
109, 122. Nothing here proves it. Declarations live in the namespace `MassGap.BalabanFlow`.

## 1. The ladder and its effective densities (proved)

* `Ladder G`: lattices `sys j : LatticeGauge.System G` (`j` block steps above the finest) and block maps
  `blk j : (sys j).Config → (sys (j+1)).Config`. `blkTo j` is the composite of the first `j` of them.
  The block map is a parameter: Bałaban's averaging operation (CMP 98) is not constructed in the tree,
  and `BlockLattice.blockConf` (`SU(2)`, on the infinite `IConf`) is a different map.
* `gibbs μ β` is the unnormalised Wilson–Gibbs measure on the finest lattice; `effLaw μ β j` its image
  under `blkTo j`, the law of the field after `j` steps. `effLaw_zero`; `effLaw_succ`: the law after
  `j+1` steps is the image of the law after `j` under one block map.
* `IsEffDensity sys μ law ρ`: `law = (vol μ).withDensity ρ`, `ρ ≥ 0` measurable. `isEffDensity_zero`:
  at `j = 0` the density is the Wilson weight `boltz β`.
* `effFibre sys κ₀ ρ = κ₀ · ρ`, the fibre measure weighted by an effective density; `fibreGibbs` of
  `CondGap` is `effFibre` at `ρ = boltz β` (`fibreGibbs_eq_effFibre`). `effFibre_disintegrates`: with
  `κ₀` the conditional Haar measure given a block map, `effFibre` disintegrates the law with density
  `ρ`. So the conditional law of the level-`j` field given the level-`(j+1)` block field is the fibre
  measure weighted by the level-`j` effective density: `CondGap`'s fibre Gibbs measure with the bare
  Wilson weight replaced by the effective density at the current scale.

## 2. The hypothesis (`IsBackground`, `ShapeStep`, `BalabanShape`)

`SmallField sys thr V`: every plaquette has `φ(hol p V) ≤ thr`; `largeCount sys thr V` the number of
plaquettes above `thr`.

`IsBackground B dom bg`: on `dom`, `bg V` lies on the fibre `{B U = V}` and minimises the fine action
there, so `A(bg V) = min_{B U = V} A(U)` is fixed by `B`. `BalabanShape` asks for such a `bg`
(`∃ bg`), so it **assumes** the minimiser exists. `B (bg V) = V` makes `blkTo j` onto the
small-field region, a condition on `Ladder.blk` that the ladder does not state. Existence would follow
from compact configuration spaces, continuous `φ`, `hol` and `B`, and that surjectivity; none of
these is in the tree for a general `Ladder`. The identification with Bałaban's background field
(the variational problem of CMP 102), and the claims that `A(bg V)` is non-local in `V` and differs
from the coarse Wilson action `S(V)` by order `p(g)²` per block (so that the difference cannot be
carried by polymers with `|R X| ≤ e^{−κ|X|}`), are recalled, not proved here.

`ShapeStep sys fine μ law bg βe thr ℓ κ σR E`: the law has an effective density `ρ` with a
normalisation `Z > 0`, a finite polymer family `P` of link sets and activities `R X` such that

* (small field) `ρ V = Z exp(−βe A(bg V) − Σ_{X ∈ P} R X V)` on `SmallField V`, `A` the action of
  the fine lattice;
* (locality) `R X V` depends only on `V` restricted to `X`;
* (decay) `|R X V| ≤ e^{−κ |X|}` for `X ∈ P` at small-field `V`, and the local sum
  `Σ_{X ∈ P, X ∋ l} e^{−κ|X|} ≤ σR` at every link `l` (the volume-uniform summability that
  connectedness plus decay gives; stated directly because `System` carries no geometry);
* (large field) `ρ V ≤ Z exp(−ℓ · largeCount V + E · #links)` everywhere. The slack `E · #links` is
  extensive, so the bound suppresses `ρ` below `Z` only where `largeCount ≥ (E/ℓ) · #links`; for a
  few large plaquettes in a big volume it says little.

`isBackground_id`, `shapeStep_zero`: the bare Wilson measure satisfies the shape at the finest scale
with background `id`, `βe = β`, `P = ∅`, `ℓ ≤ β thr`, for `φ ≥ 0`. So the shape is consistent there
and its content lies at `j ≥ 1`.

`BalabanShape lad steps μ β₀ nrm b₀ logL gmax` (`lad n` the ladder at zoom `n`, `steps n` block
steps of factor `L = e^{logL}` from the finest lattice, bare coupling `β₀ n`, `gmax` the smallness
bound of the window): there are `κ > 0`, `σR, E, Crun ≥ 0` with `Crun ḡ² < 2 b₀ logL`,
`0 < ḡ² ≤ gmax`, a first zoom `n₀`, functions `thr, ℓ, η` and constants `thrMax`, `ℓMin > 0`,
`ηMax < 1` with, **uniformly on `(0, ḡ²]`**, `0 ≤ thr ≤ thrMax`, `ℓ ≥ ℓMin`, `0 ≤ η ≤ ηMax`, and
`thr → 0`, `ℓ → ∞`, `η → 0` as `g² → 0⁺`, all independent of `n` (uniform in the spacing), such that
at every zoom `n ≥ n₀` there are couplings `g_j²` and backgrounds `bg j` with `g_0² = nrm/β₀ n`,
`0 < g_j² ≤ ḡ²` for `j ≤ steps n` (the bare coupling and the whole run lie in the window),
`OneLoopStep b₀ logL Crun`, and at every `j ≤ steps n`: `IsBackground (blkTo j)` on the small-field
region at `thr(g_j²)`; the law after `j` steps non-zero, and **locally** for every plaquette `p` the
event `φ(hol p V) > thr(g_j²)` has mass at most `η(g_j²)` times the total; and `ShapeStep` at
`βe = nrm/g_j²`, `thr(g_j²)`, `ℓ(g_j²)`. The uniform bounds keep every step in the window
non-trivial (no step can take `thr < 0`, `η ≥ 1` or `ℓ ≤ 0`), and the per-plaquette bound with
`ηMax < 1` makes the small field at each plaquette carry mass `≥ (1 − ηMax)` of the total; it is a
local statement, not the global rarity of large fields, which fails in large volume. `BalabanShapeSU`:
the `SU(N)` instance with `nrm = N` (the tree's Lean coupling `β = N/g²`, `gSq_lean_SU`) and
`b₀ = GaugeRunning.b0G`.

`BalabanShape` is a hypothesis about a **given** family of ladders. `∃ lad, BalabanShape lad …` is
trivial (for instance with lattices that have no plaquettes), so a consumer must fix `lad` to the
intended instance.

**Where `BalabanShape` is stronger than the published statements** (as recalled; to be checked
against CMP 109, 122):

* Bałaban's effective density is a sum over large-field regions produced at earlier scales, with
  characteristic functions; `ShapeStep` asserts one exact small-field identity with no such sum.
* His local large-field control comes from that region expansion, each large-field cube costing
  `e^{−c p(g)²}`; `BalabanShape` asserts a per-plaquette large-field probability `≤ η(g²)` directly.
* His large-field suppression is `e^{−c p(g_k)²}` per large-field cube with `p(g) = (−log g)^{p₀}`,
  inside that sum; `ShapeStep` asserts one pointwise large-field bound with the same `Z`.
* His polymer decay is in a tree length `d_k(X)` of connected polymers; `ShapeStep` asserts
  `e^{−κ|X|}` and a per-link sum `σR`, a stand-in for the summability that connectedness gives.
* His background `U_k(V)` is defined for regular small fields after gauge fixing; `IsBackground`
  asks for a minimiser of the fine action on the fibre of the composite block map.
* His coupling recursion has the one-loop coefficient with corrections he bounds; `OneLoopStep`
  asks for an `O(g_j²)` per-step error (the form the two-loop running gives, `oneLoop_of_twoLoop`),
  which is stronger than bounded corrections.

## 3. Consequences proved from the shape

* `polymer_osc`: for two configurations that differ only on the links of `D`, the polymer sums differ
  by at most `2 |D| σR`. Polymers not meeting `D` are the same at both (locality).
* `ShapeStep.cell` (**the action comparison on one cell**): at two small-field configurations that
  agree off `D`, `ρ U = ρ U' · exp(−βe (A(bg U) − A(bg U')) + h)` with `|h| ≤ 2 |D| σR`. So on one
  fibre the effective density is the background weight at the effective coupling times a factor
  within `e^{±2|D|σR}`.
* `ratio_of_weights` (finite form): weights `w = E w₀ e^{h}` on a set `S`, `|h| ≤ θ`, give
  `w/Z ≤ e^{2θ} w₀/A₀` and `(A/Z)(w₀/A₀) ≤ e^{2θ} w/Z` on `S` (`Z = Σ w`, `A`, `A₀` the masses of `S`).
  The fibre-constant factor `E` (the coarse-field-dependent part) drops out.
* `marg`, `largeMarg`, `dens_of_config`, `nearFree_of_config`: pointwise bounds `lo p₀ ≤ p ≤ hi p₀`
  on the small configurations of a finite configuration space give, for the two-slice laws
  (marginals through the slice pair `q`), `|J − J₀| ≤ max(hi − 1, 1 − lo) J₀ + L` with `L` the
  two-slice marginal of `p + p₀` on the large configurations: `FineLinks.NearFree` once `L` has
  relative weight `ε` on the readings.
* `cell_corrW_le`, `cell_rate_of_action`: with the free reference rate `2 − √3` on a layer closed under
  constants and `max(hi − 1, 1 − lo) + ε ≤ κ̄ ≤ 1/4`, `4κ̄ < √3 − 1`, the true two-slice law has rate
  `2 − √3 + 4κ̄ < 1`, depending on `κ̄` only, so uniform in the zoom and the block field when `κ̄` is.
  `exists_c_stepCorr`: on a realised fibre this is `CondGap.StepCorr` at `e^{−c}`, `c > 0`.
* `nearFree_of_density`, `corrW_along_zoom`, `corrW_uniform_along_zoom` (**link (2), density form**):
  observer two-slice laws `J_k` on one fixed finite observer space with `|J_{k+1} − J_k| ≤ δ_k J_k`,
  `δ_k ≤ 1/4`, have rate `r_{K₀} + 4 Σ_{K₀ ≤ j < k} δ_j` at zoom `k` while that is `≤ 1`; with
  `Σ δ_j ≤ D` the rate is `r_{K₀} + 4D` at every zoom.
* `oneLoop_of_twoLoop`, `invCoupling_drop`, `window_steps_le`: under `OneLoopStep` in the window,
  `g_0⁻² − g_k⁻²` lies between `k (2 b₀ logL ∓ Crun ḡ²)`. With `Crun ḡ² < 2 b₀ logL` (a clause of
  `BalabanShape`; a hypothesis of `window_steps_le`) the number of steps in the window is at most
  `(g_0⁻² − ḡ⁻²)/(2 b₀ logL − Crun ḡ²)`, so `O(g_0⁻²)`. `window_steps_le` is the upper bound only;
  that the window actually spans `~ g_0⁻²/(2 b₀ logL)` steps (the dimensional transmutation of
  `EdgeCost.rStar` in step form) needs also a lower bound on the final coupling and is not proved.
* `window_not_strong`: `g² ≤ ḡ²` and the explicit assumption `ḡ² < 20 N` give the Lean coupling
  `N/g² > 1/20`. The value `1/20` is the threshold of the cited strong-coupling clustering (Wilson,
  Lean `β ≤ 1/20`) that `ApertureInvariance.dyBeta_not_strong` also reads; that clustering is not
  proved in the tree. So it is never in force at a step `j ≤ steps n`, `n ≥ n₀`, of `BalabanShape`
  when `ḡ² < 20N`.

## 4. What the consumers still need

* **`BalabanShape` itself** for the intended ladders, including the uniform constraints on `thr`,
  `ℓ`, `η` and the per-plaquette large-field bound; the existence of the background minimiser and the
  surjectivity of `blkTo j` onto the small-field region; and a block map defined on all
  configurations: Bałaban's averaging is defined on regular, small fields with gauge fixing, while
  `Ladder.blk` is a total map.
* **CondGap input (i) / `FineLinks.NearFree`.** From `ShapeStep.cell` the remaining inputs are:
  (a) the background part of `h` on the small-field fibre, `βe (A(bg U) − A(bg U'))` against the
  quadratic form of the axially gauge-fixed free field around the fibre minimiser, bounded by `θ_W`
  uniformly; (b) `2|D|σR + θ_W` small enough that `max(hi − 1, 1 − lo) + ε ≤ κ̄` with
  `4κ̄ < √3 − 1` — `BalabanShape` gives `σR` bounded, not small;
  (c) the free reference rate `2 − √3` on the gauge-invariant new-mode layer of the gauge field
  (`CondGap` section 4 computes it for the scalar); (d) the relative large-field weight `ε` on the
  readings, which the large-field bound gives only through a sup ratio (`FineLinks.large_of_sup₀`,
  infinite for an `L²` layer); (e) a finite realisation of the fibre measures (`CondGap.Realises`),
  absent for continuous `SU(N)` links.
* **Link (2), the summable observer-law flow.** `corrW_along_zoom` needs `Σ_k δ_k < ∞` for the change
  of the observer's coarse law between consecutive zooms. `BalabanShape` gives bounds uniform in the
  spacing at every zoom, not a Cauchy estimate between zooms: ultraviolet stability is compactness of
  the effective theories, not convergence. So `δ_k` summable is not a consequence of `BalabanShape`.
* **Part (A) of `OneBridge`** (`FineLinks.relFloorM_box_of_splits`) needs the `SplitM` data of every
  refinement step of the Wilson box slabs: the isometry `ι`, the layer, `η`, `δ`, `r_W` on `L²(Haar)`.
  None of these is built from `BalabanShape` here; the theorems above give `r_W` in finite form and a
  density form of link (2), not the `L²` objects of `SplitM`.
* **The crossover at `r*`.** `BalabanShape` speaks only about the steps `j ≤ steps n` at zooms
  `n ≥ n₀`, all with `0 < g_j² ≤ ḡ²` (weak coupling).
  `window_not_strong` shows those steps never reach the strong-coupling window where the tree had
  clustering. The steps from `ḡ` to strong coupling are not covered by any statement here.

DERIVED (module-wide): `0` the sign of every density, weight and bound; `1` the normalisation `Z = 1`
of the bare step, the bound `ρ ≤ 1` of a rate and `1 ≤ hi`; `2` the two configurations in the
oscillation `2|D|σR`, the `L²` exponent, the `2θ` of a ratio of two normalised weights and the `2` of
`2 b₀ logL` (`d g⁻²/d log μ = 2 b₀ + 2 b₁ g² + …`); `4` and `1/4` the slope and window of
`FineLinks.nearFreeRate_le`; `2 − √3` the free per-step factor of `CondGap`; `20` the inverse of the
cited strong-coupling threshold `1/20` (as in `ApertureInvariance.dyBeta_not_strong`).
-/

noncomputable section

open scoped Classical

namespace MassGap.BalabanFlow

open MeasureTheory ProbabilityTheory Filter Topology GapL2
open MassGap.LatticeGauge MassGap.CondGap MassGap.FineLinks

/-! ## 1. The ladder and its effective densities -/

section Ladder

variable {G : Type} [MeasurableSpace G]

/-- **A renormalisation ladder**: lattices `sys j` (`j` block steps above the finest) and one block
map per step. The block map is a parameter. -/
structure Ladder (G : Type) [MeasurableSpace G] where
  sys : ℕ → System G
  blk : ∀ j, (sys j).Config → (sys (j + 1)).Config

namespace Ladder

/-- The composite of the first `j` block maps. -/
def blkTo (Lad : Ladder G) : ∀ j, (Lad.sys 0).Config → (Lad.sys j).Config
  | 0 => id
  | j + 1 => Lad.blk j ∘ blkTo Lad j

theorem measurable_blkTo (Lad : Ladder G) (hb : ∀ j, Measurable (Lad.blk j)) :
    ∀ j, Measurable (Lad.blkTo j)
  | 0 => measurable_id
  | j + 1 => (hb j).comp (measurable_blkTo Lad hb j)

/-- The unnormalised Wilson–Gibbs measure on the finest lattice. -/
def gibbs (Lad : Ladder G) (μ : Measure G) (β : ℝ) : Measure (Lad.sys 0).Config :=
  ((Lad.sys 0).vol μ).withDensity fun U => ENNReal.ofReal ((Lad.sys 0).boltz β U)

/-- **The law of the field after `j` block steps.** -/
def effLaw (Lad : Ladder G) (μ : Measure G) (β : ℝ) (j : ℕ) : Measure (Lad.sys j).Config :=
  (Lad.gibbs μ β).map (Lad.blkTo j)

theorem effLaw_zero (Lad : Ladder G) (μ : Measure G) (β : ℝ) : Lad.effLaw μ β 0 = Lad.gibbs μ β :=
  Measure.map_id

/-- **One more block step maps the law after `j` steps to the law after `j+1`.** -/
theorem effLaw_succ (Lad : Ladder G) (hb : ∀ j, Measurable (Lad.blk j)) (μ : Measure G) (β : ℝ)
    (j : ℕ) : Lad.effLaw μ β (j + 1) = (Lad.effLaw μ β j).map (Lad.blk j) := by
  unfold effLaw
  rw [Measure.map_map (hb j) (Lad.measurable_blkTo hb j)]
  rfl

end Ladder

/-- **An effective density**: `law = (vol μ).withDensity ρ`, `ρ ≥ 0` measurable. -/
def IsEffDensity (sys : System G) (μ : Measure G) (law : Measure sys.Config)
    (ρ : sys.Config → ℝ) : Prop :=
  Measurable ρ ∧ (∀ V, 0 ≤ ρ V) ∧ law = (sys.vol μ).withDensity fun V => ENNReal.ofReal (ρ V)

/-- **At the finest scale the effective density is the Wilson weight.** -/
theorem isEffDensity_zero (Lad : Ladder G) (μ : Measure G) (β : ℝ)
    (hb : Measurable ((Lad.sys 0).boltz β)) :
    IsEffDensity (Lad.sys 0) μ (Lad.effLaw μ β 0) ((Lad.sys 0).boltz β) :=
  ⟨hb, fun _ => (Real.exp_pos _).le, Lad.effLaw_zero μ β⟩

/-- **The fibre measure weighted by an effective density.** -/
def effFibre (sys : System G) {C : Type*} [MeasurableSpace C] (κ₀ : Kernel C sys.Config)
    [IsSFiniteKernel κ₀] (ρ : sys.Config → ℝ) : Kernel C sys.Config :=
  κ₀.withDensity fun _ U => ENNReal.ofReal (ρ U)

/-- `CondGap.fibreGibbs` is `effFibre` at the Wilson weight. -/
theorem fibreGibbs_eq_effFibre (sys : System G) {C : Type*} [MeasurableSpace C]
    (κ₀ : Kernel C sys.Config) [IsSFiniteKernel κ₀] (β : ℝ) :
    fibreGibbs sys κ₀ β = effFibre sys κ₀ (sys.boltz β) := rfl

/-- **The effective fibre measure disintegrates the effective law**: with `κ₀` a conditional
measure of the product Haar measure given the block map `B`, `effFibre sys κ₀ ρ` disintegrates the
law of density `ρ` over `B`. -/
theorem effFibre_disintegrates (sys : System G) (μ : Measure G) [IsProbabilityMeasure μ]
    {C : Type*} [MeasurableSpace C] {B : sys.Config → C} (hB : Measurable B)
    {κ₀ : Kernel C sys.Config} [IsSFiniteKernel κ₀] (h : IsCondMeasure (sys.vol μ) B κ₀)
    {law : Measure sys.Config} {ρ : sys.Config → ℝ} (hρ : IsEffDensity sys μ law ρ) :
    ((sys.vol μ).map B) ⊗ₘ effFibre sys κ₀ ρ = law.map (fun U => (B U, U)) := by
  haveI : IsProbabilityMeasure (sys.vol μ) := by unfold System.vol; infer_instance
  rw [hρ.2.2]
  unfold effFibre
  exact compProd_fibreWeight (w := fun U => ENNReal.ofReal (ρ U)) hB h.2
    (ENNReal.measurable_ofReal.comp hρ.1) fun _ => ENNReal.ofReal_ne_top

end Ladder

/-! ## 2. The statement -/

section Statement

variable {G : Type} [MeasurableSpace G]

/-- **The small-field region**: every plaquette has `φ(hol p V) ≤ thr`. -/
def SmallField (sys : System G) (thr : ℝ) (V : sys.Config) : Prop :=
  ∀ p, sys.φ (sys.hol p V) ≤ thr

/-- **The number of large-field plaquettes**, `φ(hol p V) > thr`. -/
def largeCount (sys : System G) (thr : ℝ) (V : sys.Config) : ℕ :=
  (Finset.univ.filter fun p => thr < sys.φ (sys.hol p V)).card

/-- **A background map on the small-field region**: for every small-field `V` (`dom V`), `bg V`
lies on the fibre `{B U = V}` of the composite block map and minimises the fine action there. Any two
such maps have the same action `A(bg V) = min_{B U = V} A(U)`. A map with this property need not
exist; asking for one assumes the minimiser exists and that `B` is onto `dom`. Its identification
with the background of Bałaban's variational problem (CMP 102) is recalled, not proved.
DERIVED: no constant; `102` is the volume number of the cited journal (Commun. Math. Phys.). -/
def IsBackground {fine sys : System G} (B : fine.Config → sys.Config) (dom : sys.Config → Prop)
    (bg : sys.Config → fine.Config) : Prop :=
  ∀ V, dom V → B (bg V) = V ∧ ∀ U, B U = V → fine.action (bg V) ≤ fine.action U

/-- **One scale in the shape of this module** (a hypothesis of Bałaban type, compressed; see the
module docstring for what is stronger than the published statements). The law has an effective
density `ρ`, a normalisation `Z > 0`, a polymer family `P` and activities `R` with: the small-field
representation `ρ = Z exp(−βe A(bg V) − Σ_{X ∈ P} R X)`, `A(bg V)` the fine action of the background
`bg V`; the large-field bound `ρ ≤ Z exp(−ℓ · largeCount + E · #links)`; locality of `R X`; decay
`|R X| ≤ e^{−κ|X|}` at small-field configurations; and the local sum
`Σ_{X ∈ P, X ∋ l} e^{−κ|X|} ≤ σR` at every link. -/
def ShapeStep (sys fine : System G) (μ : Measure G) (law : Measure sys.Config)
    (bg : sys.Config → fine.Config) (βe thr ℓ κ σR E : ℝ) : Prop :=
  ∃ (ρ : sys.Config → ℝ) (Z : ℝ) (P : Finset (Finset sys.Link))
    (R : Finset sys.Link → sys.Config → ℝ),
    IsEffDensity sys μ law ρ ∧ 0 < Z ∧
    (∀ V, SmallField sys thr V →
      ρ V = Z * Real.exp (-(βe * fine.action (bg V)) - ∑ X ∈ P, R X V)) ∧
    (∀ V, ρ V ≤ Z * Real.exp (-(ℓ * largeCount sys thr V) + E * Fintype.card sys.Link)) ∧
    (∀ X V V', (∀ l ∈ X, V l = V' l) → R X V = R X V') ∧
    (∀ X ∈ P, ∀ V, SmallField sys thr V → |R X V| ≤ Real.exp (-(κ * X.card))) ∧
    (∀ l, ∑ X ∈ P.filter (fun X => l ∈ X), Real.exp (-(κ * X.card)) ≤ σR)

/-- **The one-loop recursion of the effective couplings with an `O(g²)` per-step error**:
`|g_{j+1}⁻² − (g_j⁻² − 2 b₀ logL)| ≤ Crun g_j²` for `j < n`. This is the form the two-loop running
gives (`oneLoop_of_twoLoop`); it is stronger than a recursion whose corrections are only bounded. -/
def OneLoopStep (b₀ logL Crun : ℝ) (gsq : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ j < n, |(gsq (j + 1))⁻¹ - ((gsq j)⁻¹ - 2 * b₀ * logL)| ≤ Crun * gsq j

/-- **The two-loop recursion with an `O(g⁴)` per-step error**:
`|g_{j+1}⁻² − (g_j⁻² − 2 b₀ logL − 2 b₁ logL g_j²)| ≤ C₂ g_j⁴`. -/
def TwoLoopStep (b₀ b₁ logL C₂ : ℝ) (gsq : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ j < n, |(gsq (j + 1))⁻¹ - ((gsq j)⁻¹ - 2 * b₀ * logL - 2 * b₁ * logL * gsq j)|
    ≤ C₂ * gsq j ^ 2

/-- **`BalabanShape`, a hypothesis of Bałaban type** (not his statement; to be checked against CMP
109, 122). For the ladders `lad n` (zoom `n`, `steps n` block steps of factor `e^{logL}` from the
finest lattice `sys 0`, bare coupling `β₀ n`) and a smallness bound `gmax` on the coupling window:
constants `κ > 0`, `σR, E, Crun ≥ 0` with `Crun ḡ² < 2 b₀ logL`, `0 < ḡ² ≤ gmax`, a first zoom
`n₀`, functions `thr, ℓ, η` and constants `thrMax`, `ℓMin > 0`, `ηMax < 1` such that on all of
`(0, ḡ²]` `0 ≤ thr ≤ thrMax`, `ℓMin ≤ ℓ`, `0 ≤ η ≤ ηMax`, with `thr g² → 0`, `ℓ g² → ∞`,
`η g² → 0` as `g² → 0⁺`, all independent of the zoom, such that at every zoom `n ≥ n₀` there are
couplings `g_j²` and background maps `bg j` with

* `g_0² = nrm/β₀ n` and `0 < g_j² ≤ ḡ²` for `j ≤ steps n` (the bare coupling is in the window);
* `OneLoopStep b₀ logL Crun`;
* at every scale `j ≤ steps n`: `bg j` a background map of `blkTo j` on the small-field region at
  `thr (g_j²)` (assumed to exist); the law after `j` steps is non-zero and, at every plaquette `p`,
  the event `φ(hol p V) > thr (g_j²)` has mass at most `η (g_j²)` times its total mass; and
  `ShapeStep` at `βe = nrm/g_j²`, `thr (g_j²)`, `ℓ (g_j²)`.

The intended instance (finite periodic lattices of fixed physical size, Bałaban's averaging block
map, `SU(N)`) is not constructed here; `∃ lad, BalabanShape lad …` is trivial, so a consumer fixes
`lad`. DERIVED: `2` of `2 b₀ logL` from `d g⁻²/d log μ = 2 b₀ + …`; `109`, `122` are volume
numbers of the cited journal (Commun. Math. Phys.), not values. -/
def BalabanShape (lad : ℕ → Ladder G) (steps : ℕ → ℕ) (μ : Measure G) (β₀ : ℕ → ℝ)
    (nrm b₀ logL gmax : ℝ) : Prop :=
  ∃ (κ σR E Crun gbar thrMax ℓMin ηMax : ℝ) (n₀ : ℕ) (thr ℓ η : ℝ → ℝ),
    0 < κ ∧ 0 ≤ σR ∧ 0 ≤ E ∧ 0 ≤ Crun ∧ 0 < gbar ∧ gbar ≤ gmax ∧
    Crun * gbar < 2 * b₀ * logL ∧ 0 < ℓMin ∧ ηMax < 1 ∧
    (∀ g, 0 < g → g ≤ gbar →
      0 ≤ thr g ∧ thr g ≤ thrMax ∧ ℓMin ≤ ℓ g ∧ 0 ≤ η g ∧ η g ≤ ηMax) ∧
    Tendsto thr (𝓝[>] 0) (𝓝 0) ∧ Tendsto ℓ (𝓝[>] 0) atTop ∧ Tendsto η (𝓝[>] 0) (𝓝 0) ∧
    ∀ n, n₀ ≤ n → ∃ (gsq : ℕ → ℝ) (bg : ∀ j, ((lad n).sys j).Config → ((lad n).sys 0).Config),
      gsq 0 = nrm / β₀ n ∧
      (∀ j ≤ steps n, 0 < gsq j ∧ gsq j ≤ gbar) ∧
      OneLoopStep b₀ logL Crun gsq (steps n) ∧
      ∀ j ≤ steps n,
        IsBackground ((lad n).blkTo j) (SmallField ((lad n).sys j) (thr (gsq j))) (bg j) ∧
        (lad n).effLaw μ (β₀ n) j Set.univ ≠ 0 ∧
        (∀ p : ((lad n).sys j).Plaq,
          (lad n).effLaw μ (β₀ n) j
              {V | thr (gsq j) < ((lad n).sys j).φ (((lad n).sys j).hol p V)}
            ≤ ENNReal.ofReal (η (gsq j)) * (lad n).effLaw μ (β₀ n) j Set.univ) ∧
        ShapeStep ((lad n).sys j) ((lad n).sys 0) μ ((lad n).effLaw μ (β₀ n) j) (bg j)
          (nrm / gsq j) (thr (gsq j)) (ℓ (gsq j)) κ σR E

/-- **The `SU(N)` instance**: `nrm = N` (Lean coupling `β = N/g²`) and `b₀ = GaugeRunning.b0G`. -/
def BalabanShapeSU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] (lad : ℕ → Ladder (MassGap.SUN.SU N))
    (steps : ℕ → ℕ) (μ : Measure (MassGap.SUN.SU N)) (β₀ : ℕ → ℝ) (logL gmax : ℝ) : Prop :=
  BalabanShape lad steps μ β₀ N (MassGap.GaugeRunning.b0G (MassGap.SUN.SU N)) logL gmax

/-- **The Lean coupling is `N/g²`**: `GaugeRunning.gSqG` at the standard coupling `2β` is `N/β`. -/
theorem gSq_lean_SU (N : ℕ) [NeZero N] [Fact (2 ≤ N)] (β : ℝ) :
    MassGap.GaugeRunning.gSqG (MassGap.SUN.SU N) (2 * β) = (N : ℝ) / β := by
  rw [MassGap.GaugeRunning.gSqG_SU]
  congr 1
  ring

/-- **At the finest scale the background is the identity**: the fibre of `id` is one point. -/
theorem isBackground_id (sys : System G) (dom : sys.Config → Prop) :
    IsBackground (fine := sys) (sys := sys) id dom id :=
  fun _ _ => ⟨rfl, fun _ hU => by subst hU; exact le_rfl⟩

/-- **The bare Wilson measure has the shape at the finest scale**: background `id`, `ρ = boltz β`,
`Z = 1`, no polymers, for `φ ≥ 0`, `β ≥ 0`, `ℓ ≤ β thr`. -/
theorem shapeStep_zero (sys : System G) (μ : Measure G) {β thr ℓ κ σR E : ℝ}
    (hb : Measurable (sys.boltz β)) (hβ : 0 ≤ β) (hφ : ∀ g, 0 ≤ sys.φ g) (hℓ : ℓ ≤ β * thr)
    (hσ : 0 ≤ σR) (hE : 0 ≤ E) :
    ShapeStep sys sys μ ((sys.vol μ).withDensity fun U => ENNReal.ofReal (sys.boltz β U)) id
      β thr ℓ κ σR E := by
  refine ⟨sys.boltz β, 1, ∅, fun _ _ => 0, ⟨hb, fun _ => (Real.exp_pos _).le, rfl⟩, one_pos,
    ?_, ?_, fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro V _
    simp only [System.boltz, Finset.sum_empty, sub_zero, one_mul, neg_mul, id]
  · intro V
    have h1 : (Finset.univ.filter fun p => thr < sys.φ (sys.hol p V)).card • thr
        ≤ ∑ p ∈ Finset.univ.filter (fun p => thr < sys.φ (sys.hol p V)), sys.φ (sys.hol p V) :=
      Finset.card_nsmul_le_sum _ _ _ fun p hp => (Finset.mem_filter.1 hp).2.le
    have h2 : ∑ p ∈ Finset.univ.filter (fun p => thr < sys.φ (sys.hol p V)), sys.φ (sys.hol p V)
        ≤ ∑ p, sys.φ (sys.hol p V) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun p _ _ => hφ (sys.hol p V)
    rw [nsmul_eq_mul] at h1
    have hS : (largeCount sys thr V : ℝ) * thr ≤ sys.action V := by
      unfold largeCount System.action
      linarith
    have hn : (0 : ℝ) ≤ largeCount sys thr V := Nat.cast_nonneg _
    have h3 : ℓ * largeCount sys thr V ≤ β * thr * largeCount sys thr V :=
      mul_le_mul_of_nonneg_right hℓ hn
    have h4 : β * ((largeCount sys thr V : ℝ) * thr) ≤ β * sys.action V :=
      mul_le_mul_of_nonneg_left hS hβ
    have h5 : 0 ≤ E * (Fintype.card sys.Link : ℝ) := mul_nonneg hE (Nat.cast_nonneg _)
    rw [one_mul]
    unfold System.boltz
    exact Real.exp_le_exp.2 (by linarith)
  · intro X hX
    simp at hX
  · intro l
    simpa using hσ

end Statement

/-! ## 3. Consequences of the shape -/

section Polymer

variable {L Cf : Type*}

/-- **Locality bounds the polymer oscillation on a cell**: if `U`, `U'` differ only on `D`, the
polymer sums differ by at most `2 |D| σ`. -/
theorem polymer_osc (P : Finset (Finset L)) (R : Finset L → (L → Cf) → ℝ)
    (hloc : ∀ X U U', (∀ l ∈ X, U l = U' l) → R X U = R X U') {U U' : L → Cf} {κ σ : ℝ}
    (hdec : ∀ X ∈ P, |R X U| ≤ Real.exp (-(κ * X.card)) ∧ |R X U'| ≤ Real.exp (-(κ * X.card)))
    (hsum : ∀ l, ∑ X ∈ P.filter (fun X => l ∈ X), Real.exp (-(κ * X.card)) ≤ σ)
    (D : Finset L) (hD : ∀ l, l ∉ D → U l = U' l) :
    |∑ X ∈ P, R X U - ∑ X ∈ P, R X U'| ≤ 2 * (D.card * σ) := by
  have hterm : ∀ X ∈ P, |R X U - R X U'|
      ≤ 2 * ∑ l ∈ D, if l ∈ X then Real.exp (-(κ * X.card)) else 0 := by
    intro X hX
    have hnn : ∀ i ∈ D, 0 ≤ if i ∈ X then Real.exp (-(κ * X.card)) else 0 := fun i _ => by
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    by_cases hXD : ∃ l ∈ D, l ∈ X
    · obtain ⟨l, hlD, hlX⟩ := hXD
      have ha := abs_le.1 (hdec X hX).1
      have hb := abs_le.1 (hdec X hX).2
      have h1 : |R X U - R X U'| ≤ 2 * Real.exp (-(κ * X.card)) := by
        rw [abs_le]; constructor <;> linarith
      have h2 : Real.exp (-(κ * X.card))
          ≤ ∑ i ∈ D, if i ∈ X then Real.exp (-(κ * X.card)) else 0 := by
        have := Finset.single_le_sum (f := fun i => if i ∈ X then Real.exp (-(κ * X.card)) else 0)
          hnn hlD
        simp only [if_pos hlX] at this
        exact this
      linarith
    · simp only [not_exists, not_and] at hXD
      have : R X U = R X U' := hloc X U U' fun l hl => hD l fun hlD => hXD l hlD hl
      rw [this, sub_self, abs_zero]
      exact mul_nonneg zero_le_two (Finset.sum_nonneg hnn)
  calc |∑ X ∈ P, R X U - ∑ X ∈ P, R X U'| = |∑ X ∈ P, (R X U - R X U')| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ X ∈ P, |R X U - R X U'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ X ∈ P, 2 * ∑ l ∈ D, (if l ∈ X then Real.exp (-(κ * X.card)) else 0) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ l ∈ D, ∑ X ∈ P.filter (fun X => l ∈ X), Real.exp (-(κ * X.card)) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_filter]
    _ ≤ 2 * ∑ _l ∈ D, σ := by
        gcongr with l hl
        exact hsum l
    _ = 2 * (D.card * σ) := by rw [Finset.sum_const, nsmul_eq_mul]

end Polymer

section Cell

variable {G : Type} [MeasurableSpace G]

/-- **The action comparison on one cell.** Under `ShapeStep`, at two small-field configurations
that agree off the links `D`, `ρ U = ρ U' · exp(−βe (A(bg U) − A(bg U')) + h)` with
`|h| ≤ 2 |D| σR`, `A(bg ·)` the fine action of the background. -/
theorem ShapeStep.cell {sys fine : System G} {μ : Measure G} {law : Measure sys.Config}
    {bg : sys.Config → fine.Config} {βe thr ℓ κ σR E : ℝ}
    (h : ShapeStep sys fine μ law bg βe thr ℓ κ σR E) :
    ∃ ρ, IsEffDensity sys μ law ρ ∧ ∀ (D : Finset sys.Link) (U U' : sys.Config),
      SmallField sys thr U → SmallField sys thr U' → (∀ l, l ∉ D → U l = U' l) →
      ∃ hU : ℝ, |hU| ≤ 2 * (D.card * σR) ∧
        ρ U = ρ U' * Real.exp (-(βe * (fine.action (bg U) - fine.action (bg U'))) + hU) := by
  obtain ⟨ρ, Z, P, R, hρ, -, hsm, -, hloc, hdec, hsum⟩ := h
  refine ⟨ρ, hρ, fun D U U' hU hU' hD => ⟨-(∑ X ∈ P, R X U - ∑ X ∈ P, R X U'), ?_, ?_⟩⟩
  · rw [abs_neg]
    exact polymer_osc P R hloc (fun X hX => ⟨hdec X hX U hU, hdec X hX U' hU'⟩) hsum D hD
  · rw [hsm U hU, hsm U' hU', mul_assoc, ← Real.exp_add]
    congr 2
    ring

end Cell

section Finite

variable {Ω α : Type*} [Fintype Ω] [Fintype α]

/-- **Normalised weights from an action comparison** (finite form). With `w = E w₀ e^{h}` on `S`,
`|h| ≤ θ`, `Z = Σ w`, `A = Σ_S w`, `A₀ = Σ_S w₀`: on `S`, `w/Z ≤ e^{2θ} w₀/A₀` and
`(A/Z)(w₀/A₀) ≤ e^{2θ} w/Z`. -/
theorem ratio_of_weights {w w₀ : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw₀ : ∀ ω, 0 ≤ w₀ ω) {S : Finset Ω}
    {E θ : ℝ} {h : Ω → ℝ} (hE : 0 < E) (hrel : ∀ ω ∈ S, w ω = E * w₀ ω * Real.exp (h ω))
    (hh : ∀ ω ∈ S, |h ω| ≤ θ) (hA₀ : 0 < ∑ ω ∈ S, w₀ ω) (hZ : 0 < ∑ ω, w ω) :
    ∀ ω ∈ S, w ω / (∑ ω', w ω') ≤ Real.exp θ ^ 2 * (w₀ ω / ∑ ω' ∈ S, w₀ ω') ∧
      (∑ ω' ∈ S, w ω') / (∑ ω', w ω') * (w₀ ω / ∑ ω' ∈ S, w₀ ω')
        ≤ Real.exp θ ^ 2 * (w ω / ∑ ω', w ω') := by
  set Z := ∑ ω', w ω' with hZdef
  set A := ∑ ω' ∈ S, w ω' with hAdef
  set A₀ := ∑ ω' ∈ S, w₀ ω' with hA₀def
  set t := Real.exp θ with htdef
  set ti := Real.exp (-θ) with htidef
  have htt : t * ti = 1 := by rw [htdef, htidef, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hup : ∀ ω ∈ S, Real.exp (h ω) ≤ t := fun ω hω =>
    Real.exp_le_exp.2 (abs_le.1 (hh ω hω)).2
  have hlo : ∀ ω ∈ S, ti ≤ Real.exp (h ω) := fun ω hω =>
    Real.exp_le_exp.2 (by linarith [(abs_le.1 (hh ω hω)).1])
  have hAlo : E * ti * A₀ ≤ A := by
    calc E * ti * A₀ = ∑ ω ∈ S, E * w₀ ω * ti := by
          rw [hA₀def, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ ω ∈ S, E * w₀ ω * Real.exp (h ω) :=
          Finset.sum_le_sum fun ω hω =>
            mul_le_mul_of_nonneg_left (hlo ω hω) (mul_nonneg hE.le (hw₀ ω))
      _ = A := Finset.sum_congr rfl fun ω hω => (hrel ω hω).symm
  have hAhi : A ≤ E * t * A₀ := by
    calc A = ∑ ω ∈ S, E * w₀ ω * Real.exp (h ω) := Finset.sum_congr rfl fun ω hω => hrel ω hω
      _ ≤ ∑ ω ∈ S, E * w₀ ω * t :=
          Finset.sum_le_sum fun ω hω =>
            mul_le_mul_of_nonneg_left (hup ω hω) (mul_nonneg hE.le (hw₀ ω))
      _ = E * t * A₀ := by
          rw [hA₀def, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
  have hZA : A ≤ Z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hw i
  intro ω hω
  have hwle : w ω ≤ E * t * w₀ ω := by
    rw [hrel ω hω]
    calc E * w₀ ω * Real.exp (h ω) ≤ E * w₀ ω * t :=
          mul_le_mul_of_nonneg_left (hup ω hω) (mul_nonneg hE.le (hw₀ ω))
      _ = E * t * w₀ ω := by ring
  have hwge : E * ti * w₀ ω ≤ w ω := by
    rw [hrel ω hω]
    calc E * ti * w₀ ω = E * w₀ ω * ti := by ring
      _ ≤ E * w₀ ω * Real.exp (h ω) :=
          mul_le_mul_of_nonneg_left (hlo ω hω) (mul_nonneg hE.le (hw₀ ω))
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  constructor
  · rw [div_le_iff₀ hZ, show t ^ 2 * (w₀ ω / A₀) * Z = t ^ 2 * w₀ ω * Z / A₀ by ring,
      le_div_iff₀ hA₀]
    calc w ω * A₀ ≤ E * t * w₀ ω * A₀ := mul_le_mul_of_nonneg_right hwle hA₀.le
      _ = t ^ 2 * w₀ ω * (E * ti * A₀) := by
          linear_combination (-(E * t * w₀ ω * A₀)) * htt
      _ ≤ t ^ 2 * w₀ ω * A := mul_le_mul_of_nonneg_left hAlo (mul_nonneg ht2 (hw₀ ω))
      _ ≤ t ^ 2 * w₀ ω * Z := mul_le_mul_of_nonneg_left hZA (mul_nonneg ht2 (hw₀ ω))
  · have key : A * w₀ ω ≤ t ^ 2 * A₀ * w ω := by
      calc A * w₀ ω ≤ E * t * A₀ * w₀ ω := mul_le_mul_of_nonneg_right hAhi (hw₀ ω)
        _ = t ^ 2 * A₀ * (E * ti * w₀ ω) := by
            linear_combination (-(E * t * A₀ * w₀ ω)) * htt
        _ ≤ t ^ 2 * A₀ * w ω := mul_le_mul_of_nonneg_left hwge (mul_nonneg ht2 hA₀.le)
    rw [show A / Z * (w₀ ω / A₀) = A * w₀ ω / A₀ / Z by ring,
      show t ^ 2 * (w ω / Z) = t ^ 2 * w ω / Z by ring]
    refine div_le_div_of_nonneg_right ?_ hZ.le
    rw [div_le_iff₀ hA₀]
    linarith

/-- **The two-slice marginal** of a configuration weight `p` through the slice pair `q`. -/
def marg (q : Ω → α × α) (p : Ω → ℝ) (x y : α) : ℝ := ∑ ω, if q ω = (x, y) then p ω else 0

/-- **The large-field excess**: the two-slice marginal of `p + p₀` on the configurations outside
`S`. -/
def largeMarg (q : Ω → α × α) (S : Ω → Prop) (p p₀ : Ω → ℝ) (x y : α) : ℝ :=
  ∑ ω, if q ω = (x, y) ∧ ¬ S ω then p ω + p₀ ω else 0

omit [Fintype α] in
theorem largeMarg_nonneg (q : Ω → α × α) (S : Ω → Prop) {p p₀ : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    (hp₀ : ∀ ω, 0 ≤ p₀ ω) (x y : α) : 0 ≤ largeMarg q S p p₀ x y :=
  Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact add_nonneg (hp ω) (hp₀ ω)
    · exact le_rfl

omit [Fintype α] in
/-- **Configuration bounds pass to the two-slice laws**: `lo p₀ ≤ p ≤ hi p₀` on `S`, `1 ≤ hi`,
give `|J − J₀| ≤ max(hi − 1, 1 − lo) J₀ + L` for the marginals `J`, `J₀` and the large-field
excess `L`. -/
theorem dens_of_config (q : Ω → α × α) {p p₀ : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hp₀ : ∀ ω, 0 ≤ p₀ ω)
    {S : Ω → Prop} {lo hi : ℝ} (hhi : 1 ≤ hi)
    (hb : ∀ ω, S ω → lo * p₀ ω ≤ p ω ∧ p ω ≤ hi * p₀ ω) (x y : α) :
    |marg q p x y - marg q p₀ x y|
      ≤ max (hi - 1) (1 - lo) * marg q p₀ x y + largeMarg q S p p₀ x y := by
  set δ := max (hi - 1) (1 - lo) with hδdef
  have hδ0 : 0 ≤ δ := le_max_of_le_left (by linarith)
  unfold marg largeMarg
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => ?_)
  have h1 : (hi - 1) * p₀ ω ≤ δ * p₀ ω := mul_le_mul_of_nonneg_right (le_max_left _ _) (hp₀ ω)
  have h2 : (1 - lo) * p₀ ω ≤ δ * p₀ ω := mul_le_mul_of_nonneg_right (le_max_right _ _) (hp₀ ω)
  have hδp : 0 ≤ δ * p₀ ω := mul_nonneg hδ0 (hp₀ ω)
  by_cases hq : q ω = (x, y)
  · by_cases hs : S ω
    · have hb' := hb ω hs
      have hl : ¬ (q ω = (x, y) ∧ ¬ S ω) := fun h => h.2 hs
      rw [if_pos hq, if_pos hq, if_neg hl, add_zero, abs_le]
      constructor <;> linarith [hb'.1, hb'.2]
    · rw [if_pos hq, if_pos hq, if_pos ⟨hq, hs⟩, abs_le]
      constructor <;> linarith [hp ω, hp₀ ω]
  · have hl : ¬ (q ω = (x, y) ∧ ¬ S ω) := fun h => hq h.1
    rw [if_neg hq, if_neg hq, if_neg hl]
    simp

/-- **`FineLinks.NearFree` from configuration bounds**: the bounds of `dens_of_config` and a
large-field excess of relative weight `ε` on the readings `W` (both slices) and mass `≤ ε`. -/
theorem nearFree_of_config {π₀ : α → ℝ} {W : Set (α → ℝ)} (q : Ω → α × α) {p p₀ : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hp₀ : ∀ ω, 0 ≤ p₀ ω) {S : Ω → Prop} {lo hi ε : ℝ} (hhi : 1 ≤ hi) (hb : ∀ ω, S ω → lo * p₀ ω ≤ p ω ∧ p ω ≤ hi * p₀ ω) (hε : 0 ≤ ε)
    (hL₀ : ∀ f ∈ W, ∑ x, ∑ y, largeMarg q S p p₀ x y * f x ^ 2 ≤ ε * nsq π₀ f)
    (hL₁ : ∀ g ∈ W, ∑ x, ∑ y, largeMarg q S p p₀ x y * g y ^ 2 ≤ ε * nsq π₀ g)
    (hLm : ∑ x, ∑ y, largeMarg q S p p₀ x y ≤ ε) :
    NearFree π₀ (marg q p₀) (marg q p) (largeMarg q S p p₀) W (max (hi - 1) (1 - lo)) ε where
  δ_nonneg := le_max_of_le_left (by linarith)
  ε_nonneg := hε
  L_nonneg := largeMarg_nonneg q S hp hp₀
  dens := dens_of_config q hp hp₀ hhi hb
  large₀ := hL₀
  large₁ := hL₁
  mass := hLm

/-- **A rate is a rate at every larger value.** -/
theorem corrW_mono {π : α → ℝ} {J : α → α → ℝ} {W : Set (α → ℝ)} {r r' : ℝ}
    (hπ : ∀ x, 0 ≤ π x) (h : CorrW π J W r) (hr : r ≤ r') : CorrW π J W r' := by
  refine ⟨h.1.trans hr, fun f hf g hg hf0 hg0 => (h.2 f hf g hg hf0 hg0).trans ?_⟩
  have h2 : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ h.1 hr 2
  have h3 := mul_nonneg (nsq_nonneg hπ f) (nsq_nonneg hπ g)
  calc r ^ 2 * nsq π f * nsq π g = r ^ 2 * (nsq π f * nsq π g) := by ring
    _ ≤ r' ^ 2 * (nsq π f * nsq π g) := mul_le_mul_of_nonneg_right h2 h3
    _ = r' ^ 2 * nsq π f * nsq π g := by ring

/-- **The cell rate from near-free**: with the free reference rate `e^{−arccosh 2} = 2 − √3` on a
layer closed under constants and `δ + ε ≤ κ̄ ≤ 1/4`, `4κ̄ < √3 − 1`, the true two-slice law has rate
`2 − √3 + 4κ̄ < 1`. The rate depends on `κ̄` only. -/
theorem cell_corrW_le {π₀ π : α → ℝ} {J₀ J L : α → α → ℝ} {W : Set (α → ℝ)} {δ ε κb : ℝ}
    (h₀ : Joint π₀ J₀) (h : Joint π J) (hW : ∀ f ∈ W, ∀ c : ℝ, (fun x => f x - c) ∈ W)
    (hr₀ : CorrW π₀ J₀ W (Real.exp (-Real.log (2 + Real.sqrt 3))))
    (hN : NearFree π₀ J₀ J L W δ ε) (hκ : δ + ε ≤ κb) (hκb : κb ≤ 1 / 4)
    (h4 : 4 * κb < Real.sqrt 3 - 1) :
    CorrW π J W (2 - Real.sqrt 3 + 4 * κb) ∧ 2 - Real.sqrt 3 + 4 * κb < 1 := by
  have hκ0 : 0 ≤ δ + ε := add_nonneg hN.δ_nonneg hN.ε_nonneg
  have hk : δ + ε ≤ 1 / 4 := hκ.trans hκb
  have hκ1 : (δ + ε) + (δ + ε) ^ 2 < 1 := by nlinarith [mul_nonneg hκ0 (sub_nonneg.2 hk)]
  have hc := corrW_of_nearFree h₀ h hW hr₀ hN hκ1
  rw [exp_neg_arccosh_two] at hc
  have h3 : (1 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hle := nearFreeRate_le (r₀ := 2 - Real.sqrt 3) (by linarith) hκ0 (hκ.trans hκb)
  exact ⟨corrW_mono h.pi_nonneg hc (by linarith), by linarith⟩

/-- **The per-step correlation of a realised fibre**: a rate `r ∈ (0, 1)` of the two-slice law of a
realising Markov pair is `CondGap.StepCorr` at `e^{−c}` with `c = −log r > 0`. -/
theorem exists_c_stepCorr {Ω' F : Type*} [MeasurableSpace Ω'] [Fintype F] {m : Measure Ω'}
    {X₀ X₁ : Ω' → F} {π : F → ℝ} {Q : Matrix F F ℝ} {Z : ℝ} (hR : Realises m X₀ X₁ π Q Z)
    {W : Set (F → ℝ)} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (h : CorrW π (fun x y => π x * Q x y) W r) :
    ∃ c : ℝ, 0 < c ∧ StepCorr m X₀ X₁ W (Real.exp (-c)) :=
  ⟨-Real.log r, by linarith [Real.log_neg hr0 hr1], by
    rw [neg_neg, Real.exp_log hr0]; exact stepCorr_of_corrW hR h⟩

/-- **From an action comparison on the small configurations to the cell rate.** Weights `w` (true)
and `w₀` (reference) on a finite configuration space, `w = E w₀ e^{h}` with `|h| ≤ θ` on the small
set `S`; normalised laws `p = w/Z`, `p₀ = w₀/Z₀` with two-slice marginals through `q`; the free
reference rate on a layer closed under constants; a large-field excess of relative weight `ε`. With
`hi = e^{2θ} Z₀/A₀`, `lo = (A/Z)/e^{2θ}` and `max(hi − 1, 1 − lo) + ε ≤ κ̄ ≤ 1/4`, `4κ̄ < √3 − 1`,
the true two-slice law has rate `2 − √3 + 4κ̄ < 1`. -/
theorem cell_rate_of_action {π₀ π : α → ℝ} {W : Set (α → ℝ)} (q : Ω → α × α) {w w₀ : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hw₀ : ∀ ω, 0 ≤ w₀ ω) {S : Finset Ω} {E θ ε κb : ℝ} {h : Ω → ℝ}
    (hθ : 0 ≤ θ) (hE : 0 < E) (hrel : ∀ ω ∈ S, w ω = E * w₀ ω * Real.exp (h ω))
    (hh : ∀ ω ∈ S, |h ω| ≤ θ) (hA₀ : 0 < ∑ ω ∈ S, w₀ ω) (hZ : 0 < ∑ ω, w ω)
    (h₀ : Joint π₀ (marg q fun ω => w₀ ω / ∑ ω', w₀ ω'))
    (h₁ : Joint π (marg q fun ω => w ω / ∑ ω', w ω'))
    (hWc : ∀ f ∈ W, ∀ c : ℝ, (fun x => f x - c) ∈ W)
    (hr₀ : CorrW π₀ (marg q fun ω => w₀ ω / ∑ ω', w₀ ω') W
      (Real.exp (-Real.log (2 + Real.sqrt 3))))
    (hε : 0 ≤ ε)
    (hL₀ : ∀ f ∈ W, ∑ x, ∑ y, largeMarg q (· ∈ S) (fun ω => w ω / ∑ ω', w ω')
      (fun ω => w₀ ω / ∑ ω', w₀ ω') x y * f x ^ 2 ≤ ε * nsq π₀ f)
    (hL₁ : ∀ g ∈ W, ∑ x, ∑ y, largeMarg q (· ∈ S) (fun ω => w ω / ∑ ω', w ω')
      (fun ω => w₀ ω / ∑ ω', w₀ ω') x y * g y ^ 2 ≤ ε * nsq π₀ g)
    (hLm : ∑ x, ∑ y, largeMarg q (· ∈ S) (fun ω => w ω / ∑ ω', w ω')
      (fun ω => w₀ ω / ∑ ω', w₀ ω') x y ≤ ε)
    (hκ : max (Real.exp θ ^ 2 * ((∑ ω, w₀ ω) / ∑ ω ∈ S, w₀ ω) - 1)
      (1 - (∑ ω ∈ S, w ω) / (∑ ω, w ω) / Real.exp θ ^ 2) + ε ≤ κb)
    (hκb : κb ≤ 1 / 4) (h4 : 4 * κb < Real.sqrt 3 - 1) :
    CorrW π (marg q fun ω => w ω / ∑ ω', w ω') W (2 - Real.sqrt 3 + 4 * κb) ∧
      2 - Real.sqrt 3 + 4 * κb < 1 := by
  set Z := ∑ ω', w ω' with hZdef
  set Z₀ := ∑ ω', w₀ ω' with hZ₀def
  set A := ∑ ω' ∈ S, w ω' with hAdef
  set A₀ := ∑ ω' ∈ S, w₀ ω' with hA₀def
  set t := Real.exp θ with htdef
  have hA₀Z₀ : A₀ ≤ Z₀ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hw₀ i
  have hZ₀ : 0 < Z₀ := hA₀.trans_le hA₀Z₀
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => hw i
  have ht1 : 1 ≤ t := by rw [htdef]; exact Real.one_le_exp hθ
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
  have ht2p : 0 < t ^ 2 := by positivity
  have hp : ∀ ω, 0 ≤ w ω / Z := fun ω => div_nonneg (hw ω) hZ.le
  have hp₀ : ∀ ω, 0 ≤ w₀ ω / Z₀ := fun ω => div_nonneg (hw₀ ω) hZ₀.le
  have hhi : 1 ≤ t ^ 2 * (Z₀ / A₀) := by
    have : 1 ≤ Z₀ / A₀ := (one_le_div hA₀).2 hA₀Z₀
    nlinarith
  have hb : ∀ ω, ω ∈ S → A / Z / t ^ 2 * (w₀ ω / Z₀) ≤ w ω / Z ∧
      w ω / Z ≤ t ^ 2 * (Z₀ / A₀) * (w₀ ω / Z₀) := by
    intro ω hω
    obtain ⟨hU, hL⟩ := ratio_of_weights hw hw₀ hE hrel hh hA₀ hZ ω hω
    constructor
    · have hw0le : w₀ ω / Z₀ ≤ w₀ ω / A₀ := div_le_div_of_nonneg_left (hw₀ ω) hA₀ hA₀Z₀
      have hc0 : 0 ≤ A / Z / t ^ 2 := div_nonneg (div_nonneg hA0 hZ.le) ht2p.le
      calc A / Z / t ^ 2 * (w₀ ω / Z₀) ≤ A / Z / t ^ 2 * (w₀ ω / A₀) :=
            mul_le_mul_of_nonneg_left hw0le hc0
        _ = (A / Z * (w₀ ω / A₀)) / t ^ 2 := by ring
        _ ≤ (t ^ 2 * (w ω / Z)) / t ^ 2 := div_le_div_of_nonneg_right hL ht2p.le
        _ = w ω / Z := mul_div_cancel_left₀ _ ht2p.ne'
    · have e : t ^ 2 * (Z₀ / A₀) * (w₀ ω / Z₀) = t ^ 2 * (w₀ ω / A₀) := by
        rw [mul_assoc, div_mul_div_comm, mul_comm Z₀ (w₀ ω), mul_div_mul_right _ _ hZ₀.ne']
      rw [e]; exact hU
  have hN := nearFree_of_config (π₀ := π₀) (W := W) q hp hp₀ hhi hb hε hL₀ hL₁ hLm
  exact cell_corrW_le h₀ h₁ hWc hr₀ hN hκ hκb h4

end Finite

/-! ## Link (2) in density form -/

section Flow

variable {α : Type*} [Fintype α]

/-- **A pointwise density comparison is near-free with no large field**. -/
theorem nearFree_of_density {π₀ : α → ℝ} {J₀ J : α → α → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ x y, |J x y - J₀ x y| ≤ δ * J₀ x y) :
    NearFree π₀ J₀ J (fun _ _ => 0) Set.univ δ 0 where
  δ_nonneg := hδ
  ε_nonneg := le_rfl
  L_nonneg _ _ := le_rfl
  dens x y := by
    show |J x y - J₀ x y| ≤ δ * J₀ x y + 0
    rw [add_zero]; exact hd x y
  large₀ f _ := by simp
  large₁ g _ := by simp
  mass := by simp

/-- **Link (2), density form, along the zoom.** Observer two-slice laws `J k` on one fixed finite
space, `|J_{k+1} − J_k| ≤ δ_k J_k`, `0 ≤ δ_k ≤ 1/4`: the rate on all readings at zoom `k ≥ K₀` is
`r₀ + 4 Σ_{K₀ ≤ j < k} δ_j`, as long as that stays `≤ 1`. -/
theorem corrW_along_zoom {π : ℕ → α → ℝ} {J : ℕ → α → α → ℝ} (hJ : ∀ k, Joint (π k) (J k))
    {δ : ℕ → ℝ} (hδ0 : ∀ k, 0 ≤ δ k) (hδ : ∀ k, δ k ≤ 1 / 4)
    (hd : ∀ k x y, |J (k + 1) x y - J k x y| ≤ δ k * J k x y) {K₀ : ℕ} {r₀ : ℝ}
    (h0 : CorrW (π K₀) (J K₀) Set.univ r₀)
    (hB : ∀ k, K₀ ≤ k → r₀ + 4 * ∑ j ∈ Finset.Ico K₀ k, δ j ≤ 1) :
    ∀ k, K₀ ≤ k → CorrW (π k) (J k) Set.univ (r₀ + 4 * ∑ j ∈ Finset.Ico K₀ k, δ j) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using h0
  | succ n hn ih =>
    have hr1 := hB n hn
    have hN := nearFree_of_density (π₀ := π n) (hδ0 n) (hd n)
    have hκ : (δ n + 0) + (δ n + 0) ^ 2 < 1 := by nlinarith [hδ0 n, hδ n]
    have hc := corrW_of_nearFree (hJ n) (hJ (n + 1)) (fun _ _ _ => Set.mem_univ _) ih hN hκ
    rw [add_zero] at hc
    have hle := nearFreeRate_le hr1 (hδ0 n) (hδ n)
    refine corrW_mono (hJ (n + 1)).pi_nonneg hc ?_
    rw [Finset.sum_Ico_succ_top hn]
    linarith

/-- **A summable observer-law flow gives one rate at every zoom**: with `Σ_{K₀ ≤ j < k} δ_j ≤ D` for
every `k` and `r₀ + 4D ≤ 1`, the rate is `r₀ + 4D` at every zoom `k ≥ K₀`. -/
theorem corrW_uniform_along_zoom {π : ℕ → α → ℝ} {J : ℕ → α → α → ℝ}
    (hJ : ∀ k, Joint (π k) (J k)) {δ : ℕ → ℝ} (hδ0 : ∀ k, 0 ≤ δ k) (hδ : ∀ k, δ k ≤ 1 / 4)
    (hd : ∀ k x y, |J (k + 1) x y - J k x y| ≤ δ k * J k x y) {K₀ : ℕ} {r₀ Dsum : ℝ}
    (h0 : CorrW (π K₀) (J K₀) Set.univ r₀)
    (hD : ∀ k, K₀ ≤ k → ∑ j ∈ Finset.Ico K₀ k, δ j ≤ Dsum) (hlt : r₀ + 4 * Dsum ≤ 1) :
    ∀ k, K₀ ≤ k → CorrW (π k) (J k) Set.univ (r₀ + 4 * Dsum) := by
  intro k hk
  have hB : ∀ k, K₀ ≤ k → r₀ + 4 * ∑ j ∈ Finset.Ico K₀ k, δ j ≤ 1 := fun k hk => by
    linarith [hD k hk]
  exact corrW_mono (hJ k).pi_nonneg (corrW_along_zoom hJ hδ0 hδ hd h0 hB k hk)
    (by linarith [hD k hk])

end Flow

/-! ## The running inside the window -/

section Running

/-- **The two-loop recursion implies the one-loop recursion with an `O(g²)` error**: in the window
`0 < g² ≤ ḡ²`, `TwoLoopStep b₀ b₁ logL C₂` gives `OneLoopStep b₀ logL (2 b₁ logL + C₂ ḡ²)`. -/
theorem oneLoop_of_twoLoop {b₀ b₁ logL C₂ gbar : ℝ} {gsq : ℕ → ℝ} {n : ℕ} (hb₁ : 0 ≤ b₁)
    (hL : 0 ≤ logL) (hC : 0 ≤ C₂) (hg : ∀ j < n, 0 < gsq j ∧ gsq j ≤ gbar)
    (h : TwoLoopStep b₀ b₁ logL C₂ gsq n) :
    OneLoopStep b₀ logL (2 * b₁ * logL + C₂ * gbar) gsq n := by
  intro j hj
  obtain ⟨h0, h1⟩ := hg j hj
  have hs := abs_le.1 (h j hj)
  have hq : gsq j ^ 2 ≤ gbar * gsq j := by nlinarith
  have hsq : C₂ * gsq j ^ 2 ≤ C₂ * (gbar * gsq j) := mul_le_mul_of_nonneg_left hq hC
  have hb : 0 ≤ 2 * b₁ * logL * gsq j := by positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- **The inverse coupling drops by `2 b₀ logL ± Crun ḡ²` per step in the window**: under
`OneLoopStep`, `k (2 b₀ logL − Crun ḡ²) ≤ g_0⁻² − g_k⁻² ≤ k (2 b₀ logL + Crun ḡ²)` for `k ≤ n`. -/
theorem invCoupling_drop {b₀ logL Crun gbar : ℝ} {gsq : ℕ → ℝ} {n : ℕ}
    (hg : ∀ j < n, 0 < gsq j ∧ gsq j ≤ gbar) (hC : 0 ≤ Crun)
    (h : OneLoopStep b₀ logL Crun gsq n) :
    ∀ k, k ≤ n → (k : ℝ) * (2 * b₀ * logL - Crun * gbar) ≤ (gsq 0)⁻¹ - (gsq k)⁻¹ ∧
      (gsq 0)⁻¹ - (gsq k)⁻¹ ≤ (k : ℝ) * (2 * b₀ * logL + Crun * gbar) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k < n := Nat.lt_of_succ_le hk
    obtain ⟨ih1, ih2⟩ := ih hk'.le
    have hs := abs_le.1 (h k hk')
    have hcg : Crun * gsq k ≤ Crun * gbar := mul_le_mul_of_nonneg_left (hg k hk').2 hC
    have hcg0 : 0 ≤ Crun * gsq k := mul_nonneg hC (hg k hk').1.le
    push_cast
    constructor <;> nlinarith

/-- **The number of steps in the window**: with every `g_j²` for `j ≤ n` in `(0, ḡ²]`,
`OneLoopStep`, and `Crun ḡ² < 2 b₀ logL` (a clause of `BalabanShape`),
`n ≤ (g_0⁻² − ḡ⁻²)/(2 b₀ logL − Crun ḡ²)`. An upper bound only. -/
theorem window_steps_le {b₀ logL Crun gbar : ℝ} {gsq : ℕ → ℝ} {n : ℕ}
    (hg : ∀ j ≤ n, 0 < gsq j ∧ gsq j ≤ gbar) (hC : 0 ≤ Crun)
    (h : OneLoopStep b₀ logL Crun gsq n) (hd : Crun * gbar < 2 * b₀ * logL) :
    (n : ℝ) ≤ ((gsq 0)⁻¹ - gbar⁻¹) / (2 * b₀ * logL - Crun * gbar) := by
  have h1 := (invCoupling_drop (fun j hj => hg j hj.le) hC h n le_rfl).1
  have hinv : gbar⁻¹ ≤ (gsq n)⁻¹ := inv_anti₀ (hg n le_rfl).1 (hg n le_rfl).2
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **The weak-coupling window does not reach the strong-coupling window**: `0 < g² ≤ ḡ²` with the
explicit assumption `ḡ² < 20 N` gives the Lean coupling `N/g² > 1/20`, `1/20` the cited
strong-coupling threshold. -/
theorem window_not_strong {N gsq gbar : ℝ} (hg : 0 < gsq) (hgb : gsq ≤ gbar)
    (hbar : gbar < 20 * N) : 1 / 20 < N / gsq := by
  rw [lt_div_iff₀ hg]
  linarith

end Running

#print axioms isBackground_id
#print axioms window_steps_le
#print axioms Ladder.measurable_blkTo
#print axioms Ladder.effLaw_zero
#print axioms Ladder.effLaw_succ
#print axioms isEffDensity_zero
#print axioms fibreGibbs_eq_effFibre
#print axioms effFibre_disintegrates
#print axioms gSq_lean_SU
#print axioms shapeStep_zero
#print axioms polymer_osc
#print axioms ShapeStep.cell
#print axioms ratio_of_weights
#print axioms largeMarg_nonneg
#print axioms dens_of_config
#print axioms nearFree_of_config
#print axioms corrW_mono
#print axioms cell_corrW_le
#print axioms exists_c_stepCorr
#print axioms cell_rate_of_action
#print axioms nearFree_of_density
#print axioms corrW_along_zoom
#print axioms corrW_uniform_along_zoom
#print axioms oneLoop_of_twoLoop
#print axioms invCoupling_drop
#print axioms window_not_strong

end MassGap.BalabanFlow
