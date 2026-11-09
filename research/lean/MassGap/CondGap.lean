import Mathlib
import MassGap.LayerRate
import MassGap.LatticeGauge

/-!
# MassGap.CondGap — the conditional UV gap: its statement, the tools that reduce it, and their regimes

`LayerRate` section 5 names input (i), the conditional UV gap: for the fine Wilson measure at zoom
`k+1` conditioned on the coarse (block) field, the per-step transfer of the new modes on one fixed
physical cell contracts them in `L²` of the conditional measure by `e^{−c}`, `c > 0` uniform in `k`,
at the bare couplings of the asymptotically free regime; plus the link from that conditional kernel
to the slab restricted to the new layer `W` (the `hW` of `LayerRate.refine_step_*`). This module
states (i) on the tree's objects, proves the general steps that reduce it, and records which regime
each available tool covers. **It does not prove (i).**

## 1. The conditional measure given the block field

* `IsCondMeasure P B κ`: `κ` is a Markov kernel from block values to configurations with
  `(P.map B) ⊗ₘ κ = P.map (U ↦ (B U, U))` — the disintegration of `P` over the block map `B`.
* `exists_condMeasure`: on a standard Borel configuration space one exists
  (`ProbabilityTheory.condDistrib`). It does not ask `B` to be measurable; for a non-measurable `B`
  the map `P.map B` is `0` and the statement is degenerate. `WilsonCondUVGap` asks for measurable
  block maps.
* `IsCondMeasure.ae_fibre`: for almost every block value `V`, `κ V` lives on the fibre `{B U = V}`
  (given a measurable graph of `B`).
* `compProd_fibreWeight`: if `κ₀` disintegrates `ν` over `B`, then `κ₀` weighted by a density `w`
  disintegrates `ν` weighted by `w`. `fibreGibbs sys κ₀ β = κ₀ · e^{−β S}` and
  `fibreGibbs_disintegrates`: with `κ₀` the conditional of the product Haar measure (the fibre's
  Haar measure), `fibreGibbs` disintegrates the unnormalised Wilson–Gibbs measure. Its normalisation
  on each fibre is the conditional Gibbs measure; every statement below is homogeneous in the
  measure, so the normalisation is not taken.

## 2. The statement of (i)

* `StepCorr m X₀ X₁ W r`: under `m`, every mean-zero `f, g ∈ W` with `f ∘ X₀, g ∘ X₁ ∈ L²(m)` has
  `(∫ f(X₀) g(X₁))² ≤ r² ∫ f(X₀)² ∫ g(X₁)²` — the maximal correlation of the new modes across one
  fine time step (`X₀`, `X₁` the fine slices at `t`, `t+1` of the cell) is at most `r`. For a
  reflection-positive slab this is the `L²` contraction of the transfer on `W`
  (`GapL2.corr_iff_contr` in finite form).
* `GaugeInvariantLayer act actS X₀ X₁ B W`: `act` fixes the block field and is intertwined by the
  slice maps with `actS`, and every function of `W` is `actS`-invariant. `System` has no sites and
  the tree's gauge action (`igaugeTransform`) is on the infinite `IConf`, so the action is an
  explicit parameter. `NontrivialLayer m X₀ W`: `W` holds a mean-zero function of positive norm.
* `WilsonCondUVGap sys μ B κ₀ βs X₀ X₁ W act actS`: **input (i)**. It asks `βs → ∞`, `B k`
  measurable, `κ₀ k` a conditional measure of the product measure given `B k`, every `W k V` a
  gauge-invariant layer, the Boltzmann weight gauge invariant, and: there is `c > 0` such that at
  every zoom `k`, for almost every block field `V` of the cell `sys k`, `NontrivialLayer` and
  `StepCorr (fibreGibbs (sys k) (κ₀ k) (βs k) V) (X₀ k) (X₁ k) (W k V) (e^{−c})`. These clauses
  exclude the vacuous instances `κ₀ = 0`, `W = ∅`, `W = {0}` and a non-measurable `B`; gauge
  invariance is relative to the supplied action. The intended instance (not constructed here): for
  `SU(2)` the block map is the restriction of `BlockLattice.blockConf` to one cell, spatial blocks at
  each fine time as in `LayerRate`'s numerics; the cell system carries the fine links of one physical
  cell (side `2^{k+1}` fine steps) with the links outside it absorbed into its plaquette terms;
  `βs k → ∞` is the asymptotically free regime. Blocking in the time direction is excluded: a block
  variable spanning two fine times constrains the new modes on both and gives correlation `1` across
  the step.

**This is a Bałaban-type small-field/large-field statement.** The conditional measure is, for small
coarse fields and couplings `βs k` large, concentrated near the classical minimum on the fibre,
where after an axial gauge fixing inside the cell it is near-Gaussian with the free lattice
dispersion of section 4; uniformity in `V` needs a separate large-field bound. That is the shape of
Bałaban's renormalisation-group control of the Wilson measure (small-field Gaussian domination,
large-field suppression by `e^{−β p(ε)}`), cited, not formalised. The module does not decide whether
(i) holds in the stated `∀ᵐ V` form or only after removing a large-field set (section 6).

**What must be in `W`** (`research/code/cond_gap_checks.py`, part A, exact). In 2D, temporal gauge,
one doubled spatial link with the block field held, the new mode is the midpoint variable `X` on the
fibre `{U₀ U₁ = V}` and its one-step kernel is the convolution by `w²`; its conditional gap is
`−log(I₂(2β)/I₁(2β))` (`SU(2)`), `−log(I₁(2β)/I₀(2β))` (`U(1)`), with `β · gap = 0.7507`, `0.2502` at
`β = 256`: the gap tends to `0` like `3/(4β)`, `1/(4β)`. These modes are gauge-variant (the residual
gauge transformation at the middle site is transitive on the fibre) and carry the static-charge
energy. So `W k V` must consist of gauge-invariant functions (invariant under the fine gauge
transformations that fix the block field, cf. `BlockLattice.blockConf_gauge`), or a Gauss-law sector
after gauge fixing. In 2D there are no gauge-invariant new modes given the spatial block field
(`W = {constants}`, rate `0` at every `β`), so 2D tests (i) only vacuously.

## 3. Poincaré to contraction

Finite form, in the `GapL2` objects:

* `dir π K g = ½ Σ π(x) K(x,y) (g x − g y)²`, the Dirichlet form; `dir_eq`:
  `dir π K g = ‖g‖² − ⟨g, K g⟩` for a Markov pair.
* `nsq_mulVec_eq_dir` (reversible `K`): `‖K g‖² = ‖g‖² − dir π (K K) g`.
* `contr_on_of_poincare`, `contr_of_poincare`: a Poincaré inequality `λ ‖g‖² ≤ dir π (K K) g` on
  mean-zero `g` (in `W`) gives `‖K g‖² ≤ e^{−λ} ‖g‖²`: per-step rate `e^{−λ/2}`.
  `poincare_iff_contr`: `Contr π K r ↔ Poincaré (K K) (1 − r²)` — the per-step contraction **is** a
  Poincaré inequality for the two-step kernel; nothing is lost in the reduction.
* Continuous time: `gronwall_decay` (`φ' ≤ −2λ φ` gives `φ t ≤ e^{−2λ t} φ 0`), and
  `semigroup_contr`: a generator `L` with `π L = 0` and Poincaré constant `λ`
  (`λ ‖g‖² ≤ −⟨g, L g⟩`), and a family `P t` solving `d/dt (P t f) = L (P t f)`, `P 0 = 1`, give
  `Contr π (P t) (e^{−λ t})` at `t ≥ 0`. `semigroup_slab`: with `Markov π (P dt)`, the slab of
  `n` steps of spacing `a`, `n a ≥ τ`, has `ρ ≤ e^{−λ dt τ / a}`.

## 4. The Gaussian (free) limit: the lowest new-mode mass of the doubling

For a free lattice field the transfer eigenvalue at spatial momentum `p` is `e^{−E_p}` with
`cosh E_p = 1 + ω̂²/2`, `ω̂² = Σ_j 4 sin²(p_j/2)` (lattice units, standard, cited; checked in the
script). A new mode of the doubling has some `|p_i| ∈ [π/2, π]`.

* `sin_sq_half_ge`, `omegaSq_ge_two`: then `ω̂² ≥ 2`.
* `cosh_log_two_add_sqrt_three`: `cosh(log(2 + √3)) = 2`, i.e. `arccosh 2 = log(2 + √3) ≈ 1.317`.
* `newMode_mass_ge`: `E_p ≥ arccosh 2` for every new mode; `newMode_mass_attained`: equality at
  `p = (π/2) e_i`. `exp_neg_arccosh_two`: the per-step factor `e^{−arccosh 2} = 2 − √3`.
* `freeLayerRate_summable`: with `c = arccosh 2` the layer rates of `LayerRate.layerRate` are
  summable.

Script, part C: the Fourier new layer on `N³` has `E_min = arccosh 2 = 1.316958` for `4 | N`
(`N = 4 … 64`; `1.5668`, `1.4794` at `N = 6, 10`); the free field conditioned on the `2³` spatial
block averages at every time has lag-one canonical correlation `2 − √3 = 0.267949`, i.e.
`c = arccosh 2` to six digits, at `N = 4, 8, 16`. These numbers are for the free massless **scalar**
(each component of the free photon in Feynman gauge has the same dispersion). That the
gauge-invariant new modes of the free gauge field in axial gauge have the same constant
`c = arccosh 2` at every zoom is stated here, not computed.

## 5. The link to `hW` (finite form)

State space `C × F` (block value, fibre coordinate), joint weight `p(V) m_V(y)` (`jointPi`), and the
coarse-conditioned kernel `condKer Q` that acts by `Q V` on the fibre of `V` and does not move `V`.

* `condKer_mulVec`, `nsq_joint`; `layer_of_fibres`: fibrewise contraction by `r` on `W_V` gives the
  contraction by `r` of every `w` whose fibre restrictions lie in `W_V`.
* `hW_of_cond`: a slab kernel `K'` within `ε` of `condKer Q` on `W` (relative `L²` norm) has rate
  `r + ε` on `W`.
* `hW_of_condGap`: per-step fibre rate `e^{−c}` on invariant `W_V`, `n a ≥ τ`, and the bound `ε`
  give `‖K' w‖² ≤ (e^{−c τ / a} + ε)² ‖w‖²`: the `hW` of `LayerRate.refine_step_*` with
  `r_W = e^{−c τ / a} + ε`. Its `hstep` has no mean-zero clause, so `W_V` must exclude the fibre
  constants (section 7 takes the mean-zero part). The **slab–conditioned defect** `ε` absorbs every
  difference between the slab `K'` and the conditioned `n`-step kernel on `W`, measured relative to
  the state: the movement of the block field while the new modes evolve, and anything else in which
  the two kernels differ. It is part of the remaining input.

## 7. Wiring

* `Realises m X₀ X₁ π Q Z`: a finite Markov transfer `(π, Q)` realises the two-slice law of the
  (unnormalised) fibre measure `m`; true by definition when `Q` is the conditional law of `X₁` given
  `X₀` under `m / Z`.
* `corrOn_of_stepCorr`: on a realisation, `StepCorr` is the `GapL2.Corr` bound on the mean-zero
  functions of `W`. `contrOn_of_corrOn`: for a Markov pair mapping `W` into itself this is the
  contraction on mean-zero `g ∈ W` (restricted `GapL2.corr_iff_contr`; reversibility not needed).
* `hW_of_stepCorr`: the per-step correlation on every fibre gives the `hW` of `refine_step_*`.
* `WilsonCondUVGap.at_atoms`, `hW_of_wilsonCondUVGap`: at a zoom with finitely many block values,
  each of positive law, and finite slices, `WilsonCondUVGap` together with the realisations, the
  invariance of `W k V` under `Q V` and the bound `ε` gives `∃ c > 0` and the `hW`. So
  `WilsonCondUVGap → hW → refine_step_*` is a chain of theorems; the inputs left are (i) itself,
  the finite realisation of the fibre measures, and `ε`.

## 6. Which regime each tool covers

* **Bakry–Émery.** On `SU(N)` with the metric in which `Ric = N/4`, a potential `β V` with
  `Hess V ≥ −H` gives the curvature constant `beConst N H β = N/4 − β H` (the criterion is cited).
  `beConst_pos_iff`: positive iff `β < N/(4H)`; `beConst_tendsto_atBot`: it tends to `−∞` as
  `β → ∞`. So Bakry–Émery covers the strong-coupling window only — the regime of `StrongCoupling`,
  opposite to (i). For `U(1)` (`Ric = 0`, `beConst_torus_neg`) it covers no `β > 0` once `H > 0`.
  Script, part B: the fibre of a two-plaquette block is a von Mises circle (`U(1)`,
  `κ = 2β cos(θ_V/2)`) or a von Mises–Fisher `S³` (`SU(2)`, unit radius, `κ = 2β cos(α/2)`); its
  Poincaré constant is `λ/κ = 0.9994`, `1.0005` at `κ = 1024` (Gaussian concentration) while the
  Bakry–Émery bound `−κ`, `2 − κ` is negative for `κ > 0`, `κ > 2`. In units of `β` the constant is
  `2 cos(θ_V/2)` for small coarse fields and tends to `0` as `θ_V → π`, the large-field region,
  whose probability at `|θ_V| > 0.9π` is `8.0·10⁻¹³` at `β = 16` and `2.4·10⁻⁴⁸` at `β = 64`.
* **Brascamp–Lieb / Helffer–Sjöstrand after axial gauge fixing**, the asymptotically free regime:
  needs (a) convexity of the gauge-fixed fibre potential near the minimum, `Hess ≥ β (m₀² − C ε)` on
  the small-field set with `m₀² = 2` the free new-mode floor of section 4 (`ω̂² ≥ 2`), and (b) a
  large-field bound. Neither is formalised (Brascamp–Lieb is cited).

**The remaining hypothesis for 4D `SU(N)`**, in the finite form consumed by `LayerRate`: uniformly in
the zoom `k` and the block field `V`, a Poincaré constant `λ₀ > 0` for the reversible two-step
conditional transfer of the gauge-invariant new modes on one physical cell (equivalently, by
`poincare_iff_contr`, the per-step rate `e^{−c}` with `1 − e^{−2c} = λ₀`), at couplings
`βs k → ∞`; and the slab–conditioned defect `ε_k` with `e^{−c τ / a_k} + ε_k` below the floor `ρb`
of `LayerRate.relFloor_*`. For the free scalar model `λ₀ = 1 − (2 − √3)² = 4√3 − 6`.

DERIVED (module-wide): `0` the mean that selects the readings orthogonal to the vacuum and the sign
of every bound; `1` the unit transfer and `P 0 = 1`; `2` the degree of the norm, the two-step kernel
`K K`, the doubling and the factor in `d/dt ‖v‖² = 2⟨v, L v⟩`; `½` the double counting in `dir`;
`4` in `4 sin²` the lattice Laplacian symbol and in `N/4` the Ricci constant of `SU(N)`; `3` from
`(2 + √3)(2 − √3) = 1`.
-/

noncomputable section

namespace MassGap.CondGap

open MeasureTheory ProbabilityTheory Filter Topology Matrix GapL2
open MassGap.LatticeGauge MassGap.LayerRate MassGap.FixedAperture
open scoped ENNReal

/-! ## 1. The conditional measure given the block field -/

section Disint

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]

/-- **`κ` is a conditional measure of `P` given the block map `B`**: a Markov kernel with
`(P.map B) ⊗ₘ κ = P.map (U ↦ (B U, U))`. -/
def IsCondMeasure (P : Measure Ω) (B : Ω → C) (κ : Kernel C Ω) : Prop :=
  IsMarkovKernel κ ∧ (P.map B) ⊗ₘ κ = P.map (fun U => (B U, U))

/-- **A conditional measure exists** on a standard Borel configuration space. -/
theorem exists_condMeasure [StandardBorelSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (B : Ω → C) : ∃ κ : Kernel C Ω, IsCondMeasure P B κ :=
  ⟨condDistrib id B P, inferInstance, compProd_map_condDistrib measurable_id.aemeasurable⟩

/-- **The conditional measure lives on the fibre**: for almost every block value `V`,
`κ V`-almost every `U` has `B U = V`. -/
theorem IsCondMeasure.ae_fibre {P : Measure Ω} [IsFiniteMeasure P] {B : Ω → C} {κ : Kernel C Ω}
    (h : IsCondMeasure P B κ) (hB : Measurable B)
    (hD : MeasurableSet {p : C × Ω | B p.2 = p.1}) :
    ∀ᵐ V ∂(P.map B), ∀ᵐ U ∂(κ V), B U = V := by
  haveI := h.1
  have h0 : ∀ᵐ p ∂((P.map B) ⊗ₘ κ), B p.2 = p.1 := by
    have hBU : Measurable (fun U => (B U, U)) := hB.prodMk measurable_id
    rw [h.2, ae_map_iff hBU.aemeasurable hD]
    exact Filter.Eventually.of_forall fun U => rfl
  exact Measure.ae_ae_of_ae_compProd h0

/-- **A density on the fibres disintegrates the weighted measure**: if `κ₀` disintegrates `ν` over
`B`, then `κ₀` weighted by `w` disintegrates `ν.withDensity w` (unnormalised). -/
theorem compProd_fibreWeight {ν : Measure Ω} [IsFiniteMeasure ν] {B : Ω → C} (hB : Measurable B)
    {κ₀ : Kernel C Ω} [IsSFiniteKernel κ₀] (h : (ν.map B) ⊗ₘ κ₀ = ν.map (fun U => (B U, U)))
    {w : Ω → ℝ≥0∞} (hw : Measurable w) (hwt : ∀ U, w U ≠ ∞) :
    (ν.map B) ⊗ₘ (κ₀.withDensity fun _ U => w U) = (ν.withDensity w).map (fun U => (B U, U)) := by
  have hBU : Measurable (fun U => (B U, U)) := hB.prodMk measurable_id
  have hwu : Measurable (Function.uncurry fun (_ : C) (U : Ω) => w U) := hw.comp measurable_snd
  haveI : IsSFiniteKernel (κ₀.withDensity fun _ U => w U) :=
    Kernel.IsSFiniteKernel.withDensity κ₀ fun _ U => hwt U
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hBU hs, withDensity_apply _ (hBU hs)]
  have hF : Measurable (s.indicator fun p : C × Ω => w p.2) := (hw.comp measurable_snd).indicator hs
  have key := congrArg (fun m => ∫⁻ p, s.indicator (fun p : C × Ω => w p.2) p ∂m) h
  rw [Measure.lintegral_compProd hF, lintegral_map hF hBU] at key
  calc ∫⁻ V, (κ₀.withDensity fun _ U => w U) V (Prod.mk V ⁻¹' s) ∂(ν.map B)
      = ∫⁻ V, ∫⁻ U, s.indicator (fun p : C × Ω => w p.2) (V, U) ∂κ₀ V ∂(ν.map B) := by
        refine lintegral_congr fun V => ?_
        rw [Kernel.withDensity_apply' _ hwu, ← lintegral_indicator (measurable_prodMk_left hs)]
        rfl
    _ = ∫⁻ U, s.indicator (fun p : C × Ω => w p.2) (B U, U) ∂ν := key
    _ = ∫⁻ U in (fun U => (B U, U)) ⁻¹' s, w U ∂ν := by
        rw [← lintegral_indicator (hBU hs)]; rfl

end Disint

section Wilson

variable {G : Type} [MeasurableSpace G]

/-- **The fibre Gibbs measure**: the fibre measure `κ₀ V` weighted by the Boltzmann weight
`e^{−β S}` of the cell system (unnormalised). With `κ₀` the conditional of the product Haar measure
given the block map, this is "density `∝ e^{−β S}` on the fibre `{B U = V}` with respect to the
fibre's Haar measure". -/
def fibreGibbs (sys : System G) {C : Type*} [MeasurableSpace C] (κ₀ : Kernel C sys.Config)
    [IsSFiniteKernel κ₀] (β : ℝ) : Kernel C sys.Config :=
  κ₀.withDensity fun _ U => ENNReal.ofReal (sys.boltz β U)

/-- **The fibre Gibbs measure disintegrates the Wilson–Gibbs measure**: if `κ₀` is a conditional
measure of the product measure `vol μ` given `B` and the Boltzmann weight is measurable, then
`(vol μ).map B ⊗ₘ fibreGibbs = ((vol μ).withDensity e^{−β S}).map (U ↦ (B U, U))`. -/
theorem fibreGibbs_disintegrates (sys : System G) (μ : Measure G) [IsProbabilityMeasure μ]
    {C : Type*} [MeasurableSpace C] {B : sys.Config → C} (hB : Measurable B)
    {κ₀ : Kernel C sys.Config} [IsSFiniteKernel κ₀] (h : IsCondMeasure (sys.vol μ) B κ₀) {β : ℝ}
    (hb : Measurable (sys.boltz β)) :
    ((sys.vol μ).map B) ⊗ₘ fibreGibbs sys κ₀ β
      = ((sys.vol μ).withDensity fun U => ENNReal.ofReal (sys.boltz β U)).map
          (fun U => (B U, U)) := by
  haveI : IsProbabilityMeasure (sys.vol μ) := by unfold System.vol; infer_instance
  exact compProd_fibreWeight (w := fun U => ENNReal.ofReal (sys.boltz β U)) hB h.2
    (ENNReal.measurable_ofReal.comp hb) fun _ => ENNReal.ofReal_ne_top

end Wilson

/-! ## 2. The statement of (i) -/

section Statement

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- **The per-step correlation of the new modes**: under `m`, mean-zero `f, g ∈ W` (read on the
slices `X₀`, `X₁`, square-integrable) have `(∫ f(X₀) g(X₁))² ≤ r² ∫ f(X₀)² ∫ g(X₁)²`. Homogeneous
in `m`, so `m` may be the unnormalised conditional measure. -/
def StepCorr (m : Measure Ω) (X₀ X₁ : Ω → S) (W : Set (S → ℝ)) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ f ∈ W, ∀ g ∈ W, MemLp (fun x => f (X₀ x)) 2 m → MemLp (fun x => g (X₁ x)) 2 m →
    ∫ x, f (X₀ x) ∂m = 0 → ∫ x, g (X₁ x) ∂m = 0 →
    (∫ x, f (X₀ x) * g (X₁ x) ∂m) ^ 2
      ≤ r ^ 2 * (∫ x, f (X₀ x) ^ 2 ∂m) * ∫ x, g (X₁ x) ^ 2 ∂m

/-- **A gauge-invariant layer.** `act` is an action of the fine gauge transformations that fix the
block field on configurations (`fixB`), `actS` its action on a fine slice, intertwined by both slice
maps (`slice₀`, `slice₁`); every function in `W` is invariant under `actS`. `LatticeGauge.System`
carries no site structure, and the tree's gauge action (`GaugeInvariantAlgebra.igaugeTransform`)
lives on the infinite configurations `IConf`, so the action is an explicit parameter here. -/
structure GaugeInvariantLayer {C Γ : Type*} (act : Γ → Ω → Ω) (actS : Γ → S → S)
    (X₀ X₁ : Ω → S) (B : Ω → C) (W : Set (S → ℝ)) : Prop where
  fixB : ∀ g U, B (act g U) = B U
  slice₀ : ∀ g U, X₀ (act g U) = actS g (X₀ U)
  slice₁ : ∀ g U, X₁ (act g U) = actS g (X₁ U)
  inv : ∀ f ∈ W, ∀ g s, f (actS g s) = f s

/-- **A non-trivial layer**: `W` contains a square-integrable, mean-zero function of the slice with
positive norm under `m`. Excludes `W = ∅`, `W = {0}`, `W = {constants}` and `m = 0`. -/
def NontrivialLayer (m : Measure Ω) (X₀ : Ω → S) (W : Set (S → ℝ)) : Prop :=
  ∃ f ∈ W, MemLp (fun x => f (X₀ x)) 2 m ∧ ∫ x, f (X₀ x) ∂m = 0 ∧ 0 < ∫ x, f (X₀ x) ^ 2 ∂m

/-- **Input (i), the conditional UV gap, on the Wilson cell.** Cells `sys k` (one physical cell at
zoom `k+1`), block maps `B k` (intended for `SU(2)`: the cell restriction of
`BlockLattice.blockConf`), fibre Haar measures `κ₀ k`, bare couplings `βs k`, fine slices `X₀ k`,
`X₁ k` at consecutive times, new-mode spaces `W k V`, and the fine gauge transformations `act k`,
`actS k` that fix the block field. The statement asks:
* `βs k → ∞` (the asymptotically free regime);
* `B k` measurable and `κ₀ k` a conditional measure of the product measure given `B k` (so the law
  of the block field is a probability measure and `κ₀ k` is Markov);
* every `W k V` a gauge-invariant layer, and the Boltzmann weight gauge invariant;
* there is `c > 0` such that at every zoom, for almost every block field `V`, the layer is
  non-trivial under the fibre Gibbs measure and its per-step correlation is at most `e^{−c}`.
Not proved in this module. The cell `sys k`, the slices `X₀ k`, `X₁ k` and the action are
parameters, not tied here to a Wilson cell, consecutive time slices or the lattice gauge action:
with `X₁` constant, or with slices reading independent links, or with a trivial action, the
statement holds at any `c`. Its content is the intended instance; in `hW_of_wilsonCondUVGap` the
link to the actual slab is the defect `ε` (`hpert`), which a degenerate choice of slices does not
make small. -/
def WilsonCondUVGap {G : Type} [MeasurableSpace G] (sys : ℕ → System G) (μ : Measure G)
    {C : ℕ → Type} [∀ k, MeasurableSpace (C k)] {Sl : ℕ → Type} [∀ k, MeasurableSpace (Sl k)]
    {Γ : ℕ → Type} (B : ∀ k, (sys k).Config → C k) (κ₀ : ∀ k, Kernel (C k) (sys k).Config)
    [∀ k, IsSFiniteKernel (κ₀ k)] (βs : ℕ → ℝ)
    (X₀ X₁ : ∀ k, (sys k).Config → Sl k) (W : ∀ k, C k → Set (Sl k → ℝ))
    (act : ∀ k, Γ k → (sys k).Config → (sys k).Config) (actS : ∀ k, Γ k → Sl k → Sl k) : Prop :=
  Tendsto βs atTop atTop ∧
  (∀ k, Measurable (B k)) ∧
  (∀ k, IsCondMeasure ((sys k).vol μ) (B k) (κ₀ k)) ∧
  (∀ k V, GaugeInvariantLayer (act k) (actS k) (X₀ k) (X₁ k) (B k) (W k V)) ∧
  (∀ k g U, (sys k).boltz (βs k) (act k g U) = (sys k).boltz (βs k) U) ∧
  ∃ c : ℝ, 0 < c ∧ ∀ k, ∀ᵐ V ∂((sys k).vol μ).map (B k),
    NontrivialLayer (fibreGibbs (sys k) (κ₀ k) (βs k) V) (X₀ k) (W k V) ∧
    StepCorr (fibreGibbs (sys k) (κ₀ k) (βs k) V) (X₀ k) (X₁ k) (W k V) (Real.exp (-c))

end Statement

/-! ## 3. Poincaré to contraction -/

section Poincare

variable {α : Type*} [Fintype α]

/-- **The Dirichlet form** `½ Σ π(x) K(x,y) (g x − g y)²`. -/
def dir (π : α → ℝ) (K : Matrix α α ℝ) (g : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, π x * K x y * (g x - g y) ^ 2

/-- **The Dirichlet form of a Markov pair**: `dir π K g = ‖g‖² − ⟨g, K g⟩`. -/
theorem dir_eq {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (g : α → ℝ) :
    dir π K g = nsq π g - ip π g (K *ᵥ g) := by
  have h1 : ∑ x, ∑ y, π x * K x y * g x ^ 2 = nsq π g := by
    unfold nsq
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, M.row x, mul_one]
  have h2 : ∑ x, ∑ y, π x * K x y * g y ^ 2 = nsq π g := by
    rw [Finset.sum_comm]
    unfold nsq
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, M.stat y]
  have h3 : ∑ x, ∑ y, π x * K x y * (g x * g y) = ip π g (K *ᵥ g) := by
    unfold ip
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mulVec_apply', Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e : ∀ x y, π x * K x y * (g x - g y) ^ 2 = π x * K x y * g x ^ 2
      - 2 * (π x * K x y * (g x * g y)) + π x * K x y * g y ^ 2 := fun x y => by ring
  have hsplit : ∑ x, ∑ y, π x * K x y * (g x - g y) ^ 2 = ∑ x, ∑ y, π x * K x y * g x ^ 2
      - 2 * ∑ x, ∑ y, π x * K x y * (g x * g y) + ∑ x, ∑ y, π x * K x y * g y ^ 2 := by
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold dir
  rw [hsplit, h1, h2, h3]
  ring

/-- **The one-step norm of a reversible kernel**: `‖K g‖² = ‖g‖² − dir π (K K) g`. -/
theorem nsq_mulVec_eq_dir {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    (g : α → ℝ) : nsq π (K *ᵥ g) = nsq π g - dir π (K * K) g := by
  rw [dir_eq (M.mul M), ← Matrix.mulVec_mulVec, ip_mulVec_symm hrev, ← nsq_eq_ip]
  ring

/-- **A Poincaré inequality on a set `W`**: `λ ‖g‖² ≤ dir π K g` for mean-zero `g ∈ W`. -/
def PoincareOn (π : α → ℝ) (K : Matrix α α ℝ) (W : Set (α → ℝ)) (lam : ℝ) : Prop :=
  ∀ g ∈ W, mean π g = 0 → lam * nsq π g ≤ dir π K g

theorem exp_neg_half_sq (lam : ℝ) : Real.exp (-(lam / 2)) ^ 2 = Real.exp (-lam) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- **Poincaré for the two-step kernel gives the per-step contraction on `W`**:
`‖K g‖² ≤ e^{−λ} ‖g‖²`, i.e. rate `e^{−λ/2}`. -/
theorem contr_on_of_poincare {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    {W : Set (α → ℝ)} {lam : ℝ} (hP : PoincareOn π (K * K) W lam) :
    ∀ g ∈ W, mean π g = 0 → nsq π (K *ᵥ g) ≤ Real.exp (-(lam / 2)) ^ 2 * nsq π g := by
  intro g hgW hg
  rw [nsq_mulVec_eq_dir M hrev, exp_neg_half_sq]
  have h1 := hP g hgW hg
  have h3 : 1 - lam ≤ Real.exp (-lam) := by linarith [Real.add_one_le_exp (-lam)]
  nlinarith [mul_le_mul_of_nonneg_right h3 (nsq_nonneg M.pi_nonneg g)]

/-- **Poincaré for the two-step kernel gives `Contr π K (e^{−λ/2})`.** -/
theorem contr_of_poincare {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    {lam : ℝ} (hP : PoincareOn π (K * K) Set.univ lam) : Contr π K (Real.exp (-(lam / 2))) :=
  ⟨(Real.exp_pos _).le, fun g hg => contr_on_of_poincare M hrev hP g (Set.mem_univ g) hg⟩

/-- **The per-step contraction is a Poincaré inequality for the two-step kernel**:
`Contr π K r ↔ PoincareOn π (K K) univ (1 − r²)` at `r ≥ 0`. -/
theorem poincare_iff_contr {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    {r : ℝ} (hr : 0 ≤ r) : Contr π K r ↔ PoincareOn π (K * K) Set.univ (1 - r ^ 2) := by
  constructor
  · intro h g _ hg
    have := h.2 g hg
    rw [nsq_mulVec_eq_dir M hrev] at this
    linarith
  · intro h
    refine ⟨hr, fun g hg => ?_⟩
    have := h g (Set.mem_univ g) hg
    rw [nsq_mulVec_eq_dir M hrev]
    linarith

/-- **Grönwall**: `φ' ≤ −2λ φ` everywhere gives `φ t ≤ e^{−2λ t} φ 0` at `t ≥ 0`. -/
theorem gronwall_decay {φ φ' : ℝ → ℝ} {lam : ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hle : ∀ t, φ' t ≤ -(2 * lam) * φ t) {t : ℝ} (ht : 0 ≤ t) :
    φ t ≤ Real.exp (-(2 * lam * t)) * φ 0 := by
  have hψ : ∀ s, HasDerivAt (fun s => Real.exp (2 * lam * s) * φ s)
      (Real.exp (2 * lam * s) * (2 * lam) * φ s + Real.exp (2 * lam * s) * φ' s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (2 * lam * s)) (Real.exp (2 * lam * s) * (2 * lam)) s := by
      have h0 : HasDerivAt (fun s => 2 * lam * s) (2 * lam) s := by
        simpa using (hasDerivAt_id s).const_mul (2 * lam)
      exact h0.exp
    exact he.mul (hd s)
  have hanti : Antitone (fun s => Real.exp (2 * lam * s) * φ s) := by
    refine antitone_of_deriv_nonpos (fun s => (hψ s).differentiableAt) fun s => ?_
    rw [(hψ s).deriv]
    have hp := Real.exp_pos (2 * lam * s)
    nlinarith [mul_le_mul_of_nonneg_left (hle s) hp.le]
  have h := hanti ht
  simp only [mul_zero, Real.exp_zero, one_mul] at h
  have hp := Real.exp_pos (2 * lam * t)
  rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ hp, mul_comm]
  exact h

/-- A function with zero derivative everywhere is constant. -/
theorem const_of_hasDerivAt_zero {f : ℝ → ℝ} (hd : ∀ t, HasDerivAt f 0 t) (t : ℝ) : f t = f 0 := by
  have h1 : Antitone f := antitone_of_deriv_nonpos (fun s => (hd s).differentiableAt)
    fun s => by rw [(hd s).deriv]
  have hn : ∀ s, HasDerivAt (fun s => -1 * f s) (-1 * 0) s := fun s => (hd s).const_mul (-1)
  have h2 : Antitone (fun s => -1 * f s) := antitone_of_deriv_nonpos
    (fun s => (hn s).differentiableAt) fun s => by rw [(hn s).deriv]; norm_num
  rcases le_total 0 t with h | h
  · have := h1 h; have := h2 h; linarith
  · have := h1 h; have := h2 h; linarith

/-- **The semigroup of a generator with a Poincaré constant contracts**: `π L = 0`,
`λ ‖g‖² ≤ −⟨g, L g⟩` on mean-zero `g`, and `d/dt (P t f) = L (P t f)`, `P 0 = 1`, give
`Contr π (P t) (e^{−λ t})` at `t ≥ 0`. -/
theorem semigroup_contr [DecidableEq α] {π : α → ℝ} {L : Matrix α α ℝ}
    (hL : ∀ y, ∑ x, π x * L x y = 0) {lam : ℝ}
    (hP : ∀ g, mean π g = 0 → lam * nsq π g ≤ -ip π g (L *ᵥ g))
    {P : ℝ → Matrix α α ℝ} (hP0 : P 0 = 1)
    (hder : ∀ f : α → ℝ, ∀ t, HasDerivAt (fun s => P s *ᵥ f) (L *ᵥ (P t *ᵥ f)) t)
    {t : ℝ} (ht : 0 ≤ t) : Contr π (P t) (Real.exp (-(lam * t))) := by
  refine ⟨(Real.exp_pos _).le, fun g hg => ?_⟩
  set v : ℝ → α → ℝ := fun s => P s *ᵥ g with hv
  have hc : ∀ s x, HasDerivAt (fun s => v s x) ((L *ᵥ v s) x) s :=
    fun s x => hasDerivAt_pi.1 (hder g s) x
  -- the mean is conserved
  have hmean : ∀ s, mean π (v s) = 0 := by
    have hd : ∀ s, HasDerivAt (fun s => mean π (v s)) 0 s := by
      intro s
      have h := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => (hc s x).const_mul (π x))
      have e : ∑ x, π x * (L *ᵥ v s) x = 0 := by
        simp only [mulVec_apply', Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [show ∑ x, π x * (L x y * v s y) = (∑ x, π x * L x y) * v s y by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring, hL y, zero_mul]
      rw [e] at h
      exact h
    intro s
    rw [const_of_hasDerivAt_zero hd s]
    simp only [hv, hP0, Matrix.one_mulVec]
    exact hg
  -- the derivative of the norm
  have hd : ∀ s, HasDerivAt (fun s => nsq π (v s)) (2 * ip π (v s) (L *ᵥ v s)) s := by
    intro s
    have hx : ∀ x ∈ (Finset.univ : Finset α), HasDerivAt (fun s => π x * (v s x * v s x))
        (π x * ((L *ᵥ v s) x * v s x + v s x * (L *ᵥ v s) x)) s :=
      fun x _ => ((hc s x).mul (hc s x)).const_mul (π x)
    have h := HasDerivAt.fun_sum hx
    have ef : (fun s => nsq π (v s)) = fun s => ∑ x, π x * (v s x * v s x) := by
      funext s'
      unfold nsq
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [ef]
    refine h.congr_deriv ?_
    unfold ip
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hg2 := gronwall_decay (φ := fun s => nsq π (v s)) hd
    (fun s => by have := hP (v s) (hmean s); linarith) ht
  have e1 : Real.exp (-(lam * t)) ^ 2 = Real.exp (-(2 * lam * t)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e0 : v 0 = g := by simp only [hv, hP0, Matrix.one_mulVec]
  rw [e1]
  simpa only [e0] using hg2

/-- **The slab from a generator's Poincaré constant**: with `Markov π (P dt)`, `dt ≥ 0`, `λ ≥ 0`,
spacing `a > 0` and `n a ≥ τ`, `ρ((P dt)ⁿ) ≤ e^{−λ dt τ / a}`. -/
theorem semigroup_slab [DecidableEq α] {π : α → ℝ} {L : Matrix α α ℝ}
    (hL : ∀ y, ∑ x, π x * L x y = 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hP : ∀ g, mean π g = 0 → lam * nsq π g ≤ -ip π g (L *ᵥ g))
    {P : ℝ → Matrix α α ℝ} (hP0 : P 0 = 1)
    (hder : ∀ f : α → ℝ, ∀ t, HasDerivAt (fun s => P s *ᵥ f) (L *ᵥ (P t *ᵥ f)) t)
    {dt : ℝ} (hdt : 0 ≤ dt) (M : Markov π (P dt)) {a τ : ℝ} {n : ℕ} (ha : 0 < a)
    (hn : τ ≤ n * a) : maxCorr π (P dt ^ n) ≤ Real.exp (-(lam * dt * τ / a)) :=
  maxCorr_slab_le_of_stepGap M ha (mul_nonneg hlam hdt) hn
    (semigroup_contr hL hP hP0 hder hdt)

end Poincare

/-! ## 4. The Gaussian (free) limit: the lowest new-mode mass of the doubling -/

section Free

/-- `sin²(p/2) ≥ 1/2` for `π/2 ≤ |p| ≤ π`. -/
theorem sin_sq_half_ge {p : ℝ} (h1 : Real.pi / 2 ≤ |p|) (h2 : |p| ≤ Real.pi) :
    1 / 2 ≤ Real.sin (p / 2) ^ 2 := by
  have hs : Real.sin (p / 2) ^ 2 = Real.sin (|p| / 2) ^ 2 := by
    rcases abs_cases p with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_div, Real.sin_neg, neg_sq]
  rw [hs]
  have hmono : Real.sin (Real.pi / 4) ≤ Real.sin (|p| / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)
  rw [Real.sin_pi_div_four] at hmono
  have h22 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  nlinarith [mul_le_mul hmono hmono h0 (h0.trans hmono)]

/-- **The lattice symbol of a new mode is at least `2`**: `Σ_j 4 sin²(p_j/2) ≥ 2` when some
`|p_i| ∈ [π/2, π]`. -/
theorem omegaSq_ge_two {d : ℕ} (p : Fin d → ℝ) (i : Fin d) (hi1 : Real.pi / 2 ≤ |p i|)
    (hi2 : |p i| ≤ Real.pi) : 2 ≤ ∑ j, 4 * Real.sin (p j / 2) ^ 2 := by
  have h := Finset.single_le_sum (f := fun j => 4 * Real.sin (p j / 2) ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)
  have := sin_sq_half_ge hi1 hi2
  linarith

/-- **`arccosh 2 = log(2 + √3)`**: `cosh(log(2 + √3)) = 2`. -/
theorem cosh_log_two_add_sqrt_three : Real.cosh (Real.log (2 + Real.sqrt 3)) = 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < 2 + Real.sqrt 3 := by positivity
  rw [Real.cosh_log hpos]
  have hinv : (2 + Real.sqrt 3)⁻¹ = 2 - Real.sqrt 3 :=
    inv_eq_of_mul_eq_one_right (by linear_combination -h3)
  rw [hinv]
  ring

theorem log_two_add_sqrt_three_pos : 0 < Real.log (2 + Real.sqrt 3) :=
  Real.log_pos (by have := Real.sqrt_nonneg 3; linarith)

/-- **The lowest new-mode mass of the free doubling**: a transfer exponent `E ≥ 0` with
`cosh E = 1 + ω̂²/2` at a new-mode momentum has `E ≥ arccosh 2 = log(2 + √3)`. -/
theorem newMode_mass_ge {d : ℕ} (p : Fin d → ℝ) (i : Fin d) (hi1 : Real.pi / 2 ≤ |p i|)
    (hi2 : |p i| ≤ Real.pi) {E : ℝ} (hE : 0 ≤ E)
    (hdisp : Real.cosh E = 1 + (∑ j, 4 * Real.sin (p j / 2) ^ 2) / 2) :
    Real.log (2 + Real.sqrt 3) ≤ E := by
  have h2 := omegaSq_ge_two p i hi1 hi2
  have hc : Real.cosh (Real.log (2 + Real.sqrt 3)) ≤ Real.cosh E := by
    rw [cosh_log_two_add_sqrt_three, hdisp]; linarith
  rw [Real.cosh_le_cosh, abs_of_nonneg log_two_add_sqrt_three_pos.le, abs_of_nonneg hE] at hc
  exact hc

/-- **The floor is attained** at `p = (π/2) e_i`: `ω̂² = 2` there, so `E = arccosh 2` solves the
dispersion relation. -/
theorem newMode_mass_attained {d : ℕ} (i : Fin d) :
    Real.cosh (Real.log (2 + Real.sqrt 3))
      = 1 + (∑ j, 4 * Real.sin ((Pi.single i (Real.pi / 2) : Fin d → ℝ) j / 2) ^ 2) / 2 := by
  rw [cosh_log_two_add_sqrt_three, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, show Real.pi / 2 / 2 = Real.pi / 4 by ring, Real.sin_pi_div_four,
      div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · simp

/-- **The free per-step factor**: `e^{−arccosh 2} = 2 − √3`. -/
theorem exp_neg_arccosh_two : Real.exp (-Real.log (2 + Real.sqrt 3)) = 2 - Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < 2 + Real.sqrt 3 := by positivity
  rw [Real.exp_neg, Real.exp_log hpos]
  exact inv_eq_of_mul_eq_one_right (by linear_combination -h3)

/-- **In the free limit the layer rates are summable along the zoom** with `c = arccosh 2`, at
every physical thickness `τ > 0` and starting spacing `a₀ > 0`. -/
theorem freeLayerRate_summable {a₀ τ : ℝ} (ha : 0 < a₀) (hτ : 0 < τ) :
    Summable (layerRate a₀ (Real.log (2 + Real.sqrt 3)) τ) :=
  layerRate_summable (div_pos (mul_pos log_two_add_sqrt_three_pos hτ) ha)

end Free

/-! ## 5. The link to `hW` (finite form) -/

section Link

variable {C F : Type*} [Fintype C] [Fintype F] [DecidableEq C]

/-- **The coarse-conditioned kernel**: `Q V` on the fibre of `V`; the block value does not move. -/
def condKer (Q : C → Matrix F F ℝ) : Matrix (C × F) (C × F) ℝ :=
  fun x x' => if x.1 = x'.1 then Q x.1 x.2 x'.2 else 0

/-- **The joint weight** `p(V) m_V(y)`. -/
def jointPi (p : C → ℝ) (m : C → F → ℝ) : C × F → ℝ := fun x => p x.1 * m x.1 x.2

theorem condKer_mulVec (Q : C → Matrix F F ℝ) (w : C × F → ℝ) (x : C × F) :
    (condKer Q *ᵥ w) x = (Q x.1 *ᵥ fun y => w (x.1, y)) x.2 := by
  simp only [mulVec_apply', condKer, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x.1]
  · simp
  · intro V _ hV
    simp [Ne.symm hV]
  · simp

omit [DecidableEq C] in
theorem nsq_joint (p : C → ℝ) (m : C → F → ℝ) (u : C × F → ℝ) :
    nsq (jointPi p m) u = ∑ V, p V * nsq (m V) (fun y => u (V, y)) := by
  unfold nsq jointPi
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Fibrewise contraction gives the contraction of the layer**: if `Q V` contracts `W_V` by `r`
in `L²(m_V)` for every `V`, every `w` whose fibre restrictions lie in `W_V` contracts by `r` in
`L²(p m)` under `condKer Q`. -/
theorem layer_of_fibres {p : C → ℝ} (hp : ∀ V, 0 ≤ p V) {m : C → F → ℝ} {Q : C → Matrix F F ℝ}
    {WV : C → Set (F → ℝ)} {r : ℝ}
    (hQ : ∀ V, ∀ u ∈ WV V, nsq (m V) (Q V *ᵥ u) ≤ r ^ 2 * nsq (m V) u)
    {W : Set (C × F → ℝ)} (hW : ∀ w ∈ W, ∀ V, (fun y => w (V, y)) ∈ WV V) :
    ∀ w ∈ W, nsq (jointPi p m) (condKer Q *ᵥ w) ≤ r ^ 2 * nsq (jointPi p m) w := by
  intro w hw
  rw [nsq_joint, nsq_joint, Finset.mul_sum]
  refine Finset.sum_le_sum fun V _ => ?_
  have e : (fun y => (condKer Q *ᵥ w) (V, y)) = Q V *ᵥ fun y => w (V, y) :=
    funext fun y => condKer_mulVec Q w (V, y)
  rw [e]
  calc p V * nsq (m V) (Q V *ᵥ fun y => w (V, y))
      ≤ p V * (r ^ 2 * nsq (m V) fun y => w (V, y)) :=
        mul_le_mul_of_nonneg_left (hQ V _ (hW w hw V)) (hp V)
    _ = r ^ 2 * (p V * nsq (m V) fun y => w (V, y)) := by ring

/-- **The slab within `ε` of the conditioned kernel on `W` has rate `r + ε` on `W`.** -/
theorem hW_of_cond {p : C → ℝ} (hp : ∀ V, 0 ≤ p V) {m : C → F → ℝ} (hm : ∀ V y, 0 ≤ m V y)
    {Q : C → Matrix F F ℝ} {WV : C → Set (F → ℝ)} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hQ : ∀ V, ∀ u ∈ WV V, nsq (m V) (Q V *ᵥ u) ≤ r ^ 2 * nsq (m V) u)
    {W : Set (C × F → ℝ)} (hW : ∀ w ∈ W, ∀ V, (fun y => w (V, y)) ∈ WV V)
    {K' : Matrix (C × F) (C × F) ℝ}
    (hpert : ∀ w ∈ W, nsq (jointPi p m) ((K' - condKer Q) *ᵥ w) ≤ ε ^ 2 * nsq (jointPi p m) w) :
    ∀ w ∈ W, nsq (jointPi p m) (K' *ᵥ w) ≤ (r + ε) ^ 2 * nsq (jointPi p m) w := by
  intro w hw
  have hπ : ∀ x, 0 ≤ jointPi p m x := fun x => mul_nonneg (hp x.1) (hm x.1 x.2)
  have hs : K' *ᵥ w = condKer Q *ᵥ w + (K' - condKer Q) *ᵥ w := by
    rw [Matrix.sub_mulVec]; abel
  rw [hs]
  exact nsq_add_le_sq hπ hr hε (nsq_nonneg hπ w) (layer_of_fibres hp hQ hW w hw) (hpert w hw)

/-- **The `hW` of `refine_step_*` from the conditional per-step gap**: per fibre, `Q V` maps `W_V`
into itself and contracts it by `e^{−c}`; the slab `K'` is within `ε` of the conditioned `n`-step
kernel on `W`; spacing `a > 0`, `n a ≥ τ`, `c ≥ 0`. Then `‖K' w‖² ≤ (e^{−c τ / a} + ε)² ‖w‖²` on
`W`. -/
theorem hW_of_condGap [DecidableEq F] {p : C → ℝ} (hp : ∀ V, 0 ≤ p V) {m : C → F → ℝ}
    (hm : ∀ V y, 0 ≤ m V y) {Q : C → Matrix F F ℝ} {WV : C → Set (F → ℝ)} {c a τ ε : ℝ}
    {n : ℕ} (ha : 0 < a) (hc : 0 ≤ c) (hn : τ ≤ n * a) (hε : 0 ≤ ε)
    (hinv : ∀ V, ∀ u ∈ WV V, Q V *ᵥ u ∈ WV V)
    (hstep : ∀ V, ∀ u ∈ WV V, nsq (m V) (Q V *ᵥ u) ≤ Real.exp (-c) ^ 2 * nsq (m V) u)
    {W : Set (C × F → ℝ)} (hW : ∀ w ∈ W, ∀ V, (fun y => w (V, y)) ∈ WV V)
    {K' : Matrix (C × F) (C × F) ℝ}
    (hpert : ∀ w ∈ W, nsq (jointPi p m) ((K' - condKer fun V => Q V ^ n) *ᵥ w)
      ≤ ε ^ 2 * nsq (jointPi p m) w) :
    ∀ w ∈ W, nsq (jointPi p m) (K' *ᵥ w)
      ≤ (Real.exp (-(c * τ / a)) + ε) ^ 2 * nsq (jointPi p m) w :=
  hW_of_cond hp hm (Real.exp_pos _).le hε
    (fun V => layer_rate_slab (hm V) ha hc hn (hinv V) (hstep V)) hW hpert

end Link

/-! ## 6. Which regime each tool covers -/

section Regime

/-- **The Bakry–Émery constant** on `SU(N)` (`Ric = N/4`) for a potential `β V` with
`Hess V ≥ −H`: `N/4 − β H`. -/
def beConst (N H β : ℝ) : ℝ := N / 4 - β * H

/-- **Bakry–Émery covers `β < N/(4H)` only.** -/
theorem beConst_pos_iff {N H β : ℝ} (hH : 0 < H) : 0 < beConst N H β ↔ β < N / (4 * H) := by
  unfold beConst
  rw [lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- **The Bakry–Émery constant tends to `−∞` as `β → ∞`**: no lower bound in the asymptotically
free regime. -/
theorem beConst_tendsto_atBot {N H : ℝ} (hH : 0 < H) :
    Tendsto (fun β => beConst N H β) atTop atBot := by
  refine Filter.tendsto_atBot.2 fun b => Filter.eventually_atTop.2 ⟨(N / 4 - b) / H, fun β hβ => ?_⟩
  unfold beConst
  have := (div_le_iff₀ hH).1 hβ
  linarith

/-- **On a torus (`U(1)`, `Ric = 0`) Bakry–Émery covers no `β > 0`** once `H > 0`. -/
theorem beConst_torus_neg {H β : ℝ} (hH : 0 < H) (hβ : 0 < β) : beConst 0 H β < 0 := by
  unfold beConst; nlinarith [mul_pos hβ hH]

/-- **The free Poincaré constant of the two-step kernel**: `1 − (2 − √3)² = 4√3 − 6 > 0`, the
`λ₀` of the remaining hypothesis for the free scalar model. -/
theorem free_poincare_const :
    1 - (Real.exp (-Real.log (2 + Real.sqrt 3))) ^ 2 = 4 * Real.sqrt 3 - 6 ∧
      0 < 4 * Real.sqrt 3 - 6 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨by rw [exp_neg_arccosh_two]; nlinarith [h3], ?_⟩
  have : (3 : ℝ) / 2 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

end Regime

/-! ## 7. Wiring: (i) to the `hW` of `refine_step_*` -/

section Wiring

/-- A property that holds almost everywhere holds at every atom. -/
theorem ae_at_atom {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : α → Prop}
    (h : ∀ᵐ x ∂μ, p x) {V : α} (hV : μ {V} ≠ 0) : p V := by
  by_contra hp
  apply hV
  exact measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hp) (ae_iff.1 h)

variable {Ω F : Type*} [MeasurableSpace Ω] [Fintype F]

/-- **A finite transfer realises the two-slice law of `m`**: with normalisation `Z > 0`, the slice
laws are `π` (both slices) and the one-step law is `π(s) Q(s, s')`; every function of a slice is in
`L²(m)`. When `Q` is the conditional law of `X₁` given `X₀` under `m / Z`, this holds by definition. -/
structure Realises (m : Measure Ω) (X₀ X₁ : Ω → F) (π : F → ℝ) (Q : Matrix F F ℝ) (Z : ℝ) :
    Prop where
  pos : 0 < Z
  memLp₀ : ∀ f : F → ℝ, MemLp (fun x => f (X₀ x)) 2 m
  memLp₁ : ∀ g : F → ℝ, MemLp (fun x => g (X₁ x)) 2 m
  mean₀ : ∀ f : F → ℝ, ∫ x, f (X₀ x) ∂m = Z * mean π f
  mean₁ : ∀ g : F → ℝ, ∫ x, g (X₁ x) ∂m = Z * mean π g
  sq₀ : ∀ f : F → ℝ, ∫ x, f (X₀ x) ^ 2 ∂m = Z * nsq π f
  sq₁ : ∀ g : F → ℝ, ∫ x, g (X₁ x) ^ 2 ∂m = Z * nsq π g
  cross : ∀ f g : F → ℝ, ∫ x, f (X₀ x) * g (X₁ x) ∂m = Z * ip π f (Q *ᵥ g)

/-- **`StepCorr` in finite form**: on a realisation, the per-step correlation bound is the
`GapL2.Corr` bound restricted to the mean-zero functions of `W`. -/
theorem corrOn_of_stepCorr {m : Measure Ω} {X₀ X₁ : Ω → F} {π : F → ℝ} {Q : Matrix F F ℝ} {Z : ℝ}
    (hR : Realises m X₀ X₁ π Q Z) {W : Set (F → ℝ)} {r : ℝ} (h : StepCorr m X₀ X₁ W r) :
    ∀ f ∈ W, ∀ g ∈ W, mean π f = 0 → mean π g = 0 →
      ip π f (Q *ᵥ g) ^ 2 ≤ r ^ 2 * nsq π f * nsq π g := by
  intro f hf g hg hf0 hg0
  have h1 := h.2 f hf g hg (hR.memLp₀ f) (hR.memLp₁ g) (by rw [hR.mean₀, hf0, mul_zero])
    (by rw [hR.mean₁, hg0, mul_zero])
  rw [hR.cross, hR.sq₀, hR.sq₁] at h1
  have hZ : 0 < Z ^ 2 := pow_pos hR.pos 2
  have e1 : (Z * ip π f (Q *ᵥ g)) ^ 2 = Z ^ 2 * ip π f (Q *ᵥ g) ^ 2 := by ring
  have e2 : r ^ 2 * (Z * nsq π f) * (Z * nsq π g) = Z ^ 2 * (r ^ 2 * nsq π f * nsq π g) := by ring
  rw [e1, e2] at h1
  exact le_of_mul_le_mul_left h1 hZ

/-- **Correlation to contraction on an invariant layer** (the restricted form of
`GapL2.corr_iff_contr`; a Markov pair suffices, reversibility is not used): if `Q` maps `W` into
itself, the correlation bound on mean-zero `f, g ∈ W` gives `‖Q g‖² ≤ r² ‖g‖²` for mean-zero
`g ∈ W`. -/
theorem contrOn_of_corrOn {π : F → ℝ} {Q : Matrix F F ℝ} (M : Markov π Q) {W : Set (F → ℝ)}
    {r : ℝ} (hinv : ∀ g ∈ W, Q *ᵥ g ∈ W)
    (h : ∀ f ∈ W, ∀ g ∈ W, mean π f = 0 → mean π g = 0 →
      ip π f (Q *ᵥ g) ^ 2 ≤ r ^ 2 * nsq π f * nsq π g) :
    ∀ g ∈ W, mean π g = 0 → nsq π (Q *ᵥ g) ≤ r ^ 2 * nsq π g := by
  intro g hgW hg
  have hm : mean π (Q *ᵥ g) = 0 := by rw [mean_mulVec M.stat, hg]
  have h1 := h _ (hinv g hgW) g hgW hm hg
  rw [← nsq_eq_ip π (Q *ᵥ g)] at h1
  rcases (nsq_nonneg M.pi_nonneg (Q *ᵥ g)).lt_or_eq with hp | hz
  · have h2 : nsq π (Q *ᵥ g) * nsq π (Q *ᵥ g) ≤ nsq π (Q *ᵥ g) * (r ^ 2 * nsq π g) := by
      nlinarith [h1]
    exact le_of_mul_le_mul_left h2 hp
  · rw [← hz]; exact mul_nonneg (sq_nonneg r) (nsq_nonneg M.pi_nonneg g)

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **The `hW` of `refine_step_*` from the per-step correlation on every fibre.** For every block
value `V`: a realisation `(π V, Q V, Z V)` of the fibre measure `m V`, `Markov (π V) (Q V)`, `Q V`
maps `Wf V` into itself, and `StepCorr (m V) X₀ X₁ (Wf V) (e^{−c})`. The new layer `W` has fibre
restrictions in `Wf V` with mean zero on every fibre (fibre constants excluded). With the slab `K'`
within `ε` of the conditioned `n`-step kernel on `W`, `n a ≥ τ`: `‖K' w‖² ≤ (e^{−c τ / a} + ε)² ‖w‖²`. -/
theorem hW_of_stepCorr [DecidableEq F] {p : C → ℝ} (hp : ∀ V, 0 ≤ p V) {m : C → Measure Ω}
    {X₀ X₁ : Ω → F} {π : C → F → ℝ} {Q : C → Matrix F F ℝ} {Z : C → ℝ}
    (hR : ∀ V, Realises (m V) X₀ X₁ (π V) (Q V) (Z V)) (hM : ∀ V, Markov (π V) (Q V))
    {Wf : C → Set (F → ℝ)} (hinv : ∀ V, ∀ u ∈ Wf V, Q V *ᵥ u ∈ Wf V)
    {c a τ ε : ℝ} {n : ℕ} (ha : 0 < a) (hc : 0 ≤ c) (hn : τ ≤ n * a) (hε : 0 ≤ ε)
    (hcorr : ∀ V, StepCorr (m V) X₀ X₁ (Wf V) (Real.exp (-c)))
    {W : Set (C × F → ℝ)}
    (hW : ∀ w ∈ W, ∀ V, (fun y => w (V, y)) ∈ Wf V ∧ mean (π V) (fun y => w (V, y)) = 0)
    {K' : Matrix (C × F) (C × F) ℝ}
    (hpert : ∀ w ∈ W, nsq (jointPi p π) ((K' - condKer fun V => Q V ^ n) *ᵥ w)
      ≤ ε ^ 2 * nsq (jointPi p π) w) :
    ∀ w ∈ W, nsq (jointPi p π) (K' *ᵥ w)
      ≤ (Real.exp (-(c * τ / a)) + ε) ^ 2 * nsq (jointPi p π) w :=
  hW_of_condGap (WV := fun V => {u | u ∈ Wf V ∧ mean (π V) u = 0}) hp
    (fun V y => (hM V).pi_nonneg y) ha hc hn hε
    (fun V u hu => by
      simp only [Set.mem_setOf_eq] at hu ⊢
      exact ⟨hinv V u hu.1, by rw [mean_mulVec (hM V).stat, hu.2]⟩)
    (fun V u hu => by
      simp only [Set.mem_setOf_eq] at hu
      exact contrOn_of_corrOn (hM V) (hinv V) (corrOn_of_stepCorr (hR V) (hcorr V)) u hu.1 hu.2)
    (fun w hw V => by simp only [Set.mem_setOf_eq]; exact hW w hw V) hpert

end Wiring

/-- **(i) at the atoms of the block-field law**: `WilsonCondUVGap` gives one `c > 0` such that at
every zoom and every block value of positive law the layer is non-trivial and has per-step
correlation at most `e^{−c}`. -/
theorem WilsonCondUVGap.at_atoms {G : Type} [MeasurableSpace G] {sys : ℕ → System G}
    {μ : Measure G} {C : ℕ → Type} [∀ k, MeasurableSpace (C k)] {Sl : ℕ → Type}
    [∀ k, MeasurableSpace (Sl k)] {Γ : ℕ → Type} {B : ∀ k, (sys k).Config → C k}
    {κ₀ : ∀ k, Kernel (C k) (sys k).Config} [∀ k, IsSFiniteKernel (κ₀ k)] {βs : ℕ → ℝ}
    {X₀ X₁ : ∀ k, (sys k).Config → Sl k} {W : ∀ k, C k → Set (Sl k → ℝ)}
    {act : ∀ k, Γ k → (sys k).Config → (sys k).Config} {actS : ∀ k, Γ k → Sl k → Sl k}
    (h : WilsonCondUVGap sys μ B κ₀ βs X₀ X₁ W act actS) :
    ∃ c : ℝ, 0 < c ∧ ∀ k V, ((sys k).vol μ).map (B k) {V} ≠ 0 →
      NontrivialLayer (fibreGibbs (sys k) (κ₀ k) (βs k) V) (X₀ k) (W k V) ∧
      StepCorr (fibreGibbs (sys k) (κ₀ k) (βs k) V) (X₀ k) (X₁ k) (W k V) (Real.exp (-c)) := by
  obtain ⟨-, -, -, -, -, c, hc, hk⟩ := h
  exact ⟨c, hc, fun k V hV => ae_at_atom (hk k) hV⟩

/-- **The chain `WilsonCondUVGap → hW`** at zoom `k`, for a finite block-value type every value of
which has positive law, and a finite slice type: given a realisation `(π V, Q V, Z V)` of each fibre
Gibbs measure by a Markov pair that maps `W k V` into itself, a new layer `W'` whose fibre
restrictions lie in `W k V` with mean zero on every fibre, and the slab `K'` within `ε` of the
conditioned `n`-step kernel on `W'`, there is `c > 0` with `‖K' w‖² ≤ (e^{−c τ / a} + ε)² ‖w‖²` on
`W'` — the `hW` of `LayerRate.refine_step_*` with `r_W = e^{−c τ / a} + ε`. -/
theorem hW_of_wilsonCondUVGap {G : Type} [MeasurableSpace G] {sys : ℕ → System G}
    {μ : Measure G} {C : ℕ → Type} [∀ k, MeasurableSpace (C k)] {Sl : ℕ → Type}
    [∀ k, MeasurableSpace (Sl k)] {Γ : ℕ → Type} {B : ∀ k, (sys k).Config → C k}
    {κ₀ : ∀ k, Kernel (C k) (sys k).Config} [∀ k, IsSFiniteKernel (κ₀ k)] {βs : ℕ → ℝ}
    {X₀ X₁ : ∀ k, (sys k).Config → Sl k} {W : ∀ k, C k → Set (Sl k → ℝ)}
    {act : ∀ k, Γ k → (sys k).Config → (sys k).Config} {actS : ∀ k, Γ k → Sl k → Sl k}
    (h : WilsonCondUVGap sys μ B κ₀ βs X₀ X₁ W act actS) (k : ℕ) [Fintype (C k)]
    [DecidableEq (C k)] [Fintype (Sl k)] [DecidableEq (Sl k)]
    (hpos : ∀ V, ((sys k).vol μ).map (B k) {V} ≠ 0) {p : C k → ℝ} (hp : ∀ V, 0 ≤ p V)
    {π : C k → Sl k → ℝ} {Q : C k → Matrix (Sl k) (Sl k) ℝ} {Z : C k → ℝ}
    (hR : ∀ V, Realises (fibreGibbs (sys k) (κ₀ k) (βs k) V) (X₀ k) (X₁ k) (π V) (Q V) (Z V))
    (hM : ∀ V, Markov (π V) (Q V)) (hinv : ∀ V, ∀ u ∈ W k V, Q V *ᵥ u ∈ W k V)
    {a τ ε : ℝ} {n : ℕ} (ha : 0 < a) (hn : τ ≤ n * a) (hε : 0 ≤ ε)
    {W' : Set (C k × Sl k → ℝ)}
    (hW' : ∀ w ∈ W', ∀ V, (fun y => w (V, y)) ∈ W k V ∧ mean (π V) (fun y => w (V, y)) = 0)
    {K' : Matrix (C k × Sl k) (C k × Sl k) ℝ}
    (hpert : ∀ w ∈ W', nsq (jointPi p π) ((K' - condKer fun V => Q V ^ n) *ᵥ w)
      ≤ ε ^ 2 * nsq (jointPi p π) w) :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ W', nsq (jointPi p π) (K' *ᵥ w)
      ≤ (Real.exp (-(c * τ / a)) + ε) ^ 2 * nsq (jointPi p π) w := by
  obtain ⟨c, hc, hat⟩ := h.at_atoms
  exact ⟨c, hc, hW_of_stepCorr hp hR hM hinv ha hc.le hn hε (fun V => (hat k V (hpos V)).2) hW'
    hpert⟩

#print axioms exists_condMeasure
#print axioms IsCondMeasure.ae_fibre
#print axioms compProd_fibreWeight
#print axioms fibreGibbs_disintegrates
#print axioms dir_eq
#print axioms nsq_mulVec_eq_dir
#print axioms exp_neg_half_sq
#print axioms contr_on_of_poincare
#print axioms contr_of_poincare
#print axioms poincare_iff_contr
#print axioms gronwall_decay
#print axioms const_of_hasDerivAt_zero
#print axioms semigroup_contr
#print axioms semigroup_slab
#print axioms sin_sq_half_ge
#print axioms omegaSq_ge_two
#print axioms cosh_log_two_add_sqrt_three
#print axioms log_two_add_sqrt_three_pos
#print axioms newMode_mass_ge
#print axioms newMode_mass_attained
#print axioms exp_neg_arccosh_two
#print axioms freeLayerRate_summable
#print axioms condKer_mulVec
#print axioms nsq_joint
#print axioms layer_of_fibres
#print axioms hW_of_cond
#print axioms hW_of_condGap
#print axioms beConst_pos_iff
#print axioms beConst_tendsto_atBot
#print axioms beConst_torus_neg
#print axioms free_poincare_const
#print axioms ae_at_atom
#print axioms corrOn_of_stepCorr
#print axioms contrOn_of_corrOn
#print axioms hW_of_stepCorr
#print axioms WilsonCondUVGap.at_atoms
#print axioms hW_of_wilsonCondUVGap

end MassGap.CondGap
