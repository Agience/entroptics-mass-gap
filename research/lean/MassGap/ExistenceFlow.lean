import Mathlib
import MassGap.FlowMoments
import MassGap.ClaySUFinal

/-!
# MassGap.ExistenceFlow — the existence input `hU`, read through three reasons

`ClaySUFinal.clayStatementAt_SU_final` takes `hU : ClassMoments hN W (SymPlaqClass N) t C` for one
configuration flow `W` with `PhysRange r`. This module formalises three readings of why `hU` should
hold ("the observer fixes the scale", "asymptotic freedom", "the zoom is self-similar"), proves the
reduction of `hU` to each, and proves one discharge of `hU` outright, at a degenerate flow.

## 1. A flow that meets `hU` and `PhysRange` (proved)

`flatFlow L : ConfFlow N`: at step `k`, inside the box `[-L_k, L_k]⁴` every link is replaced by
`P(x)⁻¹ P(x + μ̂)`, `P(x)` the parallel transporter from the origin to `x` along the axis-ordered path
(`P`); outside the box the link is unchanged. It is continuous (`continuous_flatV`), gauge covariant
(`flatV_gauge`), covariant under the reflections `ireflConf τ 0` (`flatV_refl`), and reads only the
links based in the box, so its range is `2 L_k` (`flatV_local`).

Inside the box the flowed configuration is a gauge transform of the identity configuration, so every
local gauge-invariant field `O` reads, once its support is inside the box, the constant `O(1)`
(`flatFlow_fieldMap`). On `SymPlaqClass N` that constant is `0` (`symPlaq_one`). Hence:

* `classMoments_of_densityEach`: a per-field pointwise bound `|O ∘ V_k| ≤ K a_k⁴` (eventually, one `K`
  for every field of a non-negative class) gives `ClassMoments hN W D 1 (e^{625 K})`;
* `classMoments_flatFlow`: `ClassMoments hN (flatFlow L) (SymPlaqClass N) 1 1` whenever `L_k → ∞`;
* `flat_hU_hphys_hreach`: for `L_k = ⌊1/√a_k⌋`, the flow meets `hU`, vanishing reach
  `a_k · range_k → 0`, and `PhysRange r` of `energy0` at every `r > 0`.

So `hU`, with `PhysRange` and even with vanishing reach, is met by a flow. What the flat flow does
not give (argued from `flatFlow_fieldMap`, not a declaration): its flowed fields are eventually
constant, so the connected Schwinger functions of `energy0 (flatFlow L)` vanish in the limit. The
content left in the existence question is `hU` **together with** the inputs of the capstone that read
the same `W` non-trivially (`hLC`, `hX`, the non-zero vector of `ClayData`). At `flatFlow` the
observer's form `kernF` has rank one, so `preH = ℂ · preVac`, and `PreObserver.preNontrivial` (which
gives a non-zero vector orthogonal to `preVac` from `hLC`, `he1`, `he2`, `hK`, `hAF`) shows `hLC` cannot
hold there together with those inputs: the capstone is vacuous at `flatFlow` (argued from those
declarations, not a separate theorem). The target itself fails there, as a theorem:
`ObserverCarries.not_clayStatementAt_flatFlow` (the flowed fields are eventually constant, so the
observer's form has rank one, and `ClayStatement.ObsGen` makes the Hilbert space its
reconstruction). Not shown either: `SiteExp`, `ClassUnitExp` or `DensityVolumeBound`
on `SymPlaqClass N`. Those are uniform over the class (`∀ᶠ k, ∀ O ∈ D`), while the flat flow
flattens each plaquette only from a step on that depends on the plaquette, and plaquettes outside the
box keep their Wilson value. `ClassMoments` is per field (`∀ O ∈ D, ∀ᶠ k`), which is why it is met.

## 2. Reason (h): "the observer fixes the scale"

Formal content: the observer's reading at a fixed physical size is, pointwise, the cell volume `a⁴`
times a bounded density. The per-field form is `∀ O ∈ D, DensityVolumeBound W {O} K`, and
`classMoments_of_densityEach` proves `hU` from it. The flat flow meets it with `K = 0`.

The averaging reading does not give it: a normalised average over the `≈ (r/a)⁴` plaquettes of a
physical cube is a number in `[0, 2]`, while `hU` needs the mean of the flowed density to be
`O(a⁴)` (`FlowMoments.classMoments_mean_le`); the loss is the site count of the unit cube, not the
size per site (`ObserverMoments`, module docstring). The flowed plaquette is the plaquette of the
flowed configuration, not an average of plaquette densities, and for it to be `O(a⁴)` the flowed
field must vary by `O(a²)` across one lattice spacing.

Why the per-field pointwise form needs a degenerate flow (argued, not formalised): if a continuous
flow keeps every flowed plaquette of a physical `r`-loop inside a contractible neighbourhood of `1`
for every configuration, then the flowed holonomy of that loop is, by non-abelian Stokes, a
continuous function of the flowed plaquettes and of transporters, homotopic to the constant `1`; so
as a map `Cfg → G` it is null-homotopic, and cannot follow the bare holonomy of the loop (which
restricts to the identity map of `G` on one link, not null-homotopic since `π₃(SU(N)) ≠ 0`). A
pointwise `O(a⁴)` bound therefore forces the observer to forget the physical-scale holonomy, as the
flat flow does. For a flow that keeps it, the bound can only be a statement about the measure: large
flowed fields are rare (reason (i)).

## 3. Reason (i): "asymptotic freedom"

Formal content: a split of the one-site exponential moment of `FlowUV.SiteExp` into a small-field
part and a large-field part, `SmallLargeSplit hN W D s M C₁ C₂`: eventually, for every field, a
continuous cut-off `0 ≤ χ ≤ 1` with

* (small field) `ν_k(χ · e^{s a_k⁻⁴ O∘V_k}) ≤ C₁`,
* (large field) `ν_k(1 − χ) ≤ C₂ e^{−s M / a_k⁴}`, `M` a bound on the class.

`siteExp_of_split` proves `SiteExp hN W D s (C₁ + C₂)` from it (`largeField_le`), and
`classMoments_of_split` then `hU` (`ClaySUFinal.classMoments_of_siteExp`).

What each clause asks, against the tree (argued):

* The small-field clause is Gaussian domination: on `{χ > 0}` the flowed density is a quadratic form
  in Lie-algebra fluctuations of variance `≈ g₀²`, smoothed at radius `r`, and its exponential moment
  is the free-field value `(1 − s σ²)^{−3(N²−1)}`, finite for `s < 128π²τ²` uniformly in `a`
  (`FlowUV`, unit tests). No Gaussian reference measure on `ℤ⁴` exists in the tree.
* The large-field clause asks a probability `≤ C₂ e^{−sM/a_k⁴}`. Since `a_k⁻⁴` grows like
  `e^{96π²β_k/(11N²)}`, this is doubly exponential in `β_k`. A single large lattice-scale block costs
  only `e^{−p(g)/g²}` (Bałaban's large-field suppression, recalled in `BalabanUV`), so the cut-off
  `χ` must be defined at the physical scale: `1 − χ` may charge only configurations where a positive
  fraction of the `(r/a)⁴` blocks of the region are large, so that the suppression is
  `e^{−c (r/a)⁴ p(g)/g²}`.
* `BalabanUV.BalabanShape` is a hypothesis on finite `Ladder` systems with a parameter block map, not
  on `stateK`; nothing connects it to `stateK`. `CondGap` states a conditional spectral gap, not
  moments. `HaarMoments` gives `SU(2)` Haar moments at coupling zero. `PlaneVariance` and
  `PeriodicContent` give lower bounds. `EnergySeed` is about the mean action on tori and takes its
  Coulomb-type lower bound `finiteSize ≥ κ/β` as a hypothesis. None of them supplies either clause.

## 4. Reason (j): "the zoom is self-similar"

Formal content: the one-site exponential moment in physical units,
`physExp hN W O s k = ν_k(e^{s a_k⁻⁴ O∘V_k})`, changes by a summable relative amount per zoom step:
`ZoomStable hN W D s ε K`: `physExp (k+1) ≤ (1 + ε_k) physExp k` for `k ≥ K`, with `ε ≥ 0` summable.
`siteExp_of_zoomStable` proves `SiteExp hN W D s (X₀ e^{Σε})` from it and a bound `X₀` at step `K`
(`seq_le_exp_sum`). `classMoments_of_zoomStable` gives `hU`.

Summability is the content (argued): the running coupling alone moves the density only through
`g²(r)`, which is fixed at fixed physical `r`, so the per-step change at fixed `r` is a lattice
artefact, expected `O(a_k²)` (summable along `a_k = a₀ 2^{−(k+1)}`). A per-step change of order
`g_k² ∼ 1/k` would not be summable and the product `∏(1 + c/k)` diverges. The comparison of two
consecutive steps is a comparison of two Wilson measures (`β_k`, `β_{k+1}`) under two flows; the RG
step that makes it a contraction is again a Bałaban-type statement. The flat flow meets
`ZoomStable` with `ε = 0` on each field from a step on (its flowed fields are `0`), which is the
degenerate case again.

## 5. The plain plaquette floor

`not_classMoments_identity_poly`: a polynomial floor `ν_k(1 − Re tr U_q/N) ≥ c β_k^{−m}`, any
`m`, makes `ClassMoments` fail at the identity flow (through `FlowMoments.not_classMoments_identity` at
`λ = 48π²/(11N²)`). So a floor at any polynomial rate suffices for the identity-flow no-go.

`PlaquetteFloor` proves such a floor at `m = 2` for `N ≥ 2`
(`PlaquetteFloor.stateK_plaq_ge`: `ν_k(1 − Re tr U_q/N) ≥ e^{−n(16/N + 2)} / (N β_k²)` for `q` with
distinct directions, `n` the number of plaquettes reading its first link), by one-link conditioning
and a right translation of the link by a fixed element of `SU(N)`, and feeds it to
`not_classMoments_identity_poly` (`PlaquetteFloor.not_classMoments_identity`, no floor hypothesis).

## Contents

* `pt`, `lineF`, `lineB`, `lineZ`, `P`: the transporter along the axis-ordered path; gauge
  (`P_gauge`), reflection (`P_refl`), continuity (`continuous_P`), locality (`P_congr`).
* `inBox`, `flatV`, `flatFlow`, `flatFlow_fieldMap`, `symPlaq_one`.
* `classMoments_of_densityEach`, `classMoments_flatFlow`, `flat_hU_hphys_hreach` — section 1, 2.
* `largeField_le`, `SmallLargeSplit`, `siteExp_of_split`, `classMoments_of_split` — section 3.
* `seq_le_exp_sum`, `physExp`, `ZoomStable`, `siteExp_of_zoomStable`, `classMoments_of_zoomStable`
  — section 4.
* `not_classMoments_identity_poly` — section 5.
-/

noncomputable section

namespace MassGap.ExistenceFlow

open MassGap MassGap.InfiniteLattice MassGap.GaugeInvariantAlgebra MassGap.LatticeReflection Filter
open scoped Topology

/-! ## 1. The transporter along the axis-ordered path -/

section Path

variable {G : Type} [Group G]

/-- The site `y` moved by `n` steps along `μ`.

DERIVED: no numeral. -/
def pt (μ : Fin 4) (y : ISite) (n : ℤ) : ISite := Function.update y μ (y μ + n)

/-- DERIVED: `0` the empty move. -/
theorem pt_zero (μ : Fin 4) (y : ISite) : pt μ y 0 = y := by
  simp [pt]

/-- DERIVED: `1` one step. -/
theorem ishift_pt (μ : Fin 4) (y : ISite) (n : ℤ) : ishift μ (pt μ y n) = pt μ y (n + 1) := by
  funext i
  by_cases h : i = μ
  · subst h
    simp [ishift, pt, add_assoc]
  · simp [ishift, pt, Function.update_of_ne h]

/-- **The forward line**: the transporter from `y` to `y + n μ̂`, `n ≥ 0`.

DERIVED: `0`, `1` the empty product and one step. -/
def lineF (U : IConf G) (μ : Fin 4) (y : ISite) : ℕ → G
  | 0 => 1
  | n + 1 => lineF U μ y n * U (μ, pt μ y n)

/-- **The backward line**: the transporter from `y` to `y − n μ̂`.

DERIVED: `0`, `1` the empty product and one step. -/
def lineB (U : IConf G) (μ : Fin 4) (y : ISite) : ℕ → G
  | 0 => 1
  | n + 1 => lineB U μ y n * (U (μ, pt μ y (-(n : ℤ) - 1)))⁻¹

/-- **The line** from `y` to `y + n μ̂`, `n ∈ ℤ`.

DERIVED: `1` the shift of `Int.negSucc`. -/
def lineZ (U : IConf G) (μ : Fin 4) (y : ISite) : ℤ → G
  | Int.ofNat n => lineF U μ y n
  | Int.negSucc n => lineB U μ y (n + 1)

/-- DERIVED: no numeral. -/
theorem igauge_apply (g : ISite → G) (U : IConf G) (μ : Fin 4) (x : ISite) :
    igaugeTransform g U (μ, x) = g x * U (μ, x) * (g (ishift μ x))⁻¹ := rfl

/-- **The forward line is gauge covariant.**

DERIVED: `0` the base case. -/
theorem lineF_gauge (g : ISite → G) (U : IConf G) (μ : Fin 4) (y : ISite) (n : ℕ) :
    lineF (igaugeTransform g U) μ y n = g y * lineF U μ y n * (g (pt μ y n))⁻¹ := by
  induction n with
  | zero => simp [lineF, pt_zero]
  | succ n ih =>
    simp only [lineF]
    rw [ih, igauge_apply, ishift_pt]
    push_cast
    group

/-- **The backward line is gauge covariant.**

DERIVED: `0` the base case; `1` one step. -/
theorem lineB_gauge (g : ISite → G) (U : IConf G) (μ : Fin 4) (y : ISite) (n : ℕ) :
    lineB (igaugeTransform g U) μ y n = g y * lineB U μ y n * (g (pt μ y (-(n : ℤ))))⁻¹ := by
  induction n with
  | zero => simp [lineB, pt_zero]
  | succ n ih =>
    simp only [lineB]
    have e1 : (-(n : ℤ) - 1) + 1 = -(n : ℤ) := by ring
    have e2 : (-(((n + 1 : ℕ)) : ℤ)) = -(n : ℤ) - 1 := by push_cast; ring
    rw [ih, igauge_apply, ishift_pt, e1, e2]
    group

/-- **The line is gauge covariant.**

DERIVED: `1` the shift of `Int.negSucc`. -/
theorem lineZ_gauge (g : ISite → G) (U : IConf G) (μ : Fin 4) (y : ISite) (n : ℤ) :
    lineZ (igaugeTransform g U) μ y n = g y * lineZ U μ y n * (g (pt μ y n))⁻¹ := by
  cases n with
  | ofNat m => exact lineF_gauge g U μ y m
  | negSucc m =>
    have e : pt μ y (-(((m + 1 : ℕ)) : ℤ)) = pt μ y (Int.negSucc m) := rfl
    show lineB (igaugeTransform g U) μ y (m + 1) = g y * lineB U μ y (m + 1) * _
    rw [lineB_gauge, e]

/-- **The transporter from the origin to `x`** along the axis-ordered path: `x₀` steps along `0`,
then `x₁` along `1`, `x₂` along `2`, `x₃` along `3`.

DERIVED: `0`, `1`, `2`, `3` the four axes in order. -/
def P (U : IConf G) (x : ISite) : G :=
  lineZ U 0 0 (x 0) * lineZ U 1 (pt 0 0 (x 0)) (x 1)
    * lineZ U 2 (pt 1 (pt 0 0 (x 0)) (x 1)) (x 2)
    * lineZ U 3 (pt 2 (pt 1 (pt 0 0 (x 0)) (x 1)) (x 2)) (x 3)

/-- The axis-ordered path ends at `x`.

DERIVED: `0`, `1`, `2`, `3` the axes. -/
theorem pt_corner (x : ISite) : pt 3 (pt 2 (pt 1 (pt 0 0 (x 0)) (x 1)) (x 2)) (x 3) = x := by
  funext i
  fin_cases i <;> simp [pt]

/-- **The path transporter is gauge covariant**: `P(gU)(x) = g(0) P(U)(x) g(x)⁻¹`.

DERIVED: `0` the origin; `1`, `2`, `3` the axes. -/
theorem P_gauge (g : ISite → G) (U : IConf G) (x : ISite) :
    P (igaugeTransform g U) x = g 0 * P U x * (g x)⁻¹ := by
  unfold P
  rw [lineZ_gauge, lineZ_gauge, lineZ_gauge, lineZ_gauge, pt_corner]
  group

/-! ### Reflection -/

/-- DERIVED: `0` the reflection constant. -/
theorem reflSite_apply (τ : Fin 4) (x : ISite) (i : Fin 4) :
    ireflSite τ 0 x i = if i = τ then -x i else x i := by
  by_cases h : i = τ
  · subst h; simp [ireflSite]
  · simp [ireflSite, h]

/-- **The reflection moves a moved site**: `R(y + n μ̂) = R y ± n μ̂`, the sign `−` on the reflected
axis.

DERIVED: `0` the reflection constant. -/
theorem refl_pt (τ μ : Fin 4) (y : ISite) (n : ℤ) :
    ireflSite τ 0 (pt μ y n) = pt μ (ireflSite τ 0 y) (if μ = τ then -n else n) := by
  funext i
  simp only [ireflSite, pt, Function.update_apply]
  by_cases h1 : i = τ <;> by_cases h2 : i = μ <;> by_cases h3 : μ = τ <;> simp_all
  all_goals ring

/-- A `τ`-link of the reflected configuration reads the reflected `τ`-link one step back.

DERIVED: `0` the reflection constant; `1` the `τ`-link offset. -/
theorem refl_pt_tau (τ : Fin 4) (y : ISite) (m : ℤ) :
    ireflSite τ (-1) (pt τ y m) = pt τ (ireflSite τ 0 y) (-m - 1) := by
  funext i
  simp only [ireflSite, pt, Function.update_apply]
  by_cases h1 : i = τ <;> simp_all
  all_goals ring

/-- DERIVED: `0` the reflection constant. -/
theorem conf_refl_ne {τ μ : Fin 4} (h : μ ≠ τ) (U : IConf G) (z : ISite) :
    ireflConf τ 0 U (μ, z) = U (μ, ireflSite τ 0 z) := by
  simp [ireflConf, ireflLink, h]

/-- DERIVED: `0` the reflection constant; `1` the `τ`-link offset. -/
theorem conf_refl_eq (τ : Fin 4) (U : IConf G) (z : ISite) :
    ireflConf τ 0 U (τ, z) = (U (τ, ireflSite τ (-1) z))⁻¹ := by
  simp [ireflConf, ireflLink]

/-- DERIVED: `0` the reflection constant; `1` one step. -/
theorem lineF_refl_ne {τ μ : Fin 4} (h : μ ≠ τ) (U : IConf G) (y : ISite) (n : ℕ) :
    lineF (ireflConf τ 0 U) μ y n = lineF U μ (ireflSite τ 0 y) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lineF]
    rw [ih, conf_refl_ne h, refl_pt, if_neg h]

/-- DERIVED: `0` the reflection constant; `1` one step. -/
theorem lineB_refl_ne {τ μ : Fin 4} (h : μ ≠ τ) (U : IConf G) (y : ISite) (n : ℕ) :
    lineB (ireflConf τ 0 U) μ y n = lineB U μ (ireflSite τ 0 y) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lineB]
    rw [ih, conf_refl_ne h, refl_pt, if_neg h]

/-- **The reflected forward line along `τ` is the backward line.**

DERIVED: `0` the reflection constant; `1` one step. -/
theorem lineF_refl_eq (τ : Fin 4) (U : IConf G) (y : ISite) (n : ℕ) :
    lineF (ireflConf τ 0 U) τ y n = lineB U τ (ireflSite τ 0 y) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lineF, lineB]
    rw [ih, conf_refl_eq, refl_pt_tau]

/-- **The reflected backward line along `τ` is the forward line.**

DERIVED: `0` the reflection constant; `1` one step. -/
theorem lineB_refl_eq (τ : Fin 4) (U : IConf G) (y : ISite) (n : ℕ) :
    lineB (ireflConf τ 0 U) τ y n = lineF U τ (ireflSite τ 0 y) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lineF, lineB]
    have e : -(-(n : ℤ) - 1) - 1 = (n : ℤ) := by ring
    rw [ih, conf_refl_eq, refl_pt_tau, e, inv_inv]

/-- DERIVED: `0` the empty line; `1` the shift of `Int.negSucc`. -/
theorem lineZ_neg_nat (U : IConf G) (μ : Fin 4) (y : ISite) (m : ℕ) :
    lineZ U μ y (-(m : ℤ)) = lineB U μ y m := by
  cases m with
  | zero => rfl
  | succ m =>
    have e : -(((m + 1 : ℕ)) : ℤ) = Int.negSucc m := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [e]
    rfl

/-- **The reflected line**: the line of the reflected configuration from `y` is the line from `R y`,
with the step count negated on the reflected axis.

DERIVED: `0` the reflection constant; `1` the shift of `Int.negSucc`. -/
theorem lineZ_refl (τ μ : Fin 4) (U : IConf G) (y : ISite) (n : ℤ) :
    lineZ (ireflConf τ 0 U) μ y n = lineZ U μ (ireflSite τ 0 y) (if μ = τ then -n else n) := by
  by_cases h : μ = τ
  · rw [h, if_pos rfl]
    cases n with
    | ofNat m =>
      show lineF (ireflConf τ 0 U) τ y m = _
      rw [lineF_refl_eq]
      exact (lineZ_neg_nat U τ _ m).symm
    | negSucc m =>
      show lineB (ireflConf τ 0 U) τ y (m + 1) = _
      have e : -(Int.negSucc m) = ((m + 1 : ℕ) : ℤ) := by
        rw [Int.negSucc_eq]; push_cast; ring
      rw [lineB_refl_eq, e]
      rfl
  · rw [if_neg h]
    cases n with
    | ofNat m => exact lineF_refl_ne h U y m
    | negSucc m => exact lineB_refl_ne h U y (m + 1)

/-- DERIVED: `0` the origin and the reflection constant. -/
theorem refl_origin (τ : Fin 4) : ireflSite τ 0 (0 : ISite) = 0 := by
  funext i
  simp [ireflSite, Function.update_apply]

/-- **The path transporter of the reflected configuration** is the path transporter at the reflected
site.

DERIVED: `0` the reflection constant. -/
theorem P_refl (τ : Fin 4) (U : IConf G) (x : ISite) :
    P (ireflConf τ 0 U) x = P U (ireflSite τ 0 x) := by
  unfold P
  simp only [lineZ_refl, refl_pt, refl_origin, ← reflSite_apply]

/-! ### Continuity and locality -/

section Cont

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- DERIVED: `0` the base case. -/
theorem continuous_lineF (μ : Fin 4) (y : ISite) (n : ℕ) :
    Continuous (fun U : IConf G => lineF U μ y n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.mul (continuous_apply _)

/-- DERIVED: `0` the base case. -/
theorem continuous_lineB (μ : Fin 4) (y : ISite) (n : ℕ) :
    Continuous (fun U : IConf G => lineB U μ y n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.mul (continuous_apply _).inv

/-- DERIVED: `1` the shift of `Int.negSucc`. -/
theorem continuous_lineZ (μ : Fin 4) (y : ISite) (n : ℤ) :
    Continuous (fun U : IConf G => lineZ U μ y n) := by
  cases n with
  | ofNat m => exact continuous_lineF μ y m
  | negSucc m => exact continuous_lineB μ y (m + 1)

/-- DERIVED: no numeral. -/
theorem continuous_P (x : ISite) : Continuous (fun U : IConf G => P U x) := by
  unfold P
  exact (((continuous_lineZ _ _ _).mul (continuous_lineZ _ _ _)).mul
    (continuous_lineZ _ _ _)).mul (continuous_lineZ _ _ _)

end Cont

/-- **The box** `[-L, L]⁴`.

DERIVED: `4` the dimension. -/
def inBox (L : ℕ) (x : ISite) : Prop := ∀ i, |x i| ≤ (L : ℤ)

instance (L : ℕ) : DecidablePred (inBox L) := fun x => by
  unfold inBox; infer_instance

/-- DERIVED: `0` the reflection constant. -/
theorem inBox_refl (L : ℕ) (τ : Fin 4) (x : ISite) : inBox L (ireflSite τ 0 x) ↔ inBox L x := by
  have one : ∀ y : ISite, inBox L y → inBox L (ireflSite τ 0 y) := by
    intro y hy i
    rw [reflSite_apply]
    split_ifs
    · rw [abs_neg]; exact hy i
    · exact hy i
  refine ⟨fun h => ?_, one x⟩
  have := one _ h
  rwa [ireflSite_involutive τ 0 x] at this

/-- DERIVED: `0` the reflection constant; `1` the `τ`-link offset. -/
theorem refl_ishift_tau (τ : Fin 4) (x : ISite) : ireflSite τ 0 (ishift τ x) = ireflSite τ (-1) x := by
  funext i
  simp only [ireflSite, ishift, Function.update_apply]
  by_cases h : i = τ <;> simp_all
  all_goals ring

/-- DERIVED: `0` the reflection constant; `1` the `τ`-link offset. -/
theorem ishift_refl_m1 (τ : Fin 4) (x : ISite) : ishift τ (ireflSite τ (-1) x) = ireflSite τ 0 x := by
  funext i
  simp only [ireflSite, ishift, Function.update_apply]
  by_cases h : i = τ <;> simp_all
  all_goals ring

/-- DERIVED: `0` the reflection constant. -/
theorem refl_ishift_ne' {τ μ : Fin 4} (h : μ ≠ τ) (x : ISite) :
    ireflSite τ 0 (ishift μ x) = ishift μ (ireflSite τ 0 x) := by
  funext i
  simp only [ireflSite, ishift, Function.update_apply]
  by_cases h1 : i = τ <;> by_cases h2 : i = μ <;> simp_all

/-- DERIVED: `0` the empty line. -/
theorem lineF_congr {U U' : IConf G} (μ : Fin 4) (y : ISite) (n : ℕ)
    (h : ∀ j : ℕ, j < n → U (μ, pt μ y j) = U' (μ, pt μ y j)) : lineF U μ y n = lineF U' μ y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lineF]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

/-- DERIVED: `0` the empty line; `1` one step. -/
theorem lineB_congr {U U' : IConf G} (μ : Fin 4) (y : ISite) (n : ℕ)
    (h : ∀ j : ℕ, j < n → U (μ, pt μ y (-(j : ℤ) - 1)) = U' (μ, pt μ y (-(j : ℤ) - 1))) :
    lineB U μ y n = lineB U' μ y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lineB]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

/-- A move along an axis on which the site sits at `0` stays in the box when its length does.

DERIVED: `0` the coordinate. -/
theorem inBox_pt {L : ℕ} {μ : Fin 4} {y : ISite} (hy : inBox L y) (hy0 : y μ = 0) {m : ℤ}
    (hm : |m| ≤ (L : ℤ)) : inBox L (pt μ y m) := by
  intro i
  by_cases h : i = μ
  · subst h; simp [pt, hy0, hm]
  · simp only [pt, Function.update_of_ne h]; exact hy i

/-- **The line from a box site at `0` on its axis reads only box links.**

DERIVED: `0` the coordinate; `1` the shift of `Int.negSucc`. -/
theorem lineZ_congr {U U' : IConf G} {L : ℕ} (hUU : ∀ ν z, inBox L z → U (ν, z) = U' (ν, z))
    {μ : Fin 4} {y : ISite} (hy : inBox L y) (hy0 : y μ = 0) {n : ℤ} (hn : |n| ≤ (L : ℤ)) :
    lineZ U μ y n = lineZ U' μ y n := by
  cases n with
  | ofNat m =>
    refine lineF_congr μ y m (fun j hj => hUU _ _ (inBox_pt hy hy0 ?_))
    have : |((m : ℕ) : ℤ)| ≤ (L : ℤ) := hn
    rw [abs_le] at this ⊢
    constructor <;> omega
  | negSucc m =>
    refine lineB_congr μ y (m + 1) (fun j hj => hUU _ _ (inBox_pt hy hy0 ?_))
    rw [Int.negSucc_eq, abs_le] at hn
    rw [abs_le]
    constructor <;> omega

/-- **The path transporter to a box site reads only box links.**

DERIVED: `0`, `1`, `2`, `3` the axes; `0` the origin. -/
theorem P_congr {U U' : IConf G} {L : ℕ} (hUU : ∀ ν z, inBox L z → U (ν, z) = U' (ν, z))
    {x : ISite} (hx : inBox L x) : P U x = P U' x := by
  have h0 : inBox L (0 : ISite) := fun i => by simp
  have h1 : inBox L (pt 0 0 (x 0)) := inBox_pt h0 rfl (hx 0)
  have h2 : inBox L (pt 1 (pt 0 0 (x 0)) (x 1)) := inBox_pt h1 (by simp [pt]) (hx 1)
  have h3 : inBox L (pt 2 (pt 1 (pt 0 0 (x 0)) (x 1)) (x 2)) := inBox_pt h2 (by simp [pt]) (hx 2)
  unfold P
  rw [lineZ_congr hUU h0 rfl (hx 0), lineZ_congr hUU h1 (by simp [pt]) (hx 1),
    lineZ_congr hUU h2 (by simp [pt]) (hx 2), lineZ_congr hUU h3 (by simp [pt]) (hx 3)]

/-! ### The flat flow -/

/-- **The flat configuration map**: inside the box `[-L, L]⁴` every link `(μ, x)` becomes
`P(x)⁻¹ P(x + μ̂)`; outside, the link is kept.

DERIVED: no numeral. -/
def flatV (L : ℕ) (U : IConf G) : IConf G := fun l =>
  if inBox L l.2 ∧ inBox L (ishift l.1 l.2) then (P U l.2)⁻¹ * P U (ishift l.1 l.2) else U l

/-- **The flat map is gauge covariant.**

DERIVED: no numeral. -/
theorem flatV_gauge (L : ℕ) (g : ISite → G) (U : IConf G) :
    flatV L (igaugeTransform g U) = igaugeTransform g (flatV L U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  show (if inBox L x ∧ inBox L (ishift μ x) then
      (P (igaugeTransform g U) x)⁻¹ * P (igaugeTransform g U) (ishift μ x)
      else igaugeTransform g U (μ, x))
    = g x * (if inBox L x ∧ inBox L (ishift μ x) then (P U x)⁻¹ * P U (ishift μ x)
      else U (μ, x)) * (g (ishift μ x))⁻¹
  split_ifs with hc
  · rw [P_gauge, P_gauge]; group
  · rfl

/-- **The flat map commutes with the reflections** `ireflConf τ 0`.

DERIVED: `0` the reflection constant. -/
theorem flatV_refl (L : ℕ) (τ : Fin 4) (U : IConf G) :
    flatV L (ireflConf τ 0 U) = ireflConf τ 0 (flatV L U) := by
  funext l
  obtain ⟨μ, x⟩ := l
  by_cases hμ : μ = τ
  · rw [hμ, conf_refl_eq]
    show (if inBox L x ∧ inBox L (ishift τ x) then
        (P (ireflConf τ 0 U) x)⁻¹ * P (ireflConf τ 0 U) (ishift τ x)
        else ireflConf τ 0 U (τ, x))
      = (if inBox L (ireflSite τ (-1) x) ∧ inBox L (ishift τ (ireflSite τ (-1) x)) then
          (P U (ireflSite τ (-1) x))⁻¹ * P U (ishift τ (ireflSite τ (-1) x))
          else U (τ, ireflSite τ (-1) x))⁻¹
    rw [ishift_refl_m1, P_refl, P_refl, refl_ishift_tau, conf_refl_eq]
    have c1 : inBox L (ireflSite τ (-1) x) ↔ inBox L (ishift τ x) := by
      rw [← refl_ishift_tau, inBox_refl]
    have c2 : inBox L (ireflSite τ 0 x) ↔ inBox L x := inBox_refl L τ x
    by_cases hc : inBox L x ∧ inBox L (ishift τ x)
    · rw [if_pos hc, if_pos ⟨c1.mpr hc.2, c2.mpr hc.1⟩, mul_inv_rev, inv_inv]
    · have hc' : ¬ (inBox L (ireflSite τ (-1) x) ∧ inBox L (ireflSite τ 0 x)) :=
        fun h => hc ⟨c2.mp h.2, c1.mp h.1⟩
      rw [if_neg hc, if_neg hc']
  · rw [conf_refl_ne hμ]
    show (if inBox L x ∧ inBox L (ishift μ x) then
        (P (ireflConf τ 0 U) x)⁻¹ * P (ireflConf τ 0 U) (ishift μ x)
        else ireflConf τ 0 U (μ, x))
      = (if inBox L (ireflSite τ 0 x) ∧ inBox L (ishift μ (ireflSite τ 0 x)) then
          (P U (ireflSite τ 0 x))⁻¹ * P U (ishift μ (ireflSite τ 0 x))
          else U (μ, ireflSite τ 0 x))
    rw [P_refl, P_refl, conf_refl_ne hμ, ← refl_ishift_ne' hμ]
    simp only [inBox_refl]

/-- **The flat map is continuous.**

DERIVED: no numeral. -/
theorem continuous_flatV [TopologicalSpace G] [IsTopologicalGroup G] (L : ℕ) :
    Continuous (flatV (G := G) L) := by
  refine continuous_pi (fun l => ?_)
  by_cases hc : inBox L l.2 ∧ inBox L (ishift l.1 l.2)
  · simp only [flatV, hc, and_self, if_true]
    exact (continuous_P _).inv.mul (continuous_P _)
  · simp only [flatV, hc, if_false]
    exact continuous_apply l

/-- **The flat map reads only the links based in the box**, so its range is `2L`.

DERIVED: `2` the two half-widths. -/
theorem flatV_local (L : ℕ) (l : ILink) : ∃ T : Finset ILink,
    (∀ l' ∈ T, ∀ i, |l'.2 i - l.2 i| ≤ ((2 * L : ℕ) : ℤ)) ∧
      ∀ U U' : IConf G, (∀ l' ∈ T, U l' = U' l') → flatV L U l = flatV L U' l := by
  by_cases hc : inBox L l.2 ∧ inBox L (ishift l.1 l.2)
  · refine ⟨Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(L : ℤ)) (L : ℤ)),
      fun l' hl' i => ?_, fun U U' h => ?_⟩
    · rw [Finset.mem_product, Fintype.mem_piFinset] at hl'
      have a1 := Finset.mem_Icc.mp (hl'.2 i)
      have a2 := abs_le.mp (hc.1 i)
      rw [abs_le]
      push_cast
      constructor <;> omega
    · have hUU : ∀ ν z, inBox L z → U (ν, z) = U' (ν, z) := fun ν z hz =>
        h (ν, z) (Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Fintype.mem_piFinset.mpr (fun i => Finset.mem_Icc.mpr (abs_le.mp (hz i)))⟩)
      simp only [flatV, hc, and_self, if_true]
      rw [P_congr hUU hc.1, P_congr hUU hc.2]
  · refine ⟨{l}, fun l' hl' i => ?_, fun U U' h => ?_⟩
    · rw [Finset.mem_singleton.mp hl', sub_self, abs_zero]
      positivity
    · simp only [flatV, hc, if_false]
      exact h l (Finset.mem_singleton_self l)

/-- **Inside the box the flat configuration is a gauge transform of the identity configuration.**

DERIVED: `1` the identity configuration. -/
theorem flatV_eq_gauge_one (L : ℕ) (U : IConf G) (l : ILink)
    (hl : inBox L l.2 ∧ inBox L (ishift l.1 l.2)) :
    flatV L U l = igaugeTransform (fun x => (P U x)⁻¹) (1 : IConf G) l := by
  obtain ⟨μ, x⟩ := l
  simp only [flatV, hl, and_self, if_true]
  rw [igauge_apply]
  simp

end Path

/-! ## 2. The flat flow as a `ConfFlow`, and `hU` -/

section Flat

open MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumFlow
  MassGap.ObserverSymField MassGap.ObserverOSSchwartz MassGap.ObserverOSEuclidS
  MassGap.ObserverEnergyBox MassGap.ObserverMoments

variable {N : ℕ}

/-- **The flat flow**: at step `k`, `flatV (L k)`; range `2 L_k`.

DERIVED: `2` the two half-widths. -/
def flatFlow (L : ℕ → ℕ) : ConfFlow N where
  V k := flatV (L k)
  continuous_V k := continuous_flatV (L k)
  gauge k g U := flatV_gauge (L k) g U
  refl k τ U := flatV_refl (L k) τ U
  range k := 2 * L k
  local_V k l := flatV_local (L k) l

/-- **Every local gauge-invariant field reads a constant through the flat flow** once its support is
in the box: if `L_k → ∞`, eventually `O(V_k U) = O(1)` for every `U`.

DERIVED: `1` the identity configuration. -/
theorem flatFlow_fieldMap {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (O : LField (MassGap.SUN.SU N)) :
    ∀ᶠ k in atTop, ∀ U : Cfg N, ((flatFlow (N := N) L).fieldMap k O).1 U = O.1 1 := by
  obtain ⟨S, hS⟩ := O.2.1
  have hev : ∀ᶠ k in atTop, ∀ l ∈ S, inBox (L k) l.2 ∧ inBox (L k) (ishift l.1 l.2) := by
    rw [Filter.eventually_all_finset]
    intro l _
    have h1 : ∀ i : Fin 4, ∀ᶠ k in atTop,
        |l.2 i| ≤ (L k : ℤ) ∧ |ishift l.1 l.2 i| ≤ (L k : ℤ) := fun i => by
      filter_upwards [hL.eventually_ge_atTop ((l.2 i).natAbs + (ishift l.1 l.2 i).natAbs)]
        with k hk
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      constructor <;> omega
    filter_upwards [Filter.eventually_all.2 h1] with k hk
    exact ⟨fun i => (hk i).1, fun i => (hk i).2⟩
  filter_upwards [hev] with k hk U
  show O.1 (flatV (L k) U) = O.1 1
  rw [hS (flatV (L k) U) (igaugeTransform (fun x => (P U x)⁻¹) (1 : Cfg N))
    (fun l hl => flatV_eq_gauge_one (L k) U l (hk l hl))]
  exact O.2.2 _ _

/-- **The symmetrised plaquette density vanishes at the identity configuration.**

DERIVED: `0` the excluded colour count and the value; `1` the identity configuration. -/
theorem symPlaq_one (hN : N ≠ 0) : ∀ O ∈ SymPlaqClass N, O.1 (1 : Cfg N) = 0 := by
  rintro O ⟨q, rfl⟩
  rw [sym_apply]
  refine Finset.sum_eq_zero (fun g _ => ?_)
  have hax : ContinuumHypercubic.iaxisConf g.1 (1 : Cfg N) = 1 := rfl
  have hr : ∀ (b : Bool) (τ : Fin 4), rpow b τ (1 : Cfg N) = 1 := by
    intro b τ
    cases b
    · rfl
    · funext l
      simp [rpow, ireflConf]
  have hrefl : reflAll g.2 (1 : Cfg N) = 1 := by
    simp only [reflAll, hr]
  rw [hax, hrefl]
  show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) q 1) = 0
  have hhol : MassGap.GibbsSpec.ihol (G := MassGap.SUN.SU N) q 1 = 1 := by
    simp [MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol]
  rw [hhol, MassGap.WilsonAction.wilsonDensity_one hN]

/-- **Reason (h), per field: a pointwise bound at the cell volume gives `hU`.** If every field of a
non-negative class has, eventually, `|O ∘ V_k| ≤ K a_k⁴` pointwise (one `K` for the class), then
`ClassMoments hN W D 1 (e^{625 K})` (`ObserverMoments.classUnitExp_of_density` and
`classMoments_of_classUnitExp` on the singleton class).

DERIVED: `1` the strength; `2 * 1 + 3`, `4` the site count of the unit cube. -/
theorem classMoments_of_densityEach (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))} (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {K : ℝ}
    (h : ∀ O ∈ D, DensityVolumeBound W {O} K) :
    ClassMoments hN W D 1 (Real.exp (K * (2 * 1 + 3) ^ 4)) := by
  intro O hO
  have h1 := classMoments_of_classUnitExp hN W (D := {O})
    (fun O' hO' => by rw [Set.mem_singleton_iff.mp hO']; exact hpos O hO) one_pos
    (classUnitExp_of_density hN W (h O hO))
  have h2 := h1 O (Set.mem_singleton O)
  rwa [abs_of_pos (Real.exp_pos _)] at h2

/-- **The flat flow meets the per-field cell-volume bound at `K = 0`** on `SymPlaqClass N`.

DERIVED: `0` the bound. -/
theorem densityEach_flatFlow (hN : N ≠ 0) {L : ℕ → ℕ} (hL : Tendsto L atTop atTop) :
    ∀ O ∈ SymPlaqClass N, DensityVolumeBound (flatFlow (N := N) L) {O} 0 := by
  intro O hO
  filter_upwards [flatFlow_fieldMap hL O] with k hk O' hO' U
  rw [Set.mem_singleton_iff.mp hO', hk U, symPlaq_one hN O hO]
  simp

/-- **`hU` at the flat flow**: `ClassMoments hN (flatFlow L) (SymPlaqClass N) 1 1` when `L_k → ∞`.

DERIVED: `1` the strength and the constant. -/
theorem classMoments_flatFlow (hN : N ≠ 0) {L : ℕ → ℕ} (hL : Tendsto L atTop atTop) :
    ClassMoments hN (flatFlow (N := N) L) (SymPlaqClass N) 1 1 := by
  have h := classMoments_of_densityEach hN (flatFlow (N := N) L) (symPlaq_nonneg hN)
    (densityEach_flatFlow hN hL)
  rwa [zero_mul, Real.exp_zero] at h

/-- The box half-width `⌊1/√a_k⌋`.

DERIVED: `1` the unit of length. -/
def flatL (N : ℕ) (k : ℕ) : ℕ := ⌊1 / Real.sqrt (dySpacing N k)⌋₊

/-- **`⌊1/√a_k⌋ → ∞`.**

DERIVED: `0` the limit of the spacing; `1` the unit. -/
theorem tendsto_flatL (hN : N ≠ 0) : Tendsto (flatL N) atTop atTop := by
  have hs : Tendsto (fun k => Real.sqrt (dySpacing N k)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall (fun k => Set.mem_Ioi.mpr (Real.sqrt_pos.mpr
      (dySpacing_pos (one_le_of_ne_zero hN) k)))⟩
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_dySpacing N)
    simpa [Function.comp_def] using this
  have hi : Tendsto (fun k => 1 / Real.sqrt (dySpacing N k)) atTop atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hs
  exact tendsto_nat_floor_atTop.comp hi

/-- **The flat flow at `L_k = ⌊1/√a_k⌋` has vanishing physical reach**: `a_k · 2L_k ≤ 2√a_k → 0`.

DERIVED: `0` the limit; `2` the two half-widths. -/
theorem flat_reach (hN : N ≠ 0) :
    Tendsto (fun k => dySpacing N k * ((flatFlow (N := N) (flatL N)).range k : ℝ)) atTop (𝓝 0) := by
  have hup : ∀ k, dySpacing N k * ((flatFlow (N := N) (flatL N)).range k : ℝ)
      ≤ 2 * Real.sqrt (dySpacing N k) := by
    intro k
    have ha := dySpacing_pos (one_le_of_ne_zero hN) k
    have hsq := Real.sqrt_pos.mpr ha
    have hfl : ((flatL N k : ℕ) : ℝ) ≤ 1 / Real.sqrt (dySpacing N k) :=
      Nat.floor_le (by positivity)
    show dySpacing N k * (((2 * flatL N k : ℕ)) : ℝ) ≤ _
    push_cast
    have e : dySpacing N k * (1 / Real.sqrt (dySpacing N k)) = Real.sqrt (dySpacing N k) := by
      rw [mul_one_div, Real.div_sqrt]
    nlinarith [mul_le_mul_of_nonneg_left hfl ha.le]
  have h0 : ∀ k, 0 ≤ dySpacing N k * ((flatFlow (N := N) (flatL N)).range k : ℝ) := fun k =>
    mul_nonneg (dySpacing_pos (one_le_of_ne_zero hN) k).le (Nat.cast_nonneg _)
  have hlim : Tendsto (fun k => 2 * Real.sqrt (dySpacing N k)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp (tendsto_dySpacing N)).const_mul 2
    simpa using this
  exact squeeze_zero h0 hup hlim

/-- **The degenerate discharge**: the flat flow at `L_k = ⌊1/√a_k⌋` meets `hU` of
`ClaySUFinal.clayStatementAt_SU_final` (at `t = 1`, `C = 1`), vanishing reach, and the physical
range of `energy0` at every `r > 0`. Its flowed fields are eventually constant
(`flatFlow_fieldMap`); the inputs of the capstone that read the same `W` non-trivially are not
addressed.

DERIVED: `1` the strength and the constant; `0` the limit and the sign of `r`. -/
theorem flat_hU_hphys_hreach (hN : N ≠ 0) :
    ClassMoments hN (flatFlow (N := N) (flatL N)) (SymPlaqClass N) 1 1
      ∧ Tendsto (fun k => dySpacing N k * ((flatFlow (N := N) (flatL N)).range k : ℝ)) atTop (𝓝 0)
      ∧ ∀ r : ℝ, 0 < r →
        (ObserverOS.energy0 (flatFlow (N := N) (flatL N)) (SymPlaqClass N)
          (symPlaq_refl N)).PhysRange r :=
  ⟨classMoments_flatFlow hN (tendsto_flatL hN), flat_reach hN,
    fun _ hr => (flat_reach hN).eventually (eventually_le_nhds hr)⟩

end Flat

/-! ## 3. Reason (i): the small-field / large-field split -/

section Split

open MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumFlow
  MassGap.ObserverSymField MassGap.ObserverOSEuclidS MassGap.ObserverEnergyBox

variable {N : ℕ}

/-- **The large-field part is bounded by the large-field probability**: for `χ ≤ 1`, `c ≥ 0` and
`F ≤ M`, `ν((1 − χ) e^{cF}) ≤ e^{cM} ν(1 − χ)`.

DERIVED: `1` the cut-off's upper value; `0` the sign of `c`. -/
theorem largeField_le (ν : MassGap.DLRLimit.State (Cfg N)) (χ F : C(Cfg N, ℝ))
    (hχ : ∀ U, χ U ≤ 1) {c M : ℝ} (hc : 0 ≤ c) (hF : ∀ U, F U ≤ M) :
    ν ((1 - χ) * expC (c • F)) ≤ Real.exp (c * M) * ν (1 - χ) := by
  rw [← ν.map_smul]
  refine ν.mono (fun U => ?_)
  simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply, expC_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  have h1 : 0 ≤ 1 - χ U := by linarith [hχ U]
  have h2 : Real.exp (c * F U) ≤ Real.exp (c * M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hF U) hc)
  nlinarith [mul_le_mul_of_nonneg_left h2 h1]

/-- **Reason (i), formal**: eventually, for every field of `D`, a continuous cut-off `0 ≤ χ ≤ 1` with
a bounded small-field exponential moment `ν_k(χ e^{s a_k⁻⁴ O∘V_k}) ≤ C₁` and a large-field
probability `ν_k(1 − χ) ≤ C₂ e^{−s M / a_k⁴}`.

DERIVED: `0`, `1` the cut-off's range; `4` the canonical dimension. -/
def SmallLargeSplit (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (s M C₁ C₂ : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ O ∈ D, ∃ χ : C(Cfg N, ℝ), (∀ U, 0 ≤ χ U ∧ χ U ≤ 1)
    ∧ stateK hN k (χ * expC ((s / dySpacing N k ^ 4) • (W.fieldMap k O).1)) ≤ C₁
    ∧ stateK hN k (1 - χ) ≤ C₂ * Real.exp (-((s / dySpacing N k ^ 4) * M))

/-- **`SiteExp` from the split**: on a class bounded by `M`, `SmallLargeSplit` at `s ≥ 0` gives
`SiteExp hN W D s (C₁ + C₂)`.

DERIVED: `1` the partition `χ + (1 − χ)`; `4` the canonical dimension. -/
theorem siteExp_of_split (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    {s M C₁ C₂ : ℝ} (hs : 0 ≤ s) (hM : ∀ O ∈ D, ∀ U, O.1 U ≤ M)
    (h : SmallLargeSplit hN W D s M C₁ C₂) : FlowUV.SiteExp hN W D s (C₁ + C₂) := by
  unfold SmallLargeSplit at h
  unfold FlowUV.SiteExp
  filter_upwards [h] with k hk O hO
  obtain ⟨χ, hχ, h1, h2⟩ := hk O hO
  have ha4 : 0 < dySpacing N k ^ 4 := pow_pos (dySpacing_pos (one_le_of_ne_zero hN) k) 4
  set c : ℝ := s / dySpacing N k ^ 4 with hc
  have hc0 : 0 ≤ c := div_nonneg hs ha4.le
  set E : C(Cfg N, ℝ) := expC (c • (W.fieldMap k O).1) with hE
  have hsplit : E = χ * E + (1 - χ) * E := by ring
  have hL := largeField_le (stateK hN k) χ (W.fieldMap k O).1 (fun U => (hχ U).2) hc0
    (fun U => hM O hO (W.V k U))
  have hexp : Real.exp (c * M) * (C₂ * Real.exp (-(c * M))) = C₂ := by
    rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have h3 : Real.exp (c * M) * stateK hN k (1 - χ) ≤ C₂ := by
    calc Real.exp (c * M) * stateK hN k (1 - χ)
        ≤ Real.exp (c * M) * (C₂ * Real.exp (-(c * M))) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = C₂ := hexp
  calc stateK hN k E = stateK hN k (χ * E) + stateK hN k ((1 - χ) * E) := by
        rw [← (stateK hN k).map_add, ← hsplit]
    _ ≤ C₁ + C₂ := add_le_add h1 (hL.trans h3)

/-- **`hU` from the split** at strength `625 t` (`ClaySUFinal.classMoments_of_siteExp`).

DERIVED: `2 * 1 + 3`, `4` the site count; `0` the sign of `t`. -/
theorem classMoments_of_split (hN : N ≠ 0) (W : ConfFlow N) {t M C₁ C₂ : ℝ} (ht : 0 < t)
    (hM : ∀ O ∈ SymPlaqClass N, ∀ U, O.1 U ≤ M)
    (h : SmallLargeSplit hN W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) M C₁ C₂) :
    ClassMoments hN W (SymPlaqClass N) t |C₁ + C₂| :=
  ClaySUFinal.classMoments_of_siteExp hN W ht
    (siteExp_of_split hN W (mul_pos ht (by norm_num)).le hM h)

end Split

/-! ## 4. Reason (j): a summable change per zoom step -/

section Zoom

open MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumFlow
  MassGap.ObserverSymField MassGap.ObserverOSEuclidS MassGap.ObserverEnergyBox

variable {N : ℕ}

/-- **A relative change per step bounds the sequence**: `x_{k+1} ≤ (1 + ε_k) x_k` for `k ≥ K` and
`x ≥ 0` give `x_{K+n} ≤ x_K e^{Σ_{j<n} ε_{K+j}}`.

DERIVED: `1` the relative factor; `0` the base case. -/
theorem seq_le_exp_sum (x ε : ℕ → ℝ) (K : ℕ) (hx : ∀ k, 0 ≤ x k)
    (h : ∀ k, K ≤ k → x (k + 1) ≤ (1 + ε k) * x k) (n : ℕ) :
    x (K + n) ≤ x K * Real.exp (∑ j ∈ Finset.range n, ε (K + j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x (K + n + 1) ≤ (1 + ε (K + n)) * x (K + n) := h (K + n) (by omega)
    have h2 : (1 + ε (K + n)) * x (K + n) ≤ Real.exp (ε (K + n)) * x (K + n) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (ε (K + n))]) (hx _)
    have h3 : Real.exp (ε (K + n)) * x (K + n)
        ≤ Real.exp (ε (K + n)) * (x K * Real.exp (∑ j ∈ Finset.range n, ε (K + j))) :=
      mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
    rw [Finset.sum_range_succ, Real.exp_add]
    calc x (K + (n + 1)) = x (K + n + 1) := rfl
      _ ≤ _ := h1.trans (h2.trans h3)
      _ = _ := by ring

/-- **The one-site exponential moment in physical units**, `ν_k(e^{s a_k⁻⁴ O∘V_k})`.

DERIVED: `4` the canonical dimension. -/
def physExp (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) (s : ℝ) (k : ℕ) : ℝ :=
  stateK hN k (expC ((s / dySpacing N k ^ 4) • (W.fieldMap k O).1))

/-- DERIVED: `0` the sign. -/
theorem physExp_nonneg (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) (s : ℝ)
    (k : ℕ) : 0 ≤ physExp hN W O s k := by
  have := (stateK hN k).mono (f := (0 : C(Cfg N, ℝ)))
    (g := expC ((s / dySpacing N k ^ 4) • (W.fieldMap k O).1)) (fun U => (Real.exp_pos _).le)
  rwa [(stateK hN k).map_zero] at this

/-- **Reason (j), formal**: from step `K` on, every field's one-site exponential moment in physical
units changes by at most the relative amount `ε_k` per zoom step.

DERIVED: `1` the relative factor and the next step. -/
def ZoomStable (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N))) (s : ℝ)
    (ε : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ k, K ≤ k → ∀ O ∈ D, physExp hN W O s (k + 1) ≤ (1 + ε k) * physExp hN W O s k

/-- **`SiteExp` from a summable change per step**: `ZoomStable` with `ε ≥ 0` summable and a bound
`X₀` at step `K` give `SiteExp hN W D s (X₀ e^{Σ ε})`.

DERIVED: `0` the sign of `ε`. -/
theorem siteExp_of_zoomStable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    {s : ℝ} {ε : ℕ → ℝ} {K : ℕ} (hε : ∀ k, 0 ≤ ε k) (hsum : Summable ε)
    (h : ZoomStable hN W D s ε K) {X₀ : ℝ} (h0 : ∀ O ∈ D, physExp hN W O s K ≤ X₀) :
    FlowUV.SiteExp hN W D s (X₀ * Real.exp (∑' j, ε j)) := by
  unfold FlowUV.SiteExp
  filter_upwards [eventually_ge_atTop K] with k hk O hO
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hX : 0 ≤ X₀ := (physExp_nonneg hN W O s K).trans (h0 O hO)
  have hseq := seq_le_exp_sum (fun k => physExp hN W O s k) ε K
    (fun k => physExp_nonneg hN W O s k) (fun k hk => h k hk O hO) n
  have hS : ∑ j ∈ Finset.range n, ε (K + j) ≤ ∑' j, ε j := by
    calc ∑ j ∈ Finset.range n, ε (K + j)
        ≤ ∑ j ∈ Finset.range K, ε j + ∑ j ∈ Finset.range n, ε (K + j) :=
          le_add_of_nonneg_left (Finset.sum_nonneg (fun j _ => hε j))
      _ = ∑ j ∈ Finset.range (K + n), ε j := (Finset.sum_range_add ε K n).symm
      _ ≤ ∑' j, ε j := hsum.sum_le_tsum _ (fun j _ => hε j)
  show physExp hN W O s (K + n) ≤ _
  calc physExp hN W O s (K + n)
      ≤ physExp hN W O s K * Real.exp (∑ j ∈ Finset.range n, ε (K + j)) := hseq
    _ ≤ X₀ * Real.exp (∑' j, ε j) :=
        mul_le_mul (h0 O hO) (Real.exp_le_exp.mpr hS) (Real.exp_pos _).le hX

/-- **`hU` from a summable change per step**, at strength `625 t`.

DERIVED: `2 * 1 + 3`, `4` the site count; `0` the signs. -/
theorem classMoments_of_zoomStable (hN : N ≠ 0) (W : ConfFlow N) {t : ℝ} (ht : 0 < t)
    {ε : ℕ → ℝ} {K : ℕ} (hε : ∀ k, 0 ≤ ε k) (hsum : Summable ε)
    (h : ZoomStable hN W (SymPlaqClass N) (t * (2 * 1 + 3) ^ 4) ε K) {X₀ : ℝ}
    (h0 : ∀ O ∈ SymPlaqClass N, physExp hN W O (t * (2 * 1 + 3) ^ 4) K ≤ X₀) :
    ClassMoments hN W (SymPlaqClass N) t |X₀ * Real.exp (∑' j, ε j)| :=
  ClaySUFinal.classMoments_of_siteExp hN W ht (siteExp_of_zoomStable hN W hε hsum h h0)

end Zoom

/-! ## 5. A polynomial plaquette floor suffices for the identity-flow no-go -/

section Floor

open MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumFlow
  MassGap.ObserverSymField MassGap.ObserverOSEuclidS MassGap.ObserverEnergyMoments

variable {N : ℕ}

/-- **A polynomial floor beats every exponential**: for `λ > 0`, eventually in `β`,
`e^{−λβ} ≤ β^{−m}`.

DERIVED: `0` the limit; `1` the comparison. -/
theorem exp_le_inv_pow {lam : ℝ} (hlam : 0 < lam) (m : ℕ) :
    ∀ᶠ β : ℝ in atTop, Real.exp (-(lam * β)) ≤ 1 / β ^ m := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
    (tendsto_id.const_mul_atTop hlam)
  have hev := h.eventually (gt_mem_nhds (pow_pos hlam m))
  filter_upwards [hev, eventually_gt_atTop 0] with β hβ hβ0
  simp only [Function.comp_apply, id] at hβ
  rw [mul_pow] at hβ
  have hβm : 0 < β ^ m := pow_pos hβ0 m
  rw [le_div_iff₀ hβm]
  have hlm : 0 < lam ^ m := pow_pos hlam m
  have : lam ^ m * (β ^ m * Real.exp (-(lam * β))) < lam ^ m * 1 := by
    rw [mul_one]; linarith [mul_assoc (lam ^ m) (β ^ m) (Real.exp (-(lam * β)))]
  have := lt_of_mul_lt_mul_left this hlm.le
  linarith [mul_comm (Real.exp (-(lam * β))) (β ^ m)]

/-- **The identity flow fails `hU` under any polynomial plaquette floor**: if eventually
`c β_k^{−m} ≤ ν_k(1 − Re tr U_q / N)` with `c > 0`, then
`ClassMoments hN (ConfFlow.identity N) (SymPlaqClass N) t C` fails at every `t`, `C`
(`FlowMoments.not_classMoments_identity` at `λ = 48π²/(11N²)`).

DERIVED: `48 = 96/2` half the rate of `a⁴`; `11` is `aRun`'s; `0` the signs. -/
theorem not_classMoments_identity_poly (hN : N ≠ 0) (q : MassGap.GibbsSpec.IPlaq) {c : ℝ}
    (hc : 0 < c) (m : ℕ)
    (hfloor : ∀ᶠ k in atTop,
      c / dyBeta (one_le_of_ne_zero hN) k ^ m ≤ stateK hN k (plaqField (N := N) q).1)
    (t C : ℝ) : ¬ ClassMoments hN (ConfFlow.identity N) (SymPlaqClass N) t C := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hlam : (0 : ℝ) < 48 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) := by positivity
  have hlt : 48 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) < 96 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) := by
    apply div_lt_div_of_pos_right _ (by positivity)
    nlinarith [Real.pi_pos]
  refine FlowMoments.not_classMoments_identity hN q hc hlt ?_ t C
  filter_upwards [hfloor, (tendsto_dyBeta (one_le_of_ne_zero hN)).eventually (exp_le_inv_pow hlam m)]
    with k hk hk2
  calc c * Real.exp (-(48 * Real.pi ^ 2 / (11 * (N : ℝ) ^ 2) * dyBeta (one_le_of_ne_zero hN) k))
      ≤ c * (1 / dyBeta (one_le_of_ne_zero hN) k ^ m) := mul_le_mul_of_nonneg_left hk2 hc.le
    _ = c / dyBeta (one_le_of_ne_zero hN) k ^ m := by ring
    _ ≤ _ := hk

end Floor

#print axioms P_gauge
#print axioms P_refl
#print axioms flatV_gauge
#print axioms flatV_refl
#print axioms flatV_local
#print axioms flatFlow_fieldMap
#print axioms symPlaq_one
#print axioms classMoments_of_densityEach
#print axioms classMoments_flatFlow
#print axioms flat_reach
#print axioms flat_hU_hphys_hreach
#print axioms siteExp_of_split
#print axioms classMoments_of_split
#print axioms siteExp_of_zoomStable
#print axioms classMoments_of_zoomStable
#print axioms not_classMoments_identity_poly

end MassGap.ExistenceFlow

end
