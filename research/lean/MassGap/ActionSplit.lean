import Mathlib
import MassGap.Reflect
import MassGap.ReflectPositive

/-!
# MassGap.ActionSplit — the shared block, integrated OUTSIDE the square

`ReflectionPositivity.pairing_with_reflection_nonneg` proves that an observable paired with its own
reflection integrates to a SQUARE, and it needs `Disjoint S T`: the positive half and its mirror must
read disjoint coordinates. Under a reflection of the Wilson lattice they do not. The links lying in
the reflection plane — the transverse links at a fixed site-plane, and, when the extent is odd, the
axis link whose midpoint is fixed — are read by BOTH halves. `WilsonReal.block_integral_factor`, the
tree's only decomposition, is two-block and requires disjointness, so neither lemma applies.

## What is here

The three-block form. Split the index set into `S` (one side), `T` (its mirror) and `R` (the shared
block), and condition on `R`:

    ∫ w(U|R) · O(U) · O(ΘU) dU  =  ∫ over U|R of  w(U|R) · ( ∫ over U|S of O )²

— the shared block integrated OUTSIDE the square, with a weight `w` of the shared block riding along.
`pairing_eq_weighted_square` is that identity; `pairing_nonneg_of_shared_block` is the inequality it
gives once `w ≥ 0`, proved directly and with weaker hypotheses. Neither requires `S ∪ T ∪ R` to
exhaust the index set, and neither is available from `pairing_with_reflection_nonneg`.

The reflection is allowed to TWIST each coordinate, not merely relabel it (`twist`), because the
Osterwalder–Seiler time reflection daggers the axis links: `Reflect.reflConf` is exactly
`twist (reflLinkPerm τ c) (axisDagger τ)` (`reflConf_eq_twist`), and
`wilson_pairing_nonneg_of_shared_block` is the weld stated on the Wilson lattice.

## Where the plane is, and which cases have a cross term

`reflSite τ c` fixes the sites with `2x = c` (`reflSite_fixed_iff`); `reflLink τ c` fixes a
transverse link when `2 x_τ = c` (`reflLink_fixed_iff_transverse`) and an axis link when
`2 x_τ = c − 1` (`reflLink_fixed_iff_axis`). On `Fin n` that is a parity question and it splits three
ways:

* **`n` even, `c` even** — `2x = c` has a solution (`exists_fixed_site`) and `2x = c − 1` has none
  (`no_fixed_axis_link`). Site-planes only: the shared block `R` is made of transverse links,
  `reflLink` fixes each one and `reflConf` does not invert it, so the two geometric hypotheses of
  `wilson_pairing_nonneg_of_shared_block` (`hR`, `hRτ`) are available, and
  `exists_fixed_transverse_link` shows `R` is genuinely nonempty. What is still NOT supplied in this
  case is the PLAQUETTE partition — that every plaquette reads `S ∪ R`, `T ∪ R` or `R` alone — which
  the weld takes as its hypotheses `hO` and `hW`.
* **`n` even, `c` odd** — no fixed site, and fixed AXIS links, which `reflConf` INVERTS. The shared
  block is acted on nontrivially, so `hσR` fails and the conditional argument does not close. This is
  link reflection.
* **`n` odd** — `2` is a unit, so for EVERY `c` there is a fixed site AND a fixed axis link. Proved
  here at the PINNED extent only, by evaluation: `Complete.wilsonCorr` runs the lag over
  `Fin (nCorrYM + 1)` with `nCorrYM = 16`, so `n = 17`, and `pinned_exists_half`,
  `pinned_exists_half_sub_one`, `pinned_half_unique` and `exists_fixed_axis_link_pinned` settle that
  extent. `reflConf_inverts_fixed_axis_link` is then the exact blocker.

## The negative control

Moving the shared block INSIDE the square is not a harmless rearrangement. `coin_pairing_ne_sq`
computes both sides on a fair coin: the conditional form (shared block outside) gives `1/2`, which is
the true value of the pairing; the two-block form (shared block inside) gives `1/4`.
`shared_block_inside_square_false` turns that into a refutation of the two-block identity applied to
a shared coordinate — so the `Disjoint` hypothesis of `pairing_with_reflection_nonneg` is not
decoration.

## The Wilson weight, in that case, is put into the paired form — and the pairing inequality holds

At even extent the plaquettes partition four ways: degenerate (`μ = ν = τ`, identity holonomy, zero
contribution), inside a plane, reading `S ∪ R`, reading `T ∪ R` (`sum_plaq_split`, `plaq_links_le`,
`plaq_links_ge`, `plaq_links_plane`). The reflection EXCHANGES the last two
(`sum_plqMinus_eq_plus_refl`), so `exp(−βS)` becomes `w(U|R) · h(U) · h(ΘU)`
(`integrand_eq_paired`), and `wilson_pairing_nonneg_even` is the Osterwalder–Seiler pairing
inequality for the `SU(N)` plaquette-energy observable — proved, not cited.

`plaqReflPositive_of_even_lag` discharges `ReflectPositive.PlaqReflPositive` outright at even extent
and even lag, and `corrHyper_nonneg_even_lag` gives `0 ≤ corrHyper` there with no hypothesis at all.

## Choosing the aperture so that this applies

`Complete.confinement_of_bounded_substrate` concludes `∀ᶠ N in atTop`, and
`exists_even_extent_aperture` intersects that cofinal set with the cofinal set of `N` whose extent
`N + 1` is even. So the even case is reachable without changing any pinned constant.

## What this still does NOT discharge

`Complete.wilson_reflection_positive_at`, because `ReflectPositive.corrClay_rp_of` needs
`PlaqReflPositive` at EVERY lag and only the even lags are covered — half of them at even extent, and
NONE at the pinned extent `17`, which is odd so `n = 2 * m` never holds there.

An ODD lag at even extent fixes an AXIS link (`odd_lag_has_fixed_axis_link`) which `reflConf`
INVERTS (`reflConf_inverts_fixed_axis_link`), so `hσR` of the weld fails and the conditional square
has nothing to condition on. That is the link-reflection cross term, and closing it is the
Osterwalder–Seiler character expansion: `ReflectionPositivity.reflection_positive_of_expansion` is
proved and foundational-only and consumes exactly such an expansion, so what is missing is the
expansion's nonnegative coefficients for the `SU(3)` Wilson weight, not the mechanism.

Foundational footprint only (`#print axioms` at the end).
Build: `python code/lean_build.py build MassGap.ActionSplit`.
-/

namespace MassGap.ActionSplit

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ReflectionPositivity
open MassGap.CompactGauge

/-! ## Small measure-theoretic tools -/

/-- A bounded measurable real function is integrable against a finite measure. -/
theorem integrable_of_bounded {γ : Type} [MeasurableSpace γ] (m : Measure γ) [IsFiniteMeasure m]
    {g : γ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ z, |g z| ≤ C) : Integrable g m :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC z)

/-- Change of variables along a measure-preserving MAP (not necessarily an equivalence) — the twist
below need not be invertible. -/
theorem integral_comp_of_mp {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {m' : Measure β} {f : α → β} (hf : MeasurePreserving f m m')
    {G : β → ℝ} (hG : Measurable G) : (∫ x, G (f x) ∂m) = ∫ y, G y ∂m' := by
  have h1 : (∫ y, G y ∂(Measure.map f m)) = ∫ x, G (f x) ∂m :=
    integral_map hf.measurable.aemeasurable hG.aestronglyMeasurable
  rw [← h1, hf.map_eq]

/-- **Fubini in the form this file uses**: a product integral is nonnegative as soon as every INNER
integral is. Getting the pairing into this shape is the whole point of the three-block split. -/
theorem prod_integral_nonneg {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (m : Measure α) (m' : Measure β) [IsProbabilityMeasure m] [IsProbabilityMeasure m']
    {f : α × β → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ z, |f z| ≤ C)
    (hpos : ∀ x, 0 ≤ ∫ y, f (x, y) ∂m') : 0 ≤ ∫ z, f z ∂(m.prod m') := by
  rw [integral_prod _ (integrable_of_bounded _ hf hC)]
  exact integral_nonneg (fun x => hpos x)

/-- The companion of `prod_integral_nonneg`: two product integrals agree as soon as every pair of
INNER integrals does. -/
theorem prod_integral_congr_inner {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (m : Measure α) (m' : Measure β) [IsProbabilityMeasure m] [IsProbabilityMeasure m']
    {f g : α × β → ℝ} (hf : Measurable f) (hg : Measurable g) {C : ℝ}
    (hCf : ∀ z, |f z| ≤ C) (hCg : ∀ z, |g z| ≤ C)
    (hinner : ∀ x, (∫ y, f (x, y) ∂m') = ∫ y, g (x, y) ∂m') :
    (∫ z, f z ∂(m.prod m')) = ∫ z, g z ∂(m.prod m') := by
  rw [integral_prod _ (integrable_of_bounded _ hf hCf),
    integral_prod _ (integrable_of_bounded _ hg hCg)]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

/-! ## Configurations, relabelling, twisting -/

/-- The product measure on configurations `ι → Ω`. -/
noncomputable abbrev cvol (ι : Type) [Fintype ι] {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) : Measure (ι → Ω) := Measure.pi (fun _ : ι => μ)

/-- **Relabel the coordinates by `e` and twist each coordinate by `σ`.**

A bare permutation of the index set is not enough for a reflection: the Osterwalder–Seiler time
reflection inverts the gauge variable on every link running along the reflection axis, and that
dagger is the `σ`. With `σ = id` this is `ReflectionPositivity.relabel`; with the axis inversion it
is `Reflect.reflConf` (`reflConf_eq_twist`). -/
def twist {ι Ω : Type} (e : Equiv.Perm ι) (σ : ι → Ω → Ω) (U : ι → Ω) : ι → Ω :=
  fun i => σ i (U (e i))

@[simp] theorem twist_apply {ι Ω : Type} (e : Equiv.Perm ι) (σ : ι → Ω → Ω) (U : ι → Ω) (i : ι) :
    twist e σ U i = σ i (U (e i)) := rfl

theorem measurable_twist {ι Ω : Type} [MeasurableSpace Ω] (e : Equiv.Perm ι) (σ : ι → Ω → Ω)
    (hσ : ∀ i, Measurable (σ i)) : Measurable (twist e σ) :=
  measurable_pi_lambda _ (fun i => (hσ i).comp (measurable_pi_apply (e i)))

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **The twist preserves the product measure** when every coordinate map does: relabelling is a
symmetry of a product of identical factors, and the coordinate maps act one factor at a time. -/
theorem twist_measurePreserving (e : Equiv.Perm ι) (σ : ι → Ω → Ω)
    (hσ : ∀ i, MeasurePreserving (σ i) μ μ) :
    MeasurePreserving (twist e σ) (cvol ι μ) (cvol ι μ) := by
  have hrel : MeasurePreserving (fun (U : ι → Ω) (i : ι) => U (e i)) (cvol ι μ) (cvol ι μ) := by
    have h : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e)
        (cvol ι μ) (cvol ι μ) := by
      simpa using measurePreserving_piCongrLeft (μ := fun _ : ι => μ) e
    exact h.symm _
  have hco : MeasurePreserving (fun (V : ι → Ω) (i : ι) => σ i (V i)) (cvol ι μ) (cvol ι μ) := by
    refine ⟨measurable_pi_lambda _ (fun i => (hσ i).measurable.comp (measurable_pi_apply i)), ?_⟩
    show Measure.map (fun (V : ι → Ω) (i : ι) => σ i (V i)) (cvol ι μ) = cvol ι μ
    rw [Measure.pi_map_pi (fun i => (hσ i).aemeasurable)]
    exact congrArg Measure.pi (funext fun i => (hσ i).map_eq)
  exact hco.comp hrel

/-- **Disjoint blocks factorise**, for any product of identical probability factors. The generic form
of `WilsonReal.block_integral_factor`; the three-block argument applies it on the COMPLEMENT of the
shared block, whose coordinate type is a subtype, which is why the `SU(N)`-specific statement in the
tree could not be reused. -/
theorem block_factor (S T : Finset ι) (hST : Disjoint S T)
    (φ : (S → Ω) → ℝ) (ψ : (T → Ω) → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    (∫ U, φ (fun i : S => U (i : ι)) * ψ (fun i : T => U (i : ι)) ∂(cvol ι μ))
      = (∫ U, φ (fun i : S => U (i : ι)) ∂(cvol ι μ))
        * (∫ U, ψ (fun i : T => U (i : ι)) ∂(cvol ι μ)) := by
  have hi : iIndepFun (fun (i : ι) (U : ι → Ω) => U i) (cvol ι μ) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hind := hi.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  have hrS : Measurable (fun U : ι → Ω => fun i : S => U (i : ι)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ι))
  have hrT : Measurable (fun U : ι → Ω => fun i : T => U (i : ι)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ι))
  exact (hind.comp hφ hψ).integral_fun_mul_eq_mul_integral
    (hφ.comp hrS).aestronglyMeasurable (hψ.comp hrT).aestronglyMeasurable

end Generic

/-- A block of the index set, seen inside the complement of the shared block `R`. -/
def offBlock {ι : Type} [Fintype ι] [DecidableEq ι] (R S : Finset ι) :
    Finset {i : ι // i ∉ R} :=
  Finset.univ.filter (fun j => (j : ι) ∈ S)

theorem mem_offBlock {ι : Type} [Fintype ι] [DecidableEq ι] (R S : Finset ι)
    (j : {i : ι // i ∉ R}) : j ∈ offBlock R S ↔ (j : ι) ∈ S := by
  simp [offBlock]

theorem offBlock_disjoint {ι : Type} [Fintype ι] [DecidableEq ι] (R S T : Finset ι)
    (hST : Disjoint S T) : Disjoint (offBlock R S) (offBlock R T) :=
  Finset.disjoint_left.mpr fun j hj hj' =>
    Finset.disjoint_left.mp hST ((mem_offBlock R S j).mp hj) ((mem_offBlock R T j).mp hj')

/-! ## THE WELD: the shared block, integrated outside the square -/

section Weld

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Reflection positivity with a SHARED block.**

`S` is one side of the reflection, `T` its mirror, `R` the block both sides read — the reflection
plane. `Θ = twist θ σ` relabels by `θ` and twists coordinatewise; it must fix `R` (`hθR`, `hσR`) and
carry `S` into `T` (`hθST`). `O` reads `S` and `R` only (`hO`); `W` reads `R` only (`hW`) and is
nonnegative (`hw`) — that is where `exp(−β S₀)`, the plane's own share of the Boltzmann weight, goes.

The proof is the three-block conditional Fubini: condition on `R`, and for each FIXED configuration
of the plane the remaining integral factorises over the two disjoint halves (`block_factor`) into two
EQUAL factors (`twist_measurePreserving`, on the complement of the plane), i.e. into a square. The
shared block is integrated OUTSIDE that square, against the nonnegative weight. Moving it inside is
false — `coin_pairing_ne_sq`.

Nothing here needs `S ∪ T ∪ R` to exhaust the index set: coordinates no one reads come along.

DERIVED: the only numeral is the `0` of `0 ≤ …`, which IS the property asserted. -/
theorem pairing_nonneg_of_shared_block
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u)
    (hθST : ∀ i ∈ S, θ i ∈ T)
    (h : (S → Ω) → (R → Ω) → ℝ) (hmS : ∀ v : (R → Ω), Measurable (fun u : (S → Ω) => h u v))
    (w : (R → Ω) → ℝ) (hw : ∀ v, 0 ≤ w v)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hO : ∀ U, O U = h (fun i : S => U (i : ι)) (fun i : R => U (i : ι)))
    (W : (ι → Ω) → ℝ) (hWm : Measurable W)
    (hW : ∀ U, W U = w (fun i : R => U (i : ι)))
    (C : ℝ) (hC : ∀ U, |W U * O U * O (twist θ σ U)| ≤ C) :
    0 ≤ ∫ U, W U * O U * O (twist θ σ U) ∂(cvol ι μ) := by
  -- the reflection fixes the shared block setwise, hence its complement too
  have hθmem : ∀ i, θ i ∈ R ↔ i ∈ R := by
    intro i
    constructor
    · intro hi
      have h1 : θ (θ i) = θ i := hθR _ hi
      have h2 : θ i = i := θ.injective h1
      rwa [h2] at hi
    · intro hi; rw [hθR i hi]; exact hi
  have hθY : ∀ i : ι, (θ i ∉ R) ↔ (i ∉ R) := fun i => not_congr (hθmem i)
  have hSoff : ∀ i : S, ((i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hSR i.2
  have hToff : ∀ i : S, (θ (i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hTR (hθST _ i.2)
  set F : (ι → Ω) → ℝ := fun U => W U * O U * O (twist θ σ U) with hF
  have hFm : Measurable F :=
    (hWm.mul hOm).mul (hOm.comp (measurable_twist θ σ (fun i => (hσ i).measurable)))
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ R)
  have hsm : Measurable
      ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) (fun i => i ∈ R)).symm) :=
    MeasurableEquiv.measurable _
  have hsym : ∀ (x : {i : ι // i ∈ R} → Ω) (y : {i : ι // i ∉ R} → Ω) (i : ι),
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) (fun i => i ∈ R)).symm (x, y) i
        = if hi : i ∈ R then x ⟨i, hi⟩ else y ⟨i, hi⟩ := fun _ _ _ => rfl
  refine le_of_le_of_eq ?_ ((hmp.symm _).integral_comp' F)
  refine prod_integral_nonneg _ _ (hFm.comp hsm) (C := C) (fun z => hC _) ?_
  intro x
  set Φ : ((offBlock R S) → Ω) → ℝ :=
    fun v => h (fun i : S => v ⟨⟨(i : ι), hSoff i⟩, (mem_offBlock R S _).mpr i.2⟩) x with hΦ
  set Ψ : ((offBlock R T) → Ω) → ℝ :=
    fun v => h (fun i : S => σ (i : ι)
      (v ⟨⟨θ (i : ι), hToff i⟩, (mem_offBlock R T _).mpr (hθST _ i.2)⟩)) x with hΨ
  have hΦm : Measurable Φ :=
    (hmS x).comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  have hΨm : Measurable Ψ :=
    (hmS x).comp (measurable_pi_lambda _
      (fun i => ((hσ (i : ι)).measurable).comp (measurable_pi_apply _)))
  -- the inner integrand, rewritten into a paired product over two DISJOINT blocks
  have hrw : ∀ y : {i : ι // i ∉ R} → Ω,
      F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) (fun i => i ∈ R)).symm (x, y))
        = w x * (Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
            * Ψ (fun j : offBlock R T => y (j : {i : ι // i ∉ R}))) := by
    intro y
    have hxR : (fun i : R => (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y) (i : ι)) = x := by
      funext i; rw [hsym, dif_pos i.2]
    have hxS : (fun i : S => (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y) (i : ι))
          = fun i : S => y ⟨(i : ι), hSoff i⟩ := by
      funext i; rw [hsym, dif_neg (hSoff i)]
    have hxT : (fun i : S => twist θ σ ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y)) (i : ι))
          = fun i : S => σ (i : ι) (y ⟨θ (i : ι), hToff i⟩) := by
      funext i
      simp only [twist_apply]
      rw [hsym, dif_neg (hToff i)]
    have hxR' : (fun i : R => twist θ σ ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y)) (i : ι)) = x := by
      funext i
      simp only [twist_apply]
      rw [hθR (i : ι) i.2, hσR (i : ι) i.2, hsym, dif_pos i.2]
    simp only [hF]
    rw [hW, hO, hO, hxR, hxR', hxS, hxT]
    simp only [hΦ, hΨ]
    ring
  -- the mirror: the two factors integrate to the same number
  have hmir : (∫ y, Ψ (fun j : offBlock R T => y (j : {i : ι // i ∉ R}))
        ∂(cvol {i : ι // i ∉ R} μ))
      = ∫ y, Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
        ∂(cvol {i : ι // i ∉ R} μ) := by
    have hmpY := twist_measurePreserving (ι := {i : ι // i ∉ R}) μ (θ.subtypePerm hθY)
      (fun j => σ (j : ι)) (fun j => hσ _)
    have hres : Measurable (fun (y : {i : ι // i ∉ R} → Ω) (j : offBlock R S) =>
        y (j : {i : ι // i ∉ R})) := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
    have hGm : Measurable (fun y : {i : ι // i ∉ R} → Ω =>
        Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))) := hΦm.comp hres
    rw [← integral_comp_of_mp hmpY hGm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hΦ, hΨ, twist_apply]
    rfl
  have hstep : (∫ y, F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y)) ∂(cvol {i : ι // i ∉ R} μ))
      = w x * ((∫ y, Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
          ∂(cvol {i : ι // i ∉ R} μ))
        * (∫ y, Ψ (fun j : offBlock R T => y (j : {i : ι // i ∉ R}))
          ∂(cvol {i : ι // i ∉ R} μ))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw), integral_const_mul,
      block_factor μ (offBlock R S) (offBlock R T) (offBlock_disjoint R S T hST) Φ Ψ hΦm hΨm]
  show (0 : ℝ) ≤ ∫ y, F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
    (fun i => i ∈ R)).symm (x, y)) ∂(cvol {i : ι // i ∉ R} μ)
  rw [hstep, hmir]
  exact mul_nonneg (hw x) (mul_self_nonneg _)

/-- **The conditional half-integral.** Integrate the observable over one side of the plane with the
shared block held FIXED at `U|R`; it depends on `U` only through `U|R`. This is the `∫` that gets
squared in `pairing_eq_weighted_square`, with the plane integral outside it. -/
noncomputable def halfIntegral (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ) (U : ι → Ω) : ℝ :=
  ∫ y : {i : ι // i ∉ R} → Ω,
    h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩) (fun i : R => U (i : ι))
    ∂(cvol {i : ι // i ∉ R} μ)

/-- **The conditional half-integral is measurable**, as a function of the whole configuration — it
reads it only through the shared block.

Used by `pairing_eq_weighted_square` and `integrable_weighted_halfIntegral_sq`.

DERIVED: no numeral. -/
theorem measurable_halfIntegral (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2)) :
    Measurable (halfIntegral μ S R hSR h) := by
  have hSoff : ∀ i : S, ((i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hSR i.2
  have hrest : Measurable (fun (y : {i : ι // i ∉ R} → Ω) (i : S) => y ⟨(i : ι), hSoff i⟩) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hjoint : Measurable (fun p : ((R → Ω) × ({i : ι // i ∉ R} → Ω)) =>
      h (fun i : S => p.2 ⟨(i : ι), hSoff i⟩) p.1) :=
    hmj.comp ((hrest.comp measurable_snd).prodMk measurable_fst)
  have hk : Measurable (fun v : (R → Ω) =>
      ∫ y, h (fun i : S => y ⟨(i : ι), hSoff i⟩) v ∂(cvol {i : ι // i ∉ R} μ)) :=
    (hjoint.stronglyMeasurable.integral_prod_right').measurable
  have hres2 : Measurable (fun (U : ι → Ω) (i : R) => U (i : ι)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ι))
  exact hk.comp hres2

/-- **A bound on the observable bounds its half-integral**, the measure being a probability measure
so the integral cannot amplify it.

Used by `pairing_eq_weighted_square` and `integrable_weighted_halfIntegral_sq`.

DERIVED: no numeral. -/
theorem abs_halfIntegral_le (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ) {Ch : ℝ} (hCh : ∀ u v, |h u v| ≤ Ch) (U : ι → Ω) :
    |halfIntegral μ S R hSR h U| ≤ Ch := by
  show |∫ y, h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
      (fun i : R => U (i : ι)) ∂(cvol {i : ι // i ∉ R} μ)| ≤ Ch
  have hb : ‖∫ y, h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
      (fun i : R => U (i : ι)) ∂(cvol {i : ι // i ∉ R} μ)‖
      ≤ Ch * (cvol {i : ι // i ∉ R} μ Set.univ).toReal := by
    refine norm_integral_le_of_norm_le_const ?_
    exact Filter.Eventually.of_forall (fun y => by simpa [Real.norm_eq_abs] using hCh _ _)
  simpa [Real.norm_eq_abs] using hb

/-- **⭐ A FLOOR ON THE OBSERVABLE IS A FLOOR ON ITS HALF-INTEGRAL.**

The half-integral is taken against a PROBABILITY measure, so it cannot fall below the observable's
own lower bound. That is the whole content.

**⛔ THE UPPER BOUND IS LOAD-BEARING FOR THE STATEMENT**, not merely for the tactic: the Bochner
integral of a non-integrable function is `0` by convention, so without `hCh` an unbounded `h` gives
`halfIntegral = 0` and any positive floor REFUTES the conclusion.

**⛔ NOTHING CONSUMES THIS.** It is recorded as the companion to `abs_halfIntegral_le` — that one
bounds above, this one below — and because the Bochner convention above is worth writing down once.

DERIVED: no numeral. -/
theorem le_halfIntegral (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    {Ch : ℝ} (hCh : ∀ u v, |h u v| ≤ Ch)
    {c : ℝ} (hc : ∀ u v, c ≤ h u v) (U : ι → Ω) :
    c ≤ halfIntegral μ S R hSR h U := by
  classical
  have hSoff : ∀ i : S, ((i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hSR i.2
  have hrest : Measurable (fun (y : {i : ι // i ∉ R} → Ω) (i : S) => y ⟨(i : ι), hSoff i⟩) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hfm : Measurable (fun y : {i : ι // i ∉ R} → Ω =>
      h (fun i : S => y ⟨(i : ι), hSoff i⟩) (fun i : R => U (i : ι))) :=
    hmj.comp (hrest.prodMk measurable_const)
  have hfi : Integrable (fun y : {i : ι // i ∉ R} → Ω =>
      h (fun i : S => y ⟨(i : ι), hSoff i⟩) (fun i : R => U (i : ι)))
      (cvol {i : ι // i ∉ R} μ) :=
    integrable_of_bounded (cvol {i : ι // i ∉ R} μ) hfm (fun _ => hCh _ _)
  have hmono := integral_mono (integrable_const c) hfi (fun _ => hc _ _)
  show c ≤ ∫ y, h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
      (fun i : R => U (i : ι)) ∂(cvol {i : ι // i ∉ R} μ)
  simpa using hmono

/-- **⭐ A CONSTANT COMES OUT OF THE HALF-INTEGRAL.**

The half-integral is against a PROBABILITY measure, so subtracting a constant from the observable
subtracts it from the half-integral.

**WHY IT IS WANTED.** It is what makes the vanishing criterion usable on a MEAN-SUBTRACTED
observable — the only kind `TransferGap.GapAt` sees. With it, the form at `O - k` vanishes exactly
when `O`'s conditional half-integral is a.e. `k`, which is a statement about `O`'s dependence on the
SHARED block and not about `O` being constant.

DERIVED: no numeral. -/
theorem halfIntegral_sub_const (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    {Ch : ℝ} (hCh : ∀ u v, |h u v| ≤ Ch) (k : ℝ) (U : ι → Ω) :
    halfIntegral μ S R hSR (fun v w => h v w - k) U
      = halfIntegral μ S R hSR h U - k := by
  classical
  have hSoff : ∀ i : S, ((i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hSR i.2
  have hrest : Measurable (fun (y : {i : ι // i ∉ R} → Ω) (i : S) => y ⟨(i : ι), hSoff i⟩) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hfm : Measurable (fun y : {i : ι // i ∉ R} → Ω =>
      h (fun i : S => y ⟨(i : ι), hSoff i⟩) (fun i : R => U (i : ι))) :=
    hmj.comp (hrest.prodMk measurable_const)
  have hfi : Integrable (fun y : {i : ι // i ∉ R} → Ω =>
      h (fun i : S => y ⟨(i : ι), hSoff i⟩) (fun i : R => U (i : ι)))
      (cvol {i : ι // i ∉ R} μ) :=
    integrable_of_bounded (cvol {i : ι // i ∉ R} μ) hfm (fun _ => hCh _ _)
  show (∫ y, (h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
      (fun i : R => U (i : ι)) - k) ∂(cvol {i : ι // i ∉ R} μ))
      = (∫ y, h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
        (fun i : R => U (i : ι)) ∂(cvol {i : ι // i ∉ R} μ)) - k
  rw [integral_sub hfi (integrable_const k), integral_const]
  simp



/-- **A factor reading the shared block alone pulls out of the half-integral.**

DERIVED: no numeral. -/
theorem halfIntegral_mul_R_left (S R : Finset ι) (hSR : Disjoint S R)
    (f : (R → Ω) → ℝ) (k : (S → Ω) → (R → Ω) → ℝ) (U : ι → Ω) :
    halfIntegral μ S R hSR (fun v w => f w * k v w) U
      = f (fun i : R => U (i : ι)) * halfIntegral μ S R hSR k U := by
  unfold halfIntegral
  exact integral_const_mul _ _

#print axioms halfIntegral_mul_R_left

/-- **TWO VALUES of the half-integral, from a shared-block factor with a zero.**

`f` vanishing at one plane configuration and positive at another suffices, because the remaining
`S`-integral is strictly positive whenever the integrand has a positive lower bound.

DERIVED: the `0`s are `f`'s value at `a` and the lower bounds; no other numeral. -/
theorem halfIntegral_two_values_of_R_factor (S R : Finset ι) (hSR : Disjoint S R)
    (f : (R → Ω) → ℝ) (k : (S → Ω) → (R → Ω) → ℝ)
    (hkm : Measurable (fun q : ((S → Ω) × (R → Ω)) => k q.1 q.2))
    {Ck : ℝ} (hkb : ∀ v w, |k v w| ≤ Ck) {c : ℝ} (hc0 : 0 < c) (hc : ∀ v w, c ≤ k v w)
    {a b : ι → Ω}
    (ha : f (fun i : R => a (i : ι)) = 0) (hb : 0 < f (fun i : R => b (i : ι))) :
    halfIntegral μ S R hSR (fun v w => f w * k v w) a
      ≠ halfIntegral μ S R hSR (fun v w => f w * k v w) b := by
  rw [halfIntegral_mul_R_left μ S R hSR f k a, halfIntegral_mul_R_left μ S R hSR f k b, ha,
    zero_mul]
  have hD : 0 < halfIntegral μ S R hSR k b :=
    lt_of_lt_of_le hc0 (le_halfIntegral μ S R hSR k hkm hkb hc b)
  exact ne_of_lt (mul_pos hb hD)

#print axioms halfIntegral_two_values_of_R_factor

/-- **THE VARIANCE IS BELOW EVERY CENTRED SECOND MOMENT.** The quadratic in `k` is minimised at the
mean, so subtracting the WRONG constant can only increase the integral.

A lower bound built on this holds at EVERY `k`, so a caller need not identify the constant being
subtracted.

**⛔ NOTHING ROUTES THAT INTO `hfin` YET.** `gapAt_of_finite_volume_connected` is discharged
through `WilsonTransferReduction.gapAt_iff_subtracted_pairing`, which does not mention this.

DERIVED: the `2`s are the squares; no other numeral. -/
theorem variance_le_integral_sub_const_sq {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (g : X → ℝ) (hg : Integrable g ν)
    (hg2 : Integrable (fun x => g x ^ 2) ν) (k : ℝ) :
    (∫ x, g x ^ 2 ∂ν) - (∫ x, g x ∂ν) ^ 2 ≤ ∫ x, (g x - k) ^ 2 ∂ν := by
  have hi1 : Integrable (fun x => g x ^ 2 - 2 * k * g x) ν := hg2.sub (hg.const_mul _)
  have hrw : (fun x => (g x - k) ^ 2) = fun x => (g x ^ 2 - 2 * k * g x) + k ^ 2 := by
    funext x
    ring
  have he : (∫ x, (g x - k) ^ 2 ∂ν)
      = (∫ x, g x ^ 2 ∂ν) - 2 * k * (∫ x, g x ∂ν) + k ^ 2 := by
    rw [hrw, integral_add hi1 (integrable_const _), integral_sub hg2 (hg.const_mul _)]
    simp [integral_const_mul]
  rw [he]
  nlinarith [sq_nonneg (k - ∫ x, g x ∂ν)]

#print axioms variance_le_integral_sub_const_sq

/-- **THE VARIANCE IS THE SECOND MOMENT ABOUT THE MEAN.**

**⛔ THIS IS NOT NEW CONTENT.** Mathlib's `ProbabilityTheory.variance` carries the same identity
for `MemLp 2`; this states it for the `∫f² − (∫f)²` difference that
`pairing_ge_weight_min_mul_variance` writes, with `Integrable` hypotheses instead.

DERIVED: the `2`s are the squares; no other numeral. -/
theorem variance_eq_integral_sub_mean_sq {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (g : X → ℝ) (hg : Integrable g ν)
    (hg2 : Integrable (fun x => g x ^ 2) ν) :
    (∫ x, g x ^ 2 ∂ν) - (∫ x, g x ∂ν) ^ 2
      = ∫ x, (g x - (∫ y, g y ∂ν)) ^ 2 ∂ν := by
  have hi1 : Integrable (fun x => g x ^ 2 - 2 * (∫ y, g y ∂ν) * g x) ν :=
    hg2.sub (hg.const_mul _)
  have hrw : (fun x => (g x - (∫ y, g y ∂ν)) ^ 2)
      = fun x => (g x ^ 2 - 2 * (∫ y, g y ∂ν) * g x) + (∫ y, g y ∂ν) ^ 2 := by
    funext x
    ring
  have he : (∫ x, (g x - (∫ y, g y ∂ν)) ^ 2 ∂ν)
      = (∫ x, g x ^ 2 ∂ν) - 2 * (∫ y, g y ∂ν) * (∫ x, g x ∂ν)
        + (∫ y, g y ∂ν) ^ 2 := by
    rw [hrw, integral_add hi1 (integrable_const _), integral_sub hg2 (hg.const_mul _)]
    simp [integral_const_mul]
  rw [he]
  ring

#print axioms variance_eq_integral_sub_mean_sq

/-- **⭐ AND IT IS POSITIVE EXACTLY WHEN `g` IS NOT A.E. ITS OWN MEAN.**

This is what makes `pairing_ge_weight_min_mul_variance` say more than `pairing_nonneg_of_local`:
without it the bound is `0 ≤ pairing`, which is already known.
`not_ae_eq_const_of_two_values` discharges the hypothesis from two values.

**⛔ DO NOT ADD A `variance_pos_of_two_values` HERE.**
`HaarVariance.variance_pos_of_two_values` proves the EQUIVALENT fact, independently: it cannot be
this composition, since `HaarVariance` does not import `ActionSplit`. It works in Mathlib's
`variance`, applies `Continuous.ae_eq_iff_eq` directly, and takes its integrability from
`CompactSpace` rather than as a hypothesis. Compose the two here at the call site instead.

DERIVED: the `2`s are the squares; the `0` is the positivity concluded. -/
theorem variance_pos_of_not_ae_const {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (g : X → ℝ) (hg : Integrable g ν)
    (hg2 : Integrable (fun x => g x ^ 2) ν)
    (hne : ¬ (g =ᵐ[ν] fun _ => ∫ y, g y ∂ν)) :
    0 < (∫ x, g x ^ 2 ∂ν) - (∫ x, g x ∂ν) ^ 2 := by
  have hqi : Integrable (fun x => (g x - (∫ y, g y ∂ν)) ^ 2) ν := by
    have hrw : (fun x => (g x - (∫ y, g y ∂ν)) ^ 2)
        = fun x => (g x ^ 2 - 2 * (∫ y, g y ∂ν) * g x) + (∫ y, g y ∂ν) ^ 2 := by
      funext x
      ring
    rw [hrw]
    exact (hg2.sub (hg.const_mul _)).add (integrable_const _)
  rw [variance_eq_integral_sub_mean_sq ν g hg hg2]
  have hnn : (0 : ℝ) ≤ ∫ x, (g x - (∫ y, g y ∂ν)) ^ 2 ∂ν :=
    integral_nonneg (fun x => sq_nonneg _)
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    refine hne ?_
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hqi).mp heq.symm
    filter_upwards [hz] with x hx
    have hx0 : (g x - (∫ y, g y ∂ν)) ^ 2 = 0 := hx
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx0
    linarith

#print axioms variance_pos_of_not_ae_const

/-- **⭐⭐ A NUMERIC FLOOR FOR THE VARIANCE, FROM A TEST FUNCTION WITH KNOWN MOMENTS.**

Cauchy–Schwarz: correlating `f` against any mean-zero `g` bounds `f`'s variance below by
`(∫f·g)² / ∫g²`. When `g`'s moments are COMPUTED and `∫f·g` has a floor, the right-hand side is a
number.

Proved by instantiating `0 ≤ ∫((f − mean) − λ·g)²` at the optimal `λ = ∫f·g / ∫g²`, rather than
through a discriminant lemma: `Schwinger.sq_le_of_quad_nonneg` is this tree's discriminant lemma and
`ActionSplit` does not import `Schwinger`.

DERIVED: the `2`s are the squares; the `0`s are `g`'s mean and the sign of its second moment. -/
theorem variance_ge_sq_div_of_mean_zero {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f g : X → ℝ)
    (hf : Integrable f ν) (hf2 : Integrable (fun x => f x ^ 2) ν)
    (hg : Integrable g ν) (hg2 : Integrable (fun x => g x ^ 2) ν)
    (hfg : Integrable (fun x => f x * g x) ν)
    (hg0 : (∫ x, g x ∂ν) = 0) (hgpos : 0 < ∫ x, g x ^ 2 ∂ν) :
    (∫ x, f x * g x ∂ν) ^ 2 / (∫ x, g x ^ 2 ∂ν)
      ≤ (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
  have hi1 : Integrable (fun x => (f x - (∫ y, f y ∂ν)) ^ 2) ν := by
    have hrw : (fun x => (f x - (∫ y, f y ∂ν)) ^ 2)
        = fun x => (f x ^ 2 - 2 * (∫ y, f y ∂ν) * f x) + (∫ y, f y ∂ν) ^ 2 := by
      funext x
      ring
    rw [hrw]
    exact (hf2.sub (hf.const_mul _)).add (integrable_const _)
  have hi2 : Integrable (fun x => (f x - (∫ y, f y ∂ν)) * g x) ν := by
    have hrw : (fun x => (f x - (∫ y, f y ∂ν)) * g x)
        = fun x => f x * g x - (∫ y, f y ∂ν) * g x := by
      funext x
      ring
    rw [hrw]
    exact hfg.sub (hg.const_mul _)
  have hFg : (∫ x, (f x - (∫ y, f y ∂ν)) * g x ∂ν) = ∫ x, f x * g x ∂ν := by
    have hrw : (fun x => (f x - (∫ y, f y ∂ν)) * g x)
        = fun x => f x * g x - (∫ y, f y ∂ν) * g x := by
      funext x
      ring
    rw [hrw, integral_sub hfg (hg.const_mul _), integral_const_mul, hg0]
    ring
  have hF2 : (∫ x, (f x - (∫ y, f y ∂ν)) ^ 2 ∂ν)
      = (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 :=
    (variance_eq_integral_sub_mean_sq ν f hf hf2).symm
  set l : ℝ := (∫ x, f x * g x ∂ν) / (∫ x, g x ^ 2 ∂ν) with hl
  set P1 : X → ℝ := fun x => (f x - (∫ y, f y ∂ν)) ^ 2
      - 2 * l * ((f x - (∫ y, f y ∂ν)) * g x) with hP1
  set P2 : X → ℝ := fun x => l ^ 2 * (g x ^ 2) with hP2
  have hiP1 : Integrable P1 ν := hi1.sub (hi2.const_mul _)
  have hiP2 : Integrable P2 ν := hg2.const_mul _
  have h1 : (∫ x, P1 x ∂ν)
      = ((∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)
        - 2 * l * (∫ x, f x * g x ∂ν) := by
    simp only [hP1]
    rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul, hF2, hFg]
  have h2 : (∫ x, P2 x ∂ν) = l ^ 2 * (∫ x, g x ^ 2 ∂ν) := by
    simp only [hP2]
    rw [integral_const_mul]
  have he : (∫ x, ((f x - (∫ y, f y ∂ν)) - l * g x) ^ 2 ∂ν)
      = ((∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)
        - 2 * l * (∫ x, f x * g x ∂ν) + l ^ 2 * (∫ x, g x ^ 2 ∂ν) := by
    have hpt : (fun x => ((f x - (∫ y, f y ∂ν)) - l * g x) ^ 2)
        = fun x => P1 x + P2 x := by
      funext x
      simp only [hP1, hP2]
      ring
    rw [hpt, integral_add hiP1 hiP2, h1, h2]
  have hnn : 0 ≤ ((∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)
      - 2 * l * (∫ x, f x * g x ∂ν) + l ^ 2 * (∫ x, g x ^ 2 ∂ν) := by
    rw [← he]
    exact integral_nonneg (fun x => sq_nonneg _)
  rw [div_le_iff₀ hgpos]
  rw [hl] at hnn
  field_simp at hnn
  nlinarith [hnn, hgpos]

#print axioms variance_ge_sq_div_of_mean_zero

/-- **A FUNCTION OF ONE COORDINATE INTEGRATES AS IF THE OTHERS WERE NOT THERE.**

`cvol` is `Measure.pi` of copies of one probability measure, so evaluation at a coordinate is
measure preserving (`MeasureTheory.measurePreserving_eval`). This is what carries a COMPUTED
single-link Haar moment to the configuration measure.

DERIVED: no numeral. -/
theorem integral_eval_cvol {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (i₀ : ι) (φ : Ω → ℝ) (hφ : Measurable φ) :
    (∫ U, φ (U i₀) ∂(cvol ι μ)) = ∫ w, φ w ∂μ := by
  have hmp := MeasureTheory.measurePreserving_eval (fun _ : ι => μ) i₀
  have hmeas : AEMeasurable (Function.eval i₀ : (ι → Ω) → Ω) (cvol ι μ) :=
    (measurable_pi_apply i₀).aemeasurable
  have hsm : AEStronglyMeasurable φ (Measure.map (Function.eval i₀) (cvol ι μ)) := by
    rw [hmp.map_eq]
    exact hφ.aestronglyMeasurable
  have h := integral_map hmeas hsm
  rw [hmp.map_eq] at h
  exact h.symm

#print axioms integral_eval_cvol

/-- **⭐⭐ OBSERVABLES ON DISJOINT BLOCKS FACTORISE**, in the LOCALITY form.

`block_factor` states this for observables presented as functions of a block's coordinates. What a
caller holds is a READING statement, so this restates it for `F` reading `R` and `G` reading the
complement, and obtains it from `block_factor` rather than re-deriving the independence.

**⛔ THIS IS THE FREE MEASURE**, not a Gibbs measure. At non-zero coupling the Boltzmann weight
couples the blocks and this is false; bounding that coupling is what a cluster expansion is for.

**⭐ IT IS STATED FOR ARBITRARY BOUNDED MEASURABLE OBSERVABLES**, which is the generality `hfin`
quantifies over. `StrongCoupling`'s decay is stated for ONE PLAQUETTE.

DERIVED: no numeral. -/
theorem integral_mul_of_indep_blocks (R : Finset ι) (base : ι → Ω)
    (F G : (ι → Ω) → ℝ) (hFm : Measurable F) (hGm : Measurable G)
    (hFloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → F U = F V)
    (hGloc : ∀ U V : ι → Ω, (∀ i, i ∉ R → U i = V i) → G U = G V) :
    (∫ U, F U * G U ∂(cvol ι μ))
      = (∫ U, F U ∂(cvol ι μ)) * ∫ U, G U ∂(cvol ι μ) := by
  classical
  set φ : (↥R → Ω) → ℝ := fun x => F (fun i => if h : i ∈ R then x ⟨i, h⟩ else base i) with hφd
  set ψ : (↥(Rᶜ) → Ω) → ℝ :=
    fun y => G (fun i => if h : i ∈ Rᶜ then y ⟨i, h⟩ else base i) with hψd
  have hφm : Measurable φ := by
    refine hFm.comp (measurable_pi_lambda _ (fun i => ?_))
    by_cases h : i ∈ R
    · simp only [dif_pos h]
      exact measurable_pi_apply _
    · simp only [dif_neg h]
      exact measurable_const
  have hψm : Measurable ψ := by
    refine hGm.comp (measurable_pi_lambda _ (fun i => ?_))
    by_cases h : i ∈ Rᶜ
    · simp only [dif_pos h]
      exact measurable_pi_apply _
    · simp only [dif_neg h]
      exact measurable_const
  have hFeq : ∀ U : ι → Ω, F U = φ (fun i : ↥R => U (i : ι)) := by
    intro U
    refine hFloc _ _ (fun i hi => ?_)
    simp [hi]
  have hGeq : ∀ U : ι → Ω, G U = ψ (fun i : ↥(Rᶜ) => U (i : ι)) := by
    intro U
    refine hGloc _ _ (fun i hi => ?_)
    have hic : i ∈ Rᶜ := Finset.mem_compl.mpr hi
    simp [hic]
  have hmul : (∫ U, F U * G U ∂(cvol ι μ))
      = ∫ U, φ (fun i : ↥R => U (i : ι)) * ψ (fun i : ↥(Rᶜ) => U (i : ι)) ∂(cvol ι μ) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun U => by simp only [hFeq, hGeq]))
  have hF : (∫ U, F U ∂(cvol ι μ)) = ∫ U, φ (fun i : ↥R => U (i : ι)) ∂(cvol ι μ) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun U => by simp only [hFeq]))
  have hG : (∫ U, G U ∂(cvol ι μ)) = ∫ U, ψ (fun i : ↥(Rᶜ) => U (i : ι)) ∂(cvol ι μ) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun U => by simp only [hGeq]))
  rw [hmul, hF, hG]
  exact block_factor μ R Rᶜ disjoint_compl_right φ ψ hφm hψm

#print axioms integral_mul_of_indep_blocks




/-- **A UNIFORM LOWER BOUND ON THE WEIGHT PASSES THROUGH THE INTEGRAL**, for a nonnegative
integrand.

DERIVED: the `0` is the integrand's sign; no other numeral. -/
theorem integral_weight_ge {X : Type} [MeasurableSpace X] (ν : Measure X) (W q : X → ℝ)
    {Wmin : ℝ} (hW : ∀ x, Wmin ≤ W x) (hq : ∀ x, 0 ≤ q x)
    (hqi : Integrable q ν) (hWqi : Integrable (fun x => W x * q x) ν) :
    Wmin * (∫ x, q x ∂ν) ≤ ∫ x, W x * q x ∂ν := by
  rw [← integral_const_mul]
  exact integral_mono (hqi.const_mul _) hWqi
    (fun x => mul_le_mul_of_nonneg_right (hW x) (hq x))

#print axioms integral_weight_ge

/-- **A CEILING ON THE THREE-BLOCK PAIRING**, from boundedness alone.

The twin of the floor: `pairing_ge_weight_min_mul_variance` bounds the pairing below, this bounds it
above, and `hfin` needs both because it is a RATIO of two pairings.

**⛔ THERE IS NO DECAY IN THIS.** It is the product of the three bounding constants and nothing
else, so a ratio formed from it and a floor measures how much decay is MISSING — it does not supply
any.

DERIVED: the `0`s are the signs of the two bounding constants; no other numeral. -/
theorem abs_pairing_le
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω)
    (O : (ι → Ω) → ℝ) (Ch : ℝ) (hCh0 : 0 ≤ Ch) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (ι → Ω) → ℝ) (Cw : ℝ) (hCw0 : 0 ≤ Cw) (hWb : ∀ U, |W U| ≤ Cw) (k : ℝ) :
    |∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ)|
      ≤ Cw * (Ch + |k|) * (Ch + |k|) := by
  have hCh0' : (0 : ℝ) ≤ Ch + |k| := add_nonneg hCh0 (abs_nonneg _)
  have hsub : ∀ U, |O U - k| ≤ Ch + |k| :=
    fun U => le_trans (abs_sub _ _) (add_le_add (hOb U) (le_refl _))
  have hpt : ∀ U, |W U * (O U - k) * (O (twist θ σ U) - k)| ≤ Cw * (Ch + |k|) * (Ch + |k|) := by
    intro U
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hWb U) (hsub U) (abs_nonneg _) hCw0) (hsub _)
      (abs_nonneg _) (mul_nonneg hCw0 hCh0')
  have hb : ‖∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ)‖
      ≤ (Cw * (Ch + |k|) * (Ch + |k|)) * (cvol ι μ Set.univ).toReal := by
    refine norm_integral_le_of_norm_le_const ?_
    exact Filter.Eventually.of_forall (fun U => by simpa [Real.norm_eq_abs] using hpt U)
  simpa [Real.norm_eq_abs] using hb

#print axioms abs_pairing_le

/-- **⭐⭐⭐ A NUMBER FOR THE VARIANCE OF `g · D`**, from `g`'s computed moments and a floor on `D`.

Correlating against `g` itself makes the correlation `∫ D·g²`, which the floor bounds below by
`c·v`; `variance_ge_sq_div_of_mean_zero` then gives `Var ≥ (c·v)²/v = c²·v`.

**⛔ IT NEEDS `∫ g = 0`.** Against a `g` with a mean the correlation is not the second moment and
the floor does not pass through.

DERIVED: the `2`s are the squares; the `0`s are `g`'s mean and the signs of `c` and `v`. -/
theorem variance_ge_sq_mul_of_factor_floor {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (g D : X → ℝ)
    {c : ℝ} (hc0 : 0 < c) (hD : ∀ x, c ≤ D x)
    (hg : Integrable g ν) (hg2 : Integrable (fun x => g x ^ 2) ν)
    (hgD : Integrable (fun x => g x * D x) ν)
    (hgDsq : Integrable (fun x => (g x * D x) ^ 2) ν)
    (hgDg : Integrable (fun x => (g x * D x) * g x) ν)
    {v : ℝ} (hg0 : (∫ x, g x ∂ν) = 0) (hv : (∫ x, g x ^ 2 ∂ν) = v) (hvpos : 0 < v) :
    c ^ 2 * v
      ≤ (∫ x, (g x * D x) ^ 2 ∂ν) - (∫ x, g x * D x ∂ν) ^ 2 := by
  have hrw : (fun x => (g x * D x) * g x) = fun x => D x * (g x ^ 2) := by
    funext x
    ring
  have hDg2 : Integrable (fun x => D x * (g x ^ 2)) ν := by
    rw [← hrw]
    exact hgDg
  have hcorr : c * v ≤ ∫ x, (g x * D x) * g x ∂ν := by
    rw [hrw, ← hv]
    exact integral_weight_ge ν D (fun x => g x ^ 2) hD (fun x => sq_nonneg _) hg2 hDg2
  have hcs := variance_ge_sq_div_of_mean_zero ν (fun x => g x * D x) g
    hgD hgDsq hg hg2 hgDg hg0 (by rw [hv]; exact hvpos)
  rw [hv] at hcs
  have hcv : 0 ≤ c * v := le_of_lt (mul_pos hc0 hvpos)
  have hsq : (c * v) ^ 2 ≤ (∫ x, (g x * D x) * g x ∂ν) ^ 2 := by
    nlinarith [hcorr, hcv]
  refine le_trans ?_ hcs
  rw [le_div_iff₀ hvpos]
  nlinarith [hsq]

#print axioms variance_ge_sq_mul_of_factor_floor


/-- **THE THREE-BLOCK CONDITIONAL IDENTITY.**

    ∫ W·O·(O∘Θ)  =  ∫ W · (half-integral)²

with the shared block integrated OUTSIDE the square: the right-hand side is an integral of the SQUARE
of the conditional half-integral, and the weight `W` and the half-integral both read the shared block
only, so the whole right-hand side is a plane integral of `w · (∫ over the half)²`.

This is the identity `pairing_nonneg_of_shared_block` runs on, stated rather than merely used. No
sign hypothesis on `w` is needed — this is an equation. Positivity follows the moment `w ≥ 0`, which
is `pairing_nonneg_of_shared_block`.

The negative control says what changes if the shared block is moved inside the square:
`NegControl.coin_pairing_ne_sq` computes `1/2` here against `1/4` there.

DERIVED: the `2` is the square the identity asserts; the `0`s are the signs of the two bounding
constants `Ch` and `Cw`; the `1`s, `2` and `4` of the control are that control's own values. -/
theorem pairing_eq_weighted_square
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u)
    (hθST : ∀ i ∈ S, θ i ∈ T)
    (h : (S → Ω) → (R → Ω) → ℝ) (hmS : ∀ v : (R → Ω), Measurable (fun u : (S → Ω) => h u v))
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    (Ch : ℝ) (hCh0 : 0 ≤ Ch) (hCh : ∀ u v, |h u v| ≤ Ch)
    (w : (R → Ω) → ℝ) (Cw : ℝ) (hCw0 : 0 ≤ Cw) (hCw : ∀ v, |w v| ≤ Cw)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hO : ∀ U, O U = h (fun i : S => U (i : ι)) (fun i : R => U (i : ι)))
    (W : (ι → Ω) → ℝ) (hWm : Measurable W)
    (hW : ∀ U, W U = w (fun i : R => U (i : ι))) :
    (∫ U, W U * O U * O (twist θ σ U) ∂(cvol ι μ))
      = ∫ U, W U * (halfIntegral μ S R hSR h U) ^ 2 ∂(cvol ι μ) := by
  have hθmem : ∀ i, θ i ∈ R ↔ i ∈ R := by
    intro i
    constructor
    · intro hi
      have h1 : θ (θ i) = θ i := hθR _ hi
      have h2 : θ i = i := θ.injective h1
      rwa [h2] at hi
    · intro hi; rw [hθR i hi]; exact hi
  have hθY : ∀ i : ι, (θ i ∉ R) ↔ (i ∉ R) := fun i => not_congr (hθmem i)
  have hSoff : ∀ i : S, ((i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hSR i.2
  have hToff : ∀ i : S, (θ (i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hTR (hθST _ i.2)
  -- the half-integral is measurable and bounded
  have hhm : Measurable (halfIntegral μ S R hSR h) := measurable_halfIntegral μ S R hSR h hmj
  have hhb : ∀ U, |halfIntegral μ S R hSR h U| ≤ Ch :=
    fun U => abs_halfIntegral_le μ S R hSR h hCh U
  have hOb : ∀ U, |O U| ≤ Ch := fun U => by rw [hO]; exact hCh _ _
  have hWb : ∀ U, |W U| ≤ Cw := fun U => by rw [hW]; exact hCw _
  set F : (ι → Ω) → ℝ := fun U => W U * O U * O (twist θ σ U) with hF
  set G : (ι → Ω) → ℝ := fun U => W U * (halfIntegral μ S R hSR h U) ^ 2 with hG
  have hFm : Measurable F :=
    (hWm.mul hOm).mul (hOm.comp (measurable_twist θ σ (fun i => (hσ i).measurable)))
  have hGm : Measurable G := hWm.mul (hhm.pow_const 2)
  have hFb : ∀ U, |F U| ≤ Cw * Ch ^ 2 := by
    intro U
    have e1 : |F U| = |W U| * |O U| * |O (twist θ σ U)| := by
      simp only [hF, abs_mul]
    have h1 : |W U| * |O U| ≤ Cw * Ch := mul_le_mul (hWb U) (hOb U) (abs_nonneg _) hCw0
    have h2 : |W U| * |O U| * |O (twist θ σ U)| ≤ Cw * Ch * Ch :=
      mul_le_mul h1 (hOb (twist θ σ U)) (abs_nonneg _) (mul_nonneg hCw0 hCh0)
    calc |F U| = |W U| * |O U| * |O (twist θ σ U)| := e1
      _ ≤ Cw * Ch * Ch := h2
      _ = Cw * Ch ^ 2 := by ring
  have hGb : ∀ U, |G U| ≤ Cw * Ch ^ 2 := by
    intro U
    have e1 : |G U| = |W U| * (|halfIntegral μ S R hSR h U| * |halfIntegral μ S R hSR h U|) := by
      simp only [hG, abs_mul, abs_pow]; ring
    have hsq : |halfIntegral μ S R hSR h U| * |halfIntegral μ S R hSR h U| ≤ Ch * Ch :=
      mul_self_le_mul_self (abs_nonneg _) (hhb U)
    calc |G U| = |W U| * (|halfIntegral μ S R hSR h U| * |halfIntegral μ S R hSR h U|) := e1
      _ ≤ Cw * (Ch * Ch) :=
          mul_le_mul (hWb U) hsq (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCw0
      _ = Cw * Ch ^ 2 := by ring
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ R)
  have hsm : Measurable
      ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) (fun i => i ∈ R)).symm) :=
    MeasurableEquiv.measurable _
  have hsym : ∀ (x : {i : ι // i ∈ R} → Ω) (y : {i : ι // i ∉ R} → Ω) (i : ι),
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) (fun i => i ∈ R)).symm (x, y) i
        = if hi : i ∈ R then x ⟨i, hi⟩ else y ⟨i, hi⟩ := fun _ _ _ => rfl
  rw [← (hmp.symm _).integral_comp' F, ← (hmp.symm _).integral_comp' G]
  refine prod_integral_congr_inner _ _ (hFm.comp hsm) (hGm.comp hsm) (C := Cw * Ch ^ 2)
    (fun z => hFb _) (fun z => hGb _) ?_
  intro x
  set Φ : ((offBlock R S) → Ω) → ℝ :=
    fun v => h (fun i : S => v ⟨⟨(i : ι), hSoff i⟩, (mem_offBlock R S _).mpr i.2⟩) x with hΦ
  set Ψ : ((offBlock R T) → Ω) → ℝ :=
    fun v => h (fun i : S => σ (i : ι)
      (v ⟨⟨θ (i : ι), hToff i⟩, (mem_offBlock R T _).mpr (hθST _ i.2)⟩)) x with hΨ
  have hΦm : Measurable Φ :=
    (hmS x).comp (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  have hΨm : Measurable Ψ :=
    (hmS x).comp (measurable_pi_lambda _
      (fun i => ((hσ (i : ι)).measurable).comp (measurable_pi_apply _)))
  have hxR : ∀ y : {i : ι // i ∉ R} → Ω,
      (fun i : R => (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y) (i : ι)) = x := by
    intro y; funext i; rw [hsym, dif_pos i.2]
  have hrw : ∀ y : {i : ι // i ∉ R} → Ω,
      F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) (fun i => i ∈ R)).symm (x, y))
        = w x * (Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
            * Ψ (fun j : offBlock R T => y (j : {i : ι // i ∉ R}))) := by
    intro y
    have hxS : (fun i : S => (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y) (i : ι))
          = fun i : S => y ⟨(i : ι), hSoff i⟩ := by
      funext i; rw [hsym, dif_neg (hSoff i)]
    have hxT : (fun i : S => twist θ σ ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y)) (i : ι))
          = fun i : S => σ (i : ι) (y ⟨θ (i : ι), hToff i⟩) := by
      funext i
      simp only [twist_apply]
      rw [hsym, dif_neg (hToff i)]
    have hxR' : (fun i : R => twist θ σ ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y)) (i : ι)) = x := by
      funext i
      simp only [twist_apply]
      rw [hθR (i : ι) i.2, hσR (i : ι) i.2, hsym, dif_pos i.2]
    simp only [hF]
    rw [hW, hO, hO, hxR y, hxR', hxS, hxT]
    simp only [hΦ, hΨ]
    ring
  have hmir : (∫ y, Ψ (fun j : offBlock R T => y (j : {i : ι // i ∉ R}))
        ∂(cvol {i : ι // i ∉ R} μ))
      = ∫ y, Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
        ∂(cvol {i : ι // i ∉ R} μ) := by
    have hmpY := twist_measurePreserving (ι := {i : ι // i ∉ R}) μ (θ.subtypePerm hθY)
      (fun j => σ (j : ι)) (fun j => hσ _)
    have hres : Measurable (fun (y : {i : ι // i ∉ R} → Ω) (j : offBlock R S) =>
        y (j : {i : ι // i ∉ R})) := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
    have hGm' : Measurable (fun y : {i : ι // i ∉ R} → Ω =>
        Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))) := hΦm.comp hres
    rw [← integral_comp_of_mp hmpY hGm']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hΦ, hΨ, twist_apply]
    rfl
  have hGval : ∀ y : {i : ι // i ∉ R} → Ω,
      G ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) (fun i => i ∈ R)).symm (x, y))
        = w x * (∫ y', Φ (fun j : offBlock R S => y' (j : {i : ι // i ∉ R}))
            ∂(cvol {i : ι // i ∉ R} μ)) ^ 2 := by
    intro y
    have hid : (∫ y', h (fun i : S => y' ⟨(i : ι), hSoff i⟩) x ∂(cvol {i : ι // i ∉ R} μ))
        = ∫ y', Φ (fun j : offBlock R S => y' (j : {i : ι // i ∉ R}))
          ∂(cvol {i : ι // i ∉ R} μ) := rfl
    simp only [hG, halfIntegral]
    rw [hW, hxR y, hid]
  have hLHS : (∫ y, F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y)) ∂(cvol {i : ι // i ∉ R} μ))
      = w x * ((∫ y, Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
          ∂(cvol {i : ι // i ∉ R} μ))
        * (∫ y, Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
          ∂(cvol {i : ι // i ∉ R} μ))) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw), integral_const_mul,
      block_factor μ (offBlock R S) (offBlock R T) (offBlock_disjoint R S T hST) Φ Ψ hΦm hΨm,
      hmir]
  have hRHS : (∫ y, G ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω)
        (fun i => i ∈ R)).symm (x, y)) ∂(cvol {i : ι // i ∉ R} μ))
      = w x * (∫ y, Φ (fun j : offBlock R S => y (j : {i : ι // i ∉ R}))
          ∂(cvol {i : ι // i ∉ R} μ)) ^ 2 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hGval), integral_const]
    simp
  rw [hLHS, hRHS]
  ring

/-- **The weighted square is integrable**, which is what `integral_eq_zero_iff_of_nonneg` requires
of it in `pairing_eq_zero_iff_halfIntegral`.

DERIVED: the `2` is the square of `pairing_eq_weighted_square`, as there; the `0` is the sign of
the weight's bound in `hCw0`, which `integrable_of_bounded` consumes. -/
theorem integrable_weighted_halfIntegral_sq (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    {Ch : ℝ} (hCh : ∀ u v, |h u v| ≤ Ch)
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) {Cw : ℝ} (hCw0 : 0 ≤ Cw) (hCw : ∀ U, |W U| ≤ Cw) :
    Integrable (fun U => W U * (halfIntegral μ S R hSR h U) ^ 2) (cvol ι μ) := by
  have hhm := measurable_halfIntegral μ S R hSR h hmj
  refine integrable_of_bounded (cvol ι μ) (hWm.mul (hhm.pow_const 2))
    (C := Cw * Ch ^ 2) (fun U => ?_)
  have hsq : |halfIntegral μ S R hSR h U| * |halfIntegral μ S R hSR h U| ≤ Ch * Ch :=
    mul_self_le_mul_self (abs_nonneg _) (abs_halfIntegral_le μ S R hSR h hCh U)
  have e1 : |W U * (halfIntegral μ S R hSR h U) ^ 2|
      = |W U| * (|halfIntegral μ S R hSR h U| * |halfIntegral μ S R hSR h U|) := by
    simp only [abs_mul, abs_pow]; ring
  calc |W U * (halfIntegral μ S R hSR h U) ^ 2|
      = |W U| * (|halfIntegral μ S R hSR h U| * |halfIntegral μ S R hSR h U|) := e1
    _ ≤ Cw * (Ch * Ch) :=
        mul_le_mul (hCw U) hsq (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCw0
    _ = Cw * Ch ^ 2 := by ring

/-- **⭐⭐ THE REFLECTION FORM IS BOUNDED BELOW BY THE HALF-INTEGRAL'S VARIANCE, UNIFORMLY IN `k`.**

`pairing_eq_weighted_square` at `h - k` writes the pairing as `∫ W·(halfIntegral - k)²`;
`variance_le_integral_sub_const_sq` drops the `k`; `integral_weight_ge` drops the weight to its
floor.

**⛔ IT IS NOT A NUMBER.** The right-hand side is still an integral, and a ratio needs a value.

What it removes is the dependence on `k`. `hfin` subtracts the state's mean and no lemma
identifies that constant, so a bound holding at every `k` is the shape that could be used —
**⛔ but no term in the tree connects this to `hfin`.**

DERIVED: the `2`s are the squares; the `0`s are the signs of `Ch`, `Cw` and `Wmin`; no other
numeral. -/
theorem pairing_ge_weight_min_mul_variance
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u)
    (hθST : ∀ i ∈ S, θ i ∈ T)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (hmS : ∀ v : (R → Ω), Measurable (fun u : (S → Ω) => h u v))
    (hmj : Measurable (fun q : ((S → Ω) × (R → Ω)) => h q.1 q.2))
    (Ch : ℝ) (hCh0 : 0 ≤ Ch) (hCh : ∀ u v, |h u v| ≤ Ch)
    (w : (R → Ω) → ℝ) (Cw : ℝ) (hCw0 : 0 ≤ Cw) (hCw : ∀ v, |w v| ≤ Cw)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hO : ∀ U, O U = h (fun i : S => U (i : ι)) (fun i : R => U (i : ι)))
    (W : (ι → Ω) → ℝ) (hWm : Measurable W)
    (hW : ∀ U, W U = w (fun i : R => U (i : ι)))
    {Wmin : ℝ} (hWmin0 : 0 ≤ Wmin) (hWmin : ∀ U, Wmin ≤ W U) (k : ℝ) :
    Wmin * ((∫ U, (halfIntegral μ S R hSR h U) ^ 2 ∂(cvol ι μ))
        - (∫ U, halfIntegral μ S R hSR h U ∂(cvol ι μ)) ^ 2)
      ≤ ∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ) := by
  classical
  have hmj' : Measurable (fun q : ((S → Ω) × (R → Ω)) => h q.1 q.2 - k) :=
    hmj.sub measurable_const
  have hCh' : ∀ u v, |h u v - k| ≤ Ch + |k| := by
    intro u v
    calc |h u v - k| ≤ |h u v| + |k| := abs_sub _ _
      _ ≤ Ch + |k| := by linarith [hCh u v]
  have hCh0' : (0 : ℝ) ≤ Ch + |k| := by linarith [abs_nonneg k]
  -- the pairing IS the weighted square of the shifted half-integral
  have hsq := pairing_eq_weighted_square μ S T R hST hSR hTR θ σ hσ hθR hσR hθST
    (fun u v => h u v - k) (fun v => (hmS v).sub measurable_const) hmj'
    (Ch + |k|) hCh0' hCh' w Cw hCw0 hCw
    (fun U => O U - k) (hOm.sub measurable_const) (fun U => by rw [hO U])
    W hWm hW
  -- and that half-integral is the original one shifted
  have hshift : ∀ U, halfIntegral μ S R hSR (fun u v => h u v - k) U
      = halfIntegral μ S R hSR h U - k :=
    fun U => halfIntegral_sub_const μ S R hSR h hmj hCh k U
  have hhm : Measurable (halfIntegral μ S R hSR h) := measurable_halfIntegral μ S R hSR h hmj
  have hhb : ∀ U, |halfIntegral μ S R hSR h U| ≤ Ch :=
    fun U => abs_halfIntegral_le μ S R hSR h hCh U
  have hgi : Integrable (halfIntegral μ S R hSR h) (cvol ι μ) :=
    integrable_of_bounded (cvol ι μ) hhm hhb
  have hg2i : Integrable (fun U => (halfIntegral μ S R hSR h U) ^ 2) (cvol ι μ) := by
    refine integrable_of_bounded (cvol ι μ) (hhm.pow_const 2) (C := Ch ^ 2) (fun U => ?_)
    rw [abs_pow]
    nlinarith [abs_nonneg (halfIntegral μ S R hSR h U), hhb U]
  have hqi : Integrable (fun U => (halfIntegral μ S R hSR h U - k) ^ 2) (cvol ι μ) := by
    refine integrable_of_bounded (cvol ι μ) ((hhm.sub measurable_const).pow_const 2)
      (C := (Ch + |k|) ^ 2) (fun U => ?_)
    have hb : |halfIntegral μ S R hSR h U - k| ≤ Ch + |k| := by
      calc |halfIntegral μ S R hSR h U - k| ≤ |halfIntegral μ S R hSR h U| + |k| := abs_sub _ _
        _ ≤ Ch + |k| := by linarith [hhb U]
    rw [abs_pow]
    nlinarith [abs_nonneg (halfIntegral μ S R hSR h U - k), hb]
  have hWqi : Integrable (fun U => W U * (halfIntegral μ S R hSR h U - k) ^ 2) (cvol ι μ) := by
    have := integrable_weighted_halfIntegral_sq μ S R hSR (fun u v => h u v - k) hmj' hCh'
      W hWm hCw0 (fun U => by rw [hW U]; exact hCw _)
    refine this.congr (Filter.Eventually.of_forall (fun U => ?_))
    simp only [hshift]
  -- assemble
  have hvar := variance_le_integral_sub_const_sq (cvol ι μ) (halfIntegral μ S R hSR h)
    hgi hg2i k
  have hstep1 : Wmin * ((∫ U, (halfIntegral μ S R hSR h U) ^ 2 ∂(cvol ι μ))
      - (∫ U, halfIntegral μ S R hSR h U ∂(cvol ι μ)) ^ 2)
      ≤ Wmin * ∫ U, (halfIntegral μ S R hSR h U - k) ^ 2 ∂(cvol ι μ) :=
    mul_le_mul_of_nonneg_left hvar hWmin0
  have hstep2 : Wmin * (∫ U, (halfIntegral μ S R hSR h U - k) ^ 2 ∂(cvol ι μ))
      ≤ ∫ U, W U * (halfIntegral μ S R hSR h U - k) ^ 2 ∂(cvol ι μ) :=
    integral_weight_ge (cvol ι μ) W _ hWmin (fun U => sq_nonneg _) hqi hWqi
  have hrhs : (∫ U, W U * (halfIntegral μ S R hSR h U - k) ^ 2 ∂(cvol ι μ))
      = ∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ) := by
    rw [hsq]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun U => ?_))
    simp only [hshift]
  linarith [hstep1, hstep2, hrhs.ge, hrhs.le]

#print axioms pairing_ge_weight_min_mul_variance

/-- **⭐⭐ EXACTLY WHEN THE REFLECTION PAIRING VANISHES.**

    INT W·O·(O∘Θ) = 0   ↔   W · (half-integral)² = 0 almost everywhere

`pairing_eq_weighted_square` is an EQUATION, so the pairing is an integral of a nonnegative function
the moment the weight is nonnegative, and a nonnegative integrand integrates to zero exactly when it
vanishes a.e. What enters beyond the identity is BOUNDEDNESS, which is what supplies the
integrability `integral_eq_zero_iff_of_nonneg` requires. There is no smallness, no condition on the
coupling and no topology on `Ω`.

**WHY THIS IS THE ONE WORTH HAVING.** `pairing_nonneg_of_shared_block` gives `0 ≤`. A ratio needs its
denominator bounded BELOW, and `0 ≤` does not bound anything below. This replaces the inequality by
an equivalence, so the denominator's vanishing becomes a checkable property of the observable rather
than an unknown.

**⛔ THE RIGHT-HAND SIDE IS NOT "`O` IS CONSTANT".** What it constrains is the CONDITIONAL
half-integral — `O` integrated over one side with the shared block held fixed — and not `O` itself.
No witness is recorded here for an `O` that varies while its half-integral vanishes;
`NegControl.coin_pairing_ne_sq` is NOT one, being a control on where the shared block sits (its
half-integral is `1/2`, not `0`).

**⛔ AND IT SAYS NOTHING ABOUT A LIMIT STATE.** This is one finite index set `ι` with the product
measure. Transporting it to the thermodynamic limit is a separate step and the tree does not take it
here.

DERIVED: the `0`s are the vanishing asserted on each side, the weight's sign in `hwnn`, and the
signs of the two bounding constants in `hCh0` and `hCw0`; the `2` is the square of
`pairing_eq_weighted_square`, as there. -/
theorem pairing_eq_zero_iff_halfIntegral
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u)
    (hθST : ∀ i ∈ S, θ i ∈ T)
    (h : (S → Ω) → (R → Ω) → ℝ) (hmS : ∀ v : (R → Ω), Measurable (fun u : (S → Ω) => h u v))
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    (Ch : ℝ) (hCh0 : 0 ≤ Ch) (hCh : ∀ u v, |h u v| ≤ Ch)
    (w : (R → Ω) → ℝ) (hwnn : ∀ v, 0 ≤ w v)
    (Cw : ℝ) (hCw0 : 0 ≤ Cw) (hCw : ∀ v, |w v| ≤ Cw)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hO : ∀ U, O U = h (fun i : S => U (i : ι)) (fun i : R => U (i : ι)))
    (W : (ι → Ω) → ℝ) (hWm : Measurable W)
    (hW : ∀ U, W U = w (fun i : R => U (i : ι))) :
    (∫ U, W U * O U * O (twist θ σ U) ∂(cvol ι μ)) = 0
      ↔ (fun U => W U * (halfIntegral μ S R hSR h U) ^ 2) =ᵐ[cvol ι μ] 0 := by
  have hWnn : ∀ U, 0 ≤ W U := fun U => by rw [hW]; exact hwnn _
  have hWb : ∀ U, |W U| ≤ Cw := fun U => by rw [hW]; exact hCw _
  have hnn : (0 : (ι → Ω) → ℝ) ≤ fun U => W U * (halfIntegral μ S R hSR h U) ^ 2 :=
    fun U => mul_nonneg (hWnn U) (sq_nonneg _)
  have hint := integrable_weighted_halfIntegral_sq μ S R hSR h hmj hCh W hWm hCw0 hWb
  rw [pairing_eq_weighted_square μ S T R hST hSR hTR θ σ hσ hθR hσR hθST h hmS hmj
    Ch hCh0 hCh w Cw hCw0 hCw O hOm hO W hWm hW]
  exact integral_eq_zero_iff_of_nonneg hnn hint

/-- **⭐⭐⭐ AND SO THE PAIRING IS STRICTLY POSITIVE**, given the one thing that can make it vanish.

This is the shape a ratio bound consumes: a lower bound on the DENOMINATOR, at a fixed finite index
set, on the hypotheses of `pairing_eq_weighted_square` plus the weight's nonnegativity and the
failure of the a.e. identity above. Those hypotheses include a UNIFORM BOUND on the observable,
which is a restriction on it and not bookkeeping.

**⛔ THE HYPOTHESIS IS NOT DISCHARGED HERE**, and it is NOT the same proposition as the
non-degeneracy guards on the GNS side. `TransferGap.gapAt_of_nondegenerate` guards on `0 < form x x`
and `WilsonTransferReduction.gapAt_of_subtracted_pairing_nondegenerate` on a pairing of the
MEAN-SUBTRACTED observable against a `DLRLimit.State`; `hne` has no subtraction, ranges over no
algebra, and lives on `cvol ι μ` at a finite index set. It plays the same ROLE and nothing in the
tree connects the two. What this theorem does is convert `hne` from a statement about an unknown
pairing into a statement about an explicit integrand; it does not supply it.

DERIVED: the `0`s are the vanishing denied, the positivity asserted, the weight's sign in `hwnn`,
and the signs of the two bounding constants in `hCh0` and `hCw0`; the `2` is the square of
`pairing_eq_weighted_square`, as there. -/
theorem pairing_pos_of_halfIntegral_ne
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u)
    (hθST : ∀ i ∈ S, θ i ∈ T)
    (h : (S → Ω) → (R → Ω) → ℝ) (hmS : ∀ v : (R → Ω), Measurable (fun u : (S → Ω) => h u v))
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    (Ch : ℝ) (hCh0 : 0 ≤ Ch) (hCh : ∀ u v, |h u v| ≤ Ch)
    (w : (R → Ω) → ℝ) (hwnn : ∀ v, 0 ≤ w v)
    (Cw : ℝ) (hCw0 : 0 ≤ Cw) (hCw : ∀ v, |w v| ≤ Cw)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hO : ∀ U, O U = h (fun i : S => U (i : ι)) (fun i : R => U (i : ι)))
    (W : (ι → Ω) → ℝ) (hWm : Measurable W)
    (hW : ∀ U, W U = w (fun i : R => U (i : ι)))
    (hne : ¬ ((fun U => W U * (halfIntegral μ S R hSR h U) ^ 2) =ᵐ[cvol ι μ] 0)) :
    0 < ∫ U, W U * O U * O (twist θ σ U) ∂(cvol ι μ) := by
  have hWnn : ∀ U, 0 ≤ W U := fun U => by rw [hW]; exact hwnn _
  have hnn : (0 : (ι → Ω) → ℝ) ≤ fun U => W U * (halfIntegral μ S R hSR h U) ^ 2 :=
    fun U => mul_nonneg (hWnn U) (sq_nonneg _)
  have hsq := pairing_eq_weighted_square μ S T R hST hSR hTR θ σ hσ hθR hσR hθST h hmS hmj
    Ch hCh0 hCh w Cw hCw0 hCw O hOm hO W hWm hW
  have hge : 0 ≤ ∫ U, W U * O U * O (twist θ σ U) ∂(cvol ι μ) := by
    rw [hsq]; exact integral_nonneg hnn
  refine lt_of_le_of_ne hge (fun h0 => hne ?_)
  exact (pairing_eq_zero_iff_halfIntegral μ S T R hST hSR hTR θ σ hσ hθR hσR hθST h hmS hmj
    Ch hCh0 hCh w hwnn Cw hCw0 hCw O hOm hO W hWm hW).mp h0.symm

end Weld

/-! ## The weld in the form a caller actually has it: LOCALITY instead of a factorisation

`pairing_nonneg_of_shared_block` asks for the observable already written as `h (U|S) (U|R)`. What a
caller has is the weaker and far more checkable statement that the observable READS only `S ∪ R` —
which on the Wilson lattice is `hol_congr_on_support` applied to a plaquette partition. `glue`
converts one into the other.
-/

section Localised

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Rebuild a configuration from its `S` and `R` parts, with a fixed base configuration elsewhere. -/
def glue (S R : Finset ι) (base : ι → Ω) (v : S → Ω) (w : R → Ω) : ι → Ω :=
  fun i => if hs : i ∈ S then v ⟨i, hs⟩ else if hr : i ∈ R then w ⟨i, hr⟩ else base i

theorem glue_agree_S (S R : Finset ι) (base : ι → Ω) (v : S → Ω) (w : R → Ω) {i : ι}
    (hi : i ∈ S) : glue S R base v w i = v ⟨i, hi⟩ := by
  simp only [glue, dif_pos hi]

theorem glue_agree_R (S R : Finset ι) (hSR : Disjoint S R) (base : ι → Ω) (v : S → Ω)
    (w : R → Ω) {i : ι} (hi : i ∈ R) : glue S R base v w i = w ⟨i, hi⟩ := by
  have hs : i ∉ S := fun hc => Finset.disjoint_left.mp hSR hc hi
  simp only [glue, dif_neg hs, dif_pos hi]

/-- **The `R`-restriction of a glue IS the `R`-part.** `glue_agree_R` pointwise, as a function.

DERIVED: no numeral. -/
theorem glue_restrict_R (S R : Finset ι) (hSR : Disjoint S R) (base : ι → Ω) (v : S → Ω)
    (w : R → Ω) : (fun i : R => glue S R base v w (i : ι)) = w := by
  funext i
  exact glue_agree_R S R hSR base v w i.2

#print axioms glue_restrict_R

/-- **`O` CANNOT SEE `base`.** Two glues differing only in `base` agree on `S` and on `R`, so a
reading hypothesis equates the observable on them. The `base` in `glue` is scaffolding: it fills the
coordinates the observable is blind to, and every VALUE built from it is independent of the filling,
not merely every vanishing.

DERIVED: no numeral. -/
theorem glue_base_congr (S R : Finset ι) (hSR : Disjoint S R) (b b' : ι → Ω)
    (O : (ι → Ω) → ℝ)
    (hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V)
    (v : S → Ω) (w : R → Ω) :
    O (glue S R b v w) = O (glue S R b' v w) :=
  hOloc _ _
    (fun i hi => by rw [glue_agree_S S R b v w hi, glue_agree_S S R b' v w hi])
    (fun i hi => by rw [glue_agree_R S R hSR b v w hi, glue_agree_R S R hSR b' v w hi])

/-- **`glue` is JOINTLY measurable**, which the square identity needs because it integrates over both
blocks. `measurable_glue_left` is the specialisation at a fixed `w`.

DERIVED: no numeral. -/
theorem measurable_glue (S R : Finset ι) (base : ι → Ω) :
    Measurable (fun q : ((S → Ω) × (R → Ω)) => glue S R base q.1 q.2) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases hs : i ∈ S
  · simp only [glue, dif_pos hs]
    exact (measurable_pi_apply _).comp measurable_fst
  · by_cases hr : i ∈ R
    · simp only [glue, dif_neg hs, dif_pos hr]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [glue, dif_neg hs, dif_neg hr]
      exact measurable_const

theorem measurable_glue_left (S R : Finset ι) (base : ι → Ω) (w : R → Ω) :
    Measurable (fun v : S → Ω => glue S R base v w) :=
  (measurable_glue S R base).comp (measurable_id.prodMk measurable_const)

/-- **Reflection positivity from LOCALITY.** `O` need only READ `S ∪ R` and `W` read `R`; the
factorised form the previous theorem wants is built here by `glue`.

This is the shape the Wilson lattice supplies: a plaquette partition plus
`ReflectionPositivity.hol_congr_on_support` gives exactly these two reading statements.

DERIVED: the `0`s are the nonnegativity asserted and the weight's sign in `hWnn`. -/
theorem pairing_nonneg_of_local
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u) (hθST : ∀ i ∈ S, θ i ∈ T)
    (base : ι → Ω)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V)
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (hWnn : ∀ U, 0 ≤ W U)
    (hWloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → W U = W V)
    (C : ℝ) (hC : ∀ U, |W U * O U * O (twist θ σ U)| ≤ C) :
    0 ≤ ∫ U, W U * O U * O (twist θ σ U) ∂(cvol ι μ) := by
  refine pairing_nonneg_of_shared_block μ S T R hST hSR hTR θ σ hσ hθR hσR hθST
    (fun v w => O (glue S R base v w))
    (fun w => hOm.comp (measurable_glue_left S R base w))
    (fun w => W (glue S R base (fun i : S => base (i : ι)) w))
    (fun w => hWnn _) O hOm ?_ W hWm ?_ C hC
  · intro U
    exact hOloc U _
      (fun i hi => (glue_agree_S S R base (fun i : S => U (i : ι))
        (fun i : R => U (i : ι)) hi).symm)
      (fun i hi => (glue_agree_R S R hSR base (fun i : S => U (i : ι))
        (fun i : R => U (i : ι)) hi).symm)
  · intro U
    exact hWloc U _
      (fun i hi => (glue_agree_R S R hSR base (fun i : S => base (i : ι))
        (fun i : R => U (i : ι)) hi).symm)


/-- **⭐⭐ EXACTLY WHEN THE PAIRING VANISHES, FROM LOCALITY.**

`pairing_nonneg_of_local` gives `0 ≤` from the reading statement a caller has;
`pairing_eq_zero_iff_halfIntegral` gives the EQUIVALENCE from a factorisation no caller of the
SHARED-BLOCK weld has. This is the equivalence from the reading statement, `glue` supplying the
factorisation exactly as there.

`base` APPEARS ON THE RIGHT AND CHANGES NOTHING: `glue_base_congr` shows `hOloc` makes the glued
observable's VALUE independent of it, not merely its vanishing.

**⛔ IT COSTS TWO BOUNDS WHERE `pairing_nonneg_of_local` COSTS ONE**, because the half-integral is
bounded before it is squared. That cost is nominal in this tree: both caller families —
`wilson_pairing_nonneg_even` and `ReflectionHalfSpace.irefl_box_wilson_pairing_nonneg` — already hold
separate bounds and CONSTRUCT the single product bound from them.

`ReflectionHalfSpace.irefl_box_pairing_eq_zero_iff` is the consumer: the same instantiation
`irefl_box_pairing_nonneg` makes, at the box's three blocks, with `base` the all-identity
configuration.

**⛔ THE WELD SIBLINGS STILL HAVE NONE.** `pairing_eq_zero_iff_halfIntegral` and
`pairing_pos_of_halfIntegral_ne` are reached only through this theorem. And a vanishing CRITERION is
not a lower BOUND: the shape `TransferGap.GapAt`'s denominator and row 13's null space want is a
proof that the half-integral does NOT vanish, which nothing supplies.

`pairing_pos_iff_half_ne_const` below is this theorem with a constant subtracted and the weight
strictly positive, stated as an equivalence. It adds `halfIntegral_sub_const` and the sign, and no
content beyond them — with `0 < W` its two sides are the same proposition.

DERIVED: the `0`s are the vanishing asserted on each side and the weight's sign in `hWnn`; the `2`
is the square, as in `pairing_eq_weighted_square`. The two bounding constants carry no sign
hypothesis — `base` is already a hypothesis, so `abs_nonneg` supplies it. -/
theorem pairing_eq_zero_iff_local
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u) (hθST : ∀ i ∈ S, θ i ∈ T)
    (base : ι → Ω)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (hWnn : ∀ U, 0 ≤ W U)
    (hWloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) :
    (∫ U, W U * O U * O (twist θ σ U) ∂(cvol ι μ)) = 0
      ↔ (fun U => W U
          * (halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U) ^ 2) =ᵐ[cvol ι μ] 0 := by
  refine pairing_eq_zero_iff_halfIntegral μ S T R hST hSR hTR θ σ hσ hθR hσR hθST
    (fun v w => O (glue S R base v w))
    (fun w => hOm.comp (measurable_glue_left S R base w))
    (hOm.comp (measurable_glue S R base))
    Ch (le_trans (abs_nonneg _) (hOb base)) (fun _ _ => hOb _)
    (fun w => W (glue S R base (fun i : S => base (i : ι)) w))
    (fun w => hWnn _) Cw (le_trans (abs_nonneg _) (hWb base)) (fun _ => hWb _)
    O hOm ?_ W hWm ?_
  · intro U
    exact hOloc U _
      (fun i hi => (glue_agree_S S R base (fun i : S => U (i : ι))
        (fun i : R => U (i : ι)) hi).symm)
      (fun i hi => (glue_agree_R S R hSR base (fun i : S => U (i : ι))
        (fun i : R => U (i : ι)) hi).symm)
  · intro U
    exact hWloc U _
      (fun i hi => (glue_agree_R S R hSR base (fun i : S => base (i : ι))
        (fun i : R => U (i : ι)) hi).symm)



/-- **⭐⭐ POSITIVITY OF THE CONSTANT-SUBTRACTED FORM, AS AN EQUIVALENCE.**

The form at `O - k` is positive exactly when `O`'s conditional half-integral is NOT almost everywhere
`k`.

**⛔ THE TWO SIDES ARE THE SAME PROPOSITION, AND THAT IS WHY THIS IS AN `↔`.**
`pairing_eq_zero_iff_local` is already an equivalence and assumes only `0 ≤ W`; with `0 < W` the
factor `W` drops out of `W·x² = 0`, so the right-hand side is the form's non-vanishing rewritten. No
difficulty is moved and none is removed. What is added over `pairing_eq_zero_iff_local` is exactly
`halfIntegral_sub_const` — the constant coming out — and the sign, which turns non-vanishing into
positivity.

**⛔ `k` IS NOT A MEAN.** It is a free real. At `O ≡ 5` and `k = 0` the right-hand side holds while
`O` is constant, so this is NOT the statement "the half-integral is non-constant", and the two are
incomparable rather than ordered. Only when `k` is `O`'s own conditional mean does the right-hand
side read "the half-integral is non-constant".

**⛔ AND IT IS NOT THE GNS NON-DEGENERACY.** `WilsonTransferReduction.gapAt_of_subtracted_pairing_nondegenerate`
guards a `DLRLimit.State` on `C(IConf G, ℝ)` at infinite volume with the subtracted constant pinned
to `ν F`. This is `cvol ι μ` at a finite index set, over no algebra, with `k` free. It plays the same
ROLE; nothing in the tree connects the two.

**HOW SUCH A HYPOTHESIS GETS DISCHARGED ELSEWHERE.** `HaarVariance.variance_pos_of_two_values` does
it with continuity, an open-positive measure and two values, and `PlaqVariance.wilsonCorrConn_self_pos`
is the Wilson instance. That route is NOT available here: `Ω` carries no topology in this section.

DERIVED: the `0`s are the positivity asserted, the weight's sign and the a.e. vanishing denied; the
`2` of the proof is the square, as in `pairing_eq_weighted_square`. -/
theorem pairing_pos_iff_half_ne_const
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u) (hθST : ∀ i ∈ S, θ i ∈ T)
    (base : ι → Ω)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (hWpos : ∀ U, 0 < W U)
    (hWloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) (k : ℝ) :
    0 < (∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ))
      ↔ ¬ ((fun U => halfIntegral μ S R hSR
          (fun v w => O (glue S R base v w)) U - k) =ᵐ[cvol ι μ] 0) := by
  classical
  have hCh0 : 0 ≤ Ch := le_trans (abs_nonneg _) (hOb base)
  have hCw0 : 0 ≤ Cw := le_trans (abs_nonneg _) (hWb base)
  have hWnn : ∀ U, 0 ≤ W U := fun U => (hWpos U).le
  set O' : (ι → Ω) → ℝ := fun U => O U - k with hO'
  have hO'm : Measurable O' := hOm.sub measurable_const
  have hO'loc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O' U = O' V :=
    fun U V h1 h2 => by simp only [hO']; rw [hOloc U V h1 h2]
  have hO'b : ∀ U, |O' U| ≤ Ch + |k| := by
    intro U
    simp only [hO']
    exact le_trans (abs_sub _ _) (add_le_add (hOb U) (le_refl _))
  have hCh0' : 0 ≤ Ch + |k| := add_nonneg hCh0 (abs_nonneg _)
  have hC : ∀ U, |W U * O' U * O' (twist θ σ U)| ≤ Cw * (Ch + |k|) * (Ch + |k|) := by
    intro U
    have e1 : |W U * O' U * O' (twist θ σ U)| = |W U| * |O' U| * |O' (twist θ σ U)| := by
      simp only [abs_mul]
    have h1 : |W U| * |O' U| ≤ Cw * (Ch + |k|) :=
      mul_le_mul (hWb U) (hO'b U) (abs_nonneg _) hCw0
    rw [e1]
    exact mul_le_mul h1 (hO'b _) (abs_nonneg _) (mul_nonneg hCw0 hCh0')
  have hnn := pairing_nonneg_of_local μ S T R hST hSR hTR θ σ hσ hθR hσR hθST base
    O' hO'm hO'loc W hWm hWnn hWloc (Cw * (Ch + |k|) * (Ch + |k|)) hC
  have hiff := pairing_eq_zero_iff_local μ S T R hST hSR hTR θ σ hσ hθR hσR hθST base
    O' hO'm hO'loc (Ch + |k|) hO'b W hWm hWnn hWloc Cw hWb
  have hsub : ∀ U, halfIntegral μ S R hSR (fun v w => O' (glue S R base v w)) U
      = halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U - k :=
    fun U => halfIntegral_sub_const μ S R hSR _ (hOm.comp (measurable_glue S R base))
      (fun _ _ => hOb _) k U
  constructor
  · intro hpos hcon
    have hz : (fun U => W U
        * (halfIntegral μ S R hSR (fun v w => O' (glue S R base v w)) U) ^ 2)
        =ᵐ[cvol ι μ] 0 := by
      filter_upwards [hcon] with U hU
      simp only [Pi.zero_apply] at hU ⊢
      rw [hsub U, hU]
      ring
    exact absurd (hiff.mpr hz) hpos.ne'
  · intro hne
    refine lt_of_le_of_ne hnn (fun h0 => hne ?_)
    have hae := hiff.mp h0.symm
    filter_upwards [hae] with U hU
    simp only [Pi.zero_apply, hsub U] at hU
    have hW0 : W U ≠ 0 := (hWpos U).ne'
    have hsq : (halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U - k) ^ 2 = 0 :=
      (mul_eq_zero.mp hU).resolve_left hW0
    simp only [Pi.zero_apply]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-- **⭐⭐ THE VARIANCE BOUND IN THE SHAPE A BOX CALLER HAS.**

`pairing_ge_weight_min_mul_variance` asks for a FACTORISATION of `O` and `W` through the blocks;
what a caller of the shared-block weld holds is the READING statement. `glue` supplies the
factorisation, exactly as in `pairing_nonneg_of_local`.

DERIVED: the `2`s are the squares; the `0` is `Wmin`'s sign; no other numeral. -/
theorem pairing_ge_variance_of_local
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u) (hθST : ∀ i ∈ S, θ i ∈ T)
    (base : ι → Ω)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (ι → Ω) → ℝ) (hWm : Measurable W)
    (hWloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw)
    {Wmin : ℝ} (hWmin0 : 0 ≤ Wmin) (hWmin : ∀ U, Wmin ≤ W U) (k : ℝ) :
    Wmin * ((∫ U, (halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U) ^ 2
          ∂(cvol ι μ))
        - (∫ U, halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U ∂(cvol ι μ)) ^ 2)
      ≤ ∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ) :=
  pairing_ge_weight_min_mul_variance μ S T R hST hSR hTR θ σ hσ hθR hσR hθST
    (fun v w => O (glue S R base v w))
    (fun w => hOm.comp (measurable_glue_left S R base w))
    (hOm.comp (measurable_glue S R base))
    Ch (le_trans (abs_nonneg _) (hOb base)) (fun _ _ => hOb _)
    (fun w => W (glue S R base (fun i : S => base (i : ι)) w))
    Cw (le_trans (abs_nonneg _) (hWb base)) (fun _ => hWb _)
    O hOm
    (fun U => hOloc U _
      (fun i hi => (glue_agree_S S R base (fun i : S => U (i : ι))
        (fun i : R => U (i : ι)) hi).symm)
      (fun i hi => (glue_agree_R S R hSR base (fun i : S => U (i : ι))
        (fun i : R => U (i : ι)) hi).symm))
    W hWm
    (fun U => hWloc U _
      (fun i hi => (glue_agree_R S R hSR base (fun i : S => base (i : ι))
        (fun i : R => U (i : ι)) hi).symm))
    hWmin0 hWmin k

#print axioms pairing_ge_variance_of_local

/-- **⭐⭐ AN OBSERVABLE THAT DOES NOT READ THE SHARED BLOCK HAS A CONSTANT HALF-INTEGRAL.**

`glue S R base v w` and `glue S R base v w'` agree on `S` whatever `w` and `w'` are, so an observable
blind to `R` cannot tell them apart and its conditional half-integral does not depend on the
configuration at all.

DERIVED: no numeral. -/
theorem halfIntegral_const_of_indep_R (S R : Finset ι) (hSR : Disjoint S R) (base : ι → Ω)
    (O : (ι → Ω) → ℝ)
    (hOS : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → O U = O V) (U U' : ι → Ω) :
    halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U
      = halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U' := by
  classical
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  exact hOS _ _ (fun i hi => by
    rw [glue_agree_S S R base _ _ hi, glue_agree_S S R base _ _ hi])

/-- **⭐⭐ AN OBSERVABLE THAT READS THE SHARED BLOCK ALONE IS ITS OWN HALF-INTEGRAL.**

The dual of the previous theorem. `glue S R base v w` agrees with the configuration on `R` whatever
`v` is, so an observable reading `R` alone does not depend on the integration variable, and against a
PROBABILITY measure the integral of a constant is that constant.

DERIVED: no numeral. -/
theorem halfIntegral_of_indep_S (S R : Finset ι) (hSR : Disjoint S R) (base : ι → Ω)
    (O : (ι → Ω) → ℝ)
    (hOR : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → O U = O V) (U : ι → Ω) :
    halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U = O U := by
  classical
  have hval : ∀ y : {i : ι // i ∉ R} → Ω,
      O (glue S R base (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
        (fun i : R => U (i : ι))) = O U := by
    intro y
    refine hOR _ _ (fun i hi => ?_)
    rw [glue_agree_R S R hSR base _ _ hi]
  show (∫ y, O (glue S R base (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
      (fun i : R => U (i : ι))) ∂(cvol {i : ι // i ∉ R} μ)) = O U
  rw [integral_congr_ae (Filter.Eventually.of_forall hval), integral_const]
  simp

#print axioms halfIntegral_of_indep_S

/-- **A reparametrisation that absorbs the configuration makes the half-integral constant.**

If the integrand is `g` composed with a measure-preserving map that may depend on `U`, the
half-integral equals `∫ g` for every `U`.

This is the abstract form of the Haar obstruction: a free `S`-coordinate entering the integrand only
through a group translation absorbs whatever the rest of the word contributes.

DERIVED: no numeral. -/
theorem halfIntegral_eq_integral_of_reparam (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (g : ({i : ι // i ∉ R} → Ω) → ℝ) (hg : Measurable g)
    (e : (ι → Ω) → (({i : ι // i ∉ R} → Ω) → ({i : ι // i ∉ R} → Ω)))
    (hmp : ∀ U, MeasurePreserving (e U) (cvol {i : ι // i ∉ R} μ) (cvol {i : ι // i ∉ R} μ))
    (hrep : ∀ (U : ι → Ω) (y : {i : ι // i ∉ R} → Ω),
      h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
        (fun i : R => U (i : ι)) = g (e U y))
    (U : ι → Ω) :
    halfIntegral μ S R hSR h U = ∫ y, g y ∂(cvol {i : ι // i ∉ R} μ) := by
  classical
  show (∫ y, h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
      (fun i : R => U (i : ι)) ∂(cvol {i : ι // i ∉ R} μ))
      = ∫ y, g y ∂(cvol {i : ι // i ∉ R} μ)
  rw [integral_congr_ae (Filter.Eventually.of_forall (hrep U))]
  have hmap := integral_map (μ := cvol {i : ι // i ∉ R} μ) (f := g)
    (hmp U).measurable.aemeasurable hg.aestronglyMeasurable
  rw [(hmp U).map_eq] at hmap
  exact hmap.symm

#print axioms halfIntegral_eq_integral_of_reparam

/-- **Hence such a half-integral takes ONE value**, so the two-values route cannot start from it.

DERIVED: no numeral. -/
theorem halfIntegral_const_of_reparam (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (g : ({i : ι // i ∉ R} → Ω) → ℝ) (hg : Measurable g)
    (e : (ι → Ω) → (({i : ι // i ∉ R} → Ω) → ({i : ι // i ∉ R} → Ω)))
    (hmp : ∀ U, MeasurePreserving (e U) (cvol {i : ι // i ∉ R} μ) (cvol {i : ι // i ∉ R} μ))
    (hrep : ∀ (U : ι → Ω) (y : {i : ι // i ∉ R} → Ω),
      h (fun i : S => y ⟨(i : ι), Finset.disjoint_left.mp hSR i.2⟩)
        (fun i : R => U (i : ι)) = g (e U y))
    (U U' : ι → Ω) :
    halfIntegral μ S R hSR h U = halfIntegral μ S R hSR h U' := by
  rw [halfIntegral_eq_integral_of_reparam μ S R hSR h g hg e hmp hrep U,
    halfIntegral_eq_integral_of_reparam μ S R hSR h g hg e hmp hrep U']

#print axioms halfIntegral_const_of_reparam

/-- **⭐⭐⭐ THE REFLECTION FORM ANNIHILATES EVERY MEAN-SUBTRACTED OBSERVABLE BLIND TO THE SHARED
BLOCK.**

Subtract from such an observable the value its half-integral constantly takes and the form is
exactly `0` — not bounded, not small, zero.

**THIS IS A DISCHARGE, NOT A RESTATEMENT.** Everything else in this family says the form vanishes
IF some condition holds. This computes the condition and finds it holds, for a class named by a
reading statement a caller can check.

**WHAT IT MEANS.** The even reflection form is degenerate precisely on the strictly-interior
observables, so whatever the GNS quotient sees must COUPLE TO THE SHARED BLOCK. That is the
transfer-matrix picture — the live observables sit on the time slice — and it is a term here rather
than folklore.

**⛔ AND IT DOES NOT SAY THE WILSON FORM IS DEGENERATE ON THE HALF-SPACE ALGEBRA.** `hOS` is about
the observable THIS theorem is applied to, and the Wilson instantiation applies it to the DRESSED
observable `ReflectionHalfSpace.idressed = F · e^{-βA₊}`, not to `F`. `ReflectionHalfSpace.idressed_depends_on_boxR` refutes `hOS` for the
dressed observable on a one-plaquette carrier at every `β ≠ 0`, with the bare observable CONSTANT.

**⛔ SO A BARE OBSERVABLE'S BLINDNESS TO `R` DOES NOT PUT IT IN THE WILSON FORM'S NULL SPACE.** That
carrier is not reflection-closed, so no particular box is settled either way.

**⛔ AND IT DOES NOT SAY THE FORM IS DEGENERATE ANYWHERE ELSE.** An observable that reads `R`
may or may not have a constant half-integral; this says nothing about it.

DERIVED: the `0` is the vanishing proved; the constant subtracted is the half-integral's own value,
evaluated at `base` because `halfIntegral_const_of_indep_R` makes the point irrelevant. -/
theorem pairing_eq_zero_of_indep_R
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u) (hθST : ∀ i ∈ S, θ i ∈ T)
    (base : ι → Ω)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hOS : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (hWnn : ∀ U, 0 ≤ W U)
    (hWloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) :
    (∫ U, W U
        * (O U - halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) base)
        * (O (twist θ σ U)
            - halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) base)
      ∂(cvol ι μ)) = 0 := by
  classical
  set k : ℝ := halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) base with hk
  have hCh0 : 0 ≤ Ch := le_trans (abs_nonneg _) (hOb base)
  set O' : (ι → Ω) → ℝ := fun U => O U - k with hO'
  have hO'm : Measurable O' := hOm.sub measurable_const
  have hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V :=
    fun U V h1 _ => hOS U V h1
  have hO'loc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O' U = O' V :=
    fun U V h1 h2 => by simp only [hO']; rw [hOloc U V h1 h2]
  have hO'b : ∀ U, |O' U| ≤ Ch + |k| := by
    intro U
    simp only [hO']
    exact le_trans (abs_sub _ _) (add_le_add (hOb U) (le_refl _))
  have hsub : ∀ U, halfIntegral μ S R hSR (fun v w => O' (glue S R base v w)) U
      = halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) U - k :=
    fun U => halfIntegral_sub_const μ S R hSR _ (hOm.comp (measurable_glue S R base))
      (fun _ _ => hOb _) k U
  refine (pairing_eq_zero_iff_local μ S T R hST hSR hTR θ σ hσ hθR hσR hθST base
    O' hO'm hO'loc (Ch + |k|) hO'b W hWm hWnn hWloc Cw hWb).mpr ?_
  refine Filter.Eventually.of_forall (fun U => ?_)
  simp only [Pi.zero_apply]
  rw [hsub U, halfIntegral_const_of_indep_R μ S R hSR base O hOS U base, ← hk, sub_self]
  ring

/-- **⭐⭐⭐ ON THE SHARED BLOCK, NON-DEGENERATE IS EXACTLY NON-CONSTANT.**

For an observable reading the shared block ALONE, `halfIntegral_of_indep_S` collapses
`pairing_pos_iff_half_ne_const` completely: no half-integral survives, and the form at `O - k` is
strictly positive exactly when `O` itself is not almost everywhere `k`.

**WHY THIS IS THE ONE WORTH HAVING.** Every other criterion in this family states non-degeneracy in
terms of a conditional integral, which is a thing one must compute. This states it in terms of the
observable, which is a thing one can EXHIBIT — and `Continuous.ae_eq_iff_eq` against an
open-positive measure turns "not a.e. `k`" into "takes two values", which is how
`HaarVariance.variance_pos_of_two_values` and `PlaqVariance.wilsonCorrConn_self_pos` discharge the
same shape elsewhere.

**⛔ IT IS THE OPPOSITE POLE FROM `pairing_eq_zero_of_indep_R`, NOT A GENERAL ANSWER.** That one has
the observable blind to `R` and the form vanishes; this one has it blind to `S` and the form is
positive iff non-constant. An observable reading BOTH blocks — which is what the Wilson instantiation
supplies, since the dressing `e^{-βA₊}` reads the shared block — is covered by neither, and that is
the case the mass gap is about.

DERIVED: the `0`s are the positivity asserted, the weight's sign and the a.e. vanishing denied. -/
theorem pairing_pos_iff_ne_const_of_indep_S
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u) (hθST : ∀ i ∈ S, θ i ∈ T)
    (base : ι → Ω)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hOR : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (hWpos : ∀ U, 0 < W U)
    (hWloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) (k : ℝ) :
    0 < (∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ))
      ↔ ¬ ((fun U => O U - k) =ᵐ[cvol ι μ] 0) := by
  classical
  have hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V :=
    fun U V _ h2 => hOR U V h2
  have hiff := pairing_pos_iff_half_ne_const μ S T R hST hSR hTR θ σ hσ hθR hσR hθST base
    O hOm hOloc Ch hOb W hWm hWpos hWloc Cw hWb k
  have hcol : (fun U => halfIntegral μ S R hSR
      (fun v w => O (glue S R base v w)) U - k) = fun U => O U - k := by
    funext U
    rw [halfIntegral_of_indep_S μ S R hSR base O hOR U]
  rwa [hcol] at hiff

end Localised

section WeldContinuity

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω] [FirstCountableTopology Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **The conditional half-integral is continuous**, for a jointly continuous bounded integrand.

`MeasureTheory.continuous_of_dominated` at `halfIntegral`: the integrand is continuous in the
configuration for each integration point, and bounded by a constant.

DERIVED: no numeral. -/
theorem continuous_halfIntegral (S R : Finset ι) (hSR : Disjoint S R)
    (h : (S → Ω) → (R → Ω) → ℝ)
    (hmj : Measurable (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    (hcj : Continuous (fun p : ((S → Ω) × (R → Ω)) => h p.1 p.2))
    {Ch : ℝ} (hCh : ∀ u v, |h u v| ≤ Ch) :
    Continuous (halfIntegral μ S R hSR h) := by
  classical
  have hSoff : ∀ i : S, ((i : ι) ∉ R) := fun i => Finset.disjoint_left.mp hSR i.2
  have hrest : Measurable (fun (y : {i : ι // i ∉ R} → Ω) (i : S) => y ⟨(i : ι), hSoff i⟩) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hresR : Continuous (fun (U : ι → Ω) (i : R) => U (i : ι)) :=
    continuous_pi (fun i => continuous_apply _)
  have hms : ∀ U : ι → Ω, AEStronglyMeasurable
      (fun y : {i : ι // i ∉ R} → Ω =>
        h (fun i : S => y ⟨(i : ι), hSoff i⟩) (fun i : R => U (i : ι)))
      (cvol {i : ι // i ∉ R} μ) :=
    fun U => (hmj.comp (hrest.prodMk measurable_const)).aestronglyMeasurable
  have hbd : ∀ U : ι → Ω, ∀ᵐ y ∂(cvol {i : ι // i ∉ R} μ),
      ‖h (fun i : S => y ⟨(i : ι), hSoff i⟩) (fun i : R => U (i : ι))‖ ≤ Ch := by
    intro U
    refine Filter.Eventually.of_forall (fun y => ?_)
    simpa [Real.norm_eq_abs] using hCh _ _
  have hct : ∀ᵐ y ∂(cvol {i : ι // i ∉ R} μ),
      Continuous (fun U : ι → Ω =>
        h (fun i : S => y ⟨(i : ι), hSoff i⟩) (fun i : R => U (i : ι))) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    exact hcj.comp (continuous_const.prodMk hresR)
  exact continuous_of_dominated hms hbd (integrable_const _) hct

#print axioms continuous_halfIntegral

/-- **`glue` is JOINTLY CONTINUOUS.** The twin of `measurable_glue`.

`pairing_pos_of_half_two_values`'s `hcj` is continuity of the GLUED observable, so continuity of the
observable alone does not reach it.

DERIVED: no numeral. -/
theorem continuous_glue (S R : Finset ι) (base : ι → Ω) :
    Continuous (fun q : ((S → Ω) × (R → Ω)) => glue S R base q.1 q.2) := by
  refine continuous_pi (fun i => ?_)
  by_cases hs : i ∈ S
  · simp only [glue, dif_pos hs]
    exact (continuous_apply _).comp continuous_fst
  · by_cases hr : i ∈ R
    · simp only [glue, dif_neg hs, dif_pos hr]
      exact (continuous_apply _).comp continuous_snd
    · simp only [glue, dif_neg hs, dif_neg hr]
      exact continuous_const

#print axioms continuous_glue

/-- **A continuous function taking two values is not a.e. constant**, against an open-positive
measure.

DERIVED: the `0` is the a.e. vanishing denied. -/
theorem not_ae_eq_const_of_two_values {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (ν : Measure X) [ν.IsOpenPosMeasure] {f : X → ℝ} (hf : Continuous f) (k : ℝ)
    {a b : X} (hab : f a ≠ f b) :
    ¬ ((fun x => f x - k) =ᵐ[ν] 0) := by
  intro hae
  have h1 : f =ᵐ[ν] (fun _ => k) := by
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  have h2 : f = fun _ => k := (Continuous.ae_eq_iff_eq ν hf continuous_const).mp h1
  exact hab (by rw [h2])

#print axioms not_ae_eq_const_of_two_values


/-- **⭐⭐⭐ TWO VALUES OF THE HALF-INTEGRAL MAKE THE FORM POSITIVE.**

`pairing_pos_iff_half_ne_const` with its a.e. hypothesis discharged by `continuous_halfIntegral` and
`not_ae_eq_const_of_two_values`.

DERIVED: the `0`s are the positivity asserted and the weight's sign. -/
theorem pairing_pos_of_half_two_values
    [(cvol ι μ).IsOpenPosMeasure]
    (S T R : Finset ι) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (θ : Equiv.Perm ι) (σ : ι → Ω → Ω) (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hθR : ∀ i ∈ R, θ i = i) (hσR : ∀ i ∈ R, ∀ u, σ i u = u) (hθST : ∀ i ∈ S, θ i ∈ T)
    (base : ι → Ω)
    (O : (ι → Ω) → ℝ) (hOm : Measurable O)
    (hOloc : ∀ U V : ι → Ω, (∀ i ∈ S, U i = V i) → (∀ i ∈ R, U i = V i) → O U = O V)
    (Ch : ℝ) (hOb : ∀ U, |O U| ≤ Ch)
    (hcj : Continuous (fun q : ((S → Ω) × (R → Ω)) => O (glue S R base q.1 q.2)))
    (W : (ι → Ω) → ℝ) (hWm : Measurable W) (hWpos : ∀ U, 0 < W U)
    (hWloc : ∀ U V : ι → Ω, (∀ i ∈ R, U i = V i) → W U = W V)
    (Cw : ℝ) (hWb : ∀ U, |W U| ≤ Cw) (k : ℝ)
    {a b : ι → Ω}
    (hab : halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) a
        ≠ halfIntegral μ S R hSR (fun v w => O (glue S R base v w)) b) :
    0 < ∫ U, W U * (O U - k) * (O (twist θ σ U) - k) ∂(cvol ι μ) := by
  refine (pairing_pos_iff_half_ne_const μ S T R hST hSR hTR θ σ hσ hθR hσR hθST base
    O hOm hOloc Ch hOb W hWm hWpos hWloc Cw hWb k).mpr ?_
  exact not_ae_eq_const_of_two_values (cvol ι μ)
    (continuous_halfIntegral μ S R hSR (fun v w => O (glue S R base v w))
      (hOm.comp (measurable_glue S R base)) hcj (fun _ _ => hOb _)) k hab

#print axioms pairing_pos_of_half_two_values

end WeldContinuity

/-! ## NEGATIVE CONTROL: the shared block may not move inside the square -/

namespace NegControl

/-- A fair coin. Two points is the smallest space on which a function is not almost surely
constant, which is exactly what the two-block identity needs the shared block not to be.

DERIVED: a fair coin: `1/2` on each of the two outcomes, and `2` is the number of outcomes. The control needs only that the measure is not a point mass; equal weights are the simplest such choice and make the arithmetic `1/2` against `1/4` exact rather than approximate. -/
noncomputable def coin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

-- DERIVED: `1` is the total mass a probability measure has by definition; the two halves of `coin`
-- sum to it. Nothing here is chosen.
instance : IsProbabilityMeasure coin := by
  refine ⟨?_⟩
  simp only [coin, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  exact ENNReal.add_halves 1

-- DERIVED: `1/2` is the coin's own weight and `2` its outcome count.
instance halfDirac_finite (b : Bool) :
    IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac b) := by
  refine ⟨?_⟩
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.div_lt_top (by simp) (by simp)

theorem integral_coin (f : Bool → ℝ) : (∫ b, f b ∂coin) = (f true + f false) / 2 := by
  have h2 : ((1 / 2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by simp
  rw [coin, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac, h2,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The observable: read the single coordinate, which is ENTIRELY inside the shared block.

DERIVED: the indicator of one outcome: `1` and `0` are its values, which is what makes the pairing `1/2` and the square of the mean `1/4`. -/
noncomputable def gCoin (U : Fin 1 → Bool) : ℝ := if U default then 1 else 0

theorem integral_gCoin : (∫ U, gCoin U ∂(cvol (Fin 1) coin)) = 1 / 2 := by
  have h := (measurePreserving_funUnique coin (Fin 1)).integral_comp'
    (fun b : Bool => if b then (1 : ℝ) else 0)
  calc (∫ U, gCoin U ∂(cvol (Fin 1) coin))
      = ∫ b, (if b then (1 : ℝ) else 0) ∂coin := h
    _ = 1 / 2 := by rw [integral_coin]; norm_num

/-- **The TRUE value of the pairing**: the shared block integrated outside the square gives `1/2`. -/
theorem integral_gCoin_sq : (∫ U, gCoin U * gCoin U ∂(cvol (Fin 1) coin)) = 1 / 2 := by
  have h := (measurePreserving_funUnique coin (Fin 1)).integral_comp'
    (fun b : Bool => (if b then (1 : ℝ) else 0) * (if b then (1 : ℝ) else 0))
  calc (∫ U, gCoin U * gCoin U ∂(cvol (Fin 1) coin))
      = ∫ b, (if b then (1 : ℝ) else 0) * (if b then (1 : ℝ) else 0) ∂coin := h
    _ = 1 / 2 := by rw [integral_coin]; norm_num

/-- **NEGATIVE CONTROL.** The pairing of an observable with its own reflection is NOT the square of
its integral when the two halves share a coordinate: `1/2 ≠ 1/4`. -/
theorem coin_pairing_ne_sq :
    (∫ U, gCoin U * gCoin U ∂(cvol (Fin 1) coin))
      ≠ (∫ U, gCoin U ∂(cvol (Fin 1) coin)) ^ 2 := by
  rw [integral_gCoin, integral_gCoin_sq]; norm_num

/-- **NEGATIVE CONTROL, as a refutation.** `pairing_with_reflection_nonneg`'s conclusion
`∫ h·(h∘θ) = (∫h)²` is FALSE if the positive half is allowed to contain the shared block — take the
reflection to be the identity on it. So the `Disjoint S T` hypothesis is load-bearing, and the
conditional form of `pairing_nonneg_of_shared_block` is not a stylistic variant of it. -/
theorem shared_block_inside_square_false :
    ¬ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ι : Type) [Fintype ι] (O : (ι → Ω) → ℝ),
        (∫ U, O U * O U ∂(cvol ι μ)) = (∫ U, O U ∂(cvol ι μ)) ^ 2 :=
  fun hall => coin_pairing_ne_sq (hall Bool coin (Fin 1) gCoin)

end NegControl

/-! ## Where the reflection plane is: the parity of the fixed set -/

/-- `a % n` and `a` have the same parity when `n` is even. -/
theorem even_mod_iff_even {n a : ℕ} (hn : Even n) : Even (a % n) ↔ Even a := by
  have hm : Even (n * (a / n)) := hn.mul_right _
  constructor
  · intro hmod
    have hsum : Even (n * (a / n) + a % n) := hm.add hmod
    rwa [Nat.div_add_mod] at hsum
  · intro ha
    rw [← Nat.div_add_mod a n] at ha
    exact (Nat.even_add.mp ha).mp hm

/-- **Addition on `Fin n` is parity-additive exactly when the extent is even** — the reason the three
cases below are three and not one. -/
theorem fin_even_add {n : ℕ} [NeZero n] (hn : Even n) (a b : Fin n) :
    Even (a + b).val ↔ (Even a.val ↔ Even b.val) := by
  rw [Fin.val_add, even_mod_iff_even hn, Nat.even_add]

/-- On an even extent `x + x` is always even, so nothing with odd value is a half. -/
theorem no_half_of_odd_val {n : ℕ} [NeZero n] (hn : Even n) {b : Fin n} (hb : ¬ Even b.val)
    (x : Fin n) : x + x ≠ b := fun hx => hb (hx ▸ (fin_even_add hn x x).mpr Iff.rfl)

/-- On an even extent, `c` and `c − 1` have opposite parity: the site-plane condition `2x = c` and
the axis-link condition `2x = c − 1` can never both be solvable. -/
theorem sub_one_odd_of_even {n : ℕ} [NeZero n] (hn : Even n) (h2 : 2 ≤ n) {c : Fin n}
    (hc : Even c.val) : ¬ Even (c - 1 : Fin n).val := by
  intro hodd
  have hone : ¬ Even (1 : Fin n).val := by
    have : (1 : Fin n).val = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt h2
    rw [this]; decide
  have hiff : ¬ (Even (c - 1 : Fin n).val ↔ Even (1 : Fin n).val) := fun hi => hone (hi.mp hodd)
  have hno : ¬ Even (((c - 1) + 1 : Fin n)).val := fun hE => hiff ((fin_even_add hn (c - 1) 1).mp hE)
  have hcc : ((c - 1) + 1 : Fin n) = c := by simp
  rw [hcc] at hno
  exact hno hc

/-- An element whose value is even has a half — this is what makes the site-plane nonempty. -/
theorem exists_fixed_site {n : ℕ} [NeZero n] {c : Fin n} (hc : Even c.val) :
    ∃ x : Fin n, x + x = c := by
  obtain ⟨k, hk⟩ := hc
  have hkn : k < n := by have := c.isLt; omega
  refine ⟨⟨k, hkn⟩, ?_⟩
  apply Fin.ext
  rw [Fin.val_add]
  show (k + k) % n = c.val
  rw [← hk]
  exact Nat.mod_eq_of_lt c.isLt

/-! ### The fixed set of the reflection, on sites and on links -/

variable {d n : ℕ}

/-- **A site is fixed exactly when `2 x_τ = c`.** The reflection plane sits at `c/2`, which is a site
only when `c` has a half in `Fin n`. -/
theorem reflSite_fixed_iff [NeZero n] (τ : Fin d) (c : Fin n) (x : Site d n) :
    reflSite τ c x = x ↔ c = x τ + x τ := by
  constructor
  · intro hx
    have h1 := congrFun hx τ
    rw [reflSite_axis] at h1
    exact sub_eq_iff_eq_add.mp h1
  · intro hc
    funext j
    by_cases hj : j = τ
    · subst hj
      rw [reflSite_axis]
      exact sub_eq_iff_eq_add.mpr hc
    · exact reflSite_of_ne hj c x

/-- **A TRANSVERSE link is fixed exactly when `2 x_τ = c`** — it sits in the site-plane, and the
reflection neither moves it nor (in `reflConf`) inverts it. These are the links of the shared block
in the case the weld covers. -/
theorem reflLink_fixed_iff_transverse [NeZero n] {τ : Fin d} (c : Fin n)
    (l : Link d n) (hl : l.1 ≠ τ) : reflLink τ c l = l ↔ c = l.2 τ + l.2 τ := by
  constructor
  · intro hx
    have h1 : (reflLink τ c l).2 = reflSite τ c l.2 := by simp [reflLink, hl]
    have h2 : (reflLink τ c l).2 = l.2 := congrArg Prod.snd hx
    rw [h1] at h2
    exact (reflSite_fixed_iff τ c l.2).mp h2
  · intro hc
    show (l.1, if l.1 = τ then reflSite τ (c - 1) l.2 else reflSite τ c l.2) = l
    rw [if_neg hl, (reflSite_fixed_iff τ c l.2).mpr hc]

/-- **An AXIS link is fixed exactly when `2 x_τ = c − 1`** — its MIDPOINT is the plane. `reflConf`
INVERTS such a link, so it is a shared coordinate the reflection acts on nontrivially, and the
conditional argument of `pairing_nonneg_of_shared_block` does not apply to it. -/
theorem reflLink_fixed_iff_axis [NeZero n] {τ : Fin d} (c : Fin n)
    (l : Link d n) (hl : l.1 = τ) : reflLink τ c l = l ↔ c - 1 = l.2 τ + l.2 τ := by
  constructor
  · intro hx
    have h1 : (reflLink τ c l).2 = reflSite τ (c - 1) l.2 := by simp [reflLink, hl]
    have h2 : (reflLink τ c l).2 = l.2 := congrArg Prod.snd hx
    rw [h1] at h2
    exact (reflSite_fixed_iff τ (c - 1) l.2).mp h2
  · intro hc
    show (l.1, if l.1 = τ then reflSite τ (c - 1) l.2 else reflSite τ c l.2) = l
    rw [if_pos hl, (reflSite_fixed_iff τ (c - 1) l.2).mpr hc]

/-- **CASE 1 — even extent, even constant: NO axis link is fixed.** The shared block is made of
transverse links only, `reflLink` fixes each of them and `reflConf` does not invert them, so `hθR`
and `hσR` of the weld both hold. -/
theorem no_fixed_axis_link [NeZero n] (hn : Even n) (h2 : 2 ≤ n) {τ : Fin d} {c : Fin n}
    (hc : Even c.val) (l : Link d n) (hl : l.1 = τ) : reflLink τ c l ≠ l := fun hx =>
  no_half_of_odd_val hn (sub_one_odd_of_even hn h2 hc) (l.2 τ)
    ((reflLink_fixed_iff_axis c l hl).mp hx).symm

/-- **The shared block is genuinely nonempty in that case.** There is a fixed site, and every
transverse link based there is fixed. -/
theorem exists_fixed_transverse_link [NeZero n] {τ ν : Fin d} (hν : ν ≠ τ)
    {c : Fin n} (hc : Even c.val) :
    ∃ l : Link d n, l.1 = ν ∧ reflLink τ c l = l := by
  obtain ⟨x, hx⟩ := exists_fixed_site hc
  refine ⟨(ν, Function.update (fun _ => 0) τ x), rfl, ?_⟩
  refine (reflLink_fixed_iff_transverse c _ hν).mpr ?_
  simpa using hx.symm

/-! ### CASE 3 — the pinned extent is ODD, and then every constant has a cross term

`Complete.wilsonCorr` runs the lag over `Fin (nCorrYM + 1)` and `nCorrYM = 16`, so the reflection
acts on `Fin 17`. Two is a unit there, so `2x = c` and `2x = c − 1` are BOTH solvable, for every `c`:
one site-plane and one link-plane. The link-plane is the cross term. -/

/-- Every reflection constant on the pinned extent has a half: a fixed SITE-plane always exists. -/
theorem pinned_exists_half : ∀ c : Fin 17, ∃ x : Fin 17, x + x = c := by decide

/-- Every reflection constant on the pinned extent ALSO fixes an axis-link midpoint. -/
theorem pinned_exists_half_sub_one : ∀ c : Fin 17, ∃ x : Fin 17, x + x = c - 1 := by decide

/-- And both are unique — one site-plane and one link-plane, never two. -/
theorem pinned_half_unique : ∀ c x y : Fin 17, x + x = c → y + y = c → x = y := by decide

/-- **The pinned case is not covered.** At `n = 17` every reflection constant fixes an AXIS link,
which `reflConf` inverts; the plaquettes through it are read by both halves. That is the cross term
`ReflectionPositivity.reflection_positive_of_expansion` is waiting for. -/
theorem exists_fixed_axis_link_pinned {d : ℕ} (τ : Fin d) (c : Fin 17) :
    ∃ l : Link d 17, l.1 = τ ∧ reflLink τ c l = l := by
  obtain ⟨x, hx⟩ := pinned_exists_half_sub_one c
  refine ⟨(τ, Function.update (fun _ => 0) τ x), rfl, ?_⟩
  refine (reflLink_fixed_iff_axis c _ rfl).mpr ?_
  simpa using hx.symm

/-! ## The weld, on the Wilson lattice -/

section Wilson

variable {N : ℕ}

/-- The coordinate twist of the Osterwalder–Seiler reflection: invert on axis links, leave the rest
alone. This is `Reflect.daggerAxis` read one coordinate at a time. -/
def axisDagger (τ : Fin d) : Link d n → MassGap.SUN.SU N → MassGap.SUN.SU N :=
  fun l u => if l.1 = τ then u⁻¹ else u

/-- **`reflConf` IS a twist** — definitionally. -/
theorem reflConf_eq_twist [NeZero n] (τ : Fin d) (c : Fin n)
    (U : Link d n → MassGap.SUN.SU N) :
    reflConf τ c U = twist (reflLinkPerm τ c) (axisDagger (N := N) τ) U := rfl

theorem axisDagger_measurePreserving (τ : Fin d) (l : Link d n) :
    MeasurePreserving (axisDagger (n := n) (N := N) τ l) (probHaar (MassGap.SUN.SU N))
      (probHaar (MassGap.SUN.SU N)) := by
  by_cases h : l.1 = τ
  · have hinv : axisDagger (n := n) (N := N) τ l = fun u => u⁻¹ := by
      funext u; simp [axisDagger, h]
    rw [hinv]
    exact Measure.measurePreserving_inv (probHaar (MassGap.SUN.SU N))
  · have hid : axisDagger (n := n) (N := N) τ l = id := by funext u; simp [axisDagger, h]
    rw [hid]
    exact MeasurePreserving.id _

/-- **Exactly what blocks the odd extent.** A fixed AXIS link is a coordinate BOTH halves read, and
`reflConf` does not fix it — it INVERTS it. So `hσR` of `pairing_nonneg_of_shared_block` is false at
that coordinate, and there is nothing to condition on: the two factors of the would-be square are
functions of `u` and of `u⁻¹`, not the same function twice.

Together with `exists_fixed_axis_link_pinned` this is the precise reason the pinned extent is not
covered. -/
theorem reflConf_inverts_fixed_axis_link [NeZero n] {τ : Fin d} {c : Fin n} (l : Link d n)
    (hl : l.1 = τ) (hfix : reflLink τ c l = l) (U : Link d n → MassGap.SUN.SU N) :
    reflConf τ c U l = (U l)⁻¹ := by
  show (if l.1 = τ then (U (reflLink τ c l))⁻¹ else U (reflLink τ c l)) = (U l)⁻¹
  rw [if_pos hl, hfix]

/-- **THE WELD, ON THE WILSON LATTICE.**

`S` is one side of the reflection plane, `T` its mirror, `R` the links IN the plane. The three
geometric hypotheses are exactly what the parity analysis above supplies in the even/even case:
`reflLink` fixes every link of `R` (`hR`), none of them runs along the axis so `reflConf` does not
invert them (`hRτ`), and the reflection carries `S` into `T` (`hSmap`).

`O` is any observable reading `S ∪ R`, `W` any nonnegative weight reading `R` — the plane's own share
of the Boltzmann weight. The conclusion is the Osterwalder–Seiler pairing inequality for that pair.

What is NOT supplied here is the Wilson weight IN this form. That needs every plaquette to read
`S ∪ R`, `T ∪ R` or `R` alone, which fails as soon as an axis link is fixed —
`exists_fixed_axis_link_pinned` shows that happens at the pinned extent for every constant. -/
theorem wilson_pairing_nonneg_of_shared_block [NeZero n] (τ : Fin d) (c : Fin n)
    (S T R : Finset (Link d n)) (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    (hR : ∀ l ∈ R, reflLink τ c l = l) (hRτ : ∀ l ∈ R, l.1 ≠ τ)
    (hSmap : ∀ l ∈ S, reflLink τ c l ∈ T)
    (h : (S → MassGap.SUN.SU N) → (R → MassGap.SUN.SU N) → ℝ)
    (hmS : ∀ v, Measurable (fun u => h u v))
    (w : (R → MassGap.SUN.SU N) → ℝ) (hw : ∀ v, 0 ≤ w v)
    (O : (Link d n → MassGap.SUN.SU N) → ℝ) (hOm : Measurable O)
    (hO : ∀ U, O U = h (fun i : S => U (i : Link d n)) (fun i : R => U (i : Link d n)))
    (W : (Link d n → MassGap.SUN.SU N) → ℝ) (hWm : Measurable W)
    (hW : ∀ U, W U = w (fun i : R => U (i : Link d n)))
    (C : ℝ) (hC : ∀ U, |W U * O U * O (reflConf τ c U)| ≤ C) :
    0 ≤ ∫ U, W U * O U * O (reflConf τ c U) ∂(vol (Link d n) N) :=
  pairing_nonneg_of_shared_block (probHaar (MassGap.SUN.SU N)) S T R hST hSR hTR
    (reflLinkPerm τ c) (axisDagger (N := N) τ)
    (fun l => axisDagger_measurePreserving τ l)
    (fun l hl => hR l hl)
    (fun l hl u => by simp [axisDagger, hRτ l hl])
    (fun l hl => hSmap l hl)
    h hmS w hw O hOm hO W hWm hW C (fun U => hC U)

end Wilson

/-! ## Choosing an aperture with EVEN extent

`Complete.confinement_of_bounded_substrate` concludes `∀ᶠ N in atTop, …`, and `WilsonModel.apertureOf`
picks a witness from it. An `∀ᶠ … atTop` set is cofinal, and so is the set of `N` with `N + 1` even, so
the two meet: the aperture may be chosen with EVEN extent without changing any constant and without
weakening the eventual statement. That lands in the favourable reflection case below.

`Filter.Eventually.and` cannot do this — `not_eventually_even_succ` shows the even-extent set is not
eventually true — and mere nonemptiness of the second set is not enough either
(`frequently_is_load_bearing`). Frequency is exactly the right hypothesis.
-/

/-- **An eventually-true property meets a frequently-true one.** Stated for an arbitrary filter so it
can be reused wherever a witness has to satisfy a cofinal side condition. -/
theorem exists_of_eventually_of_frequently {α : Type} {f : Filter α} {P Q : α → Prop}
    (hP : ∀ᶠ x in f, P x) (hQ : ∃ᶠ x in f, Q x) : ∃ x, P x ∧ Q x :=
  (hP.and_frequently hQ).exists

/-- The odd naturals are cofinal in `ℕ`, so the EVEN extents `N + 1` are frequently reached. -/
theorem frequently_even_succ : ∃ᶠ N in Filter.atTop, Even (N + 1) := by
  rw [Filter.frequently_atTop]
  intro a
  exact ⟨2 * a + 1, by omega, ⟨a + 1, by omega⟩⟩

/-- **The aperture may be taken with EVEN extent.** -/
theorem exists_even_extent_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ N in Filter.atTop, P N) : ∃ N, P N ∧ Even (N + 1) :=
  exists_of_eventually_of_frequently hP frequently_even_succ

/-- The same, in the shape the lattice geometry consumes: extent `N + 1 = 2 * m`. -/
theorem exists_even_extent_aperture {P : ℕ → Prop}
    (hP : ∀ᶠ N in Filter.atTop, P N) : ∃ N m, P N ∧ N + 1 = 2 * m := by
  obtain ⟨N, hPN, r, hr⟩ := exists_even_extent_of_eventually hP
  exact ⟨N, r, hPN, by omega⟩

/-- **NEGATIVE CONTROL.** `Filter.Eventually.and` cannot produce the even extent: the even-extent set
is NOT eventually true, only frequently. Reaching for `and` instead of `and_frequently` would have
been a false step, and this is the theorem that says so. -/
theorem not_eventually_even_succ : ¬ (∀ᶠ N in Filter.atTop, Even (N + 1)) := by
  rw [Filter.eventually_atTop]
  rintro ⟨a, ha⟩
  obtain ⟨r, hr⟩ := ha (2 * a) (by omega)
  omega

/-- **NEGATIVE CONTROL.** Frequency is load-bearing in the other direction too: a merely NONEMPTY
second set does not meet an eventual one. Here `P N := 3 ≤ N` is eventually true, `Q N := N < 3` is
nonempty, and no `N` satisfies both. -/
theorem frequently_is_load_bearing :
    ¬ (∀ {P Q : ℕ → Prop}, (∀ᶠ N in Filter.atTop, P N) → (∃ N, Q N) → ∃ N, P N ∧ Q N) := by
  intro hall
  obtain ⟨N, hN3, hN⟩ := hall (P := fun N => 3 ≤ N) (Q := fun N => N < 3)
    (Filter.eventually_atTop.mpr ⟨3, fun b hb => hb⟩) ⟨0, by norm_num⟩
  omega

/-! ## Levels above the reflection plane

Everything about the three blocks is a statement about ONE natural number per link: how far its
`τ`-coordinate sits above the plane. Working with `ℕ`-casts into `Fin n` rather than with `Fin.val`
of negatives keeps the arithmetic inside `Nat.cast` homomorphism lemmas and `omega`.
-/

/-- The `Fin n` representative of a natural number. Written out rather than relying on a `Nat.cast`
coercion so that every step below is `Nat.mod` arithmetic that `omega` can see. -/
def fcast (n : ℕ) [NeZero n] (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩

@[simp] theorem fcast_val {n : ℕ} [NeZero n] (x : Fin n) : fcast n x.val = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem val_fcast_of_lt {n : ℕ} [NeZero n] {j : ℕ} (hj : j < n) : (fcast n j).val = j :=
  Nat.mod_eq_of_lt hj

theorem fcast_add {n : ℕ} [NeZero n] (i j : ℕ) : fcast n i + fcast n j = fcast n (i + j) :=
  Fin.ext (by
    show (i % n + j % n) % n = (i + j) % n
    exact (Nat.add_mod i j n).symm)

theorem fcast_self {n : ℕ} [NeZero n] : fcast n n = 0 :=
  Fin.ext (by
    show n % n = (0 : Fin n).val
    rw [Nat.mod_self]
    exact (Fin.val_eq_zero_iff.mpr rfl).symm)

theorem fcast_one {n : ℕ} [NeZero n] : fcast n 1 = 1 :=
  Fin.ext (by
    show 1 % n = (1 : Fin n).val
    rw [Fin.val_one'])

theorem fcast_zero {n : ℕ} [NeZero n] : fcast n 0 = 0 :=
  Fin.ext (by
    show 0 % n = (0 : Fin n).val
    rw [Nat.zero_mod]
    exact (Fin.val_eq_zero_iff.mpr rfl).symm)

theorem fcast_mod {n : ℕ} [NeZero n] (j : ℕ) : fcast n (j % n) = fcast n j :=
  Fin.ext (Nat.mod_eq_of_lt (Nat.mod_lt _ (NeZero.pos n)))

theorem fcast_inj {n : ℕ} [NeZero n] {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : fcast n i = fcast n j) : i = j := by
  have := congrArg Fin.val h
  rwa [val_fcast_of_lt hi, val_fcast_of_lt hj] at this

/-- The level of a coordinate above the plane at `a`. -/
def lv {n : ℕ} [NeZero n] (a p : Fin n) : ℕ := (p - a).val

theorem lv_lt {n : ℕ} [NeZero n] (a p : Fin n) : lv a p < n := (p - a).isLt

theorem eq_add_lv {n : ℕ} [NeZero n] (a p : Fin n) : p = a + fcast n (lv a p) := by
  rw [lv, fcast_val]
  abel

theorem lv_add_fcast {n : ℕ} [NeZero n] (a : Fin n) (j : ℕ) (hj : j < n) :
    lv a (a + fcast n j) = j := by
  have h : a + fcast n j - a = fcast n j := by abel
  rw [lv, h, val_fcast_of_lt hj]

/-- **The mirror of a TRANSVERSE level.** `c = a + a` is the plane; a coordinate at level `j` is
reflected to level `n − j`. -/
theorem refl_transverse_level {n : ℕ} [NeZero n] (a : Fin n) (j : ℕ) (hj : j < n) :
    (a + a) - (a + fcast n j) = a + fcast n (n - j) := by
  have hz : fcast n j + fcast n (n - j) = 0 := by
    rw [fcast_add]
    have : j + (n - j) = n := by omega
    rw [this, fcast_self]
  have hy : fcast n (n - j) = -(fcast n j) := eq_neg_of_add_eq_zero_right hz
  rw [hy]
  abel

/-- **The mirror of an AXIS level.** An axis link based at level `j` spans `[j, j+1]`; its mirror is
based at level `n − 1 − j`. That shift by one is `Reflect.reflLink`'s `c − 1`. -/
theorem refl_axis_level {n : ℕ} [NeZero n] (a : Fin n) (j : ℕ) (hj : j < n) :
    (a + a) - 1 - (a + fcast n j) = a + fcast n (n - 1 - j) := by
  have hn := NeZero.pos n
  have hz : (1 + fcast n j) + fcast n (n - 1 - j) = 0 := by
    rw [← fcast_one, fcast_add, fcast_add]
    have : 1 + j + (n - 1 - j) = n := by omega
    rw [this, fcast_self]
  have hy : fcast n (n - 1 - j) = -(1 + fcast n j) := eq_neg_of_add_eq_zero_right hz
  rw [hy]
  abel

/-! ## The three blocks of LINKS, at even extent

`n = 2 * m` and the plane is at `a` with `a + a = c`. Levels `0` and `m` are the two fixed
site-planes; `blkS` is everything strictly between them one way, `blkT` the other way, `blkR` the two
planes. An AXIS link based at level `j` spans `[j, j+1]`, so it is assigned by its base and belongs to
no plane — which is exactly `no_fixed_axis_link`.
-/

section Blocks

variable {d n : ℕ} [NeZero n]

theorem lv_shift_of_ne {σ τ : Fin d} (h : σ ≠ τ) (a : Fin n) (x : Site d n) :
    lv a ((shift σ x) τ) = lv a (x τ) := by
  have hc : (shift σ x) τ = x τ := by
    simp [shift, Function.update_of_ne (Ne.symm h)]
  rw [hc]

theorem lv_add_one (a p : Fin n) : lv a (p + 1) = (lv a p + 1) % n := by
  have h1 : p + 1 = a + fcast n (lv a p + 1) := by
    rw [← fcast_add, fcast_one, ← add_assoc, ← eq_add_lv]
  rw [h1, ← fcast_mod, lv_add_fcast a _ (Nat.mod_lt _ (NeZero.pos n))]

theorem lv_shift_axis (τ : Fin d) (a : Fin n) (x : Site d n) :
    lv a ((shift τ x) τ) = (lv a (x τ) + 1) % n := by
  have hc : (shift τ x) τ = x τ + 1 := by simp [shift]
  rw [hc, lv_add_one]

theorem reflLink_coord_axis {τ : Fin d} (c : Fin n) {l : Link d n} (h : l.1 = τ) :
    (reflLink τ c l).2 τ = c - 1 - l.2 τ := by
  simp [reflLink, h, reflSite]

theorem reflLink_coord_transverse {τ : Fin d} (c : Fin n) {l : Link d n} (h : l.1 ≠ τ) :
    (reflLink τ c l).2 τ = c - l.2 τ := by
  simp [reflLink, h, reflSite]

/-- The links IN the reflection plane: transverse links at level `0` or level `m`.

DERIVED: `0` is the plane's own level. A transverse link is fixed exactly when its level is `0` or `m`, the two halves of the reflection constant, so both numerals are read off the reflection. -/
def blkR (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Link d n) :=
  Finset.univ.filter (fun l => l.1 ≠ τ ∧ (lv a (l.2 τ) = 0 ∨ lv a (l.2 τ) = m))

/-- One side of the plane.

DERIVED: `0` is the plane's level; the block is the links strictly between it and `m`. -/
def blkS (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Link d n) :=
  Finset.univ.filter (fun l =>
    if l.1 = τ then lv a (l.2 τ) < m else (0 < lv a (l.2 τ) ∧ lv a (l.2 τ) < m))

/-- The mirror side. -/
def blkT (τ : Fin d) (a : Fin n) (m : ℕ) : Finset (Link d n) :=
  Finset.univ.filter (fun l => if l.1 = τ then m ≤ lv a (l.2 τ) else m < lv a (l.2 τ))

variable (τ : Fin d) (a : Fin n) (m : ℕ)

theorem mem_blkR (l : Link d n) :
    l ∈ blkR τ a m ↔ l.1 ≠ τ ∧ (lv a (l.2 τ) = 0 ∨ lv a (l.2 τ) = m) := by
  rw [blkR, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_blkS (l : Link d n) :
    l ∈ blkS τ a m ↔
      (if l.1 = τ then lv a (l.2 τ) < m else (0 < lv a (l.2 τ) ∧ lv a (l.2 τ) < m)) := by
  rw [blkS, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_blkT (l : Link d n) :
    l ∈ blkT τ a m ↔ (if l.1 = τ then m ≤ lv a (l.2 τ) else m < lv a (l.2 τ)) := by
  rw [blkT, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **What `S ∪ R` is, in one line**: a transverse link at level at most `m`, or an axis link based
strictly below `m`. -/
theorem mem_blkS_union_blkR (l : Link d n) :
    l ∈ blkS τ a m ∪ blkR τ a m ↔
      (if l.1 = τ then lv a (l.2 τ) < m else lv a (l.2 τ) ≤ m) := by
  rw [Finset.mem_union, mem_blkS, mem_blkR]
  by_cases h : l.1 = τ
  · simp [h]
  · simp only [if_neg h]
    constructor
    · rintro (⟨_, h2⟩ | ⟨_, h0 | hm'⟩) <;> omega
    · intro hle
      rcases Nat.eq_zero_or_pos (lv a (l.2 τ)) with h0 | h0
      · exact Or.inr ⟨h, Or.inl h0⟩
      · rcases Nat.lt_or_ge (lv a (l.2 τ)) m with h1 | h1
        · exact Or.inl ⟨h0, h1⟩
        · exact Or.inr ⟨h, Or.inr (by omega)⟩

/-- **What `T ∪ R` is**: level `0` or level at least `m` for a transverse link, level at least `m`
for an axis link. Level `0` is in because the extent is periodic — the planes are `0` and `m`. -/
theorem mem_blkT_union_blkR (l : Link d n) :
    l ∈ blkT τ a m ∪ blkR τ a m ↔
      (if l.1 = τ then m ≤ lv a (l.2 τ) else (lv a (l.2 τ) = 0 ∨ m ≤ lv a (l.2 τ))) := by
  rw [Finset.mem_union, mem_blkT, mem_blkR]
  by_cases h : l.1 = τ
  · simp [h]
  · simp only [if_neg h]
    constructor
    · rintro (h1 | ⟨_, h0 | hm'⟩) <;> omega
    · rintro (h0 | h1)
      · exact Or.inr ⟨h, Or.inl h0⟩
      · rcases Nat.eq_or_lt_of_le h1 with he | hl
        · exact Or.inr ⟨h, Or.inr he.symm⟩
        · exact Or.inl hl

theorem blkR_axis_free {l : Link d n} (hl : l ∈ blkR τ a m) : l.1 ≠ τ :=
  ((mem_blkR τ a m l).mp hl).1

theorem blkS_disjoint_blkT : Disjoint (blkS τ a m) (blkT τ a m) := by
  rw [Finset.disjoint_left]
  intro l hS hT
  rw [mem_blkS] at hS
  rw [mem_blkT] at hT
  by_cases h : l.1 = τ
  · rw [if_pos h] at hS hT; omega
  · rw [if_neg h] at hS hT; omega

theorem blkS_disjoint_blkR : Disjoint (blkS τ a m) (blkR τ a m) := by
  rw [Finset.disjoint_left]
  intro l hS hR
  obtain ⟨hne, hor⟩ := (mem_blkR τ a m l).mp hR
  rw [mem_blkS, if_neg hne] at hS
  rcases hor with h | h <;> omega

theorem blkT_disjoint_blkR : Disjoint (blkT τ a m) (blkR τ a m) := by
  rw [Finset.disjoint_left]
  intro l hT hR
  obtain ⟨hne, hor⟩ := (mem_blkR τ a m l).mp hR
  rw [mem_blkT, if_neg hne] at hT
  rcases hor with h | h <;> omega

/-- **The plane is fixed by the reflection**, pointwise: `hR` of the weld. -/
theorem blkR_fixed (hm : n = 2 * m) {l : Link d n} (hl : l ∈ blkR τ a m) :
    reflLink τ (a + a) l = l := by
  obtain ⟨hne, hor⟩ := (mem_blkR τ a m l).mp hl
  refine (reflLink_fixed_iff_transverse _ l hne).mpr ?_
  have key : ∀ k : Fin n, k + k = 0 → (a + a) = (a + k) + (a + k) := by
    intro k hk
    have h2 : (a + k) + (a + k) = (a + a) + (k + k) := by abel
    rw [h2, hk, add_zero]
  have hp : l.2 τ = a + fcast n (lv a (l.2 τ)) := eq_add_lv a (l.2 τ)
  rcases hor with h0 | hmm
  · rw [hp, h0]
    refine key _ ?_
    rw [fcast_zero, add_zero]
  · rw [hp, hmm]
    refine key _ ?_
    rw [fcast_add]
    have hmn : m + m = n := by omega
    rw [hmn, fcast_self]

/-- **The reflection carries one side to the other**: `hSmap` of the weld. -/
theorem blkS_maps_blkT (hm : n = 2 * m) (hm0 : 0 < m) {l : Link d n} (hl : l ∈ blkS τ a m) :
    reflLink τ (a + a) l ∈ blkT τ a m := by
  have hn : 0 < n := NeZero.pos n
  have hjn : lv a (l.2 τ) < n := lv_lt a (l.2 τ)
  have hp : l.2 τ = a + fcast n (lv a (l.2 τ)) := eq_add_lv a (l.2 τ)
  have hdir : (reflLink τ (a + a) l).1 = l.1 := rfl
  rw [mem_blkS] at hl
  rw [mem_blkT, hdir]
  by_cases h : l.1 = τ
  · rw [if_pos h] at hl ⊢
    have himg : (reflLink τ (a + a) l).2 τ = a + fcast n (n - 1 - lv a (l.2 τ)) := by
      rw [reflLink_coord_axis _ h]
      conv_lhs => rw [hp]
      exact refl_axis_level a _ hjn
    rw [himg, lv_add_fcast a _ (by omega)]
    omega
  · rw [if_neg h] at hl ⊢
    have himg : (reflLink τ (a + a) l).2 τ = a + fcast n (n - lv a (l.2 τ)) := by
      rw [reflLink_coord_transverse _ h]
      conv_lhs => rw [hp]
      exact refl_transverse_level a _ hjn
    rw [himg, lv_add_fcast a _ (by omega)]
    omega

/-! ### The PLAQUETTE partition

Every plaquette that is not the degenerate `μ = ν = τ` one reads links from `S ∪ R` alone or from
`T ∪ R` alone, and one with both directions transverse and its base on a plane reads `R` alone. That
is what turns the Boltzmann weight into the weld's paired form, and it is the content that was
missing.

The degenerate `μ = ν = τ` plaquette really does straddle — `degenerate_axis_plaquette_straddles`
exhibits it — and is harmless only because its holonomy is the identity
(`WilsonHypercubic.bd_diag_hol_one`), which is a statement about the ACTION, not the geometry.
-/

/-- **One side.** A plaquette based strictly below the plane reads `S ∪ R` only. -/
theorem plaq_links_le (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) (hlt : lv a (q.2 τ) < m) :
    ∀ l ∈ (bd q).map Prod.fst, l ∈ blkS τ a m ∪ blkR τ a m := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have hlt' : lv a (x τ) < m := hlt
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  have hsucc : (lv a (x τ) + 1) % n = lv a (x τ) + 1 := Nat.mod_eq_of_lt (by omega)
  intro l hl
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rw [mem_blkS_union_blkR]
  rcases hl with h | h | h | h <;> subst h
  · show (if μ = τ then lv a (x τ) < m else lv a (x τ) ≤ m)
    by_cases hμ : μ = τ
    · rw [if_pos hμ]; omega
    · rw [if_neg hμ]; omega
  · show (if ν = τ then lv a ((shift μ x) τ) < m else lv a ((shift μ x) τ) ≤ m)
    by_cases hμ : μ = τ
    · have hν : ν ≠ τ := fun hc => hdeg' ⟨hμ, hc⟩
      rw [if_neg hν, hμ, lv_shift_axis, hsucc]
      omega
    · rw [lv_shift_of_ne hμ]
      by_cases hν : ν = τ
      · rw [if_pos hν]; omega
      · rw [if_neg hν]; omega
  · show (if μ = τ then lv a ((shift ν x) τ) < m else lv a ((shift ν x) τ) ≤ m)
    by_cases hν : ν = τ
    · have hμ : μ ≠ τ := fun hc => hdeg' ⟨hc, hν⟩
      rw [if_neg hμ, hν, lv_shift_axis, hsucc]
      omega
    · rw [lv_shift_of_ne hν]
      by_cases hμ : μ = τ
      · rw [if_pos hμ]; omega
      · rw [if_neg hμ]; omega
  · show (if ν = τ then lv a (x τ) < m else lv a (x τ) ≤ m)
    by_cases hν : ν = τ
    · rw [if_pos hν]; omega
    · rw [if_neg hν]; omega

/-- **The other side.** A plaquette based at or above the plane reads `T ∪ R` only. -/
theorem plaq_links_ge (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) (hge : m ≤ lv a (q.2 τ)) :
    ∀ l ∈ (bd q).map Prod.fst, l ∈ blkT τ a m ∪ blkR τ a m := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hdeg' : ¬ (μ = τ ∧ ν = τ) := hdeg
  have hge' : m ≤ lv a (x τ) := hge
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  have hsucc : (lv a (x τ) + 1) % n = 0 ∨ (lv a (x τ) + 1) % n = lv a (x τ) + 1 := by
    rcases Nat.lt_or_ge (lv a (x τ) + 1) n with h | h
    · exact Or.inr (Nat.mod_eq_of_lt h)
    · have he : lv a (x τ) + 1 = n := by omega
      exact Or.inl (by rw [he, Nat.mod_self])
  intro l hl
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rw [mem_blkT_union_blkR]
  rcases hl with h | h | h | h <;> subst h
  · show (if μ = τ then m ≤ lv a (x τ) else (lv a (x τ) = 0 ∨ m ≤ lv a (x τ)))
    by_cases hμ : μ = τ
    · rw [if_pos hμ]; omega
    · rw [if_neg hμ]; omega
  · show (if ν = τ then m ≤ lv a ((shift μ x) τ)
      else (lv a ((shift μ x) τ) = 0 ∨ m ≤ lv a ((shift μ x) τ)))
    by_cases hμ : μ = τ
    · have hν : ν ≠ τ := fun hc => hdeg' ⟨hμ, hc⟩
      rw [if_neg hν, hμ, lv_shift_axis]
      rcases hsucc with h | h <;> rw [h] <;> omega
    · rw [lv_shift_of_ne hμ]
      by_cases hν : ν = τ
      · rw [if_pos hν]; omega
      · rw [if_neg hν]; omega
  · show (if μ = τ then m ≤ lv a ((shift ν x) τ)
      else (lv a ((shift ν x) τ) = 0 ∨ m ≤ lv a ((shift ν x) τ)))
    by_cases hν : ν = τ
    · have hμ : μ ≠ τ := fun hc => hdeg' ⟨hc, hν⟩
      rw [if_neg hμ, hν, lv_shift_axis]
      rcases hsucc with h | h <;> rw [h] <;> omega
    · rw [lv_shift_of_ne hν]
      by_cases hμ : μ = τ
      · rw [if_pos hμ]; omega
      · rw [if_neg hμ]; omega
  · show (if ν = τ then m ≤ lv a (x τ) else (lv a (x τ) = 0 ∨ m ≤ lv a (x τ)))
    by_cases hν : ν = τ
    · rw [if_pos hν]; omega
    · rw [if_neg hν]; omega

/-- **Inside the plane.** A plaquette with both directions transverse and its base ON a plane reads
`R` alone — this is the part of the action that becomes the weld's plane weight `w`. -/
theorem plaq_links_plane {q : Plaq d n} (h1 : q.1.1 ≠ τ) (h2 : q.1.2 ≠ τ)
    (h0 : lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m) :
    ∀ l ∈ (bd q).map Prod.fst, l ∈ blkR τ a m := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  have hμ : μ ≠ τ := h1
  have hν : ν ≠ τ := h2
  have h0' : lv a (x τ) = 0 ∨ lv a (x τ) = m := h0
  intro l hl
  simp only [bd, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hl
  rw [mem_blkR]
  rcases hl with h | h | h | h <;> subst h
  · exact ⟨hμ, h0'⟩
  · exact ⟨hν, by rw [lv_shift_of_ne hμ]; exact h0'⟩
  · exact ⟨hμ, by rw [lv_shift_of_ne hν]; exact h0'⟩
  · exact ⟨hν, h0'⟩

/-- **EVERY non-degenerate plaquette lies on one side.** The trichotomy, as one statement. -/
theorem plaq_side (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hdeg : ¬ (q.1.1 = τ ∧ q.1.2 = τ)) :
    (∀ l ∈ (bd q).map Prod.fst, l ∈ blkS τ a m ∪ blkR τ a m)
      ∨ (∀ l ∈ (bd q).map Prod.fst, l ∈ blkT τ a m ∪ blkR τ a m) := by
  rcases Nat.lt_or_ge (lv a (q.2 τ)) m with h | h
  · exact Or.inl (plaq_links_le τ a m hm hm0 hdeg h)
  · exact Or.inr (plaq_links_ge τ a m hm hm0 hdeg h)

/-- **NEGATIVE CONTROL: the degenerate plaquette genuinely straddles.** Excluding `μ = ν = τ` from
`plaq_side` is not tidying. At base level `m − 1` that plaquette reads an axis link at level `m − 1`,
which is in `S`, and one at level `m`, which is in `T`, so it lies in neither `S ∪ R` nor `T ∪ R`. -/
theorem degenerate_axis_plaquette_straddles (hm : n = 2 * m) (hm0 : 0 < m) :
    ∃ q : Plaq d n, q.1.1 = τ ∧ q.1.2 = τ ∧
      ¬ ((∀ l ∈ (bd q).map Prod.fst, l ∈ blkS τ a m ∪ blkR τ a m)
        ∨ (∀ l ∈ (bd q).map Prod.fst, l ∈ blkT τ a m ∪ blkR τ a m)) := by
  have hn : 0 < n := NeZero.pos n
  refine ⟨((τ, τ), Function.update (fun _ => a) τ (a + fcast n (m - 1))), rfl, rfl, ?_⟩
  set x : Site d n := Function.update (fun _ => a) τ (a + fcast n (m - 1)) with hx
  have hxτ : x τ = a + fcast n (m - 1) := by rw [hx, Function.update_self]
  have hlv : lv a (x τ) = m - 1 := by
    rw [hxτ, lv_add_fcast a _ (by omega)]
  have hs1 : lv a ((shift τ x) τ) = m := by
    rw [lv_shift_axis, hlv, Nat.mod_eq_of_lt (by omega)]
    omega
  have h1 : ((τ, x) : Link d n) ∈ (bd (((τ, τ), x) : Plaq d n)).map Prod.fst := by
    simp [bd]
  have h2 : ((τ, shift τ x) : Link d n) ∈ (bd (((τ, τ), x) : Plaq d n)).map Prod.fst := by
    simp [bd]
  rintro (hS | hT)
  · have hb := hS _ h2
    rw [mem_blkS_union_blkR, if_pos rfl] at hb
    rw [hs1] at hb
    omega
  · have hb := hT _ h1
    rw [mem_blkT_union_blkR, if_pos rfl] at hb
    rw [hlv] at hb
    omega

end Blocks

/-! ## The ACTION splits at even extent

Four groups of plaquettes: the degenerate `μ = ν = τ` ones (identity holonomy, zero contribution),
those lying INSIDE a plane, those reading `S ∪ R`, and those reading `T ∪ R`. The reflection permutes
them: it fixes the plane group setwise and EXCHANGES the other two, which is what makes
`∑ over T∪R` equal to `∑ over S∪R` composed with the reflection — the step that turns
`exp(−βS)` into `h(U) · h(θU) · w(U|R)`.
-/

section WilsonSplit

open MassGap.WilsonLattice MassGap.WilsonAction

variable {d n : ℕ} [NeZero n]

/-- A degenerate plaquette has identity holonomy, in any group. `WilsonHypercubic.bd_diag_hol_one`
states this for `SU 2` only; the fact is group-generic and the general form is what is needed here. -/
theorem hol_diag_one {G : Type} [Group G] (μ : Fin d) (x : Site d n) (U : Link d n → G) :
    wilsonHol (bd (d := d) (n := n)) ((μ, μ), x) U = 1 := by
  rw [hol_bd]
  group

/-- The reflected level of a transverse coordinate. -/
theorem lv_refl_site (a p : Fin n) : lv a ((a + a) - p) = (n - lv a p) % n := by
  conv_lhs => rw [eq_add_lv a p]
  rw [refl_transverse_level a _ (lv_lt a p), ← fcast_mod,
    lv_add_fcast a _ (Nat.mod_lt _ (NeZero.pos n))]

/-- The reflected level of an axis coordinate. -/
theorem lv_refl_site_axis (a p : Fin n) : lv a ((a + a) - 1 - p) = n - 1 - lv a p := by
  have h1 := lv_lt a p
  have h2 := NeZero.pos n
  conv_lhs => rw [eq_add_lv a p]
  rw [refl_axis_level a _ h1, lv_add_fcast a _ (by omega)]

variable (τ : Fin d) (a : Fin n) (m : ℕ)

/-- Plaquettes with both directions along the axis: identity holonomy, zero contribution. -/
def plqDeg : Finset (Plaq d n) := Finset.univ.filter (fun q => q.1.1 = τ ∧ q.1.2 = τ)

/-- Plaquettes lying INSIDE a plane.

DERIVED: `0` is the plane's level, the level at which a plaquette reads only fixed links. -/
def plqZero : Finset (Plaq d n) :=
  Finset.univ.filter (fun q => q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m))

/-- Plaquettes reading `S ∪ R`.

DERIVED: `0` is the plane's level; this group is the plaquettes above it. -/
def plqPlus : Finset (Plaq d n) :=
  Finset.univ.filter (fun q =>
    ¬ (q.1.1 = τ ∧ q.1.2 = τ)
      ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m))
      ∧ lv a (q.2 τ) < m)

/-- Plaquettes reading `T ∪ R`.

DERIVED: `0` is the plane's own level, the level at which a plaquette reads only fixed links. This
group is the mirror of `plqPlus` under the reflection. -/
def plqMinus : Finset (Plaq d n) :=
  Finset.univ.filter (fun q =>
    ¬ (q.1.1 = τ ∧ q.1.2 = τ)
      ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m))
      ∧ ¬ (lv a (q.2 τ) < m))

theorem mem_plqDeg (q : Plaq d n) : q ∈ plqDeg τ ↔ (q.1.1 = τ ∧ q.1.2 = τ) := by
  rw [plqDeg, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_plqZero (q : Plaq d n) :
    q ∈ plqZero τ a m ↔
      (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m)) := by
  rw [plqZero, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_plqPlus (q : Plaq d n) :
    q ∈ plqPlus τ a m ↔
      (¬ (q.1.1 = τ ∧ q.1.2 = τ)
        ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m))
        ∧ lv a (q.2 τ) < m) := by
  rw [plqPlus, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_plqMinus (q : Plaq d n) :
    q ∈ plqMinus τ a m ↔
      (¬ (q.1.1 = τ ∧ q.1.2 = τ)
        ∧ ¬ (q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m))
        ∧ ¬ (lv a (q.2 τ) < m)) := by
  rw [plqMinus, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **The four groups partition the plaquettes**, so any sum over plaquettes splits. -/
theorem sum_plaq_split {M : Type} [AddCommMonoid M] (f : Plaq d n → M) :
    ∑ q, f q = ((∑ q ∈ plqDeg τ, f q) + (∑ q ∈ plqZero τ a m, f q))
      + ((∑ q ∈ plqPlus τ a m, f q) + (∑ q ∈ plqMinus τ a m, f q)) := by
  have hdz : Disjoint (plqDeg (d := d) (n := n) τ) (plqZero τ a m) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact ((mem_plqZero τ a m q).mp h2).1 ((mem_plqDeg τ q).mp h1).1
  have hpm : Disjoint (plqPlus (d := d) (n := n) τ a m) (plqMinus τ a m) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    exact ((mem_plqMinus τ a m q).mp h2).2.2 ((mem_plqPlus τ a m q).mp h1).2.2
  have hcross : Disjoint (plqDeg (d := d) (n := n) τ ∪ plqZero τ a m)
      (plqPlus τ a m ∪ plqMinus τ a m) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    rcases Finset.mem_union.mp h1 with hd | hz <;> rcases Finset.mem_union.mp h2 with hp | hn
    · exact ((mem_plqPlus τ a m q).mp hp).1 ((mem_plqDeg τ q).mp hd)
    · exact ((mem_plqMinus τ a m q).mp hn).1 ((mem_plqDeg τ q).mp hd)
    · exact ((mem_plqPlus τ a m q).mp hp).2.1 ((mem_plqZero τ a m q).mp hz)
    · exact ((mem_plqMinus τ a m q).mp hn).2.1 ((mem_plqZero τ a m q).mp hz)
  have huniv : (plqDeg (d := d) (n := n) τ ∪ plqZero τ a m)
      ∪ (plqPlus τ a m ∪ plqMinus τ a m) = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun q => ?_)
    simp only [Finset.mem_union, mem_plqDeg, mem_plqZero, mem_plqPlus, mem_plqMinus]
    by_cases h1 : q.1.1 = τ ∧ q.1.2 = τ
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : q.1.1 ≠ τ ∧ q.1.2 ≠ τ ∧ (lv a (q.2 τ) = 0 ∨ lv a (q.2 τ) = m)
      · exact Or.inl (Or.inr h2)
      · by_cases h3 : lv a (q.2 τ) < m
        · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
        · exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
  rw [← huniv, Finset.sum_union hcross, Finset.sum_union hdz, Finset.sum_union hpm]

/-- **The degenerate group contributes nothing.** -/
theorem sum_plqDeg_zero {N : ℕ} (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    ∑ q ∈ plqDeg (d := d) (n := n) τ,
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) = 0 := by
  refine Finset.sum_eq_zero (fun q hq => ?_)
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  obtain ⟨h1, h2⟩ := (mem_plqDeg τ _).mp hq
  have hνμ : ν = μ := by
    show ν = μ
    rw [show ν = τ from h2, show μ = τ from h1]
  rw [show (((μ, ν), x) : Plaq d n) = ((μ, μ), x) by rw [hνμ], hol_diag_one,
    wilsonDensity_one hN]

/-- **A plaquette observable composed with the reflection is the reflected plaquette's.** The
mirrored holonomy is only CONJUGATE to the image plaquette's (`Reflect.hol_reflConf`) and the Wilson
density is a class function. -/
theorem density_reflConf {N : ℕ} (c : Fin n) (q : Plaq d n) (U : Link d n → MassGap.SUN.SU N) :
    wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ c U))
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) (reflPlaq τ c q) U) := by
  obtain ⟨g, hg⟩ := hol_reflConf (G := MassGap.SUN.SU N) τ c q U
  rw [hg, wilsonDensity_conj]

/-- **The reflection carries the `S ∪ R` plaquettes onto the `T ∪ R` ones.** -/
theorem reflPlaq_plus_mem_minus (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ plqPlus τ a m) : reflPlaq τ (a + a) q ∈ plqMinus τ a m := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  obtain ⟨hdeg, hzero, hlt⟩ := (mem_plqPlus τ a m _).mp hq
  have hlt' : lv a (x τ) < m := hlt
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  rw [mem_plqMinus]
  by_cases hμ : μ = τ
  · have hν : ν ≠ τ := fun hc => hdeg ⟨hμ, hc⟩
    rw [show reflPlaq τ (a + a) (((μ, ν), x) : Plaq d n)
        = ((ν, τ), reflSite τ (a + a - 1) x) by simp [reflPlaq, hμ]]
    refine ⟨fun h => hν h.1, fun h => h.2.1 rfl, ?_⟩
    show ¬ (lv a ((reflSite τ (a + a - 1) x) τ) < m)
    rw [reflSite_axis, lv_refl_site_axis]
    omega
  · by_cases hν : ν = τ
    · rw [show reflPlaq τ (a + a) (((μ, ν), x) : Plaq d n)
          = ((τ, μ), reflSite τ (a + a - 1) x) by simp [reflPlaq, hμ, hν]]
      refine ⟨fun h => hμ h.2, fun h => h.1 rfl, ?_⟩
      show ¬ (lv a ((reflSite τ (a + a - 1) x) τ) < m)
      rw [reflSite_axis, lv_refl_site_axis]
      omega
    · have hne : ¬ (lv a (x τ) = 0 ∨ lv a (x τ) = m) := fun hc => hzero ⟨hμ, hν, hc⟩
      rw [show reflPlaq τ (a + a) (((μ, ν), x) : Plaq d n)
          = ((μ, ν), reflSite τ (a + a) x) by simp [reflPlaq, hμ, hν]]
      have hlev : lv a ((reflSite τ (a + a) x) τ) = n - lv a (x τ) := by
        rw [reflSite_axis, lv_refl_site, Nat.mod_eq_of_lt (by omega)]
      refine ⟨fun h => hμ h.1, ?_, ?_⟩
      · rintro ⟨-, -, h⟩
        rw [hlev] at h
        omega
      · show ¬ (lv a ((reflSite τ (a + a) x) τ) < m)
        rw [hlev]
        omega

/-- And back the other way, so the two groups are exchanged. -/
theorem reflPlaq_minus_mem_plus (hm : n = 2 * m) (hm0 : 0 < m) {q : Plaq d n}
    (hq : q ∈ plqMinus τ a m) : reflPlaq τ (a + a) q ∈ plqPlus τ a m := by
  obtain ⟨⟨μ, ν⟩, x⟩ := q
  obtain ⟨hdeg, hzero, hge⟩ := (mem_plqMinus τ a m _).mp hq
  have hge' : ¬ (lv a (x τ) < m) := hge
  have hjn : lv a (x τ) < n := lv_lt a (x τ)
  rw [mem_plqPlus]
  by_cases hμ : μ = τ
  · have hν : ν ≠ τ := fun hc => hdeg ⟨hμ, hc⟩
    rw [show reflPlaq τ (a + a) (((μ, ν), x) : Plaq d n)
        = ((ν, τ), reflSite τ (a + a - 1) x) by simp [reflPlaq, hμ]]
    refine ⟨fun h => hν h.1, fun h => h.2.1 rfl, ?_⟩
    show lv a ((reflSite τ (a + a - 1) x) τ) < m
    rw [reflSite_axis, lv_refl_site_axis]
    omega
  · by_cases hν : ν = τ
    · rw [show reflPlaq τ (a + a) (((μ, ν), x) : Plaq d n)
          = ((τ, μ), reflSite τ (a + a - 1) x) by simp [reflPlaq, hμ, hν]]
      refine ⟨fun h => hμ h.2, fun h => h.1 rfl, ?_⟩
      show lv a ((reflSite τ (a + a - 1) x) τ) < m
      rw [reflSite_axis, lv_refl_site_axis]
      omega
    · have hne : ¬ (lv a (x τ) = 0 ∨ lv a (x τ) = m) := fun hc => hzero ⟨hμ, hν, hc⟩
      rw [show reflPlaq τ (a + a) (((μ, ν), x) : Plaq d n)
          = ((μ, ν), reflSite τ (a + a) x) by simp [reflPlaq, hμ, hν]]
      have hlev : lv a ((reflSite τ (a + a) x) τ) = n - lv a (x τ) := by
        rw [reflSite_axis, lv_refl_site, Nat.mod_eq_of_lt (by omega)]
      refine ⟨fun h => hμ h.1, ?_, ?_⟩
      · rintro ⟨-, -, h⟩
        rw [hlev] at h
        omega
      · show lv a ((reflSite τ (a + a) x) τ) < m
        rw [hlev]
        omega

/-- **THE MIRROR IDENTITY.** The `T ∪ R` part of the action, evaluated at `U`, is the `S ∪ R` part
evaluated at the REFLECTED configuration. This is what `pairing_with_reflection_nonneg`'s `hmirror`
step needs from the WEIGHT rather than from the observable, and it is what makes the Boltzmann factor
a paired product. -/
theorem sum_plqMinus_eq_plus_refl {N : ℕ} (hm : n = 2 * m) (hm0 : 0 < m)
    (U : Link d n → MassGap.SUN.SU N) :
    ∑ q ∈ plqMinus τ a m, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)
      = ∑ q ∈ plqPlus τ a m,
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a) U)) := by
  have himg : (plqPlus (d := d) (n := n) τ a m).image (reflPlaq τ (a + a)) = plqMinus τ a m := by
    ext q
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact reflPlaq_plus_mem_minus τ a m hm hm0 hp
    · intro hq
      exact ⟨reflPlaq τ (a + a) q, reflPlaq_minus_mem_plus τ a m hm hm0 hq,
        reflPlaq_involutive τ (a + a) q⟩
  have hinj : ∀ x ∈ plqPlus (d := d) (n := n) τ a m, ∀ y ∈ plqPlus (d := d) (n := n) τ a m,
      reflPlaq τ (a + a) x = reflPlaq τ (a + a) y → x = y :=
    fun x _ y _ h => (reflPlaq_involutive τ (a + a)).injective h
  calc ∑ q ∈ plqMinus τ a m, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)
      = ∑ q ∈ (plqPlus τ a m).image (reflPlaq τ (a + a)),
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U) := by rw [himg]
    _ = ∑ q ∈ plqPlus τ a m,
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) (reflPlaq τ (a + a) q) U) :=
        Finset.sum_image hinj
    _ = ∑ q ∈ plqPlus τ a m,
          wilsonDensity (wilsonHol (bd (d := d) (n := n)) q (reflConf τ (a + a) U)) :=
        Finset.sum_congr rfl (fun q _ => (density_reflConf τ (a + a) q U).symm)

/-! ### Assembling the Boltzmann weight into the weld's paired form -/

variable {N : ℕ}

/-- The `S ∪ R` part of the action. -/
noncomputable def actPlus (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ plqPlus τ a m, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- The `T ∪ R` part. -/
noncomputable def actMinus (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ plqMinus τ a m, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

/-- The part living inside the planes — this becomes the weld's plane weight. -/
noncomputable def actZero (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  ∑ q ∈ plqZero τ a m, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)

theorem action_eq_split (hN : N ≠ 0) (U : Link d n → MassGap.SUN.SU N) :
    (sysWilson N d n).action U
      = actPlus τ a m U + actMinus τ a m U + actZero τ a m U := by
  show (∑ q, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)) = _
  rw [sum_plaq_split τ a m, sum_plqDeg_zero τ hN U]
  show 0 + actZero τ a m U + (actPlus τ a m U + actMinus τ a m U) = _
  ring

theorem measurable_density_hol (q : Plaq d n) :
    Measurable (fun U : Link d n → MassGap.SUN.SU N =>
      wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)) :=
  measurable_wilsonDensity.comp (measurable_wilsonHol (G := MassGap.SUN.SU N) _ q)

theorem measurable_actSum (A : Finset (Plaq d n)) :
    Measurable (fun U : Link d n → MassGap.SUN.SU N =>
      ∑ q ∈ A, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)) :=
  Finset.measurable_sum _ (fun q _ => measurable_density_hol q)

theorem abs_actSum_le (hN : N ≠ 0) (A : Finset (Plaq d n))
    (U : Link d n → MassGap.SUN.SU N) :
    |∑ q ∈ A, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)| ≤ 2 * A.card := by
  calc |∑ q ∈ A, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)|
      ≤ ∑ q ∈ A, |wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ A, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        rw [abs_of_nonneg (wilsonDensity_nonneg hN _)]
        exact wilsonDensity_le_two hN _
    _ = (A.card : ℝ) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * A.card := by ring

theorem abs_exp_actSum_le (hN : N ≠ 0) (β : ℝ) (A : Finset (Plaq d n))
    (U : Link d n → MassGap.SUN.SU N) :
    |Real.exp (-β * ∑ q ∈ A, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U))|
      ≤ Real.exp (|β| * (2 * A.card)) := by
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  calc -β * (∑ q ∈ A, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U))
      ≤ |(-β) * ∑ q ∈ A, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)| := le_abs_self _
    _ = |β| * |∑ q ∈ A, wilsonDensity (wilsonHol (bd (d := d) (n := n)) q U)| := by
        rw [abs_mul, abs_neg]
    _ ≤ |β| * (2 * A.card) :=
        mul_le_mul_of_nonneg_left (abs_actSum_le hN A U) (abs_nonneg _)

/-- The observable of the positive half: the plaquette observable, centred, times the half-action's
Boltzmann factor. This is the `O` of the weld. -/
noncomputable def obsPlus (q₀ : Plaq d n) (aC β : ℝ) (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
    * Real.exp (-β * actPlus τ a m U)

/-- The plane weight: the Boltzmann factor of the plaquettes inside the planes. This is the `W` of
the weld, and it is where `exp(−β S₀)` goes. -/
noncomputable def wPlane (β : ℝ) (U : Link d n → MassGap.SUN.SU N) : ℝ :=
  Real.exp (-β * actZero τ a m U)

/-- **THE FACTORISATION.** The physical integrand IS the weld's paired form. -/
theorem integrand_eq_paired (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    (q₀ : Plaq d n) (aC β : ℝ) (U : Link d n → MassGap.SUN.SU N) :
    (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
        * (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ (reflConf τ (a + a) U)) - aC)
        * (sysWilson N d n).boltz β U
      = wPlane τ a m β U * obsPlus τ a m q₀ aC β U
          * obsPlus τ a m q₀ aC β (reflConf τ (a + a) U) := by
  have hmir : actPlus τ a m (reflConf τ (a + a) U) = actMinus τ a m U :=
    (sum_plqMinus_eq_plus_refl τ a m hm hm0 U).symm
  show _ * _ * Real.exp (-β * (sysWilson N d n).action U) = _
  rw [action_eq_split τ a m hN U]
  unfold wPlane obsPlus
  rw [hmir]
  rw [show -β * (actPlus τ a m U + actMinus τ a m U + actZero τ a m U)
      = (-β * actZero τ a m U) + ((-β * actPlus τ a m U) + (-β * actMinus τ a m U)) by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- **The positive-half observable READS `S ∪ R`.** -/
theorem obsPlus_local (hm : n = 2 * m) (hm0 : 0 < m) (q₀ : Plaq d n)
    (hq₀deg : ¬ (q₀.1.1 = τ ∧ q₀.1.2 = τ)) (hq₀lv : lv a (q₀.2 τ) < m) (aC β : ℝ)
    (U V : Link d n → MassGap.SUN.SU N)
    (hS : ∀ l ∈ blkS τ a m, U l = V l) (hR : ∀ l ∈ blkR τ a m, U l = V l) :
    obsPlus τ a m q₀ aC β U = obsPlus τ a m q₀ aC β V := by
  have hUV : ∀ l ∈ blkS τ a m ∪ blkR τ a m, U l = V l := by
    intro l hl
    rcases Finset.mem_union.mp hl with h | h
    · exact hS l h
    · exact hR l h
  have h1 : wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U)
      = wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ V) := by
    rw [hol_congr_on_support (bd (d := d) (n := n)) q₀ U V
      (fun l hl => hUV l (plaq_links_le τ a m hm hm0 hq₀deg hq₀lv l hl))]
  have h2 : actPlus τ a m U = actPlus τ a m V :=
    action_on_congr_of_support (bd (d := d) (n := n)) (wilsonDensity (N := N))
      (plqPlus τ a m) (blkS τ a m ∪ blkR τ a m)
      (fun p hp => plaq_links_le τ a m hm hm0 ((mem_plqPlus τ a m p).mp hp).1
        ((mem_plqPlus τ a m p).mp hp).2.2) U V hUV
  unfold obsPlus
  rw [h1, h2]

/-- **The plane weight READS `R`.** -/
theorem wPlane_local (β : ℝ) (U V : Link d n → MassGap.SUN.SU N)
    (hR : ∀ l ∈ blkR τ a m, U l = V l) :
    wPlane (N := N) τ a m β U = wPlane τ a m β V := by
  have h2 : actZero τ a m U = actZero τ a m V :=
    action_on_congr_of_support (bd (d := d) (n := n)) (wilsonDensity (N := N))
      (plqZero τ a m) (blkR τ a m)
      (fun p hp => plaq_links_plane τ a m ((mem_plqZero τ a m p).mp hp).1
        ((mem_plqZero τ a m p).mp hp).2.1 ((mem_plqZero τ a m p).mp hp).2.2) U V hR
  unfold wPlane
  rw [h2]

/-- **THE OSTERWALDER–SEILER PAIRING INEQUALITY FOR THE WILSON WEIGHT, AT EVEN EXTENT.**

No hypothesis on the observable beyond where it sits: the plaquette `q₀` must not be the degenerate
axis one and must be based strictly below the plane. Everything else — the action split, the mirror
identity, the locality, the conditional square — is proved above.

This is `ReflectPositive.PlaqReflPositive`'s integral, before dividing by `Z`. -/
theorem wilson_pairing_nonneg_even (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    (q₀ : Plaq d n) (hq₀deg : ¬ (q₀.1.1 = τ ∧ q₀.1.2 = τ)) (hq₀lv : lv a (q₀.2 τ) < m)
    (β aC : ℝ) :
    0 ≤ ∫ U, (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
        * (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ (reflConf τ (a + a) U)) - aC)
        * (sysWilson N d n).boltz β U ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) := by
  have hcongr : (∫ U, (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
        * (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ (reflConf τ (a + a) U)) - aC)
        * (sysWilson N d n).boltz β U ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))))
      = ∫ U, wPlane τ a m β U * obsPlus τ a m q₀ aC β U
          * obsPlus τ a m q₀ aC β (twist (reflLinkPerm τ (a + a)) (axisDagger (N := N) τ) U)
          ∂(cvol (Link d n) (probHaar (MassGap.SUN.SU N))) :=
    integral_congr_ae (Filter.Eventually.of_forall
      (fun U => integrand_eq_paired τ a m hN hm hm0 q₀ aC β U))
  rw [hcongr]
  -- measurability and bounds
  have hOm : Measurable (obsPlus (N := N) τ a m q₀ aC β) := by
    unfold obsPlus actPlus
    exact ((measurable_density_hol q₀).sub measurable_const).mul
      (Real.measurable_exp.comp ((measurable_actSum _).const_mul _))
  have hWm : Measurable (wPlane (N := N) τ a m β) := by
    unfold wPlane actZero
    exact Real.measurable_exp.comp ((measurable_actSum _).const_mul _)
  have hWnn : ∀ U, 0 ≤ wPlane (N := N) τ a m β U := fun U => le_of_lt (Real.exp_pos _)
  set K0 : ℝ := Real.exp (|β| * (2 * ((plqZero (d := d) (n := n) τ a m).card : ℝ))) with hK0
  set K1 : ℝ := (2 + |aC|)
    * Real.exp (|β| * (2 * ((plqPlus (d := d) (n := n) τ a m).card : ℝ))) with hK1
  have hK1nn : 0 ≤ K1 := by
    refine mul_nonneg ?_ (le_of_lt (Real.exp_pos _))
    have := abs_nonneg aC
    linarith
  have hObd : ∀ U, |obsPlus (N := N) τ a m q₀ aC β U| ≤ K1 := by
    intro U
    unfold obsPlus
    rw [abs_mul, hK1]
    refine mul_le_mul ?_ (abs_exp_actSum_le hN β _ U) (abs_nonneg _) (by
      have := abs_nonneg aC; linarith)
    have h1 : 0 ≤ wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) :=
      wilsonDensity_nonneg hN _
    have h2 : wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) ≤ 2 :=
      wilsonDensity_le_two hN _
    have h3 : -|aC| ≤ aC := neg_abs_le _
    have h4 : aC ≤ |aC| := le_abs_self _
    rw [abs_le]
    constructor <;> linarith
  have hWbd : ∀ U, |wPlane (N := N) τ a m β U| ≤ K0 := fun U => abs_exp_actSum_le hN β _ U
  refine pairing_nonneg_of_local (probHaar (MassGap.SUN.SU N))
    (blkS τ a m) (blkT τ a m) (blkR τ a m)
    (blkS_disjoint_blkT τ a m) (blkS_disjoint_blkR τ a m) (blkT_disjoint_blkR τ a m)
    (reflLinkPerm τ (a + a)) (axisDagger (N := N) τ)
    (fun l => axisDagger_measurePreserving τ l)
    (fun l hl => blkR_fixed τ a m hm hl)
    (fun l hl u => by simp [axisDagger, blkR_axis_free τ a m hl])
    (fun l hl => blkS_maps_blkT τ a m hm hm0 hl)
    (fun _ => 1)
    (obsPlus τ a m q₀ aC β) hOm
    (fun U V hS hR => obsPlus_local τ a m hm hm0 q₀ hq₀deg hq₀lv aC β U V hS hR)
    (wPlane τ a m β) hWm hWnn
    (fun U V hR => wPlane_local τ a m β U V hR)
    (K0 * K1 * K1) (fun U => ?_)
  rw [abs_mul, abs_mul]
  have h0 : (0 : ℝ) ≤ |wPlane (N := N) τ a m β U| := abs_nonneg _
  exact mul_le_mul (mul_le_mul (hWbd U) (hObd U) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hWbd U))) (hObd _) (abs_nonneg _)
    (mul_nonneg (le_trans (abs_nonneg _) (hWbd U)) hK1nn)

/-- **The Gibbs form**: dividing by `Z > 0`. This is exactly `ReflectPositive.PlaqReflPositive`'s
statement, unfolded — `EW Nc β O` is `(wilsonSystem bd wilsonDensity).expect (probHaar) β O` and
`plaqE Nc q` is `fun U => wilsonDensity (wilsonHol bd q U)`. -/
theorem wilson_expect_pairing_nonneg_even (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    (q₀ : Plaq d n) (hq₀deg : ¬ (q₀.1.1 = τ ∧ q₀.1.2 = τ)) (hq₀lv : lv a (q₀.2 τ) < m)
    (β aC : ℝ) :
    0 ≤ (sysWilson N d n).expect (probHaar (MassGap.SUN.SU N)) β
      (fun U => (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ U) - aC)
        * (wilsonDensity (wilsonHol (bd (d := d) (n := n)) q₀ (reflConf τ (a + a) U)) - aC)) := by
  have hZ : 0 < (sysWilson N d n).partition (probHaar (MassGap.SUN.SU N)) β :=
    MassGap.WilsonReal.wilsonSystem_partition_pos hN (bd (d := d) (n := n)) β
  refine div_nonneg ?_ (le_of_lt hZ)
  exact wilson_pairing_nonneg_even τ a m hN hm hm0 q₀ hq₀deg hq₀lv β aC

/-! ### Which lags this covers, and which it does not

A lag `c` is covered exactly when it has a half in `Fin n` — when `c.val` is even. At extent
`n = 2m` that is half the lags. `odd_lag_has_no_plane` is the negative control: for an odd lag the
plane is not merely unconstructed, it does not exist, and the reflection is a LINK reflection with a
fixed axis link that `reflConf` inverts. -/

/-- The level seen from the OTHER half of the same reflection constant, which is the first one
shifted by `m`. -/
theorem lv_other_half (hm : n = 2 * m) (a p : Fin n) :
    lv (a + fcast n m) p = (lv a p + m) % n := by
  have hnm : n - m = m := by omega
  have hneg : fcast n m + fcast n (n - m) = 0 := by
    rw [fcast_add]
    have hs : m + (n - m) = n := by omega
    rw [hs, fcast_self]
  have hneg' : fcast n (n - m) = -(fcast n m) := eq_neg_of_add_eq_zero_right hneg
  have h1 : p - (a + fcast n m) = fcast n (lv a p + m) := by
    have h2 : p - a = fcast n (lv a p) := by rw [lv, fcast_val]
    have h4 : p - (a + fcast n m) = (p - a) + (-(fcast n m)) := by abel
    rw [h4, h2, ← hneg', fcast_add, hnm]
  rw [lv, h1]
  rfl

/-- **One of the two halves always puts a given site strictly below the plane.** Both halves of the
same reflection constant are available, and they differ by `m`, so whichever side a site falls on
there is a choice of plane for which it is on the `S` side. -/
theorem exists_half_below (hm : n = 2 * m) (hm0 : 0 < m) {c : Fin n} (hc : Even c.val)
    (p : Fin n) : ∃ a : Fin n, a + a = c ∧ lv a p < m := by
  obtain ⟨a0, ha0⟩ := exists_fixed_site hc
  have hj := lv_lt a0 p
  by_cases h : lv a0 p < m
  · exact ⟨a0, ha0, h⟩
  · have hmm : fcast n m + fcast n m = 0 := by
      rw [fcast_add]
      have hs : m + m = n := by omega
      rw [hs, fcast_self]
    refine ⟨a0 + fcast n m, ?_, ?_⟩
    · calc (a0 + fcast n m) + (a0 + fcast n m)
          = (a0 + a0) + (fcast n m + fcast n m) := by abel
        _ = c := by rw [hmm, add_zero, ha0]
    · have hmod : (lv a0 p + m) % n = lv a0 p + m - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [lv_other_half m hm, hmod]
      omega

/-- **NEGATIVE CONTROL.** At even extent an ODD lag has no plane at all. The construction does not
extend to it because the geometry is absent, not because a proof is missing: that case is the LINK
reflection, whose fixed axis link `reflConf` inverts
(`reflLink_fixed_iff_axis`, `reflConf_inverts_fixed_axis_link`). -/
theorem odd_lag_has_no_plane (hn : Even n) {c : Fin n} (hc : ¬ Even c.val) :
    ¬ ∃ a : Fin n, a + a = c := by
  rintro ⟨a, ha⟩
  exact no_half_of_odd_val hn hc a ha

/-- At even extent, `c` odd makes `c − 1` even. -/
theorem even_sub_one_of_odd (hn : Even n) (h2 : 2 ≤ n) {c : Fin n} (hc : ¬ Even c.val) :
    Even (c - 1 : Fin n).val := by
  by_contra hodd
  have hone : ¬ Even (1 : Fin n).val := by
    have hv : (1 : Fin n).val = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt h2
    rw [hv]; decide
  have hiff : (Even (c - 1 : Fin n).val ↔ Even (1 : Fin n).val) :=
    ⟨fun h => absurd h hodd, fun h => absurd h hone⟩
  have hE : Even (((c - 1) + 1 : Fin n)).val := (fin_even_add hn (c - 1) 1).mpr hiff
  have hcc : ((c - 1) + 1 : Fin n) = c := by simp
  rw [hcc] at hE
  exact hc hE

/-- **NEGATIVE CONTROL, sharper.** An odd lag at even extent is a LINK reflection: it fixes an AXIS
link, and `reflConf_inverts_fixed_axis_link` shows `reflConf` sends that link's variable to its
inverse. So the shared block is acted on nontrivially, `hσR` of the weld fails, and the conditional
square has nothing to condition on. That case needs the Osterwalder–Seiler character expansion, which
is not here. -/
theorem odd_lag_has_fixed_axis_link (hn : Even n) (h2 : 2 ≤ n) {c : Fin n}
    (hc : ¬ Even c.val) : ∃ l : Link d n, l.1 = τ ∧ reflLink τ c l = l := by
  obtain ⟨x, hx⟩ := exists_fixed_site (even_sub_one_of_odd hn h2 hc)
  refine ⟨(τ, Function.update (fun _ => 0) τ x), rfl, ?_⟩
  refine (reflLink_fixed_iff_axis c _ rfl).mpr ?_
  simpa using hx.symm

/-- **`ReflectPositive.PlaqReflPositive`, DISCHARGED at even extent and even lag.**

No hypothesis remains except the geometry: the extent is even and the lag has a half. The
Osterwalder–Seiler pairing inequality for the `SU(N)` plaquette-energy observable is a theorem here,
not a citation. -/
theorem plaqReflPositive_of_even_lag (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    {c : Fin n} (hc : Even c.val) (q₀ : Plaq d n) (hq₀deg : ¬ (q₀.1.1 = τ ∧ q₀.1.2 = τ))
    (β : ℝ) : MassGap.ReflectPositive.PlaqReflPositive N τ c β q₀ := by
  obtain ⟨a', ha', hlv⟩ := exists_half_below m hm hm0 hc (q₀.2 τ)
  intro aC
  rw [← ha']
  exact wilson_expect_pairing_nonneg_even τ a' m hN hm hm0 q₀ hq₀deg hlv β aC

/-- **The lag correlation is NONNEGATIVE at every even lag of an even-extent lattice** — no
hypothesis, no citation. This is the first conjunct of `Complete.wilson_reflection_positive_at`,
proved on the lags the geometry covers. -/
theorem corrHyper_nonneg_even_lag (hN : N ≠ 0) (hm : n = 2 * m) (hm0 : 0 < m)
    {μ ν : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) {lag : Fin n} (hlag : Even lag.val) :
    0 ≤ MassGap.WilsonBridge.corrHyper (d := d) N n μ ν τ β lag :=
  MassGap.ReflectPositive.corrHyper_nonneg_of_reflPositive hN hμ hν β lag
    (plaqReflPositive_of_even_lag τ m hN hm hm0 hlag _ (fun h => hμ h.1) β)

end WilsonSplit

section Audit
#print axioms integrable_of_bounded
#print axioms integral_comp_of_mp
#print axioms prod_integral_nonneg
#print axioms twist_measurePreserving
#print axioms block_factor
#print axioms offBlock_disjoint
#print axioms pairing_nonneg_of_shared_block
#print axioms prod_integral_congr_inner
#print axioms measurable_halfIntegral
#print axioms abs_halfIntegral_le
#print axioms le_halfIntegral

#print axioms halfIntegral_sub_const
#print axioms pairing_eq_weighted_square
#print axioms integrable_weighted_halfIntegral_sq
#print axioms pairing_eq_zero_iff_halfIntegral
#print axioms pairing_pos_of_halfIntegral_ne
#print axioms NegControl.integral_coin
#print axioms NegControl.integral_gCoin
#print axioms NegControl.integral_gCoin_sq
#print axioms NegControl.coin_pairing_ne_sq
#print axioms NegControl.shared_block_inside_square_false
#print axioms even_mod_iff_even
#print axioms fin_even_add
#print axioms no_half_of_odd_val
#print axioms sub_one_odd_of_even
#print axioms exists_fixed_site
#print axioms reflSite_fixed_iff
#print axioms reflLink_fixed_iff_transverse
#print axioms reflLink_fixed_iff_axis
#print axioms no_fixed_axis_link
#print axioms exists_fixed_transverse_link
#print axioms pinned_exists_half
#print axioms pinned_exists_half_sub_one
#print axioms pinned_half_unique
#print axioms exists_fixed_axis_link_pinned
#print axioms reflConf_eq_twist
#print axioms axisDagger_measurePreserving
#print axioms reflConf_inverts_fixed_axis_link
#print axioms wilson_pairing_nonneg_of_shared_block
#print axioms pairing_nonneg_of_local
#print axioms glue_base_congr
#print axioms measurable_glue
#print axioms pairing_eq_zero_iff_local
#print axioms pairing_pos_iff_half_ne_const

#print axioms pairing_pos_iff_ne_const_of_indep_S
#print axioms halfIntegral_const_of_indep_R
#print axioms pairing_eq_zero_of_indep_R
#print axioms exists_of_eventually_of_frequently
#print axioms frequently_even_succ
#print axioms exists_even_extent_of_eventually
#print axioms exists_even_extent_aperture
#print axioms not_eventually_even_succ
#print axioms frequently_is_load_bearing
#print axioms fcast_add
#print axioms refl_transverse_level
#print axioms refl_axis_level
#print axioms mem_blkS_union_blkR
#print axioms mem_blkT_union_blkR
#print axioms blkS_disjoint_blkT
#print axioms blkR_fixed
#print axioms blkS_maps_blkT
#print axioms plaq_links_le
#print axioms plaq_links_ge
#print axioms plaq_links_plane
#print axioms plaq_side
#print axioms degenerate_axis_plaquette_straddles
#print axioms sum_plaq_split
#print axioms sum_plqDeg_zero
#print axioms density_reflConf
#print axioms reflPlaq_plus_mem_minus
#print axioms reflPlaq_minus_mem_plus
#print axioms sum_plqMinus_eq_plus_refl
#print axioms action_eq_split
#print axioms integrand_eq_paired
#print axioms obsPlus_local
#print axioms wPlane_local
#print axioms wilson_pairing_nonneg_even
#print axioms wilson_expect_pairing_nonneg_even
#print axioms lv_other_half
#print axioms exists_half_below
#print axioms odd_lag_has_no_plane
#print axioms even_sub_one_of_odd
#print axioms odd_lag_has_fixed_axis_link
#print axioms plaqReflPositive_of_even_lag
#print axioms corrHyper_nonneg_even_lag
end Audit

end MassGap.ActionSplit
