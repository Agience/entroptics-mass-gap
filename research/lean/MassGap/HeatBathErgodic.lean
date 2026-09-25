import Mathlib
import MassGap.HeatBathGapDecay
import MassGap.HeatBath

noncomputable section

/-!
# MassGap.HeatBathErgodic — the lazy heat bath is ergodic at every finite volume

## What it gives

1. **Squares against a probability measure.** `hb_integral_sub_const_sq`:
   `∫ (f − c)² = ∫ f² − 2c ∫ f + c²`; `hb_sq_integral_le` (Jensen for the square) and
   `hb_integral_sub_mean_sq_le` (the mean minimises the centred square).
2. **The Haar average at one link.** `havg l φ W = ∫ φ(W[l ↦ g]) dg` against the probability Haar
   measure: continuous (`continuous_havg`), not reading `l` (`havg_update`), keeping every other link
   a function does not read (`havg_update_other`), preserving the product Haar integral
   (`integral_havg`), linear (`havg_sub`), an `L²` contraction (`integral_havg_sq_le`), and the best
   `L²` approximation among functions not reading `l` (`havg_integral_min`).
3. **The sweep.** `sweep L φ` applies the Haar averages of the links of the list `L`. Its value does
   not read any link of `L` (`sweep_readsNot`); a function reading no link is constant
   (`eq_of_readsNot_all`); the sweep keeps the Haar integral (`integral_sweep`); and
   `∫ (φ − sweep L φ)² ≤ (2^{|L|+1} − 2) Σ_l ∫ (φ − havg l φ)²` (`sweep_energy`).
4. **The Poincaré inequality of a finite Wilson system.** `heat_poincare`: for every finite Wilson
   system at every real `β` there is `C ≥ 0` with
   `⟨φ²⟩ − ⟨φ⟩² ≤ C Σ_l ⟨(φ − heatAvg l φ)²⟩` for every continuous `φ`. The proof compares the Wilson
   measure with the product Haar measure, whose density lies between `e^{∓2|β||P|}`
   (`wt_bounds`), bounds the Haar variance by the sweep, and each Haar-average defect by the
   heat-bath defect (`havg_integral_min`).
5. **Ergodicity of the lazy heat bath.** `ergodicLimit_of_poincare`: on a patch system with a unit
   vector `u` (`B(u, u) = 1`, `B(Hv, u) = 0`) and a Poincaré inequality
   `B(v, v) − B(v, u)² ≤ C B(Hv, v)`, the lazy heat bath at `K = |ι| + 1` has
   `B(Tᴹ f, g) → B(f, u) B(g, u)`. The variance of `Tᴹ f` contracts by `1 − (K(C + 1))⁻¹` per step
   (`Tstep_form`), and `tendsto_of_sq_le` turns the geometric bound into the limit.

## The literature

The comparison of Poincaré constants under a bounded change of density is R. Holley,
D. Stroock, J. Stat. Phys. 46 (1987) 1159–1194, Lemma on bounded perturbations; the telescoping bound
of a product-measure variance by coordinate defects is the Efron–Stein inequality in its crude form
(B. Efron, C. Stein, Ann. Statist. 9 (1981) 586–596). Every constant here depends on the volume,
which is all the ergodic limit asks.
-/

namespace MassGap.HeatBathErgodic

open MeasureTheory Filter
open MassGap.HeatBath MassGap.KnabeCriterion MassGap.HeatBathGapDecay
open MassGap.WilsonLattice (wilsonSystem)
open MassGap.WilsonAction (wilsonDensity)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

/-! ## 1. Squares against a probability measure -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The centred square**: `∫ (f − c)² = ∫ f² − 2c ∫ f + c²` against a probability measure.

DERIVED: `2` is the square and its cross term. -/
theorem hb_integral_sub_const_sq {f : Ω → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (c : ℝ) :
    ∫ x, (f x - c) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - 2 * c * ∫ x, f x ∂μ + c ^ 2 := by
  have i1 : Integrable (fun x => f x ^ 2 - 2 * c * f x) μ := hf2.sub (hf.const_mul (2 * c))
  have i2 : Integrable (fun x => 2 * c * f x) μ := hf.const_mul (2 * c)
  have e : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - 2 * c * f x) + c ^ 2 := by
    funext x
    ring
  rw [e, integral_add i1 (integrable_const _), integral_sub hf2 i2, integral_const_mul,
    integral_const, probReal_univ, one_smul]

#print axioms hb_integral_sub_const_sq

/-- **Jensen for the square**: `(∫ f)² ≤ ∫ f²` against a probability measure.

DERIVED: `2` is the square. -/
theorem hb_sq_integral_le {f : Ω → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [hb_integral_sub_const_sq hf hf2] at h0
  nlinarith [h0]

#print axioms hb_sq_integral_le

/-- **The mean minimises the centred square**: `∫ (f − ∫ f)² ≤ ∫ (f − b)²` for every constant `b`.

DERIVED: `2` is the square. -/
theorem hb_integral_sub_mean_sq_le {f : Ω → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (b : ℝ) :
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ ∫ x, (f x - b) ^ 2 ∂μ := by
  rw [hb_integral_sub_const_sq hf hf2, hb_integral_sub_const_sq hf hf2]
  nlinarith [sq_nonneg (∫ y, f y ∂μ - b)]

#print axioms hb_integral_sub_mean_sq_le

end Prob

/-! ## 2. The Haar average at one link -/

/-- **The product Haar measure** on the configurations of a finite link set.

DERIVED: no numeral. -/
abbrev piHaar (N : ℕ) (Lk : Type) [Fintype Lk] : Measure (Lk → SU N) :=
  Measure.pi fun _ : Lk => probHaar (SU N)

/-- The product Haar measure is a probability measure.

DERIVED: no numeral. -/
instance piHaar_isProbabilityMeasure (N : ℕ) (Lk : Type) [Fintype Lk] :
    IsProbabilityMeasure (piHaar N Lk) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Lk => probHaar (SU N)))

section Haar

variable {N : ℕ} {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- A continuous function of a finite configuration is integrable against the product Haar measure
(`HeatBath.exists_abs_le`, `HeatBath.integrable_of_abs_le`).

DERIVED: no numeral. -/
theorem haar_integrable {F : (Lk → SU N) → ℝ} (hF : Continuous F) :
    Integrable F (piHaar N Lk) := by
  obtain ⟨C, hC⟩ := exists_abs_le hF
  exact integrable_of_abs_le _ hF.measurable hC

#print axioms haar_integrable

/-- The one-link section `g ↦ φ(W[l ↦ g])` of a continuous `φ` is Haar integrable.

DERIVED: no numeral. -/
theorem integrable_comp_update (l : Lk) {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ)
    (W : Lk → SU N) :
    Integrable (fun g => φ (Function.update W l g)) (probHaar (SU N)) := by
  obtain ⟨C, hC⟩ := exists_abs_le hφ
  exact integrable_of_abs_le _ (hφ.comp (continuous_const.update l continuous_id)).measurable
    (fun g => hC _)

#print axioms integrable_comp_update

/-- **The Haar average at the link `l`**: `havg l φ W = ∫ φ(W[l ↦ g]) dg`.

DERIVED: no numeral. -/
def havg (l : Lk) (φ : (Lk → SU N) → ℝ) (W : Lk → SU N) : ℝ :=
  ∫ g, φ (Function.update W l g) ∂(probHaar (SU N))

/-- The Haar average of a continuous function is continuous (`continuous_of_dominated`).

DERIVED: no numeral. -/
theorem continuous_havg (l : Lk) {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ) :
    Continuous (havg l φ) := by
  obtain ⟨C, hC⟩ := exists_abs_le hφ
  show Continuous (fun W => ∫ g, φ (Function.update W l g) ∂(probHaar (SU N)))
  refine continuous_of_dominated (bound := fun _ => C) (fun W => ?_) (fun W => ?_)
    (integrable_const C) ?_
  · exact (hφ.comp (continuous_const.update l continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun g => by rw [Real.norm_eq_abs]; exact hC _)
  · exact Filter.Eventually.of_forall (fun g => hφ.comp (continuous_id.update l continuous_const))

#print axioms continuous_havg

/-- The Haar average does not read the link `l` (`Function.update_idem`).

DERIVED: no numeral. -/
theorem havg_update (l : Lk) (φ : (Lk → SU N) → ℝ) (W : Lk → SU N) (h : SU N) :
    havg l φ (Function.update W l h) = havg l φ W := by
  simp only [havg, Function.update_idem]

#print axioms havg_update

/-- **The Haar average keeps the other links a function does not read**: if `φ` does not read
`l' ≠ l`, neither does `havg l φ` (`Function.update_comm`).

DERIVED: no numeral. -/
theorem havg_update_other {l l' : Lk} (hll : l ≠ l') {φ : (Lk → SU N) → ℝ}
    (hφ : ∀ W g, φ (Function.update W l' g) = φ W) (W : Lk → SU N) (h : SU N) :
    havg l φ (Function.update W l' h) = havg l φ W := by
  unfold havg
  refine integral_congr_ae (Filter.Eventually.of_forall (fun g => ?_))
  show φ (Function.update (Function.update W l' h) l g) = φ (Function.update W l g)
  rw [Function.update_comm (Ne.symm hll) h g W, hφ]

#print axioms havg_update_other

/-- **The Haar average keeps the product Haar integral** (`HeatBath.integral_eq_integral_update`).

DERIVED: no numeral. -/
theorem integral_havg (l : Lk) {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ) :
    ∫ W, havg l φ W ∂(piHaar N Lk) = ∫ W, φ W ∂(piHaar N Lk) := by
  obtain ⟨C, hC⟩ := exists_abs_le hφ
  exact (integral_eq_integral_update (probHaar (SU N)) l φ hφ.measurable hC).symm

#print axioms integral_havg

/-- The Haar average is additive on continuous functions: `havg (φ − ψ) = havg φ − havg ψ`.

DERIVED: no numeral. -/
theorem havg_sub (l : Lk) {φ ψ : (Lk → SU N) → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (W : Lk → SU N) : havg l (fun V => φ V - ψ V) W = havg l φ W - havg l ψ W :=
  integral_sub (integrable_comp_update l hφ W) (integrable_comp_update l hψ W)

#print axioms havg_sub

/-- **Jensen at one link**: `(havg l u)² ≤ havg l (u²)` (`hb_sq_integral_le`).

DERIVED: `2` is the square. -/
theorem havg_sq_le (l : Lk) {u : (Lk → SU N) → ℝ} (hu : Continuous u) (W : Lk → SU N) :
    havg l u W ^ 2 ≤ havg l (fun V => u V ^ 2) W :=
  hb_sq_integral_le (integrable_comp_update l hu W) (integrable_comp_update l (hu.pow 2) W)

#print axioms havg_sq_le

/-- **The Haar average is an `L²` contraction**: `∫ (havg l u)² ≤ ∫ u²` (`havg_sq_le`,
`integral_havg`).

DERIVED: `2` is the square. -/
theorem integral_havg_sq_le (l : Lk) {u : (Lk → SU N) → ℝ} (hu : Continuous u) :
    ∫ W, havg l u W ^ 2 ∂(piHaar N Lk) ≤ ∫ W, u W ^ 2 ∂(piHaar N Lk) := by
  have h1 : Continuous (fun W => havg l u W ^ 2) := (continuous_havg l hu).pow 2
  have h2 : Continuous (havg l (fun V => u V ^ 2)) := continuous_havg l (hu.pow 2)
  calc ∫ W, havg l u W ^ 2 ∂(piHaar N Lk)
      ≤ ∫ W, havg l (fun V => u V ^ 2) W ∂(piHaar N Lk) :=
        integral_mono (haar_integrable h1) (haar_integrable h2)
          (fun W => havg_sq_le l hu W)
    _ = ∫ W, u W ^ 2 ∂(piHaar N Lk) := integral_havg l (hu.pow 2)

#print axioms integral_havg_sq_le

/-- **The Haar average is the best approximation at one link, fibrewise**: for `w` not reading `l`,
`havg l ((u − havg l u)²) ≤ havg l ((u − w)²)` (`hb_integral_sub_mean_sq_le`).

DERIVED: `2` is the square. -/
theorem havg_min_pt (l : Lk) {u w : (Lk → SU N) → ℝ} (hu : Continuous u)
    (hw : ∀ W g, w (Function.update W l g) = w W) (W : Lk → SU N) :
    havg l (fun V => (u V - havg l u V) ^ 2) W ≤ havg l (fun V => (u V - w V) ^ 2) W := by
  have e1 : havg l (fun V => (u V - havg l u V) ^ 2) W
      = ∫ g, (u (Function.update W l g)
          - ∫ g', u (Function.update W l g') ∂(probHaar (SU N))) ^ 2 ∂(probHaar (SU N)) := by
    simp only [havg, Function.update_idem]
  have e2 : havg l (fun V => (u V - w V) ^ 2) W
      = ∫ g, (u (Function.update W l g) - w W) ^ 2 ∂(probHaar (SU N)) := by
    simp only [havg, hw]
  rw [e1, e2]
  exact hb_integral_sub_mean_sq_le (integrable_comp_update l hu W)
    (integrable_comp_update l (hu.pow 2) W) (w W)

#print axioms havg_min_pt

/-- **The Haar average is the best approximation at one link**: for continuous `w` not reading `l`,
`∫ (u − havg l u)² ≤ ∫ (u − w)²` against the product Haar measure (`havg_min_pt`,
`integral_havg`).

DERIVED: `2` is the square. -/
theorem havg_integral_min (l : Lk) {u w : (Lk → SU N) → ℝ} (hu : Continuous u)
    (hwc : Continuous w) (hw : ∀ W g, w (Function.update W l g) = w W) :
    ∫ W, (u W - havg l u W) ^ 2 ∂(piHaar N Lk) ≤ ∫ W, (u W - w W) ^ 2 ∂(piHaar N Lk) := by
  have c1 : Continuous (fun V => (u V - havg l u V) ^ 2) := (hu.sub (continuous_havg l hu)).pow 2
  have c2 : Continuous (fun V => (u V - w V) ^ 2) := (hu.sub hwc).pow 2
  calc ∫ W, (u W - havg l u W) ^ 2 ∂(piHaar N Lk)
      = ∫ W, havg l (fun V => (u V - havg l u V) ^ 2) W ∂(piHaar N Lk) :=
        (integral_havg l c1).symm
    _ ≤ ∫ W, havg l (fun V => (u V - w V) ^ 2) W ∂(piHaar N Lk) :=
        integral_mono (haar_integrable (continuous_havg l c1))
          (haar_integrable (continuous_havg l c2)) (fun W => havg_min_pt l hu hw W)
    _ = ∫ W, (u W - w W) ^ 2 ∂(piHaar N Lk) := integral_havg l c2

#print axioms havg_integral_min

/-! ## 3. The sweep -/

/-- **The sweep** along a list of links: `sweep [] φ = φ`, `sweep (l :: L) φ = havg l (sweep L φ)`.

DERIVED: no numeral. -/
def sweep : List Lk → ((Lk → SU N) → ℝ) → (Lk → SU N) → ℝ
  | [], φ => φ
  | l :: L, φ => havg l (sweep L φ)

/-- The sweep of a continuous function is continuous (`continuous_havg`).

DERIVED: no numeral. -/
theorem continuous_sweep {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ) (L : List Lk) :
    Continuous (sweep L φ) := by
  induction L with
  | nil => exact hφ
  | cons a L ih =>
    show Continuous (havg a (sweep L φ))
    exact continuous_havg a ih

#print axioms continuous_sweep

/-- **The sweep reads no link of its list** (`havg_update`, `havg_update_other`).

DERIVED: no numeral. -/
theorem sweep_readsNot (φ : (Lk → SU N) → ℝ) (L : List Lk) :
    ∀ l ∈ L, ∀ (W : Lk → SU N) (g : SU N), sweep L φ (Function.update W l g) = sweep L φ W := by
  induction L with
  | nil =>
    intro l hl
    simp at hl
  | cons a L ih =>
    intro l hl W g
    show havg a (sweep L φ) (Function.update W l g) = havg a (sweep L φ) W
    by_cases hal : a = l
    · rw [← hal]
      exact havg_update a (sweep L φ) W g
    · have hlL : l ∈ L := by
        rcases List.mem_cons.mp hl with h | h
        · exact absurd h.symm hal
        · exact h
      exact havg_update_other hal (ih l hlL) W g

#print axioms sweep_readsNot

/-- **A function reading no link is constant**: update the links of `V` into `W` one at a time
(`Finset.induction_on`).

DERIVED: no numeral. -/
theorem eq_of_readsNot_all {F : (Lk → SU N) → ℝ}
    (hF : ∀ l W g, F (Function.update W l g) = F W) (W V : Lk → SU N) : F W = F V := by
  have key : ∀ s : Finset Lk, F (fun l => if l ∈ s then V l else W l) = F W := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s _ ih
      show F (fun l => if l ∈ insert a s then V l else W l) = F W
      have e : (fun l => if l ∈ insert a s then V l else W l)
          = Function.update (fun l => if l ∈ s then V l else W l) a (V a) := by
        funext l
        by_cases hl : l = a
        · subst hl
          simp
        · simp [Function.update_of_ne hl, hl]
      rw [e]
      exact (hF a _ (V a)).trans ih
  have hV : (fun l => if l ∈ (Finset.univ : Finset Lk) then V l else W l) = V := by
    funext l
    simp
  have h := key Finset.univ
  rw [hV] at h
  exact h.symm

#print axioms eq_of_readsNot_all

/-- **The sweep keeps the product Haar integral** (`integral_havg`).

DERIVED: no numeral. -/
theorem integral_sweep {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ) (L : List Lk) :
    ∫ W, sweep L φ W ∂(piHaar N Lk) = ∫ W, φ W ∂(piHaar N Lk) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show ∫ W, havg a (sweep L φ) W ∂(piHaar N Lk) = _
    rw [integral_havg a (continuous_sweep hφ L), ih]

#print axioms integral_sweep

/-- **The energy of a sweep**: `∫ (φ − sweep L φ)² ≤ (2^{|L|+1} − 2) Σ_l ∫ (φ − havg l φ)²`.
One step writes `φ − havg a (sweep L φ) = (φ − havg a φ) + havg a (φ − sweep L φ)` (`havg_sub`),
uses `(x + y)² ≤ 2x² + 2y²` and the contraction `integral_havg_sq_le`.

DERIVED: `2` is the square, the factor of `(x + y)² ≤ 2x² + 2y²` and the base of the constant; `1`
is the shift making the constant vanish on the empty list. -/
theorem sweep_energy {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ) (L : List Lk) :
    ∫ W, (φ W - sweep L φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ((2 : ℝ) ^ (L.length + 1) - 2) * ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk) := by
  have hS : 0 ≤ ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk) :=
    Finset.sum_nonneg (fun l _ => integral_nonneg (fun W => sq_nonneg _))
  induction L with
  | nil =>
    have e : ∫ W, (φ W - sweep [] φ W) ^ 2 ∂(piHaar N Lk) = 0 := by
      simp [sweep]
    rw [e]
    norm_num
  | cons a L ih =>
    have hc : Continuous (sweep L φ) := continuous_sweep hφ L
    have hca : Continuous (havg a φ) := continuous_havg a hφ
    have hd : Continuous (fun V => φ V - sweep L φ V) := hφ.sub hc
    have hpt : ∀ W, (φ W - sweep (a :: L) φ W) ^ 2
        ≤ 2 * (φ W - havg a φ W) ^ 2 + 2 * havg a (fun V => φ V - sweep L φ V) W ^ 2 := by
      intro W
      show (φ W - havg a (sweep L φ) W) ^ 2 ≤ _
      rw [havg_sub a hφ hc W]
      nlinarith [sq_nonneg (φ W - havg a φ W - (havg a φ W - havg a (sweep L φ) W))]
    have i1 : Integrable (fun W => (φ W - sweep (a :: L) φ W) ^ 2) (piHaar N Lk) :=
      haar_integrable ((hφ.sub (continuous_sweep hφ (a :: L))).pow 2)
    have i2 : Integrable (fun W => 2 * (φ W - havg a φ W) ^ 2) (piHaar N Lk) :=
      haar_integrable (continuous_const.mul ((hφ.sub hca).pow 2))
    have i3 : Integrable (fun W => 2 * havg a (fun V => φ V - sweep L φ V) W ^ 2) (piHaar N Lk) :=
      haar_integrable (continuous_const.mul ((continuous_havg a hd).pow 2))
    have i23 : Integrable (fun W => 2 * (φ W - havg a φ W) ^ 2
        + 2 * havg a (fun V => φ V - sweep L φ V) W ^ 2) (piHaar N Lk) := i2.add i3
    have h1 := integral_mono i1 i23 hpt
    rw [integral_add i2 i3, integral_const_mul, integral_const_mul] at h1
    have h2 := integral_havg_sq_le a hd
    have h3 : ∫ W, (φ W - havg a φ W) ^ 2 ∂(piHaar N Lk)
        ≤ ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk) :=
      Finset.single_le_sum (f := fun l => ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk))
        (fun l _ => integral_nonneg (fun W => sq_nonneg _)) (Finset.mem_univ a)
    simp only [List.length_cons]
    rw [pow_succ (2 : ℝ) (L.length + 1)]
    nlinarith [ih, h1, h2, h3, hS]

#print axioms sweep_energy

/-! ## 4. The Poincaré inequality of a finite Wilson system -/

/-- **The Wilson weight between two constants**: `e^{−2|β||P|} ≤ e^{−βS} ≤ e^{2|β||P|}`, from
`0 ≤ S ≤ 2|P|` (`WilsonReal.wilsonSystem_action_nonneg`, `WilsonReal.wilsonSystem_action_le`).

DERIVED: `2` is the largest plaquette action; `0` is the excluded rank in `hN`. -/
theorem wt_bounds (hN : N ≠ 0) {Pq : Type} [Fintype Pq] (bd : Pq → List (Lk × Bool)) (β : ℝ)
    (W : Lk → SU N) :
    Real.exp (-(|β| * (2 * (Fintype.card Pq : ℝ)))) ≤ wt bd β W
      ∧ wt bd β W ≤ Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))) := by
  have h0 := MassGap.WilsonReal.wilsonSystem_action_nonneg hN bd W
  have h2 := MassGap.WilsonReal.wilsonSystem_action_le hN bd W
  have e : wt bd β W
      = Real.exp (-β * (wilsonSystem bd (wilsonDensity (N := N))).action W) := rfl
  have hb1 : β * (wilsonSystem bd (wilsonDensity (N := N))).action W
      ≤ |β| * (wilsonSystem bd (wilsonDensity (N := N))).action W :=
    mul_le_mul_of_nonneg_right (le_abs_self β) h0
  have hb2 : -β * (wilsonSystem bd (wilsonDensity (N := N))).action W
      ≤ |β| * (wilsonSystem bd (wilsonDensity (N := N))).action W :=
    mul_le_mul_of_nonneg_right (neg_le_abs β) h0
  have hb3 : |β| * (wilsonSystem bd (wilsonDensity (N := N))).action W
      ≤ |β| * (2 * (Fintype.card Pq : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg β)
  rw [e]
  constructor
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_le_exp.mpr (by linarith)

#print axioms wt_bounds

/-- **The variance against a centred square**: at `0 < Z` and `Ic = I₂ − 2c I₁ + c² Z`,
`I₂/Z − (I₁/Z)² ≤ Ic/Z`.

DERIVED: `2` is the square and its cross term; `0` is the sign of the normaliser `Z`. -/
theorem var_le_of {I2 I1 Ic Z c : ℝ} (hZ : 0 < Z) (hA : Ic = I2 - 2 * c * I1 + c ^ 2 * Z) :
    I2 / Z - (I1 / Z) ^ 2 ≤ Ic / Z := by
  rw [hA]
  have e1 : (I2 - 2 * c * I1 + c ^ 2 * Z) / Z = I2 / Z - 2 * c * (I1 / Z) + c ^ 2 * (Z / Z) := by
    ring
  rw [e1, div_self hZ.ne', mul_one]
  nlinarith [sq_nonneg (I1 / Z - c)]

#print axioms var_le_of

/-- **The chain of comparisons** of `heat_poincare`, as real arithmetic.

DERIVED: `0` is the sign of the constants. -/
theorem chain_le {Var Ic Z whi J K2 D Ee wlo X : ℝ} (hZ : 0 < Z) (hwhi : 0 ≤ whi)
    (hK2 : 0 ≤ K2) (hwlo : 0 < wlo) (h1 : Var ≤ Ic / Z) (h2 : Ic ≤ whi * J)
    (h3 : J ≤ K2 * D) (h4 : D ≤ Ee) (h5 : wlo * Ee ≤ X) :
    Var ≤ K2 * (whi / wlo) * (X / Z) := by
  have hEe : Ee ≤ X / wlo := by
    rw [le_div_iff₀ hwlo]
    linarith
  have hJ : J ≤ K2 * (X / wlo) := h3.trans (mul_le_mul_of_nonneg_left (h4.trans hEe) hK2)
  have hIc : Ic ≤ whi * (K2 * (X / wlo)) := h2.trans (mul_le_mul_of_nonneg_left hJ hwhi)
  have hdiv : Ic / Z ≤ whi * (K2 * (X / wlo)) / Z := div_le_div_of_nonneg_right hIc hZ.le
  have e : whi * (K2 * (X / wlo)) / Z = K2 * (whi / wlo) * (X / Z) := by ring
  linarith [h1, hdiv, e]

#print axioms chain_le

/-- **THE POINCARÉ INEQUALITY OF A FINITE WILSON SYSTEM.** For every finite Wilson system
`wilsonSystem bd wilsonDensity` over `SU(N)`, `N ≠ 0`, at every real `β`, some `C ≥ 0` has, for
every continuous `φ`,

    ⟨φ²⟩ − ⟨φ⟩² ≤ C Σ_l ⟨(φ − heatAvg bd β l φ)²⟩.

With `ν` the product Haar measure, `c = ∫ φ dν` and weights `w₋ ≤ e^{−βS} ≤ w₊` (`wt_bounds`):
the variance is at most `⟨(φ − c)²⟩ ≤ (w₊/Z) ∫ (φ − c)² dν` (`var_le_of`); the full sweep of `φ`
is the constant `c` (`sweep_readsNot`, `eq_of_readsNot_all`, `integral_sweep`), so
`∫ (φ − c)² dν ≤ 2^{|L|+1} Σ_l ∫ (φ − havg l φ)² dν` (`sweep_energy`); each Haar defect is at most
the heat-bath defect (`havg_integral_min`, `HeatBath.heatAvg_update`), and
`w₋ ∫ (φ − heatAvg l φ)² dν ≤ Z ⟨(φ − heatAvg l φ)²⟩`. The constant is
`2^{|L|+1} w₊/w₋`, with `|L|` the number of links. It depends on the volume through `|L|` and the
plaquette count `|P|` (`w₊/w₋ = e^{4|β||P|}`); `ergodicLimit_of_poincare` uses it at one fixed
volume, where no uniformity is asked.

DERIVED: `0` is the excluded rank in `hN` and the sign of `C`; `2` is the square. -/
theorem heat_poincare (hN : N ≠ 0) {Pq : Type} [Fintype Pq] (bd : Pq → List (Lk × Bool))
    (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : (Lk → SU N) → ℝ, Continuous φ →
      (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β (fun W => φ W * φ W)
          - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β φ ^ 2
        ≤ C * ∑ l, (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
            (fun W => (φ W - heatAvg bd β l φ W) ^ 2) := by
  obtain ⟨wlo, hwlo⟩ : ∃ w : ℝ, w = Real.exp (-(|β| * (2 * (Fintype.card Pq : ℝ)))) := ⟨_, rfl⟩
  obtain ⟨whi, hwhi⟩ : ∃ w : ℝ, w = Real.exp (|β| * (2 * (Fintype.card Pq : ℝ))) := ⟨_, rfl⟩
  have hwlo0 : 0 < wlo := by
    rw [hwlo]
    exact Real.exp_pos _
  have hwhi0 : 0 < whi := by
    rw [hwhi]
    exact Real.exp_pos _
  have hwb : ∀ W : Lk → SU N, wlo ≤ wt bd β W ∧ wt bd β W ≤ whi := by
    intro W
    rw [hwlo, hwhi]
    exact wt_bounds hN bd β W
  obtain ⟨L0, hL0⟩ : ∃ L : List Lk, L = (Finset.univ : Finset Lk).toList := ⟨_, rfl⟩
  have hmem : ∀ l, l ∈ L0 := fun l => by
    rw [hL0]
    exact Finset.mem_toList.mpr (Finset.mem_univ l)
  obtain ⟨K2, hK2⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ (L0.length + 1) := ⟨_, rfl⟩
  have hK20 : 0 ≤ K2 := by
    rw [hK2]
    positivity
  refine ⟨K2 * (whi / wlo), mul_nonneg hK20 (div_nonneg hwhi0.le hwlo0.le), fun φ hφ => ?_⟩
  have hZ : 0 < ∫ W, wt bd β W ∂(piHaar N Lk) :=
    MassGap.WilsonReal.wilsonSystem_partition_pos hN bd β
  have hE : ∀ O : (Lk → SU N) → ℝ,
      (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β O
        = (∫ W, O W * wt bd β W ∂(piHaar N Lk)) / ∫ W, wt bd β W ∂(piHaar N Lk) :=
    fun O => rfl
  have hcw : Continuous (wt (N := N) bd β) := continuous_wt bd β
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ W, φ W ∂(piHaar N Lk) := ⟨_, rfl⟩
  -- (a) the variance against the centred square
  have iφ : Integrable (fun W => φ W * wt bd β W) (piHaar N Lk) :=
    haar_integrable (hφ.mul hcw)
  have iφφ : Integrable (fun W => φ W * φ W * wt bd β W) (piHaar N Lk) :=
    haar_integrable ((hφ.mul hφ).mul hcw)
  have iw : Integrable (fun W => wt bd β W) (piHaar N Lk) := haar_integrable hcw
  have i2c : Integrable (fun W => 2 * c * (φ W * wt bd β W)) (piHaar N Lk) :=
    iφ.const_mul (2 * c)
  have i1 : Integrable (fun W => φ W * φ W * wt bd β W - 2 * c * (φ W * wt bd β W))
      (piHaar N Lk) := iφφ.sub i2c
  have icw : Integrable (fun W => c ^ 2 * wt bd β W) (piHaar N Lk) := iw.const_mul (c ^ 2)
  have hA : ∫ W, (φ W - c) ^ 2 * wt bd β W ∂(piHaar N Lk)
      = ∫ W, φ W * φ W * wt bd β W ∂(piHaar N Lk)
          - 2 * c * ∫ W, φ W * wt bd β W ∂(piHaar N Lk)
        + c ^ 2 * ∫ W, wt bd β W ∂(piHaar N Lk) := by
    have e : (fun W => (φ W - c) ^ 2 * wt bd β W)
        = fun W => (φ W * φ W * wt bd β W - 2 * c * (φ W * wt bd β W)) + c ^ 2 * wt bd β W := by
      funext W
      ring
    rw [e, integral_add i1 icw, integral_sub iφφ i2c, integral_const_mul, integral_const_mul]
  have hVar : (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => φ W * φ W)
        - (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β φ ^ 2
      ≤ (∫ W, (φ W - c) ^ 2 * wt bd β W ∂(piHaar N Lk)) / ∫ W, wt bd β W ∂(piHaar N Lk) := by
    rw [hE, hE]
    exact var_le_of hZ hA
  -- (b) the weight against the Haar measure, from above
  have hB : ∫ W, (φ W - c) ^ 2 * wt bd β W ∂(piHaar N Lk)
      ≤ whi * ∫ W, (φ W - c) ^ 2 ∂(piHaar N Lk) := by
    rw [← integral_const_mul]
    refine integral_mono (haar_integrable (((hφ.sub continuous_const).pow 2).mul hcw))
      (haar_integrable (continuous_const.mul ((hφ.sub continuous_const).pow 2)))
      (fun W => ?_)
    have h1 := (hwb W).2
    have h2 := sq_nonneg (φ W - c)
    show (φ W - c) ^ 2 * wt bd β W ≤ whi * (φ W - c) ^ 2
    nlinarith
  -- (c) the sweep
  have hread : ∀ l W g, sweep L0 φ (Function.update W l g) = sweep L0 φ W :=
    fun l => sweep_readsNot φ L0 l (hmem l)
  have hconst : ∀ W, sweep L0 φ W = c := by
    intro W
    have h1 : ∫ V, sweep L0 φ V ∂(piHaar N Lk) = ∫ _V, sweep L0 φ W ∂(piHaar N Lk) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun V => eq_of_readsNot_all hread V W))
    rw [integral_const, probReal_univ, one_smul, integral_sweep hφ L0, ← hc] at h1
    exact h1.symm
  have hJ : ∫ W, (φ W - c) ^ 2 ∂(piHaar N Lk)
      ≤ K2 * ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk) := by
    have hS := sweep_energy hφ L0
    have hS0 : 0 ≤ ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk) :=
      Finset.sum_nonneg (fun l _ => integral_nonneg (fun W => sq_nonneg _))
    have e : (fun W => (φ W - c) ^ 2) = fun W => (φ W - sweep L0 φ W) ^ 2 := by
      funext W
      rw [hconst W]
    rw [e, hK2]
    nlinarith [hS, hS0]
  -- (d) the Haar defect against the heat-bath defect
  have hD : ∀ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∫ W, (φ W - heatAvg bd β l φ W) ^ 2 ∂(piHaar N Lk) :=
    fun l => havg_integral_min l hφ (continuous_heatAvg bd β l hφ)
      (fun W g => heatAvg_update bd β l φ W g)
  -- (e) the Haar measure against the weight, from below
  have hF : ∀ l, wlo * ∫ W, (φ W - heatAvg bd β l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∫ W, (φ W - heatAvg bd β l φ W) ^ 2 * wt bd β W ∂(piHaar N Lk) := by
    intro l
    have hcont : Continuous (fun W => (φ W - heatAvg bd β l φ W) ^ 2) :=
      (hφ.sub (continuous_heatAvg bd β l hφ)).pow 2
    rw [← integral_const_mul]
    refine integral_mono (haar_integrable (continuous_const.mul hcont))
      (haar_integrable (hcont.mul hcw)) (fun W => ?_)
    have h1 := (hwb W).1
    have h2 := sq_nonneg (φ W - heatAvg bd β l φ W)
    show wlo * (φ W - heatAvg bd β l φ W) ^ 2 ≤ (φ W - heatAvg bd β l φ W) ^ 2 * wt bd β W
    nlinarith
  -- (f) the chain
  have hsumD : ∑ l, ∫ W, (φ W - havg l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∑ l, ∫ W, (φ W - heatAvg bd β l φ W) ^ 2 ∂(piHaar N Lk) :=
    Finset.sum_le_sum (fun l _ => hD l)
  have hsumF : wlo * ∑ l, ∫ W, (φ W - heatAvg bd β l φ W) ^ 2 ∂(piHaar N Lk)
      ≤ ∑ l, ∫ W, (φ W - heatAvg bd β l φ W) ^ 2 * wt bd β W ∂(piHaar N Lk) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun l _ => hF l)
  have hgoal := chain_le hZ hwhi0.le hK20 hwlo0 hVar hB hJ hsumD hsumF
  have hsumE : ∑ l, (wilsonSystem bd (wilsonDensity (N := N))).expect (probHaar (SU N)) β
        (fun W => (φ W - heatAvg bd β l φ W) ^ 2)
      = (∑ l, ∫ W, (φ W - heatAvg bd β l φ W) ^ 2 * wt bd β W ∂(piHaar N Lk))
        / ∫ W, wt bd β W ∂(piHaar N Lk) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun l _ => hE _)
  rw [hsumE]
  exact hgoal

#print axioms heat_poincare

end Haar

/-! ## 5. Ergodicity of the lazy heat bath -/

section Ergodic

/-- **A geometric square bound gives the limit**: `(a_M − L)² ≤ q^M Y` with `0 ≤ q < 1` gives
`a_M → L` (`Real.abs_le_sqrt`, `tendsto_of_tendsto_of_tendsto_of_le_of_le`).

DERIVED: `0` is the lower end of `q` and the limit of `q^M`; `1` is the upper bound on `q`; `2`
is the square. -/
theorem tendsto_of_sq_le {a : ℕ → ℝ} {L q Y : ℝ} (h0 : 0 ≤ q) (h1 : q < 1)
    (h : ∀ M, (a M - L) ^ 2 ≤ q ^ M * Y) : Tendsto a atTop (nhds L) := by
  have hb : Tendsto (fun M : ℕ => Real.sqrt (q ^ M * Y)) atTop (nhds 0) := by
    have h2 := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const Y).sqrt
    rwa [zero_mul, Real.sqrt_zero] at h2
  have hlo : Tendsto (fun M : ℕ => L - Real.sqrt (q ^ M * Y)) atTop (nhds L) := by
    have h3 : Tendsto (fun M : ℕ => L - Real.sqrt (q ^ M * Y)) atTop (nhds (L - 0)) :=
      tendsto_const_nhds.sub hb
    rwa [sub_zero] at h3
  have hhi : Tendsto (fun M : ℕ => L + Real.sqrt (q ^ M * Y)) atTop (nhds L) := by
    have h3 : Tendsto (fun M : ℕ => L + Real.sqrt (q ^ M * Y)) atTop (nhds (L + 0)) :=
      tendsto_const_nhds.add hb
    rwa [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun M => ?_) (fun M => ?_)
  · have h4 := abs_le.mp (Real.abs_le_sqrt (h M))
    show L - Real.sqrt (q ^ M * Y) ≤ a M
    linarith [h4.1]
  · have h4 := abs_le.mp (Real.abs_le_sqrt (h M))
    show a M ≤ L + Real.sqrt (q ^ M * Y)
    linarith [h4.2]

#print axioms tendsto_of_sq_le

/-- `B(Hv, v) = Σᵢ B(hᵢv, hᵢv)` on a patch system (`KnabeCriterion.form_proj_self`).

DERIVED: no numeral. -/
theorem form_H_eq_sum (S : PatchSystem) (v : S.E) :
    S.B (S.H v) v = ∑ i, S.B (S.h i v) (S.h i v) := by
  show S.B (totalOp S.h v) v = _
  rw [totalOp_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => form_proj_self S.B (S.h i) (S.selfAdj i) (S.idem i) v)

#print axioms form_H_eq_sum

/-- **`H` pairs to zero with a vector every `hᵢ` sends to a null vector**: `B(Hv, u) = 0` when
`B(hᵢu, hᵢu) = 0` for every `i` (`HeatBathGapDecay.form_eq_zero_of_null`).

DERIVED: `0` is the null value. -/
theorem form_H_left_zero (S : PatchSystem) (u : S.E) (hu : ∀ i, S.B (S.h i u) (S.h i u) = 0)
    (v : S.E) : S.B (S.H v) u = 0 := by
  show S.B (totalOp S.h v) u = 0
  rw [totalOp_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => by
    rw [S.selfAdj i v u]
    exact form_eq_zero_of_null S (hu i) v)

#print axioms form_H_left_zero

/-- **THE ERGODIC LIMIT FROM A POINCARÉ INEQUALITY.** On a patch system with a vector `u`,
`B(u, u) = 1`, `B(Hv, u) = 0` for every `v`, and `B(v, v) − B(v, u)² ≤ C B(Hv, v)` at some `C ≥ 0`:
for all `f`, `g` and `L = B(f, u) B(g, u)`, `ErgodicLimit S f g L`. The lazy step keeps `B(·, u)`
(`step_diff`) and lowers the variance `B(v, v) − B(v, u)²` by `K⁻¹ B(Hv, v)` (`Tstep_form`), so by
the factor `q = 1 − (K(C + 1))⁻¹`; Cauchy–Schwarz bounds
`(B(Tᴹf, g) − L)² ≤ qᴹ (B(f, f) − B(f, u)²) B(g, g)` (`form_sq_le_mul`), and `tendsto_of_sq_le`
closes it.

DERIVED: `0` is the sign of `C` and the null pairing; `1` is the normalisation of `u` and the shift
`C + 1`; `2` is the square. -/
theorem ergodicLimit_of_poincare (S : PatchSystem) (u : S.E) (hu : S.B u u = 1)
    (hHu : ∀ v, S.B (S.H v) u = 0) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ v, S.B v v - S.B v u ^ 2 ≤ C * S.B (S.H v) v) (f g : S.E) {L : ℝ}
    (hL : S.B f u * S.B g u = L) : ErgodicLimit S f g L := by
  unfold ErgodicLimit
  rw [← hL]
  have hKc : ((Kc S : ℕ) : ℝ) = (Fintype.card S.ι : ℝ) + 1 := by
    unfold Kc
    exact Nat.cast_succ _
  have hK1 : (1 : ℝ) ≤ ((Kc S : ℕ) : ℝ) := by
    rw [hKc]
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card S.ι)
    linarith
  have hK0 : (0 : ℝ) < ((Kc S : ℕ) : ℝ) := by linarith
  have hK : ∀ v : S.E, S.B (S.H v) (S.H v) ≤ ((Kc S : ℕ) : ℝ) * S.B (S.H v) v := by
    intro v
    rw [hKc]
    have h1 := H_form_le_card S v
    have h2 := S.H_form_nonneg v
    nlinarith
  have hmv : ∀ v : S.E, S.B (Tstep S ((Kc S : ℕ) : ℝ) v) u = S.B v u := by
    intro v
    have h := step_diff S ((Kc S : ℕ) : ℝ) v u
    rw [hHu, mul_zero, sub_eq_zero] at h
    exact h.symm
  have hmean : ∀ M, S.B (Titer S ((Kc S : ℕ) : ℝ) M f) u = S.B f u := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih => rw [Titer_succ, hmv, ih]
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ := ⟨_, rfl⟩
  have hKC : 1 ≤ ((Kc S : ℕ) : ℝ) * (C + 1) := by
    nlinarith [mul_nonneg hK0.le hC]
  have hinv0 : 0 < (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ := inv_pos.mpr (by linarith)
  have hinv1 : (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hKC
  have hq0 : 0 ≤ q := by
    rw [hq]
    linarith
  have hq1 : q < 1 := by
    rw [hq]
    linarith
  have hC1 : C + 1 ≠ 0 := (by linarith : (0 : ℝ) < C + 1).ne'
  have hstep : ∀ v : S.E,
      S.B (Tstep S ((Kc S : ℕ) : ℝ) v) (Tstep S ((Kc S : ℕ) : ℝ) v) - S.B v u ^ 2
        ≤ q * (S.B v v - S.B v u ^ 2) := by
    intro v
    have hT := Tstep_form S hK0 hK v
    have hPv := hP v
    have hD := S.H_form_nonneg v
    have h1 : S.B v v - S.B v u ^ 2 ≤ (C + 1) * S.B (S.H v) v := by nlinarith
    have h2 : (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ * (S.B v v - S.B v u ^ 2)
        ≤ (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ * ((C + 1) * S.B (S.H v) v) :=
      mul_le_mul_of_nonneg_left h1 hinv0.le
    have h3 : (((Kc S : ℕ) : ℝ) * (C + 1))⁻¹ * ((C + 1) * S.B (S.H v) v)
        = (((Kc S : ℕ) : ℝ))⁻¹ * S.B (S.H v) v := by
      rw [mul_inv]
      calc (((Kc S : ℕ) : ℝ))⁻¹ * (C + 1)⁻¹ * ((C + 1) * S.B (S.H v) v)
          = (((Kc S : ℕ) : ℝ))⁻¹ * ((C + 1)⁻¹ * (C + 1)) * S.B (S.H v) v := by ring
        _ = (((Kc S : ℕ) : ℝ))⁻¹ * S.B (S.H v) v := by rw [inv_mul_cancel₀ hC1, mul_one]
    rw [hq]
    linarith [hT, h2, h3]
  have hdecay : ∀ M : ℕ,
      S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f) - S.B f u ^ 2
        ≤ q ^ M * (S.B f f - S.B f u ^ 2) := by
    intro M
    induction M with
    | zero => simp only [Titer_zero, pow_zero, one_mul, le_refl]
    | succ M ih =>
      rw [Titer_succ, pow_succ q M]
      have h := hstep (Titer S ((Kc S : ℕ) : ℝ) M f)
      rw [hmean M] at h
      calc S.B (Tstep S ((Kc S : ℕ) : ℝ) (Titer S ((Kc S : ℕ) : ℝ) M f))
            (Tstep S ((Kc S : ℕ) : ℝ) (Titer S ((Kc S : ℕ) : ℝ) M f)) - S.B f u ^ 2
          ≤ q * (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f)
              - S.B f u ^ 2) := h
        _ ≤ q * (q ^ M * (S.B f f - S.B f u ^ 2)) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ M * q * (S.B f f - S.B f u ^ 2) := by ring
  have hbound : ∀ M : ℕ, (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) g - S.B f u * S.B g u) ^ 2
      ≤ q ^ M * ((S.B f f - S.B f u ^ 2) * S.B g g) := by
    intro M
    obtain ⟨w, hw⟩ : ∃ w : S.E, w = Titer S ((Kc S : ℕ) : ℝ) M f - S.B f u • u := ⟨_, rfl⟩
    have e1 : S.B w g = S.B (Titer S ((Kc S : ℕ) : ℝ) M f) g - S.B f u * S.B g u := by
      rw [hw]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination (-(S.B f u)) * S.symm u g
    have e2 : S.B w w = S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f)
        - S.B f u ^ 2 := by
      rw [hw]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination (-(S.B f u)) * S.symm u (Titer S ((Kc S : ℕ) : ℝ) M f)
        + (-2 * S.B f u) * hmean M + (S.B f u) ^ 2 * hu
    have hcs := form_sq_le_mul S.B S.symm S.nonneg w g
    rw [e1, e2] at hcs
    have hgg := S.nonneg g
    calc (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) g - S.B f u * S.B g u) ^ 2
        ≤ (S.B (Titer S ((Kc S : ℕ) : ℝ) M f) (Titer S ((Kc S : ℕ) : ℝ) M f) - S.B f u ^ 2)
          * S.B g g := hcs
      _ ≤ (q ^ M * (S.B f f - S.B f u ^ 2)) * S.B g g :=
          mul_le_mul_of_nonneg_right (hdecay M) hgg
      _ = q ^ M * ((S.B f f - S.B f u ^ 2) * S.B g g) := by ring
  exact tendsto_of_sq_le hq0 hq1 hbound

#print axioms ergodicLimit_of_poincare

end Ergodic

end MassGap.HeatBathErgodic
