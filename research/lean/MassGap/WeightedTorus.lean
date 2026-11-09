import Mathlib
import MassGap.WeightedHeatBath

noncomputable section

/-!
# MassGap.WeightedTorus — the Gibbs expectation and detailed balance of a general weight

The box-gap chain reads the Wilson weight through its Gibbs expectation and the single-link heat
bath, and uses three facts: the heat bath preserves the expectation (DLR), it is self-adjoint in the
expectation's `L²` form (detailed balance), and it is idempotent. This file proves the first two for
an arbitrary positive continuous weight `Φ`, the third being `WeightedHeatBath.wAvg_of_readsNot`
with `wAvg_update`. `HeatBath.heatAvg` is `wAvg (wt bd β)` by definition, so the Wilson statements
are the instance `Φ = wt bd β`.

## What it gives

* `wExpect Φ F = ∫ F Φ / ∫ Φ` against the product Haar measure.
* `integral_wAvg_mul`: `∫ wAvg Φ l f · Φ = ∫ f · Φ` (`HeatBath.integral_eq_integral_update`).
* `expect_wAvg`, `expect_wAvg_mul` (detailed balance).
-/

namespace MassGap.WeightedTorus

open MeasureTheory
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBath (exists_abs_le integral_eq_integral_update)
open MassGap.WeightedHeatBath (wNum wPart wAvg wPart_pos wAvg_update wAvg_mul_left continuous_wAvg)

variable {N : ℕ} {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **The Gibbs expectation of the weight `Φ`**: `∫ F Φ / ∫ Φ` against the product Haar measure. -/
def wExpect (Φ : (Lk → SU N) → ℝ) (F : (Lk → SU N) → ℝ) : ℝ :=
  (∫ W, F W * Φ W ∂(Measure.pi fun _ : Lk => probHaar (SU N)))
    / ∫ W, Φ W ∂(Measure.pi fun _ : Lk => probHaar (SU N))

/-- **A factor not reading `l` comes out on the right.**

DERIVED: no numeral. -/
theorem wAvg_mul_right (Φ : (Lk → SU N) → ℝ) (l : Lk) {a f : (Lk → SU N) → ℝ}
    (ha : ∀ W g, a (Function.update W l g) = a W) (W : Lk → SU N) :
    wAvg Φ l (fun V => f V * a V) W = wAvg Φ l f W * a W := by
  have h := wAvg_mul_left Φ l (f := f) ha W
  rw [show (fun V => f V * a V) = fun V => a V * f V from funext fun V => mul_comm _ _, h, mul_comm]

#print axioms wAvg_mul_right

/-- **The DLR identity at one link, integrated**: `∫ wAvg Φ l f · Φ = ∫ f · Φ`
(`HeatBath.integral_eq_integral_update`, `wAvg_update`).

DERIVED: no numeral. -/
theorem integral_wAvg_mul {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (l : Lk) {f : (Lk → SU N) → ℝ} (hf : Continuous f) :
    ∫ W, wAvg Φ l f W * Φ W ∂(Measure.pi fun _ : Lk => probHaar (SU N))
      = ∫ W, f W * Φ W ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
  have hc1 : Continuous (fun W => wAvg Φ l f W * Φ W) :=
    (continuous_wAvg hpos hcont l hf).mul hcont
  have hc2 : Continuous (fun W => f W * Φ W) := hf.mul hcont
  obtain ⟨C1, hC1⟩ := exists_abs_le hc1
  obtain ⟨C2, hC2⟩ := exists_abs_le hc2
  rw [integral_eq_integral_update (probHaar (SU N)) l _ hc1.measurable hC1,
    integral_eq_integral_update (probHaar (SU N)) l _ hc2.measurable hC2]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun W => ?_))
  show ∫ g, wAvg Φ l f (Function.update W l g) * Φ (Function.update W l g) ∂(probHaar (SU N))
    = ∫ g, f (Function.update W l g) * Φ (Function.update W l g) ∂(probHaar (SU N))
  simp only [wAvg_update, integral_const_mul]
  show wAvg Φ l f W * wPart Φ l W = wNum Φ l f W
  unfold wAvg
  exact div_mul_cancel₀ _ (wPart_pos hpos hcont l W).ne'

#print axioms integral_wAvg_mul

/-- **The DLR identity at one link**: `wExpect Φ (wAvg Φ l f) = wExpect Φ f`.

DERIVED: no numeral. -/
theorem expect_wAvg {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l : Lk)
    {f : (Lk → SU N) → ℝ} (hf : Continuous f) : wExpect Φ (wAvg Φ l f) = wExpect Φ f := by
  unfold wExpect
  rw [integral_wAvg_mul hpos hcont l hf]

#print axioms expect_wAvg

/-- **Detailed balance**: `wExpect Φ (wAvg f · g) = wExpect Φ (f · wAvg g)`, through
`wExpect Φ (wAvg f · wAvg g)` (`expect_wAvg`, `wAvg_mul_left`, `wAvg_mul_right`).

DERIVED: no numeral. -/
theorem expect_wAvg_mul {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    (l : Lk) {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    wExpect Φ (fun W => wAvg Φ l f W * g W) = wExpect Φ (fun W => f W * wAvg Φ l g W) :=
  calc wExpect Φ (fun W => wAvg Φ l f W * g W)
      = wExpect Φ (wAvg Φ l (fun W => wAvg Φ l f W * g W)) :=
        (expect_wAvg hpos hcont l ((continuous_wAvg hpos hcont l hf).mul hg)).symm
    _ = wExpect Φ (fun W => wAvg Φ l f W * wAvg Φ l g W) := by
        congr 1
        funext W
        exact wAvg_mul_left Φ l (fun V h => wAvg_update Φ l f V h) W
    _ = wExpect Φ (wAvg Φ l (fun W => f W * wAvg Φ l g W)) := by
        congr 1
        funext W
        exact (wAvg_mul_right Φ l (fun V h => wAvg_update Φ l g V h) W).symm
    _ = wExpect Φ (fun W => f W * wAvg Φ l g W) :=
        expect_wAvg hpos hcont l (hf.mul (continuous_wAvg hpos hcont l hg))

#print axioms expect_wAvg_mul

/-! ## The torus layer of a gauge-invariant weight -/

/-- **A gauge-invariant weight on every periodic lattice**: positive, continuous, and invariant under
torus gauge transformations, at every extent `M + 1`. -/
structure TorusWeight (N : ℕ) where
  Φ : (M : ℕ) → (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ
  pos : ∀ M W, 0 < Φ M W
  cont : ∀ M, Continuous (Φ M)
  gauge : ∀ M (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N),
    Φ M (LocalGauge.gaugeTransform g W) = Φ M W

section Torus

open MassGap.PeriodicState (torusObs)
open MassGap.KnabeCriterion (periodicGaugeInvSubmodule PeriodicGaugeInv)
open MassGap.InfiniteLattice (siteMod pullback)
open MassGap.HeatBath (restrictConf continuous_restrictConf restrictConf_pullback continuous_torusObs
  restrictConf_igauge torusObs_gauge integral_twoSided integrable_of_abs_le)

variable {N : ℕ}

/-- The heat bath of a continuous weight is additive on continuous functions (`integral_add`).

DERIVED: no numeral. -/
theorem wAvg_add {Lk : Type} [Fintype Lk] [DecidableEq Lk] {Φ : (Lk → SU N) → ℝ}
    (hcont : Continuous Φ) (l : Lk) {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (W : Lk → SU N) :
    wAvg Φ l (fun V => f V + g V) W = wAvg Φ l f W + wAvg Φ l g W := by
  have hi : ∀ {F : (Lk → SU N) → ℝ}, Continuous F →
      Integrable (fun y : SU N => F (Function.update W l y) * Φ (Function.update W l y))
        (probHaar (SU N)) := fun {F} hF => by
    have hc : Continuous fun y : SU N => F (Function.update W l y) * Φ (Function.update W l y) :=
      (hF.comp (continuous_const.update l continuous_id)).mul
        (hcont.comp (continuous_const.update l continuous_id))
    obtain ⟨C, hC⟩ := exists_abs_le hc
    exact integrable_of_abs_le _ hc.measurable hC
  unfold wAvg wNum
  rw [← add_div]
  congr 1
  simp only [add_mul]
  exact integral_add (hi hf) (hi hg)

#print axioms wAvg_add

/-- The heat bath is homogeneous.

DERIVED: no numeral. -/
theorem wAvg_const_mul {Lk : Type} [DecidableEq Lk] (Φ : (Lk → SU N) → ℝ) (l : Lk) (c : ℝ)
    (f : (Lk → SU N) → ℝ) (W : Lk → SU N) :
    wAvg Φ l (fun V => c * f V) W = c * wAvg Φ l f W :=
  wAvg_mul_left Φ l (a := fun _ => c) (fun _ _ => rfl) W

#print axioms wAvg_const_mul

/-- **The heat bath of a gauge-invariant weight keeps torus gauge invariance**: the gauge
transformation at the updated link is a two-sided translation of the integration variable
(`HeatBath.integral_twoSided`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wAvg_gauge (Ψ : TorusWeight N) {M : ℕ} (l : WilsonHypercubic.Link 4 (M + 1))
    {φ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hφ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), φ (LocalGauge.gaugeTransform g W) = φ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    wAvg (Ψ.Φ M) l φ (LocalGauge.gaugeTransform g W) = wAvg (Ψ.Φ M) l φ W := by
  have hupd : ∀ h : SU N, Function.update (LocalGauge.gaugeTransform g W) l h
      = LocalGauge.gaugeTransform g
          (Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2))) := by
    intro h
    funext l'
    by_cases hl : l' = l
    · rw [hl, Function.update_self]
      show h = g l.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l
        * (g (WilsonHypercubic.shift l.1 l.2))⁻¹
      rw [Function.update_self]
      group
    · rw [Function.update_of_ne hl]
      show g l'.2 * W l' * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
        = g l'.2 * Function.update W l ((g l.2)⁻¹ * h * g (WilsonHypercubic.shift l.1 l.2)) l'
          * (g (WilsonHypercubic.shift l'.1 l'.2))⁻¹
      rw [Function.update_of_ne hl]
  have hw : ∀ V : WilsonHypercubic.Link 4 (M + 1) → SU N,
      Ψ.Φ M (LocalGauge.gaugeTransform g V) = Ψ.Φ M V := fun V => Ψ.gauge M g V
  unfold wAvg wNum wPart
  simp only [hupd, hφ, hw]
  rw [integral_twoSided (fun y => φ (Function.update W l y) * Ψ.Φ M (Function.update W l y)),
    integral_twoSided (fun y => Ψ.Φ M (Function.update W l y))]

#print axioms wAvg_gauge

/-- **The heat bath of `Ψ` lifted to `ℤ⁴` observables.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def wLift (Ψ : TorusWeight N) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) : C(GibbsSpec.IConf (SU N), ℝ) :=
  ⟨fun U => wAvg (Ψ.Φ M) l (torusObs M F) (restrictConf M U),
    (continuous_wAvg (Ψ.pos M) (Ψ.cont M) l (continuous_torusObs M F)).comp
      (continuous_restrictConf M)⟩

/-- The torus reading of the lift is the heat bath of the torus reading.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_wLift (Ψ : TorusWeight N) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) :
    torusObs M (wLift Ψ M l F) = wAvg (Ψ.Φ M) l (torusObs M F) := by
  funext W
  show wAvg (Ψ.Φ M) l (torusObs M F) (restrictConf M (pullback M W))
    = wAvg (Ψ.Φ M) l (torusObs M F) W
  rw [restrictConf_pullback]

#print axioms torusObs_wLift

/-- **The lift keeps periodic gauge invariance.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wLift_mem (Ψ : TorusWeight N) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) :
    wLift Ψ M l F ∈ periodicGaugeInvSubmodule (N := N) M := by
  show ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (U : GibbsSpec.IConf (SU N)),
    wLift Ψ M l F (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U)
      = wLift Ψ M l F U
  intro g U
  show wAvg (Ψ.Φ M) l (torusObs M F)
      (restrictConf M (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U))
    = wAvg (Ψ.Φ M) l (torusObs M F) (restrictConf M U)
  rw [restrictConf_igauge]
  exact wAvg_gauge Ψ l (fun g' W => torusObs_gauge hF g' W) g (restrictConf M U)

#print axioms wLift_mem

/-- **The conditional expectation of `Ψ` at the torus link `l`**, a linear map of the periodic
gauge-invariant observables.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def wCondExp (Ψ : TorusWeight N) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1)) :
    ↥(periodicGaugeInvSubmodule (N := N) M) →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) M) where
  toFun x := ⟨wLift Ψ M l (x : C(GibbsSpec.IConf (SU N), ℝ)), wLift_mem Ψ M l x.2⟩
  map_add' x y := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show wAvg (Ψ.Φ M) l
        (torusObs M ((x : C(GibbsSpec.IConf (SU N), ℝ)) + (y : C(GibbsSpec.IConf (SU N), ℝ))))
        (restrictConf M U)
      = wAvg (Ψ.Φ M) l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
        + wAvg (Ψ.Φ M) l (torusObs M (y : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact wAvg_add (Ψ.cont M) l (continuous_torusObs M _) (continuous_torusObs M _)
      (restrictConf M U)
  map_smul' c x := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro U
    show wAvg (Ψ.Φ M) l (torusObs M (c • (x : C(GibbsSpec.IConf (SU N), ℝ)))) (restrictConf M U)
      = c * wAvg (Ψ.Φ M) l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
    exact wAvg_const_mul (Ψ.Φ M) l c _ (restrictConf M U)

/-- **Idempotence** (`wAvg_of_readsNot`, `wAvg_update`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wCondExp_idem (Ψ : TorusWeight N) (M : ℕ) (l : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    wCondExp Ψ M l (wCondExp Ψ M l x) = wCondExp Ψ M l x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show wAvg (Ψ.Φ M) l (torusObs M (wLift Ψ M l (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = wAvg (Ψ.Φ M) l (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_wLift]
  exact MassGap.WeightedHeatBath.wAvg_of_readsNot (Ψ.pos M) (Ψ.cont M) l
    (fun W g => wAvg_update (Ψ.Φ M) l _ W g) _

#print axioms wCondExp_idem

/-- The normaliser of a positive continuous weight is positive.

DERIVED: `0` is the sign; `1` is the Haar mass. -/
theorem integral_pos_weight {Lk : Type} [Fintype Lk] {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W)
    (hcont : Continuous Φ) : 0 < ∫ W, Φ W ∂(Measure.pi fun _ : Lk => probHaar (SU N)) := by
  obtain ⟨C, hC⟩ := exists_abs_le hcont
  have hint : Integrable Φ (Measure.pi fun _ : Lk => probHaar (SU N)) :=
    integrable_of_abs_le _ hcont.measurable hC
  rw [integral_pos_iff_support_of_nonneg (fun W => (hpos W).le) hint]
  have hs : Function.support Φ = Set.univ :=
    Set.eq_univ_of_forall fun W => Function.mem_support.mpr (hpos W).ne'
  rw [hs, measure_univ]
  exact one_pos

#print axioms integral_pos_weight

/-- **The periodic Gibbs state of `Ψ` at extent `M + 1`**, on `ℤ⁴` observables.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent and the
normalisation. -/
def wTorusState (Ψ : TorusWeight N) (M : ℕ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) where
  toFun f := wExpect (Ψ.Φ M) (torusObs M f)
  map_add' f g := by
    have hi : ∀ F : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Integrable (fun W => torusObs M F W * Ψ.Φ M W)
          (Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)) := fun F => by
      have hc := (continuous_torusObs M F).mul (Ψ.cont M)
      obtain ⟨C, hC⟩ := exists_abs_le hc
      exact integrable_of_abs_le _ hc.measurable hC
    unfold wExpect
    rw [← add_div]
    congr 1
    rw [← integral_add (hi f) (hi g)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun W => by
      show (f (pullback M W) + g (pullback M W)) * Ψ.Φ M W
        = f (pullback M W) * Ψ.Φ M W + g (pullback M W) * Ψ.Φ M W
      ring)
  map_smul' c f := by
    unfold wExpect
    rw [mul_div_assoc', ← integral_const_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun W => by
      show (c * f (pullback M W)) * Ψ.Φ M W = c * (f (pullback M W) * Ψ.Φ M W)
      ring)
  nonneg' f hf := by
    unfold wExpect
    exact div_nonneg (integral_nonneg fun W => mul_nonneg (hf _) (Ψ.pos M W).le)
      (integral_nonneg fun W => (Ψ.pos M W).le)
  one' := by
    unfold wExpect
    have h : ∫ W, torusObs M (1 : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) W * Ψ.Φ M W
        ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N))
        = ∫ W, Ψ.Φ M W ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun W => by
        show (1 : ℝ) * Ψ.Φ M W = Ψ.Φ M W
        ring)
    rw [h]
    exact div_self (integral_pos_weight (Ψ.pos M) (Ψ.cont M)).ne'

/-- **The torus `L²` form of `Ψ`** at extent index `j`.

DERIVED: `2 * j + 1` is the index of the even-extent family. -/
def wForm (Ψ : TorusWeight N) (j : ℕ) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ]
      ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => wTorusState Ψ (2 * j + 1)
      ((x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) * (y : C(GibbsSpec.IConf (SUN.SU N), ℝ))))
    (fun x₁ x₂ y => by simp only [Submodule.coe_add, add_mul, DLRLimit.State.map_add])
    (fun c x y => by
      simp only [Submodule.coe_smul, smul_mul_assoc, DLRLimit.State.map_smul, smul_eq_mul])
    (fun x y₁ y₂ => by simp only [Submodule.coe_add, mul_add, DLRLimit.State.map_add])
    (fun c x y => by
      simp only [Submodule.coe_smul, mul_smul_comm, DLRLimit.State.map_smul, smul_eq_mul])

/-- `wForm` is symmetric.

DERIVED: `2 * j + 1` is the index of the even-extent family. -/
theorem wForm_symm (Ψ : TorusWeight N) (j : ℕ)
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : wForm Ψ j x y = wForm Ψ j y x := by
  show wTorusState Ψ (2 * j + 1) _ = wTorusState Ψ (2 * j + 1) _
  rw [mul_comm (x : C(GibbsSpec.IConf (SUN.SU N), ℝ))]

#print axioms wForm_symm

/-- `wForm` is non-negative.

DERIVED: `0` is the sign; `2 * j + 1` is the index of the even-extent family. -/
theorem wForm_nonneg (Ψ : TorusWeight N) (j : ℕ)
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : 0 ≤ wForm Ψ j x x := by
  show 0 ≤ wTorusState Ψ (2 * j + 1)
    ((x : C(GibbsSpec.IConf (SUN.SU N), ℝ)) * (x : C(GibbsSpec.IConf (SUN.SU N), ℝ)))
  exact DLRLimit.State.nonneg _ _ (fun U => by
    rw [ContinuousMap.mul_apply]
    exact mul_self_nonneg _)

#print axioms wForm_nonneg

/-- **Self-adjointness for `wForm`** (detailed balance, `expect_wAvg_mul`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
theorem wCondExp_selfAdj (Ψ : TorusWeight N) (j : ℕ) (l : WilsonHypercubic.Link 4 (2 * j + 1 + 1))
    (x y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    wForm Ψ j (wCondExp Ψ (2 * j + 1) l x) y = wForm Ψ j x (wCondExp Ψ (2 * j + 1) l y) := by
  show wExpect (Ψ.Φ (2 * j + 1))
      (fun W => torusObs (2 * j + 1) (wLift Ψ (2 * j + 1) l (x : C(GibbsSpec.IConf (SU N), ℝ))) W
        * torusObs (2 * j + 1) (y : C(GibbsSpec.IConf (SU N), ℝ)) W)
    = wExpect (Ψ.Φ (2 * j + 1))
      (fun W => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) W
        * torusObs (2 * j + 1) (wLift Ψ (2 * j + 1) l (y : C(GibbsSpec.IConf (SU N), ℝ))) W)
  rw [torusObs_wLift, torusObs_wLift]
  exact expect_wAvg_mul (Ψ.pos _) (Ψ.cont _) l (continuous_torusObs _ _) (continuous_torusObs _ _)

#print axioms wCondExp_selfAdj

/-! ## The local gap of the box patches from pair correlations -/

open MassGap.KnabeCriterion (patchOp selfAdj_id_sub idem_id_sub)
open MassGap.BoxPatch (boxWeight)
open MassGap.BoxGap (DefectMatrix patch_gap_of_defect pair_defect_of_corr boxWeight_cases)

/-- **The box patch operator of `Ψ`**: `Σ_{l in the box at k} (1 − E_l)`.

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent. -/
def wBoxOp (Ψ : TorusWeight N) (n j : ℕ) (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1)) :
    ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)) :=
  patchOp (boxWeight n)
    (fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - wCondExp Ψ (2 * j + 1) l) k

/-- **The local gap of `Ψ` at box patches** (`BoxPatch.BoxLocalGap` with `Ψ` in place of Wilson).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `1` is the successor in `j + 1`. -/
def WBoxLocalGap (Ψ : TorusWeight N) (n : ℕ) (γ : ℝ) : Prop :=
  ∀ j : ℕ, n ≤ j + 1 → ∀ (k : WilsonHypercubic.Site 4 (2 * j + 1 + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))),
    γ * wForm Ψ j (wBoxOp Ψ n j k x) x ≤ wForm Ψ j (wBoxOp Ψ n j k x) (wBoxOp Ψ n j k x)

/-- **The two-link correlation of `Ψ` at extent index `j`** (`BoxGap.PairCorrAt` with `Ψ`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `2` is the halving. -/
def WPairCorrAt (Ψ : TorusWeight N) (j : ℕ)
    (δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ) :
    Prop :=
  ∀ l m, l ≠ m → ∀ x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
    ∃ y : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1)),
      wCondExp Ψ (2 * j + 1) l y = y ∧ wCondExp Ψ (2 * j + 1) m y = y ∧
      wForm Ψ j (wCondExp Ψ (2 * j + 1) l (x - y)) (wCondExp Ψ (2 * j + 1) m (x - y))
        ≤ δ l m * (wForm Ψ j (wCondExp Ψ (2 * j + 1) l (x - y))
              (wCondExp Ψ (2 * j + 1) l (x - y))
            + wForm Ψ j (wCondExp Ψ (2 * j + 1) m (x - y))
              (wCondExp Ψ (2 * j + 1) m (x - y))) / 2

/-- **The box local gap from pair correlations**: a defect matrix with row and column sums at most
`Δ`, entries in `[0, 1]`, satisfying `WPairCorrAt` at every extent index, gives the local gap
`1 − Δ` at every box side (`BoxGap.pair_defect_of_corr`, `BoxGap.patch_gap_of_defect`).

DERIVED: `1` is the gap at zero defect and the entry bound; `0` is the lower end of the entries;
`4`, `2 * j + 1`, `+ 1` as in `WPairCorrAt`. -/
theorem wBoxLocalGap_of_pairCorr (Ψ : TorusWeight N) {Δ : ℝ} (n : ℕ)
    (h : ∀ j : ℕ, ∃ δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ,
      DefectMatrix δ Δ ∧ (∀ l m, δ l m ≤ 1) ∧ WPairCorrAt Ψ j δ) :
    WBoxLocalGap Ψ n (1 - Δ) := by
  intro j _ k x
  obtain ⟨δ, hδ, h1, hc⟩ := h j
  refine patch_gap_of_defect (wForm Ψ j) (wForm_nonneg Ψ j)
    (fun l => (LinearMap.id : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))
      →ₗ[ℝ] ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) - wCondExp Ψ (2 * j + 1) l)
    (fun l => selfAdj_id_sub (wForm Ψ j) (wCondExp Ψ (2 * j + 1) l) (wCondExp_selfAdj Ψ j l))
    (fun l => idem_id_sub (wCondExp Ψ (2 * j + 1) l) (wCondExp_idem Ψ (2 * j + 1) l))
    (boxWeight n) k (fun l => boxWeight_cases n k l) δ hδ x (fun l m hlm _ _ => ?_)
  obtain ⟨y, hyl, hym, hcorr⟩ := hc l m hlm x
  have key := pair_defect_of_corr (wForm Ψ j) (wForm_symm Ψ j) (wForm_nonneg Ψ j)
    (wCondExp Ψ (2 * j + 1) l) (wCondExp Ψ (2 * j + 1) m)
    (wCondExp_selfAdj Ψ j l) (wCondExp_selfAdj Ψ j m)
    (wCondExp_idem Ψ (2 * j + 1) l) (wCondExp_idem Ψ (2 * j + 1) m)
    (hδ.1 l m) (h1 l m) (x - y) hcorr
  have e1 : x - y - wCondExp Ψ (2 * j + 1) l (x - y) = x - wCondExp Ψ (2 * j + 1) l x := by
    rw [map_sub, hyl]
    abel
  have e2 : x - y - wCondExp Ψ (2 * j + 1) m (x - y) = x - wCondExp Ψ (2 * j + 1) m x := by
    rw [map_sub, hym]
    abel
  rw [e1, e2] at key
  simpa only [LinearMap.sub_apply, LinearMap.id_apply] using key

#print axioms wBoxLocalGap_of_pairCorr

/-! ## The two-link conditional expectation of `Ψ` and the pair correlation -/

open MassGap.HeatBathErgodic (havg havg_update havg_update_other havg_sub continuous_havg)
open MassGap.WeightedHeatBath (w2Num w2Part w2Avg w2Part_pos continuous_w2Avg w2Avg_update_m
  w2Avg_update_l w_gibbs_corr_le_of_fibre FibreHyp)

/-- **The two-link numerator of `φ − w2Avg φ` vanishes** (`PairCorr.heatNum2_sub_self` for a
general weight).

DERIVED: `0` is the value asserted. -/
theorem w2Num_sub_self {Lk : Type} [Fintype Lk] [DecidableEq Lk] {Φ : (Lk → SU N) → ℝ}
    (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) {l m : Lk} (hlm : l ≠ m)
    {φ : (Lk → SU N) → ℝ} (hφ : Continuous φ) (W : Lk → SU N) :
    w2Num Φ l m (fun V => φ V - w2Avg Φ l m φ V) W = 0 := by
  have hc : Continuous (w2Avg Φ l m φ) := continuous_w2Avg hpos hcont l m hφ
  have hφw : Continuous (fun V => φ V * Φ V) := hφ.mul hcont
  have hcw : Continuous (fun V => w2Avg Φ l m φ V * Φ V) := hc.mul hcont
  have e1 : (fun V => (φ V - w2Avg Φ l m φ V) * Φ V)
      = fun V => φ V * Φ V - w2Avg Φ l m φ V * Φ V :=
    funext fun V => sub_mul _ _ _
  have e2a : ∀ V, havg l (fun V => w2Avg Φ l m φ V * Φ V) V = w2Avg Φ l m φ V * havg l Φ V := by
    intro V
    unfold havg
    simp only [w2Avg_update_l Φ hlm, integral_const_mul]
  have e2 : havg l (fun V => φ V * Φ V - w2Avg Φ l m φ V * Φ V)
      = fun V => havg l (fun V => φ V * Φ V) V - w2Avg Φ l m φ V * havg l Φ V := by
    funext V
    rw [havg_sub l hφw hcw V, e2a V]
  have e3a : havg m (fun V => w2Avg Φ l m φ V * havg l Φ V) W = w2Avg Φ l m φ W * w2Part Φ l m W := by
    unfold w2Part havg
    simp only [w2Avg_update_m, integral_const_mul]
  have e4 : w2Avg Φ l m φ W * w2Part Φ l m W = havg m (havg l (fun V => φ V * Φ V)) W := by
    unfold w2Avg
    exact div_mul_cancel₀ _ (w2Part_pos hpos hcont l m W).ne'
  show havg m (havg l (fun V => (φ V - w2Avg Φ l m φ V) * Φ V)) W = 0
  have e5 : havg m (fun V => havg l (fun V => φ V * Φ V) V - w2Avg Φ l m φ V * havg l Φ V) W
      = havg m (fun V => havg l (fun V => φ V * Φ V) V) W
        - havg m (fun V => w2Avg Φ l m φ V * havg l Φ V) W :=
    havg_sub m (continuous_havg l hφw) (hc.mul (continuous_havg l hcont)) W
  rw [e1, e2, e5, e3a, ← e4, sub_self]

#print axioms w2Num_sub_self

/-- **The two-link heat bath of `Ψ` keeps torus gauge invariance** (`PairCorr.havg2_gauge`).

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem w2Avg_gauge (Ψ : TorusWeight N) {M : ℕ} (l m : WilsonHypercubic.Link 4 (M + 1))
    {φ : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ}
    (hφ : ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (W : WilsonHypercubic.Link 4 (M + 1) → SU N), φ (LocalGauge.gaugeTransform g W) = φ W)
    (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    w2Avg (Ψ.Φ M) l m φ (LocalGauge.gaugeTransform g W) = w2Avg (Ψ.Φ M) l m φ W := by
  have hφw : ∀ (g' : WilsonHypercubic.Site 4 (M + 1) → SU N)
      (V : WilsonHypercubic.Link 4 (M + 1) → SU N),
      φ (LocalGauge.gaugeTransform g' V) * Ψ.Φ M (LocalGauge.gaugeTransform g' V)
        = φ V * Ψ.Φ M V :=
    fun g' V => by rw [hφ, Ψ.gauge]
  unfold w2Avg w2Num w2Part
  rw [MassGap.PairCorr.havg2_gauge l m (Ψ := fun V => φ V * Ψ.Φ M V) hφw g W,
    MassGap.PairCorr.havg2_gauge l m (Ψ := Ψ.Φ M) (Ψ.gauge M) g W]

#print axioms w2Avg_gauge

/-- **The two-link heat bath of `Ψ` lifted to `ℤ⁴` observables.**

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def w2Lift (Ψ : TorusWeight N) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) : C(GibbsSpec.IConf (SU N), ℝ) :=
  ⟨fun U => w2Avg (Ψ.Φ M) l m (torusObs M F) (restrictConf M U),
    (continuous_w2Avg (Ψ.pos M) (Ψ.cont M) l m (continuous_torusObs M F)).comp
      (continuous_restrictConf M)⟩

/-- DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem torusObs_w2Lift (Ψ : TorusWeight N) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (F : C(GibbsSpec.IConf (SU N), ℝ)) :
    torusObs M (w2Lift Ψ M l m F) = w2Avg (Ψ.Φ M) l m (torusObs M F) := by
  funext W
  show w2Avg (Ψ.Φ M) l m (torusObs M F) (restrictConf M (pullback M W))
    = w2Avg (Ψ.Φ M) l m (torusObs M F) W
  rw [restrictConf_pullback]

#print axioms torusObs_w2Lift

/-- DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem w2Lift_mem (Ψ : TorusWeight N) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    {F : C(GibbsSpec.IConf (SU N), ℝ)} (hF : F ∈ periodicGaugeInvSubmodule (N := N) M) :
    w2Lift Ψ M l m F ∈ periodicGaugeInvSubmodule (N := N) M := by
  show ∀ (g : WilsonHypercubic.Site 4 (M + 1) → SU N) (U : GibbsSpec.IConf (SU N)),
    w2Lift Ψ M l m F (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U)
      = w2Lift Ψ M l m F U
  intro g U
  show w2Avg (Ψ.Φ M) l m (torusObs M F)
      (restrictConf M (GaugeInvariantAlgebra.igaugeTransform (fun x => g (siteMod M x)) U))
    = w2Avg (Ψ.Φ M) l m (torusObs M F) (restrictConf M U)
  rw [restrictConf_igauge]
  exact w2Avg_gauge Ψ l m (fun g' W => torusObs_gauge hF g' W) g (restrictConf M U)

#print axioms w2Lift_mem

/-- **The two-link conditional expectation of `Ψ`**: given every link but `l` and `m`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
def wTwoCondExp (Ψ : TorusWeight N) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) : ↥(periodicGaugeInvSubmodule (N := N) M) :=
  ⟨w2Lift Ψ M l m (x : C(GibbsSpec.IConf (SU N), ℝ)), w2Lift_mem Ψ M l m x.2⟩

/-- `E_l` fixes the two-link conditional expectation, for `l ≠ m`.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wCondExp_wTwoCondExp_l (Ψ : TorusWeight N) (M : ℕ) {l m : WilsonHypercubic.Link 4 (M + 1)}
    (hlm : l ≠ m) (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    wCondExp Ψ M l (wTwoCondExp Ψ M l m x) = wTwoCondExp Ψ M l m x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show wAvg (Ψ.Φ M) l (torusObs M (w2Lift Ψ M l m (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = w2Avg (Ψ.Φ M) l m (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_w2Lift]
  exact MassGap.WeightedHeatBath.wAvg_of_readsNot (Ψ.pos M) (Ψ.cont M) l
    (fun W g => w2Avg_update_l (Ψ.Φ M) hlm _ W g) _

#print axioms wCondExp_wTwoCondExp_l

/-- `E_m` fixes the two-link conditional expectation.

DERIVED: `4` is the spacetime dimension; `1` is the successor writing the extent. -/
theorem wCondExp_wTwoCondExp_m (Ψ : TorusWeight N) (M : ℕ) (l m : WilsonHypercubic.Link 4 (M + 1))
    (x : ↥(periodicGaugeInvSubmodule (N := N) M)) :
    wCondExp Ψ M m (wTwoCondExp Ψ M l m x) = wTwoCondExp Ψ M l m x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro U
  show wAvg (Ψ.Φ M) m (torusObs M (w2Lift Ψ M l m (x : C(GibbsSpec.IConf (SU N), ℝ))))
      (restrictConf M U)
    = w2Avg (Ψ.Φ M) l m (torusObs M (x : C(GibbsSpec.IConf (SU N), ℝ))) (restrictConf M U)
  rw [torusObs_w2Lift]
  exact MassGap.WeightedHeatBath.wAvg_of_readsNot (Ψ.pos M) (Ψ.cont M) m
    (fun W h => w2Avg_update_m (Ψ.Φ M) l m _ W h) _

#print axioms wCondExp_wTwoCondExp_m

/-- **The two-link correlation of `Ψ` from the fibre hypothesis**: with `y` the two-link conditional
expectation, `⟨E_l(x − y), E_m(x − y)⟩ ≤ c (‖E_l(x − y)‖² + ‖E_m(x − y)‖²)/2` in `wForm`
(`WeightedHeatBath.w_gibbs_corr_le_of_fibre`, `w2Num_sub_self`).

DERIVED: `4` is the spacetime dimension; `2 * j + 1` is the index of the even-extent family and the
`+ 1` its successor writing the extent; `0` is the lower end of `c`; `2` is the halving. -/
theorem wPairCorr_twoCond (Ψ : TorusWeight N) (j : ℕ)
    {l m : WilsonHypercubic.Link 4 (2 * j + 1 + 1)} (hlm : l ≠ m) {c : ℝ} (hc : 0 ≤ c)
    (H : FibreHyp (Ψ.Φ (2 * j + 1)) l m c)
    (x : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) :
    wForm Ψ j (wCondExp Ψ (2 * j + 1) l (x - wTwoCondExp Ψ (2 * j + 1) l m x))
        (wCondExp Ψ (2 * j + 1) m (x - wTwoCondExp Ψ (2 * j + 1) l m x))
      ≤ c * (wForm Ψ j (wCondExp Ψ (2 * j + 1) l (x - wTwoCondExp Ψ (2 * j + 1) l m x))
            (wCondExp Ψ (2 * j + 1) l (x - wTwoCondExp Ψ (2 * j + 1) l m x))
          + wForm Ψ j (wCondExp Ψ (2 * j + 1) m (x - wTwoCondExp Ψ (2 * j + 1) l m x))
            (wCondExp Ψ (2 * j + 1) m (x - wTwoCondExp Ψ (2 * j + 1) l m x))) / 2 := by
  set Φ := Ψ.Φ (2 * j + 1) with hΦ
  obtain ⟨F, hFdef⟩ : ∃ F : (WilsonHypercubic.Link 4 (2 * j + 1 + 1) → SU N) → ℝ,
      F = fun V => torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - w2Avg Φ l m (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V := ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hFdef]
    exact (continuous_torusObs _ _).sub
      (continuous_w2Avg (Ψ.pos _) (Ψ.cont _) l m (continuous_torusObs _ _))
  have hzero : ∀ W, w2Num Φ l m F W = 0 := fun W => by
    rw [hFdef]
    exact w2Num_sub_self (Ψ.pos _) (Ψ.cont _) hlm (continuous_torusObs _ _) W
  have hF : torusObs (2 * j + 1) ((x - wTwoCondExp Ψ (2 * j + 1) l m x
      : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : C(GibbsSpec.IConf (SU N), ℝ)) = F := by
    rw [hFdef]
    funext V
    show torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - torusObs (2 * j + 1) (w2Lift Ψ (2 * j + 1) l m (x : C(GibbsSpec.IConf (SU N), ℝ))) V
      = torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ)) V
        - w2Avg Φ l m (torusObs (2 * j + 1) (x : C(GibbsSpec.IConf (SU N), ℝ))) V
    rw [torusObs_w2Lift]
  have hg := w_gibbs_corr_le_of_fibre (Ψ.pos _) (Ψ.cont _) hlm hFc hzero hc H
  have hZ := integral_pos_weight (Ψ.pos (2 * j + 1)) (Ψ.cont (2 * j + 1))
  have hform : ∀ (k k' : WilsonHypercubic.Link 4 (2 * j + 1 + 1)),
      wForm Ψ j (wCondExp Ψ (2 * j + 1) k (x - wTwoCondExp Ψ (2 * j + 1) l m x))
          (wCondExp Ψ (2 * j + 1) k' (x - wTwoCondExp Ψ (2 * j + 1) l m x))
        = (∫ W, wAvg Φ k F W * wAvg Φ k' F W * Φ W
            ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => probHaar (SU N)))
          / ∫ W, Φ W
            ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => probHaar (SU N)) := by
    intro k k'
    show wExpect Φ (fun W => torusObs (2 * j + 1)
          (wLift Ψ (2 * j + 1) k ((x - wTwoCondExp Ψ (2 * j + 1) l m x
            : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : C(GibbsSpec.IConf (SU N), ℝ))) W
        * torusObs (2 * j + 1)
          (wLift Ψ (2 * j + 1) k' ((x - wTwoCondExp Ψ (2 * j + 1) l m x
            : ↥(periodicGaugeInvSubmodule (N := N) (2 * j + 1))) : C(GibbsSpec.IConf (SU N), ℝ))) W)
      = _
    rw [torusObs_wLift, torusObs_wLift, hF]
    rfl
  rw [hform l m, hform l l, hform m m]
  have e : ∀ A B Z : ℝ, Z ≠ 0 → c * (A / Z + B / Z) / 2 = c / 2 * (A + B) / Z := by
    intro A B Z hZ0
    field_simp
  rw [e _ _ _ hZ.ne']
  exact div_le_div_of_nonneg_right hg hZ.le

#print axioms wPairCorr_twoCond

/-- **`WPairCorrAt` from fibre hypotheses**: a non-negative defect matrix whose entries are fibre
constants of the pairs.

DERIVED: `0` is the lower end of the entries; `4`, `2 * j + 1`, `+ 1` as in `WPairCorrAt`. -/
theorem wPairCorrAt_of_fibreHyp (Ψ : TorusWeight N) (j : ℕ)
    (δ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ)
    (hδ0 : ∀ l m, 0 ≤ δ l m) (H : ∀ l m, l ≠ m → FibreHyp (Ψ.Φ (2 * j + 1)) l m (δ l m)) :
    WPairCorrAt Ψ j δ := fun l m hlm x =>
  ⟨wTwoCondExp Ψ (2 * j + 1) l m x, wCondExp_wTwoCondExp_l Ψ (2 * j + 1) hlm x,
    wCondExp_wTwoCondExp_m Ψ (2 * j + 1) l m x,
    wPairCorr_twoCond Ψ j hlm (hδ0 l m) (H l m hlm) x⟩

#print axioms wPairCorrAt_of_fibreHyp

end Torus

end MassGap.WeightedTorus
