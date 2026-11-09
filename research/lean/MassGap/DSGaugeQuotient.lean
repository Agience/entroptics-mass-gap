import Mathlib
import MassGap.DSBoxFloor

noncomputable section

/-!
# MassGap.DSGaugeQuotient — the Dobrushin–Shlosman box hypothesis on the gauge quotient

`DSBoxFloor.DSBoxInfluence` tests the box law against every function of the box links that is Lipschitz in the
summed link cost. The box law is invariant under the gauge transforms supported on the box's interior sites (the
sites all of whose links lie in the box), so only the interior-gauge-invariant test functions carry information:
those are the functions Lipschitz in the quotient pseudo-metric `min_h Σ_l v_l d(U_l, (h·V)_l)` of the box by its
interior gauge group. This module states the hypothesis on that class and proves it equivalent to the link form for
a bi-invariant cost, so the chain `DSBlockContract → DSOllivier → DSBoxFloor` consumes it unchanged.

1. **A bi-invariant cost** (`frob`, `frob_metric`, `frob_biInv`): the Frobenius distance on `SU(N)`, a continuous
   separating metric with `d(g a k, g b k) = d(a, b)`, via `‖X‖² = Re tr(Xᴴ X)`.
2. **Interior gauge transforms** (`IntSite`, `kI`, `glue_gauge_int`, `blkAvg_gauge_int`): a gauge transform supported
   on interior sites commutes with gluing the outside, and leaves the block average unchanged.
3. **Gauge averaging** (`avgG`, `continuous_avgG`, `readsOnly_avgG`, `lipD_avgG`, `gaugeInv_avgG`, `blkAvg_avgG`): the
   Haar average over the interior gauge group keeps continuity, the box support and the Lipschitz vector (for a
   bi-invariant cost), is interior-gauge invariant, and has the same block average (Fubini).
4. **The quotient hypothesis** (`BlkInflQ`, `blkInfl_iff_Q`, `DSBoxInfluenceQ`, `dsBox_of_Q`, `dsBoxQ_of_dsBox`):
   `BlkInflQ` quantifies only over interior-gauge-invariant test functions; for a bi-invariant cost it is equivalent
   to `BlkInfl`. So the quotient form is neither weaker nor trivially satisfied: it holds exactly when the link form
   holds.
5. **The Clay statement and the vacuity check** (`clay_continuum_of_DSBoxRunQ`, `dsBoxInfluenceQ_zero`).

## Where the link metric entered

No step of the Lean chain needs test functions that see the gauge: `blkInfl_iff_Q` shows the box hypothesis on all
link-Lipschitz functions equals its restriction to interior-gauge-invariant ones. `DSOllivier` runs on all of
`C(IConf, ℝ)` and restricts to the periodic gauge-invariant observables at the end, so its Stone–Weierstrass density
is never asked on the quotient. The full link metric entered only the coupled-chain read, whose synchronous coupling
measures the distance of gauge-variant link variables.

DERIVED (module-wide): `4` the spacetime dimension; `2 * j + 1` the index; `0`, `1` the signs and the unit of the
group; `2` the squares.
-/

namespace MassGap.DSGaugeQuotient

open scoped Matrix
open MeasureTheory Filter
open MassGap MassGap.DSBlockContract MassGap.DSOllivier MassGap.DSBoxFloor
open MassGap.DobrushinMixed (LipD)
open MassGap.HeatBath (wt continuous_wt wt_pos exists_abs_le integrable_of_abs_le bdT)
open MassGap.BlockHeatBath
open MassGap.BoxGap (glue glue_of_mem glue_of_not_mem)
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

variable {N : ℕ}

/-! ## 1. The Frobenius cost -/

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/-- `‖X‖² = Re tr(Xᴴ X)` for the Frobenius norm. DERIVED: `2` the square. -/
theorem frob_sq (X : Matrix (Fin N) (Fin N) ℂ) : ‖X‖ ^ 2 = (Matrix.trace (Xᴴ * X)).re := by
  have h1 : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Real.rpow_two _
  have h2 : (Matrix.trace (Xᴴ * X)).re = ∑ j, ∑ i, ‖X i j‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← starRingEnd_apply, RCLike.conj_mul]
    norm_cast
  rw [h1, h2, Finset.sum_comm]

#print axioms frob_sq

/-- A unitary factor on the left keeps the norm. DERIVED: `2` the square. -/
theorem frob_unitary_mul {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) : ‖u * X‖ = ‖X‖ := by
  have hu' : uᴴ * u = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hu
  have h : ‖u * X‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [frob_sq, frob_sq, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ u X, hu',
      Matrix.one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- A unitary factor on the right keeps the norm. DERIVED: `2` the square. -/
theorem frob_mul_unitary {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) : ‖X * u‖ = ‖X‖ := by
  have hu' : u * uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hu
  have ht : Matrix.trace ((X * u)ᴴ * (X * u)) = Matrix.trace (Xᴴ * X) := by
    calc Matrix.trace ((X * u)ᴴ * (X * u)) = Matrix.trace (uᴴ * (Xᴴ * X * u)) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Xᴴ * X * u * uᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Xᴴ * X) := by rw [Matrix.mul_assoc (Xᴴ * X), hu', Matrix.mul_one]
  have h : ‖X * u‖ ^ 2 = ‖X‖ ^ 2 := by
    rw [frob_sq, frob_sq, ht]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- **The Frobenius distance on `SU(N)`.** DERIVED: no numeral. -/
def frob (a b : SU N) : ℝ := ‖(a : Matrix (Fin N) (Fin N) ℂ) - b‖

/-- **The Frobenius distance is a continuous separating metric.** DERIVED: `0` the diagonal. -/
theorem frob_metric {Lk : Type} : CostMetric (fun _ : Lk => frob (N := N)) where
  cont _ := by
    unfold frob
    exact ((continuous_subtype_val.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd)).norm
  nonneg _ a b := norm_nonneg _
  refl _ a := by simp [frob]
  sep _ a b h := by
    unfold frob at h
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp h))
  symm _ a b := norm_sub_rev _ _
  tri _ a b c := norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- A cost is **bi-invariant** when `d(g a k, g b k) = d(a, b)`. DERIVED: no numeral. -/
def BiInv (d0 : SU N → SU N → ℝ) : Prop := ∀ g k a b : SU N, d0 (g * a * k) (g * b * k) = d0 a b

/-- **The Frobenius distance is bi-invariant.** DERIVED: no numeral. -/
theorem frob_biInv : BiInv (frob (N := N)) := by
  intro g k a b
  have hg : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  have hk : (k : Matrix (Fin N) (Fin N) ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp k.2).1
  unfold frob
  have e : ((g * a * k : SU N) : Matrix (Fin N) (Fin N) ℂ) - ((g * b * k : SU N) : Matrix (Fin N) (Fin N) ℂ)
      = (g : Matrix (Fin N) (Fin N) ℂ) * ((a : Matrix (Fin N) (Fin N) ℂ) - b) * k := by
    show (g : Matrix (Fin N) (Fin N) ℂ) * a * k - (g : Matrix (Fin N) (Fin N) ℂ) * b * k = _
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [e, frob_mul_unitary hk, frob_unitary_mul hg]

#print axioms frob_biInv

end Frob

/-! ## 2. Interior gauge transforms -/

section Interior

variable {M : ℕ}

/-- **An interior site of `S`**: every link with an endpoint at `x` lies in `S`. DERIVED: no numeral. -/
def IntSite (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (x : WilsonHypercubic.Site 4 (M + 1)) : Prop :=
  ∀ l : WilsonHypercubic.Link 4 (M + 1), (l.2 = x ∨ WilsonHypercubic.shift l.1 l.2 = x) → l ∈ S

open Classical in
/-- **The gauge field cut to the interior**: `h` on interior sites, `1` elsewhere. DERIVED: `1` the unit. -/
def kI (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (h : WilsonHypercubic.Site 4 (M + 1) → SU N) :
    WilsonHypercubic.Site 4 (M + 1) → SU N :=
  fun x => if IntSite S x then h x else 1

/-- A gauge field is **supported on the interior**. DERIVED: `1` the unit. -/
def SuppInt (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (h : WilsonHypercubic.Site 4 (M + 1) → SU N) : Prop :=
  ∀ x, ¬ IntSite S x → h x = 1

/-- DERIVED: `1` the unit. -/
theorem suppInt_kI (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (h : WilsonHypercubic.Site 4 (M + 1) → SU N) :
    SuppInt S (kI S h) := fun x hx => by
  classical
  simp only [kI, if_neg hx]

/-- **Interior-gauge invariance** of a function of the configuration. DERIVED: no numeral. -/
def GaugeInvI (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    (g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ) : Prop :=
  ∀ h : WilsonHypercubic.Site 4 (M + 1) → SU N, SuppInt S h →
    ∀ U, g (LocalGauge.gaugeTransform h U) = g U

/-- **An interior gauge transform commutes with gluing the outside.** DERIVED: `1` the unit. -/
theorem glue_gauge_int (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {h : WilsonHypercubic.Site 4 (M + 1) → SU N} (hh : SuppInt S h) (W V : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    LocalGauge.gaugeTransform h (glue S W V) = glue S W (LocalGauge.gaugeTransform h V) := by
  funext l
  by_cases hl : l ∈ S
  · show h l.2 * glue S W V l * (h (WilsonHypercubic.shift l.1 l.2))⁻¹ = glue S W _ l
    rw [glue_of_mem hl, glue_of_mem hl]
    rfl
  · have h1 : h l.2 = 1 := hh _ fun hx => hl (hx l (Or.inl rfl))
    have h2 : h (WilsonHypercubic.shift l.1 l.2) = 1 := hh _ fun hx => hl (hx l (Or.inr rfl))
    show h l.2 * glue S W V l * (h (WilsonHypercubic.shift l.1 l.2))⁻¹ = glue S W _ l
    rw [glue_of_not_mem hl, glue_of_not_mem hl, h1, h2]
    simp

#print axioms glue_gauge_int

/-- **The block numerator is unchanged by an interior gauge transform of the test function.**

DERIVED: no numeral. -/
theorem blkNum_gauge_int (β : ℝ) (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {h : WilsonHypercubic.Site 4 (M + 1) → SU N} (hh : SuppInt S h)
    (g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    blkNum (bdT M) β S (fun U => g (LocalGauge.gaugeTransform h U)) W = blkNum (bdT M) β S g W := by
  have hmp := LocalGauge.gaugeEquiv_measurePreserving (d := 4) (n := M + 1) (SU N) h
  unfold blkNum
  have hwt : ∀ V, wt (bdT M) β (glue S W V) = wt (bdT M) β (glue S W (LocalGauge.gaugeTransform h V)) := by
    intro V
    rw [← glue_gauge_int S hh W V]
    exact (LocalGauge.boltz_gauge_invariant_local h β _).symm
  refine (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)).trans
    (hmp.integral_comp' (fun V => g (glue S W V) * wt (bdT M) β (glue S W V)))
  show g (LocalGauge.gaugeTransform h (glue S W V)) * wt (bdT M) β (glue S W V)
    = g (glue S W (LocalGauge.gaugeTransform h V)) * wt (bdT M) β (glue S W (LocalGauge.gaugeTransform h V))
  rw [glue_gauge_int S hh W V, ← hwt V]

#print axioms blkNum_gauge_int

end Interior

/-! ## 3. Gauge averaging over the interior -/

section Avg

variable {M : ℕ}

/-- The product Haar measure on gauge fields. -/
local notation "μG" => Measure.pi fun _ : WilsonHypercubic.Site 4 (M + 1) => probHaar (SU N)

/-- **The interior gauge average**: `ḡ(U) = ∫ g(kI h · U) dh`. DERIVED: no numeral. -/
def avgG (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ)
    (U : WilsonHypercubic.Link 4 (M + 1) → SU N) : ℝ :=
  ∫ h, g (LocalGauge.gaugeTransform (kI S h) U) ∂μG

/-- The gauge action is jointly continuous. DERIVED: no numeral. -/
theorem continuous_gauge_joint (S : Finset (WilsonHypercubic.Link 4 (M + 1))) :
    Continuous (fun p : (WilsonHypercubic.Site 4 (M + 1) → SU N) × (WilsonHypercubic.Link 4 (M + 1) → SU N) =>
      LocalGauge.gaugeTransform (kI S p.1) p.2) := by
  classical
  have hk : ∀ x, Continuous (fun h : WilsonHypercubic.Site 4 (M + 1) → SU N => kI S h x) := by
    intro x
    unfold kI
    split_ifs
    · exact continuous_apply x
    · exact continuous_const
  refine continuous_pi fun l => ?_
  show Continuous (fun p : (WilsonHypercubic.Site 4 (M + 1) → SU N) × (WilsonHypercubic.Link 4 (M + 1) → SU N) =>
    kI S p.1 l.2 * p.2 l * (kI S p.1 (WilsonHypercubic.shift l.1 l.2))⁻¹)
  exact (((hk _).comp continuous_fst).mul ((continuous_apply l).comp continuous_snd)).mul
    ((hk _).comp continuous_fst).inv

/-- DERIVED: no numeral. -/
theorem continuous_avgG (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ} (hg : Continuous g) : Continuous (avgG S g) := by
  obtain ⟨C, hC⟩ := exists_abs_le hg
  have hj := continuous_gauge_joint (N := N) S
  refine continuous_of_dominated (bound := fun _ => C) (fun U => ?_) (fun U => ?_) (integrable_const C) ?_
  · exact (hg.comp (hj.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun h => by rw [Real.norm_eq_abs]; exact hC _
  · refine Filter.Eventually.of_forall fun h => ?_
    have hc : Continuous fun U : WilsonHypercubic.Link 4 (M + 1) → SU N =>
        LocalGauge.gaugeTransform (kI S h) U := by
      refine continuous_pi fun l => ?_
      show Continuous (fun U : WilsonHypercubic.Link 4 (M + 1) → SU N =>
        kI S h l.2 * U l * (kI S h (WilsonHypercubic.shift l.1 l.2))⁻¹)
      exact (continuous_const.mul (continuous_apply l)).mul continuous_const
    exact hg.comp hc

#print axioms continuous_avgG

/-- **The average keeps the box support.** DERIVED: no numeral. -/
theorem readsOnly_avgG (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ} (hR : ReadsOnly S g) : ReadsOnly S (avgG S g) := by
  intro U U' hUU
  unfold avgG
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => hR _ _ fun l hl => ?_)
  show kI S h l.2 * U l * (kI S h (WilsonHypercubic.shift l.1 l.2))⁻¹
    = kI S h l.2 * U' l * (kI S h (WilsonHypercubic.shift l.1 l.2))⁻¹
  rw [hUU l hl]

#print axioms readsOnly_avgG

/-- **The average keeps the Lipschitz vector** for a bi-invariant cost. DERIVED: no numeral. -/
theorem lipD_avgG (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {d0 : SU N → SU N → ℝ} (hbi : BiInv d0)
    {g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ} (hg : Continuous g) {v : WilsonHypercubic.Link 4 (M + 1) → ℝ}
    (hv : LipD (fun _ => d0) g v) : LipD (fun _ => d0) (avgG S g) v := by
  refine ⟨hv.1, fun U k x => ?_⟩
  obtain ⟨C, hC⟩ := exists_abs_le hg
  have hj := continuous_gauge_joint (N := N) S
  have hint : ∀ U', Integrable (fun h => g (LocalGauge.gaugeTransform (kI S h) U')) μG := fun U' =>
    integrable_of_abs_le _ (hg.comp (hj.comp (continuous_id.prodMk continuous_const))).measurable
      (fun h => hC _)
  have hupd : ∀ h : WilsonHypercubic.Site 4 (M + 1) → SU N,
      LocalGauge.gaugeTransform (kI S h) (Function.update U k x)
        = Function.update (LocalGauge.gaugeTransform (kI S h) U) k
          (kI S h k.2 * x * (kI S h (WilsonHypercubic.shift k.1 k.2))⁻¹) := by
    intro h
    funext l
    by_cases hl : l = k
    · subst hl
      show kI S h l.2 * Function.update U l x l * _ = _
      rw [Function.update_self, Function.update_self]
    · show kI S h l.2 * Function.update U k x l * _ = _
      rw [Function.update_of_ne hl, Function.update_of_ne hl]
      rfl
  unfold avgG
  rw [← integral_sub (hint _) (hint _)]
  calc |∫ h, (g (LocalGauge.gaugeTransform (kI S h) (Function.update U k x))
          - g (LocalGauge.gaugeTransform (kI S h) U)) ∂μG|
      ≤ ∫ h, v k * d0 x (U k) ∂μG := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (integrable_const _) (Filter.Eventually.of_forall fun h => ?_)
        rw [Real.norm_eq_abs, hupd]
        have h1 := hv.2 (LocalGauge.gaugeTransform (kI S h) U) k
          (kI S h k.2 * x * (kI S h (WilsonHypercubic.shift k.1 k.2))⁻¹)
        have h2 : (LocalGauge.gaugeTransform (kI S h) U) k
            = kI S h k.2 * U k * (kI S h (WilsonHypercubic.shift k.1 k.2))⁻¹ := rfl
        rw [h2] at h1
        beta_reduce at h1
        rw [hbi] at h1
        exact h1
    _ = v k * d0 x (U k) := by simp

#print axioms lipD_avgG

/-- Composition of gauge transforms. DERIVED: no numeral. -/
theorem gauge_gauge (a b : WilsonHypercubic.Site 4 (M + 1) → SU N) (U : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    LocalGauge.gaugeTransform a (LocalGauge.gaugeTransform b U) = LocalGauge.gaugeTransform (a * b) U := by
  funext l
  show a l.2 * (b l.2 * U l * (b (WilsonHypercubic.shift l.1 l.2))⁻¹) * (a (WilsonHypercubic.shift l.1 l.2))⁻¹
    = (a l.2 * b l.2) * U l * (a (WilsonHypercubic.shift l.1 l.2) * b (WilsonHypercubic.shift l.1 l.2))⁻¹
  group

/-- **The average is interior-gauge invariant.** DERIVED: `1` the unit. -/
theorem gaugeInv_avgG (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    (g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ) : GaugeInvI S (avgG S g) := by
  classical
  intro k hk U
  have hmul : ∀ h : WilsonHypercubic.Site 4 (M + 1) → SU N, kI S h * k = kI S (h * k) := by
    intro h
    funext x
    simp only [Pi.mul_apply, kI]
    split_ifs with hx
    · rfl
    · rw [hk x hx, one_mul]
  set E : (WilsonHypercubic.Site 4 (M + 1) → SU N) ≃ᵐ (WilsonHypercubic.Site 4 (M + 1) → SU N) :=
    MeasurableEquiv.piCongrRight fun x => MeasurableEquiv.mulRight (k x)
  have hmp : MeasurePreserving E μG μG := by
    have hf : ∀ x : WilsonHypercubic.Site 4 (M + 1),
        MeasurePreserving (fun u : SU N => u * k x) (probHaar (SU N)) (probHaar (SU N)) :=
      fun x => measurePreserving_mul_right (probHaar (SU N)) (k x)
    refine ⟨E.measurable, ?_⟩
    show Measure.map (fun (h : WilsonHypercubic.Site 4 (M + 1) → SU N) (x : WilsonHypercubic.Site 4 (M + 1)) =>
      (fun u : SU N => u * k x) (h x)) μG = μG
    rw [Measure.pi_map_pi (fun x => (hf x).aemeasurable)]
    exact congrArg Measure.pi (funext fun x => (hf x).map_eq)
  unfold avgG
  simp only [gauge_gauge, hmul]
  exact hmp.integral_comp' (fun h => g (LocalGauge.gaugeTransform (kI S h) U))

#print axioms gaugeInv_avgG

/-- **The block average of the gauge average is the block average** (Fubini and `blkNum_gauge_int`).

DERIVED: no numeral. -/
theorem blkAvg_avgG (β : ℝ) (S : Finset (WilsonHypercubic.Link 4 (M + 1)))
    {g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ} (hg : Continuous g) (W : WilsonHypercubic.Link 4 (M + 1) → SU N) :
    blkAvg (bdT M) β S (avgG S g) W = blkAvg (bdT M) β S g W := by
  unfold blkAvg
  congr 1
  have hj := continuous_gauge_joint (N := N) S
  have hFc : Continuous (Function.uncurry fun (V : WilsonHypercubic.Link 4 (M + 1) → SU N)
      (h : WilsonHypercubic.Site 4 (M + 1) → SU N) =>
        g (LocalGauge.gaugeTransform (kI S h) (glue S W V)) * wt (bdT M) β (glue S W V)) := by
    have h1 : Continuous (fun p : (WilsonHypercubic.Link 4 (M + 1) → SU N) × (WilsonHypercubic.Site 4 (M + 1) → SU N)
        => (p.2, glue S W p.1)) :=
      continuous_snd.prodMk ((continuous_glue_right S W).comp continuous_fst)
    exact (hg.comp (hj.comp h1)).mul ((continuous_wt (bdT M) β).comp
      ((continuous_glue_right S W).comp continuous_fst))
  obtain ⟨C, hC⟩ := exists_abs_le hFc
  have hint := integrable_of_abs_le
    ((Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)).prod μG) hFc.measurable hC
  have e1 : blkNum (bdT M) β S (avgG S g) W
      = ∫ V, ∫ h, g (LocalGauge.gaugeTransform (kI S h) (glue S W V)) * wt (bdT M) β (glue S W V) ∂μG
          ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)) := by
    unfold blkNum avgG
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    show (∫ h, g (LocalGauge.gaugeTransform (kI S h) (glue S W V)) ∂μG) * wt (bdT M) β (glue S W V) = _
    rw [← integral_mul_const]
  rw [e1, integral_integral_swap hint]
  have e2 : (fun h : WilsonHypercubic.Site 4 (M + 1) → SU N =>
      ∫ V, g (LocalGauge.gaugeTransform (kI S h) (glue S W V)) * wt (bdT M) β (glue S W V)
        ∂(Measure.pi fun _ : WilsonHypercubic.Link 4 (M + 1) => probHaar (SU N)))
      = fun _ => blkNum (bdT M) β S g W :=
    funext fun h => blkNum_gauge_int β S (suppInt_kI S h) g W
  rw [e2, integral_const]
  simp

#print axioms blkAvg_avgG

end Avg

/-! ## 4. The quotient hypothesis -/

section Quot

variable {M : ℕ}

/-- **The block influence on interior-gauge-invariant test functions.** DERIVED: no numeral. -/
def BlkInflQ (β : ℝ) (S : Finset (WilsonHypercubic.Link 4 (M + 1))) (d0 : SU N → SU N → ℝ)
    (C : WilsonHypercubic.Link 4 (M + 1) → WilsonHypercubic.Link 4 (M + 1) → ℝ) : Prop :=
  ∀ g : (WilsonHypercubic.Link 4 (M + 1) → SU N) → ℝ, Continuous g → ReadsOnly S g → GaugeInvI S g →
    ∀ v, LipD (fun _ => d0) g v → ∀ (W : WilsonHypercubic.Link 4 (M + 1) → SU N) (k : WilsonHypercubic.Link 4 (M + 1)),
      k ∉ S → ∀ x : SU N,
        |blkAvg (bdT M) β S g (Function.update W k x) - blkAvg (bdT M) β S g W|
          ≤ (∑ l ∈ S, C l k * v l) * d0 x (W k)

/-- **For a bi-invariant cost, the quotient form is the link form.** DERIVED: no numeral. -/
theorem blkInfl_iff_Q (β : ℝ) (S : Finset (WilsonHypercubic.Link 4 (M + 1))) {d0 : SU N → SU N → ℝ}
    (hbi : BiInv d0) (C : WilsonHypercubic.Link 4 (M + 1) → WilsonHypercubic.Link 4 (M + 1) → ℝ) :
    BlkInfl (wilsonKer (bdT M) β S) (fun _ => d0) C ↔ BlkInflQ β S d0 C := by
  constructor
  · intro h g hg hR _ v hv W k hk x
    exact h g hg hR v hv W k hk x
  · intro h g hg hR v hv W k hk x
    have hq := h (avgG S g) (continuous_avgG S hg) (readsOnly_avgG S hR) (gaugeInv_avgG S g) v
      (lipD_avgG S hbi hg hv) W k hk x
    show |blkAvg (bdT M) β S g (Function.update W k x) - blkAvg (bdT M) β S g W| ≤ _
    rw [← blkAvg_avgG β S hg, ← blkAvg_avgG β S hg]
    exact hq

#print axioms blkInfl_iff_Q

/-- **The DS box hypothesis on the gauge quotient**: a bi-invariant continuous separating metric cost `d0` and a
matrix `C ≥ 0` bounding the influence of the outside on the box law, tested only against interior-gauge-invariant
functions, whose per-direction box average is at most `ρ`.

DERIVED: `2 * j + 1` the index; `0` the box corner and the sign. -/
def DSBoxInfluenceQ (β : ℝ) (L j : ℕ) (ρ : ℝ) : Prop :=
  ∃ d0 : SU N → SU N → ℝ, CostMetric (fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => d0) ∧ BiInv d0 ∧
    ∃ C : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ,
      (∀ l k, 0 ≤ C l k) ∧ BlkInflQ β (boxV (2 * j + 1) L 0) d0 C ∧
      ∀ μ : Fin 4, ∑ x ∈ boxSites (2 * j + 1) L μ, ∑ k ∈ (boxV (2 * j + 1) L 0)ᶜ, C (μ, x) k
        ≤ ρ * (boxSites (2 * j + 1) L μ).card

/-- **The quotient hypothesis gives the link hypothesis.** DERIVED: no numeral. -/
theorem dsBox_of_Q {β : ℝ} {L j : ℕ} {ρ : ℝ} (h : DSBoxInfluenceQ (N := N) β L j ρ) :
    DSBoxInfluence (N := N) β L j ρ := by
  obtain ⟨d0, hd, hbi, C, hC0, hC, hρ⟩ := h
  exact ⟨d0, hd, C, hC0, (blkInfl_iff_Q β _ hbi C).mpr hC, hρ⟩

#print axioms dsBox_of_Q

/-- **The link hypothesis in a bi-invariant cost gives the quotient hypothesis.** DERIVED: no numeral. -/
theorem dsBoxQ_of_dsBox {β : ℝ} {L j : ℕ} {ρ : ℝ} {d0 : SU N → SU N → ℝ}
    (hd : CostMetric (fun _ : WilsonHypercubic.Link 4 (2 * j + 1 + 1) => d0)) (hbi : BiInv d0)
    {C : WilsonHypercubic.Link 4 (2 * j + 1 + 1) → WilsonHypercubic.Link 4 (2 * j + 1 + 1) → ℝ}
    (hC0 : ∀ l k, 0 ≤ C l k) (hC : BlkInfl (wilsonKer (bdT (2 * j + 1)) β (boxV (2 * j + 1) L 0)) (fun _ => d0) C)
    (hρ : ∀ μ : Fin 4, ∑ x ∈ boxSites (2 * j + 1) L μ, ∑ k ∈ (boxV (2 * j + 1) L 0)ᶜ, C (μ, x) k
      ≤ ρ * (boxSites (2 * j + 1) L μ).card) :
    DSBoxInfluenceQ (N := N) β L j ρ :=
  ⟨d0, hd, hbi, C, hC0, (blkInfl_iff_Q β _ hbi C).mp hC, hρ⟩

#print axioms dsBoxQ_of_dsBox

end Quot

/-! ## 5. The Clay statement and the vacuity check -/

section Clay

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from the DS box criterion on the gauge quotient.**

DERIVED: `2` the least rank; `0` the signs; `4` the spacetime dimension; `1` the scale bound. -/
theorem clay_continuum_of_DSBoxRunQ (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ < 1)
    (hDS : ∀ᶠ β in atTop, ∀ᶠ j in atTop, DSBoxInfluenceQ (N := N) β
      (BlockGapDef.blockSide (fun β => κ * AsymptoticScaling.aRun N β) β) j ρ)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconvK : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_of_DSBoxRun hN2 hN Z τ hZ hB hL hκ hρ
    (hDS.mono fun _ h => h.mono fun _ h' => dsBox_of_Q h') O G hconvK hY

#print axioms clay_continuum_of_DSBoxRunQ

/-- **Vacuity check: the quotient hypothesis holds at `β = 0`** with the Frobenius cost and `ρ = 0`.

DERIVED: `0` the coupling, the matrix and `ρ`. -/
theorem dsBoxInfluenceQ_zero (L j : ℕ) : DSBoxInfluenceQ (N := N) 0 L j 0 := by
  refine ⟨frob, frob_metric, frob_biInv, fun _ _ => 0, fun _ _ => le_rfl, ?_, fun μ => by simp⟩
  intro g _ hR _ v _ W k hk x
  have hQ : blkAvg (bdT (2 * j + 1)) 0 (boxV (2 * j + 1) L 0) g (Function.update W k x)
      = blkAvg (bdT (2 * j + 1)) 0 (boxV (2 * j + 1) L 0) g W := by
    unfold blkAvg blkNum blkPart
    simp only [DSBoxFloor.wt_zero, mul_one]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    refine hR _ _ fun l hl => ?_
    rw [glue_of_mem hl, glue_of_mem hl]
  rw [hQ, sub_self, abs_zero]
  simp

#print axioms dsBoxInfluenceQ_zero

end Clay

end MassGap.DSGaugeQuotient
