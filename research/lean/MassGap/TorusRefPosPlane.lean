import Mathlib
import MassGap.SliceRPStrict
import MassGap.TorusRefPosProof
import MassGap.ExistencePosNonnull

/-!
# MassGap.TorusRefPosPlane — reflection positivity of every slice pair, and the sum of slices

On the periodic torus of extent `2M′ + 2` (`SliceRPStrict`), `Q_r = Qr q r` reads a function `q` of
the spatial links of the slice at time `r`. This module proves that every reflected slice pair
`⟨θ Q_r · Q_{r'}⟩` is nonnegative (M1) and that a sum of slices `Y = ∑_{r∈R} Q_r` has strictly
positive reflected value, and reduces `TorusCapstone.TorusRefPos` to the statement that the torus
reference vector is such a sum (`SliceForm`).

## Kernel level

`P_j = KernelPower.iter hS kT j = kT^{∗(j+1)}`, `H = SliceKernelPower.sand s u q`.

* `iter_gact_left`, `iter_gact_right`, `sand_gact_left`, `sand_gact_right`: the kernel powers, and
  so `H`, are gauge invariant in each argument, for every function `q`.
* `kT_eq_axis`: `kT(V, V') = C₀ ∫_A w(V) w(gact A V') exp((2β/N) κ(V, gact A V'))`, the identity
  behind `SliceKernelDefinite.sliceKernel_form_eq` read pointwise (`form_integrand_eq` at `u = 1`).
* `integral_shuffle`: `((a, b), (c, d)) ↦ ((a, c), (b, d))` preserves the integral of a continuous
  function of four slices.
* `integral_swap_gact2`: on pairs of slices, the axis averages of two kernels swap with the
  four-slice integral and drop out by the change of variables `(z', w) ↦ (gact A z', gact B w)`.
* `integral_jFun`: `∫ H(z,w') H(z',w) kT(z,z') kT(w',w) = C₀² · crossForm (hS ⊗ hS) coord2 (2β/N)
  (w ⊗ w · H)`, the link-plane crossing form on pairs of slices (`coord2`: the coordinates of both
  slices).
* `odd_pair_nonneg` (**M1, odd–odd**): for every continuous `q`, at `N ≠ 0`, `0 ≤ β`,
  `0 ≤ ∫∫ q(x) q(y) P_{2s+2}(x,y) P_{2u+2}(y,x)`. The six-slice Fubini (`phi6`) writes the left
  side as the four-slice integral above. The even–even case is `SliceKernelPower.sand_square`.

## Torus

* `torusState_refl_Qr_pair`: for `r' + r ≤ M`, `⟨θ Q_r · Q_{r'}⟩ = Zc(q(V 0) q(V (r'+r))) / Zc 1`
  (shift by `r`, `TorusChain.winF_refl`, `TorusChain.winF_shift`, `TorusChain.torusState_winF`).
* `Zc_one_pos`: the normalisation is positive.
* `torusState_refl_Qr_pair_nonneg`: for `1 ≤ r, r'`, `r + r' ≤ 2M′` and every continuous `q`,
  `0 ≤ ⟨θ Q_r · Q_{r'}⟩` (`SliceRPStrict.Zc_pair`; even `r + r'`: `sand_square`; odd:
  `odd_pair_nonneg`).
* `torusState_refl_sum_pos`: for a nonempty `R ⊆ [1, M′]` and `q` continuous, gauge invariant and
  nonzero, `0 < ⟨θY · Y⟩`: every pair term is `≥ 0` and the diagonal terms are `> 0`
  (`SliceRPStrict.torusState_refl_Qr_pos`).

## The reference reading

* `SliceForm hN M₀ O t ℓ`: eventually in `k`, the torus reference vector
  `Y_k = Yv (connectedS (stateT hN M₀) 1) k (refMono O t ℓ)` equals `∑_{r∈R} Qr q r` with `R` a
  nonempty set of times in `[1, M₀ 2ᵏ]` and `q` continuous, gauge invariant and nonzero.
* `torusRefPos_of_sliceForm`: `SliceForm → TorusRefPos` (`0 < dyBeta k`).
* `clay_canonical_sliceForm`: `TorusPassageProof.clay_canonical_refPassage` with `TorusRefPos`
  supplied by the slice form: `ClayContinuumPair` from `SliceForm`, `RefPassage` at some `ε < 1`,
  `hD` and `hW`.

`SliceForm` at `O = planePlaq N` is `SliceFormPlane.sliceForm_planePlaq`. Its content is
finite-torus bookkeeping: the
cube smear of `planePlaq N − c` is `∑_{x∈P} a⁴ T_x(planePlaq N − c)` (`ContinuumField.smear_eq_sum`,
the cube indicator at lattice sites), the sites `P` split into times `R` and a spatial box `B` (the
bijection of `ExistencePosNonnull.Yv_base_eq_slices`, without the shift `d_m`), each translate reads
the spatial links of one slice, and `q = ∑_{y∈B} a⁴ (P_y − c)` read through `SliceRPStrict.readSl`
is gauge invariant (each plaquette is conjugated, as in `SliceKernelDefinite.sp_gact`) and nonzero
(`ExistencePosNonnull.planeV_ne_zero`). Under `0 < t`, `0 < ℓ` and `2(t + ℓ) < M₀ · aRun N 1` the
times lie in `[1, M₀ 2ᵏ]` and no plaquette of `B` wraps, eventually in `k`.

Classification: finite-torus content inside `TorusCapstone.TorusRefPos`. With `SliceForm` at
`planePlaq N`, `hpos` (`ExistencePos.LagOnePos`) reduces to `RefPassage` alone, a relative comparison
on one fixed physical torus, eventually in `k` (uniform in the spacing); this is a reduction, not a
discharge.
-/

noncomputable section

namespace MassGap.TorusRefPosPlane

open MeasureTheory MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.RectTransfer
  MassGap.SliceKernelDefinite MassGap.SliceKernelPower MassGap.KernelInjective MassGap.KernelPower
  MassGap.CharacterExpansion

set_option linter.unusedSectionVars false

/-! ## 1. Kernel level: the odd–odd two-insertion chain is a crossing form -/

section Kernel

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

set_option hygiene false in
local notation "S₂" => ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
set_option hygiene false in
local notation "A₂" => ((TT μ T → SUN.SU N) × (TT μ T → SUN.SU N))

/-! The Borel structure of pairs of slices and of pairs of axis configurations, stated once so
that the instances on their products are found. -/

instance instSecondCountableSl2 :
    SecondCountableTopology ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) := inferInstance
instance instBorelSl2 : BorelSpace ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) := inferInstance
instance instSecondCountableSl4 :
    SecondCountableTopology (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) := inferInstance
instance instBorelSl4 : BorelSpace (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
    × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) := inferInstance
instance instSecondCountableAx2 :
    SecondCountableTopology ((TT μ T → SUN.SU N) × (TT μ T → SUN.SU N)) := inferInstance
instance instBorelAx2 : BorelSpace ((TT μ T → SUN.SU N) × (TT μ T → SUN.SU N)) := inferInstance

/-- The kernel powers are gauge invariant in the first argument. -/
theorem iter_gact_left (β : ℝ) (g : TT μ T → SUN.SU N) :
    ∀ (j : ℕ) (V V' : SpT μ T → SUN.SU N),
      iter (hS μ T N) (kT μ T N β) j (gact g V) V' = iter (hS μ T N) (kT μ T N β) j V V'
  | 0, V, V' => kT_gact_left β g V V'
  | j + 1, V, V' => by
    show ∫ y, kT μ T N β (gact g V) y * iter (hS μ T N) (kT μ T N β) j y V' ∂(hS μ T N)
      = ∫ y, kT μ T N β V y * iter (hS μ T N) (kT μ T N β) j y V' ∂(hS μ T N)
    simp only [kT_gact_left]

theorem iter_symm' (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) (V V' : SpT μ T → SUN.SU N) :
    iter (hS μ T N) (kT μ T N β) j V V' = iter (hS μ T N) (kT μ T N β) j V' V :=
  CyclicKernel.iter_symm (μ := hS μ T N) (bdd_kT (μ := μ) (T := T) hN hβ) (kT_symm β) j V V'

/-- The kernel powers are gauge invariant in the second argument. -/
theorem iter_gact_right (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (g : TT μ T → SUN.SU N) (j : ℕ)
    (V V' : SpT μ T → SUN.SU N) :
    iter (hS μ T N) (kT μ T N β) j V (gact g V') = iter (hS μ T N) (kT μ T N β) j V V' := by
  rw [iter_symm' hN hβ j V (gact g V'), iter_gact_left, iter_symm' hN hβ j V' V]

theorem sand_gact_left (β : ℝ) (r m : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (g : TT μ T → SUN.SU N) (z z' : SpT μ T → SUN.SU N) :
    sand μ T N β r m q (gact g z) z' = sand μ T N β r m q z z' := by
  unfold sand
  simp only [iter_gact_left]

theorem sand_gact_right (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (r m : ℕ)
    (q : (SpT μ T → SUN.SU N) → ℝ) (g : TT μ T → SUN.SU N) (z z' : SpT μ T → SUN.SU N) :
    sand μ T N β r m q z (gact g z') = sand μ T N β r m q z z' := by
  unfold sand
  simp only [iter_gact_right hN hβ]

variable (μ T N) in
/-- The Wilson density of the plaquette of one slice in directions `(ν, ν')` at `y`:
`wilsonDensity (V_{(ν,y)} V_{(ν', y+ν)} V_{(ν, y+ν')}⁻¹ V_{(ν', y)}⁻¹)`. -/
def plaqSl (ν ν' : {j : Fin 4 // j ≠ μ}) (y : TT μ T) (V : SpT μ T → SUN.SU N) : ℝ :=
  WilsonAction.wilsonDensity (V (ν, y) * (V (ν', tsh μ T ν y)
    * ((V (ν, tsh μ T ν' y))⁻¹ * (V (ν', y))⁻¹)))

/-- **A plaquette of one slice is gauge invariant**: it is conjugated by `g_y`. -/
theorem plaqSl_gact (ν ν' : {j : Fin 4 // j ≠ μ}) (y : TT μ T) (g : TT μ T → SUN.SU N)
    (V : SpT μ T → SUN.SU N) : plaqSl μ T N ν ν' y (gact g V) = plaqSl μ T N ν ν' y V := by
  have e : ∀ a b c d p q r s : SUN.SU N,
      a * p * b⁻¹ * (b * q * d⁻¹ * ((c * r * d⁻¹)⁻¹ * (a * s * c⁻¹)⁻¹))
        = a * (p * (q * (r⁻¹ * s⁻¹))) * a⁻¹ := by
    intros; group
  unfold plaqSl
  simp only [gact]
  rw [tsh_comm ν' ν y, e, WilsonAction.wilsonDensity_conj]

/-- A weighted sum of plaquettes of one slice, shifted by a constant, is gauge invariant. -/
theorem gaugeInv_plaqSum (ν ν' : {j : Fin 4 // j ≠ μ}) (B : Finset (TT μ T)) (s c : ℝ) :
    GaugeInv (fun V : SpT μ T → SUN.SU N => ∑ y ∈ B, s * (plaqSl μ T N ν ν' y V - c)) :=
  fun g V => by simp only [plaqSl_gact]

/-- The slice kernel as an axis average of the link-plane kernel, with the weight read at the
transformed second slice. -/
theorem kT_eq_axis (β : ℝ) (V V' : SpT μ T → SUN.SU N) :
    kT μ T N β V V' = cZero μ T β * ∫ A, wt μ T N β V * wt μ T N β (gact A V')
      * Real.exp (2 * β / N * coordKernel planeCoord V (gact A V')) ∂(hA μ T N) := by
  have h := form_integrand_eq (μ := μ) (T := T) (N := N) β (u := fun _ => (1 : ℝ))
    (fun _ _ => rfl) (V, V')
  simp only [ffun, one_mul, mul_one] at h
  exact h

/-- A parametric integral of a continuous function on a compact space is continuous. -/
theorem continuous_integral_snd {Y Z : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    [LocallyCompactSpace Y] [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [SecondCountableTopologyEither Z ℝ] [CompactSpace Z] (ν : Measure Z) [IsFiniteMeasure ν]
    {F : Y → Z → ℝ} (hF : Continuous (Function.uncurry F)) :
    Continuous fun y => ∫ z, F y z ∂ν := by
  have hc := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
  simp only [Measure.restrict_univ] at hc
  exact hc

/-- **The middle shuffle** `((a, b), (c, d)) ↦ ((a, c), (b, d))` preserves the integral of a
continuous function on four slices. -/
theorem integral_shuffle
    {F : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) → ℝ} (hF : Continuous F) :
    ∫ W, F ((W.1.1, W.2.1), (W.1.2, W.2.2))
        ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
      = ∫ W, F W ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) := by
  have key : ∀ H : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) → ℝ, Continuous H →
      ∫ W, H W ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
        = ∫ a, ∫ b, ∫ c, ∫ d, H ((a, b), (c, d)) ∂(hS μ T N) ∂(hS μ T N) ∂(hS μ T N)
            ∂(hS μ T N) := by
    intro H hH
    rw [integral_prod H (KernelInjective.integrable_of_continuous hH)]
    have hin : Continuous fun p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
        ∫ p', H (p, p') ∂((hS μ T N).prod (hS μ T N)) :=
      continuous_integral_snd _ (F := fun p p' => H (p, p')) hH
    rw [integral_prod _ (KernelInjective.integrable_of_continuous hin)]
    congr 1; funext a; congr 1; funext b
    exact integral_prod _ (KernelInjective.integrable_of_continuous
      (hH.comp (continuous_const.prodMk continuous_id)))
  have hc1 : Continuous fun W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => F ((W.1.1, W.2.1), (W.1.2, W.2.2)) :=
    hF.comp (by fun_prop)
  have k1 := key _ hc1
  have k2 := key _ hF
  dsimp only at k1 k2
  rw [k1, k2]
  congr 1; funext a
  have hc : Continuous fun p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      ∫ d, F ((a, p.2), (p.1, d)) ∂(hS μ T N) :=
    continuous_integral_snd _
      (F := fun (p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) (d : SpT μ T → SUN.SU N) =>
        F ((a, p.2), (p.1, d)))
      (hF.comp (by fun_prop))
  exact integral_integral_swap (KernelInjective.integrable_of_continuous hc)

variable (μ T N) in
/-- The gauge action on a pair of slices. -/
def gact2 (AB : (TT μ T → SUN.SU N) × (TT μ T → SUN.SU N)) :
    (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) → (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) :=
  Prod.map (gact AB.1) (gact AB.2)

theorem measurePreserving_gact2 (AB : (TT μ T → SUN.SU N) × (TT μ T → SUN.SU N)) :
    MeasurePreserving (gact2 μ T N AB) ((hS μ T N).prod (hS μ T N)) ((hS μ T N).prod (hS μ T N)) :=
  (measurePreserving_gact AB.1).prod (measurePreserving_gact AB.2)

theorem integral_gact2_snd (AB : (TT μ T → SUN.SU N) × (TT μ T → SUN.SU N))
    {F : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) → ℝ} (hF : Continuous F) :
    ∫ W, F (W.1, gact2 μ T N AB W.2)
        ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
      = ∫ W, F W ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) := by
  have hmp : MeasurePreserving (Prod.map id (gact2 μ T N AB))
      (((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
      (((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) :=
    (MeasurePreserving.id _).prod (measurePreserving_gact2 AB)
  have h := integral_map (μ := ((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
    hmp.measurable.aemeasurable
    (hF.aestronglyMeasurable (μ := Measure.map (Prod.map id (gact2 μ T N AB))
      (((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))))
  rw [hmp.map_eq] at h
  exact h.symm

theorem continuous_gact2_uncurry :
    Continuous fun p : ((TT μ T → SUN.SU N) × (TT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => gact2 μ T N p.1 p.2 := by
  have hg := continuous_gact_uncurry (μ := μ) (T := T) (N := N)
  have h1 : Continuous fun p : ((TT μ T → SUN.SU N) × (TT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => gact p.1.1 p.2.1 :=
    Continuous.comp' (f := fun p : A₂ × S₂ => (p.1.1, p.2.1)) hg (by fun_prop)
  have h2 : Continuous fun p : ((TT μ T → SUN.SU N) × (TT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => gact p.1.2 p.2.2 :=
    Continuous.comp' (f := fun p : A₂ × S₂ => (p.1.2, p.2.2)) hg (by fun_prop)
  exact h1.prodMk h2

/-- The axis averages and the four-slice integral swap, and the change of variables removes the
axis averages. -/
theorem integral_swap_gact2
    {F : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) → ℝ} (hF : Continuous F) :
    ∫ W, ∫ AB, F (W.1, gact2 μ T N AB W.2) ∂((hA μ T N).prod (hA μ T N))
        ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
      = ∫ W, F W ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) := by
  have hφ : Continuous fun p : (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)))
        × ((TT μ T → SUN.SU N) × (TT μ T → SUN.SU N)) =>
      ((p.1.1, gact2 μ T N p.2 p.1.2) : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) :=
    (show Continuous fun p : (S₂ × S₂) × A₂ => p.1.1 by fun_prop).prodMk
      (Continuous.comp' (f := fun p : (S₂ × S₂) × A₂ => (p.2, p.1.2)) continuous_gact2_uncurry
        (by fun_prop))
  have hG : Integrable (Function.uncurry fun (W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)))
      (AB : (TT μ T → SUN.SU N) × (TT μ T → SUN.SU N)) => F (W.1, gact2 μ T N AB W.2))
      ((((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))).prod
        ((hA μ T N).prod (hA μ T N))) :=
    KernelInjective.integrable_of_continuous (hF.comp hφ)
  refine (integral_integral_swap hG).trans ?_
  refine (integral_congr_ae (Filter.Eventually.of_forall fun AB => integral_gact2_snd AB hF)).trans ?_
  rw [integral_const, probReal_univ, one_smul]

variable (μ T N) in
/-- The coordinates of a pair of slices: those of the first slice, then those of the second. -/
def coord2 : (SpT μ T × Coord N) ⊕ (SpT μ T × Coord N) →
    (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) → ℝ
  | Sum.inl q, z => planeCoord q z.1
  | Sum.inr q, z => planeCoord q z.2

theorem continuous_coord2 : ∀ p, Continuous (coord2 μ T N p)
  | Sum.inl q => (continuous_planeCoord q).comp continuous_fst
  | Sum.inr q => (continuous_planeCoord q).comp continuous_snd

theorem coordKernel_coord2 (z z' : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) :
    coordKernel (coord2 μ T N) z z'
      = coordKernel planeCoord z.1 z'.1 + coordKernel planeCoord z.2 z'.2 := by
  unfold coordKernel
  rw [Fintype.sum_sum_type]
  rfl

variable (μ T N) in
/-- The weighted pair function `w(z) w(z') H(z, z')`, `H = sand s u q`. -/
def fPair (β : ℝ) (s u : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (p : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) : ℝ :=
  wt μ T N β p.1 * wt μ T N β p.2 * sand μ T N β s u q p.1 p.2

theorem continuous_fPair (β : ℝ) (s u : ℕ) {q : (SpT μ T → SUN.SU N) → ℝ} (hq : Continuous q) :
    Continuous (fPair μ T N β s u q) :=
  (((continuous_wt β).comp continuous_fst).mul ((continuous_wt β).comp continuous_snd)).mul
    (continuous_sand β s u hq)

variable (μ T N) in
/-- The four-slice integrand `H(z,w') H(z',w) kT(z,z') kT(w',w)`, written at
`W = ((z, w'), (z', w))`. -/
def jFun (β : ℝ) (s u : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) : ℝ :=
  sand μ T N β s u q W.1.1 W.1.2 * sand μ T N β s u q W.2.1 W.2.2
    * (kT μ T N β W.1.1 W.2.1 * kT μ T N β W.1.2 W.2.2)

variable (μ T N) in
/-- The crossing-form integrand on pairs. -/
def psiFun (β : ℝ) (s u : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) : ℝ :=
  fPair μ T N β s u q W.1 * fPair μ T N β s u q W.2
    * Real.exp (2 * β / N * coordKernel (coord2 μ T N) W.1 W.2)

theorem continuous_psiFun (β : ℝ) (s u : ℕ) {q : (SpT μ T → SUN.SU N) → ℝ} (hq : Continuous q) :
    Continuous (psiFun μ T N β s u q) :=
  (((continuous_fPair β s u hq).comp continuous_fst).mul
    ((continuous_fPair β s u hq).comp continuous_snd)).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_coordKernel continuous_coord2)))

/-- Pointwise: the four-slice integrand is `C₀²` times the axis average of the pair crossing
integrand. -/
theorem jFun_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (s u : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) :
    jFun μ T N β s u q W = cZero μ T β ^ 2
      * ∫ AB, psiFun μ T N β s u q (W.1, gact2 μ T N AB W.2) ∂((hA μ T N).prod (hA μ T N)) := by
  have hpt : ∀ AB : (TT μ T → SUN.SU N) × (TT μ T → SUN.SU N),
      psiFun μ T N β s u q (W.1, gact2 μ T N AB W.2)
        = (sand μ T N β s u q W.1.1 W.1.2 * sand μ T N β s u q W.2.1 W.2.2)
          * ((wt μ T N β W.1.1 * wt μ T N β (gact AB.1 W.2.1)
              * Real.exp (2 * β / N * coordKernel planeCoord W.1.1 (gact AB.1 W.2.1)))
            * (wt μ T N β W.1.2 * wt μ T N β (gact AB.2 W.2.2)
              * Real.exp (2 * β / N * coordKernel planeCoord W.1.2 (gact AB.2 W.2.2)))) := by
    intro AB
    simp only [psiFun, fPair, gact2, Prod.map_fst, Prod.map_snd, coordKernel_coord2]
    rw [sand_gact_left, sand_gact_right hN hβ, mul_add, Real.exp_add]
    ring
  have hp : ∫ AB : (TT μ T → SUN.SU N) × (TT μ T → SUN.SU N),
        (wt μ T N β W.1.1 * wt μ T N β (gact AB.1 W.2.1)
          * Real.exp (2 * β / N * coordKernel planeCoord W.1.1 (gact AB.1 W.2.1)))
        * (wt μ T N β W.1.2 * wt μ T N β (gact AB.2 W.2.2)
          * Real.exp (2 * β / N * coordKernel planeCoord W.1.2 (gact AB.2 W.2.2)))
        ∂((hA μ T N).prod (hA μ T N))
      = (∫ A, wt μ T N β W.1.1 * wt μ T N β (gact A W.2.1)
          * Real.exp (2 * β / N * coordKernel planeCoord W.1.1 (gact A W.2.1)) ∂(hA μ T N))
        * ∫ B, wt μ T N β W.1.2 * wt μ T N β (gact B W.2.2)
          * Real.exp (2 * β / N * coordKernel planeCoord W.1.2 (gact B W.2.2)) ∂(hA μ T N) :=
    integral_prod_mul (fun A => wt μ T N β W.1.1 * wt μ T N β (gact A W.2.1)
      * Real.exp (2 * β / N * coordKernel planeCoord W.1.1 (gact A W.2.1)))
      (fun B => wt μ T N β W.1.2 * wt μ T N β (gact B W.2.2)
      * Real.exp (2 * β / N * coordKernel planeCoord W.1.2 (gact B W.2.2)))
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hp]
  unfold jFun
  rw [kT_eq_axis β W.1.1 W.2.1, kT_eq_axis β W.1.2 W.2.2]
  ring

/-- **The four-slice integral is a crossing form on pairs of slices.** -/
theorem integral_jFun (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (s u : ℕ)
    {q : (SpT μ T → SUN.SU N) → ℝ} (hq : Continuous q) :
    ∫ W, jFun μ T N β s u q W
        ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
      = cZero μ T β ^ 2 * crossForm ((hS μ T N).prod (hS μ T N)) (coord2 μ T N) (2 * β / N)
          (fPair μ T N β s u q) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (jFun_eq hN hβ s u q)), integral_const_mul,
    integral_swap_gact2 (continuous_psiFun β s u hq)]
  rfl

theorem integral_jFun_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (s u : ℕ)
    {q : (SpT μ T → SUN.SU N) → ℝ} (hq : Continuous q) :
    0 ≤ ∫ W, jFun μ T N β s u q W
        ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) := by
  rw [integral_jFun hN hβ s u hq]
  exact mul_nonneg (pow_nonneg (cZero_pos β).le 2)
    (crossForm_nonneg ((hS μ T N).prod (hS μ T N)) continuous_coord2 (continuous_fPair β s u hq)
      (div_nonneg (mul_nonneg zero_le_two hβ) (Nat.cast_nonneg N)))

/-- `kT^{∗(2s+3)}(x, y) = ∫∫ kT^{∗(s+1)}(x, z) kT(z, z') kT^{∗(s+1)}(z', y)`. -/
theorem iter_odd_eq (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (s : ℕ) (x y : SpT μ T → SUN.SU N) :
    iter (hS μ T N) (kT μ T N β) (s + (s + 1) + 1) x y
      = ∫ P, iter (hS μ T N) (kT μ T N β) s x P.1
          * (kT μ T N β P.1 P.2 * iter (hS μ T N) (kT μ T N β) s P.2 y)
          ∂((hS μ T N).prod (hS μ T N)) := by
  have hc : Continuous fun P : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      iter (hS μ T N) (kT μ T N β) s x P.1
        * (kT μ T N β P.1 P.2 * iter (hS μ T N) (kT μ T N β) s P.2 y) :=
    ((continuous_iter β s).comp (continuous_const.prodMk continuous_fst)).mul
      ((continuous_kT β).mul ((continuous_iter β s).comp (continuous_snd.prodMk continuous_const)))
  rw [iter_add (μ := hS μ T N) (bdd_kT (μ := μ) (T := T) hN hβ) s (s + 1),
    integral_prod _ (KernelInjective.integrable_of_continuous hc)]
  show ∫ z, iter (hS μ T N) (kT μ T N β) s x z
      * (∫ z', kT μ T N β z z' * iter (hS μ T N) (kT μ T N β) s z' y ∂(hS μ T N)) ∂(hS μ T N) = _
  congr 1; funext z
  rw [← integral_const_mul]

variable (μ T N) in
/-- The six-slice integrand at `v = (x, y)`, `Q = ((z, z'), (w', w))`:
`q(x) q(y) P_s(x,z) kT(z,z') P_s(z',y) · P_u(x,w') kT(w',w) P_u(w,y)`. -/
def phi6 (β : ℝ) (s u : ℕ) (q : (SpT μ T → SUN.SU N) → ℝ)
    (v : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
    (Q : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) : ℝ :=
  q v.1 * q v.2
    * ((iter (hS μ T N) (kT μ T N β) s v.1 Q.1.1
        * (kT μ T N β Q.1.1 Q.1.2 * iter (hS μ T N) (kT μ T N β) s Q.1.2 v.2))
      * (iter (hS μ T N) (kT μ T N β) u v.1 Q.2.1
        * (kT μ T N β Q.2.1 Q.2.2 * iter (hS μ T N) (kT μ T N β) u Q.2.2 v.2)))

/-- **M1, odd–odd.** At `N ≠ 0`, `0 ≤ β`, for every continuous `q`, the two-insertion closed chain
at odd separations `2s + 3` and `2u + 3` is nonnegative:
`0 ≤ ∫∫ q(x) q(y) kT^{∗(2s+3)}(x,y) kT^{∗(2u+3)}(y,x)`. The six-slice Fubini makes it
`∫ H(z,w') H(z',w) kT(z,z') kT(w',w)` with `H = sand s u q`; `H` is gauge invariant in each
argument because the kernel powers are (`sand_gact_left`, `sand_gact_right`), so the axis averages
of both kernels drop out (`integral_swap_gact2`) and the integral is `C₀²` times the link-plane
crossing form on pairs of slices (`integral_jFun`), `≥ 0` by `KernelInjective.crossForm_nonneg`. -/
theorem odd_pair_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (s u : ℕ)
    (q : C(SpT μ T → SUN.SU N, ℝ)) :
    0 ≤ ∫ x, ∫ y, q x * q y * (iter (hS μ T N) (kT μ T N β) (s + (s + 1) + 1) x y
        * iter (hS μ T N) (kT μ T N β) (u + (u + 1) + 1) y x) ∂(hS μ T N) ∂(hS μ T N) := by
  have ci : ∀ j, Continuous fun p : S₂ => iter (hS μ T N) (kT μ T N β) j p.1 p.2 :=
    continuous_iter β
  have ck : Continuous fun p : S₂ => kT μ T N β p.1 p.2 := continuous_kT β
  have hΦc : Continuous (Function.uncurry (phi6 μ T N β s u q)) := by
    have c1 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) =>
        iter (hS μ T N) (kT μ T N β) s p.1.1 p.2.1.1 :=
      Continuous.comp' (f := fun p : S₂ × (S₂ × S₂) => (p.1.1, p.2.1.1)) (ci s) (by fun_prop)
    have c2 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) =>
        kT μ T N β p.2.1.1 p.2.1.2 :=
      Continuous.comp' (f := fun p : S₂ × (S₂ × S₂) => (p.2.1.1, p.2.1.2)) ck (by fun_prop)
    have c3 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) =>
        iter (hS μ T N) (kT μ T N β) s p.2.1.2 p.1.2 :=
      Continuous.comp' (f := fun p : S₂ × (S₂ × S₂) => (p.2.1.2, p.1.2)) (ci s) (by fun_prop)
    have c4 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) =>
        iter (hS μ T N) (kT μ T N β) u p.1.1 p.2.2.1 :=
      Continuous.comp' (f := fun p : S₂ × (S₂ × S₂) => (p.1.1, p.2.2.1)) (ci u) (by fun_prop)
    have c5 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) =>
        kT μ T N β p.2.2.1 p.2.2.2 :=
      Continuous.comp' (f := fun p : S₂ × (S₂ × S₂) => (p.2.2.1, p.2.2.2)) ck (by fun_prop)
    have c6 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) =>
        iter (hS μ T N) (kT μ T N β) u p.2.2.2 p.1.2 :=
      Continuous.comp' (f := fun p : S₂ × (S₂ × S₂) => (p.2.2.2, p.1.2)) (ci u) (by fun_prop)
    have cq1 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) => q p.1.1 :=
      q.continuous.comp continuous_fst.fst
    have cq2 : Continuous fun p : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × (((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
          × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))) => q p.1.2 :=
      q.continuous.comp continuous_fst.snd
    exact (cq1.mul cq2).mul ((c1.mul (c2.mul c3)).mul (c4.mul (c5.mul c6)))
  -- step 1: the left side is `∫_v ∫_Q Φ`, `v = (x, y)`, `Q = ((z, z'), (w', w))`
  have h1 : ∀ x y, q x * q y * (iter (hS μ T N) (kT μ T N β) (s + (s + 1) + 1) x y
        * iter (hS μ T N) (kT μ T N β) (u + (u + 1) + 1) y x)
      = ∫ Q, phi6 μ T N β s u q (x, y) Q
          ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) := by
    intro x y
    rw [iter_symm' hN hβ (u + (u + 1) + 1) y x, iter_odd_eq hN hβ s x y,
      iter_odd_eq hN hβ u x y, ← integral_prod_mul, ← integral_const_mul]
    rfl
  have hcv : Continuous fun v : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N) =>
      ∫ Q, phi6 μ T N β s u q v Q
        ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) :=
    continuous_integral_snd _ hΦc
  have hL : ∫ x, ∫ y, q x * q y * (iter (hS μ T N) (kT μ T N β) (s + (s + 1) + 1) x y
        * iter (hS μ T N) (kT μ T N β) (u + (u + 1) + 1) y x) ∂(hS μ T N) ∂(hS μ T N)
      = ∫ v, ∫ Q, phi6 μ T N β s u q v Q
          ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
          ∂((hS μ T N).prod (hS μ T N)) := by
    rw [integral_prod _ (KernelInjective.integrable_of_continuous hcv)]
    congr 1; funext x; congr 1; funext y
    exact h1 x y
  -- step 2: integrate `v` first
  have h2 : ∀ Q : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
      × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)),
      ∫ v, phi6 μ T N β s u q v Q ∂((hS μ T N).prod (hS μ T N))
        = jFun μ T N β s u q ((Q.1.1, Q.2.1), (Q.1.2, Q.2.2)) := by
    intro Q
    have hpt : ∀ v : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N), phi6 μ T N β s u q v Q
        = ((iter (hS μ T N) (kT μ T N β) s Q.1.1 v.1
              * (q v.1 * iter (hS μ T N) (kT μ T N β) u v.1 Q.2.1))
          * (iter (hS μ T N) (kT μ T N β) s Q.1.2 v.2
              * (q v.2 * iter (hS μ T N) (kT μ T N β) u v.2 Q.2.2)))
          * (kT μ T N β Q.1.1 Q.1.2 * kT μ T N β Q.2.1 Q.2.2) := by
      intro v
      unfold phi6
      rw [iter_symm' hN hβ s v.1 Q.1.1, iter_symm' hN hβ u Q.2.2 v.2]
      ring
    have hp : ∫ v : (SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N),
          (iter (hS μ T N) (kT μ T N β) s Q.1.1 v.1
              * (q v.1 * iter (hS μ T N) (kT μ T N β) u v.1 Q.2.1))
          * (iter (hS μ T N) (kT μ T N β) s Q.1.2 v.2
              * (q v.2 * iter (hS μ T N) (kT μ T N β) u v.2 Q.2.2)) ∂((hS μ T N).prod (hS μ T N))
        = sand μ T N β s u q Q.1.1 Q.2.1 * sand μ T N β s u q Q.1.2 Q.2.2 :=
      integral_prod_mul (fun x => iter (hS μ T N) (kT μ T N β) s Q.1.1 x
          * (q x * iter (hS μ T N) (kT μ T N β) u x Q.2.1))
        (fun y => iter (hS μ T N) (kT μ T N β) s Q.1.2 y
          * (q y * iter (hS μ T N) (kT μ T N β) u y Q.2.2))
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_mul_const, hp]
    unfold jFun
    rfl
  have hswap : ∫ v, ∫ Q, phi6 μ T N β s u q v Q
        ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N)))
        ∂((hS μ T N).prod (hS μ T N))
      = ∫ Q, ∫ v, phi6 μ T N β s u q v Q ∂((hS μ T N).prod (hS μ T N))
          ∂(((hS μ T N).prod (hS μ T N)).prod ((hS μ T N).prod (hS μ T N))) :=
    integral_integral_swap (KernelInjective.integrable_of_continuous hΦc)
  have hJc : Continuous (jFun μ T N β s u q) := by
    have hsc : Continuous fun p : S₂ => sand μ T N β s u q p.1 p.2 :=
      continuous_sand (μ := μ) (T := T) (N := N) β s u q.continuous
    have d1 : Continuous fun W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => sand μ T N β s u q W.1.1 W.1.2 :=
      Continuous.comp' (f := fun W : S₂ × S₂ => (W.1.1, W.1.2)) hsc (by fun_prop)
    have d2 : Continuous fun W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => sand μ T N β s u q W.2.1 W.2.2 :=
      Continuous.comp' (f := fun W : S₂ × S₂ => (W.2.1, W.2.2)) hsc (by fun_prop)
    have d3 : Continuous fun W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => kT μ T N β W.1.1 W.2.1 :=
      Continuous.comp' (f := fun W : S₂ × S₂ => (W.1.1, W.2.1)) ck (by fun_prop)
    have d4 : Continuous fun W : ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N))
        × ((SpT μ T → SUN.SU N) × (SpT μ T → SUN.SU N)) => kT μ T N β W.1.2 W.2.2 :=
      Continuous.comp' (f := fun W : S₂ × S₂ => (W.1.2, W.2.2)) ck (by fun_prop)
    exact (d1.mul d2).mul (d3.mul d4)
  rw [hL, hswap, integral_congr_ae (Filter.Eventually.of_forall h2),
    integral_shuffle (F := jFun μ T N β s u q) hJc]
  exact integral_jFun_nonneg hN hβ s u q.continuous

end Kernel

/-! ## 2. The torus: every slice pair is nonnegative, and a sum of slices is strictly positive -/

section Torus

open MassGap.RectWilson MassGap.HiddenChain MassGap.TorusChain MassGap.SliceRPStrict

variable {N : ℕ}

/-- **The off-diagonal slice pair on the torus as a closed chain.** For `r' + r ≤ M`,
`⟨θ Q_r · Q_{r'}⟩ = Zc(q(V 0) q(V (r' + r))) / Zc 1`. -/
theorem torusState_refl_Qr_pair (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {M r r' : ℕ}
    (hrr : r' + r ≤ M) (q : C(Sl M N, ℝ)) :
    PeriodicState.torusState hN M β (LatticeReflection.ireflObs 0 0 (Qr q r) * Qr q r')
      = Zc M N β (fun V _ => q (V 0) * q (V (r' + r))) / Zc M N β (fun _ _ => 1) := by
  rw [← torusState_shift_iter hN M β r]
  have hprod : (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
        (LatticeReflection.ireflObs 0 0 (Qr q r) * Qr q r')
      = (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
          (LatticeReflection.ireflObs 0 0 (Qr q r))
        * (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r] (Qr q r') := by
    ext U; simp only [ContinuousMap.mul_apply, shiftObs_iter]
  have hQ := winLocal_Qr q r
  have hQ' := winLocal_Qr q r'
  have hloc := ((winLocal_refl hQ).mono (Nat.le_add_left r r')).mul (winLocal_shift hQ' r)
  rw [hprod, torusState_winF hN hβ hloc hrr]
  have hw : winF (M := M) ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
          (LatticeReflection.ireflObs 0 0 (Qr q r))
        * (⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r] (Qr q r'))
      = fun V _ => q (V 0) * q (V (r' + r)) := by
    funext V A
    show winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r]
          (LatticeReflection.ireflObs 0 0 (Qr q r))) V A
        * winF ((⇑(ReflectionShift.ishiftObsL (G := SUN.SU N) 0))^[r] (Qr q r')) V A = _
    rw [winF_refl hQ, winF_shift hQ', winF_Qr, winF_Qr]
    simp [revX, sshift]
  rw [hw]

/-- The torus normalisation is positive, at `N ≠ 0`, `0 < β`, `1 ≤ M′`. -/
theorem Zc_one_pos (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) {M' : ℕ} (hM' : 1 ≤ M') :
    0 < Zc (2 * M' + 1) N β (fun _ _ => 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, M' = c + 1 := ⟨M' - 1, by omega⟩
  have hM : 2 * (c + 1) + 1 = 0 + 0 + 1 + 1 + (c + c + 1) := by omega
  have h1 : (1 : C(Sl (2 * (c + 1) + 1) N, ℝ)) ≠ 0 := fun h => by
    have := congrArg (fun f : C(Sl (2 * (c + 1) + 1) N, ℝ) => f (fun _ => 1)) h
    simp at this
  rw [Zc_one β (0 + 0 + 1), Zc_pair hN hβ.le 1 _ _ hM]
  exact SliceKernelPower.sand_square_pos hN hβ 0 c 1 (fun _ _ => rfl) h1

/-- **M1 on the torus: every slice pair is nonnegative.** At `N ≠ 0`, `0 < β`, for `1 ≤ r, r'`
with `r + r' ≤ 2M′` and `q` continuous,
`0 ≤ ⟨θ Q_r · Q_{r'}⟩` on the torus of extent `2M′ + 2`. Even `r + r'`: the square formula
(`SliceKernelPower.sand_square`). Odd `r + r'`: a crossing form on pairs of slices
(`odd_pair_nonneg`). -/
theorem torusState_refl_Qr_pair_nonneg (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) {M' r r' : ℕ}
    (hr : 1 ≤ r) (hr' : 1 ≤ r') (hrr : r' + r ≤ 2 * M') (q : C(Sl (2 * M' + 1) N, ℝ)) :
    0 ≤ PeriodicState.torusState hN (2 * M' + 1) β
      (LatticeReflection.ireflObs 0 0 (Qr q r) * Qr q r') := by
  rw [torusState_refl_Qr_pair hN hβ.le (by omega) q]
  refine div_nonneg ?_ (Zc_one_pos hN hβ (by omega)).le
  rcases Nat.even_or_odd (r' + r) with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    set m := M' - a' - 1 with hm
    rw [show r' + r = a' + a' + 1 + 1 by omega,
      Zc_pair hN hβ.le q (a' + a' + 1) (m + m + 1) (by omega),
      SliceKernelPower.sand_square hN hβ.le a' m q]
    exact integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    set c := M' - a' - 2 with hc
    rw [show r' + r = a' + (a' + 1) + 1 + 1 by omega,
      Zc_pair hN hβ.le q (a' + (a' + 1) + 1) (c + (c + 1) + 1) (by omega)]
    exact odd_pair_nonneg hN hβ.le a' c q

/-- **Strict reflection positivity of a sum of slices on the torus.** At `N ≠ 0`, `0 < β`, for a
nonempty finite set `R` of times in `[1, M′]` and `q` continuous, gauge invariant and nonzero,
`0 < ⟨θY · Y⟩` on the torus of extent `2M′ + 2`, `Y = ∑_{r∈R} Q_r`. Every pair term is `≥ 0`
(`torusState_refl_Qr_pair_nonneg`) and each diagonal term is `> 0`
(`SliceRPStrict.torusState_refl_Qr_pos`). -/
theorem torusState_refl_sum_pos (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β) {M' : ℕ} (R : Finset ℕ)
    (hR : ∀ r ∈ R, 1 ≤ r ∧ r ≤ M') (hRne : R.Nonempty) (q : C(Sl (2 * M' + 1) N, ℝ))
    (hq : SliceKernelDefinite.GaugeInv ⇑q) (hq0 : q ≠ 0) :
    0 < PeriodicState.torusState hN (2 * M' + 1) β
      (LatticeReflection.ireflObs 0 0 (∑ r ∈ R, Qr q r) * ∑ r ∈ R, Qr q r) := by
  rw [map_sum, Finset.sum_mul_sum, DLRLimit.State.map_sum]
  obtain ⟨r₀, hr₀⟩ := hRne
  refine Finset.sum_pos' (fun r hr => ?_) ⟨r₀, hr₀, ?_⟩
  · rw [DLRLimit.State.map_sum]
    exact Finset.sum_nonneg fun r' hr' =>
      torusState_refl_Qr_pair_nonneg hN hβ (hR r hr).1 (hR r' hr').1
        (by have := (hR r hr).2; have := (hR r' hr').2; omega) q
  · rw [DLRLimit.State.map_sum]
    refine Finset.sum_pos' (fun r' hr' => ?_) ⟨r₀, hr₀, ?_⟩
    · exact torusState_refl_Qr_pair_nonneg hN hβ (hR r₀ hr₀).1 (hR r' hr').1
        (by have := (hR r₀ hr₀).2; have := (hR r' hr').2; omega) q
    · exact torusState_refl_Qr_pos hN hβ (hR r₀ hr₀).1 (hR r₀ hr₀).2 q hq hq0

end Torus

/-! ## 3. The torus reference reading from its slice form -/

section Reading

open MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.TorusCapstone
  MassGap.SliceRPStrict MassGap.TorusChain Filter

variable {N : ℕ}

/-- **The slice form of the torus reference vector.** Eventually in `k`, the cube-smeared connected
field `Y_k = Yv (connectedS (stateT hN M₀) 1) k (refMono O t ℓ)` read on the torus `stateT hN M₀ k`
(extent `2M′ + 2`, `M′ = M₀ 2ᵏ`) is `∑_{r∈R} Q_r` with `Q_r = Qr q r`, for a nonempty set `R` of
times in `[1, M′]` and one continuous, gauge-invariant, nonzero function `q` of the spatial links of
a slice. -/
def SliceForm (hN : N ≠ 0) (M₀ : ℕ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∃ (R : Finset ℕ) (q : C(Sl (2 * (M₀ * 2 ^ k) + 1) N, ℝ)),
    (∀ r ∈ R, 1 ≤ r ∧ r ≤ M₀ * 2 ^ k) ∧ R.Nonempty ∧ SliceKernelDefinite.GaugeInv ⇑q ∧ q ≠ 0 ∧
      ContinuumCluster.Yv (connectedS (stateT hN M₀) (fun _ _ => 1)) k
        (ExistenceReduce.refMono O t ℓ) = ∑ r ∈ R, Qr q r

/-- **`TorusRefPos` from the slice form.** The torus reading is `⟨θY_k · Y_k⟩`
(`TorusRefPosProof.refReadingS_stateT_eq`), and a sum of slices has strictly positive reflected
value (`torusState_refl_sum_pos`, at the coupling `dyBeta k ≥ 1`). -/
theorem torusRefPos_of_sliceForm (hN : N ≠ 0) {M₀ : ℕ} {O : LField (MassGap.SUN.SU N)} {t ℓ : ℝ}
    (h : SliceForm hN M₀ O t ℓ) : TorusRefPos hN M₀ O t ℓ := by
  filter_upwards [h] with k hk
  obtain ⟨R, q, hR, hRne, hq, hq0, hY⟩ := hk
  rw [TorusRefPosProof.refReadingS_stateT_eq, hY]
  exact torusState_refl_sum_pos hN
    (lt_of_lt_of_le zero_lt_one (one_le_dyBeta (one_le_of_ne_zero hN) k)) R hR hRne q hq hq0

/-- **The pinned path with `hpos` reduced to the slice form and `RefPassage`.**
`TorusPassageProof.clay_canonical_refPassage` with `TorusRefPos` supplied by
`torusRefPos_of_sliceForm`. -/
theorem clay_canonical_sliceForm (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N))
    {t ℓ : ℝ} (ht : 0 < t) {M₀ : ℕ} (hSF : SliceForm hN M₀ O t ℓ) {ε : ℝ} (hε : ε < 1)
    (hR : TorusPassageProof.RefPassage hN M₀ O t ℓ ε)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  TorusPassageProof.clay_canonical_refPassage hN2 hN O ht (torusRefPos_of_sliceForm hN hSF) hε hR
    hD hℓ₀ hW

end Reading

end MassGap.TorusRefPosPlane

#print axioms MassGap.TorusRefPosPlane.iter_gact_left
#print axioms MassGap.TorusRefPosPlane.iter_gact_right
#print axioms MassGap.TorusRefPosPlane.plaqSl_gact
#print axioms MassGap.TorusRefPosPlane.gaugeInv_plaqSum
#print axioms MassGap.TorusRefPosPlane.kT_eq_axis
#print axioms MassGap.TorusRefPosPlane.integral_shuffle
#print axioms MassGap.TorusRefPosPlane.integral_swap_gact2
#print axioms MassGap.TorusRefPosPlane.jFun_eq
#print axioms MassGap.TorusRefPosPlane.integral_jFun
#print axioms MassGap.TorusRefPosPlane.odd_pair_nonneg
#print axioms MassGap.TorusRefPosPlane.torusState_refl_Qr_pair
#print axioms MassGap.TorusRefPosPlane.Zc_one_pos
#print axioms MassGap.TorusRefPosPlane.torusState_refl_Qr_pair_nonneg
#print axioms MassGap.TorusRefPosPlane.torusState_refl_sum_pos
#print axioms MassGap.TorusRefPosPlane.torusRefPos_of_sliceForm
#print axioms MassGap.TorusRefPosPlane.clay_canonical_sliceForm
