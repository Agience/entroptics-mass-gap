import Mathlib
import MassGap.RectTransfer

/-!
# MassGap.ElectricStep — the time-like kernel `gk` is a Gauss-projected product of per-link class weights, and integrating a slice with no spatial plaquettes composes it by the per-link Haar convolution

Direction `μ`, transverse extents `T`, as in `RectTransfer`. A slice carries spatial links `V : SpT μ T → G`; the
links joining two slices along `μ` are the axis links `A : TT μ T → G`.

## The objects

* `tplaq A V V' l`, for a spatial link `l = (ν, y)`: the boundary word `A_y V'_l A_{y+ν}⁻¹ V_l⁻¹` of the time-like
  plaquette between the two slices above `l`. At `A = 1` it is `V'_l V_l⁻¹` (`tplaq_one`).
* `gkW w V V' = ∫ ∏_l w_l(tplaq A V V' l) dA`, product Haar on the axis links: the product over spatial links of a
  weight per link, projected onto gauge-invariant functions by the axis integral (the Gauss law). The weights may
  differ from link to link, so the moved lattice of `HolderBondMoving` (weights `w⁴` on surviving time-like
  plaquettes, `1` on removed ones) is covered.
* `conv u v g = ∫ u(h) v(h⁻¹ g) dh`, the group convolution against Haar probability.

## What is proved

* `gk_eq_gkW` (**the factorisation**). `RectTransfer.gk μ T N β V V' = gkW (fun _ => elecWeight N β) V V'` with
  `elecWeight N β g = e^{−2β·wilsonDensity g}`, a class function (`elecWeight_conj`). The `2` is the tree's count of
  each time-like plaquette in both orders (`RectWilson.action_Φ`).
* `integral_link`: for `v` a class function, `∫ u(a g b⁻¹ x⁻¹) v(c y d⁻¹ g⁻¹) dg = conv u v ((ac) y (bd)⁻¹ x⁻¹)`,
  by left and right invariance of Haar.
* `gkW_comp` (**the composition**). For continuous weights, `v` class on every link:
  `∫ gkW u V V'' · gkW v V'' V' dV'' = gkW (fun l => conv (u l) (v l)) V V'`. The intermediate slice's links
  integrate one by one (`integral_link`); the two axis configurations `A, B` enter only through `A·B`, the composite
  axis link, and the Gauss projection absorbs the second (`integral_mul_left_eq_self` on the product group).
* `gk_comp`: at `SU(N)` and the Wilson weight, `∫ gk(V, V'') gk(V'', V') dV'' = gkW (conv w w) V V'`,
  `w = elecWeight N β`.

Every statement is for an arbitrary compact second-countable group (`U(1)` included) except the two that name
`wilsonDensity`. The composition is exact; it carries no non-abelian content.

## Where the rest is proved

These modules import this one.

* `SU2DiskLaw.convT_eq_pi_conv`: for `SU(2)` and `U` continuous and `≥ 0` on `[−1, 1]`,
  `convT U (τ g) = π · conv (U ∘ τ) (U ∘ τ) g` wherever `τ g = ½ Re tr g ∈ (−1, 1)`. This is the Weyl integration formula: Haar measure on `SU(2)` is normalised ball
  volume of `ℝ⁴` pushed to the sphere.
* `MovedTorusDecimation.decimation`: the moved side-`2n` torus decimates to the side-`n` torus with weight
  `(w ⋆ w) ⋆ (w ⋆ w)`. It integrates the `2 × 2` blocks directly, one `integral_link` per interior link, and needs no
  slice-kernel assembly.
* `ElectricExactProof.electricExact` combines the two into `ElectricStepChain.ElectricExact` for every chain.

Foundational footprint only (`#print axioms` at the end).
-/

noncomputable section

namespace MassGap.ElectricStep

open MeasureTheory MassGap.CompactGauge MassGap.RectWilson

/-! ## 1. The per-link convolution -/

section Link

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Nonempty G] [MeasurableSpace G] [BorelSpace G]

/-- **The group convolution against Haar probability**, `(u ⋆ v)(g) = ∫ u(h) v(h⁻¹ g) dh`. -/
def conv (u v : G → ℝ) (g : G) : ℝ := ∫ h, u h * v (h⁻¹ * g) ∂(probHaar G)

/-- **One link of the intermediate slice.** For a class function `v`, integrating the shared link `g` of two
time-like plaquettes `a g b⁻¹ x⁻¹` and `c y d⁻¹ g⁻¹` gives the convolution at `(ac) y (bd)⁻¹ x⁻¹`. -/
theorem integral_link (u v : G → ℝ) (hv : ∀ k x, v (k * x * k⁻¹) = v x) (a b c d x y : G) :
    ∫ g, u (a * g * b⁻¹ * x⁻¹) * v (c * y * d⁻¹ * g⁻¹) ∂(probHaar G)
      = conv u v (a * c * y * (b * d)⁻¹ * x⁻¹) := by
  set F : G → ℝ := fun g => u (a * g * b⁻¹ * x⁻¹) * v (c * y * d⁻¹ * g⁻¹) with hF
  have h1 : ∫ g, F g ∂(probHaar G) = ∫ g, F (a⁻¹ * g) ∂(probHaar G) :=
    (integral_mul_left_eq_self F a⁻¹).symm
  have h2 : ∫ g, F (a⁻¹ * g) ∂(probHaar G) = ∫ g, F (a⁻¹ * (g * (x * b))) ∂(probHaar G) :=
    (integral_mul_right_eq_self (fun g => F (a⁻¹ * g)) (x * b)).symm
  rw [h1, h2]
  unfold conv
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  show u (a * (a⁻¹ * (h * (x * b))) * b⁻¹ * x⁻¹) * v (c * y * d⁻¹ * (a⁻¹ * (h * (x * b)))⁻¹)
    = u h * v (h⁻¹ * (a * c * y * (b * d)⁻¹ * x⁻¹))
  rw [← hv (a⁻¹ * h) (h⁻¹ * (a * c * y * (b * d)⁻¹ * x⁻¹))]
  congr 2
  · group
  · group

end Link

/-! ## 2. The time-like kernel with a weight per spatial link -/

section Kernel

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ}

/-- **The time-like plaquette above the spatial link `l = (ν, y)`**: `A_y V'_l A_{y+ν}⁻¹ V_l⁻¹`. -/
def tplaq {G : Type} [Group G] (A : TT μ T → G) (V V' : SpT μ T → G) (l : SpT μ T) : G :=
  A l.2 * V' l * (A (tsh μ T l.1 l.2))⁻¹ * (V l)⁻¹

/-- At trivial axis links the time-like plaquette is `V'_l V_l⁻¹`. -/
theorem tplaq_one {G : Type} [Group G] (V V' : SpT μ T → G) (l : SpT μ T) :
    tplaq (1 : TT μ T → G) V V' l = V' l * (V l)⁻¹ := by
  simp [tplaq]

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Nonempty G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

variable (μ T G) in
/-- Haar probability on the axis links of one slice. -/
abbrev axH : Measure (TT μ T → G) := Measure.pi fun _ : TT μ T => probHaar G

variable (μ T G) in
/-- Haar probability on the spatial links of one slice. -/
abbrev spH : Measure (SpT μ T → G) := Measure.pi fun _ : SpT μ T => probHaar G

/-- **The Gauss-projected product of per-link weights**: `gkW w V V' = ∫ ∏_l w_l(A_y V'_l A_{y+ν}⁻¹ V_l⁻¹) dA`. -/
def gkW (w : SpT μ T → G → ℝ) (V V' : SpT μ T → G) : ℝ :=
  ∫ A, ∏ l, w l (tplaq A V V' l) ∂(axH μ T G)

omit [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem continuous_tplaq_uncurry (V' : SpT μ T → G) :
    Continuous fun p : (TT μ T → G) × (SpT μ T → G) => fun l => tplaq p.1 p.2 V' l := by
  refine continuous_pi fun l => ?_
  unfold tplaq
  fun_prop

omit [CompactSpace G] [Nonempty G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem continuous_tplaq_uncurry' (V : SpT μ T → G) :
    Continuous fun p : (TT μ T → G) × (SpT μ T → G) => fun l => tplaq p.1 V p.2 l := by
  refine continuous_pi fun l => ?_
  unfold tplaq
  fun_prop

/-- **The composition.** Integrating the spatial links `V''` of a slice that couples to its neighbours only
through time-like plaquettes composes the two kernels into one, with the per-link convolution as the new weight
and the product of the two axis links as the new axis link. Exact for every compact group. -/
theorem gkW_comp (u v : SpT μ T → G → ℝ) (hu : ∀ l, Continuous (u l)) (hv : ∀ l, Continuous (v l))
    (hvc : ∀ l k x, v l (k * x * k⁻¹) = v l x) (V V' : SpT μ T → G) :
    ∫ V'', gkW u V V'' * gkW v V'' V' ∂(spH μ T G) = gkW (fun l => conv (u l) (v l)) V V' := by
  set P : (TT μ T → G) → (SpT μ T → G) → ℝ := fun A V'' => ∏ l, u l (tplaq A V V'' l) with hPdef
  set Q : (TT μ T → G) → (SpT μ T → G) → ℝ := fun B V'' => ∏ l, v l (tplaq B V'' V' l) with hQdef
  have hP : Continuous (Function.uncurry P) := by
    refine continuous_finsetProd _ fun l _ => (hu l).comp ?_
    exact (continuous_apply l).comp (continuous_tplaq_uncurry' V)
  have hQ : Continuous (Function.uncurry Q) := by
    refine continuous_finsetProd _ fun l _ => (hv l).comp ?_
    exact (continuous_apply l).comp (continuous_tplaq_uncurry V')
  -- the product of the two kernels as a double integral over the two axis configurations
  have e1 : ∀ V'', gkW u V V'' * gkW v V'' V'
      = ∫ A, ∫ B, P A V'' * Q B V'' ∂(axH μ T G) ∂(axH μ T G) := by
    intro V''
    show (∫ A, P A V'' ∂(axH μ T G)) * (∫ B, Q B V'' ∂(axH μ T G)) = _
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
    show P A V'' * ∫ B, Q B V'' ∂(axH μ T G) = ∫ B, P A V'' * Q B V'' ∂(axH μ T G)
    rw [integral_const_mul]
  -- continuity of the inner integral, for the first swap
  have hR : Continuous fun p : (SpT μ T → G) × (TT μ T → G) =>
      ∫ B, P p.2 p.1 * Q B p.1 ∂(axH μ T G) := by
    have hf : Continuous (Function.uncurry fun (p : (SpT μ T → G) × (TT μ T → G)) (B : TT μ T → G) =>
        P p.2 p.1 * Q B p.1) :=
      (hP.comp (continuous_fst.snd.prodMk continuous_fst.fst)).mul
        (hQ.comp (continuous_snd.prodMk continuous_fst.fst))
    have h := continuous_parametric_integral_of_continuous (μ := axH μ T G) hf isCompact_univ
    simp only [Measure.restrict_univ] at h
    exact h
  have e2 : ∫ V'', ∫ A, ∫ B, P A V'' * Q B V'' ∂(axH μ T G) ∂(axH μ T G) ∂(spH μ T G)
      = ∫ A, ∫ V'', ∫ B, P A V'' * Q B V'' ∂(axH μ T G) ∂(spH μ T G) ∂(axH μ T G) :=
    integral_integral_swap (hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have e3 : ∀ A, ∫ V'', ∫ B, P A V'' * Q B V'' ∂(axH μ T G) ∂(spH μ T G)
      = ∫ B, ∫ V'', P A V'' * Q B V'' ∂(spH μ T G) ∂(axH μ T G) := by
    intro A
    have hc : Continuous (Function.uncurry fun (V'' : SpT μ T → G) (B : TT μ T → G) =>
        P A V'' * Q B V'') :=
      (hP.comp (continuous_const.prodMk continuous_fst)).mul
        (hQ.comp (continuous_snd.prodMk continuous_fst))
    exact integral_integral_swap (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  -- the intermediate slice, link by link
  have e4 : ∀ A B, ∫ V'', P A V'' * Q B V'' ∂(spH μ T G)
      = ∏ l, conv (u l) (v l) (tplaq (A * B) V V' l) := by
    intro A B
    have h := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := fun _ : SpT μ T => probHaar G)
      (fun l (g : G) => u l (A l.2 * g * (A (tsh μ T l.1 l.2))⁻¹ * (V l)⁻¹)
        * v l (B l.2 * V' l * (B (tsh μ T l.1 l.2))⁻¹ * g⁻¹))
    have hint : (fun V'' : SpT μ T → G => P A V'' * Q B V'')
        = fun V'' => ∏ l, (u l (A l.2 * V'' l * (A (tsh μ T l.1 l.2))⁻¹ * (V l)⁻¹)
          * v l (B l.2 * V' l * (B (tsh μ T l.1 l.2))⁻¹ * (V'' l)⁻¹)) := by
      funext V''
      simp only [hPdef, hQdef, tplaq]
      rw [Finset.prod_mul_distrib]
    rw [hint]
    refine h.trans (Finset.prod_congr rfl fun l _ => ?_)
    exact integral_link (u l) (v l) (hvc l) _ _ _ _ _ _
  -- the Gauss projection absorbs the second axis configuration
  set F : (TT μ T → G) → ℝ := fun C => ∏ l, conv (u l) (v l) (tplaq C V V' l) with hFdef
  have e5 : ∫ A, ∫ B, F (A * B) ∂(axH μ T G) ∂(axH μ T G) = ∫ C, F C ∂(axH μ T G) := by
    have hin : ∀ A : TT μ T → G, ∫ B, F (A * B) ∂(axH μ T G) = ∫ C, F C ∂(axH μ T G) :=
      fun A => integral_mul_left_eq_self F A
    simp_rw [hin]
    rw [integral_const, probReal_univ, one_smul]
  calc ∫ V'', gkW u V V'' * gkW v V'' V' ∂(spH μ T G)
      = ∫ V'', ∫ A, ∫ B, P A V'' * Q B V'' ∂(axH μ T G) ∂(axH μ T G) ∂(spH μ T G) :=
        integral_congr_ae (Filter.Eventually.of_forall fun V'' => e1 V'')
    _ = ∫ A, ∫ V'', ∫ B, P A V'' * Q B V'' ∂(axH μ T G) ∂(spH μ T G) ∂(axH μ T G) := e2
    _ = ∫ A, ∫ B, ∫ V'', P A V'' * Q B V'' ∂(spH μ T G) ∂(axH μ T G) ∂(axH μ T G) :=
        integral_congr_ae (Filter.Eventually.of_forall fun A => e3 A)
    _ = ∫ A, ∫ B, F (A * B) ∂(axH μ T G) ∂(axH μ T G) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
        exact integral_congr_ae (Filter.Eventually.of_forall fun B => e4 A B)
    _ = ∫ C, F C ∂(axH μ T G) := e5
    _ = gkW (fun l => conv (u l) (v l)) V V' := rfl

end Kernel

/-! ## 3. The Wilson weight: the factorisation of `RectTransfer.gk` -/

section Wilson

variable {μ : Fin 4} {T : {j : Fin 4 // j ≠ μ} → ℕ} {N : ℕ}

/-- **The electric weight per spatial link**, `e^{−2β·wilsonDensity}`. DERIVED: `2` the tree's count of each
time-like plaquette in both orders (`RectTransfer.gk`). -/
def elecWeight (N : ℕ) (β : ℝ) (g : SUN.SU N) : ℝ := Real.exp (-(2 * β) * WilsonAction.wilsonDensity g)

theorem elecWeight_conj (β : ℝ) (k x : SUN.SU N) : elecWeight N β (k * x * k⁻¹) = elecWeight N β x := by
  unfold elecWeight; rw [WilsonAction.wilsonDensity_conj]

theorem continuous_elecWeight (β : ℝ) : Continuous (elecWeight N β) :=
  Real.continuous_exp.comp (continuous_const.mul WilsonAction.continuous_wilsonDensity)

/-- **The factorisation.** `gk` is the Gauss-projected product over spatial links of the electric weight of the
time-like plaquette above each link. -/
theorem gk_eq_gkW (β : ℝ) (V V' : SpT μ T → SUN.SU N) :
    RectTransfer.gk μ T N β V V' = gkW (fun _ => elecWeight N β) V V' := by
  unfold RectTransfer.gk gkW
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  show Real.exp (-β * (2 * tpT μ T A V V')) = ∏ l, Real.exp (-(2 * β) * WilsonAction.wilsonDensity (tplaq A V V' l))
  rw [← Real.exp_sum]
  congr 1
  unfold tpT
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [tplaq]
  ring

/-- **`gk_comp`.** Integrating a slice with no spatial plaquettes composes two time-like kernels at weight
`w = elecWeight N β` into the kernel at weight `w ⋆ w` on every link. -/
theorem gk_comp (β : ℝ) (V V' : SpT μ T → SUN.SU N) :
    ∫ V'', RectTransfer.gk μ T N β V V'' * RectTransfer.gk μ T N β V'' V' ∂(RectTransfer.hS μ T N)
      = gkW (fun _ => conv (elecWeight N β) (elecWeight N β)) V V' := by
  simp_rw [gk_eq_gkW]
  exact gkW_comp (fun _ => elecWeight N β) (fun _ => elecWeight N β) (fun _ => continuous_elecWeight β)
    (fun _ => continuous_elecWeight β) (fun _ => elecWeight_conj β) V V'

end Wilson

end MassGap.ElectricStep

end

#print axioms MassGap.ElectricStep.integral_link
#print axioms MassGap.ElectricStep.tplaq_one
#print axioms MassGap.ElectricStep.gkW_comp
#print axioms MassGap.ElectricStep.gk_eq_gkW
#print axioms MassGap.ElectricStep.gk_comp
