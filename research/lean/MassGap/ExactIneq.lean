import Mathlib
import MassGap.MixExpand

/-!
# MassGap.ExactIneq — exact identities of the Wilson measure and the bar for a group-reading inequality

The search here was for an inequality exact at every `β ≥ 0` and side `n`, reading the commutator or Casimir structure of
`SU(N)`, consumed by `MixCut.MixCutBound`, `MixCutTest.VarGap`, `MixEqui.MixEquiUp` or the flux half. None was found. This
module holds the identities that survive, each with its outcome against the bar: (a) exact, (b) group-reading, (c)
consumed, (d) not refuted by `U(1)`. Declarations are in `MassGap.ExactIneq`.

## 1. Flows and Schwinger–Dyson (proved)

`IsFlow μ Φ`: a one-parameter flow preserving integrals. `IsGen Φ F D`: `D` is the continuous derivative of `F` along `Φ`
at time `0`; the group law then gives it at every time, and compactness dominates the integrand.
`integral_gen_eq_zero`: `∫ D = 0`. `schwingerDyson`: `∫ (DO − O DV) e^{−V} = 0`. `det_exp_eq_one`, `exp_mem`, `E`:
`exp(sX) ∈ SU(N)` for traceless anti-Hermitian `X`, by the spectral theorem.

## 2. One link (proved; bar: a yes, b no, c no)

`linkFlow l A`: left translation of the link `l` along `exp(sX)`. `isGen_link_plaq`: every plaquette density has a
generator `dplaq`, the four-factor Leibniz rule, with no restriction on `n` or on repeats of `l` in the plaquette.
`sd_link`: `∫ (DO − O (β DS_in + t DS_mix)) e^{−(β S_in + t S_mix)} = 0`. `sd_link_plaq`: `⟨D φ_p⟩` equals the
two-plaquette correlators through the link. The equal-coupling case `t = β` is the Wilson measure of `RectWilson`.

(b) fails: summed over a basis this is the master loop equation (Makeenko–Migdal, Chatterjee, cited), and the `U(N)` form
at `N = 1` is compact `U(1)`. (c) fails: it is linear and at one side.

## 3. The layer rotation (proved; bar: a yes, b no, c restates)

`pageFlow z A`: the rotation `MixCut.gT` at one site. It fixes `S_in` (`sinR_page`), so `sd_page` has no `β`:
`∫ (DO − t O J_{z,X}) e^{−(β S_in + t S_mix)} = 0`, `J_{z,X} = curS z X` the derivative of `S_mix`. Each mixed plaquette
is left-translated in a corner read (`chi`, `chi_gT`, `plaq_eq_chi`). `CasFam`: a family with `Σ_a X_a² = −c`.

* `sum_curS`: `Σ_{z,a} Y_{z,a}² S_mix = 4 c (8 n⁴ − S_mix)`, pointwise.
* `energy_current`: `4 c (8 n⁴ − ⟨S_mix⟩_n) = t G_n`, with `G_n = Σ_{z,a} ⟨J_{z,a}²⟩_n ≥ 0` (`curG`, `curG_nonneg`).
* `mixCut_eq_current`: `mixCut = (t / 4c)(16 G_n − G_{2n})`; the constant `8 n⁴` cancels in the doubling.
  `mixCut_eq_offDiag`: the same at every `N ≥ 2` with the family `offDiag`, `c = N − 1`.
* `var_current`: `4 c Var_n(S_mix) = G_n − t Cov_n(S_mix, |J|²)` (`covCur`).
* `meanMix_le`: `⟨S_mix⟩_n ≤ 8 n⁴` for `t ≥ 0`.

The doubling combination is thereby a difference of sums of squares. Each has a sign; the difference has none.
(b) fails: for `U(1)` the same computation runs with `X = i`, `c = 1`. (c): `16 G_n − G_{2n} ≤ 4 c M / t` is
`MixCutBound` in another letter, `G_L = L⁴ g_L` with `g` a local density. (d): at the `U(1)` transition `G` jumps with
the energy, so the identity excludes nothing. Tests: `t = 0` reads `0 = 0`, which is `MixCut.mixCut_zero` at the factor
`t`; `β = t = 0` the same.

## 4. The colour Ward identity (proved; bar: a yes, b yes, c no)

`gF`: the full gauge rotation. `J_{z,X}` is charged under a rotation at `z` (`cur_gF_flip`) and blind to one elsewhere
(`cur_gF_ne`). `cross_zero`: if `a₀ X a₀⁻¹ = −X` then `⟨J_{z,X} J_{w,Y}⟩ = 0` for `z ≠ w`, at every `β`, `t`, `n ≥ 2`.
`page_charge`: over any set of sites, `⟨(Σ_z J_z)²⟩ = Σ_z ⟨J_z²⟩`. `flipEl`, `flip_of_support`, `cross_zero_off`,
`page_charge_off`: these at every `N` for the off-diagonal generators. `flip_comm`: a commutative ring has no flip unless
`2 X = 0`.

(b) holds: for `U(1)` the current is neutral, `⟨J_z J_w⟩` is non-zero at adjacent corners (by hand, `∓⟨cos θ_q⟩/t`), and
the sum over a page vanishes identically, which follows from `PageCouple.frame_comm`. (c) fails: `J` is an equation-of-motion operator,
so for either group its correlators are contact terms, and the identity removes off-diagonal terms that do not enter
`G_n`. The group difference here is one contact term with no reach and no comparison of sides.

## 5. Route 2 on one generator (proved; bar: a yes, b no, c no)

`bochner_frame`: `⟨(Y² f − t (Y f)²)²⟩ = ⟨(Y² f)²⟩ + t ⟨Y² S · (Y f)²⟩` at `f = S_mix`. No curvature and no `β`.
`hess_local`: the last term is `⟨K²⟩ + ⟨J L⟩`, a local expectation by Schwinger–Dyson, so keeping the Hessian of the
action rather than bounding it returns Route 1.

By hand, for all generators: `∫ (Lf)² dμ = ∫ Σ_{a,b} (X_b X_a f)² dμ + ∫ Σ_{a,b} X_a f X_b f X_a X_b V dμ`, the commutator
terms cancelling through the total antisymmetry of `c_abc`. `Ric = N/4` appears only on splitting the frame Hessian,
`Σ (X_a X_b f)² = |Hess f|² + (N/4) |∇f|²`. So the curvature term is the antisymmetric frame Hessian on the other
side; the frame form reads alike for every compact group, and (b) fails. In the doubling combination the curvature term is
`(N c / t) mixCut`, cancelled by that antisymmetric part.

## 6. Why no route passes

Two reasons, argued, not theorems of the tree. First: a one-sided bound at one side loses a density, `~ L⁴`, unless
saturated, and `16 n⁴ (a_n − a_{2n}) = O(1)` for the lost density `a` is a finite-size statement of the same kind.
Second: Schwinger–Dyson is linear in the state and reflection positivity convex, with the same coefficients at sides `n`,
`2n`, `∞`; so the admissible set is convex and holds all Gibbs states, and for `U(1)` at its transition it has two points.
A bound on the doubling combination from these inputs alone is a uniqueness theorem for that system at every coupling,
and the only known mechanism, the Casimir diagonal dominating the `β` term, holds below a coupling depending on `N`, the
regime of `CondGap`, and for `U(1)` in the same form.

Other candidates, by hand: reflection positivity gives
`Var_{2n}(S_mix) ≥ 16 Var_{2n}(S_b)` for half-weighted blocks (a yes, b no, feeds `VarGap` by one reduction; not built);
Bakry–Émery on the layer-gauge orbit is free of `β` and holds for `t < N/(4H)` (a no, c no); Hölder between couplings
leaves an extensive Bregman term (b no, c no). For the flux half, twisted local expectations satisfy the same relations,
Jensen gives an area cost, and the centre twist has no derivative in the twist; `TomboulisYaffe` runs from the twisted
ratio to the Wilson loop, the wrong way for a consumer.

DERIVED (module-wide): `4` the corners of a plaquette and the dimension; `8` the mixed ordered orientations per site;
`16 = 2⁴` the copies; `2` the two orientations, the doubling, the least side, the square; `1/2` the normalization of an
off-diagonal pair; `3`, `4` the powers in the Leibniz rule of `bochner_frame`; `0`, `1` the base time and the unit.
Inherited: none beyond `MixExpand`, `MixEqui`, `MixCut`, `MixCutTest`. `c` is a field of `CasFam`, read from the family:
`N − 1` for `offDiag`, which counts each pair twice and omits the Cartan directions. Cited: Makeenko–Migdal, Chatterjee,
Shen–Zhu–Zhu, in prose only.

## What does not follow

Nothing here bounds `mixCut`, `MixCutTest.VarGap`, `MixEqui.MixEquiUp` or a twisted ratio from above at any `t > 0`.
`mixCut_eq_current` and `var_current` restate those objects; they discharge nothing. `cross_zero` reads the group and has no
consumer. `bochner_frame` is on one generator; the sum over generators and the statement on `Ric` are by hand. The reasons
in section 6 are about method: they do not show the Schwinger–Dyson set of `SU(N)` has two points.
-/

namespace MassGap.ExactIneq

open MeasureTheory Filter Topology Set MassGap MassGap.CompactGauge MassGap.RectWilson MassGap.MixCut
open MassGap.MixEqui MassGap.MixExpand
open scoped Matrix

/-! ## 1. Measure-preserving flows and their generators -/

section Flow

variable {Ω : Type*} [TopologicalSpace Ω]

/-- A continuous one-parameter flow preserving the integral of every continuous function. No numeral. -/
structure IsFlow [MeasurableSpace Ω] (μ : Measure Ω) (Φ : ℝ → Ω → Ω) : Prop where
  zero : ∀ U, Φ 0 U = U
  add : ∀ s r U, Φ (s + r) U = Φ s (Φ r U)
  cont : ∀ s, Continuous (Φ s)
  pres : ∀ s (F : Ω → ℝ), Continuous F → ∫ U, F (Φ s U) ∂μ = ∫ U, F U ∂μ

/-- `D` is the continuous derivative of `F` along `Φ` at time `0`. DERIVED: `0` the base time. -/
def IsGen (Φ : ℝ → Ω → Ω) (F D : Ω → ℝ) : Prop :=
  Continuous D ∧ ∀ U, HasDerivAt (fun s => F (Φ s U)) (D U) 0

variable {Φ : ℝ → Ω → Ω} {F G D E : Ω → ℝ}

theorem IsGen.of_inv (h : ∀ s U, F (Φ s U) = F U) : IsGen Φ F fun _ => 0 :=
  ⟨continuous_const, fun U => by
    have e : (fun s => F (Φ s U)) = fun _ => F U := funext fun s => h s U
    rw [e]; exact hasDerivAt_const _ _⟩

theorem IsGen.add (hF : IsGen Φ F D) (hG : IsGen Φ G E) :
    IsGen Φ (fun U => F U + G U) fun U => D U + E U :=
  ⟨hF.1.add hG.1, fun U => (hF.2 U).add (hG.2 U)⟩

theorem IsGen.const_mul (c : ℝ) (hF : IsGen Φ F D) : IsGen Φ (fun U => c * F U) fun U => c * D U :=
  ⟨continuous_const.mul hF.1, fun U => (hF.2 U).const_mul c⟩

theorem IsGen.sum {ι : Type*} (s : Finset ι) {f d : ι → Ω → ℝ} (h : ∀ i ∈ s, IsGen Φ (f i) (d i)) :
    IsGen Φ (fun U => ∑ i ∈ s, f i U) fun U => ∑ i ∈ s, d i U :=
  ⟨continuous_finsetSum _ fun i hi => (h i hi).1, fun U => by
    have := HasDerivAt.fun_sum (u := s) (A := fun i s' => f i (Φ s' U)) (A' := fun i => d i U) (x := 0)
      fun i hi => (h i hi).2 U
    exact this⟩

theorem IsGen.mul (hz : ∀ U, Φ 0 U = U) (hFc : Continuous F) (hGc : Continuous G) (hF : IsGen Φ F D)
    (hG : IsGen Φ G E) : IsGen Φ (fun U => F U * G U) fun U => D U * G U + F U * E U :=
  ⟨(hF.1.mul hGc).add (hFc.mul hG.1), fun U => by
    have h : HasDerivAt (fun s => F (Φ s U) * G (Φ s U)) (D U * G (Φ 0 U) + F (Φ 0 U) * E U) 0 :=
      (hF.2 U).mul (hG.2 U)
    simpa only [hz] using h⟩

/-- The derivative at time `0` is the derivative at every time, by the group law. No numeral. -/
theorem IsGen.hasDerivAt_at [MeasurableSpace Ω] {μ : Measure Ω} (hΦ : IsFlow μ Φ) (h : IsGen Φ F D)
    (s : ℝ) (U : Ω) : HasDerivAt (fun r => F (Φ r U)) (D (Φ s U)) s := by
  have h1 : HasDerivAt (fun x => F (Φ x (Φ s U))) (D (Φ s U)) (s + -s) := by
    rw [add_neg_cancel]; exact h.2 (Φ s U)
  have h2 := HasDerivAt.comp_add_const s (-s) h1
  have e : (fun r => F (Φ (r + -s) (Φ s U))) = fun r => F (Φ r U) := by
    funext r
    rw [← hΦ.add, neg_add_cancel_right]
  rw [e] at h2
  exact h2

variable [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- **The integral of a generator vanishes.** No numeral. -/
theorem integral_gen_eq_zero {μ : Measure Ω} [IsFiniteMeasure μ] (hΦ : IsFlow μ Φ) (hF : Continuous F)
    (h : IsGen Φ F D) : ∫ U, D U ∂μ = 0 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn h.1.continuousOn
  have hD : ∀ U, ‖D U‖ ≤ C := fun U => hC U (mem_univ U)
  have hFs : ∀ s, Continuous fun U => F (Φ s U) := fun s => hF.comp (hΦ.cont s)
  have hint : Integrable (fun U => F (Φ 0 U)) μ := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (hFs 0).continuousOn
    exact (integrable_const M).mono' (hFs 0).aestronglyMeasurable
      (Eventually.of_forall fun U => hM U (mem_univ U))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (s : ℝ) U => F (Φ s U)) (F' := fun s U => D (Φ s U)) (x₀ := 0)
    (bound := fun _ => C) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s => (hFs s).aestronglyMeasurable) hint
    (h.1.comp (hΦ.cont 0)).aestronglyMeasurable
    (Eventually.of_forall fun U s _ => hD _) (integrable_const _)
    (Eventually.of_forall fun U s _ => h.hasDerivAt_at hΦ s U)
  have k2 : HasDerivAt (fun s => ∫ U, F (Φ s U) ∂μ) (∫ U, D (Φ 0 U) ∂μ) 0 := key.2
  have hconst : (fun s => ∫ U, F (Φ s U) ∂μ) = fun _ => ∫ U, F U ∂μ :=
    funext fun s => hΦ.pres s F hF
  rw [hconst] at k2
  have := k2.unique (hasDerivAt_const 0 _)
  simpa only [hΦ.zero] using this

/-- **The Schwinger–Dyson identity of a flow**: `∫ (DO − O DV) e^{−V} = 0`. No numeral. -/
theorem schwingerDyson {μ : Measure Ω} [IsFiniteMeasure μ] (hΦ : IsFlow μ Φ) {O DO V DV : Ω → ℝ}
    (hO : Continuous O) (hV : Continuous V) (hgO : IsGen Φ O DO) (hgV : IsGen Φ V DV) :
    ∫ U, (DO U - O U * DV U) * Real.exp (-V U) ∂μ = 0 := by
  have hexp : Continuous fun U => Real.exp (-V U) := Real.continuous_exp.comp hV.neg
  refine integral_gen_eq_zero hΦ (F := fun U => O U * Real.exp (-V U)) (hO.mul hexp)
    ⟨(hgO.1.sub (hO.mul hgV.1)).mul hexp, fun U => ?_⟩
  have h2 : HasDerivAt (fun s => Real.exp (-V (Φ s U))) (Real.exp (-V U) * (-DV U)) 0 := by
    have h := (hgV.2 U).neg.exp
    simpa only [hΦ.zero, Pi.neg_apply] using h
  have h3 : HasDerivAt (fun s => O (Φ s U) * Real.exp (-V (Φ s U)))
      (DO U * Real.exp (-V (Φ 0 U)) + O (Φ 0 U) * (Real.exp (-V U) * (-DV U))) 0 :=
    (hgO.2 U).mul h2
  refine h3.congr_deriv ?_
  simp only [hΦ.zero]
  ring

end Flow

/-! ## 2. One-parameter subgroups of `SU(N)` -/

/-- Complex `N × N` matrices. No numeral. -/
abbrev Mat (N : ℕ) : Type := Matrix (Fin N) (Fin N) ℂ

variable {N : ℕ}

/-- `Re tr`. No numeral. -/
noncomputable def rt (A : Mat N) : ℝ := (Matrix.trace A).re

theorem continuous_rt : Continuous (rt (N := N)) :=
  Complex.continuous_re.comp (Continuous.matrix_trace continuous_id)

theorem rt_add (A B : Mat N) : rt (A + B) = rt A + rt B := by
  simp [rt, Matrix.trace_add]

theorem rt_sum {ι : Type*} (s : Finset ι) (f : ι → Mat N) : rt (∑ i ∈ s, f i) = ∑ i ∈ s, rt (f i) := by
  simp [rt, Matrix.trace_sum]

theorem rt_real_smul (c : ℝ) (A : Mat N) : rt ((c : ℂ) • A) = c * rt A := by
  simp [rt, Matrix.trace_smul]

theorem wilsonDensity_eq (g : SUN.SU N) :
    WilsonAction.wilsonDensity g = 1 - (1 / (N : ℝ)) * rt (g : Mat N) := rfl

/-- **`det exp X = 1` for traceless anti-Hermitian `X`**, by the spectral theorem for `−iX`. No numeral. -/
theorem det_exp_eq_one {X : Mat N} (hs : Xᴴ = -X) (ht : Matrix.trace X = 0) :
    Matrix.det (NormedSpace.exp X) = 1 := by
  set H : Mat N := (-Complex.I) • X with hH
  have hHerm : H.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH, Matrix.conjTranspose_smul, hs]
    simp
  have hsp := hHerm.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  set u : Mat N := (hHerm.eigenvectorUnitary : Mat N) with hu
  have hu1 : u * star u = 1 := Unitary.coe_mul_star_self hHerm.eigenvectorUnitary
  have hu2 : star u * u = 1 := Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
  have hinv : u⁻¹ = star u := Matrix.inv_eq_right_inv hu1
  have hunit : IsUnit u := ⟨⟨u, star u, hu1, hu2⟩, rfl⟩
  set v : Fin N → ℂ := fun k => Complex.I * ((hHerm.eigenvalues k : ℝ) : ℂ) with hv
  have hd : Complex.I • Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) = Matrix.diagonal v := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hv]
    · simp [Matrix.diagonal_apply_ne, hab]
  have hX : X = u * Matrix.diagonal v * u⁻¹ := by
    have h1 : X = Complex.I • H := by
      rw [hH, smul_smul]; simp
    rw [h1, hsp, hinv, ← hd]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have htr : ∑ k, v k = 0 := by
    have h1 : Matrix.trace (u * Matrix.diagonal v * star u) = ∑ k, v k := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, hu2, one_mul, Matrix.trace_diagonal]
    rw [← h1, ← hinv, ← hX, ht]
  rw [hX, Matrix.exp_conj _ _ hunit, hinv, Matrix.exp_diagonal, Matrix.det_mul, Matrix.det_mul,
    mul_right_comm, ← Matrix.det_mul, hu1, Matrix.det_one, one_mul, Matrix.det_diagonal]
  simp only [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_sum, htr, Complex.exp_zero]

theorem exp_mem {X : Mat N} (hs : Xᴴ = -X) (ht : Matrix.trace X = 0) :
    NormedSpace.exp X ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, det_exp_eq_one hs ht⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
    ← Matrix.exp_add_of_commute X (-X) (Commute.neg_right (Commute.refl X)), add_neg_cancel,
    NormedSpace.exp_zero]

/-- An element of `su(N)`: traceless and anti-Hermitian. No numeral. -/
structure Su (N : ℕ) where
  X : Mat N
  skew : Xᴴ = -X
  tr : Matrix.trace X = 0

/-- The one-parameter subgroup `s ↦ exp(s X)`. No numeral. -/
noncomputable def E (A : Su N) (s : ℝ) : SUN.SU N :=
  ⟨NormedSpace.exp (s • A.X), exp_mem (by
      rw [Matrix.conjTranspose_smul, A.skew, star_trivial, smul_neg]) (by
      rw [Matrix.trace_smul, A.tr, smul_zero])⟩

theorem coe_E (A : Su N) (s : ℝ) : ((E A s : SUN.SU N) : Mat N) = NormedSpace.exp (s • A.X) := rfl

theorem E_zero (A : Su N) : E A 0 = 1 := by
  apply Subtype.ext
  rw [coe_E, zero_smul, NormedSpace.exp_zero]
  rfl

theorem E_add (A : Su N) (s r : ℝ) : E A (s + r) = E A s * E A r := by
  apply Subtype.ext
  show NormedSpace.exp ((s + r) • A.X) = NormedSpace.exp (s • A.X) * NormedSpace.exp (r • A.X)
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl A.X).smul_left s).smul_right r)]

section Deriv

open scoped Matrix.Norms.Operator

theorem completeMat : CompleteSpace (Mat N) := FiniteDimensional.complete ℝ (Mat N)

attribute [local instance] completeMat

/-- `Re tr` as a continuous linear map. No numeral. -/
noncomputable def rtL : Mat N →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (Complex.reCLM.toLinearMap ∘ₗ Matrix.traceLinearMap (Fin N) ℝ ℂ)

/-- **The derivative of `s ↦ Re tr(Y exp(sX) ψ)` at `0`.** DERIVED: `0` the base time. -/
theorem hasDerivAt_rt_E (A : Su N) (Y ψ : Mat N) :
    HasDerivAt (fun s : ℝ => rt (Y * (E A s : Mat N) * ψ)) (rt (Y * A.X * ψ)) 0 := by
  have h0 := hasDerivAt_exp_smul_const (𝕂 := ℝ) A.X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h0
  have h1 := (h0.const_mul Y).mul_const ψ
  have h2 := (rtL (N := N)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  exact h2

end Deriv

theorem hasDerivAt_rt_E_left (A : Su N) (ψ : Mat N) :
    HasDerivAt (fun s : ℝ => rt ((E A s : Mat N) * ψ)) (rt (A.X * ψ)) 0 := by
  simpa only [one_mul] using hasDerivAt_rt_E A 1 ψ

theorem hasDerivAt_rt_mul_E (A : Su N) (Y ψ : Mat N) :
    HasDerivAt (fun s : ℝ => rt (Y * ((E A s : Mat N) * ψ))) (rt (Y * A.X * ψ)) 0 := by
  simpa only [mul_assoc] using hasDerivAt_rt_E A Y ψ

/-! ## 3. The layer rotation as a flow -/

variable {n : ℕ}

theorem gT_comp (L : Fin 4 → ℕ) (h k : RSite L → SUN.SU N) (U : RLink L → SUN.SU N) :
    gT L h (gT L k U) = gT L (fun y => h y * k y) U := by
  funext l
  unfold gT
  by_cases hl : l.1.val / 2 = 0
  · simp only [if_pos hl]; group
  · simp only [if_neg hl]

theorem gT_one (L : Fin 4 → ℕ) (U : RLink L → SUN.SU N) : gT L (fun _ => 1) U = U := by
  funext l
  unfold gT
  by_cases hl : l.1.val / 2 = 0
  · simp only [if_pos hl, inv_one, mul_one, one_mul]
  · simp only [if_neg hl]

theorem continuous_gT (L : Fin 4 → ℕ) (h : RSite L → SUN.SU N) :
    Continuous (gT L h : (RLink L → SUN.SU N) → _) := by
  refine continuous_pi fun l => ?_
  unfold gT
  by_cases hl : l.1.val / 2 = 0
  · simp only [if_pos hl]
    exact (continuous_const.mul (continuous_apply l)).mul continuous_const
  · simp only [if_neg hl]
    exact continuous_apply l

/-- **The layer rotation at `z` along `exp(sX)`.** No numeral. -/
noncomputable def pageFlow (z : St n) (A : Su N) (s : ℝ) (U : Lk n → SUN.SU N) : Lk n → SUN.SU N :=
  gT (fun _ => n) (siteG (fun _ => n) z (E A s)) U

theorem isFlow_pageFlow (z : St n) (A : Su N) : IsFlow (piH N n) (pageFlow z A) where
  zero U := by
    unfold pageFlow
    rw [E_zero]
    have e : siteG (fun _ => n) z (1 : SUN.SU N) = fun _ => 1 := by
      funext y; unfold siteG; split_ifs <;> rfl
    rw [e, gT_one]
  add s r U := by
    unfold pageFlow
    rw [gT_comp]
    congr 1
    funext y
    unfold siteG
    split_ifs
    · exact E_add A s r
    · simp
  cont s := continuous_gT _ _
  pres s F hF := integral_gT (fun _ => n) _ F hF

theorem sinR_page (z : St n) (A : Su N) (s : ℝ) (U : Lk n → SUN.SU N) :
    sinR N n (pageFlow z A s U) = sinR N n U :=
  sinR_gT n _ U

/-! ## 4. The corner reads -/

open Classical in
/-- The holonomy of `((i, j), y)` read from the corner `z`, oriented so that the rotation at `z` left-translates it.
No numeral. -/
noncomputable def chi (i j : Fin 4) (y z : St n) (U : Lk n → SUN.SU N) : SUN.SU N :=
  if z = y then (sysR (fun _ => n) N).hol ((i, j), y) U
  else if z = rshift (fun _ => n) i y then (psiI i j y U)⁻¹
  else if z = rshift (fun _ => n) j y then (psiJ i j y U)⁻¹
  else psiK i j y U

theorem continuous_chi (i j : Fin 4) (y z : St n) : Continuous (chi (N := N) i j y z) := by
  unfold chi
  split_ifs
  · exact MixAnchor.continuous_hol _
  · exact (continuous_psiI i j y).inv
  · exact (continuous_psiJ i j y).inv
  · exact continuous_psiK i j y

section Corners

variable {i j : Fin 4} (hn : 2 ≤ n) (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0) (y : St n)
include hn hi hj

theorem ne_ij : i ≠ j := fun h => hj (h ▸ hi)

theorem c1 : rshift (fun _ => n) i y ≠ y := WindowRead.rshift_ne _ hn y

theorem c2 : rshift (fun _ => n) j y ≠ y := WindowRead.rshift_ne _ hn y

theorem c3 : rshift (fun _ => n) j y ≠ rshift (fun _ => n) i y :=
  ne_of_rot hn (k := j) (by simp [MixEqui.rshift_apply, (ne_ij hn hi hj).symm])

theorem c4 : rshift (fun _ => n) i (rshift (fun _ => n) j y) ≠ y :=
  rshift2_ne (fun _ => n) (ne_ij hn hi hj) hn y

theorem c5 : rshift (fun _ => n) i (rshift (fun _ => n) j y) ≠ rshift (fun _ => n) i y :=
  ne_of_rot hn (k := j) (by simp [MixEqui.rshift_apply, (ne_ij hn hi hj).symm])

theorem c6 : rshift (fun _ => n) i (rshift (fun _ => n) j y) ≠ rshift (fun _ => n) j y :=
  WindowRead.rshift_ne _ hn _

theorem chi_gT {z : St n} (hc : IsCorner n i j y z) (a : SUN.SU N) (U : Lk n → SUN.SU N) :
    chi i j y z (gT (fun _ => n) (siteG (fun _ => n) z a) U) = a * chi i j y z U := by
  have hL : ∀ k : Fin 4, 2 ≤ (fun _ : Fin 4 => n) k := fun _ => hn
  rcases hc with rfl | rfl | rfl | rfl
  · unfold chi
    rw [if_pos rfl, if_pos rfl]
    exact hol_gT_mixA (fun _ => n) hL a U hi hj z
  · unfold chi
    rw [if_neg (c1 hn hi hj y), if_pos rfl, if_neg (c1 hn hi hj y), if_pos rfl, psiI_gT hn hi hj y a U,
      mul_inv_rev, inv_inv]
  · unfold chi
    rw [if_neg (c2 hn hi hj y), if_neg (c3 hn hi hj y), if_pos rfl, if_neg (c2 hn hi hj y),
      if_neg (c3 hn hi hj y), if_pos rfl, psiJ_gT hn hi hj y a U, mul_inv_rev, inv_inv]
  · unfold chi
    rw [if_neg (c4 hn hi hj y), if_neg (c5 hn hi hj y), if_neg (c6 hn hi hj y),
      if_neg (c4 hn hi hj y), if_neg (c5 hn hi hj y), if_neg (c6 hn hi hj y), psiK_gT hn hi hj y a U]

theorem plaq_eq_chi {z : St n} (hc : IsCorner n i j y z) (U : Lk n → SUN.SU N) :
    plaq N n ((i, j), y) U = WilsonAction.wilsonDensity (chi i j y z U) := by
  rcases hc with rfl | rfl | rfl | rfl
  · unfold chi
    rw [if_pos rfl]; rfl
  · unfold chi
    rw [if_neg (c1 hn hi hj y), if_pos rfl, RectWilson.wilsonDensity_inv]
    exact plaq_eq_psiI i j y U
  · unfold chi
    rw [if_neg (c2 hn hi hj y), if_neg (c3 hn hi hj y), if_pos rfl, RectWilson.wilsonDensity_inv]
    exact plaq_eq_psiJ i j y U
  · unfold chi
    rw [if_neg (c4 hn hi hj y), if_neg (c5 hn hi hj y), if_neg (c6 hn hi hj y)]
    exact plaq_eq_psiK i j y U

end Corners

open Classical in
/-- **The current of one plaquette at the site `z`**, with the matrix `Y` inserted at the corner.
DERIVED: `1/N` the Wilson normalization; `0` off the corners. -/
noncomputable def curP (i j : Fin 4) (y z : St n) (Y : Mat N) (U : Lk n → SUN.SU N) : ℝ :=
  if IsCorner n i j y z then -(1 / (N : ℝ)) * rt (Y * (chi i j y z U : Mat N)) else 0

theorem continuous_curP (i j : Fin 4) (y z : St n) (Y : Mat N) : Continuous (curP (N := N) i j y z Y) := by
  unfold curP
  split_ifs
  · exact continuous_const.mul (continuous_rt.comp (continuous_const.mul
      (continuous_subtype_val.comp (continuous_chi i j y z))))
  · exact continuous_const

theorem isGen_plaq {i j : Fin 4} (hn : 2 ≤ n) (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0) (y z : St n)
    (A : Su N) : IsGen (pageFlow z A) (plaq N n ((i, j), y)) (curP i j y z A.X) := by
  refine ⟨continuous_curP i j y z A.X, fun U => ?_⟩
  by_cases hc : IsCorner n i j y z
  · have e : (fun s => plaq N n ((i, j), y) (pageFlow z A s U))
        = fun s => 1 - (1 / (N : ℝ)) * rt ((E A s : Mat N) * (chi i j y z U : Mat N)) := by
      funext s
      rw [plaq_eq_chi hn hi hj y hc, wilsonDensity_eq]
      unfold pageFlow
      rw [chi_gT hn hi hj y hc]
      rfl
    rw [e]
    unfold curP
    rw [if_pos hc]
    have h := ((hasDerivAt_rt_E_left A (chi i j y z U : Mat N)).const_mul (1 / (N : ℝ))).const_sub 1
    refine h.congr_deriv (by ring)
  · have e : (fun s => plaq N n ((i, j), y) (pageFlow z A s U)) = fun _ => plaq N n ((i, j), y) U := by
      funext s
      exact plaq_gT_off hi hj y z _ U hc
    rw [e]
    unfold curP
    rw [if_neg hc]
    exact hasDerivAt_const _ _

theorem isGen_curP {i j : Fin 4} (hn : 2 ≤ n) (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0) (y z : St n)
    (A : Su N) (Y : Mat N) : IsGen (pageFlow z A) (curP i j y z Y) (curP i j y z (Y * A.X)) := by
  refine ⟨continuous_curP i j y z _, fun U => ?_⟩
  by_cases hc : IsCorner n i j y z
  · have e : (fun s => curP i j y z Y (pageFlow z A s U))
        = fun s => -(1 / (N : ℝ)) * rt (Y * ((E A s : Mat N) * (chi i j y z U : Mat N))) := by
      funext s
      unfold curP
      rw [if_pos hc]
      unfold pageFlow
      rw [chi_gT hn hi hj y hc]
      rfl
    rw [e]
    unfold curP
    rw [if_pos hc]
    exact (hasDerivAt_rt_mul_E A Y (chi i j y z U : Mat N)).const_mul _
  · have e : (fun s => curP i j y z Y (pageFlow z A s U)) = fun _ => 0 := by
      funext s
      unfold curP
      rw [if_neg hc]
    rw [e]
    unfold curP
    rw [if_neg hc]
    exact hasDerivAt_const _ _

/-! ## 5. The mixed action through its currents -/

/-- A direction of the `(0,1)` plane. DERIVED: `2` the size of the block, `4` the dimension. -/
def oA (a : Fin 2) : Fin 4 := ⟨a.val, by omega⟩

/-- A direction of the `(2,3)` plane. DERIVED: `2` the size of the block, `4` the dimension. -/
def oB (b : Fin 2) : Fin 4 := ⟨2 + b.val, by omega⟩

theorem oA_low (a : Fin 2) : (oA a).val / 2 = 0 := by
  have := a.isLt
  simp only [oA]
  omega

theorem oB_high (b : Fin 2) : ¬ (oB b).val / 2 = 0 := by
  have := b.isLt
  simp only [oB]
  omega

/-- Reversing the orientation inverts the holonomy, so the density is the same. No numeral. -/
theorem plaq_swap (i j : Fin 4) (y : St n) (U : Lk n → SUN.SU N) :
    plaq N n ((j, i), y) U = plaq N n ((i, j), y) U := by
  unfold plaq
  rw [← RectWilson.wilsonDensity_inv ((sysR (fun _ => n) N).hol ((i, j), y) U), hol_eq, hol_eq]
  congr 1
  group

/-- DERIVED: `2` the two orientations of each mixed plane; `4` the dimension. -/
theorem sum_mixedOri (g : Fin 4 → Fin 4 → ℝ) (hg : ∀ i j, g j i = g i j) :
    (∑ i, ∑ j, if AnisoTorus.inPlane (i, j) then (0 : ℝ) else g i j)
      = 2 * ∑ a : Fin 2, ∑ b : Fin 2, g (oA a) (oB b) := by
  have e1 : oA 0 = 0 := by decide
  have e2 : oA 1 = 1 := by decide
  have e3 : oB 0 = 2 := by decide
  have e4 : oB 1 = 3 := by decide
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, e1, e2, e3, e4]
  have h20 := hg 0 2
  have h21 := hg 1 2
  have h30 := hg 0 3
  have h31 := hg 1 3
  rw [if_pos (by decide : AnisoTorus.inPlane ((0 : Fin 4), (0 : Fin 4)) = true),
    if_pos (by decide : AnisoTorus.inPlane ((0 : Fin 4), (1 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((0 : Fin 4), (2 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((0 : Fin 4), (3 : Fin 4)) = true),
    if_pos (by decide : AnisoTorus.inPlane ((1 : Fin 4), (0 : Fin 4)) = true),
    if_pos (by decide : AnisoTorus.inPlane ((1 : Fin 4), (1 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((1 : Fin 4), (2 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((1 : Fin 4), (3 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((2 : Fin 4), (0 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((2 : Fin 4), (1 : Fin 4)) = true),
    if_pos (by decide : AnisoTorus.inPlane ((2 : Fin 4), (2 : Fin 4)) = true),
    if_pos (by decide : AnisoTorus.inPlane ((2 : Fin 4), (3 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((3 : Fin 4), (0 : Fin 4)) = true),
    if_neg (by decide : ¬ AnisoTorus.inPlane ((3 : Fin 4), (1 : Fin 4)) = true),
    if_pos (by decide : AnisoTorus.inPlane ((3 : Fin 4), (2 : Fin 4)) = true),
    if_pos (by decide : AnisoTorus.inPlane ((3 : Fin 4), (3 : Fin 4)) = true), h20, h21, h30, h31]
  ring

/-- `S_mix = 2 Σ` over the plaquettes with first direction in `{0, 1}`. DERIVED: `2` the two orientations. -/
theorem smix_eq_sum (U : Lk n → SUN.SU N) :
    smixR N n U = 2 * ∑ a : Fin 2, ∑ b : Fin 2, ∑ y : St n, plaq N n ((oA a, oB b), y) U := by
  have step : smixR N n U
      = ∑ i, ∑ j, if AnisoTorus.inPlane (i, j) then (0 : ℝ) else ∑ y : St n, plaq N n ((i, j), y) U := by
    unfold smixR
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : AnisoTorus.inPlane (i, j) = true
    · simp [h]
    · simp [h]
  rw [step]
  exact sum_mixedOri _ fun i j => Finset.sum_congr rfl fun y _ => plaq_swap i j y U

/-- **The current of `S_mix` at the site `z`**, with `Y` inserted. DERIVED: `2` the two orientations. -/
noncomputable def curS (z : St n) (Y : Mat N) (U : Lk n → SUN.SU N) : ℝ :=
  2 * ∑ a : Fin 2, ∑ b : Fin 2, ∑ y : St n, curP (oA a) (oB b) y z Y U

theorem continuous_curS (z : St n) (Y : Mat N) : Continuous (curS (N := N) z Y) :=
  continuous_const.mul (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_finsetSum _ fun y _ => continuous_curP _ _ _ _ _)

theorem isGen_smix (hn : 2 ≤ n) (z : St n) (A : Su N) :
    IsGen (pageFlow z A) (smixR N n) (curS z A.X) := by
  have e : smixR N n = fun U => 2 * ∑ a : Fin 2, ∑ b : Fin 2, ∑ y : St n, plaq N n ((oA a, oB b), y) U :=
    funext smix_eq_sum
  rw [e]
  exact IsGen.const_mul 2 (IsGen.sum _ fun a _ => IsGen.sum _ fun b _ => IsGen.sum _ fun y _ =>
    isGen_plaq hn (oA_low a) (oB_high b) y z A)

theorem isGen_curS (hn : 2 ≤ n) (z : St n) (A : Su N) (Y : Mat N) :
    IsGen (pageFlow z A) (curS z Y) (curS z (Y * A.X)) :=
  IsGen.const_mul 2 (IsGen.sum _ fun a _ => IsGen.sum _ fun b _ => IsGen.sum _ fun y _ =>
    isGen_curP hn (oA_low a) (oB_high b) y z A Y)

/-- The Gibbs weight of the anisotropic torus. No numeral. -/
noncomputable def wt (N : ℕ) (β t : ℝ) (n : ℕ) (U : Lk n → SUN.SU N) : ℝ :=
  Real.exp (-(β * sinR N n U + t * smixR N n U))

theorem continuous_act (β t : ℝ) :
    Continuous fun U : Lk n → SUN.SU N => β * sinR N n U + t * smixR N n U :=
  (continuous_const.mul (continuous_sinR n)).add (continuous_const.mul (continuous_smixR n))

theorem continuous_wt (β t : ℝ) : Continuous (wt N β t n) :=
  Real.continuous_exp.comp (continuous_act β t).neg

theorem integrable_of_cont {f : (Lk n → SUN.SU N) → ℝ} (hf : Continuous f) : Integrable f (piH N n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem int_sub {f g : (Lk n → SUN.SU N) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ U, (f U - g U) ∂piH N n = ∫ U, f U ∂piH N n - ∫ U, g U ∂piH N n :=
  integral_sub (integrable_of_cont hf) (integrable_of_cont hg)

theorem int_sum2 {α β : Type*} [Fintype α] [Fintype β] (f : α → β → (Lk n → SUN.SU N) → ℝ)
    (hf : ∀ a b, Continuous (f a b)) :
    ∫ U, ∑ x, ∑ y, f x y U ∂piH N n = ∑ x, ∑ y, ∫ U, f x y U ∂piH N n := by
  rw [integral_finsetSum _ fun x _ => integrable_of_cont (continuous_finsetSum _ fun y _ => hf x y)]
  exact Finset.sum_congr rfl fun x _ => integral_finsetSum _ fun y _ => integrable_of_cont (hf x y)

/-- **The Schwinger–Dyson identity of the layer rotation, free of `β`**:
`∫ (DO − t O J_{z,X}) e^{−(β S_in + t S_mix)} = 0`. The rotation fixes `S_in`, so the in-plane coupling enters only
through the weight. No numeral. -/
theorem sd_page (hn : 2 ≤ n) (z : St n) (A : Su N) (β t : ℝ) {O DO : (Lk n → SUN.SU N) → ℝ}
    (hO : Continuous O) (hg : IsGen (pageFlow z A) O DO) :
    ∫ U, (DO U - t * (O U * curS z A.X U)) * wt N β t n U ∂piH N n = 0 := by
  have hV : IsGen (pageFlow z A) (fun U => β * sinR N n U + t * smixR N n U)
      fun U => β * 0 + t * curS z A.X U :=
    ((IsGen.of_inv (sinR_page z A)).const_mul β).add ((isGen_smix hn z A).const_mul t)
  have h := schwingerDyson (isFlow_pageFlow z A) hO (continuous_act β t) hg hV
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show (DO U - t * (O U * curS z A.X U)) * wt N β t n U
    = (DO U - O U * (β * 0 + t * curS z A.X U)) * Real.exp (-(β * sinR N n U + t * smixR N n U))
  unfold wt
  ring

/-- A family in `su(N)` whose squares sum to a scalar: `Σ_a X_a² = −c`. For an orthonormal basis `c` is the Casimir
`C_F` of the fundamental. No numeral. -/
structure CasFam (N : ℕ) (ι : Type*) [Fintype ι] where
  el : ι → Su N
  c : ℝ
  sq : ∑ a, (el a).X * (el a).X = -((c : ℂ) • (1 : Mat N))

variable {ι : Type*} [Fintype ι]

open Classical in
/-- The Casimir at one corner. DERIVED: `1` the Wilson normalization. -/
theorem sum_curP (F : CasFam N ι) {i j : Fin 4} (hn : 2 ≤ n) (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0)
    (y z : St n) (U : Lk n → SUN.SU N) :
    ∑ a, curP i j y z ((F.el a).X * (F.el a).X) U
      = if IsCorner n i j y z then F.c * (1 - plaq N n ((i, j), y) U) else 0 := by
  by_cases hc : IsCorner n i j y z
  · simp only [curP, if_pos hc]
    rw [← Finset.mul_sum, ← rt_sum, ← Finset.sum_mul, F.sq, plaq_eq_chi hn hi hj y hc, wilsonDensity_eq]
    have e : -((F.c : ℂ) • (1 : Mat N)) * (chi i j y z U : Mat N)
        = ((-F.c : ℝ) : ℂ) • (chi i j y z U : Mat N) := by
      rw [neg_mul, Matrix.smul_mul, one_mul, ← neg_smul]
      congr 1
      push_cast
      rfl
    rw [e, rt_real_smul]
    ring
  · simp only [curP, if_neg hc, Finset.sum_const_zero]

open Classical in
/-- A plaquette has four corners. DERIVED: `4` the corners. -/
theorem sum_corner {i j : Fin 4} (hn : 2 ≤ n) (hi : i.val / 2 = 0) (hj : ¬ j.val / 2 = 0) (y : St n) (G : ℝ) :
    (∑ z : St n, if IsCorner n i j y z then G else 0) = 4 * G := by
  set S : Finset (St n) :=
    {y, rshift (fun _ => n) i y, rshift (fun _ => n) j y, rshift (fun _ => n) i (rshift (fun _ => n) j y)}
    with hS
  have hmem : ∀ z, IsCorner n i j y z ↔ z ∈ S := fun z => by
    unfold MixEqui.IsCorner
    simp [hS]
  have hcard : S.card = 4 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact (c6 hn hi hj y).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(c3 hn hi hj y).symm, (c5 hn hi hj y).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(c1 hn hi hj y).symm, (c2 hn hi hj y).symm, (c4 hn hi hj y).symm⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have hf : (Finset.univ.filter fun z => IsCorner n i j y z) = S := by
    ext z
    simp [hmem z]
  rw [hf, hcard]
  simp

theorem sum_pull {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (g : α → β → γ → ℝ) :
    ∑ x, ∑ y, ∑ w, g x y w = ∑ w, ∑ x, ∑ y, g x y w :=
  calc ∑ x, ∑ y, ∑ w, g x y w = ∑ x, ∑ w, ∑ y, g x y w :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- **The Casimir of the mixed action**, pointwise:
`Σ_z Σ_a J²_{z,a} = 4 c (8 n⁴ − S_mix)`, each mixed plaquette read at its four corners.
DERIVED: `4` the corners; `8` the mixed ordered orientations per site; `4` the exponent, the dimension. -/
theorem sum_curS (F : CasFam N ι) (hn : 2 ≤ n) (U : Lk n → SUN.SU N) :
    ∑ z : St n, ∑ a, curS z ((F.el a).X * (F.el a).X) U
      = 4 * F.c * (8 * (n : ℝ) ^ 4 - smixR N n U) := by
  classical
  have h1 : ∀ (a' b : Fin 2) (y : St n),
      ∑ z : St n, ∑ a, curP (oA a') (oB b) y z ((F.el a).X * (F.el a).X) U
        = 4 * (F.c * (1 - plaq N n ((oA a', oB b), y) U)) := fun a' b y => by
    simp_rw [sum_curP F hn (oA_low a') (oB_high b) y _ U]
    exact sum_corner hn (oA_low a') (oB_high b) y _
  have h2 : ∑ _a : Fin 2, ∑ _b : Fin 2, ∑ _y : St n, (1 : ℝ) = 4 * (n : ℝ) ^ 4 := by
    simp [Fintype.card_pi]
    ring
  have h3 : ∑ z : St n, ∑ a, curS z ((F.el a).X * (F.el a).X) U
      = 2 * ∑ a' : Fin 2, ∑ b : Fin 2, ∑ y : St n, ∑ z : St n, ∑ a,
          curP (oA a') (oB b) y z ((F.el a).X * (F.el a).X) U := by
    unfold curS
    simp only [← Finset.mul_sum]
    congr 1
    exact (sum_pull fun z a a' => ∑ b : Fin 2, ∑ y : St n,
        curP (oA a') (oB b) y z ((F.el a).X * (F.el a).X) U).trans
      (Finset.sum_congr rfl fun a' _ => (sum_pull fun z a b => ∑ y : St n,
        curP (oA a') (oB b) y z ((F.el a).X * (F.el a).X) U).trans
      (Finset.sum_congr rfl fun b _ => sum_pull fun z a y =>
        curP (oA a') (oB b) y z ((F.el a).X * (F.el a).X) U))
  rw [h3, smix_eq_sum U]
  simp only [h1]
  have h4 : ∑ a' : Fin 2, ∑ b : Fin 2, ∑ y : St n, 4 * (F.c * (1 - plaq N n ((oA a', oB b), y) U))
      = 4 * F.c * ((∑ _a : Fin 2, ∑ _b : Fin 2, ∑ _y : St n, (1 : ℝ))
        - ∑ a' : Fin 2, ∑ b : Fin 2, ∑ y : St n, plaq N n ((oA a', oB b), y) U) := by
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [h4, h2]
  ring

/-- The Gibbs expectation on the anisotropic torus. No numeral. -/
noncomputable def gib (N : ℕ) (β t : ℝ) (n : ℕ) (f : (Lk n → SUN.SU N) → ℝ) : ℝ :=
  (∫ U, f U * wt N β t n U ∂piH N n) / AnisoTorus.ZA N β t n

/-- **The current square** `G_n = Σ_{z, a} ⟨J_{z,a}²⟩_n`. DERIVED: `2` the square. -/
noncomputable def curG (F : CasFam N ι) (β t : ℝ) (n : ℕ) : ℝ :=
  ∑ z : St n, ∑ a, gib N β t n fun U => curS z (F.el a).X U ^ 2

theorem za_eq (β t : ℝ) : AnisoTorus.ZA N β t n = ∫ U, wt N β t n U ∂piH N n := ZA_eq_int β t n

/-- One current: `⟨J_{X X}⟩ = t ⟨J²⟩`, integrated. DERIVED: `2` the square. -/
theorem sd_current (hn : 2 ≤ n) (z : St n) (A : Su N) (β t : ℝ) :
    ∫ U, curS z (A.X * A.X) U * wt N β t n U ∂piH N n
      = t * ∫ U, curS z A.X U ^ 2 * wt N β t n U ∂piH N n := by
  have h := sd_page hn z A β t (continuous_curS z A.X) (isGen_curS hn z A A.X)
  have hc := continuous_curS (N := N) z A.X
  have hc2 := continuous_curS (N := N) z (A.X * A.X)
  have e : ∀ U, (curS z (A.X * A.X) U - t * (curS z A.X U * curS z A.X U)) * wt N β t n U
      = curS z (A.X * A.X) U * wt N β t n U - t * (curS z A.X U ^ 2 * wt N β t n U) := fun U => by ring
  simp only [e] at h
  have h1 : ∫ U, (curS z (A.X * A.X) U * wt N β t n U - t * (curS z A.X U ^ 2 * wt N β t n U)) ∂piH N n
      = ∫ U, curS z (A.X * A.X) U * wt N β t n U ∂piH N n
        - ∫ U, t * (curS z A.X U ^ 2 * wt N β t n U) ∂piH N n :=
    int_sub (hc2.mul (continuous_wt β t)) (continuous_const.mul ((hc.pow 2).mul (continuous_wt β t)))
  rw [h1, integral_const_mul] at h
  linarith

/-- **The energy identity**: `4 c (8 n⁴ − ⟨S_mix⟩_n) = t G_n`, at every `β`, `t`, `n ≥ 2`, for the Wilson measure.
DERIVED: `4` the corners; `8` the mixed orientations per site; `4` the dimension. -/
theorem energy_current (F : CasFam N ι) (hn : 2 ≤ n) (β t : ℝ) :
    4 * F.c * (8 * (n : ℝ) ^ 4 - meanMix N β t n) = t * curG F β t n := by
  have hZ : AnisoTorus.ZA N β t n ≠ 0 := (ZA_pos β t n).ne'
  have hw := continuous_wt (N := N) (n := n) β t
  have hL : ∑ z : St n, ∑ a, ∫ U, curS z ((F.el a).X * (F.el a).X) U * wt N β t n U ∂piH N n
      = 4 * F.c * (8 * (n : ℝ) ^ 4 * AnisoTorus.ZA N β t n - mixNum N β t n) := by
    have h1 : ∀ U : Lk n → SUN.SU N,
        (∑ z : St n, ∑ a, curS z ((F.el a).X * (F.el a).X) U * wt N β t n U)
          = 4 * F.c * (8 * (n : ℝ) ^ 4) * wt N β t n U
            - 4 * F.c * (smixR N n U * wt N β t n U) := fun U => by
      simp only [← Finset.sum_mul]
      rw [sum_curS F hn U]
      ring
    have h2 : ∫ U, (∑ z : St n, ∑ a, curS z ((F.el a).X * (F.el a).X) U * wt N β t n U) ∂piH N n
        = ∑ z : St n, ∑ a, ∫ U, curS z ((F.el a).X * (F.el a).X) U * wt N β t n U ∂piH N n :=
      int_sum2 (fun z a U => curS z ((F.el a).X * (F.el a).X) U * wt N β t n U)
        fun z a => (continuous_curS z _).mul hw
    rw [← h2]
    simp only [h1]
    have h5 : ∫ U, (4 * F.c * (8 * (n : ℝ) ^ 4) * wt N β t n U
          - 4 * F.c * (smixR N n U * wt N β t n U)) ∂piH N n
        = ∫ U, 4 * F.c * (8 * (n : ℝ) ^ 4) * wt N β t n U ∂piH N n
          - ∫ U, 4 * F.c * (smixR N n U * wt N β t n U) ∂piH N n :=
      int_sub (continuous_const.mul hw) (continuous_const.mul ((continuous_smixR n).mul hw))
    rw [h5, integral_const_mul, integral_const_mul, ← za_eq]
    unfold mixNum wt
    ring
  have hR : ∑ z : St n, ∑ a, ∫ U, curS z ((F.el a).X * (F.el a).X) U * wt N β t n U ∂piH N n
      = t * (curG F β t n * AnisoTorus.ZA N β t n) := by
    unfold curG gib
    simp only [Finset.sum_mul, Finset.mul_sum, div_mul_cancel₀ _ hZ]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun a _ => sd_current hn z (F.el a) β t
  have h := hL.symm.trans hR
  unfold meanMix
  have h3 : 4 * F.c * (8 * (n : ℝ) ^ 4 - mixNum N β t n / AnisoTorus.ZA N β t n)
      = (4 * F.c * (8 * (n : ℝ) ^ 4 * AnisoTorus.ZA N β t n - mixNum N β t n)) / AnisoTorus.ZA N β t n := by
    field_simp
  rw [h3, h, ← mul_assoc, mul_div_cancel_right₀ _ hZ]

/-- **The doubling combination through the currents**:
`mixCut = ⟨S_mix⟩_{2n} − 16 ⟨S_mix⟩_n = (t / 4c)(16 G_n − G_{2n})`, for every `β`, `t`, window `w ≥ 1`. The constant
`8 n⁴` cancels exactly in the doubling. DERIVED: `16 = 2⁴`; `4` the corners; `2` the doubling, the least side;
`1` the least window. -/
theorem mixCut_eq_current (F : CasFam N ι) (hc : F.c ≠ 0) (β t : ℝ) {w : ℕ} (hw : 1 ≤ w) :
    mixCut N β t w = t / (4 * F.c) * (16 * curG F β t (2 ^ w) - curG F β t (2 ^ (w + 1))) := by
  have hn1 : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hn2 : 2 ≤ 2 ^ (w + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 := energy_current F hn1 β t
  have h2 := energy_current F hn2 β t
  unfold mixCut
  push_cast at h1 h2
  have hc4 : 4 * F.c ≠ 0 := mul_ne_zero (by norm_num) hc
  have a1 : t * curG F β t (2 ^ w) / (4 * F.c) = 8 * ((2 : ℝ) ^ w) ^ 4 - meanMix N β t (2 ^ w) := by
    rw [div_eq_iff hc4]; linarith
  have a2 : t * curG F β t (2 ^ (w + 1)) / (4 * F.c)
      = 8 * ((2 : ℝ) ^ (w + 1)) ^ 4 - meanMix N β t (2 ^ (w + 1)) := by
    rw [div_eq_iff hc4]; linarith
  have e1 : meanMix N β t (2 ^ w) = 8 * ((2 : ℝ) ^ w) ^ 4 - t * curG F β t (2 ^ w) / (4 * F.c) := by
    linarith
  have e2 : meanMix N β t (2 ^ (w + 1)) = 8 * ((2 : ℝ) ^ (w + 1)) ^ 4
      - t * curG F β t (2 ^ (w + 1)) / (4 * F.c) := by
    linarith
  rw [e1, e2]
  field_simp
  ring

/-- `G_n ≥ 0`. DERIVED: `2` the square. -/
theorem curG_nonneg (F : CasFam N ι) (β t : ℝ) : 0 ≤ curG F β t n := by
  unfold curG gib
  refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun a _ => div_nonneg ?_ (ZA_pos β t n).le
  exact integral_nonneg fun U => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- **The one-sided consequence**: `⟨S_mix⟩_n ≤ 8 n⁴` for `t ≥ 0`. DERIVED: `8`, `4` as in `energy_current`. -/
theorem meanMix_le (F : CasFam N ι) (hc : 0 < F.c) (hn : 2 ≤ n) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    meanMix N β t n ≤ 8 * (n : ℝ) ^ 4 := by
  have h := energy_current F hn β t
  have h2 := mul_nonneg ht (curG_nonneg F β t (n := n))
  rw [← h] at h2
  have h3 : 0 ≤ 8 * (n : ℝ) ^ 4 - meanMix N β t n := by
    by_contra hneg
    have hneg' := not_le.mp hneg
    nlinarith
  linarith

/-- The Gibbs covariance of `S_mix` with the current square, `Cov_n(S_mix, |J|²)`. No numeral. -/
noncomputable def covCur (F : CasFam N ι) (β t : ℝ) (n : ℕ) : ℝ :=
  (∑ z : St n, ∑ a, gib N β t n fun U => smixR N n U * curS z (F.el a).X U ^ 2)
    - meanMix N β t n * curG F β t n

/-- **The variance through the currents**: `4 c Var_n(S_mix) = G_n − t Cov_n(S_mix, |J|²)`.
DERIVED: `4`, `8` as in `energy_current`; `2` the square. -/
theorem var_current (F : CasFam N ι) (hn : 2 ≤ n) (β t : ℝ) :
    4 * F.c * MixCutTest.varMix N β t n = curG F β t n - t * covCur F β t n := by
  have hZ : AnisoTorus.ZA N β t n ≠ 0 := (ZA_pos β t n).ne'
  have hw := continuous_wt (N := N) (n := n) β t
  have hS := continuous_smixR (N := N) n
  have hs : ∀ (z : St n) (a : ι),
      (∫ U, curS z (F.el a).X U ^ 2 * wt N β t n U ∂piH N n)
        + ∫ U, smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U ∂piH N n
      = t * ∫ U, smixR N n U * curS z (F.el a).X U ^ 2 * wt N β t n U ∂piH N n := fun z a => by
    have hc := continuous_curS (N := N) z (F.el a).X
    have hc2 := continuous_curS (N := N) z ((F.el a).X * (F.el a).X)
    have hg := IsGen.mul (isFlow_pageFlow z (F.el a)).zero hS hc (isGen_smix hn z (F.el a))
      (isGen_curS hn z (F.el a) (F.el a).X)
    have h : ∫ U, (curS z (F.el a).X U * curS z (F.el a).X U
          + smixR N n U * curS z ((F.el a).X * (F.el a).X) U
          - t * (smixR N n U * curS z (F.el a).X U * curS z (F.el a).X U)) * wt N β t n U ∂piH N n = 0 :=
      sd_page hn z (F.el a) β t (hS.mul hc) hg
    have e : ∀ U, (curS z (F.el a).X U * curS z (F.el a).X U
          + smixR N n U * curS z ((F.el a).X * (F.el a).X) U
          - t * (smixR N n U * curS z (F.el a).X U * curS z (F.el a).X U)) * wt N β t n U
        = (curS z (F.el a).X U ^ 2 * wt N β t n U
          + smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U)
          - t * (smixR N n U * curS z (F.el a).X U ^ 2 * wt N β t n U) := fun U => by ring
    simp only [e] at h
    have h1 : ∫ U, ((curS z (F.el a).X U ^ 2 * wt N β t n U
          + smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U)
          - t * (smixR N n U * curS z (F.el a).X U ^ 2 * wt N β t n U)) ∂piH N n
        = ∫ U, (curS z (F.el a).X U ^ 2 * wt N β t n U
          + smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U) ∂piH N n
          - ∫ U, t * (smixR N n U * curS z (F.el a).X U ^ 2 * wt N β t n U) ∂piH N n :=
      int_sub (((hc.pow 2).mul hw).add ((hS.mul hc2).mul hw))
        (continuous_const.mul ((hS.mul (hc.pow 2)).mul hw))
    have h2 : ∫ U, (curS z (F.el a).X U ^ 2 * wt N β t n U
          + smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U) ∂piH N n
        = ∫ U, curS z (F.el a).X U ^ 2 * wt N β t n U ∂piH N n
          + ∫ U, smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U ∂piH N n :=
      integral_add (integrable_of_cont ((hc.pow 2).mul hw)) (integrable_of_cont ((hS.mul hc2).mul hw))
    rw [h1, h2, integral_const_mul] at h
    linarith
  have hL : ∑ z : St n, ∑ a, ∫ U, smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U ∂piH N n
      = 4 * F.c * (8 * (n : ℝ) ^ 4 * mixNum N β t n - MixCutTest.mixSq N β t n) := by
    have h1 : ∀ U : Lk n → SUN.SU N,
        (∑ z : St n, ∑ a, smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U)
          = 4 * F.c * (8 * (n : ℝ) ^ 4) * (smixR N n U * wt N β t n U)
            - 4 * F.c * (smixR N n U * smixR N n U * wt N β t n U) := fun U => by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      rw [sum_curS F hn U]
      ring
    have h2 : ∫ U, (∑ z : St n, ∑ a, smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U) ∂piH N n
        = ∑ z : St n, ∑ a, ∫ U, smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U ∂piH N n :=
      int_sum2 (fun z a U => smixR N n U * curS z ((F.el a).X * (F.el a).X) U * wt N β t n U)
        fun z a => (hS.mul (continuous_curS z _)).mul hw
    rw [← h2]
    simp only [h1]
    have h5 : ∫ U, (4 * F.c * (8 * (n : ℝ) ^ 4) * (smixR N n U * wt N β t n U)
          - 4 * F.c * (smixR N n U * smixR N n U * wt N β t n U)) ∂piH N n
        = ∫ U, 4 * F.c * (8 * (n : ℝ) ^ 4) * (smixR N n U * wt N β t n U) ∂piH N n
          - ∫ U, 4 * F.c * (smixR N n U * smixR N n U * wt N β t n U) ∂piH N n :=
      int_sub (continuous_const.mul (hS.mul hw)) (continuous_const.mul ((hS.mul hS).mul hw))
    rw [h5, integral_const_mul, integral_const_mul]
    unfold mixNum MixCutTest.mixSq wt
    ring
  have hG : ∑ z : St n, ∑ a, ∫ U, curS z (F.el a).X U ^ 2 * wt N β t n U ∂piH N n
      = curG F β t n * AnisoTorus.ZA N β t n := by
    unfold curG gib
    simp only [Finset.sum_mul, div_mul_cancel₀ _ hZ]
  have hT : ∑ z : St n, ∑ a, ∫ U, smixR N n U * curS z (F.el a).X U ^ 2 * wt N β t n U ∂piH N n
      = (covCur F β t n + meanMix N β t n * curG F β t n) * AnisoTorus.ZA N β t n := by
    unfold covCur
    rw [sub_add_cancel]
    unfold gib
    simp only [Finset.sum_mul, div_mul_cancel₀ _ hZ]
  have hsum : curG F β t n * AnisoTorus.ZA N β t n
      + 4 * F.c * (8 * (n : ℝ) ^ 4 * mixNum N β t n - MixCutTest.mixSq N β t n)
      = t * ((covCur F β t n + meanMix N β t n * curG F β t n) * AnisoTorus.ZA N β t n) := by
    rw [← hG, ← hL, ← hT, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => hs z a
  have hE := energy_current F hn β t
  unfold MixCutTest.varMix
  have hm : mixNum N β t n = meanMix N β t n * AnisoTorus.ZA N β t n := by
    unfold meanMix
    field_simp
  have hq : MixCutTest.mixSq N β t n
      = (MixCutTest.mixSq N β t n / AnisoTorus.ZA N β t n) * AnisoTorus.ZA N β t n := by
    field_simp
  set q := MixCutTest.mixSq N β t n / AnisoTorus.ZA N β t n
  rw [hq, hm] at hsum
  have hsum2 : curG F β t n + 4 * F.c * (8 * (n : ℝ) ^ 4 * meanMix N β t n - q)
      = t * (covCur F β t n + meanMix N β t n * curG F β t n) := by
    have : (curG F β t n + 4 * F.c * (8 * (n : ℝ) ^ 4 * meanMix N β t n - q)) * AnisoTorus.ZA N β t n
        = (t * (covCur F β t n + meanMix N β t n * curG F β t n)) * AnisoTorus.ZA N β t n := by
      linear_combination hsum
    exact mul_right_cancel₀ hZ this
  have hE2 : t * (meanMix N β t n * curG F β t n)
      = meanMix N β t n * (4 * F.c * (8 * (n : ℝ) ^ 4 - meanMix N β t n)) := by
    rw [mul_left_comm, hE.symm]
  linear_combination -hsum2 - hE2

/-! ## 6. The colour Ward identity -/

section Full

variable (L : Fin 4 → ℕ)

/-- The full gauge rotation, every link. No numeral. -/
noncomputable def gF (h : RSite L → SUN.SU N) (U : RLink L → SUN.SU N) : RLink L → SUN.SU N :=
  fun l => h l.2 * U l * (h (rshift L l.1 l.2))⁻¹

theorem hol_gF (h : RSite L → SUN.SU N) (U : RLink L → SUN.SU N) (i j : Fin 4) (x : RSite L) :
    (sysR L N).hol ((i, j), x) (gF L h U) = h x * (sysR L N).hol ((i, j), x) U * (h x)⁻¹ := by
  rw [hol_eq, hol_eq]
  simp only [gF]
  rw [rshift_comm L j i x]
  group

theorem gF_gT (a h : RSite L → SUN.SU N) (U : RLink L → SUN.SU N) :
    gF L a (gT L h U) = gT L (fun y => a y * h y * (a y)⁻¹) (gF L a U) := by
  funext l
  unfold gF gT
  by_cases hl : l.1.val / 2 = 0
  · simp only [if_pos hl]; group
  · simp only [if_neg hl]

/-- Linkwise measure-preserving maps preserve product Haar integrals of continuous functions. No numeral. -/
theorem integral_linkwise (f : RLink L → SUN.SU N → SUN.SU N)
    (hc : ∀ l, MeasurePreserving (f l) (probHaar (SUN.SU N)) (probHaar (SUN.SU N)))
    (F : (RLink L → SUN.SU N) → ℝ) (hF : Continuous F) :
    ∫ U, F (fun l => f l (U l)) ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
      = ∫ U, F U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) := by
  have hmeas : Measurable (fun (U : RLink L → SUN.SU N) (l : RLink L) => f l (U l)) :=
    measurable_pi_lambda _ fun l => (hc l).measurable.comp (measurable_pi_apply l)
  have hmap : (Measure.pi fun _ : RLink L => probHaar (SUN.SU N)).map
      (fun (U : RLink L → SUN.SU N) (l : RLink L) => f l (U l))
      = Measure.pi fun _ : RLink L => probHaar (SUN.SU N) := by
    rw [Measure.pi_map_pi (fun l => (hc l).aemeasurable)]
    simp only [(hc _).map_eq]
  rw [← integral_map hmeas.aemeasurable (by rw [hmap]; exact hF.aestronglyMeasurable), hmap]

theorem integral_gF (h : RSite L → SUN.SU N) (F : (RLink L → SUN.SU N) → ℝ) (hF : Continuous F) :
    ∫ U, F (gF L h U) ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N))
      = ∫ U, F U ∂(Measure.pi fun _ : RLink L => probHaar (SUN.SU N)) :=
  integral_linkwise L (fun l u => h l.2 * u * (h (rshift L l.1 l.2))⁻¹)
    (fun _ => (measurePreserving_mul_right (probHaar (SUN.SU N)) _).comp
      (measurePreserving_mul_left (probHaar (SUN.SU N)) _)) F hF

end Full

theorem plaq_gF (h : St n → SUN.SU N) (q : Pq n) (U : Lk n → SUN.SU N) :
    plaq N n q (gF (fun _ => n) h U) = plaq N n q U := by
  obtain ⟨⟨i, j⟩, x⟩ := q
  unfold plaq
  rw [hol_gF]
  exact WilsonAction.wilsonDensity_conj _ _

theorem smix_gF (h : St n → SUN.SU N) (U : Lk n → SUN.SU N) :
    smixR N n (gF (fun _ => n) h U) = smixR N n U := by
  unfold smixR
  simp only [plaq_gF]

theorem sin_gF (h : St n → SUN.SU N) (U : Lk n → SUN.SU N) :
    sinR N n (gF (fun _ => n) h U) = sinR N n U := by
  unfold sinR
  simp only [plaq_gF]

theorem wt_gF (β t : ℝ) (h : St n → SUN.SU N) (U : Lk n → SUN.SU N) :
    wt N β t n (gF (fun _ => n) h U) = wt N β t n U := by
  unfold wt
  rw [smix_gF, sin_gF]

theorem conj_site_ne {z w : St n} (hzw : w ≠ z) (a₀ e : SUN.SU N) :
    (fun y => siteG (fun _ => n) z a₀ y * siteG (fun _ => n) w e y * (siteG (fun _ => n) z a₀ y)⁻¹)
      = siteG (fun _ => n) w e := by
  funext y
  unfold siteG
  by_cases hy : y = z
  · subst hy
    simp [hzw.symm]
  · simp [hy]

theorem conj_site_same (z : St n) (a₀ e : SUN.SU N) :
    (fun y => siteG (fun _ => n) z a₀ y * siteG (fun _ => n) z e y * (siteG (fun _ => n) z a₀ y)⁻¹)
      = siteG (fun _ => n) z (a₀ * e * a₀⁻¹) := by
  funext y
  unfold siteG
  by_cases hy : y = z
  · simp [hy]
  · simp [hy]

/-- A rotation at another site does not see the current at `w`. No numeral. -/
theorem cur_gF_ne (hn : 2 ≤ n) {z w : St n} (hzw : w ≠ z) (a₀ : SUN.SU N) (B : Su N)
    (U : Lk n → SUN.SU N) :
    curS w B.X (gF (fun _ => n) (siteG (fun _ => n) z a₀) U) = curS w B.X U := by
  have h1 := (isGen_smix (N := N) hn w B).2 (gF (fun _ => n) (siteG (fun _ => n) z a₀) U)
  have h2 := (isGen_smix (N := N) hn w B).2 U
  have e : (fun s => smixR N n (pageFlow w B s (gF (fun _ => n) (siteG (fun _ => n) z a₀) U)))
      = fun s => smixR N n (pageFlow w B s U) := by
    funext s
    unfold pageFlow
    have hc := gF_gT (fun _ => n) (siteG (fun _ => n) z a₀) (siteG (fun _ => n) w (E B s)) U
    rw [conj_site_ne hzw] at hc
    rw [← hc, smix_gF]
  rw [e] at h1
  exact h1.unique h2

/-- `exp` of a flipped generator. No numeral. -/
theorem E_flip (A : Su N) (a₀ : SUN.SU N) (h : (a₀ : Mat N) * A.X * star (a₀ : Mat N) = -A.X) (s : ℝ) :
    a₀ * E A (-s) * a₀⁻¹ = E A s := by
  apply Subtype.ext
  show (a₀ : Mat N) * NormedSpace.exp ((-s) • A.X) * star (a₀ : Mat N) = NormedSpace.exp (s • A.X)
  have hu1 : (a₀ : Mat N) * star (a₀ : Mat N) = 1 := (Matrix.mem_unitaryGroup_iff.mp a₀.2.1)
  have hu2 : star (a₀ : Mat N) * (a₀ : Mat N) = 1 := Matrix.mem_unitaryGroup_iff'.mp a₀.2.1
  have hinv : (a₀ : Mat N)⁻¹ = star (a₀ : Mat N) := Matrix.inv_eq_right_inv hu1
  have hunit : IsUnit (a₀ : Mat N) := ⟨⟨_, star (a₀ : Mat N), hu1, hu2⟩, rfl⟩
  have e := Matrix.exp_conj (a₀ : Mat N) ((-s) • A.X) hunit
  rw [hinv] at e
  rw [← e]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, h, smul_neg, neg_smul, neg_neg]

/-- The rotation by a flipping element reverses the current at `z`. DERIVED: `0` the base time. -/
theorem cur_gF_flip (hn : 2 ≤ n) (z : St n) (A : Su N) (a₀ : SUN.SU N)
    (h : (a₀ : Mat N) * A.X * star (a₀ : Mat N) = -A.X) (U : Lk n → SUN.SU N) :
    curS z A.X (gF (fun _ => n) (siteG (fun _ => n) z a₀) U) = -curS z A.X U := by
  have h1 := (isGen_smix (N := N) hn z A).2 (gF (fun _ => n) (siteG (fun _ => n) z a₀) U)
  have h2 := (isGen_smix (N := N) hn z A).2 U
  have e : (fun s => smixR N n (pageFlow z A s (gF (fun _ => n) (siteG (fun _ => n) z a₀) U)))
      = fun s => smixR N n (pageFlow z A (-s) U) := by
    funext s
    unfold pageFlow
    have hc := gF_gT (fun _ => n) (siteG (fun _ => n) z a₀) (siteG (fun _ => n) z (E A (-s))) U
    rw [conj_site_same, E_flip A a₀ h s] at hc
    rw [← hc, smix_gF]
  rw [e] at h1
  have h0 : HasDerivAt (fun s : ℝ => -s) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have h3 : HasDerivAt (fun s => smixR N n (pageFlow z A s U)) (curS z A.X U) ((fun s : ℝ => -s) 0) := by
    simpa using h2
  have h4 := h3.comp (0 : ℝ) h0
  have h5 : HasDerivAt (fun s => smixR N n (pageFlow z A (-s) U)) (curS z A.X U * -1) 0 := h4
  rw [mul_neg_one] at h5
  exact h1.unique h5

/-- **The colour Ward identity**: if `a₀ X a₀⁻¹ = −X` then `⟨J_{z,X} J_{w,Y}⟩ = 0` for `z ≠ w`, at every `β`, `t`,
`n ≥ 2`. The current at `z` is charged under gauge rotations at `z`, and the current at `w` is not. No numeral. -/
theorem cross_zero (hn : 2 ≤ n) {z w : St n} (hzw : w ≠ z) (A B : Su N) (a₀ : SUN.SU N)
    (h : (a₀ : Mat N) * A.X * star (a₀ : Mat N) = -A.X) (β t : ℝ) :
    ∫ U, curS z A.X U * curS w B.X U * wt N β t n U ∂piH N n = 0 := by
  have hF : Continuous fun U : Lk n → SUN.SU N => curS z A.X U * curS w B.X U * wt N β t n U :=
    ((continuous_curS z A.X).mul (continuous_curS w B.X)).mul (continuous_wt β t)
  have hi := integral_gF (fun _ => n) (siteG (fun _ => n) z a₀) _ hF
  have e : ∀ U : Lk n → SUN.SU N,
      curS z A.X (gF (fun _ => n) (siteG (fun _ => n) z a₀) U)
          * curS w B.X (gF (fun _ => n) (siteG (fun _ => n) z a₀) U)
          * wt N β t n (gF (fun _ => n) (siteG (fun _ => n) z a₀) U)
        = -(curS z A.X U * curS w B.X U * wt N β t n U) := fun U => by
    rw [cur_gF_flip hn z A a₀ h, cur_gF_ne hn hzw, wt_gF]
    ring
  simp only [e] at hi
  rw [integral_neg] at hi
  have hi' : -∫ U, curS z A.X U * curS w B.X U * wt N β t n U ∂piH N n
      = ∫ U, curS z A.X U * curS w B.X U * wt N β t n U ∂piH N n := hi
  linarith

/-- **The page charge**: over any set of sites the current square of the sum is the sum of the current squares.
For `U(1)` the sum over a whole page is `0` identically. DERIVED: `2` the square. -/
theorem page_charge (hn : 2 ≤ n) (s : Finset (St n)) (A : Su N) (a₀ : SUN.SU N)
    (h : (a₀ : Mat N) * A.X * star (a₀ : Mat N) = -A.X) (β t : ℝ) :
    ∫ U, (∑ z ∈ s, curS z A.X U) ^ 2 * wt N β t n U ∂piH N n
      = ∑ z ∈ s, ∫ U, curS z A.X U ^ 2 * wt N β t n U ∂piH N n := by
  have hw := continuous_wt (N := N) (n := n) β t
  have e : ∀ U : Lk n → SUN.SU N, (∑ z ∈ s, curS z A.X U) ^ 2 * wt N β t n U
      = ∑ z ∈ s, ∑ w ∈ s, curS z A.X U * curS w A.X U * wt N β t n U := fun U => by
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_mul _ _ _
  simp only [e]
  have ha : ∫ U, ∑ z ∈ s, ∑ w ∈ s, curS z A.X U * curS w A.X U * wt N β t n U ∂piH N n
      = ∑ z ∈ s, ∫ U, ∑ w ∈ s, curS z A.X U * curS w A.X U * wt N β t n U ∂piH N n :=
    integral_finsetSum _ fun z _ => integrable_of_cont
      (f := fun U => ∑ w ∈ s, curS z A.X U * curS w A.X U * wt N β t n U)
      (continuous_finsetSum _ fun w _ => ((continuous_curS z _).mul (continuous_curS w _)).mul hw)
  rw [ha]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hb : ∫ U, ∑ w ∈ s, curS z A.X U * curS w A.X U * wt N β t n U ∂piH N n
      = ∑ w ∈ s, ∫ U, curS z A.X U * curS w A.X U * wt N β t n U ∂piH N n :=
    integral_finsetSum _ fun w _ => integrable_of_cont
      (f := fun U => curS z A.X U * curS w A.X U * wt N β t n U)
      (((continuous_curS z _).mul (continuous_curS w _)).mul hw)
  rw [hb, Finset.sum_eq_single z (fun w _ hwz => cross_zero hn hwz A A a₀ h β t)
    (fun hz' => absurd hz hz')]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  show curS z A.X U * curS z A.X U * wt N β t n U = curS z A.X U ^ 2 * wt N β t n U
  ring

/-- In a commutative ring no invertible element flips `X` unless `2 X = 0`: the flip of `cross_zero` does not exist
for `U(1)`. DERIVED: `2` the two sides of the flip. -/
theorem flip_comm {R : Type*} [CommRing R] {a b X : R} (hab : a * b = 1) (h : a * X * b = -X) :
    2 * X = 0 := by
  have : a * X * b = X := by
    rw [mul_right_comm, hab, one_mul]
  rw [this] at h
  linear_combination h

/-! ## 7. The Schwinger–Dyson identity of one link -/

/-- Left translation of one link along `exp(sX)`. No numeral. -/
noncomputable def linkFlow (l : Lk n) (A : Su N) (s : ℝ) (U : Lk n → SUN.SU N) : Lk n → SUN.SU N :=
  fun m => if m = l then E A s * U m else U m

theorem isFlow_linkFlow (l : Lk n) (A : Su N) : IsFlow (piH N n) (linkFlow l A) where
  zero U := by
    funext m
    unfold linkFlow
    split_ifs
    · rw [E_zero, one_mul]
    · rfl
  add s r U := by
    funext m
    unfold linkFlow
    by_cases h : m = l
    · simp only [if_pos h, E_add, mul_assoc]
    · simp only [if_neg h]
  cont s := by
    refine continuous_pi fun m => ?_
    unfold linkFlow
    by_cases h : m = l
    · simp only [if_pos h]
      exact continuous_const.mul (continuous_apply m)
    · simp only [if_neg h]
      exact continuous_apply m
  pres s F hF := by
    refine integral_linkwise (fun _ => n) (fun m u => if m = l then E A s * u else u) (fun m => ?_) F hF
    by_cases h : m = l
    · simp only [if_pos h]
      exact measurePreserving_mul_left (probHaar (SUN.SU N)) _
    · simp only [if_neg h]
      exact MeasurePreserving.id _

section Curve

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hd_fwd (p : Prop) [Decidable p] (X M : 𝔸) :
    HasDerivAt (fun s : ℝ => if p then NormedSpace.exp (s • X) * M else M) (if p then X * M else 0) 0 := by
  by_cases h : p
  · simp only [if_pos h]
    have h0 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h0
    exact h0.mul_const M
  · simp only [if_neg h]
    exact hasDerivAt_const _ _

theorem hd_bwd (p : Prop) [Decidable p] (X M : 𝔸) :
    HasDerivAt (fun s : ℝ => if p then M * NormedSpace.exp (s • (-X)) else M)
      (if p then -(M * X) else 0) 0 := by
  by_cases h : p
  · simp only [if_pos h]
    have h0 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h0
    exact (h0.const_mul M).congr_deriv (mul_neg _ _)
  · simp only [if_neg h]
    exact hasDerivAt_const _ _

theorem hd_fwd0 (p : Prop) [Decidable p] (X M : 𝔸) :
    (fun s : ℝ => if p then NormedSpace.exp (s • X) * M else M) 0 = M := by
  by_cases h : p <;> simp [h]

theorem hd_bwd0 (p : Prop) [Decidable p] (X M : 𝔸) :
    (fun s : ℝ => if p then M * NormedSpace.exp (s • (-X)) else M) 0 = M := by
  by_cases h : p <;> simp [h]

theorem hd_four {a b c d : ℝ → 𝔸} {a' b' c' d' A B C D : 𝔸} (ha : HasDerivAt a a' 0)
    (hb : HasDerivAt b b' 0) (hc : HasDerivAt c c' 0) (hd : HasDerivAt d d' 0)
    (h0a : a 0 = A) (h0b : b 0 = B) (h0c : c 0 = C) (h0d : d 0 = D) :
    HasDerivAt (fun s => a s * b s * c s * d s)
      (a' * B * C * D + A * b' * C * D + A * B * c' * D + A * B * C * d') 0 := by
  subst h0a h0b h0c h0d
  have h := ((ha.mul hb).mul hc).mul hd
  refine HasDerivAt.congr_deriv h ?_
  simp only [Pi.mul_apply]
  noncomm_ring

end Curve

/-- The link in matrix form. No numeral. -/
def lk (U : Lk n → SUN.SU N) (m : Lk n) : Mat N := ((U m : SUN.SU N) : Mat N)

/-- The inverse link in matrix form. No numeral. -/
def lki (U : Lk n → SUN.SU N) (m : Lk n) : Mat N := (((U m)⁻¹ : SUN.SU N) : Mat N)

/-- The derivative of the link `m` along the flow of `l`. No numeral. -/
noncomputable def dLk (l : Lk n) (A : Su N) (U : Lk n → SUN.SU N) (m : Lk n) : Mat N :=
  if m = l then A.X * lk U m else 0

/-- The derivative of the inverse link `m` along the flow of `l`. No numeral. -/
noncomputable def dLi (l : Lk n) (A : Su N) (U : Lk n → SUN.SU N) (m : Lk n) : Mat N :=
  if m = l then -(lki U m * A.X) else 0

theorem coe_link (l : Lk n) (A : Su N) (s : ℝ) (U : Lk n → SUN.SU N) (m : Lk n) :
    ((linkFlow l A s U m : SUN.SU N) : Mat N)
      = if m = l then NormedSpace.exp (s • A.X) * lk U m else lk U m := by
  unfold linkFlow
  split_ifs <;> rfl

theorem coe_E_inv (A : Su N) (s : ℝ) :
    (((E A s)⁻¹ : SUN.SU N) : Mat N) = NormedSpace.exp (s • (-A.X)) := by
  show star (NormedSpace.exp (s • A.X)) = _
  rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, A.skew,
    star_trivial]

theorem coe_link_inv (l : Lk n) (A : Su N) (s : ℝ) (U : Lk n → SUN.SU N) (m : Lk n) :
    (((linkFlow l A s U m)⁻¹ : SUN.SU N) : Mat N)
      = if m = l then lki U m * NormedSpace.exp (s • (-A.X)) else lki U m := by
  unfold linkFlow
  by_cases h : m = l
  · simp only [if_pos h]
    rw [mul_inv_rev]
    show (((U m)⁻¹ : SUN.SU N) : Mat N) * (((E A s)⁻¹ : SUN.SU N) : Mat N) = _
    rw [coe_E_inv]
    rfl
  · simp only [if_neg h]
    rfl

section LinkDeriv

open scoped Matrix.Norms.Operator

attribute [local instance] completeMat

theorem hd_rt4 (l : Lk n) (A : Su N) (U : Lk n → SUN.SU N) (m₁ m₂ m₃ m₄ : Lk n) :
    HasDerivAt (fun s : ℝ => rt ((if m₁ = l then NormedSpace.exp (s • A.X) * lk U m₁ else lk U m₁)
        * (if m₂ = l then NormedSpace.exp (s • A.X) * lk U m₂ else lk U m₂)
        * (if m₃ = l then lki U m₃ * NormedSpace.exp (s • (-A.X)) else lki U m₃)
        * (if m₄ = l then lki U m₄ * NormedSpace.exp (s • (-A.X)) else lki U m₄)))
      (rt (dLk l A U m₁ * lk U m₂ * lki U m₃ * lki U m₄ + lk U m₁ * dLk l A U m₂ * lki U m₃ * lki U m₄
        + lk U m₁ * lk U m₂ * dLi l A U m₃ * lki U m₄ + lk U m₁ * lk U m₂ * lki U m₃ * dLi l A U m₄)) 0 := by
  have h := hd_four (hd_fwd (m₁ = l) A.X (lk U m₁)) (hd_fwd (m₂ = l) A.X (lk U m₂))
    (hd_bwd (m₃ = l) A.X (lki U m₃)) (hd_bwd (m₄ = l) A.X (lki U m₄))
    (hd_fwd0 _ _ _) (hd_fwd0 _ _ _) (hd_bwd0 _ _ _) (hd_bwd0 _ _ _)
  have h2 := (rtL (N := N)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact h2

end LinkDeriv

/-- **The derivative of a plaquette density along the flow of one link.** DERIVED: `1/N` the Wilson normalization. -/
noncomputable def dplaq (l : Lk n) (A : Su N) (q : Pq n) (U : Lk n → SUN.SU N) : ℝ :=
  -(1 / (N : ℝ)) * rt (
    dLk l A U (q.1.1, q.2) * lk U (q.1.2, rshift (fun _ => n) q.1.1 q.2)
        * lki U (q.1.1, rshift (fun _ => n) q.1.2 q.2) * lki U (q.1.2, q.2)
      + lk U (q.1.1, q.2) * dLk l A U (q.1.2, rshift (fun _ => n) q.1.1 q.2)
        * lki U (q.1.1, rshift (fun _ => n) q.1.2 q.2) * lki U (q.1.2, q.2)
      + lk U (q.1.1, q.2) * lk U (q.1.2, rshift (fun _ => n) q.1.1 q.2)
        * dLi l A U (q.1.1, rshift (fun _ => n) q.1.2 q.2) * lki U (q.1.2, q.2)
      + lk U (q.1.1, q.2) * lk U (q.1.2, rshift (fun _ => n) q.1.1 q.2)
        * lki U (q.1.1, rshift (fun _ => n) q.1.2 q.2) * dLi l A U (q.1.2, q.2))

theorem continuous_lk (m : Lk n) : Continuous fun U : Lk n → SUN.SU N => lk U m :=
  continuous_subtype_val.comp (continuous_apply m)

theorem continuous_lki (m : Lk n) : Continuous fun U : Lk n → SUN.SU N => lki U m :=
  continuous_subtype_val.comp (continuous_apply m).inv

theorem continuous_dLk (l : Lk n) (A : Su N) (m : Lk n) :
    Continuous fun U : Lk n → SUN.SU N => dLk l A U m := by
  unfold dLk
  split_ifs
  · exact continuous_const.matrix_mul (continuous_lk m)
  · exact continuous_const

theorem continuous_dLi (l : Lk n) (A : Su N) (m : Lk n) :
    Continuous fun U : Lk n → SUN.SU N => dLi l A U m := by
  unfold dLi
  split_ifs
  · exact ((continuous_lki m).matrix_mul continuous_const).neg
  · exact continuous_const

theorem continuous_dplaq (l : Lk n) (A : Su N) (q : Pq n) :
    Continuous (dplaq (N := N) l A q) := by
  unfold dplaq
  refine continuous_const.mul (continuous_rt.comp ?_)
  have m4 : ∀ {f g h k : (Lk n → SUN.SU N) → Mat N}, Continuous f → Continuous g → Continuous h →
      Continuous k → Continuous fun U => f U * g U * h U * k U := fun h1 h2 h3 h4 =>
    ((h1.matrix_mul h2).matrix_mul h3).matrix_mul h4
  exact ((m4 (continuous_dLk _ _ _) (continuous_lk _) (continuous_lki _) (continuous_lki _)).add
    (m4 (continuous_lk _) (continuous_dLk _ _ _) (continuous_lki _) (continuous_lki _))).add
    (m4 (continuous_lk _) (continuous_lk _) (continuous_dLi _ _ _) (continuous_lki _)) |>.add
    (m4 (continuous_lk _) (continuous_lk _) (continuous_lki _) (continuous_dLi _ _ _))

/-- **Every plaquette density has a generator along the flow of one link.** DERIVED: `1` the Wilson normalization. -/
theorem isGen_link_plaq (l : Lk n) (A : Su N) (q : Pq n) :
    IsGen (linkFlow l A) (plaq N n q) (dplaq l A q) := by
  refine ⟨continuous_dplaq l A q, fun U => ?_⟩
  obtain ⟨⟨i, j⟩, x⟩ := q
  have e : (fun s => plaq N n ((i, j), x) (linkFlow l A s U))
      = fun s : ℝ => 1 - (1 / (N : ℝ)) * rt (
        (if (i, x) = l then NormedSpace.exp (s • A.X) * lk U (i, x) else lk U (i, x))
        * (if (j, rshift (fun _ => n) i x) = l then NormedSpace.exp (s • A.X) * lk U (j, rshift (fun _ => n) i x)
            else lk U (j, rshift (fun _ => n) i x))
        * (if (i, rshift (fun _ => n) j x) = l then lki U (i, rshift (fun _ => n) j x) * NormedSpace.exp (s • (-A.X))
            else lki U (i, rshift (fun _ => n) j x))
        * (if (j, x) = l then lki U (j, x) * NormedSpace.exp (s • (-A.X)) else lki U (j, x))) := by
    funext s
    unfold plaq
    rw [hol_eq, wilsonDensity_eq]
    simp only [Submonoid.coe_mul, coe_link, coe_link_inv]
  rw [e]
  have h := ((hd_rt4 l A U (i, x) (j, rshift (fun _ => n) i x) (i, rshift (fun _ => n) j x) (j, x)).const_mul
    (1 / (N : ℝ))).const_sub 1
  refine h.congr_deriv ?_
  unfold dplaq
  ring

theorem IsGen.ite_left {Ω : Type*} [TopologicalSpace Ω] {Φ : ℝ → Ω → Ω} {F D : Ω → ℝ} (c : Prop)
    [Decidable c] (h : IsGen Φ F D) :
    IsGen Φ (fun U => if c then F U else 0) fun U => if c then D U else 0 := by
  by_cases hc : c
  · simpa only [if_pos hc] using h
  · simp only [if_neg hc]
    exact IsGen.of_inv fun _ _ => rfl

theorem IsGen.ite_right {Ω : Type*} [TopologicalSpace Ω] {Φ : ℝ → Ω → Ω} {F D : Ω → ℝ} (c : Prop)
    [Decidable c] (h : IsGen Φ F D) :
    IsGen Φ (fun U => if c then 0 else F U) fun U => if c then 0 else D U := by
  by_cases hc : c
  · simp only [if_pos hc]
    exact IsGen.of_inv fun _ _ => rfl
  · simpa only [if_neg hc] using h

/-- The derivative of `S_in` along the flow of one link. DERIVED: `0` the excluded terms. -/
noncomputable def dSin (l : Lk n) (A : Su N) (U : Lk n → SUN.SU N) : ℝ :=
  ∑ q : Pq n, if AnisoTorus.inPlane q.1 then dplaq l A q U else 0

/-- The derivative of `S_mix` along the flow of one link. DERIVED: `0` the excluded terms. -/
noncomputable def dSmix (l : Lk n) (A : Su N) (U : Lk n → SUN.SU N) : ℝ :=
  ∑ q : Pq n, if AnisoTorus.inPlane q.1 then 0 else dplaq l A q U

theorem isGen_sin_link (l : Lk n) (A : Su N) : IsGen (linkFlow l A) (sinR N n) (dSin l A) :=
  IsGen.sum _ fun q _ => IsGen.ite_left _ (isGen_link_plaq l A q)

theorem isGen_smix_link (l : Lk n) (A : Su N) : IsGen (linkFlow l A) (smixR N n) (dSmix l A) :=
  IsGen.sum _ fun q _ => IsGen.ite_right _ (isGen_link_plaq l A q)

/-- **The Schwinger–Dyson identity of one link**, exact at every `β`, `t`, side `n`:
`∫ (DO − O (β DS_in + t DS_mix)) e^{−(β S_in + t S_mix)} = 0`. No numeral. -/
theorem sd_link (l : Lk n) (A : Su N) (β t : ℝ) {O DO : (Lk n → SUN.SU N) → ℝ} (hO : Continuous O)
    (hg : IsGen (linkFlow l A) O DO) :
    ∫ U, (DO U - O U * (β * dSin l A U + t * dSmix l A U)) * wt N β t n U ∂piH N n = 0 :=
  schwingerDyson (isFlow_linkFlow l A) hO (continuous_act β t) hg
    (((isGen_sin_link l A).const_mul β).add ((isGen_smix_link l A).const_mul t))

/-- **The Schwinger–Dyson identity at a plaquette**: `⟨D φ_p⟩` against the two-plaquette correlators through the link.
No numeral. -/
theorem sd_link_plaq (l : Lk n) (A : Su N) (β t : ℝ) (p : Pq n) :
    gib N β t n (dplaq l A p)
      = gib N β t n fun U => plaq N n p U * (β * dSin l A U + t * dSmix l A U) := by
  have hw := continuous_wt (N := N) (n := n) β t
  have h := sd_link l A β t (continuous_plaq n p) (isGen_link_plaq l A p)
  have hc : Continuous fun U : Lk n → SUN.SU N => β * dSin l A U + t * dSmix l A U :=
    (continuous_const.mul (isGen_sin_link l A).1).add (continuous_const.mul (isGen_smix_link l A).1)
  have e : ∫ U, (dplaq l A p U * wt N β t n U
        - plaq N n p U * (β * dSin l A U + t * dSmix l A U) * wt N β t n U) ∂piH N n
      = ∫ U, dplaq l A p U * wt N β t n U ∂piH N n
        - ∫ U, plaq N n p U * (β * dSin l A U + t * dSmix l A U) * wt N β t n U ∂piH N n :=
    int_sub ((continuous_dplaq l A p).mul hw) (((continuous_plaq n p).mul hc).mul hw)
  have h2 : ∫ U, (dplaq l A p U * wt N β t n U
        - plaq N n p U * (β * dSin l A U + t * dSmix l A U) * wt N β t n U) ∂piH N n = 0 := by
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    show _ = (dplaq l A p U - plaq N n p U * (β * dSin l A U + t * dSmix l A U)) * wt N β t n U
    ring
  rw [e] at h2
  unfold gib
  rw [sub_eq_zero.mp h2]

/-! ## 8. A family at every `N` -/

section Family

/-- The matrix unit. DERIVED: `1` the entry. -/
noncomputable def eU (i j : Fin N) : Mat N := Matrix.single i j 1

theorem eU_mul_same (i j k : Fin N) : eU (N := N) i j * eU j k = eU i k := by
  unfold eU
  rw [Matrix.single_mul_single_same, one_mul]

theorem eU_mul_ne (i j k l : Fin N) (h : j ≠ k) : eU (N := N) i j * eU k l = 0 :=
  Matrix.single_mul_single_of_ne 1 i j k h 1

/-- The real off-diagonal generator. DERIVED: `1/2` the normalization of the pair. -/
noncomputable def genA (i j : Fin N) (h : i ≠ j) : Su N where
  X := (1 / 2 : ℂ) • (eU i j - eU j i)
  skew := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub]
    unfold eU
    rw [Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, ← smul_neg, neg_sub]
    congr 1
    simp
  tr := by
    rw [Matrix.trace_smul, Matrix.trace_sub]
    unfold eU
    rw [Matrix.trace_single_eq_of_ne _ _ _ h, Matrix.trace_single_eq_of_ne _ _ _ h.symm]
    simp

/-- The imaginary off-diagonal generator. DERIVED: `1/2` the normalization of the pair. -/
noncomputable def genB (i j : Fin N) (h : i ≠ j) : Su N where
  X := (Complex.I / 2) • (eU i j + eU j i)
  skew := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add]
    unfold eU
    rw [Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, add_comm, ← neg_smul]
    congr 1
    simp [Complex.star_def, neg_div]
  tr := by
    rw [Matrix.trace_smul, Matrix.trace_add]
    unfold eU
    rw [Matrix.trace_single_eq_of_ne _ _ _ h, Matrix.trace_single_eq_of_ne _ _ _ h.symm]
    simp

theorem genA_sq {i j : Fin N} (h : i ≠ j) :
    (genA i j h).X * (genA i j h).X = -((1 / 4 : ℂ) • (eU i i + eU j j)) := by
  show ((1 / 2 : ℂ) • (eU i j - eU j i)) * ((1 / 2 : ℂ) • (eU i j - eU j i)) = _
  have hD : (eU i j - eU j i) * (eU i j - eU j i) = -(eU i i + eU j j) := by
    rw [sub_mul, mul_sub, mul_sub, eU_mul_ne i j i j h.symm, eU_mul_same, eU_mul_same,
      eU_mul_ne j i j i h]
    abel
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hD, smul_neg]
  congr 2
  norm_num

theorem genB_sq {i j : Fin N} (h : i ≠ j) :
    (genB i j h).X * (genB i j h).X = -((1 / 4 : ℂ) • (eU i i + eU j j)) := by
  show ((Complex.I / 2) • (eU i j + eU j i)) * ((Complex.I / 2) • (eU i j + eU j i)) = _
  have hD : (eU i j + eU j i) * (eU i j + eU j i) = eU i i + eU j j := by
    rw [add_mul, mul_add, mul_add, eU_mul_ne i j i j h.symm, eU_mul_same, eU_mul_same,
      eU_mul_ne j i j i h]
    abel
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hD, ← neg_smul]
  congr 1
  have : (Complex.I / 2) * (Complex.I / 2) = (Complex.I * Complex.I) / 4 := by ring
  rw [this, Complex.I_mul_I]
  ring

/-- The zero of `su(N)`. No numeral. -/
noncomputable def zeroSu : Su N := ⟨0, by simp, by simp⟩

/-- The off-diagonal family, each pair counted in both orders, the Cartan directions left out. It need not be a
basis: `CasFam` asks only that the squares sum to a scalar. DERIVED: `0` on the diagonal. -/
noncomputable def offEl (p : Fin N × Fin N × Bool) : Su N :=
  if h : p.1 ≠ p.2.1 then (if p.2.2 then genB p.1 p.2.1 h else genA p.1 p.2.1 h) else zeroSu

theorem offEl_pair (i j : Fin N) :
    ∑ b : Bool, (offEl (i, j, b)).X * (offEl (i, j, b)).X
      = if i ≠ j then -((1 / 2 : ℂ) • (eU i i + eU j j)) else 0 := by
  by_cases h : i = j
  · subst h
    simp [offEl, zeroSu]
  · have h' : i ≠ j := h
    rw [if_pos h', Fintype.sum_bool]
    simp only [offEl, dif_pos h', if_true, Bool.false_eq_true, if_false]
    rw [genB_sq h', genA_sq h', ← neg_add, ← add_smul]
    congr 2
    norm_num

theorem sum_ne (i : Fin N) (M : Mat N) :
    ∑ j, (if i ≠ j then M else 0) = (N : ℂ) • M - M := by
  have e : ∀ j, (if i ≠ j then M else 0) = M - (if i = j then M else 0) := fun j => by
    by_cases h : i = j <;> simp [h]
  simp only [e]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq]
  simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]

/-- DERIVED: `2`, `1/2`, as in the pair; `1` the unit. -/
theorem sum_offDiag :
    ∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then -((1 / 2 : ℂ) • (eU i i + eU j j)) else 0)
      = -((((N : ℝ) - 1 : ℝ) : ℂ) • (1 : Mat N)) := by
  set T : Mat N := ∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then eU i i else 0) with hT
  have h1 : T = (N : ℂ) • (1 : Mat N) - 1 := by
    rw [hT]
    simp only [sum_ne]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
    have : ∑ i : Fin N, eU (N := N) i i = 1 := Matrix.sum_single_one
    rw [this]
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (if i ≠ j then eU j j else 0) = T := by
    rw [hT, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  have h3 : ∀ i j : Fin N, (if i ≠ j then -((1 / 2 : ℂ) • (eU i i + eU j j)) else 0)
      = -((1 / 2 : ℂ) • ((if i ≠ j then eU i i else 0) + (if i ≠ j then eU j j else 0))) := fun i j => by
    by_cases h : i = j <;> simp [h]
  have h4 : ∀ a b : Fin N → Fin N → Mat N,
      ∑ i, ∑ j, -((1 / 2 : ℂ) • (a i j + b i j))
        = -((1 / 2 : ℂ) • ((∑ i, ∑ j, a i j) + ∑ i, ∑ j, b i j)) := fun a b => by
    simp only [Finset.sum_neg_distrib, ← Finset.smul_sum, Finset.sum_add_distrib]
  have h5 : (1 / 2 : ℂ) • (T + T) = T := by
    rw [← two_smul ℂ T, smul_smul]
    norm_num
  simp only [h3]
  rw [h4, h2, ← hT, h5, h1]
  congr 1
  push_cast
  rw [sub_smul, one_smul]

/-- **The off-diagonal family**: `c = N − 1`. DERIVED: `1` the unit. -/
noncomputable def offDiag (N : ℕ) : CasFam N (Fin N × Fin N × Bool) where
  el := offEl
  c := (N : ℝ) - 1
  sq := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type (f := fun q : Fin N × Bool => _)]
    simp only [offEl_pair]
    exact sum_offDiag

/-- The doubling combination at every `N ≥ 2`, with no hypothesis on a family. DERIVED: `2` the least `N`, as in
`mixCut_eq_current`; `16 = 2⁴` the copies of the doubling, as in `mixCut_eq_current`. -/
theorem mixCut_eq_offDiag (hN : 2 ≤ N) (β t : ℝ) {w : ℕ} (hw : 1 ≤ w) :
    mixCut N β t w = t / (4 * ((N : ℝ) - 1))
      * (16 * curG (offDiag N) β t (2 ^ w) - curG (offDiag N) β t (2 ^ (w + 1))) := by
  have h : ((N : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  exact mixCut_eq_current (offDiag N) h β t hw

/-- The diagonal flip of the pair `(i, j)`. DERIVED: `1` off the pair. -/
noncomputable def dEl (i j k : Fin N) : ℂ :=
  if k = i then Complex.I else if k = j then -Complex.I else 1

theorem dEl_mul_star (i j k : Fin N) : dEl i j k * star (dEl i j k) = 1 := by
  unfold dEl
  split_ifs <;> simp [Complex.star_def]

/-- `diag(i, −i, 1, …)`, an element of `SU(N)`. No numeral. -/
noncomputable def flipEl (i j : Fin N) (h : i ≠ j) : SUN.SU N :=
  ⟨Matrix.diagonal (dEl i j), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      exact dEl_mul_star i j k
    · rw [Matrix.det_diagonal, Fintype.prod_eq_mul i j h fun x hx => by
        unfold dEl; rw [if_neg hx.1, if_neg hx.2]]
      unfold dEl
      rw [if_pos rfl, if_neg h.symm, if_pos rfl]
      simp⟩

/-- A matrix supported on the pair `(i, j)` is flipped. DERIVED: `0` off the pair. -/
theorem flip_of_support {i j : Fin N} (h : i ≠ j) (M : Mat N)
    (hs : ∀ k l, ¬ (k = i ∧ l = j) → ¬ (k = j ∧ l = i) → M k l = 0) :
    ((flipEl i j h : SUN.SU N) : Mat N) * M * star ((flipEl i j h : SUN.SU N) : Mat N) = -M := by
  show Matrix.diagonal (dEl i j) * M * star (Matrix.diagonal (dEl i j)) = -M
  ext k l
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.neg_apply]
  by_cases h1 : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [Pi.star_apply, dEl, if_true, if_neg h.symm]
    simp only [Complex.star_def, map_neg, Complex.conj_I, neg_neg]
    linear_combination (M k l) * Complex.I_mul_I
  · by_cases h2 : k = j ∧ l = i
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [Pi.star_apply, dEl, if_true, if_neg h.symm]
      simp only [Complex.star_def, Complex.conj_I]
      linear_combination (M k l) * Complex.I_mul_I
    · rw [hs k l h1 h2]
      simp

theorem offEl_support (p : Fin N × Fin N × Bool) (k l : Fin N)
    (h1 : ¬ (k = p.1 ∧ l = p.2.1)) (h2 : ¬ (k = p.2.1 ∧ l = p.1)) : (offEl p).X k l = 0 := by
  obtain ⟨i, j, b⟩ := p
  have a1 : eU (N := N) i j k l = 0 := by
    unfold eU
    rw [Matrix.single_apply, if_neg fun h => h1 ⟨h.1.symm, h.2.symm⟩]
  have a2 : eU (N := N) j i k l = 0 := by
    unfold eU
    rw [Matrix.single_apply, if_neg fun h => h2 ⟨h.1.symm, h.2.symm⟩]
  unfold offEl
  by_cases h : i = j
  · simp [h, zeroSu]
  · have h' : i ≠ j := h
    simp only [dif_pos h']
    cases b
    · show ((1 / 2 : ℂ) • (eU i j - eU j i)) k l = 0
      rw [Matrix.smul_apply, Matrix.sub_apply, a1, a2]
      simp
    · show ((Complex.I / 2) • (eU i j + eU j i)) k l = 0
      rw [Matrix.smul_apply, Matrix.add_apply, a1, a2]
      simp

/-- **The colour Ward identity for the family**, at every `N`. No numeral. -/
theorem cross_zero_off (hn : 2 ≤ n) {z w : St n} (hzw : w ≠ z) (p : Fin N × Fin N × Bool)
    (hp : p.1 ≠ p.2.1) (B : Su N) (β t : ℝ) :
    ∫ U, curS z (offEl p).X U * curS w B.X U * wt N β t n U ∂piH N n = 0 :=
  cross_zero hn hzw (offEl p) B (flipEl p.1 p.2.1 hp)
    (flip_of_support hp _ fun k l h1 h2 => offEl_support p k l h1 h2) β t

/-- **The page charge for the family.** DERIVED: `2` the square. -/
theorem page_charge_off (hn : 2 ≤ n) (s : Finset (St n)) (p : Fin N × Fin N × Bool) (hp : p.1 ≠ p.2.1)
    (β t : ℝ) :
    ∫ U, (∑ z ∈ s, curS z (offEl p).X U) ^ 2 * wt N β t n U ∂piH N n
      = ∑ z ∈ s, ∫ U, curS z (offEl p).X U ^ 2 * wt N β t n U ∂piH N n :=
  page_charge hn s (offEl p) (flipEl p.1 p.2.1 hp)
    (flip_of_support hp _ fun k l h1 h2 => offEl_support p k l h1 h2) β t

end Family

/-! ## 9. Route 2 on one generator: the integrated Bochner identity and its Hessian term -/

/-- **The Hessian term is local**: with `J = Y S_mix`, `K = Y J`, `L = Y K`,
`t ⟨K J²⟩ = ⟨K²⟩ + ⟨J L⟩`. The term `t Hess S(∇f, ∇f)` of the Bochner identity at `f = S_mix` is a local expectation by
Schwinger–Dyson: keeping it adds nothing to Route 1. DERIVED: `2` the square. -/
theorem hess_local (hn : 2 ≤ n) (z : St n) (A : Su N) (β t : ℝ) :
    t * ∫ U, curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U ∂piH N n
      = (∫ U, curS z (A.X * A.X) U ^ 2 * wt N β t n U ∂piH N n)
        + ∫ U, curS z A.X U * curS z (A.X * A.X * A.X) U * wt N β t n U ∂piH N n := by
  have hw := continuous_wt (N := N) (n := n) β t
  have hJ := continuous_curS (N := N) z A.X
  have hK := continuous_curS (N := N) z (A.X * A.X)
  have hL := continuous_curS (N := N) z (A.X * A.X * A.X)
  have hg := IsGen.mul (isFlow_pageFlow z A).zero hK hJ (isGen_curS hn z A (A.X * A.X))
    (isGen_curS hn z A A.X)
  have h : ∫ U, (curS z (A.X * A.X * A.X) U * curS z A.X U
        + curS z (A.X * A.X) U * curS z (A.X * A.X) U
        - t * (curS z (A.X * A.X) U * curS z A.X U * curS z A.X U)) * wt N β t n U ∂piH N n = 0 :=
    sd_page hn z A β t (hK.mul hJ) hg
  have e : ∀ U, (curS z (A.X * A.X * A.X) U * curS z A.X U
        + curS z (A.X * A.X) U * curS z (A.X * A.X) U
        - t * (curS z (A.X * A.X) U * curS z A.X U * curS z A.X U)) * wt N β t n U
      = (curS z (A.X * A.X) U ^ 2 * wt N β t n U
          + curS z A.X U * curS z (A.X * A.X * A.X) U * wt N β t n U)
        - t * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U) := fun U => by ring
  simp only [e] at h
  have h1 : ∫ U, ((curS z (A.X * A.X) U ^ 2 * wt N β t n U
          + curS z A.X U * curS z (A.X * A.X * A.X) U * wt N β t n U)
        - t * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U)) ∂piH N n
      = ∫ U, (curS z (A.X * A.X) U ^ 2 * wt N β t n U
          + curS z A.X U * curS z (A.X * A.X * A.X) U * wt N β t n U) ∂piH N n
        - ∫ U, t * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U) ∂piH N n :=
    int_sub (((hK.pow 2).mul hw).add ((hJ.mul hL).mul hw))
      (continuous_const.mul ((hK.mul (hJ.pow 2)).mul hw))
  have h2 : ∫ U, (curS z (A.X * A.X) U ^ 2 * wt N β t n U
          + curS z A.X U * curS z (A.X * A.X * A.X) U * wt N β t n U) ∂piH N n
      = ∫ U, curS z (A.X * A.X) U ^ 2 * wt N β t n U ∂piH N n
        + ∫ U, curS z A.X U * curS z (A.X * A.X * A.X) U * wt N β t n U ∂piH N n :=
    integral_add (integrable_of_cont ((hK.pow 2).mul hw)) (integrable_of_cont ((hJ.mul hL).mul hw))
  rw [h1, h2, integral_const_mul] at h
  linarith

/-- **The integrated Bochner identity in the frame form, on one generator**:
`⟨(Y² f − t (Y f)²)²⟩ = ⟨(Y² f)²⟩ + t ⟨Y² S · (Y f)²⟩` at `f = S_mix`, the identity of the module docstring's Route 2 for
the generator of the layer rotation. No curvature appears, and no `β`. DERIVED: `2` the square; `3` the Leibniz rule on
`J³`; `4` the power `J⁴`. -/
theorem bochner_frame (hn : 2 ≤ n) (z : St n) (A : Su N) (β t : ℝ) :
    ∫ U, (curS z (A.X * A.X) U - t * curS z A.X U ^ 2) ^ 2 * wt N β t n U ∂piH N n
      = (∫ U, curS z (A.X * A.X) U ^ 2 * wt N β t n U ∂piH N n)
        + t * ∫ U, curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U ∂piH N n := by
  have hw := continuous_wt (N := N) (n := n) β t
  have hJ := continuous_curS (N := N) z A.X
  have hK := continuous_curS (N := N) z (A.X * A.X)
  have hzero := (isFlow_pageFlow (N := N) z A).zero
  have gJ := isGen_curS hn z A A.X
  have g2 := IsGen.mul hzero hJ hJ gJ gJ
  have g3 := IsGen.mul hzero (hJ.mul hJ) hJ g2 gJ
  have h3 : ∫ U, ((curS z (A.X * A.X) U * curS z A.X U + curS z A.X U * curS z (A.X * A.X) U) * curS z A.X U
        + curS z A.X U * curS z A.X U * curS z (A.X * A.X) U
        - t * (curS z A.X U * curS z A.X U * curS z A.X U * curS z A.X U)) * wt N β t n U ∂piH N n = 0 :=
    sd_page hn z A β t ((hJ.mul hJ).mul hJ) g3
  have e3 : ∀ U, ((curS z (A.X * A.X) U * curS z A.X U + curS z A.X U * curS z (A.X * A.X) U) * curS z A.X U
        + curS z A.X U * curS z A.X U * curS z (A.X * A.X) U
        - t * (curS z A.X U * curS z A.X U * curS z A.X U * curS z A.X U)) * wt N β t n U
      = 3 * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U)
        - t * (curS z A.X U ^ 4 * wt N β t n U) := fun U => by ring
  simp only [e3] at h3
  have hA := (hK.mul (hJ.pow 2)).mul hw
  have hB := (hJ.pow 4).mul hw
  have hQ := (hK.pow 2).mul hw
  have h4 : ∫ U, (3 * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U)
        - t * (curS z A.X U ^ 4 * wt N β t n U)) ∂piH N n
      = ∫ U, 3 * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U) ∂piH N n
        - ∫ U, t * (curS z A.X U ^ 4 * wt N β t n U) ∂piH N n :=
    int_sub (continuous_const.mul hA) (continuous_const.mul hB)
  rw [h4, integral_const_mul, integral_const_mul] at h3
  have e : ∀ U, (curS z (A.X * A.X) U - t * curS z A.X U ^ 2) ^ 2 * wt N β t n U
      = (curS z (A.X * A.X) U ^ 2 * wt N β t n U
          - (2 * t) * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U))
        + t ^ 2 * (curS z A.X U ^ 4 * wt N β t n U) := fun U => by ring
  simp only [e]
  have h5 : ∫ U, ((curS z (A.X * A.X) U ^ 2 * wt N β t n U
          - (2 * t) * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U))
        + t ^ 2 * (curS z A.X U ^ 4 * wt N β t n U)) ∂piH N n
      = ∫ U, (curS z (A.X * A.X) U ^ 2 * wt N β t n U
          - (2 * t) * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U)) ∂piH N n
        + ∫ U, t ^ 2 * (curS z A.X U ^ 4 * wt N β t n U) ∂piH N n :=
    integral_add (integrable_of_cont (hQ.sub (continuous_const.mul hA)))
      (integrable_of_cont (continuous_const.mul hB))
  have h6 : ∫ U, (curS z (A.X * A.X) U ^ 2 * wt N β t n U
          - (2 * t) * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U)) ∂piH N n
      = ∫ U, curS z (A.X * A.X) U ^ 2 * wt N β t n U ∂piH N n
        - ∫ U, (2 * t) * (curS z (A.X * A.X) U * curS z A.X U ^ 2 * wt N β t n U) ∂piH N n :=
    int_sub hQ (continuous_const.mul hA)
  rw [h5, h6, integral_const_mul, integral_const_mul]
  linear_combination (-t) * h3

end MassGap.ExactIneq

#print axioms MassGap.ExactIneq.IsGen.of_inv
#print axioms MassGap.ExactIneq.IsGen.add
#print axioms MassGap.ExactIneq.IsGen.const_mul
#print axioms MassGap.ExactIneq.IsGen.sum
#print axioms MassGap.ExactIneq.IsGen.mul
#print axioms MassGap.ExactIneq.IsGen.hasDerivAt_at
#print axioms MassGap.ExactIneq.integral_gen_eq_zero
#print axioms MassGap.ExactIneq.schwingerDyson
#print axioms MassGap.ExactIneq.continuous_rt
#print axioms MassGap.ExactIneq.rt_add
#print axioms MassGap.ExactIneq.rt_sum
#print axioms MassGap.ExactIneq.rt_real_smul
#print axioms MassGap.ExactIneq.wilsonDensity_eq
#print axioms MassGap.ExactIneq.det_exp_eq_one
#print axioms MassGap.ExactIneq.exp_mem
#print axioms MassGap.ExactIneq.coe_E
#print axioms MassGap.ExactIneq.E_zero
#print axioms MassGap.ExactIneq.E_add
#print axioms MassGap.ExactIneq.completeMat
#print axioms MassGap.ExactIneq.hasDerivAt_rt_E
#print axioms MassGap.ExactIneq.hasDerivAt_rt_E_left
#print axioms MassGap.ExactIneq.hasDerivAt_rt_mul_E
#print axioms MassGap.ExactIneq.gT_comp
#print axioms MassGap.ExactIneq.gT_one
#print axioms MassGap.ExactIneq.continuous_gT
#print axioms MassGap.ExactIneq.isFlow_pageFlow
#print axioms MassGap.ExactIneq.sinR_page
#print axioms MassGap.ExactIneq.continuous_chi
#print axioms MassGap.ExactIneq.ne_ij
#print axioms MassGap.ExactIneq.c1
#print axioms MassGap.ExactIneq.c2
#print axioms MassGap.ExactIneq.c3
#print axioms MassGap.ExactIneq.c4
#print axioms MassGap.ExactIneq.c5
#print axioms MassGap.ExactIneq.c6
#print axioms MassGap.ExactIneq.chi_gT
#print axioms MassGap.ExactIneq.plaq_eq_chi
#print axioms MassGap.ExactIneq.continuous_curP
#print axioms MassGap.ExactIneq.isGen_plaq
#print axioms MassGap.ExactIneq.isGen_curP
#print axioms MassGap.ExactIneq.oA_low
#print axioms MassGap.ExactIneq.oB_high
#print axioms MassGap.ExactIneq.plaq_swap
#print axioms MassGap.ExactIneq.sum_mixedOri
#print axioms MassGap.ExactIneq.smix_eq_sum
#print axioms MassGap.ExactIneq.continuous_curS
#print axioms MassGap.ExactIneq.isGen_smix
#print axioms MassGap.ExactIneq.isGen_curS
#print axioms MassGap.ExactIneq.continuous_act
#print axioms MassGap.ExactIneq.continuous_wt
#print axioms MassGap.ExactIneq.integrable_of_cont
#print axioms MassGap.ExactIneq.int_sub
#print axioms MassGap.ExactIneq.int_sum2
#print axioms MassGap.ExactIneq.sd_page
#print axioms MassGap.ExactIneq.sum_curP
#print axioms MassGap.ExactIneq.sum_corner
#print axioms MassGap.ExactIneq.sum_pull
#print axioms MassGap.ExactIneq.sum_curS
#print axioms MassGap.ExactIneq.za_eq
#print axioms MassGap.ExactIneq.sd_current
#print axioms MassGap.ExactIneq.energy_current
#print axioms MassGap.ExactIneq.mixCut_eq_current
#print axioms MassGap.ExactIneq.curG_nonneg
#print axioms MassGap.ExactIneq.meanMix_le
#print axioms MassGap.ExactIneq.var_current
#print axioms MassGap.ExactIneq.hol_gF
#print axioms MassGap.ExactIneq.gF_gT
#print axioms MassGap.ExactIneq.integral_linkwise
#print axioms MassGap.ExactIneq.integral_gF
#print axioms MassGap.ExactIneq.plaq_gF
#print axioms MassGap.ExactIneq.smix_gF
#print axioms MassGap.ExactIneq.sin_gF
#print axioms MassGap.ExactIneq.wt_gF
#print axioms MassGap.ExactIneq.conj_site_ne
#print axioms MassGap.ExactIneq.conj_site_same
#print axioms MassGap.ExactIneq.cur_gF_ne
#print axioms MassGap.ExactIneq.E_flip
#print axioms MassGap.ExactIneq.cur_gF_flip
#print axioms MassGap.ExactIneq.cross_zero
#print axioms MassGap.ExactIneq.page_charge
#print axioms MassGap.ExactIneq.flip_comm
#print axioms MassGap.ExactIneq.isFlow_linkFlow
#print axioms MassGap.ExactIneq.hd_fwd
#print axioms MassGap.ExactIneq.hd_bwd
#print axioms MassGap.ExactIneq.hd_fwd0
#print axioms MassGap.ExactIneq.hd_bwd0
#print axioms MassGap.ExactIneq.hd_four
#print axioms MassGap.ExactIneq.coe_link
#print axioms MassGap.ExactIneq.coe_E_inv
#print axioms MassGap.ExactIneq.coe_link_inv
#print axioms MassGap.ExactIneq.hd_rt4
#print axioms MassGap.ExactIneq.continuous_lk
#print axioms MassGap.ExactIneq.continuous_lki
#print axioms MassGap.ExactIneq.continuous_dLk
#print axioms MassGap.ExactIneq.continuous_dLi
#print axioms MassGap.ExactIneq.continuous_dplaq
#print axioms MassGap.ExactIneq.isGen_link_plaq
#print axioms MassGap.ExactIneq.IsGen.ite_left
#print axioms MassGap.ExactIneq.IsGen.ite_right
#print axioms MassGap.ExactIneq.isGen_sin_link
#print axioms MassGap.ExactIneq.isGen_smix_link
#print axioms MassGap.ExactIneq.sd_link
#print axioms MassGap.ExactIneq.sd_link_plaq
#print axioms MassGap.ExactIneq.eU_mul_same
#print axioms MassGap.ExactIneq.eU_mul_ne
#print axioms MassGap.ExactIneq.genA_sq
#print axioms MassGap.ExactIneq.genB_sq
#print axioms MassGap.ExactIneq.offEl_pair
#print axioms MassGap.ExactIneq.sum_ne
#print axioms MassGap.ExactIneq.sum_offDiag
#print axioms MassGap.ExactIneq.mixCut_eq_offDiag
#print axioms MassGap.ExactIneq.dEl_mul_star
#print axioms MassGap.ExactIneq.flip_of_support
#print axioms MassGap.ExactIneq.offEl_support
#print axioms MassGap.ExactIneq.cross_zero_off
#print axioms MassGap.ExactIneq.page_charge_off
#print axioms MassGap.ExactIneq.hess_local
#print axioms MassGap.ExactIneq.bochner_frame
