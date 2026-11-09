import Mathlib
import MassGap.ThickSheetCost

/-!
# MassGap.NonCartanTwist — a centre twist off the Cartan directions of `SU(2)` is not cheaper

`ThickSheetCost` bounds below only abelian (Cartan) twist profiles: a section of `m` plaquettes
carrying `diag(e^{iφ_k}, e^{−iφ_k})` with `Σ φ_k = π`. This module bounds every `SU(2)` profile, the
plaquette holonomies `g_1, …, g_m` multiplying to the centre element `−1` in any directions,
commuting or not, and the transported form `Π_k h_k g_k h_k⁻¹ = −1` of a sheet whose plaquettes are
carried to a common base point. The answer is that no such profile is cheaper than a Cartan one.

## The argument

The class angle `angle g = arccos(½ Re tr g) ∈ [0, π]` is the geodesic distance from `1` on
`SU(2) ≅ S³`, and the Wilson density is `1 − cos(angle g)` (`wilsonDensity_eq`). With
`g = [[a, −b̄], [b, ā]]`, `h = [[c, −d̄], [d, c̄]]`,
`½ Re tr(gh) = a₀c₀ − (a₁c₁ + b₀d₀ + b₁d₁)` (`suTau_mul`), and Cauchy–Schwarz on the three
imaginary coordinates gives `½ Re tr(gh) ≥ cos(angle g + angle h)`, hence the triangle inequality
`angle (g h) ≤ angle g + angle h` (`angle_mul_le`). Along the ordered product of a section,
`π = angle(−1) ≤ Σ angle g_k` (`pi_le_sum_angle`). The angle vector then lies in `[0, π]^m` with
total at least `π`; scaling it by `π / Σ angle` gives a Cartan profile of total exactly `π` whose
entries are no larger, and `1 − cos` increases on `[0, π]`, so the Cartan profile costs no more
(`cartan_dominates`).

## What is proved

* `angle_mul_le`, `angle_conj`, `angle_one`, `angle_negOne`: the triangle inequality, class
  invariance and the two end values of the `SU(2)` angle.
* **`su2_profile_dominated`**: every `SU(2)` section multiplying to `−1` is dominated by a Cartan
  section of total `π`, realized by `dmat`, at no greater Wilson cost.
* **`su2_transported_dominated`**: the same for a transported section `Π_k h_k g_k h_k⁻¹ = −1`,
  costed by `Σ φ(g_k)`.
* **`su2_section_ge`**, **`su2_cellCost_ge`**: every `SU(2)` section costs at least `2/m`, every
  coarse cell of `m` such sections at least `2 = 2θ²/π²` at `θ = π`, whatever the directions.
* **`su2_trial_summable`**: above `β = ln 3 / 8` the surface sum at the cell cost of any `SU(2)`
  profile converges, at every `m`.
* `u1_profile_dominated`, `u1_section_ge`, `u1_cellCost_ge`, `u1_trial_summable`: the same for `U(1)`
  phases multiplying to `−1`, through the angle `arccos(Re z)`, where the total phase may be any
  odd multiple of `π`.
* **`su2_u1_same_floor`**: each group's sections of product `−1` are dominated by sections of the
  other at the same Cartan angles; the two groups have the same minimal cost per section and per
  coarse cell at every `m`.

## The answer

No non-Cartan profile is cheaper. The minimal cost of a section, over all `SU(2)` profiles, equals
the minimal cost over Cartan profiles, which equals the `U(1)` minimum, at every `m`. The last
corner `ThickSheetCost` left open is closed negatively for plaquette-holonomy costs: at fixed coupling no classical sheet cost,
abelian or not, separates `SU(2)` from `U(1)`.

DERIVED (module-wide): `π` the angle of the centre element (`arccos(−1)`); `½` the `1/N` of
`wilsonDensity` at `N = 2`; `π / Σ angle` the scaling of the measured angles to the centre total;
`2 = 2θ²/π²` at `θ = π`, `ThickSheetCost.cellCost_ge`'s; `8 = 4 · 2` and `¼ ln 3` inherited from
`ThickSheetCost.trial_summable` and `VortexEntropy`. CHOSEN: none.

## What does not follow

* The exact minimum `min Σ (1 − cos α_k)` over `α ∈ [0, π]^m` with `Σ α_k = π` is not computed; it
  lies in `[2/m, m(1 − cos(π/m))]` (`su2_section_ge`, `ThickSheetCost.uniform_spreadCost_le`). The
  comparison of the groups does not need it: both reduce to the same real problem.
* No link field realizing a section is built; the costs are those of the plaquette holonomies.
* Nothing here is entropy-weighted beyond `VortexEntropy`'s directed family, and nothing bounds
  `vortexR`, `FluxConfinedAt` or the doubling defect. A separation of `SU(2)` from `U(1)` through
  sheets can come only from a coupling that depends on the thickness (the running), or from a
  non-classical (entropic or quantum) effect; within plaquette-holonomy costs at fixed `β`, a classical
  cost cannot supply it.
-/

noncomputable section

namespace MassGap.NonCartanTwist

open Real MassGap.SUN MassGap.ThickSheetCost
open MassGap.SU2DiskLaw (dmat)

/-! ## 1. The cosine triangle step -/

/-- **The cosine form of the triangle step**: if `a² + S = 1`, `c² + T = 1` and `p² ≤ S T`, then
`cos(arccos a + arccos c) ≤ a c − p`. Cited: `Real.cos_add`, `Real.sin_arccos`. -/
theorem cos_add_arccos_le {a c p S T : ℝ} (ha : a ^ 2 + S = 1) (hc : c ^ 2 + T = 1) (hS : 0 ≤ S)
    (hT : 0 ≤ T) (hp : p ^ 2 ≤ S * T) : Real.cos (Real.arccos a + Real.arccos c) ≤ a * c - p := by
  have ha1 : |a| ≤ 1 := (sq_le_one_iff_abs_le_one a).mp (by linarith)
  have hc1 : |c| ≤ 1 := (sq_le_one_iff_abs_le_one c).mp (by linarith)
  rw [Real.cos_add, Real.cos_arccos (abs_le.mp ha1).1 (abs_le.mp ha1).2,
    Real.cos_arccos (abs_le.mp hc1).1 (abs_le.mp hc1).2, Real.sin_arccos, Real.sin_arccos,
    show 1 - a ^ 2 = S by linarith, show 1 - c ^ 2 = T by linarith, ← Real.sqrt_mul hS]
  have hpS : p ≤ √(S * T) :=
    calc p ≤ |p| := le_abs_self p
      _ = √(p ^ 2) := (Real.sqrt_sq_eq_abs p).symm
      _ ≤ √(S * T) := Real.sqrt_le_sqrt hp
  linarith

/-- **The angle triangle step**: `cos(arccos a + arccos c) ≤ z` gives
`arccos z ≤ arccos a + arccos c`. -/
theorem arccos_le_add {a c z : ℝ} (h : Real.cos (Real.arccos a + Real.arccos c) ≤ z) :
    Real.arccos z ≤ Real.arccos a + Real.arccos c := by
  by_cases hs : Real.arccos a + Real.arccos c ≤ π
  · calc Real.arccos z ≤ Real.arccos (Real.cos (Real.arccos a + Real.arccos c)) :=
          Real.arccos_le_arccos h
      _ = Real.arccos a + Real.arccos c :=
          Real.arccos_cos (add_nonneg (Real.arccos_nonneg a) (Real.arccos_nonneg c)) hs
  · exact (Real.arccos_le_pi z).trans (le_of_lt (not_le.mp hs))

/-- **Subadditivity along an ordered product**, in any monoid. -/
theorem angle_prod_le {M : Type*} [Monoid M] (A : M → ℝ) (h1 : A 1 ≤ 0)
    (hmul : ∀ x y, A (x * y) ≤ A x + A y) :
    ∀ {m : ℕ} (g : Fin m → M), A (List.ofFn g).prod ≤ ∑ i, A (g i)
  | 0, g => by simpa using h1
  | m + 1, g => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    linarith [angle_prod_le A h1 hmul (fun i => g i.succ),
      hmul (g 0) (List.ofFn fun i => g i.succ).prod]

/-! ## 2. The Cartan scaling -/

/-- **Every angle vector of total at least `π` is dominated by a Cartan profile of total `π`.**
DERIVED: the scale `π / Σ α`. Cited: `Real.cos_le_cos_of_nonneg_of_le_pi`. -/
theorem cartan_dominates {m : ℕ} {α : Fin m → ℝ} (h0 : ∀ i, 0 ≤ α i) (hπ : ∀ i, α i ≤ π)
    (hs : π ≤ ∑ i, α i) :
    ∃ φ : Fin m → ℝ, ∑ i, φ i = π ∧ (∀ i, 0 ≤ φ i ∧ φ i ≤ α i) ∧ spreadCost φ ≤ spreadCost α := by
  have hS : 0 < ∑ i, α i := lt_of_lt_of_le Real.pi_pos hs
  have hr0 : 0 ≤ π / ∑ i, α i := div_nonneg Real.pi_pos.le hS.le
  have hr1 : π / ∑ i, α i ≤ 1 := (div_le_one hS).mpr hs
  refine ⟨fun i => α i * (π / ∑ i, α i), ?_, fun i => ⟨mul_nonneg (h0 i) hr0,
    mul_le_of_le_one_right (h0 i) hr1⟩, ?_⟩
  · show ∑ i, α i * (π / ∑ i, α i) = π
    rw [← Finset.sum_mul, mul_div_assoc', div_eq_iff hS.ne']
    ring
  · unfold spreadCost
    refine Finset.sum_le_sum fun i _ => ?_
    have := Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (h0 i) hr0) (hπ i)
      (mul_le_of_le_one_right (h0 i) hr1)
    linarith

/-! ## 3. The `SU(2)` angle -/

/-- **The class angle of an `SU(2)` element**, `arccos(½ Re tr g)`, the geodesic distance from `1`. -/
def angle (g : SU 2) : ℝ := Real.arccos (ChainCoarseSeed.suTau g)

theorem angle_nonneg (g : SU 2) : 0 ≤ angle g := Real.arccos_nonneg _

theorem angle_le_pi (g : SU 2) : angle g ≤ π := Real.arccos_le_pi _

/-- The Wilson density is `1 − cos(angle g)`. -/
theorem wilsonDensity_eq (g : SU 2) : WilsonAction.wilsonDensity g = 1 - Real.cos (angle g) := by
  have hm := ChainCoarseSeed.suTau_mem g
  unfold angle
  rw [Real.cos_arccos hm.1 hm.2]
  unfold ChainCoarseSeed.suTau
  ring

theorem angle_one : angle 1 = 0 := by
  have h := SU2DiskLaw.suTau_dmat 0
  rw [SU2DiskLaw.dmat_zero, Real.cos_zero] at h
  unfold angle
  rw [h, Real.arccos_one]

theorem angle_negOne : angle TwistedTraceBound.negOne = π := by
  have h := SU2DiskLaw.suTau_dmat π
  rw [dmat_pi, Real.cos_pi] at h
  unfold angle
  rw [h, Real.arccos_neg_one]

/-- The angle is a class function. Cited: `WilsonAction.wilsonDensity_conj`. -/
theorem angle_conj (h g : SU 2) : angle (h * g * h⁻¹) = angle g := by
  unfold angle ChainCoarseSeed.suTau
  rw [WilsonAction.wilsonDensity_conj]

/-- **`½ Re tr (g h)`** in the coordinates `a = g₀₀, b = g₁₀, c = h₀₀, d = h₁₀`. -/
theorem suTau_mul (g h : SU 2) :
    ChainCoarseSeed.suTau (g * h)
      = ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re * ((h : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re
        - (((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im * ((h : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
          + ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re * ((h : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re
          + ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im * ((h : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im) := by
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
      = -(starRingEnd ℂ) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
    conv_lhs => rw [SU2DiskLaw.su2_eq g]
    simp
  rw [SU2DiskLaw.suTau_eq, Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h01]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **The triangle inequality on `SU(2)`**: `angle (g h) ≤ angle g + angle h`. Cauchy–Schwarz on
the three imaginary coordinates (Lagrange's identity). -/
theorem angle_mul_le (g h : SU 2) : angle (g * h) ≤ angle g + angle h := by
  unfold angle
  apply arccos_le_add
  rw [suTau_mul, SU2DiskLaw.suTau_eq g, SU2DiskLaw.suTau_eq h]
  set a0 := ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re
  set a1 := ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
  set b0 := ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re
  set b1 := ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im
  set c0 := ((h : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re
  set c1 := ((h : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
  set d0 := ((h : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re
  set d1 := ((h : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im
  have hg : a0 ^ 2 + a1 ^ 2 + b0 ^ 2 + b1 ^ 2 = 1 := SU2DiskLaw.su2_col g
  have hh : c0 ^ 2 + c1 ^ 2 + d0 ^ 2 + d1 ^ 2 = 1 := SU2DiskLaw.su2_col h
  refine cos_add_arccos_le (S := a1 ^ 2 + b0 ^ 2 + b1 ^ 2) (T := c1 ^ 2 + d0 ^ 2 + d1 ^ 2)
    (by linarith) (by linarith) (by positivity) (by positivity) ?_
  nlinarith [sq_nonneg (a1 * d0 - b0 * c1), sq_nonneg (a1 * d1 - b1 * c1),
    sq_nonneg (b0 * d1 - b1 * d0)]

/-- **A section multiplying to the centre spends total angle at least `π`.** -/
theorem pi_le_sum_angle {m : ℕ} (g : Fin m → SU 2)
    (h : (List.ofFn g).prod = TwistedTraceBound.negOne) : π ≤ ∑ i, angle (g i) := by
  have := angle_prod_le angle angle_one.le angle_mul_le g
  rwa [h, angle_negOne] at this

/-- The Wilson cost of a section is the spread cost of its angles. -/
theorem su2_cost_eq {m : ℕ} (g : Fin m → SU 2) :
    ∑ i, WilsonAction.wilsonDensity (g i) = spreadCost (fun i => angle (g i)) :=
  Finset.sum_congr rfl fun i _ => wilsonDensity_eq (g i)

/-! ## 4. `SU(2)`: every profile is dominated by a Cartan profile -/

/-- **Every `SU(2)` section of product `−1` is dominated by a Cartan section.** The Cartan angles
`φ` total `π`, lie in `[−π, π]`, their diagonal elements multiply to `−1`, and their cost
`spreadCost φ` (the Wilson cost of `dmat ∘ φ`) is at most that of `g`. -/
theorem su2_profile_dominated {m : ℕ} (g : Fin m → SU 2)
    (h : (List.ofFn g).prod = TwistedTraceBound.negOne) :
    ∃ φ : Fin m → ℝ, ∑ i, φ i = π ∧ (∀ i, |φ i| ≤ π)
      ∧ (List.ofFn fun i => dmat (φ i)).prod = TwistedTraceBound.negOne
      ∧ ∑ i, WilsonAction.wilsonDensity (dmat (φ i)) = spreadCost φ
      ∧ spreadCost φ ≤ ∑ i, WilsonAction.wilsonDensity (g i) := by
  obtain ⟨φ, hs, hb, hc⟩ := cartan_dominates (fun i => angle_nonneg (g i))
    (fun i => angle_le_pi (g i)) (pi_le_sum_angle g h)
  have hsec := su2_section φ hs
  refine ⟨φ, hs, fun i => abs_le.mpr ⟨by linarith [(hb i).1, Real.pi_pos],
    (hb i).2.trans (angle_le_pi _)⟩, hsec.1, hsec.2, ?_⟩
  rw [su2_cost_eq]
  exact hc

/-- **A transported `SU(2)` section is dominated by a Cartan section.** The plaquette holonomies
`g_k`, carried to a common base point by `h_k`, multiply to `−1`; the cost `Σ φ(g_k)` is at least
that of a Cartan section of total `π`. Cited: `WilsonAction.wilsonDensity_conj`. -/
theorem su2_transported_dominated {m : ℕ} (g t : Fin m → SU 2)
    (h : (List.ofFn fun i => t i * g i * (t i)⁻¹).prod = TwistedTraceBound.negOne) :
    ∃ φ : Fin m → ℝ, ∑ i, φ i = π ∧ (∀ i, |φ i| ≤ π)
      ∧ (List.ofFn fun i => dmat (φ i)).prod = TwistedTraceBound.negOne
      ∧ spreadCost φ ≤ ∑ i, WilsonAction.wilsonDensity (g i) := by
  obtain ⟨φ, hs, hb, hp, -, hc⟩ := su2_profile_dominated _ h
  refine ⟨φ, hs, hb, hp, ?_⟩
  calc spreadCost φ ≤ ∑ i, WilsonAction.wilsonDensity (t i * g i * (t i)⁻¹) := hc
    _ = ∑ i, WilsonAction.wilsonDensity (g i) :=
        Finset.sum_congr rfl fun i _ => WilsonAction.wilsonDensity_conj (t i) (g i)

/-- **Every `SU(2)` section of product `−1` costs at least `2/m`**, in any directions. Cited:
`ThickSheetCost.spreadCost_ge` at `θ = π`. -/
theorem su2_section_ge {m : ℕ} (hm : 0 < m) (g : Fin m → SU 2)
    (h : (List.ofFn g).prod = TwistedTraceBound.negOne) :
    2 / (m : ℝ) ≤ ∑ i, WilsonAction.wilsonDensity (g i) := by
  obtain ⟨φ, hs, hb, -, -, hc⟩ := su2_profile_dominated g h
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_pos.ne'
  have h1 := spreadCost_ge hm hs hb
  have e : 2 * π ^ 2 / (π ^ 2 * m) = 2 / (m : ℝ) := by field_simp
  linarith

/-- **Every coarse cell of `m` `SU(2)` sections of product `−1` costs at least `2`**, the
`2θ²/π²` of `ThickSheetCost.cellCost_ge` at `θ = π`, at every thickness and in any directions. -/
theorem su2_cellCost_ge {m : ℕ} (hm : 0 < m) (G : Fin m → Fin m → SU 2)
    (hG : ∀ s, (List.ofFn (G s)).prod = TwistedTraceBound.negOne) :
    2 ≤ ∑ s, ∑ i, WilsonAction.wilsonDensity (G s i) := by
  choose Φ hΦs hΦb _ _ hΦc using fun s => su2_profile_dominated (G s) (hG s)
  have h1 := cellCost_ge hm hΦs hΦb
  have h2 : cellCost Φ ≤ ∑ s, ∑ i, WilsonAction.wilsonDensity (G s i) :=
    by unfold cellCost; exact Finset.sum_le_sum fun s _ => hΦc s
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_pos.ne'
  have e : 2 * π ^ 2 / π ^ 2 = 2 := by field_simp
  linarith

/-- **Above `ln 3 / 8` no `SU(2)` thickening, Cartan or not, beats the entropy**: the surface sum
at the cell cost converges at every thickness. DERIVED: `8 = 4 · 2`, the `¼` of the entropy
against the cell floor `2`; `3` the cube-path step directions of `VortexEntropy.floorTerm`. -/
theorem su2_trial_summable {m : ℕ} (hm : 0 < m) (G : Fin m → Fin m → SU 2)
    (hG : ∀ s, (List.ofFn (G s)).prod = TwistedTraceBound.negOne) {β : ℝ}
    (hβ : Real.log 3 / 8 < β) :
    Summable (VortexEntropy.floorTerm (β * ∑ s, ∑ i, WilsonAction.wilsonDensity (G s i))) := by
  rw [VortexEntropy.floorTerm_summable_iff]
  have hc := su2_cellCost_ge hm G hG
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hβ0 : 0 < β := lt_trans (by positivity) hβ
  have h1 : β * 2 ≤ β * ∑ s, ∑ i, WilsonAction.wilsonDensity (G s i) :=
    mul_le_mul_of_nonneg_left hc hβ0.le
  linarith

/-! ## 5. `U(1)`: the same reduction -/

/-- **The angle of a `U(1)` phase**, `arccos(Re z) = |arg z|`. -/
def angleU (z : Circle) : ℝ := Real.arccos (z : ℂ).re

theorem re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have h := Circle.normSq_coe z
  rw [Complex.normSq_apply] at h
  linear_combination h

theorem angleU_one : angleU 1 = 0 := by
  unfold angleU
  rw [Circle.coe_one, Complex.one_re, Real.arccos_one]

/-- **The triangle inequality on `U(1)`.** -/
theorem angleU_mul_le (z w : Circle) : angleU (z * w) ≤ angleU z + angleU w := by
  unfold angleU
  apply arccos_le_add
  rw [Circle.coe_mul, Complex.mul_re]
  exact cos_add_arccos_le (S := (z : ℂ).im ^ 2) (T := (w : ℂ).im ^ 2) (re_sq_add_im_sq z)
    (re_sq_add_im_sq w) (sq_nonneg _) (sq_nonneg _) (le_of_eq (by ring))

/-- The cost `1 − Re z` of a phase is `1 − cos(angleU z)`. -/
theorem u1_cost_eq (z : Circle) : 1 - (z : ℂ).re = 1 - Real.cos (angleU z) := by
  have h1 : |(z : ℂ).re| ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mp (by nlinarith [re_sq_add_im_sq z, sq_nonneg (z : ℂ).im])
  unfold angleU
  rw [Real.cos_arccos (abs_le.mp h1).1 (abs_le.mp h1).2]

/-- **Every `U(1)` section of product `−1` is dominated by a section of total phase `π`.** The
phases may total any odd multiple of `π`; the angle sum is at least `π` either way. -/
theorem u1_profile_dominated {m : ℕ} (z : Fin m → Circle) (h : ((∏ i, z i : Circle) : ℂ) = -1) :
    ∃ φ : Fin m → ℝ, ∑ i, φ i = π ∧ (∀ i, |φ i| ≤ π)
      ∧ ∏ i, Complex.exp (φ i * Complex.I) = -1
      ∧ ∑ i, (1 - (Complex.exp (φ i * Complex.I)).re) = spreadCost φ
      ∧ spreadCost φ ≤ ∑ i, (1 - (z i : ℂ).re) := by
  have hp := angle_prod_le angleU angleU_one.le angleU_mul_le z
  rw [Fin.prod_ofFn] at hp
  have hpi : angleU (∏ i, z i) = π := by
    unfold angleU
    rw [h, Complex.neg_re, Complex.one_re, Real.arccos_neg_one]
  rw [hpi] at hp
  obtain ⟨φ, hs, hb, hc⟩ := cartan_dominates (fun i => Real.arccos_nonneg _)
    (fun i => Real.arccos_le_pi _) hp
  refine ⟨φ, hs, fun i => abs_le.mpr ⟨by linarith [(hb i).1, Real.pi_pos],
    (hb i).2.trans (Real.arccos_le_pi _)⟩, u1_section_pi φ hs, (u1_section φ).2, ?_⟩
  have e : ∑ i, (1 - (z i : ℂ).re) = spreadCost (fun i => angleU (z i)) :=
    Finset.sum_congr rfl fun i _ => u1_cost_eq (z i)
  rw [e]
  exact hc

/-- **Every `U(1)` section of product `−1` costs at least `2/m`.** -/
theorem u1_section_ge {m : ℕ} (hm : 0 < m) (z : Fin m → Circle)
    (h : ((∏ i, z i : Circle) : ℂ) = -1) : 2 / (m : ℝ) ≤ ∑ i, (1 - (z i : ℂ).re) := by
  obtain ⟨φ, hs, hb, -, -, hc⟩ := u1_profile_dominated z h
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_pos.ne'
  have h1 := spreadCost_ge hm hs hb
  have e : 2 * π ^ 2 / (π ^ 2 * m) = 2 / (m : ℝ) := by field_simp
  linarith

/-- **Every coarse cell of `m` `U(1)` sections of product `−1` costs at least `2`.** -/
theorem u1_cellCost_ge {m : ℕ} (hm : 0 < m) (Z : Fin m → Fin m → Circle)
    (hZ : ∀ s, ((∏ i, Z s i : Circle) : ℂ) = -1) : 2 ≤ ∑ s, ∑ i, (1 - (Z s i : ℂ).re) := by
  choose Φ hΦs hΦb _ _ hΦc using fun s => u1_profile_dominated (Z s) (hZ s)
  have h1 := cellCost_ge hm hΦs hΦb
  have h2 : cellCost Φ ≤ ∑ s, ∑ i, (1 - (Z s i : ℂ).re) := by
    unfold cellCost; exact Finset.sum_le_sum fun s _ => hΦc s
  have hpi : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_pos.ne'
  have e : 2 * π ^ 2 / π ^ 2 = 2 := by field_simp
  linarith

/-- **Above `ln 3 / 8` no `U(1)` thickening beats the entropy.** -/
theorem u1_trial_summable {m : ℕ} (hm : 0 < m) (Z : Fin m → Fin m → Circle)
    (hZ : ∀ s, ((∏ i, Z s i : Circle) : ℂ) = -1) {β : ℝ} (hβ : Real.log 3 / 8 < β) :
    Summable (VortexEntropy.floorTerm (β * ∑ s, ∑ i, (1 - (Z s i : ℂ).re))) := by
  rw [VortexEntropy.floorTerm_summable_iff]
  have hc := u1_cellCost_ge hm Z hZ
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hβ0 : 0 < β := lt_trans (by positivity) hβ
  have h1 : β * 2 ≤ β * ∑ s, ∑ i, (1 - (Z s i : ℂ).re) := mul_le_mul_of_nonneg_left hc hβ0.le
  linarith

/-! ## 6. The two groups side by side -/

/-- **`SU(2)` and `U(1)` have the same section floor.** Every `SU(2)` section of product `−1` is
dominated by `U(1)` phases of product `−1` at the same Cartan angles, and every `U(1)` section of
product `−1` by `SU(2)` diagonal elements of product `−1`. The infimum of the section cost is the
same in both groups at every `m`. -/
theorem su2_u1_same_floor {m : ℕ} :
    (∀ g : Fin m → SU 2, (List.ofFn g).prod = TwistedTraceBound.negOne →
      ∃ φ : Fin m → ℝ, ∏ i, Complex.exp (φ i * Complex.I) = -1
        ∧ ∑ i, (1 - (Complex.exp (φ i * Complex.I)).re) ≤ ∑ i, WilsonAction.wilsonDensity (g i))
    ∧ (∀ z : Fin m → Circle, ((∏ i, z i : Circle) : ℂ) = -1 →
      ∃ φ : Fin m → ℝ, (List.ofFn fun i => dmat (φ i)).prod = TwistedTraceBound.negOne
        ∧ ∑ i, WilsonAction.wilsonDensity (dmat (φ i)) ≤ ∑ i, (1 - (z i : ℂ).re)) := by
  refine ⟨fun g h => ?_, fun z h => ?_⟩
  · obtain ⟨φ, hs, -, -, -, hc⟩ := su2_profile_dominated g h
    exact ⟨φ, u1_section_pi φ hs, by rw [(u1_section φ).2]; exact hc⟩
  · obtain ⟨φ, hs, -, -, -, hc⟩ := u1_profile_dominated z h
    exact ⟨φ, (su2_section φ hs).1, by rw [(su2_section φ hs).2]; exact hc⟩

#print axioms cos_add_arccos_le
#print axioms arccos_le_add
#print axioms angle_prod_le
#print axioms cartan_dominates
#print axioms wilsonDensity_eq
#print axioms angle_one
#print axioms angle_negOne
#print axioms angle_conj
#print axioms suTau_mul
#print axioms angle_mul_le
#print axioms pi_le_sum_angle
#print axioms su2_cost_eq
#print axioms su2_profile_dominated
#print axioms su2_transported_dominated
#print axioms su2_section_ge
#print axioms su2_cellCost_ge
#print axioms su2_trial_summable
#print axioms re_sq_add_im_sq
#print axioms angleU_one
#print axioms angleU_mul_le
#print axioms u1_cost_eq
#print axioms u1_profile_dominated
#print axioms u1_section_ge
#print axioms u1_cellCost_ge
#print axioms u1_trial_summable
#print axioms su2_u1_same_floor

end MassGap.NonCartanTwist

end
