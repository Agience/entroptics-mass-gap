import Mathlib
import MassGap.BandClose
import MassGap.BulkBound
import MassGap.HaarVariance

/-!
# MassGap.ReadPos — the contact reflected read of the centred tensor reading is strictly positive

`BandClose.gE β 0 = ν_β(θX · X)`, `X = E 0 − ν_β(E 0)` the centred tensor reading at the origin,
`θ` the site reflection about `x₀ = 0`, `ν_β = periodicStateG (SU N) β`. Reflection positivity gives
`gE β 0 ≥ 0`. This module proves `0 < gE β 0` at every `β ≥ 0` and every `N ≥ 2`. Declarations are in the
namespace `MassGap.ReadPos`.

## The argument

Write `A = P₀₁(0)`, `A' = P₀₁(−e₀)`, `B = P₂₃(0)` (plaquette densities) and `c = ν(A − B)`. Then
`X = A − B − c` and `θX = A' − B − c` (`BandClose.ireflObs_tensorEnergyG_zero`); `B` lies in the mirror,
`θB = B`.

1. Polarisation. If `ν(θX · X) = 0`, then for every `Y` in the half-space algebra with `θY = Y`,
   `t ↦ ν(θ(X + tY)(X + tY)) = t · ν((θX + X) Y) + t² ν(Y²)` is non-negative for every real `t`, so
   `ν((A + A' − 2B − 2c) Y) = 0` (`lin_zero`).
2. Top end. `b = max B` is attained (compact configuration space); every plaquette density is at most
   `b`, since a single-link configuration gives `B` any holonomy (`ihol_update`). With
   `Y = max(0, B − (b − ε))`, `ν(Y) > 0` (`BulkBound.periodicState_pos_of_local`) and the integrand is at
   most `2(ε − c) Y`; so `c ≤ ε` for every `ε > 0`: `c ≤ 0`.
3. Bottom end. The DLR kernel on the four links of a `(0, 1)`-plaquette `q` reads `P_q` at least
   `κ_q > 0` at every boundary condition (`kernel_floor`, the weight bound `e^{−2β|∂S|}` of
   `BulkBound`), and a reading of the `(2, 3)`-plaquette is outside those links
   (`wspec_mul_outside`). With `Y = max(0, ε − B)`, `ν(Y) > 0` (identity configuration), and
   `ν((A + A')Y) ≥ (κ_A + κ_{A'}) ν(Y)`, `ν(BY) ≤ ε ν(Y)`; at `ε = (κ_A + κ_{A'})/4`, `c > 0`.

Steps 2 and 3 contradict, so `ν(θX · X) ≠ 0`. `N ≥ 2` enters only through an element `g ≠ 1` of
`SU(N)` (`HaarVariance.flipEl`), so `P_q` is not identically zero; at `N = 1` the read is `0`.

## Consequence

`ReflFloorAt N βs U` is `BandClose.ReflReadsAt` without the positivity conjunct; along any sequence of
couplings eventually `≥ 0` it gives `ReflReadsAt` (`reflReadsAt_of_floor`), and every coupling tower is
eventually `≥ 0`, so in `clayStatement_of_strongEnd_floor` the positivity is discharged.
That capstone is vacuous: `ReflFloor.headline_hypotheses_inconsistent` proves that `StrongEnd N` and its
residual `ReflFloorAt N βs (2 log 2)` (frequently near `0⁺`, along every tower) give `False`, and
`ReflFloor.not_floor_residual` refutes the residual at every fixed level. It is kept because `ReflFloor`
states its refutation against it. The root to use is `OneInput.clayStatement_of_strongEnd` (residual
`MeasTowerG ∧ ExistAlong`, the band level existential per tower). The lemmas of this module are unaffected.

DERIVED (module-wide): `0` the plane, the time axis, the origin and the signs; `1` the group unit and the
unit step; `2` the two plaquette reads of one polarisation, the least rank and the plane directions
`(2, 3)`; `3` the last plane direction; `4` the quarter that places `ε` below the kernel floor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.ReadPos

open Filter MeasureTheory
open MassGap.SUN (SU)

variable {N : ℕ}

/-- The configuration space at `SU(N)`. DERIVED: no numeral. -/
abbrev Conf (N : ℕ) : Type := MassGap.GibbsSpec.IConf (SU N)

/-- The plaquette density as an observable. DERIVED: no numeral. -/
abbrev Pq [NeZero N] (q : MassGap.GibbsSpec.IPlaq) : C(Conf N, ℝ) :=
  (MassGap.ClayTreeG.plaqFieldG (G := SU N) q).1

/-! ## 1. Single-link configurations -/

/-- A configuration equal to `1` off the first link of `q` and to `g` there has holonomy `g`. DERIVED:
`1` the group unit. -/
theorem ihol_update (q : MassGap.GibbsSpec.IPlaq) (h : q.1.1 ≠ q.1.2) (g : SU N) :
    MassGap.GibbsSpec.ihol q (Function.update (1 : Conf N) (q.1.1, q.2) g) = g := by
  have h1 : ((q.1.2, MassGap.GibbsSpec.ishift q.1.1 q.2) : MassGap.InfiniteLattice.ILink)
      ≠ (q.1.1, q.2) := fun e => h (congrArg Prod.fst e).symm
  have h2 : ((q.1.1, MassGap.GibbsSpec.ishift q.1.2 q.2) : MassGap.InfiniteLattice.ILink)
      ≠ (q.1.1, q.2) := fun e => by
    have := congrFun (congrArg Prod.snd e) q.1.2
    simp [MassGap.GibbsSpec.ishift] at this
  have h3 : ((q.1.2, q.2) : MassGap.InfiniteLattice.ILink) ≠ (q.1.1, q.2) :=
    fun e => h (congrArg Prod.fst e).symm
  simp [MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd,
    Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]

/-- The identity configuration has unit holonomy. DERIVED: `1` the group unit. -/
theorem ihol_one (q : MassGap.GibbsSpec.IPlaq) : MassGap.GibbsSpec.ihol q (1 : Conf N) = 1 := by
  simp [MassGap.GibbsSpec.ihol, MassGap.WilsonLattice.wilsonHol, MassGap.GibbsSpec.ibd]

/-- `SU(N)` at `N ≥ 2` has an element other than `1`. DERIVED: `2` the least rank. -/
theorem exists_ne_one (hN : 2 ≤ N) : ∃ g : SU N, g ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact ⟨MassGap.HaarVariance.flipEl m, fun e =>
    MassGap.HaarVariance.reTr_flipEl_ne_reTr_one m (by rw [e])⟩

/-- The links of a plaquette lie in its two plane directions. DERIVED: no numeral. -/
theorem fst_of_mem_ilinks {q : MassGap.GibbsSpec.IPlaq} {l : MassGap.InfiniteLattice.ILink}
    (h : l ∈ MassGap.GibbsSpec.ilinks q) : l.1 = q.1.1 ∨ l.1 = q.1.2 := by
  rw [MassGap.GibbsSpec.ilinks_eq] at h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp

/-- A plaquette density is local on its own links. DERIVED: no numeral. -/
theorem Pq_local [NeZero N] (q : MassGap.GibbsSpec.IPlaq) (U V : Conf N)
    (h : ∀ l ∈ (MassGap.GibbsSpec.ilinks q).toFinset, U l = V l) : Pq (N := N) q U = Pq q V := by
  show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol q U)
    = GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol q V)
  rw [MassGap.GibbsSpec.ihol_congr q U V (fun l hl => h l (List.mem_toFinset.mpr hl))]

/-! ## 2. The kernel floor -/

section Kernel

open MassGap.GibbsSpec MassGap.PeriodicStateDLR MassGap.WilsonAction
open MassGap.CompactGauge (probHaar)

/-- **The DLR kernel on `S` reads a non-negative `S`-local field, positive somewhere, at least a fixed
`κ > 0` at every boundary condition.** The weight is at least `e^{−2β|∂S|}`, the partition function at most
`1`. DERIVED: `0` the signs and `β ≥ 0`; `2` the range of the density; `1` the weight bound. -/
theorem kernel_floor (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (F : C(IConf (SU N), ℝ))
    (S : Finset MassGap.InfiniteLattice.ILink)
    (hS : ∀ U V : IConf (SU N), (∀ l ∈ S, U l = V l) → F U = F V)
    (hF0 : ∀ U, 0 ≤ F U) {P : IConf (SU N)} (hP : 0 < F P) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ω, κ ≤ wspec hN β S F ω := by
  classical
  set μ : Measure (SU N) := probHaar (SU N) with hμ
  set c0 : ℝ := Real.exp (-(β * (((boundaryPlaqs S).card : ℝ) * 2))) with hc0
  let g : VConf (SU N) S → ℝ := fun u => F (splice S u P)
  have hgc : Continuous g := F.continuous.comp (MassGap.BulkBound.continuous_splice_left S P)
  have hg0 : ∀ u, 0 ≤ g u := fun u => hF0 _
  have hFb : ∀ U, |F U| ≤ ‖F‖ := fun U => by
    rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm U
  have hgint : Integrable g (vol μ S) := integrable_of_bounded _ hgc.measurable (fun u => hFb _)
  have hI : 0 < ∫ u, g u ∂(vol μ S) := by
    haveI : (vol μ S).IsOpenPosMeasure :=
      inferInstanceAs ((Measure.pi fun _ : ↥S => μ).IsOpenPosMeasure)
    rw [integral_pos_iff_support_of_nonneg hg0 hgint]
    let u0 : VConf (SU N) S := fun l => P l.1
    have hu0 : splice S u0 P = P := by
      funext l
      by_cases h : l ∈ S
      · rw [splice_mem h]
      · rw [splice_not_mem h]
    have hopen : IsOpen {u : VConf (SU N) S | 0 < g u} := isOpen_lt continuous_const hgc
    have hne : ({u : VConf (SU N) S | 0 < g u}).Nonempty := ⟨u0, by
      show 0 < F (splice S u0 P); rw [hu0]; exact hP⟩
    exact lt_of_lt_of_le (hopen.measure_pos _ hne)
      (measure_mono fun u hu => Function.mem_support.mpr (ne_of_gt hu))
  have hc0pos : 0 < c0 := Real.exp_pos _
  refine ⟨c0 * ∫ u, g u ∂(vol μ S), mul_pos hc0pos hI, fun ω => ?_⟩
  rw [wspec_apply]
  have hloc : ∀ u, F (splice S u ω) = g u := fun u =>
    hS _ _ (fun l hl => by rw [splice_mem hl, splice_mem hl])
  have hwlo : ∀ u, c0 ≤ wt wilsonDensity β S u ω := fun u => by
    unfold wt
    rw [hc0, Real.exp_le_exp]
    have := actionOn_le (wilsonDensity_le_two hN) (boundaryPlaqs S) (splice S u ω)
    nlinarith
  have hwhi : ∀ u, wt wilsonDensity β S u ω ≤ 1 := fun u =>
    exp_neg_actionOn_le_one (wilsonDensity_nonneg hN) hβ _ _
  have hwint : Integrable (fun u => wt wilsonDensity β S u ω) (vol μ S) :=
    integrable_wt measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN) β S μ ω
  have hpart := part_pos measurable_wilsonDensity (wilsonDensity_nonneg hN) (wilsonDensity_le_two hN)
    β S μ ω
  have hpart1 : part wilsonDensity β S μ ω ≤ 1 := by
    unfold part
    calc ∫ u, wt wilsonDensity β S u ω ∂(vol μ S) ≤ ∫ _u, (1 : ℝ) ∂(vol μ S) :=
          integral_mono hwint (integrable_const 1) hwhi
      _ = 1 := by simp
  have hnum : c0 * ∫ u, g u ∂(vol μ S) ≤ num wilsonDensity β S μ (⇑F) ω := by
    unfold num
    have hfun : (fun u => F (splice S u ω) * wt wilsonDensity β S u ω)
        = fun u => g u * wt wilsonDensity β S u ω := funext fun u => by rw [hloc u]
    rw [hfun, ← integral_const_mul]
    have hint2 : Integrable (fun u => g u * wt wilsonDensity β S u ω) (vol μ S) :=
      integrable_of_bounded _ (hgc.measurable.mul (measurable_wt_left measurable_wilsonDensity β S ω))
        (fun u => by
          rw [abs_mul, abs_of_pos (wt_pos _ _ _ _ _)]
          calc |g u| * wt wilsonDensity β S u ω ≤ ‖F‖ * 1 :=
                mul_le_mul (hFb _) (hwhi u) (wt_pos _ _ _ _ _).le (norm_nonneg _)
            _ = ‖F‖ := mul_one _)
    refine integral_mono (hgint.const_mul c0) hint2 (fun u => ?_)
    have := mul_le_mul_of_nonneg_left (hwlo u) (hg0 u)
    show c0 * g u ≤ g u * wt wilsonDensity β S u ω
    linarith [mul_comm c0 (g u)]
  have hc0I : 0 ≤ c0 * ∫ u, g u ∂(vol μ S) := (mul_pos hc0pos hI).le
  unfold spec
  rw [le_div_iff₀ hpart]
  calc c0 * (∫ u, g u ∂(vol μ S)) * part wilsonDensity β S μ ω
      ≤ c0 * (∫ u, g u ∂(vol μ S)) * 1 := mul_le_mul_of_nonneg_left hpart1 hc0I
    _ ≤ num wilsonDensity β S μ (⇑F) ω := by rw [mul_one]; exact hnum

/-- **The kernel on `S` passes a factor that does not read `S`.** DERIVED: no numeral. -/
theorem wspec_mul_outside (hN : N ≠ 0) (β : ℝ) (S : Finset MassGap.InfiniteLattice.ILink)
    (F Y : C(IConf (SU N), ℝ)) (hY : ∀ u ω, Y (splice S u ω) = Y ω) (ω : IConf (SU N)) :
    wspec hN β S (F * Y) ω = wspec hN β S F ω * Y ω := by
  rw [wspec_apply, wspec_apply]
  unfold spec num
  have h : ∀ u, (⇑(F * Y)) (splice S u ω) * wt wilsonDensity β S u ω
      = Y ω * (F (splice S u ω) * wt wilsonDensity β S u ω) := fun u => by
    rw [ContinuousMap.coe_mul, Pi.mul_apply, hY]; ring
  simp_rw [h, integral_const_mul]
  ring

/-- **The state reads `F · Y` at least `κ ν(Y)`** when the kernel floor of `F` on `S` is `κ` and
`Y ≥ 0` does not read `S`. DERIVED: `0` the sign of `Y`. -/
theorem state_mul_ge (hN : N ≠ 0) (β : ℝ) (S : Finset MassGap.InfiniteLattice.ILink)
    (F Y : C(IConf (SU N), ℝ)) (hY : ∀ u ω, Y (splice S u ω) = Y ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    {κ : ℝ} (hκ : ∀ ω, κ ≤ wspec hN β S F ω) :
    κ * MassGap.PeriodicState.periodicState hN β Y
      ≤ MassGap.PeriodicState.periodicState hN β (F * Y) := by
  rw [← periodicState_dlr hN β S (F * Y), ← (MassGap.PeriodicState.periodicState hN β).map_smul]
  refine (MassGap.PeriodicState.periodicState hN β).mono (fun ω => ?_)
  rw [wspec_mul_outside hN β S F Y hY ω, ContinuousMap.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hκ ω) (hY0 ω)

end Kernel

/-! ## 3. Polarisation -/

/-- A real quadratic `t L + t² Q ≥ 0` for every `t`, with `Q ≥ 0`, has `L = 0`. DERIVED: `1` the shift
of the denominator; `2` the square. -/
theorem lin_zero {L Q : ℝ} (hQ : 0 ≤ Q) (h : ∀ t : ℝ, 0 ≤ t * L + t ^ 2 * Q) : L = 0 := by
  have hQ1 : 0 < Q + 1 := by linarith
  have h1 := h (-L / (Q + 1))
  have e : (-L / (Q + 1)) * L + (-L / (Q + 1)) ^ 2 * Q = -(L ^ 2) / (Q + 1) ^ 2 := by
    field_simp; ring
  rw [e] at h1
  have h2 : 0 ≤ -(L ^ 2) := by
    have := mul_nonneg h1 (pow_pos hQ1 2).le
    rwa [div_mul_cancel₀ _ (pow_pos hQ1 2).ne'] at this
  have h3 : L ^ 2 = 0 := by nlinarith [sq_nonneg L]
  exact pow_eq_zero_iff two_ne_zero |>.mp h3

/-! ## 4. The contact read is strictly positive -/

open MassGap.InfiniteLattice MassGap.ApertureThing MassGap.ClayTreeG

variable [NeZero N]

/-- The `(2, 3)`-plaquette at the origin. DERIVED: `2`, `3` the plane; `0` the origin. -/
abbrev qB : MassGap.GibbsSpec.IPlaq := (((2 : Fin 4), (3 : Fin 4)), (0 : ISite))
/-- The `(0, 1)`-plaquette at the origin. DERIVED: `0`, `1` the plane; `0` the origin. -/
abbrev qA : MassGap.GibbsSpec.IPlaq := (((0 : Fin 4), (1 : Fin 4)), (0 : ISite))
/-- The `(0, 1)`-plaquette one step below the mirror. DERIVED: `0`, `1` the plane. -/
abbrev qA' : MassGap.GibbsSpec.IPlaq := (((0 : Fin 4), (1 : Fin 4)), -eT)

/-- The mirror fixes the `(2, 3)`-plaquette density at the origin. DERIVED: `0` the mirror. -/
theorem ireflObs_B : LatticeReflection.ireflObs 0 0 (Pq (N := N) qB) = Pq qB := by
  rw [BandClose.ireflObs_plaqFieldG]
  have h2 : LatticeReflection.ireflPlaq 0 0 qB = qB := by
    simp only [LatticeReflection.ireflPlaq]
    rw [if_neg (by decide), if_neg (by decide), BandClose.ireflSite_zero_zero]
  rw [h2]

/-- A reading of the `(2, 3)`-plaquette density through `φ`. DERIVED: no numeral. -/
def Yof (φ : C(ℝ, ℝ)) : C(Conf N, ℝ) := φ.comp (Pq (N := N) qB)

theorem Yof_apply (φ : C(ℝ, ℝ)) (U : Conf N) : Yof (N := N) φ U = φ (Pq qB U) := rfl

/-- The mirror fixes `Yof φ`. DERIVED: `0` the mirror. -/
theorem ireflObs_Yof (φ : C(ℝ, ℝ)) : LatticeReflection.ireflObs 0 0 (Yof (N := N) φ) = Yof φ := by
  ext U
  have h := congrArg (fun F : C(Conf N, ℝ) => F U) (ireflObs_B (N := N))
  simp only [LatticeReflection.ireflObs_apply] at h ⊢
  rw [Yof_apply, Yof_apply, ← h]

/-- `Yof φ` is a positive half-space observable. DERIVED: `0` the plane. -/
theorem Yof_mem (φ : C(ℝ, ℝ)) :
    Yof (N := N) φ ∈ HalfSpaceAlgebra.halfSpaceAlg (G := SU N) 0 0 := by
  refine HalfSpaceAlgebra.mem_halfSpaceAlg.mpr ⟨(MassGap.GibbsSpec.ilinks qB).toFinset, ?_, ?_⟩
  · intro l hl
    exact GaugeInvariantAlgebra.ilinks_mem_posHalf_of_le qB (by simp)
      l (List.mem_toFinset.mp (Finset.mem_coe.mp hl))
  · intro U V h
    rw [Yof_apply, Yof_apply, Pq_local qB U V h]

/-- `Yof φ` does not read the links of a `(0, 1)`-plaquette. DERIVED: `0`, `1` the plane. -/
theorem Yof_splice (φ : C(ℝ, ℝ)) {q : MassGap.GibbsSpec.IPlaq} (hq : q.1 = ((0 : Fin 4), (1 : Fin 4)))
    (u : MassGap.GibbsSpec.VConf (SU N) (MassGap.GibbsSpec.ilinks q).toFinset) (ω : Conf N) :
    Yof (N := N) φ (MassGap.GibbsSpec.splice _ u ω) = Yof φ ω := by
  rw [Yof_apply, Yof_apply, Pq_local qB _ ω (fun l hl => ?_)]
  apply MassGap.GibbsSpec.splice_not_mem
  intro hS
  have h1 := fst_of_mem_ilinks (List.mem_toFinset.mp hl)
  have h2 := fst_of_mem_ilinks (List.mem_toFinset.mp hS)
  rw [hq] at h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1] at h2 <;> exact absurd h2 (by decide)

/-- Every plaquette density is at most the maximum of the `(2, 3)`-density at the origin. DERIVED: `2`, `3`
the plane. -/
theorem Pq_le_max (Pm : Conf N) (hmax : ∀ U, Pq (N := N) qB U ≤ Pq qB Pm)
    (q : MassGap.GibbsSpec.IPlaq) (U : Conf N) : Pq (N := N) q U ≤ Pq qB Pm := by
  have h := hmax (Function.update (1 : Conf N) (qB.1.1, qB.2) (MassGap.GibbsSpec.ihol q U))
  have e : Pq (N := N) qB (Function.update (1 : Conf N) (qB.1.1, qB.2) (MassGap.GibbsSpec.ihol q U))
      = Pq q U := by
    show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol qB _) = GaugeGroup.wilsonDensityG _ _
    rw [ihol_update qB (by decide)]
  rwa [e] at h

/-- A `(0, 1)`-plaquette density is positive somewhere at `N ≥ 2`. DERIVED: `2` the least rank. -/
theorem exists_Pq_pos (hN2 : 2 ≤ N) (q : MassGap.GibbsSpec.IPlaq) (hq : q.1.1 ≠ q.1.2) :
    ∃ P : Conf N, 0 < Pq (N := N) q P := by
  obtain ⟨g, hg⟩ := exists_ne_one (N := N) hN2
  refine ⟨Function.update (1 : Conf N) (q.1.1, q.2) g, ?_⟩
  show 0 < GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol q _)
  rw [ihol_update q hq]
  exact lt_of_le_of_ne (GaugeGroup.wilsonDensityG_nonneg g)
    (fun e => hg ((GaugeGroup.wilsonDensityG_eq_zero_iff g).mp e.symm))

/-- **The contact reflected read of the centred tensor reading is strictly positive** at every `β ≥ 0`,
`N ≥ 2`. DERIVED: `0` the contact gap, the signs and `β ≥ 0`; `2` the least rank and the two reads of one
polarisation; `4` the quarter of the kernel floor. -/
theorem gE_zero_pos [Fact (2 ≤ N)] {β : ℝ} (hβ : 0 ≤ β) : 0 < BandClose.gE (N := N) β 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  have hN2 : 2 ≤ N := Fact.out
  set ν := MassGap.PeriodicState.periodicState hN β with hν
  set A := Pq (N := N) qA
  set A' := Pq (N := N) qA'
  set B := Pq (N := N) qB
  set X0 := MassGap.MeasuredTower.tensorEnergyG (SU N) 0 with hX0
  set c := ν X0 with hc
  set X := StepPeriodic.connP (N := N) β X0 with hXdef
  have hX : ∀ U, X U = A U - B U - c := fun U => by
    simp [hXdef, StepPeriodic.connP, hX0, MassGap.MeasuredTower.tensorEnergyG, A, B, hc, hν,
      GaugeWilson.periodicStateG_SU]
  have hθX : ∀ U, LatticeReflection.ireflObs 0 0 X U = A' U - B U - c := fun U => by
    have h1 : LatticeReflection.ireflObs (G := SU N) 0 0 (1 : C(Conf N, ℝ)) = 1 := rfl
    rw [hXdef, StepPeriodic.connP, map_sub, map_smul, h1, BandClose.ireflObs_tensorEnergyG_zero]
    simp [A', B, hc, hν, GaugeWilson.periodicStateG_SU, X0]
  have hgE : BandClose.gE (N := N) β 0 = ν (LatticeReflection.ireflObs 0 0 X * X) := by
    show ν (LatticeReflection.ireflObs 0 0 X * ContinuumField.transObs ((2 * 0) • eT) X) = _
    rw [mul_zero, zero_smul, ContinuumField.transObs_zero]
  have hRP := MassGap.PeriodicState.periodicState_reflPositive hN β 0 0
  rw [mul_zero] at hRP
  have hXmem : X ∈ HalfSpaceAlgebra.halfSpaceAlg (G := SU N) 0 0 :=
    StepPeriodic.connP_mem β BandClose.tensorEnergyG_zero_mem
  have h0 : 0 ≤ BandClose.gE (N := N) β 0 := by rw [hgE]; exact hRP X hXmem
  refine lt_of_le_of_ne h0 (fun hzero => ?_)
  -- polarisation: every mirror-fixed reading `Y = Yof φ` has `ν((θX + X) Y) = 0`
  have hpol : ∀ φ : C(ℝ, ℝ),
      ν (LatticeReflection.ireflObs 0 0 X * Yof φ + Yof φ * X) = 0 := fun φ => by
    set Y := Yof (N := N) φ
    refine lin_zero (Q := ν (Y * Y)) (ν.nonneg' _ (fun U => mul_self_nonneg _)) (fun t => ?_)
    have hmem : X + t • Y ∈ HalfSpaceAlgebra.halfSpaceAlg (G := SU N) 0 0 :=
      Submodule.add_mem _ hXmem (Submodule.smul_mem _ _ (Yof_mem φ))
    have hp := hRP _ hmem
    have hexp : LatticeReflection.ireflObs 0 0 (X + t • Y) * (X + t • Y)
        = LatticeReflection.ireflObs 0 0 X * X
          + t • (LatticeReflection.ireflObs 0 0 X * Y + Y * X) + t ^ 2 • (Y * Y) := by
      rw [map_add, map_smul, ireflObs_Yof]
      ext U
      simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
        smul_eq_mul]
      ring
    have hp' : 0 ≤ ν (LatticeReflection.ireflObs 0 0 (X + t • Y) * (X + t • Y)) := hp
    rw [hexp, ν.map_add, ν.map_add, ν.map_smul, ν.map_smul, ← hgE, hzero] at hp'
    linarith
  have hG : ∀ (φ : C(ℝ, ℝ)) (U : Conf N),
      (LatticeReflection.ireflObs 0 0 X * Yof φ + Yof φ * X : C(Conf N, ℝ)) U
      = (A U + A' U - 2 * B U - 2 * c) * Yof (N := N) φ U := fun φ U => by
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, hθX, hX]
    ring
  -- top end: `c ≤ 0`
  obtain ⟨Pm, -, hPm⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty (B.continuous.continuousOn)
  have hmax : ∀ U, B U ≤ B Pm := fun U => hPm (Set.mem_univ U)
  set b := B Pm
  have hAb : ∀ U, A U ≤ b := Pq_le_max Pm hmax qA
  have hA'b : ∀ U, A' U ≤ b := Pq_le_max Pm hmax qA'
  have htop : c ≤ 0 := by
    by_contra hcpos
    push Not at hcpos
    set ε := c / 2
    have hε : 0 < ε := by positivity
    let φ : C(ℝ, ℝ) := ⟨fun x => max 0 (x - (b - ε)),
      continuous_const.max (continuous_id.sub continuous_const)⟩
    have hY0 : ∀ U, 0 ≤ Yof (N := N) φ U := fun U => le_max_left _ _
    have hYpos : 0 < ν (Yof φ) :=
      MassGap.BulkBound.periodicState_pos_of_local hN hβ (Yof φ) (MassGap.GibbsSpec.ilinks qB).toFinset
        (fun U V h => by rw [Yof_apply, Yof_apply, Pq_local qB U V h]) hY0
        (P := Pm) (by show 0 < max 0 (b - (b - ε)); simp [hε])
    have hle : ν (LatticeReflection.ireflObs 0 0 X * Yof φ + Yof φ * X) ≤ ν ((2 * ε - 2 * c) • Yof φ) :=
      ν.mono (fun U => by
        rw [hG, ContinuousMap.smul_apply, smul_eq_mul]
        show (A U + A' U - 2 * B U - 2 * c) * max 0 (B U - (b - ε))
          ≤ (2 * ε - 2 * c) * max 0 (B U - (b - ε))
        have := hAb U
        have := hA'b U
        rcases le_total 0 (B U - (b - ε)) with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; simp)
    rw [hpol, ν.map_smul] at hle
    have e : 2 * ε - 2 * c = -c := by simp only [ε]; ring
    rw [e] at hle
    nlinarith [mul_pos hcpos hYpos]
  -- bottom end: `c > 0`
  have hSA := fun U V h => Pq_local (N := N) qA U V h
  have hSA' := fun U V h => Pq_local (N := N) qA' U V h
  obtain ⟨PA, hPA⟩ := exists_Pq_pos (N := N) hN2 qA (by decide)
  obtain ⟨PA', hPA'⟩ := exists_Pq_pos (N := N) hN2 qA' (by decide)
  obtain ⟨κ, hκ, hκA⟩ := kernel_floor hN hβ A _ hSA
    (fun U => GaugeGroup.wilsonDensityG_nonneg _) hPA
  obtain ⟨κ', hκ', hκA'⟩ := kernel_floor hN hβ A' _ hSA'
    (fun U => GaugeGroup.wilsonDensityG_nonneg _) hPA'
  set ε := (κ + κ') / 4
  have hε : 0 < ε := by positivity
  let φ : C(ℝ, ℝ) := ⟨fun x => max 0 (ε - x), continuous_const.max (continuous_const.sub continuous_id)⟩
  have hY0 : ∀ U, 0 ≤ Yof (N := N) φ U := fun U => le_max_left _ _
  have hB1 : B 1 = 0 := by
    show GaugeGroup.wilsonDensityG _ (MassGap.GibbsSpec.ihol qB 1) = 0
    rw [ihol_one, GaugeGroup.wilsonDensityG_one]
  have hYpos : 0 < ν (Yof φ) :=
    MassGap.BulkBound.periodicState_pos_of_local hN hβ (Yof φ) (MassGap.GibbsSpec.ilinks qB).toFinset
      (fun U V h => by rw [Yof_apply, Yof_apply, Pq_local qB U V h]) hY0
      (P := 1) (by show 0 < max 0 (ε - B 1); rw [hB1]; simp [hε])
  have hAY := state_mul_ge hN β _ A (Yof φ) (Yof_splice φ rfl) hY0 hκA
  have hA'Y := state_mul_ge hN β _ A' (Yof φ) (Yof_splice φ rfl) hY0 hκA'
  have hge : ν (A * Yof φ + A' * Yof φ - (2 * ε + 2 * c) • Yof φ)
      ≤ ν (LatticeReflection.ireflObs 0 0 X * Yof φ + Yof φ * X) :=
    ν.mono (fun U => by
      rw [hG]
      simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      show A U * max 0 (ε - B U) + A' U * max 0 (ε - B U) - (2 * ε + 2 * c) * max 0 (ε - B U)
        ≤ (A U + A' U - 2 * B U - 2 * c) * max 0 (ε - B U)
      rcases le_total 0 (ε - B U) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; simp)
  rw [hpol, ν.map_sub, ν.map_add, ν.map_smul] at hge
  have e4 : κ + κ' = 4 * ε := by simp only [ε]; ring
  nlinarith [mul_pos hε hYpos, mul_nonneg (neg_nonneg.mpr htop) hYpos.le]

/-! ## 5. The reflected reads without the positivity conjunct -/

open MassGap.CouplingTower (StrongEnd CouplingTower)
open MassGap.ConstantPhysicsLine (ExistAlong)
open Topology

variable (N) in
/-- **The reflected reads along a tower at level `U`, positivity discharged**: eventually in `k`, with
`g = gE (βs k)`, a window floor at `U` (link 2) and the mirror-defect bound. DERIVED: `2` the two steps of
one gap and the window base; `1` the least gap index and the unit fraction; `0` the origin and the signs. -/
def ReflFloorAt (βs : ℕ → ℝ) (U : ℝ) : Prop :=
  ∀ᶠ k in atTop, (∃ m₁ : ℕ, 1 ≤ m₁ ∧
    BandClose.gE (N := N) (βs k) 0 * Real.exp (-(2 * m₁ * (U / 2 ^ k))) ≤ BandClose.gE (N := N) (βs k) m₁) ∧
    ∃ c : ℝ, c < 1 ∧ ∀ᶠ m in atTop,
      |FocusZoom.stateCov (GaugeWilson.periodicStateG (SU N) (βs k)) (BandClose.mirrorDefect (N := N))
        (MassGap.MeasuredTower.tensorEnergyG (SU N) (0 + (2 * m) • eT))|
        ≤ c * |BandClose.gE (N := N) (βs k) m|

/-- **`ReflFloorAt` gives `ReflReadsAt` along couplings eventually `≥ 0`.** DERIVED: `0` the sign of the
coupling. -/
theorem reflReadsAt_of_floor [Fact (2 ≤ N)] {βs : ℕ → ℝ} {U : ℝ} (hβ : ∀ᶠ k in atTop, 0 ≤ βs k)
    (h : ReflFloorAt N βs U) : BandClose.ReflReadsAt N βs U := by
  filter_upwards [hβ, h] with k hk ⟨h1, h2⟩
  exact ⟨gE_zero_pos hk, h1, h2⟩

/-- **The root at `SU(N)` with the upper half in floor form.** `StrongEnd N` and, at window couplings
arbitrarily close to `0⁺`, `ReflFloorAt N βs (2 log 2)` and `ExistAlong N βs` along every coupling tower give
`ClayStatementOf (SU N)`; the tower supplies `βs k ≥ 0`. Vacuous: `ReflFloor.headline_hypotheses_inconsistent` proves its hypotheses jointly inconsistent (`ReflFloor.not_floor_residual`); kept as the statement that module refutes. Use `OneInput.clayStatement_of_strongEnd`.
DERIVED: `0` the limit `0⁺`; `2` the band ratio.
Inherited: `log 2` the window rate. -/
theorem clayStatement_of_strongEnd_floor [Fact (2 ≤ N)] (hS : StrongEnd N)
    (hR : ∃ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      ReflFloorAt N βs (2 * Real.log 2) ∧ ExistAlong N βs) :
    ClayStatementG.ClayStatementOf (SU N) :=
  BandClose.clayStatement_of_strongEnd_reads hS (hR.mono fun _ h βs hT =>
    ⟨reflReadsAt_of_floor (hT.2.2.mono fun _ hk => hk.2.1) (h βs hT).1, (h βs hT).2⟩)

end MassGap.ReadPos

end

#print axioms MassGap.ReadPos.ihol_update
#print axioms MassGap.ReadPos.ihol_one
#print axioms MassGap.ReadPos.exists_ne_one
#print axioms MassGap.ReadPos.fst_of_mem_ilinks
#print axioms MassGap.ReadPos.Pq_local
#print axioms MassGap.ReadPos.kernel_floor
#print axioms MassGap.ReadPos.wspec_mul_outside
#print axioms MassGap.ReadPos.state_mul_ge
#print axioms MassGap.ReadPos.lin_zero
#print axioms MassGap.ReadPos.ireflObs_B
#print axioms MassGap.ReadPos.ireflObs_Yof
#print axioms MassGap.ReadPos.Yof_mem
#print axioms MassGap.ReadPos.Yof_splice
#print axioms MassGap.ReadPos.Pq_le_max
#print axioms MassGap.ReadPos.exists_Pq_pos
#print axioms MassGap.ReadPos.gE_zero_pos
#print axioms MassGap.ReadPos.reflReadsAt_of_floor
#print axioms MassGap.ReadPos.clayStatement_of_strongEnd_floor
