import Mathlib
import MassGap.PeriodicStateDLR
import MassGap.HaarVariance
import MassGap.PlaneVariance
import MassGap.ChessboardRead
import MassGap.ContinuumCluster
import MassGap.ContinuumNontrivial
import MassGap.ExistencePos
import MassGap.HeatBathErgodic

noncomputable section

/-!
# MassGap.ExistencePosNonnull — the base vector as a sum of plane slices, and the plane plaquette

The base vector is `Y_k = Yv (rho1 hN) k (baseMono O t ℓ m)`: the connected field `O − ν_k(O)` smeared
against the indicator of a cube at times `[t − d_m, t − d_m + ℓ]`, `d_m = dySpacing N m`. In lattice
units that cube sits about `(t − d_m)/a_k` steps above the plane, a distance that grows with `k`. This
module reads `Y_k` as a sum of transfer iterates of a vector on the plane.

* `lagProfile_double_le_form_sum`: on a positive transfer, for a finite set `J` of lags and `j₀ ∈ J`,
  `form(∑_{j∈J} Tʲ v, ∑_{j∈J} Tʲ v) ≥ b_{2j₀}(v)`. Every cross term is a lag profile `b_{i+j}(v) ≥ 0`
  (`ChessboardRead.lagProfile_add`, `ChessboardRead.lagProfile_nonneg`).
* `continuous_splice_left`: the splice of a finite-volume configuration into a fixed outside
  configuration is continuous in the finite-volume part.
* `Yv_base_eq_slices`: for every field `O`, once `a_k ≤ ℓ`, the base vector is exactly
  `∑_{j∈J} τ₁ʲ V` with `V = ∑_{y∈B} a_k⁴ T_y(O − ν_k O)`, `B` a nonempty set of sites on the plane
  `x₀ = 0` and `J` a nonempty set of lags. The cube is a product of a time interval and a spatial box.
* `planePlaq N`: the Wilson density of the plaquette in directions `(1, 2)` at the origin, a field on the
  plane `x₀ = 0`. The reflection fixes it (`ireflObs_planeV`), so `ν_k(θV · V) = ν_k(V²)`, and `V` is not
  identically zero at `2 ≤ N` (`planeV_ne_zero`): setting one link of the corner plaquette to an
  element of positive density raises `V`.
-/

namespace MassGap.ExistencePosNonnull

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumCluster
  MassGap.ChessboardRead MassGap.ExistencePos Filter MeasureTheory

variable {N : ℕ}

/-! ## 1. A sum of transfer iterates dominates its lowest even lag -/

section General

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

theorem form_sum_left (D : Transfer.TransferData A) {ι : Type*} (s : Finset ι) (y : ι → A)
    (z : A) : D.form (∑ i ∈ s, y i) z = ∑ i ∈ s, D.form (y i) z :=
  map_sum (AddMonoidHom.mk' (fun x => D.form x z) (fun a b => D.form_add_left a b z)) y s

theorem form_sum_right (D : Transfer.TransferData A) {ι : Type*} (s : Finset ι) (x : A)
    (y : ι → A) : D.form x (∑ i ∈ s, y i) = ∑ i ∈ s, D.form x (y i) :=
  map_sum (AddMonoidHom.mk' (fun z => D.form x z)
    (fun a b => D.toReflForm.toPreForm.form_add_right x a b)) y s

/-- **A sum of transfer iterates of one vector has form diagonal at least its profile at twice any of
its lags.** The diagonal is `∑_{i,j∈J} b_{i+j}(v)`, every term nonnegative on a positive transfer. -/
theorem lagProfile_double_le_form_sum (D : Transfer.TransferData A)
    (hP : GNSHilbert.PositiveTransfer D) (v : A) (J : Finset ℕ) {j₀ : ℕ} (hj₀ : j₀ ∈ J) :
    lagProfile D v (2 * j₀) ≤ D.form (∑ j ∈ J, (D.T ^ j) v) (∑ j ∈ J, (D.T ^ j) v) := by
  have e : D.form (∑ j ∈ J, (D.T ^ j) v) (∑ j ∈ J, (D.T ^ j) v)
      = ∑ i ∈ J, ∑ j ∈ J, lagProfile D v (i + j) := by
    rw [form_sum_left]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [form_sum_right]
    exact Finset.sum_congr rfl (fun j _ => (lagProfile_add D v i j).symm)
  rw [e, two_mul]
  have hnn : ∀ i j, 0 ≤ lagProfile D v (i + j) := fun i j => lagProfile_nonneg D hP v _
  calc lagProfile D v (j₀ + j₀) ≤ ∑ j ∈ J, lagProfile D v (j₀ + j) :=
        Finset.single_le_sum (f := fun j => lagProfile D v (j₀ + j)) (fun j _ => hnn _ _) hj₀
    _ ≤ ∑ i ∈ J, ∑ j ∈ J, lagProfile D v (i + j) :=
        Finset.single_le_sum (f := fun i => ∑ j ∈ J, lagProfile D v (i + j))
          (fun i _ => Finset.sum_nonneg (fun j _ => hnn _ _)) hj₀

end General

/-! ## 2. Splicing a finite-volume configuration -/

section Square

open MassGap.GibbsSpec MassGap.PeriodicStateDLR
open MassGap.CompactGauge (probHaar)
open MassGap.SUN (SU)

theorem continuous_splice_left (Λ : Finset ILink) (ω : IConf (SU N)) :
    Continuous (fun u : VConf (SU N) Λ => splice Λ u ω) := by
  refine continuous_pi (fun l => ?_)
  by_cases h : l ∈ Λ
  · simp only [splice, dif_pos h]
    exact continuous_apply _
  · simp only [splice, dif_neg h]
    exact continuous_const

end Square

/-! ## 4. The base vector is a sum of time slices -/

section Slices

open scoped Classical

/-- The time condition of the base cube at spacing `a`: `t − d ≤ a n ≤ t − d + ℓ`. -/
def timeOk (a t ℓ d : ℝ) (n : ℤ) : Prop := t - d ≤ a * n ∧ a * n ≤ t - d + ℓ

/-- The spatial condition of the base cube at spacing `a`: `t ≤ a xᵢ ≤ t + ℓ` for `i ≠ 0`. -/
def spaceOk (a t ℓ : ℝ) (x : MassGap.InfiniteLattice.ISite) : Prop :=
  ∀ i : Fin 4, i ≠ 0 → t ≤ a * x i ∧ a * x i ≤ t + ℓ

/-- The base test function at a lattice site is the indicator of the two conditions. -/
theorem baseTest_site (a t ℓ : ℝ) (m : ℕ) (x : MassGap.InfiniteLattice.ISite) :
    ((ContinuumNontrivial.cubeTest t ℓ).translate (-(timeVec N m 0 1))).1 (site a x)
      = if timeOk a t ℓ (dySpacing N m) (x 0) ∧ spaceOk a t ℓ x then 1 else 0 := by
  show ContinuumNontrivial.cubeInd t ℓ (site a x - -(timeVec N m 0 1)) = _
  have hc : ∀ i, (site a x - -(timeVec N m 0 1)) i
      = a * x i + (if i = 0 then dySpacing N m else 0) := by
    intro i
    simp only [Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add, timeVec, site, axisVec]
    by_cases h : i = 0 <;> simp [h]
  have hmem : site a x - -(timeVec N m 0 1) ∈ ContinuumNontrivial.timeCube t ℓ ↔
      timeOk a t ℓ (dySpacing N m) (x 0) ∧ spaceOk a t ℓ x := by
    rw [ContinuumNontrivial.mem_timeCube]
    constructor
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · have h0 := h 0
        rw [hc, if_pos rfl] at h0
        exact ⟨by linarith [h0.1], by linarith [h0.2]⟩
      · have hi' := h i
        rw [hc, if_neg hi, add_zero] at hi'
        exact hi'
    · rintro ⟨h0, hs⟩ i
      rw [hc]
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl]
        exact ⟨by linarith [h0.1], by linarith [h0.2]⟩
      · rw [if_neg hi, add_zero]
        exact hs i hi
  by_cases h : timeOk a t ℓ (dySpacing N m) (x 0) ∧ spaceOk a t ℓ x
  · rw [if_pos h]
    exact ContinuumNontrivial.cubeInd_of_mem (hmem.mpr h)
  · rw [if_neg h]
    exact ContinuumNontrivial.cubeInd_of_not_mem (fun h' => h (hmem.mp h'))

theorem ceil_mul_mem {a ℓ : ℝ} (ha : 0 < a) (hℓ : a ≤ ℓ) (s : ℝ) :
    s ≤ a * (⌈s / a⌉ : ℝ) ∧ a * (⌈s / a⌉ : ℝ) ≤ s + ℓ := by
  have h1 := Int.le_ceil (s / a)
  have h2 := Int.ceil_lt_add_one (s / a)
  have hne : a ≠ 0 := ha.ne'
  have e : a * (s / a) = s := by field_simp
  constructor
  · calc s = a * (s / a) := e.symm
      _ ≤ a * (⌈s / a⌉ : ℝ) := mul_le_mul_of_nonneg_left h1 ha.le
  · have h3 : a * (⌈s / a⌉ : ℝ) < a * (s / a + 1) := mul_lt_mul_of_pos_left h2 ha
    have h4 : a * (s / a + 1) = s + a := by rw [mul_add, e, mul_one]
    linarith

theorem axisVec_add_apply (n : ℤ) (y : MassGap.InfiniteLattice.ISite) (i : Fin 4) :
    (axisVec 0 n + y) i = (if i = 0 then n else 0) + y i := by
  simp [axisVec]

/-- **The base vector is a sum of time slices.** Once `a_k ≤ ℓ`, for every field `O`,
`Y_k = ∑_{j∈J} τ₁ʲ V` with `V = ∑_{y∈B} a_k⁴ T_y(O − ν_k O)`, `B` a nonempty set of sites on the plane
`x₀ = 0` and `J` a nonempty set of lags. -/
theorem Yv_base_eq_slices (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} {m k : ℕ}
    (hd : dySpacing N m < t) (hℓ : dySpacing N k ≤ ℓ) :
    ∃ (J : Finset ℕ) (B : Finset MassGap.InfiniteLattice.ISite), J.Nonempty ∧ B.Nonempty ∧
      (∀ y ∈ B, y 0 = 0) ∧
      Yv (rho1 hN) k (baseMono O t ℓ m)
        = ∑ j ∈ J, (⇑(MassGap.ReflectionShift.ishiftObsL 0))^[j]
            (∑ y ∈ B, (dySpacing N k ^ 4) • transObs y (O.sub (stateK hN k O.1)).1) := by
  set a := dySpacing N k with ha_def
  have ha : 0 < a := dySpacing_pos (one_le_of_ne_zero hN) k
  set fb := (ContinuumNontrivial.cubeTest t ℓ).translate (-(timeVec N m 0 1)) with hfb
  set F := (O.sub (stateK hN k O.1)).1 with hF
  obtain ⟨R, M, hf⟩ := fb.2
  set K := ⌈R / a⌉₊ with hK
  set P : Finset MassGap.InfiniteLattice.ISite :=
    (box K).filter (fun x => timeOk a t ℓ (dySpacing N m) (x 0) ∧ spaceOk a t ℓ x) with hP
  set J : Finset ℕ := P.image (fun x => (x 0).toNat) with hJ
  set B : Finset MassGap.InfiniteLattice.ISite :=
    (box K).filter (fun y => y 0 = 0 ∧ spaceOk a t ℓ y) with hB
  have htpos : ∀ n : ℤ, timeOk a t ℓ (dySpacing N m) n → 0 < n := by
    intro n hn
    have h1 : 0 < a * (n : ℝ) := lt_of_lt_of_le (sub_pos.mpr hd) hn.1
    have h2 : (0 : ℝ) < n := pos_of_mul_pos_right h1 ha.le
    exact_mod_cast h2
  have hbox : ∀ x : MassGap.InfiniteLattice.ISite,
      x ∈ box K ↔ ∀ i, x i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro x
    unfold box
    exact Fintype.mem_piFinset
  have hmemP : ∀ x, x ∈ P ↔ x ∈ box K ∧ timeOk a t ℓ (dySpacing N m) (x 0) ∧ spaceOk a t ℓ x := by
    intro x
    rw [hP, Finset.mem_filter]
  have hmemB : ∀ y, y ∈ B ↔ y ∈ box K ∧ y 0 = 0 ∧ spaceOk a t ℓ y := by
    intro y
    rw [hB, Finset.mem_filter]
  -- a point of the cube
  set xs : MassGap.InfiniteLattice.ISite :=
    fun i => if i = 0 then ⌈(t - dySpacing N m) / a⌉ else ⌈t / a⌉ with hxs
  have hx0 : xs 0 = ⌈(t - dySpacing N m) / a⌉ := by simp [hxs]
  have hxi : ∀ i, i ≠ 0 → xs i = ⌈t / a⌉ := fun i hi => by simp [hxs, hi]
  have hxs_ok : timeOk a t ℓ (dySpacing N m) (xs 0) ∧ spaceOk a t ℓ xs := by
    refine ⟨?_, fun i hi => ?_⟩
    · have h := ceil_mul_mem ha hℓ (t - dySpacing N m)
      rw [hx0]
      exact ⟨h.1, by linarith [h.2]⟩
    · have h := ceil_mul_mem ha hℓ t
      rw [hxi i hi]
      exact h
  have hxsP : xs ∈ P := by
    refine (hmemP xs).mpr ⟨?_, hxs_ok⟩
    refine mem_box_of_ne ha hf xs ?_
    show fb.1 (site a xs) ≠ 0
    rw [hfb, baseTest_site, if_pos hxs_ok]
    exact one_ne_zero
  -- the bijection between `P` and `J × B`
  set iF : MassGap.InfiniteLattice.ISite → ℕ × MassGap.InfiniteLattice.ISite :=
    fun x => ((x 0).toNat, Function.update x 0 0) with hiF
  set jF : ℕ × MassGap.InfiniteLattice.ISite → MassGap.InfiniteLattice.ISite :=
    fun p => axisVec 0 (p.1 : ℤ) + p.2 with hjF
  have hupdB : ∀ x, x ∈ P → Function.update x 0 0 ∈ B := by
    intro x hx
    obtain ⟨hxb, -, hxsp⟩ := (hmemP x).mp hx
    refine (hmemB _).mpr ⟨(hbox _).mpr (fun i => ?_), by simp, fun i hi => ?_⟩
    · by_cases h : i = 0
      · subst h
        rw [Function.update_self, Finset.mem_Icc]
        constructor <;> omega
      · rw [Function.update_of_ne h]
        exact (hbox x).mp hxb i
    · rw [Function.update_of_ne hi]
      exact hxsp i hi
  have hi : ∀ x ∈ P, iF x ∈ J ×ˢ B := by
    intro x hx
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem _ hx, hupdB x hx⟩
  have hj : ∀ p ∈ J ×ˢ B, jF p ∈ P := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨x', hx'P, hx'eq⟩ := Finset.mem_image.mp hp1
    obtain ⟨hx'b, hx't, -⟩ := (hmemP x').mp hx'P
    obtain ⟨hyb, hy0, hysp⟩ := (hmemB p.2).mp hp2
    have hpos := htpos _ hx't
    have hcast : ((p.1 : ℕ) : ℤ) = x' 0 := by rw [← hx'eq]; omega
    have h0 : jF p 0 = x' 0 := by
      show (axisVec 0 (p.1 : ℤ) + p.2) 0 = x' 0
      rw [axisVec_add_apply, if_pos rfl, hy0, add_zero, hcast]
    have hne : ∀ i, i ≠ 0 → jF p i = p.2 i := by
      intro i hi
      show (axisVec 0 (p.1 : ℤ) + p.2) i = p.2 i
      rw [axisVec_add_apply, if_neg hi, zero_add]
    refine (hmemP _).mpr ⟨(hbox _).mpr (fun i => ?_), ?_, fun i hi => ?_⟩
    · by_cases h : i = 0
      · subst h
        rw [h0]
        exact (hbox x').mp hx'b 0
      · rw [hne i h]
        exact (hbox p.2).mp hyb i
    · rw [h0]
      exact hx't
    · rw [hne i hi]
      exact hysp i hi
  have hleft : ∀ x ∈ P, jF (iF x) = x := by
    intro x hx
    obtain ⟨-, hxt, -⟩ := (hmemP x).mp hx
    have hpos := htpos _ hxt
    funext i
    show (axisVec 0 (((x 0).toNat : ℕ) : ℤ) + Function.update x 0 0) i = x i
    rw [axisVec_add_apply]
    by_cases h : i = 0
    · subst h
      rw [if_pos rfl, Function.update_self, add_zero]
      omega
    · rw [if_neg h, zero_add, Function.update_of_ne h]
  have hright : ∀ p ∈ J ×ˢ B, iF (jF p) = p := by
    intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨-, hy0, -⟩ := (hmemB p.2).mp hp2
    have h0 : jF p 0 = (p.1 : ℤ) := by
      show (axisVec 0 (p.1 : ℤ) + p.2) 0 = (p.1 : ℤ)
      rw [axisVec_add_apply, if_pos rfl, hy0, add_zero]
    refine Prod.ext ?_ ?_
    · show (jF p 0).toNat = p.1
      rw [h0]
      omega
    · show Function.update (jF p) 0 0 = p.2
      funext i
      by_cases h : i = 0
      · subst h
        rw [Function.update_self, hy0]
      · rw [Function.update_of_ne h]
        show (axisVec 0 (p.1 : ℤ) + p.2) i = p.2 i
        rw [axisVec_add_apply, if_neg h, zero_add]
  refine ⟨J, B, ⟨_, Finset.mem_image_of_mem _ hxsP⟩, ⟨_, hupdB xs hxsP⟩,
    fun y hy => ((hmemB y).mp hy).2.1, ?_⟩
  -- the smeared field as the sum over `P`
  have hY : Yv (rho1 hN) k (baseMono O t ℓ m) = smear a F fb := by
    unfold baseMono
    rw [MassGap.ExistencePos.Yv_mono1]
    show (1 : ℝ) • smear a F fb = smear a F fb
    rw [one_smul]
  have hsm : smear a F fb = ∑ x ∈ P, (a ^ 4) • transObs x F := by
    rw [smear_eq_sum ha F fb hf (Finset.Subset.refl _), hP, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hfb, baseTest_site]
    split_ifs <;> simp
  have hbij : ∑ x ∈ P, (a ^ 4) • transObs x F = ∑ p ∈ J ×ˢ B, (a ^ 4) • transObs (jF p) F :=
    Finset.sum_nbij' iF jF hi hj hleft hright
      (fun x hx => congrArg (fun z => (a ^ 4) • transObs z F) (hleft x hx).symm)
  rw [hY, hsm, hbij, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ishiftObsL_iterate, map_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [map_smul, transObs_transObs]

end Slices

/-! ## 5. The plane plaquette -/

section Plane

/-- The plaquette in directions `(1, 2)` at the origin, on the plane `x₀ = 0`. -/
def q₀ : MassGap.GibbsSpec.IPlaq := ((1, 2), fun _ => 0)

theorem planePlaq_mem :
    GaugeInvariantAlgebra.iplaqObs (N := N) q₀
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
  GaugeInvariantAlgebra.iplaqObs_mem_gaugeInvHalfSpaceAlg_of_le q₀ 0 0 (le_of_eq rfl)

/-- **The plane plaquette field**: the Wilson density of `q₀`. -/
def planePlaq (N : ℕ) : LField (MassGap.SUN.SU N) :=
  ⟨GaugeInvariantAlgebra.iplaqObs (N := N) q₀,
    ⟨by
      obtain ⟨S, -, hS⟩ :=
        HalfSpaceAlgebra.mem_halfSpaceAlg.mp (Submodule.mem_inf.mp (planePlaq_mem (N := N))).1
      exact ⟨S, hS⟩,
     (Submodule.mem_inf.mp (planePlaq_mem (N := N))).2⟩⟩

/-- The plane slice `∑_{y∈B} s · T_y(planePlaq − c)`. -/
def planeV (s c : ℝ) (B : Finset MassGap.InfiniteLattice.ISite) : C(Cfg N, ℝ) :=
  ∑ y ∈ B, s • transObs y ((planePlaq N).sub c).1

theorem planeV_mem (s c : ℝ) (B : Finset MassGap.InfiniteLattice.ISite)
    (hB : ∀ y ∈ B, y 0 = 0) :
    planeV (N := N) s c B ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  obtain ⟨S, hSpos, hS⟩ :=
    HalfSpaceAlgebra.mem_halfSpaceAlg.mp (Submodule.mem_inf.mp (planePlaq_mem (N := N))).1
  refine Submodule.sum_mem _ (fun y hy => Submodule.smul_mem _ _ ?_)
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · refine transObs_mem_halfSpaceAlg (isLocalOn_sub_const hS c) 0 y (fun l hl => ?_)
    have h1 : (0 : ℤ) ≤ l.2 0 := hSpos (Finset.mem_coe.mpr hl)
    rw [hB y hy]
    omega
  · exact isIGaugeInvariant_transObs ((planePlaq N).sub c).2.2 y

theorem ireflSite_plane {y : MassGap.InfiniteLattice.ISite} (hy : y 0 = 0) :
    LatticeReflection.ireflSite 0 0 y = y := by
  unfold LatticeReflection.ireflSite
  rw [Function.update_eq_self_iff, hy, sub_zero]

theorem ireflPlaq_q₀ : LatticeReflection.ireflPlaq 0 0 q₀ = q₀ := by
  have hs : LatticeReflection.ireflSite 0 0 q₀.2 = q₀.2 := ireflSite_plane rfl
  have h1 : q₀.1.1 ≠ 0 := by decide
  have h2 : q₀.1.2 ≠ 0 := by decide
  unfold LatticeReflection.ireflPlaq
  rw [if_neg h1, if_neg h2, hs]

/-- **The reflection fixes the plane slice.** -/
theorem ireflObs_planeV (s c : ℝ) (B : Finset MassGap.InfiniteLattice.ISite)
    (hB : ∀ y ∈ B, y 0 = 0) :
    LatticeReflection.ireflObs 0 0 (planeV (N := N) s c B) = planeV s c B := by
  have hθ1 : LatticeReflection.ireflObs 0 0 (1 : C(Cfg N, ℝ)) = 1 := by
    ext U
    rfl
  have hθO : LatticeReflection.ireflObs 0 0 ((planePlaq N).sub c).1 = ((planePlaq N).sub c).1 := by
    show LatticeReflection.ireflObs 0 0
        (GaugeInvariantAlgebra.iplaqObs (N := N) q₀ - c • (1 : C(Cfg N, ℝ)))
      = GaugeInvariantAlgebra.iplaqObs (N := N) q₀ - c • (1 : C(Cfg N, ℝ))
    rw [map_sub, map_smul, GaugeInvariantAlgebra.ireflObs_iplaqObs, ireflPlaq_q₀, hθ1]
  unfold planeV
  rw [map_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [map_smul, ireflObs_transObs, ireflSite_plane (hB y hy), hθO]

/-- The plane slice is local on a finite set of links. -/
theorem planeV_local (s c : ℝ) (B : Finset MassGap.InfiniteLattice.ISite) :
    ∃ S : Finset MassGap.InfiniteLattice.ILink,
      MassGap.DLRLimit.IsLocalOnC S (planeV (N := N) s c B) := by
  obtain ⟨S, -, hS⟩ :=
    HalfSpaceAlgebra.mem_halfSpaceAlg.mp (Submodule.mem_inf.mp (planePlaq_mem (N := N))).1
  refine ⟨B.biUnion (fun y => S.image (fun l : MassGap.InfiniteLattice.ILink => (l.1, l.2 + y))),
    fun U U' h => ?_⟩
  unfold planeV
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  congr 1
  exact isLocalOn_transObs (isLocalOn_sub_const hS c) y U U'
    (fun l hl => h l (Finset.mem_biUnion.mpr ⟨y, hy, hl⟩))

theorem exists_wilsonDensity_pos (hN2 : 2 ≤ N) :
    ∃ g : MassGap.SUN.SU N, 0 < MassGap.WilsonAction.wilsonDensity g := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  refine ⟨MassGap.HaarVariance.flipEl n, ?_⟩
  have h := MassGap.HaarVariance.reTr_flipEl n
  unfold MassGap.HaarVariance.reTr at h
  unfold MassGap.WilsonAction.wilsonDensity
  rw [h]
  have e : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [e, div_mul_eq_mul_div, one_mul, sub_pos, div_lt_one hpos]
  linarith

/-- The value of the plane plaquette at a translated configuration. -/
theorem planePlaq_transConf (U : Cfg N) (y : MassGap.InfiniteLattice.ISite) :
    (planePlaq N).1 (transConf y U)
      = MassGap.WilsonAction.wilsonDensity
          (U (1, q₀.2 + y) * (U (2, MassGap.GibbsSpec.ishift 1 q₀.2 + y)
            * ((U (1, MassGap.GibbsSpec.ishift 2 q₀.2 + y))⁻¹ * (U (2, q₀.2 + y))⁻¹))) := by
  show MassGap.WilsonAction.wilsonDensity (MassGap.GibbsSpec.ihol q₀ (transConf y U)) = _
  rw [MassGap.PlaneVariance.ihol_eq_head_mul]
  rfl

/-- **The plane slice is not identically zero** at `2 ≤ N`, for `s > 0` and `B` nonempty. -/
theorem planeV_ne_zero (hN2 : 2 ≤ N) {s : ℝ} (hs : 0 < s) (c : ℝ)
    {B : Finset MassGap.InfiniteLattice.ISite} (hB : B.Nonempty) :
    ∃ U₀ : Cfg N, planeV (N := N) s c B U₀ ≠ 0 := by
  have hN : N ≠ 0 := by omega
  obtain ⟨g, hg⟩ := exists_wilsonDensity_pos hN2
  obtain ⟨y₀, hy₀⟩ := hB
  set U₁ : Cfg N := fun _ => 1 with hU₁
  set U₂ : Cfg N := Function.update U₁ (1, y₀) g with hU₂
  have hev : ∀ U : Cfg N, planeV (N := N) s c B U
      = ∑ y ∈ B, s * ((planePlaq N).1 (transConf y U) - c * 1) := by
    intro U
    unfold planeV
    rw [ContinuousMap.coe_sum, Finset.sum_apply]
    rfl
  have hv1 : ∀ y, (planePlaq N).1 (transConf y U₁) = 0 := by
    intro y
    rw [planePlaq_transConf]
    simp only [hU₁, inv_one, mul_one]
    exact MassGap.WilsonAction.wilsonDensity_one hN
  have hv2 : (planePlaq N).1 (transConf y₀ U₂) = MassGap.WilsonAction.wilsonDensity g := by
    rw [planePlaq_transConf]
    have e0 : q₀.2 + y₀ = y₀ := by
      funext i
      simp [q₀]
    have hne2 : ∀ z, ((2 : Fin 4), z) ≠ ((1 : Fin 4), y₀) := by
      intro z h
      have h' : (2 : Fin 4) = 1 := congrArg Prod.fst h
      exact absurd h' (by decide)
    have hne1 : ((1 : Fin 4), MassGap.GibbsSpec.ishift 2 q₀.2 + y₀) ≠ ((1 : Fin 4), y₀) := by
      intro h
      have h2 := congrFun (congrArg Prod.snd h) 2
      simp [MassGap.GibbsSpec.ishift, q₀] at h2
    rw [e0, hU₂, Function.update_self, Function.update_of_ne (hne2 _),
      Function.update_of_ne hne1, Function.update_of_ne (hne2 _)]
    simp only [hU₁, inv_one, mul_one]
  by_contra hall
  have h1 : planeV (N := N) s c B U₁ = 0 := by
    by_contra h
    exact hall ⟨U₁, h⟩
  have h2 : planeV (N := N) s c B U₂ = 0 := by
    by_contra h
    exact hall ⟨U₂, h⟩
  rw [hev] at h1 h2
  have hdiff : ∑ y ∈ B, s * (planePlaq N).1 (transConf y U₂) = 0 := by
    have e : ∑ y ∈ B, s * ((planePlaq N).1 (transConf y U₂) - c * 1)
        - ∑ y ∈ B, s * ((planePlaq N).1 (transConf y U₁) - c * 1)
        = ∑ y ∈ B, s * (planePlaq N).1 (transConf y U₂) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hv1 y]
      ring
    rw [← e, h1, h2, sub_zero]
  have hnn : ∀ y ∈ B, 0 ≤ s * (planePlaq N).1 (transConf y U₂) := fun y _ =>
    mul_nonneg hs.le (MassGap.WilsonAction.wilsonDensity_nonneg hN _)
  have hle := Finset.single_le_sum hnn hy₀
  rw [hdiff, hv2] at hle
  have : 0 < s * MassGap.WilsonAction.wilsonDensity g := mul_pos hs hg
  linarith

end Plane

end MassGap.ExistencePosNonnull

#print axioms MassGap.ExistencePosNonnull.lagProfile_double_le_form_sum
#print axioms MassGap.ExistencePosNonnull.baseTest_site
#print axioms MassGap.ExistencePosNonnull.Yv_base_eq_slices
#print axioms MassGap.ExistencePosNonnull.planeV_mem
#print axioms MassGap.ExistencePosNonnull.ireflObs_planeV
#print axioms MassGap.ExistencePosNonnull.planeV_local
#print axioms MassGap.ExistencePosNonnull.exists_wilsonDensity_pos
#print axioms MassGap.ExistencePosNonnull.planeV_ne_zero
