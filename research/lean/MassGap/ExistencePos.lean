import Mathlib
import MassGap.ExistenceReduce
import MassGap.ChessboardRead

noncomputable section

/-!
# MassGap.ExistencePos — reference positivity is lag-one positivity

`ExistenceReduce.clay_canonical` carries `hpos : ∀ᶠ k, 0 < refReading hN O t ℓ k`, the reflected
reference cube pair at unit field strength. At step `k` the cube sits `t / a_k` lattice steps above the
plane, a distance that grows with `k`. This module removes that distance.

* `baseMono O t ℓ m`: the reference monomial moved back in time by one dyadic step `dySpacing N m`;
  `shift_baseMono`: moving it forward again gives `refMono O t ℓ`.
* `refReading_eq_lagProfile`: at `k ≥ m`, `refReading hN O t ℓ k` is the lag profile of the base vector
  `x_k` of the step-`k` transfer data `ContinuumCluster.Dk hN 0 k` at the even lag `2 · 2^{k−m}`
  (`ContinuumSep.latSkR_pairFam_shift_eq_form`, `ChessboardRead.lagProfile_even`).
* `refReading_pos_iff_lagOnePos`: for `dySpacing N m < t`, eventual positivity of the reference reading
  is equivalent to `LagOnePos hN O t ℓ m`, eventual positivity of the lag-one profile
  `ν_k(θY_k · τ₁Y_k)`, `Y_k` the base vector and `τ₁` one lattice step in time. Forward: the profile is
  nonnegative and log-convex (`ChessboardRead.lagProfile_log_convex`), so `b₁ > 0` forces `b₀ > 0`, and
  `b₁ᴹ b₀ ≤ b₀ᴹ b_M` (`ChessboardRead.pow_mul_le_of_log_convex`) gives `b_M > 0`. Backward: `b₁` is the
  diagonal of the positive form `ChessboardRead.tForm`, and `b_M = tForm(x, T^{M−1}x)`, which
  Cauchy–Schwarz bounds by `b₁ · tForm(T^{M−1}x, T^{M−1}x)`.
* `clay_canonical_lagOne`: `clay_canonical` with `hpos` replaced by `LagOnePos`.

Since `T` is a positive contraction, `b₁ = ‖T^{1/2} x‖²`, so `LagOnePos` says that the step-`k` transfer
operator does not annihilate the base vector. On each finite torus that holds for every non-constant
gauge-invariant vector; `LagOnePos` asks it in the periodic infinite-volume state.
-/

namespace MassGap.ExistencePos

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumCluster
  MassGap.ChessboardRead Filter

variable {N : ℕ}

/-- The connected renormalisation at unit field strength, the one `refReading` reads. -/
abbrev rho1 (hN : N ≠ 0) : Renorm N := Renorm.connected hN (fun _ _ => 1)

theorem rho1_reflCompat (hN : N ≠ 0) : (rho1 hN).ReflCompat 0 :=
  Renorm.connected_reflCompat hN _ 0 (fun _ _ => rfl)

/-- The reference monomial moved back in time by `dySpacing N m`. -/
def baseMono (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (m : ℕ) : Mono N :=
  ContinuumNontrivial.mono1
    (O, (ContinuumNontrivial.cubeTest t ℓ).translate (-(timeVec N m 0 1)))

theorem shift_baseMono (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (m : ℕ) :
    Mono.shift (timeVec N m 0 1) (baseMono O t ℓ m) = ExistenceReduce.refMono O t ℓ := by
  simp only [Mono.shift, baseMono, ExistenceReduce.refMono, ContinuumNontrivial.mono1,
    TestFn.translate_translate, neg_add_cancel, TestFn.translate_zero]

theorem timeVec_zero_one (m : ℕ) : timeVec N m 0 1 0 = dySpacing N m := by
  simp [timeVec, site, axisVec]

/-- For `dySpacing N m < t` the base test function has positive-time support. -/
theorem posTime_base {t ℓ : ℝ} {m : ℕ} (hd : dySpacing N m < t) :
    PosTime 0 ((ContinuumNontrivial.cubeTest t ℓ).translate (-(timeVec N m 0 1))) := by
  refine ⟨t - dySpacing N m, sub_pos.mpr hd, fun y hy => ?_⟩
  have hy' : ContinuumNontrivial.cubeInd t ℓ (y - -(timeVec N m 0 1)) ≠ 0 := hy
  have hmem : y - -(timeVec N m 0 1) ∈ ContinuumNontrivial.timeCube t ℓ :=
    Set.mem_of_indicator_ne_zero hy'
  have h0 := (hmem 0).1
  have e : (y - -(timeVec N m 0 1)) 0 = y 0 + dySpacing N m := by
    simp only [Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add, timeVec_zero_one]
  rw [e] at h0
  linarith

/-- Eventually in the step the base vector lies in the gauge-invariant half-space algebra. -/
theorem eventually_base_mem (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} {m : ℕ}
    (hd : dySpacing N m < t) :
    ∀ᶠ k in atTop, Yv (rho1 hN) k (baseMono O t ℓ m)
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
  have hmem : ∀ᶠ k in atTop, ∀ i : Fin (baseMono (N := N) O t ℓ m).1, ∀ r : ℝ,
      smear (dySpacing N k) (((baseMono O t ℓ m).2 i).1.sub r).1 ((baseMono O t ℓ m).2 i).2
        ∈ HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    Filter.eventually_all.mpr (fun _ => eventually_smear_sub_mem (one_le_of_ne_zero hN) 0 _ _
      (posTime_base hd))
  filter_upwards [hmem] with k hk
  exact Yv_mem hN (rho1 hN) 0 k _ hk

/-- `PositiveTransfer` for the step-`k` transfer data. -/
theorem Dk_positiveTransfer (hN : N ≠ 0) (k : ℕ) : GNSHilbert.PositiveTransfer (Dk hN 0 k) :=
  PeriodicState.periodic_positiveTransfer 0 0 hN
    (le_trans zero_le_one (one_le_dyBeta (one_le_of_ne_zero hN) k))

/-- **The reference reading is an even lag of the base vector's profile.** -/
theorem refReading_eq_lagProfile (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ)
    {k m : ℕ} (hk : m ≤ k)
    (hY : Yv (rho1 hN) k (baseMono O t ℓ m)
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    ExistenceReduce.refReading hN O t ℓ k
      = lagProfile (Dk hN 0 k) ⟨_, hY⟩ (2 * (2 ^ (k - m) * 1)) := by
  rw [lagProfile_even]
  unfold ExistenceReduce.refReading ExistenceReduce.refReadingAlong
  rw [← shift_baseMono O t ℓ m]
  exact ContinuumSep.latSkR_pairFam_shift_eq_form hN (rho1 hN) 0 (rho1_reflCompat hN) hk 1 _ hY

/-- The lag-one profile of the base vector, as a state value. -/
theorem lagProfile_one_eq (hN : N ≠ 0) (k : ℕ) (Y : C(Cfg N, ℝ))
    (hY : Y ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    lagProfile (Dk hN 0 k) ⟨Y, hY⟩ 1
      = stateK hN k (LatticeReflection.ireflObs 0 0 Y * MassGap.ReflectionShift.ishiftObsL 0 Y) := by
  show (Dk hN 0 k).form ⟨Y, hY⟩ (((Dk hN 0 k).T ^ 1) ⟨Y, hY⟩) = _
  rw [Dk_form, Dk_T_pow, Function.iterate_one]

/-- Positivity at lag one gives positivity at every lag. -/
theorem lagProfile_pos_of_one {A : Type*} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A)
    (hP : GNSHilbert.PositiveTransfer D) (x : A) (h1 : 0 < lagProfile D x 1) (M : ℕ) :
    0 < lagProfile D x M := by
  have hb := lagProfile_nonneg D hP x
  have hlc := lagProfile_log_convex D hP x
  have h0 : 0 < lagProfile D x 0 := by
    rcases eq_or_lt_of_le (hb 0) with h | h
    · have := hlc 0
      rw [← h, zero_mul] at this
      nlinarith
    · exact h
  have key := pow_mul_le_of_log_convex hb hlc M
  have hl : 0 < lagProfile D x 1 ^ M * lagProfile D x 0 := mul_pos (pow_pos h1 M) h0
  rcases eq_or_lt_of_le (hb M) with h | h
  · rw [← h, mul_zero] at key
    linarith
  · exact h

/-- Positivity at a positive lag gives positivity at lag one. -/
theorem lagProfile_one_pos_of {A : Type*} [AddCommGroup A] [Module ℝ A] (D : Transfer.TransferData A)
    (hP : GNSHilbert.PositiveTransfer D) (x : A) {M : ℕ} (hM : M ≠ 0) (hpos : 0 < lagProfile D x M) :
    0 < lagProfile D x 1 := by
  rcases eq_or_lt_of_le (lagProfile_nonneg D hP x 1) with h | h
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
    have hxx : (tForm D hP).form x x = 0 := by
      show D.form x (D.T x) = 0
      have e : lagProfile D x 1 = D.form x (D.T x) := by
        show D.form x ((D.T ^ 1) x) = D.form x (D.T x)
        rw [pow_one]
      rw [← e, ← h]
    have hcs := (tForm D hP).cauchy_schwarz x ((D.T ^ j) x)
    rw [hxx, zero_mul] at hcs
    have hz : (tForm D hP).form x ((D.T ^ j) x) = 0 := by nlinarith [sq_nonneg ((tForm D hP).form x ((D.T ^ j) x))]
    have e2 : lagProfile D x (j + 1) = (tForm D hP).form x ((D.T ^ j) x) := by
      show D.form x ((D.T ^ (j + 1)) x) = D.form x (D.T ((D.T ^ j) x))
      rw [T_pow_succ_apply]
    rw [e2, hz] at hpos
    exact lt_irrefl _ hpos
  · exact h

/-- **Lag-one positivity of the base vector (the remaining statement).** Eventually in the step,
`ν_k(θY_k · τ₁Y_k) > 0` with `Y_k = Yv (rho1 hN) k (baseMono O t ℓ m)`, `θ` the time reflection at the
plane `x₀ = 0` and `τ₁` one lattice step forward in time. -/
def LagOnePos (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) (m : ℕ) : Prop :=
  ∀ᶠ k in atTop, 0 < stateK hN k
    (LatticeReflection.ireflObs 0 0 (Yv (rho1 hN) k (baseMono O t ℓ m))
      * MassGap.ReflectionShift.ishiftObsL 0 (Yv (rho1 hN) k (baseMono O t ℓ m)))

/-- **Reference positivity is lag-one positivity.** -/
theorem refReading_pos_iff_lagOnePos (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    {m : ℕ} (hd : dySpacing N m < t) :
    (∀ᶠ k in atTop, 0 < ExistenceReduce.refReading hN O t ℓ k) ↔ LagOnePos hN O t ℓ m := by
  constructor
  · intro h
    filter_upwards [h, eventually_base_mem hN O hd, eventually_ge_atTop m] with k hk hY hkm
    rw [refReading_eq_lagProfile hN O t ℓ hkm hY] at hk
    rw [← lagProfile_one_eq hN k _ hY]
    exact lagProfile_one_pos_of (Dk hN 0 k) (Dk_positiveTransfer hN k) _
      (by positivity) hk
  · intro h
    filter_upwards [h, eventually_base_mem hN O hd, eventually_ge_atTop m] with k hk hY hkm
    rw [refReading_eq_lagProfile hN O t ℓ hkm hY]
    rw [← lagProfile_one_eq hN k _ hY] at hk
    exact lagProfile_pos_of_one (Dk hN 0 k) (Dk_positiveTransfer hN k) _ hk _

/-- **The pinned path with `hpos` replaced by lag-one positivity.** -/
theorem clay_canonical_lagOne (hN2 : 2 ≤ N) (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ}
    {m : ℕ} (hd : dySpacing N m < t) (hL : LagOnePos hN O t ℓ m)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0)
    {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀) (hW : DoublingClay2.WDelta2 N ℓ₀) :
    ClayRoutes.ClayContinuumPair hN (ExistenceReduce.zCan hN O t ℓ) 0
      (ExistenceReduce.zCan_refl hN O t ℓ)
      (ContinuumSep.pairBoundSep_of_diagBoundSep hN
        (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) 0
        (Renorm.connected_reflCompat hN (ExistenceReduce.zCan hN O t ℓ) 0
          (ExistenceReduce.zCan_refl hN O t ℓ)) hD) (5 * ℓ₀) :=
  ExistenceReduce.clay_canonical hN2 hN O
    ((dySpacing_pos (one_le_of_ne_zero hN) m).trans hd)
    ((refReading_pos_iff_lagOnePos hN O hd).mpr hL) hD hℓ hW

/-! ## E on the span of the reference cube -/

section Span

open MassGap.InfiniteLattice

/-- **Cauchy–Schwarz over a finite sum** in a reflection form:
`⟨∑ yᵢ, ∑ yᵢ⟩ ≤ n ∑ ⟨yᵢ, yᵢ⟩`, from `2⟨yᵢ, yⱼ⟩ ≤ ⟨yᵢ, yᵢ⟩ + ⟨yⱼ, yⱼ⟩`. -/
theorem form_sum_le {A : Type*} [AddCommGroup A] [Module ℝ A] (P : Transfer.ReflForm A) {n : ℕ}
    (y : Fin n → A) :
    P.form (∑ i, y i) (∑ i, y i) ≤ n * ∑ i, P.form (y i) (y i) := by
  have hL : ∀ z, P.form (∑ i, y i) z = ∑ i, P.form (y i) z := fun z =>
    map_sum (AddMonoidHom.mk' (fun x => P.form x z) (fun a b => P.form_add_left a b z)) y
      Finset.univ
  have hR : ∀ x, P.form x (∑ i, y i) = ∑ i, P.form x (y i) := fun x =>
    map_sum (AddMonoidHom.mk' (fun z => P.form x z)
      (fun a b => P.toPreForm.form_add_right x a b)) y Finset.univ
  have hpair : ∀ i j, 2 * P.form (y i) (y j) ≤ P.form (y i) (y i) + P.form (y j) (y j) := by
    intro i j
    have h := P.form_nonneg (y i + (-1 : ℝ) • y j)
    simp only [P.toPreForm.form_add_self, P.toPreForm.form_smul_right, P.form_smul_left] at h
    nlinarith
  calc P.form (∑ i, y i) (∑ i, y i) = ∑ i, ∑ j, P.form (y i) (y j) := by
        rw [hL]; exact Finset.sum_congr rfl (fun i _ => hR (y i))
    _ ≤ ∑ i, ∑ j, (P.form (y i) (y i) + P.form (y j) (y j)) / 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by linarith [hpair i j]))
    _ = n * ∑ i, P.form (y i) (y i) := by
        have e : ∀ i, ∑ j, (P.form (y i) (y i) + P.form (y j) (y j)) / 2
            = ((n : ℝ) * P.form (y i) (y i) + ∑ j, P.form (y j) (y j)) / 2 := by
          intro i
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_div, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Smearing is linear in the test function**, for a finite combination. Both sides are sums over
one box holding every support. -/
theorem smear_lincomb {a : ℝ} (ha : 0 < a) (F : C(Cfg N, ℝ)) (f : TestFn) {n : ℕ}
    (c : Fin n → ℝ) (g : Fin n → TestFn) (hf : ∀ y, f.1 y = ∑ i, c i * (g i).1 y) :
    smear a F f = ∑ i, c i • smear a F (g i) := by
  classical
  choose R M hRM using fun i => (g i).2
  obtain ⟨R0, M0, h0⟩ := f.2
  have hsi : ∀ i, box ⌈R i / a⌉₊
      ⊆ box ⌈R0 / a⌉₊ ∪ Finset.univ.biUnion (fun i => box ⌈R i / a⌉₊) := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => box ⌈R i / a⌉₊) (Finset.mem_univ i)).trans
      Finset.subset_union_right
  have hg : ∀ i, smear a F (g i)
      = ∑ x ∈ box ⌈R0 / a⌉₊ ∪ Finset.univ.biUnion (fun i => box ⌈R i / a⌉₊),
          (a ^ 4 * (g i).1 (site a x)) • transObs x F :=
    fun i => smear_eq_sum ha F (g i) (hRM i) (hsi i)
  rw [smear_eq_sum ha F f h0
    (s := box ⌈R0 / a⌉₊ ∪ Finset.univ.biUnion (fun i => box ⌈R i / a⌉₊))
    Finset.subset_union_left]
  simp only [hg, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.sum_smul, hf, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem Yv_mono1 (ρ : Renorm N) (k : ℕ) (O : LField (MassGap.SUN.SU N)) (f : TestFn) :
    Yv ρ k (ContinuumNontrivial.mono1 (O, f))
      = ρ.Z k O • smear (dySpacing N k) (O.sub (ρ.c k O)).1 f := by
  unfold Yv
  rw [ContinuumNontrivial.zmono_mono1, ContinuumNontrivial.prodSmear_mono1]

theorem Yv_mono1_lincomb (hN : N ≠ 0) (ρ : Renorm N) (k : ℕ) (O : LField (MassGap.SUN.SU N))
    (f : TestFn) {n : ℕ} (c : Fin n → ℝ) (g : Fin n → TestFn)
    (hf : ∀ y, f.1 y = ∑ i, c i * (g i).1 y) :
    Yv ρ k (ContinuumNontrivial.mono1 (O, f))
      = ∑ i, c i • Yv ρ k (ContinuumNontrivial.mono1 (O, g i)) := by
  simp only [Yv_mono1]
  rw [smear_lincomb (dySpacing_pos (one_le_of_ne_zero hN) k) _ f c g hf, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => smul_comm _ _ _)

/-- **Cauchy–Schwarz over a combination of test functions, at one step.** For a one-insertion
monomial whose test function is `∑ cᵢ gᵢ`, the reflected diagonal is at most `n ∑ cᵢ²` times the
diagonals of the `gᵢ`. -/
theorem latSkR_mono1_lincomb_le (hN : N ≠ 0) (ρ : Renorm N) (hR : ρ.ReflCompat 0) (k : ℕ)
    (O : LField (MassGap.SUN.SU N)) (f : TestFn) {n : ℕ} (c : Fin n → ℝ) (g : Fin n → TestFn)
    (hf : ∀ y, f.1 y = ∑ i, c i * (g i).1 y)
    (hg : ∀ i, Yv ρ k (ContinuumNontrivial.mono1 (O, g i))
      ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    latSkR hN ρ k (pairFam 0 (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f)))
      ≤ n * ∑ i, c i ^ 2 * latSkR hN ρ k
          (pairFam 0 (ContinuumNontrivial.mono1 (O, g i)) (ContinuumNontrivial.mono1 (O, g i))) := by
  let x : Fin n → ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :=
    fun i => ⟨_, hg i⟩
  have hS : ((∑ i, c i • x i :
      ↥(GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0)) : C(Cfg N, ℝ))
      = Yv ρ k (ContinuumNontrivial.mono1 (O, f)) := by
    rw [Yv_mono1_lincomb hN ρ k O f c g hf, Submodule.coe_sum]
    rfl
  have h1 : latSkR hN ρ k
      (pairFam 0 (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f)))
      = (Dk hN 0 k).form (∑ i, c i • x i) (∑ i, c i • x i) := by
    rw [latSkR_pairFam_eq hN ρ 0 hR, Dk_form, hS]
  have h2 : ∀ i, latSkR hN ρ k
      (pairFam 0 (ContinuumNontrivial.mono1 (O, g i)) (ContinuumNontrivial.mono1 (O, g i)))
      = (Dk hN 0 k).form (x i) (x i) := by
    intro i
    rw [latSkR_pairFam_eq hN ρ 0 hR, Dk_form]
  rw [h1]
  refine (form_sum_le (Dk hN 0 k).toReflForm (fun i => c i • x i)).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [h2 i]
  show (Dk hN 0 k).form (c i • x i) (c i • x i) = c i ^ 2 * (Dk hN 0 k).form (x i) (x i)
  rw [(Dk hN 0 k).form_smul_left, (Dk hN 0 k).toReflForm.toPreForm.form_smul_right]
  ring

/-- **A spatial dyadic translate has the same reflected diagonal**: the reflection in time commutes
with a translation that has no time component (`ireflObs_transObs`), and the state is translation
invariant. -/
theorem latSkR_spatial_shift (hN : N ≠ 0) (ρ : Renorm N) (hR : ρ.ReflCompat 0) {k m : ℕ}
    (hk : m ≤ k) (xs : ISite) (hxs : xs 0 = 0) (P : Mono N) :
    latSkR hN ρ k (pairFam 0 (Mono.shift (site (dySpacing N m) xs) P)
        (Mono.shift (site (dySpacing N m) xs) P))
      = latSkR hN ρ k (pairFam 0 P P) := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hz : scaleSite (2 ^ (k - m)) xs 0 = 0 := by simp [scaleSite, hxs]
  have hrefl : LatticeReflection.ireflSite 0 0 (scaleSite (2 ^ (k - m)) xs)
      = scaleSite (2 ^ (k - m)) xs := by
    funext j
    by_cases h : j = 0
    · subst h
      simp [LatticeReflection.ireflSite, hz]
    · simp [LatticeReflection.ireflSite, Function.update_of_ne h]
  rw [latSkR_pairFam_eq hN ρ 0 hR, latSkR_pairFam_eq hN ρ 0 hR, site_dySpacing N hk xs,
    ← Yv_shift ρ k ha _ P, ireflObs_transObs, hrefl, ← transObs_mul,
    ContinuumNontrivial.stateK_transObs]

/-- **A forward-time and spatial dyadic translate does not raise the reflected diagonal**
(`latSkR_spatial_shift`, `ContinuumSep.latSkR_pairFam_shift_self_le`). -/
theorem latSkR_shift_le (hN : N ≠ 0) (ρ : Renorm N) (hR : ρ.ReflCompat 0) {k m : ℕ}
    (hk : m ≤ k) (j : ℕ) (xs : ISite) (hxs : xs 0 = 0) (P : Mono N)
    (hY : Yv ρ k P ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0) :
    latSkR hN ρ k (pairFam 0 (Mono.shift (timeVec N m 0 j + site (dySpacing N m) xs) P)
        (Mono.shift (timeVec N m 0 j + site (dySpacing N m) xs) P))
      ≤ latSkR hN ρ k (pairFam 0 P P) := by
  rw [← ContinuumReconstruction.Mono.shift_shift, latSkR_spatial_shift hN ρ hR hk xs hxs]
  exact ContinuumSep.latSkR_pairFam_shift_self_le hN ρ 0 hR hk j P hY

theorem posTime_cube {t ℓ : ℝ} (ht : 0 < t) : PosTime 0 (ContinuumNontrivial.cubeTest t ℓ) := by
  refine ⟨t, ht, fun y hy => ?_⟩
  have hy' : ContinuumNontrivial.cubeInd t ℓ y ≠ 0 := hy
  exact ((Set.mem_of_indicator_ne_zero hy' : y ∈ ContinuumNontrivial.timeCube t ℓ) 0).1

/-- **E on the span of the reference cube, at the canonical normalisation.** If the reference
reading is eventually positive, then for every one-insertion monomial of the reference field whose
test function is `∑ᵢ cᵢ · (reference cube translated by dySpacing N m · (jᵢ e₀ + xsᵢ))`, with
`jᵢ ≥ 0` and `xsᵢ` spatial, the reflected diagonal at `zCan` is eventually at most `n ∑ cᵢ²`. -/
theorem diag_refSpan_le (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {t ℓ : ℝ} (ht : 0 < t)
    (hpos : ∀ᶠ k in atTop, 0 < ExistenceReduce.refReading hN O t ℓ k) (f : TestFn) {n m : ℕ}
    (c : Fin n → ℝ) (j : Fin n → ℕ) (xs : Fin n → ISite) (hxs : ∀ i, xs i 0 = 0)
    (hf : ∀ y, f.1 y = ∑ i, c i * ((ContinuumNontrivial.cubeTest t ℓ).translate
      (timeVec N m 0 (j i) + site (dySpacing N m) (xs i))).1 y) :
    ∀ᶠ k in atTop,
      latSkR hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) k
        (pairFam 0 (ContinuumNontrivial.mono1 (O, f)) (ContinuumNontrivial.mono1 (O, f)))
        ≤ n * ∑ i, c i ^ 2 := by
  have hR : (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)).ReflCompat 0 :=
    Renorm.connected_reflCompat hN _ 0 (ExistenceReduce.zCan_refl hN O t ℓ)
  have hv : ∀ i, 0 ≤ (timeVec N m 0 (j i) + site (dySpacing N m) (xs i)) 0 := by
    intro i
    have h1 : (timeVec N m 0 (j i) + site (dySpacing N m) (xs i)) 0
        = dySpacing N m * (j i : ℝ) := by
      simp [timeVec, site, axisVec, hxs i]
    rw [h1]
    exact mul_nonneg (dySpacing_pos (one_le_of_ne_zero hN) m).le (Nat.cast_nonneg _)
  have hmemg : ∀ᶠ k in atTop, ∀ i,
      Yv (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) k
        (ContinuumNontrivial.mono1 (O, (ContinuumNontrivial.cubeTest t ℓ).translate
          (timeVec N m 0 (j i) + site (dySpacing N m) (xs i))))
        ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0 :=
    Filter.eventually_all.mpr (fun i => by
      filter_upwards [eventually_smear_sub_mem (one_le_of_ne_zero hN) 0 O _
        ((posTime_cube ht).translate (hv i))] with k hk
      exact Yv_mem hN _ 0 k _ (fun _ r => hk r))
  have hmemr : ∀ᶠ k in atTop,
      Yv (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) k (ExistenceReduce.refMono O t ℓ)
        ∈ GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) 0 0 := by
    filter_upwards [eventually_smear_sub_mem (one_le_of_ne_zero hN) 0 O _ (posTime_cube ht)]
      with k hk
    exact Yv_mem hN _ 0 k _ (fun _ r => hk r)
  filter_upwards [hmemg, hmemr, hpos, eventually_ge_atTop m] with k hg hr hp hkm
  have hbound := latSkR_mono1_lincomb_le hN _ hR k O f c
    (fun i => (ContinuumNontrivial.cubeTest t ℓ).translate
      (timeVec N m 0 (j i) + site (dySpacing N m) (xs i))) hf hg
  have hle : ∀ i, latSkR hN (Renorm.connected hN (ExistenceReduce.zCan hN O t ℓ)) k
      (pairFam 0 (ContinuumNontrivial.mono1 (O, (ContinuumNontrivial.cubeTest t ℓ).translate
          (timeVec N m 0 (j i) + site (dySpacing N m) (xs i))))
        (ContinuumNontrivial.mono1 (O, (ContinuumNontrivial.cubeTest t ℓ).translate
          (timeVec N m 0 (j i) + site (dySpacing N m) (xs i))))) ≤ 1 := by
    intro i
    have e : ContinuumNontrivial.mono1 (O, (ContinuumNontrivial.cubeTest t ℓ).translate
          (timeVec N m 0 (j i) + site (dySpacing N m) (xs i)))
        = Mono.shift (timeVec N m 0 (j i) + site (dySpacing N m) (xs i))
            (ExistenceReduce.refMono O t ℓ) := rfl
    rw [e]
    exact (latSkR_shift_le hN _ hR hkm (j i) (xs i) (hxs i) _ hr).trans
      (ExistenceReduce.latSkR_zCan hN O t ℓ k hp).le
  refine hbound.trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_)) (Nat.cast_nonneg n)
  exact mul_le_of_le_one_right (sq_nonneg _) (hle i)

end Span

end MassGap.ExistencePos

#print axioms MassGap.ExistencePos.refReading_eq_lagProfile
#print axioms MassGap.ExistencePos.lagProfile_pos_of_one
#print axioms MassGap.ExistencePos.lagProfile_one_pos_of
#print axioms MassGap.ExistencePos.refReading_pos_iff_lagOnePos
#print axioms MassGap.ExistencePos.clay_canonical_lagOne
#print axioms MassGap.ExistencePos.form_sum_le
#print axioms MassGap.ExistencePos.smear_lincomb
#print axioms MassGap.ExistencePos.latSkR_mono1_lincomb_le
#print axioms MassGap.ExistencePos.latSkR_spatial_shift
#print axioms MassGap.ExistencePos.latSkR_shift_le
#print axioms MassGap.ExistencePos.diag_refSpan_le
