import Mathlib
import MassGap.CutSU
import MassGap.ObserverMoments

/-!
# The SU(N) capstone from the class moments

`CutSU.clayStatementAt_of_inputs'` takes, besides the class moments `hU : ClassMoments hN W
(SymPlaqClass N) t C`, the inputs `hW`, `hcube`, `hC0`, `hUE` and `hnt`. This module derives them:

* `symPlaq_cube_of_classMoments` — `CubeMomentBound` on `SymPlaqClass N` from `hU`
  (`ObserverMoments.cubeMomentBound_of_cubeMomentsAt`). In `ClayWiring` `hW`, `hcube` enter only
  through this statement (`symPlaq_cube`).
* `one_le_of_classMoments` — `1 ≤ C` from `hU` at the zeroth moment of `sym (plaqField q0)`.
* `unitCubeExpBound_of_cubeMomentsAt` — `UnitCubeExpBound` from `CubeMomentsAt` at the unit cube:
  `e^x ≤ 2 cosh x`, the cosh series summed in `C(Cfg N, ℝ)` and read through the state.
* `hnt_of_gram` — a non-zero vector of `HLs X w` orthogonal to the vacuum, from the Gram identity,
  `w ∅ = vac`, `TwoPointKernel` and `AFCoefficient`: the vector `w P` of one trace insertion smeared
  with a continuous bump at positive time.
* `obsX'`, `gapEx'`, `obsX'_gap`, `obsX'_SM` — `ClayWiring.obsX` and its companions built from `hU`.
* `clayStatementAt_of_inputs''` — `ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N)` from the
  hypotheses of `CutSU.clayStatementAt_of_inputs'` without `hW`, `hcube`, `hC0`, `hUE`, `hnt`.
-/

noncomputable section

namespace MassGap.SUInputs

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ClayStatement MassGap.ClayWiring Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The class moments give the cube bounds, `C ≥ 1` and the unit-cube exponential moment -/

section Moments

/-- `sym (plaqField q0)` is in the class. DERIVED: `q0` the `(0, 1)` plaquette at the origin. -/
theorem q0_mem :
    sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0) ∈ SymPlaqClass N :=
  ⟨ObserverEnergyMoments.q0, rfl⟩

/-- **`CubeMomentBound` on `SymPlaqClass N` from the class moments.** DERIVED: no numeral. -/
theorem symPlaq_cube_of_classMoments (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) :
    ∀ O ∈ SymPlaqClass N, CubeMomentBound hN W O :=
  fun _ hO => ObserverMoments.cubeMomentBound_of_cubeMomentsAt hN W (hU _ hO)

#print axioms symPlaq_cube_of_classMoments

/-- **The constant of the class moments is at least `1`**: the zeroth moment at `R = 0` is
`ν_k(1) = 1 ≤ C`.

DERIVED: `0` the moment and the cube; `1` the unit observable. -/
theorem one_le_of_classMoments (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) : 1 ≤ C := by
  obtain ⟨k, hk⟩ := (hU _ q0_mem).exists
  have h := hk 0 le_rfl 0
  simpa [(stateK hN k).map_one] using h

#print axioms one_le_of_classMoments

/-- `A⁻¹ s^{2n} · 81^{2n} A t^{-2n} C = C ((81 s/t)²)ⁿ` for `A ≠ 0`.

DERIVED: `81`, `2` as in `unitCubeExpBound_of_cubeMomentsAt`. -/
theorem moment_term_eq (A s t C : ℝ) (n : ℕ) (hA : A ≠ 0) :
    A⁻¹ * s ^ (2 * n) * ((81 : ℝ) ^ (2 * n) * (A / t ^ (2 * n) * C))
      = C * ((81 * s / t) ^ 2) ^ n := by
  rw [← pow_mul, div_pow, mul_pow]
  calc A⁻¹ * s ^ (2 * n) * ((81 : ℝ) ^ (2 * n) * (A / t ^ (2 * n) * C))
      = (A⁻¹ * A) * (C * ((81 : ℝ) ^ (2 * n) * s ^ (2 * n) / t ^ (2 * n))) := by ring
    _ = C * ((81 : ℝ) ^ (2 * n) * s ^ (2 * n) / t ^ (2 * n)) := by rw [inv_mul_cancel₀ hA, one_mul]

/-- **The unit-cube exponential moment from the cube moments.** At `R = 1`,
`ν_k(E_1^{2p}) ≤ 81^{2p} (2p)! t^{-2p} C`; with `s = t/162` and `e^x ≤ 2 cosh x`,
`ν_k(e^{s E_1}) ≤ 2 ∑_p s^{2p} ν_k(E_1^{2p})/(2p)! ≤ 2 C ∑_p ((81 s/t)²)^p`.

DERIVED: `81 = (2·1 + 1)⁴` the volume factor at the unit cube; `2` the even power and
`e^x ≤ 2 cosh x`. CHOSEN: `162 = 2 · 81`, so `81 s/t = 1/2`; any factor above `81` serves. -/
theorem unitCubeExpBound_of_cubeMomentsAt (hN : N ≠ 0) (W : ConfFlow N)
    {O : LField (MassGap.SUN.SU N)} {t C : ℝ} (ht : 0 < t) (h : CubeMomentsAt hN W O t C) :
    UnitCubeExpBound hN W O := by
  refine ⟨t / 162, 2 * (C * (1 - (81 * (t / 162) / t) ^ 2)⁻¹), div_pos ht (by norm_num),
    h.mono fun k hk => ?_⟩
  have hs : (0 : ℝ) < t / 162 := div_pos ht (by norm_num)
  have ht' : t ≠ 0 := ht.ne'
  set s : ℝ := t / 162 with hs_def
  set E : C(Cfg N, ℝ) := cubeSum (dySpacing N k) 1 (W.fieldMap k O).1 with hE
  set ν := stateK hN k with hν
  let f : ℕ → C(Cfg N, ℝ) := fun p => (((2 * p).factorial : ℝ)⁻¹) • (s • E) ^ (2 * p)
  have hfU : ∀ p U, f p U = (s * E U) ^ (2 * p) / ((2 * p).factorial : ℝ) := by
    intro p U
    simp only [f, ContinuousMap.smul_apply, ContinuousMap.pow_apply, smul_eq_mul]
    ring
  have hb : ∀ p, ‖f p‖ ≤ ‖s • E‖ ^ (2 * p) / ((2 * p).factorial : ℝ) := by
    intro p
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun U => ?_
    rw [hfU, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have hU := (s • E).norm_coe_le_norm U
    rw [ContinuousMap.smul_apply, smul_eq_mul, Real.norm_eq_abs] at hU
    gcongr
  have hsum : Summable f := Summable.of_norm_bounded (Real.hasSum_cosh ‖s • E‖).summable hb
  have hT := hsum.hasSum
  have hpt : ∀ U, Real.exp (s * E U) ≤ 2 * (∑' p, f p) U := by
    intro U
    have h1 := (ContinuousMap.evalCLM ℝ U).hasSum hT
    simp only [ContinuousMap.evalCLM_apply] at h1
    have h2 : HasSum (fun p => f p U) (Real.cosh (s * E U)) := by
      simpa only [hfU] using Real.hasSum_cosh (s * E U)
    rw [h1.unique h2, Real.cosh_eq]
    have := Real.exp_pos (-(s * E U))
    linarith
  have hmono : ν (expC (s • E)) ≤ ν ((2 : ℝ) • ∑' p, f p) := ν.mono fun U => by
    simp only [expC_apply, ContinuousMap.smul_apply, smul_eq_mul]
    exact hpt U
  let νh : C(Cfg N, ℝ) →+ ℝ :=
    { toFun := fun F => ν F, map_zero' := ν.map_zero, map_add' := ν.map_add }
  have hνT : HasSum (fun p => ν (f p)) (ν (∑' p, f p)) := hT.map νh ν.continuous
  have h81 : ((2 * (1 : ℝ) + 1) ^ 4) = 81 := by norm_num
  have hterm : ∀ p, ν (f p) ≤ C * ((81 * s / t) ^ 2) ^ p := by
    intro p
    have hfac : ((2 * p).factorial : ℝ) ≠ 0 := by positivity
    have e1 : f p = ((((2 * p).factorial : ℝ)⁻¹) * s ^ (2 * p)) • E ^ (2 * p) := by
      simp only [f, smul_pow, smul_smul]
    have hm := hk 1 zero_le_one p
    rw [h81] at hm
    rw [e1, ν.map_smul]
    calc (((2 * p).factorial : ℝ)⁻¹ * s ^ (2 * p)) * ν (E ^ (2 * p))
        ≤ (((2 * p).factorial : ℝ)⁻¹ * s ^ (2 * p))
            * ((81 : ℝ) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C)) :=
          mul_le_mul_of_nonneg_left hm
            (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hs.le _))
      _ = C * ((81 * s / t) ^ 2) ^ p := moment_term_eq _ _ _ _ _ hfac
  have hr0 : (0 : ℝ) ≤ (81 * s / t) ^ 2 := sq_nonneg _
  have hhalf : 81 * s / t = 1 / 2 := by
    rw [hs_def]
    field_simp
    ring
  have hr1 : (81 * s / t) ^ 2 < 1 := by
    rw [hhalf]
    norm_num
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left C
  have hle := hasSum_le hterm hνT hgeo
  calc ν (expC (s • E)) ≤ ν ((2 : ℝ) • ∑' p, f p) := hmono
    _ = 2 * ν (∑' p, f p) := ν.map_smul _ _
    _ ≤ 2 * (C * (1 - (81 * s / t) ^ 2)⁻¹) := by linarith

#print axioms unitCubeExpBound_of_cubeMomentsAt

end Moments

/-! ## 2. A non-zero vector orthogonal to the vacuum -/

section Nontrivial

/-- The centre `(λ, 0, 0, 0)` of the bump. DERIVED: `0` the time axis and the other coordinates. -/
def bumpC (lam : ℝ) : Fin 4 → ℝ := fun i => if i = 0 then lam else 0

/-- DERIVED: `0` the time axis. -/
theorem bumpC_zero (lam : ℝ) : bumpC lam 0 = lam := if_pos rfl

/-- DERIVED: `0` the sign of `λ`. -/
theorem abs_bumpC_le {lam : ℝ} (hl : 0 ≤ lam) (i : Fin 4) : |bumpC lam i| ≤ lam := by
  unfold bumpC
  split_ifs
  · rw [abs_of_nonneg hl]
  · rw [abs_zero]
    exact hl

/-- **The bump** `max 0 (λ/2 − ∑ᵢ |yᵢ − cᵢ|)`, `c = (λ, 0, 0, 0)`.

DERIVED: `0` the floor; `2` the radius `λ/2`. -/
def bumpF (lam : ℝ) (y : Fin 4 → ℝ) : ℝ := max 0 (lam / 2 - ∑ i, |y i - bumpC lam i|)

/-- DERIVED: `0` the floor. -/
theorem bumpF_nonneg (lam : ℝ) (y : Fin 4 → ℝ) : 0 ≤ bumpF lam y := le_max_left _ _

/-- Off the zero set of the bump each coordinate is within `λ/2` of the centre.

DERIVED: `0` the floor; `2` the radius. -/
theorem abs_sub_lt_of_bumpF_ne {lam : ℝ} {y : Fin 4 → ℝ} (h : bumpF lam y ≠ 0) (i : Fin 4) :
    |y i - bumpC lam i| < lam / 2 := by
  have hpos : 0 < lam / 2 - ∑ j, |y j - bumpC lam j| := by
    by_contra hn
    exact h (max_eq_left (not_lt.mp hn))
  have hi : |y i - bumpC lam i| ≤ ∑ j, |y j - bumpC lam j| :=
    Finset.single_le_sum (f := fun j => |y j - bumpC lam j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  linarith

/-- DERIVED: `2` the bound `λ/2 + λ ≤ 2λ`. -/
theorem abs_le_of_bumpF_ne {lam : ℝ} (hl : 0 ≤ lam) {y : Fin 4 → ℝ} (h : bumpF lam y ≠ 0)
    (i : Fin 4) : |y i| ≤ 2 * lam := by
  have h1 := abs_sub_lt_of_bumpF_ne h i
  have h2 := abs_bumpC_le hl i
  have h3 : |y i| ≤ |y i - bumpC lam i| + |bumpC lam i| := by
    have := abs_add_le (y i - bumpC lam i) (bumpC lam i)
    rwa [sub_add_cancel] at this
  linarith

/-- DERIVED: no numeral. -/
theorem continuous_bumpF (lam : ℝ) : Continuous (bumpF lam) := by
  unfold bumpF
  exact continuous_const.max (continuous_const.sub (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).sub continuous_const).abs))

/-- DERIVED: `2` as in `abs_le_of_bumpF_ne` and the radius. -/
theorem isTest_bumpF {lam : ℝ} (hl : 0 ≤ lam) : IsTest (bumpF lam) (2 * lam) (lam / 2) := by
  refine ⟨by linarith, fun y => ?_, fun y hy i => abs_le_of_bumpF_ne hl hy i⟩
  rw [abs_of_nonneg (bumpF_nonneg lam y)]
  have hS : 0 ≤ ∑ j, |y j - bumpC lam j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  exact max_le (by linarith) (by linarith)

/-- The bump as a test function. DERIVED: `2` as in `isTest_bumpF`. -/
def bumpT {lam : ℝ} (hl : 0 ≤ lam) : TestFn := ⟨bumpF lam, 2 * lam, lam / 2, isTest_bumpF hl⟩

/-- **One trace insertion smeared with the bump**, at positive time beyond `λ/2`.

DERIVED: `1` the length; `0` the time axis; `2` the margin `λ/2`. -/
def oneT {lam : ℝ} (hl : 0 < lam) : TSep 0 :=
  ⟨⟨1, fun _ => (trC, bumpT hl.le)⟩, fun _ => continuous_bumpF lam, lam / 2, half_pos hl,
    fun _ y hy => by
      have h := abs_sub_lt_of_bumpF_ne (lam := lam) (y := y) hy 0
      rw [bumpC_zero] at h
      linarith [(abs_lt.mp h).1],
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-- **The trace is reflection even**: each non-zero component has its index pattern `(μ, ν, μ, ν)`,
so the count of indices equal to `0` is even.

DERIVED: `0` the reflected axis; `1` the sign; `2`, `3` the slots. -/
theorem reflC_trC : reflC 0 trC = trC := by
  funext α
  unfold reflC trC
  by_cases h : α 2 = α 0 ∧ α 3 = α 1
  · rw [if_pos h, mul_one, Finset.card_filter, Fin.sum_univ_four, h.1, h.2]
    split_ifs <;> norm_num
  · rw [if_neg h, mul_zero]

#print axioms reflC_trC

/-- `Fin 2 ≃ Fin 1 ⊕ Fin 1`, `0 ↦ inl 0`, `1 ↦ inr 0`. DERIVED: `0`, `1` the points. -/
def twoEquiv : Fin 2 ≃ Fin 1 ⊕ Fin 1 where
  toFun i := if i = 0 then Sum.inl 0 else Sum.inr 0
  invFun x := Sum.elim (fun _ => 0) (fun _ => 1) x
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro x
    rcases x with a | a <;> fin_cases a <;> rfl

/-- DERIVED: `0` the time axis; `2` the length. -/
theorem pairT_oneT_comp {lam : ℝ} (hl : 0 < lam) :
    (pairT 0 (oneT hl).1 (oneT hl).1 ∘ (twoEquiv : Fin 2 ≃ Fin (oneT hl).1.1 ⊕ Fin (oneT hl).1.1))
      = fun i : Fin 2 => (trC, (![(bumpT hl.le).reflect 0, bumpT hl.le] : Fin 2 → TestFn) i) := by
  funext i
  fin_cases i
  · show (reflC 0 trC, (bumpT hl.le).reflect 0) = (trC, (bumpT hl.le).reflect 0)
    rw [reflC_trC]
  · rfl

/-- **`S(Θ P ∪ P)` is the trace two-point function** of the reflected bump and the bump.

DERIVED: `0` the time axis; `2` the length. -/
theorem kernT_oneT_eq (hN : N ≠ 0) (ρ : RenormMix N) {lam : ℝ} (hl : 0 < lam) :
    kernT hN ρ 0 (oneT hl) (oneT hl) = contTr hN ρ ![(bumpT hl.le).reflect 0, bumpT hl.le] := by
  unfold kernT contTr contT
  congr 1
  funext k
  exact (os3T hN ρ _ (Fin 2) (twoEquiv : Fin 2 ≃ Fin (oneT hl).1.1 ⊕ Fin (oneT hl).1.1)
    (pairT 0 (oneT hl).1 (oneT hl).1) k).symm.trans
    (congrArg (fun F : Fin 2 → TDatum => latT hN ρ k F) (pairT_oneT_comp hl))

#print axioms kernT_oneT_eq

/-- The lattice reading of `Θ∅ ∪ P` vanishes at every step: one connected field.

DERIVED: `0` the time axis and the value. -/
theorem latT_empty_oneT (hN : N ≠ 0) (ρ : RenormMix N) {lam : ℝ} (hl : 0 < lam) (k : ℕ) :
    latT hN ρ k (pairT 0 (emptyT 0).1 (oneT hl).1) = 0 := by
  haveI : IsEmpty (Fin (emptyT (0 : Fin 4)).1.1) := by
    show IsEmpty (Fin 0)
    infer_instance
  haveI : Unique (Fin (oneT hl).1.1) := by
    show Unique (Fin 1)
    infer_instance
  unfold latT
  refine Finset.sum_eq_zero fun b _ => mul_eq_zero_of_right _ ?_
  show (stateK hN k) (∏ i, smear (dySpacing N k) _ _) = 0
  rw [Fintype.prod_sum_type, Fintype.prod_empty, one_mul, Fintype.prod_unique]
  exact ContinuumNontrivial.stateK_smear_connected hN k _ _

/-- **`S(Θ∅ ∪ P) = 0`.** DERIVED: `0` the time axis and the value. -/
theorem kernT_empty_oneT (hN : N ≠ 0) (ρ : RenormMix N) {lam : ℝ} (hl : 0 < lam) :
    kernT hN ρ 0 (emptyT 0) (oneT hl) = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  unfold kernT contT
  have e : (fun k => latT hN ρ k (pairT 0 (emptyT 0).1 (oneT hl).1)) = fun _ => (0 : ℝ) :=
    funext (latT_empty_oneT hN ρ hl)
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

#print axioms kernT_empty_oneT

/-- The reflected bump and the bump are `λ`-separated in time.

DERIVED: `0` the time axis; `2` the radius. -/
theorem sepBy_bump {lam : ℝ} (hl : 0 < lam) :
    ContinuumSep.sepBy lam ((bumpT hl.le).reflect 0) (bumpT hl.le) := by
  intro x y hx hy
  refine ⟨0, ?_⟩
  have hx0 := abs_sub_lt_of_bumpF_ne (lam := lam) (y := reflR 0 x) hx 0
  have hy0 := abs_sub_lt_of_bumpF_ne (lam := lam) (y := y) hy 0
  rw [bumpC_zero] at hx0 hy0
  have hr0 : reflR 0 x 0 = -x 0 := by simp only [reflR, Function.update_self]
  rw [hr0] at hx0
  obtain ⟨a1, a2⟩ := abs_lt.mp hx0
  obtain ⟨b1, b2⟩ := abs_lt.mp hy0
  have hp : 0 < y 0 - x 0 := by linarith
  rw [abs_sub_comm, abs_of_pos hp]
  linarith

/-- On the supports, `λ ≤ |x − y| ≤ 8λ`.

DERIVED: `0` the time axis; `8 = 2 · 4`, each coordinate difference at most `4λ`
(`abs_le_of_bumpF_ne`) and `√4 = 2`; `2` the squares. -/
theorem eDist_bounds_of_bump {lam : ℝ} (hl : 0 < lam) {x y : Fin 4 → ℝ}
    (hx : bumpF lam (reflR 0 x) ≠ 0) (hy : bumpF lam y ≠ 0) :
    lam ≤ ContinuumNontrivial.eDist x y ∧ ContinuumNontrivial.eDist x y ≤ 8 * lam := by
  have hx0 := abs_sub_lt_of_bumpF_ne hx 0
  have hy0 := abs_sub_lt_of_bumpF_ne hy 0
  rw [bumpC_zero] at hx0 hy0
  have hr0 : reflR 0 x 0 = -x 0 := by simp only [reflR, Function.update_self]
  rw [hr0] at hx0
  obtain ⟨a1, a2⟩ := abs_lt.mp hx0
  obtain ⟨b1, b2⟩ := abs_lt.mp hy0
  have hxi : ∀ i, |x i| ≤ 2 * lam := fun i => by
    rw [← abs_reflR 0 x i]
    exact abs_le_of_bumpF_ne hl.le hx i
  have hyi : ∀ i, |y i| ≤ 2 * lam := abs_le_of_bumpF_ne hl.le hy
  constructor
  · have h1 : (x 0 - y 0) ^ 2 ≤ ∑ i, (x i - y i) ^ 2 :=
      Finset.single_le_sum (f := fun i => (x i - y i) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ 0)
    have h2 : lam ^ 2 ≤ (x 0 - y 0) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y 0 - x 0 - lam)
        (by linarith : (0 : ℝ) ≤ y 0 - x 0 + lam)]
    calc lam = Real.sqrt (lam ^ 2) := (Real.sqrt_sq hl.le).symm
      _ ≤ ContinuumNontrivial.eDist x y := Real.sqrt_le_sqrt (h2.trans h1)
  · have hb : ∀ i, (x i - y i) ^ 2 ≤ (4 * lam) ^ 2 := by
      intro i
      obtain ⟨p1, p2⟩ := abs_le.mp (hxi i)
      obtain ⟨q1, q2⟩ := abs_le.mp (hyi i)
      exact sq_le_sq' (by linarith) (by linarith)
    have hsum : ∑ i, (x i - y i) ^ 2 ≤ (8 * lam) ^ 2 := by
      calc ∑ i, (x i - y i) ^ 2 ≤ ∑ _i : Fin 4, (4 * lam) ^ 2 :=
            Finset.sum_le_sum fun i _ => hb i
        _ = (8 * lam) ^ 2 := by
            rw [Fin.sum_univ_four]
            ring
    calc ContinuumNontrivial.eDist x y ≤ Real.sqrt ((8 * lam) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = 8 * lam := Real.sqrt_sq (by linarith)

/-- **The two-point integral of the reflected bump and the bump is positive** when `G ≥ g₀ > 0` on
`[λ, 8λ]` and `G` is continuous on `(0, ∞)`: on the supports `G` agrees with the continuous
`G ∘ clamp`, and the integrand is continuous, compactly supported, non-negative and positive at
`(Θc, c)`.

DERIVED: `8` as in `eDist_bounds_of_bump`; `0` the time axis and the signs; `2` the support
radius. -/
theorem kernel_integral_pos {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Ioi 0)) {lam g₀ : ℝ}
    (hl : 0 < lam) (hg₀ : 0 < g₀) (hGb : ∀ r, lam ≤ r → r ≤ 8 * lam → g₀ ≤ G r) :
    0 < ∫ x, ∫ y, ((bumpT hl.le).reflect 0).1 x * (bumpT hl.le).1 y
      * G (ContinuumNontrivial.eDist x y) := by
  set cl : ℝ → ℝ := fun r => max lam (min r (8 * lam)) with hcl
  have hcl_mem : ∀ r, lam ≤ cl r ∧ cl r ≤ 8 * lam := fun r =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hcl_id : ∀ r, lam ≤ r → r ≤ 8 * lam → cl r = r := fun r h1 h2 => by
    simp only [hcl, min_eq_left h2, max_eq_right h1]
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hGc : Continuous (fun r => G (cl r)) :=
    hG.comp_continuous hclc (fun r => lt_of_lt_of_le hl (hcl_mem r).1)
  have hGpos : ∀ r, g₀ ≤ G (cl r) := fun r => hGb _ (hcl_mem r).1 (hcl_mem r).2
  set F : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ := fun z =>
    bumpF lam (reflR 0 z.1) * bumpF lam z.2 * G (cl (ContinuumNontrivial.eDist z.1 z.2)) with hF
  have hpt : ∀ x y, ((bumpT hl.le).reflect 0).1 x * (bumpT hl.le).1 y
      * G (ContinuumNontrivial.eDist x y) = F (x, y) := by
    intro x y
    show bumpF lam (reflR 0 x) * bumpF lam y * G (ContinuumNontrivial.eDist x y)
      = bumpF lam (reflR 0 x) * bumpF lam y * G (cl (ContinuumNontrivial.eDist x y))
    by_cases hx : bumpF lam (reflR 0 x) = 0
    · simp only [hx, zero_mul]
    by_cases hy : bumpF lam y = 0
    · simp only [hy, mul_zero, zero_mul]
    obtain ⟨h1, h2⟩ := eDist_bounds_of_bump hl hx hy
    rw [hcl_id _ h1 h2]
  have hrefl : Continuous (reflR (0 : Fin 4)) := continuous_id.update 0 (continuous_apply 0).neg
  have hEd : Continuous (fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) => ContinuumNontrivial.eDist z.1 z.2) := by
    unfold ContinuumNontrivial.eDist
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp continuous_fst).sub ((continuous_apply i).comp continuous_snd)).pow 2)
  have hFc : Continuous F :=
    (((continuous_bumpF lam).comp (hrefl.comp continuous_fst)).mul
      ((continuous_bumpF lam).comp continuous_snd)).mul (hGc.comp hEd)
  have hFs : HasCompactSupport F := by
    refine HasCompactSupport.intro ((isCompact_closedBall (0 : Fin 4 → ℝ) (2 * lam)).prod
      (isCompact_closedBall (0 : Fin 4 → ℝ) (2 * lam))) fun z hz => ?_
    by_contra hne
    apply hz
    have hx : bumpF lam (reflR 0 z.1) ≠ 0 := fun h => hne (by simp only [hF, h, zero_mul])
    have hy : bumpF lam z.2 ≠ 0 := fun h => hne (by simp only [hF, h, mul_zero, zero_mul])
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
      intro i
      rw [Real.norm_eq_abs, ← abs_reflR 0 z.1 i]
      exact abs_le_of_bumpF_ne hl.le hx i
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
      intro i
      rw [Real.norm_eq_abs]
      exact abs_le_of_bumpF_ne hl.le hy i
  have hFnn : ∀ z, 0 ≤ F z := fun z =>
    mul_nonneg (mul_nonneg (bumpF_nonneg _ _) (bumpF_nonneg _ _)) (hg₀.le.trans (hGpos _))
  have hrr : reflR 0 (reflR 0 (bumpC lam)) = bumpC lam := by
    funext j
    by_cases hj : j = 0
    · subst hj
      simp only [reflR, Function.update_self, neg_neg]
    · simp only [reflR, Function.update_of_ne hj]
  have hbc : bumpF lam (bumpC lam) = lam / 2 := by
    simp only [bumpF, sub_self, abs_zero, Finset.sum_const_zero, sub_zero]
    exact max_eq_right (half_pos hl).le
  have hz0 : F (reflR 0 (bumpC lam), bumpC lam) ≠ 0 := by
    simp only [hF, hrr, hbc]
    exact mul_ne_zero (mul_ne_zero (half_pos hl).ne' (half_pos hl).ne')
      (lt_of_lt_of_le hg₀ (hGpos _)).ne'
  have hint : MeasureTheory.Integrable F
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin 4 → ℝ)).prod MeasureTheory.volume) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hpos : 0 < ∫ z, F z
      ∂((MeasureTheory.volume : MeasureTheory.Measure (Fin 4 → ℝ)).prod MeasureTheory.volume) :=
    hFc.integral_pos_of_hasCompactSupport_nonneg_nonzero hFs (Pi.le_def.2 hFnn) hz0
  rw [MeasureTheory.integral_prod F hint] at hpos
  simp_rw [hpt]
  exact hpos

#print axioms kernel_integral_pos

/-- **A non-zero vector of `HLs X w` orthogonal to the vacuum**, from the Gram identity, `w ∅ = vac`,
`TwoPointKernel` and `AFCoefficient`. `AFCoefficient` gives `δ > 0` with `G ≥ g₀ > 0` on `[λ, 8λ]`,
`λ = δ/16`; for `P` one trace insertion smeared with the bump, `⟪vac, w P⟫ = S(Θ∅ ∪ P) = 0`
(the one-point function of a connected field) and `‖w P‖² = S(Θ P ∪ P) > 0`
(`reflC_trC`, `kernel_integral_pos`).

DERIVED: `2` the least colour count; `0` the time axis, the vanishing pairing and the zero vector;
`8` as in `eDist_bounds_of_bump`. CHOSEN: `16 = 2 · 8`, so `8λ = δ/2 < δ`; any factor above `8`
serves. -/
theorem hnt_of_gram (hN2 : 2 ≤ N) (hN : N ≠ 0) {D : Set (LField (MassGap.SUN.SU N))} {r : ℝ}
    (X : OSDataSLinked N D 0 r) (ρ : RenormMix N) (w : TSep 0 → X.base.H)
    (hin : ∀ P Q : TSep 0, inner ℂ (w P) (w Q) = (kernT hN ρ 0 P Q : ℂ))
    (hvac : w (emptyT 0) = X.base.vac) (G : ℝ → ℝ)
    (hK : TwoPointKernel hN ρ G) (hAF : AFCoefficient N G) :
    ∃ u ∈ HLs X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0 := by
  obtain ⟨δ, hδ, -, hb⟩ :=
    ContinuumNontrivial.af_bounds_on_interval (afShortDistance_of_coefficient hN2 hAF)
  have hl : 0 < δ / 16 := div_pos hδ (by norm_num)
  obtain ⟨g₀, g₁, hg₀, hG⟩ := hb (δ / 16) (8 * (δ / 16)) hl (by linarith) (by linarith)
  have hcont_r : Continuous ((bumpT hl.le).reflect 0).1 :=
    (continuous_bumpF (δ / 16)).comp (continuous_id.update 0 (continuous_apply 0).neg)
  have hkk : kernT hN ρ 0 (oneT hl) (oneT hl) ≠ 0 := by
    rw [kernT_oneT_eq hN ρ hl,
      hK.2 _ _ hcont_r (continuous_bumpF (δ / 16)) ⟨δ / 16, hl, sepBy_bump hl⟩]
    exact (kernel_integral_pos hK.1 hl hg₀ (fun r h1 h2 => (hG r h1 h2).1)).ne'
  refine ⟨w (oneT hl), Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨oneT hl, rfl⟩),
    ?_, ?_⟩
  · rw [← hvac, hin, kernT_empty_oneT hN ρ hl, Complex.ofReal_zero]
  · intro h0
    apply hkk
    have h := hin (oneT hl) (oneT hl)
    rw [h0, inner_zero_left] at h
    exact_mod_cast h.symm

#print axioms hnt_of_gram

end Nontrivial

/-! ## 3. The observer from the class moments -/

section Observer

/-- The transfer gap at step `0` that `RunSeed N` supplies, with the uniform bound from `hU`.

DERIVED: `0` the plane and the step. -/
theorem gapEx' (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ}
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hfar : WDeltaRun.RunSeed N) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube_of_classMoments hN W hU)) 0 hphys 0) ρ :=
  LocalLink.observerGapAt_of_runSeed hN2 hN hfar _ _ hphys 0

/-- **The observer at the field `sym (plaqField q0)`** from the class moments, with the gap of the
run seed: `ClayWiring.obsX` with `hcube`, `hC0`, `hUE` given by `symPlaq_cube_of_classMoments`,
`one_le_of_classMoments`, `unitCubeExpBound_of_cubeMomentsAt`.

DERIVED: `0` the plane and the step; `1` the window. -/
def obsX' (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) : OSDataSLinked N (SymPlaqClass N) 0 r :=
  observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
    (symPlaq_cube_of_classMoments hN W hU) ht (zero_le_one.trans (one_le_of_classMoments hN W hU))
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)) q0_mem
    (unitCubeExpBound_of_cubeMomentsAt hN W ht (hU _ q0_mem)) 0 hphys 0 one_pos
    (Classical.choose_spec (gapEx' hN2 hN W hU hphys hfar)).1
    (Classical.choose_spec (gapEx' hN2 hN W hU hphys hfar)).2.1
    (Classical.choose_spec (gapEx' hN2 hN W hU hphys hfar)).2.2 hNT

/-- **The Hamiltonian gap of the observer**, from its self-adjoint generator.

DERIVED: `0` the plane. -/
theorem obsX'_gap (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    HamiltonianGap (obsX' hN2 hN W ht hU hphys hNT hfar).base :=
  hamiltonianGap_of_selfAdjoint _
    (observer_generator_isSelfAdjoint hN (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube_of_classMoments hN W hU)) 0
      (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys 0))

/-- **The observer's functional is `schwSFM`**, by definition. DERIVED: no numeral. -/
theorem obsX'_SM (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      (obsX' hN2 hN W ht hU hphys hNT hfar).SM O g
        = schwSFM hN W (SymPlaqClass N) (symPlaq_refl N) O g :=
  fun _ _ _ _ => rfl

/-- **The observer carries its Hilbert space** (`ClayStatement.obsGen_observer`).

DERIVED: `0` the plane and the step; `1` the window. -/
theorem obsX'_obsGen (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N) {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) {r : ℝ}
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N) :
    ObsGen hN W (SymPlaqClass N) (symPlaq_refl N) (obsX' hN2 hN W ht hU hphys hNT hfar) :=
  obsGen_observer hN W (symPlaq_refl N) (symPlaq_nonneg hN)
    (symPlaq_cube_of_classMoments hN W hU) ht (zero_le_one.trans (one_le_of_classMoments hN W hU))
    hU (O := sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)) q0_mem
    (unitCubeExpBound_of_cubeMomentsAt hN W ht (hU _ q0_mem)) 0 hphys 0 one_pos
    (Classical.choose_spec (gapEx' hN2 hN W hU hphys hfar)).1
    (Classical.choose_spec (gapEx' hN2 hN W hU hphys hfar)).2.1
    (Classical.choose_spec (gapEx' hN2 hN W hU hphys hfar)).2.2 hNT

end Observer

/-! ## 4. The capstone -/

section Capstone

/-- **`ClayStatementAt` from the hypotheses of `CutSU.clayStatementAt_of_inputs'` without `hW`,
`hcube`, `hC0`, `hUE`, `hnt`.** The observer is `obsX'`; `hnt` is `hnt_of_gram` from `hL`, `hK`,
`hAF`; the cut-off convergence is `CutSU.cut_of_classMoments`.

DERIVED: `2` the least colour count; `0` the plane; `8`, `4` as in `ScalarTie`. -/
theorem clayStatementAt_of_inputs'' (hN2 : 2 ≤ N) (hN : N ≠ 0) (W : ConfFlow N)
    {t C : ℝ} (ht : 0 < t)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) 0 r)
    (hfar : WDeltaRun.RunSeed N)
    {B : Type} [Fintype B] [DecidableEq B] (op : B → LField (MassGap.SUN.SU N)) (m : Idx4 → B → ℝ)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, Z k (O.refl 0) = Z k O)
    (hD : ContinuumSep.DiagBoundSep hN (Renorm.connected hN Z) 0)
    (hRie : CoefRiemann m) (b0 : B) (κ : ℝ) (htr : ∀ b, coefC m trC b = if b = b0 then κ else 0)
    (hop : op b0 = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0))
    (hZtie : Tendsto (fun k => κ * Z k (op b0) * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)))
    (h0 : OS0Own hN op Z) (hTC : TransContT hN (mixOfZ B op m Z))
    (hCov : TensorCov hN (mixOfZ B op m Z))
    (G : ℝ → ℝ) (hK : TwoPointKernel hN (mixOfZ B op m Z) G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT hN (mixOfZ B op m Z)) (hND : TensorNondeg hN (mixOfZ B op m Z))
    (w : TSep 0 → (obsX' hN2 hN W ht hU hphys hNT hfar).base.H)
    (hL : LinkHS hN W (SymPlaqClass N) (symPlaq_refl N)
      (obsX' hN2 hN W ht hU hphys hNT hfar) (mixOfZ B op m Z) w)
    (Cs : Composites N)
    (wC : TSepG Cs.Ix 0 → (obsX' hN2 hN W ht hU hphys hNT hfar).base.H)
    (hCT : ∃ (Mb : Idx4 → B → ℝ) (Zc : ℕ → Idx4 → Idx4 → ℝ),
      ChannelTie (mixOfZ B op m Z) Mb Zc ∧ TopNorm N Zc)
    (hWard : WardT hN (mixOfZ B op m Z)) (hCD : CompData Cs) (hCO : CompOS hN Cs)
    (hLC : LinkC hN (obsX' hN2 hN W ht hU hphys hNT hfar) Cs wC)
    (hTI : TIn (mixOfZ B op m Z) Cs (obsX' hN2 hN W ht hU hphys hNT hfar) w wC) :
    ClayStatementAt hN2 W (SymPlaqClass N) (symPlaq_refl N) :=
  have hConv := sepConv_mixOfZ hN op m Z hZ hD
  clayStatementAt_of_link hN2 W (SymPlaqClass N) (symPlaq_refl N)
    (obsX' hN2 hN W ht hU hphys hNT hfar) (mixOfZ B op m Z) G w
    (obsX'_SM hN2 hN W ht hU hphys hNT hfar)
    (obsX'_gap hN2 hN W ht hU hphys hNT hfar)
    (riemann_mixOfZ op m Z hRie)
    (scalarTie_mixOfZ op m Z b0 κ htr hop hZtie)
    hConv (os0Sep_mixOfZ hN op m Z hZ hD h0) (os1Sep_mixOfZ hN op m Z hZ hD hTC) hCov
    (linkTS_of_hs hN W (SymPlaqClass N) (symPlaq_refl N) _ (mixOfZ B op m Z) w hConv hL)
    (hnt_of_gram hN2 hN _ (mixOfZ B op m Z) w hL.1 hL.2.2.1 G hK hAF) hK hAF hNG hND
    ⟨uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube_of_classMoments hN W hU),
      CutSU.cut_of_classMoments hN W ht (zero_le_one.trans (one_le_of_classMoments hN W hU)) hU⟩
    Cs wC hCT hWard hCD hCO hLC hTI (obsX'_obsGen hN2 hN W ht hU hphys hNT hfar)

end Capstone

end MassGap.SUInputs

end

#print axioms MassGap.SUInputs.one_le_of_classMoments
#print axioms MassGap.SUInputs.unitCubeExpBound_of_cubeMomentsAt
#print axioms MassGap.SUInputs.hnt_of_gram
#print axioms MassGap.SUInputs.obsX'_gap
#print axioms MassGap.SUInputs.clayStatementAt_of_inputs''
