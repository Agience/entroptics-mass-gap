import Mathlib
import MassGap.ObserverOS
import MassGap.ObserverEnergyCoarseN

noncomputable section

/-!
# MassGap.ObserverOSGrowth — the growth condition of the observer's energy-density theory from one cube

`ObserverOS.os0_factorial` bounds the Schwinger functions of the energy density `energy0` on each
cube `[-R, R]⁴` by a constant that depends on the cube. Here the dependence is removed: the moments of
the energy in any cube are bounded by those of the energy in the unit cube `[-1, 1]⁴`, with a factor
polynomial in `R`, at every step. With one exponential moment of the unit cube this gives
`ObserverOS.TemperedGrowth`.

## Covering by lattice translates of one cube

At spacing `a` let `L = ⌊R/a⌋₊` and `l = ⌊1/a⌋₊`. The sites of `[-R, R]⁴` are the lattice box
`[-L, L]⁴` (`cubeSum_le_boxSum`, `boxSum_le_cubeSum`). Every site `x` of the box `[-L, L]⁴` is `y + z`
with `z` in `[-l, l]⁴` and `y = x - z` in `[-(L + l), L + l]⁴`, for each of the `(2l + 1)⁴` choices of
`z`. For a non-negative reading `F` this gives the covering inequality (`card_mul_boxSum_le`)

`(2l + 1)⁴ · boxSum L F ≤ ∑_{y ∈ [-(L+l), L+l]⁴} T_y (boxSum l F)`,

an average of lattice translates of one unit-cube energy. Minkowski's inequality in `L^{2p}`
(`ObserverEnergyCoarseN.state_pow_sum_le`) and the translation invariance of the periodic Wilson state
(`ContinuumNontrivial.stateK_transObs`) bound the `2p`-th moment of the right side by
`(2(L + l) + 1)^{8p}` times the unit-cube moment, and `2(L + l) + 1 ≤ (2R + 1)(2l + 1)` since
`L ≤ R/a < R (l + 1)` (`box_ratio_le`). Hence (`state_cubeSum_pow_le`), at every step,

`ν_k(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} ν_k(E_1^{2p})`,

`E_R = cubeSum a_k R (O ∘ V_k)`. The constant is `1`; nothing depends on the step.

## E reduces to one cube

`cubeMomentBound_of_unit`: bounded moments of the unit-cube energy give `CubeMomentBound` at every
cube. `UnitCubeExpBound`: one exponential moment of the unit-cube energy. It follows from
`CubeExpBound` (`unitCubeExpBound_of_cubeExpBound`) and gives every cube moment with an explicit
`R`-dependence (`cubeMoments_of_unitExp`).

## The growth condition

`abs_contSF_energy0_growth`: with `UnitCubeExpBound` for a non-negative field `O` of the class,
`|S_n(g₁, …, gₙ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ Mᵢ (2Rᵢ + 1)⁴` for every `n` and every family of test
functions with `|gᵢ| ≤ Mᵢ` supported in `[-Rᵢ, Rᵢ]⁴`, with `t, C` fixed by the unit cube.
`temperedGrowth_energy0` is `ObserverOS.TemperedGrowth` with `α = 1 + C`, `γ = 8 (1 + t⁻¹)²`, `β = 2`
(`(2n)! ≤ 4ⁿ (n!)²`, `n ≤ 2ⁿ`).

The norm is the sup norm times the support volume, `‖g‖_∞ (2R + 1)⁴`. A test function decaying faster
than `|y|^{-4-δ}` splits into shells `2^j ≤ |y| < 2^{j+1}` whose norms `sup_{shell} |g| · 2^{4j}` are
summable; that summed norm is a weighted sup (Schwartz) seminorm, the norm the Osterwalder–Schrader
growth condition asks for.
-/

namespace MassGap.ObserverOSGrowth

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyBox
  MassGap.ObserverOS Filter
open scoped Topology

/-! ## 1. Lattice boxes and physical cubes -/

section Boxes

/-- **Membership in the lattice box `[-K, K]⁴`** is a bound on every coordinate.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem mem_box_iff (K : ℕ) (x : ISite) : x ∈ box K ↔ ∀ i, |x i| ≤ (K : ℤ) := by
  unfold box
  rw [Fintype.mem_piFinset]
  refine forall_congr' (fun i => ?_)
  rw [Finset.mem_Icc, abs_le]

#print axioms mem_box_iff

/-- The lattice boxes increase with the radius.

DERIVED: no numeral. -/
theorem box_mono {K K' : ℕ} (h : K ≤ K') : box K ⊆ box K' := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  intro i
  exact (hx i).trans (by exact_mod_cast h)

#print axioms box_mono

/-- **A site in the physical cube `[-R, R]⁴` lies in the lattice box `[-⌊R/a⌋, ⌊R/a⌋]⁴`.**

DERIVED: `0` is the sign of `a` and of `R`. -/
theorem mem_box_floor {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) {x : ISite}
    (hx : ∀ i, |site a x i| ≤ R) : x ∈ box ⌊R / a⌋₊ := by
  rw [mem_box_iff]
  intro i
  have h1 : |a * (x i : ℝ)| ≤ R := hx i
  rw [abs_mul, abs_of_pos ha] at h1
  have h2 : |(x i : ℝ)| ≤ R / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact h1
  have h3 : |x i| ≤ ⌊R / a⌋ := Int.le_floor.mpr (by rw [Int.cast_abs]; exact h2)
  rw [← Int.natCast_floor_eq_floor (div_nonneg hR ha.le)] at h3
  exact h3

#print axioms mem_box_floor

/-- **A site of the lattice box `[-⌊R/a⌋, ⌊R/a⌋]⁴` lies in the physical cube `[-R, R]⁴`.**

DERIVED: `0` is the sign of `a` and of `R`; `4` in `Fin 4` is the spacetime dimension. -/
theorem site_le_of_mem_box_floor {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) {x : ISite}
    (hx : x ∈ box ⌊R / a⌋₊) (i : Fin 4) : |site a x i| ≤ R := by
  rw [mem_box_iff] at hx
  have h1 : ((|x i| : ℤ) : ℝ) ≤ ((⌊R / a⌋₊ : ℤ) : ℝ) := by exact_mod_cast hx i
  rw [Int.cast_abs, Int.cast_natCast] at h1
  have h2 : (⌊R / a⌋₊ : ℝ) ≤ R / a := Nat.floor_le (div_nonneg hR ha.le)
  have h3 : |(x i : ℝ)| ≤ R / a := h1.trans h2
  rw [le_div_iff₀ ha] at h3
  show |a * (x i : ℝ)| ≤ R
  rw [abs_mul, abs_of_pos ha]
  linarith [mul_comm a |(x i : ℝ)|]

#print axioms site_le_of_mem_box_floor

variable {N : ℕ}

/-- **The energy of a lattice box**: `∑_{x ∈ [-K, K]⁴} F ∘ T_x`.

DERIVED: `4` is the spacetime dimension. -/
def boxSum (K : ℕ) (F : C(Cfg N, ℝ)) : C(Cfg N, ℝ) := ∑ x ∈ box K, transObs x F

/-- DERIVED: no numeral. -/
theorem boxSum_apply (K : ℕ) (F : C(Cfg N, ℝ)) (U : Cfg N) :
    boxSum K F U = ∑ x ∈ box K, F (transConf x U) := by
  unfold boxSum
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, transObs_apply]

/-- DERIVED: `0` the sign. -/
theorem boxSum_nonneg (K : ℕ) {F : C(Cfg N, ℝ)} (hF : ∀ U, 0 ≤ F U) (U : Cfg N) :
    0 ≤ boxSum K F U := by
  rw [boxSum_apply]
  exact Finset.sum_nonneg (fun x _ => hF _)

#print axioms boxSum_nonneg

/-- **The cube energy is at most the energy of the box `[-⌊R/a⌋, ⌊R/a⌋]⁴`**, for `F ≥ 0`.

DERIVED: `0` is the sign of `a`, of `R` and of `F`; `1` the indicator on the cube. -/
theorem cubeSum_le_boxSum {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (F : C(Cfg N, ℝ))
    (hF : ∀ U, 0 ≤ F U) (U : Cfg N) : cubeSum a R F U ≤ boxSum ⌊R / a⌋₊ F U := by
  classical
  rw [cubeSum_apply, boxSum_apply]
  have e : ∑ x ∈ box ⌈R / a⌉₊, cubeInd R (site a x) * F (transConf x U)
      = ∑ x ∈ (box ⌈R / a⌉₊).filter (fun x => ∀ i, |site a x i| ≤ R), F (transConf x U) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold cubeInd
    split_ifs <;> simp
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => hF _)
  exact mem_box_floor ha hR (Finset.mem_filter.mp hx).2

#print axioms cubeSum_le_boxSum

/-- **The energy of the box `[-⌊R/a⌋, ⌊R/a⌋]⁴` is at most the cube energy**, for `F ≥ 0`.

DERIVED: `0` is the sign of `a`, of `R` and of `F`; `1` the indicator on the cube. -/
theorem boxSum_le_cubeSum {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (F : C(Cfg N, ℝ))
    (hF : ∀ U, 0 ≤ F U) (U : Cfg N) : boxSum ⌊R / a⌋₊ F U ≤ cubeSum a R F U := by
  rw [cubeSum_apply, boxSum_apply]
  have e : ∑ x ∈ box ⌊R / a⌋₊, F (transConf x U)
      = ∑ x ∈ box ⌊R / a⌋₊, cubeInd R (site a x) * F (transConf x U) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have h1 : cubeInd R (site a x) = 1 := by
      unfold cubeInd
      rw [if_pos (fun i => site_le_of_mem_box_floor ha hR hx i)]
    rw [h1, one_mul]
  rw [e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (box_mono (Nat.floor_le_ceil _))
    (fun x _ _ => mul_nonneg (cubeInd_nonneg _ _) (hF _))

#print axioms boxSum_le_cubeSum

end Boxes

/-! ## 2. The covering inequality -/

section Cover

variable {N : ℕ}

/-- **Covering a box by translates of a smaller box.** For `F ≥ 0`,
`(2l + 1)⁴ · boxSum L F ≤ ∑_{y ∈ [-(L+l), L+l]⁴} T_y (boxSum l F)`: for each `z ∈ [-l, l]⁴` the map
`x ↦ x - z` carries `[-L, L]⁴` injectively into `[-(L+l), L+l]⁴`, and `F ∘ T_x = F ∘ T_{(x-z)+z}`.

DERIVED: `2`, `1`, `4` are `card_box`'s count `(2l + 1)⁴`; `0` the sign of `F`. -/
theorem card_mul_boxSum_le (L l : ℕ) (F : C(Cfg N, ℝ)) (hF : ∀ U, 0 ≤ F U) (U : Cfg N) :
    ((2 * l + 1) ^ 4 : ℝ) * boxSum L F U
      ≤ ∑ y ∈ box (L + l), boxSum l F (transConf y U) := by
  classical
  have hshift : ∀ z ∈ box l,
      boxSum L F U ≤ ∑ y ∈ box (L + l), F (transConf (y + z) U) := by
    intro z hz
    rw [boxSum_apply]
    have hinj : Set.InjOn (fun x : ISite => x - z) (box L) := by
      intro x _ y _ h
      exact sub_left_injective h
    calc ∑ x ∈ box L, F (transConf x U)
        = ∑ y ∈ (box L).image (fun x : ISite => x - z), F (transConf (y + z) U) := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [sub_add_cancel]
      _ ≤ ∑ y ∈ box (L + l), F (transConf (y + z) U) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) (fun _ _ _ => hF _)
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          rw [mem_box_iff] at hx hz ⊢
          intro i
          have h1 := abs_sub (x i) (z i)
          have h2 := hx i
          have h3 := hz i
          simp only [Pi.sub_apply]
          push_cast
          linarith
  have hsum : ((2 * l + 1) ^ 4 : ℝ) * boxSum L F U = ∑ _z ∈ box l, boxSum L F U := by
    rw [Finset.sum_const, card_box, nsmul_eq_mul]
    norm_num
  rw [hsum]
  calc ∑ _z ∈ box l, boxSum L F U
      ≤ ∑ z ∈ box l, ∑ y ∈ box (L + l), F (transConf (y + z) U) := Finset.sum_le_sum hshift
    _ = ∑ y ∈ box (L + l), ∑ z ∈ box l, F (transConf (y + z) U) := Finset.sum_comm
    _ = ∑ y ∈ box (L + l), boxSum l F (transConf y U) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [boxSum_apply]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        exact (congrArg (fun G : C(Cfg N, ℝ) => G U) (transObs_transObs y z F)).symm

#print axioms card_mul_boxSum_le

/-- **The covering ratio**: `2(⌊R/a⌋ + ⌊1/a⌋) + 1 ≤ (2R + 1)(2⌊1/a⌋ + 1)`, since
`⌊R/a⌋ ≤ R/a < R (⌊1/a⌋ + 1)`.

DERIVED: `2`, `1` are the box side `2K + 1`; `0` the sign of `a` and of `R`. -/
theorem box_ratio_le {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    2 * ((⌊R / a⌋₊ + ⌊1 / a⌋₊ : ℕ) : ℝ) + 1 ≤ (2 * R + 1) * (2 * (⌊1 / a⌋₊ : ℝ) + 1) := by
  have hL : (⌊R / a⌋₊ : ℝ) ≤ R / a := Nat.floor_le (div_nonneg hR ha.le)
  have hl : 1 / a < (⌊1 / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hRa : R / a ≤ R * ((⌊1 / a⌋₊ : ℝ) + 1) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hl.le hR
  have hl0 : (0 : ℝ) ≤ (⌊1 / a⌋₊ : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_nonneg hR hl0]

#print axioms box_ratio_le

/-- **The moments of the energy in any cube from those of the unit cube**: at every step `k` and
spacing `a > 0`, for `F ≥ 0`, `R ≥ 0` and every `p`,
`ν_k(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} ν_k(E_1^{2p})`, `E_R = cubeSum a R F`. The covering inequality,
Minkowski's inequality in `L^{2p}` (`ObserverEnergyCoarseN.state_pow_sum_le` at unit weights), the
translation invariance of `stateK` and the covering ratio.

DERIVED: `0` is the excluded colour count, the sign of `a`, `R`, `F` and the moment `p = 0`; `1` the
unit cube and the unit weights; `2` makes the power even and with `1` is the box side; `4` the
spacetime dimension. -/
theorem state_cubeSum_pow_le {N : ℕ} (hN : N ≠ 0) (k : ℕ) {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (F : C(Cfg N, ℝ)) (hF : ∀ U, 0 ≤ F U) (p : ℕ) :
    stateK hN k (cubeSum a R F ^ (2 * p))
      ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * stateK hN k (cubeSum a 1 F ^ (2 * p)) := by
  rcases p with _ | q
  · simp
  have hm : 2 * (q + 1) = 2 * q + 2 := by ring
  rw [hm]
  set L := ⌊R / a⌋₊ with hLdef
  set l := ⌊1 / a⌋₊ with hldef
  set X : C(Cfg N, ℝ) := boxSum l F with hXdef
  set c : ℝ := ((2 * l + 1) ^ 4 : ℝ) with hcdef
  have hc : 0 < c := by positivity
  have hX0 : ∀ U, 0 ≤ X U := fun U => boxSum_nonneg l hF U
  -- the covering, pointwise
  have hcov : stateK hN k ((c • cubeSum a R F) ^ (2 * q + 2))
      ≤ stateK hN k ((∑ y ∈ box (L + l), transObs y X) ^ (2 * q + 2)) := by
    refine (stateK hN k).mono (fun U => ?_)
    simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.coe_sum, Finset.sum_apply, transObs_apply]
    have h1 := cubeSum_le_boxSum ha hR F hF U
    have h2 := card_mul_boxSum_le L l F hF U
    have h0 := cubeSum_nonneg a R hF U
    refine pow_le_pow_left₀ (mul_nonneg hc.le h0) ?_ _
    calc c * cubeSum a R F U ≤ c * boxSum L F U := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ _ := h2
  rw [smul_pow, (stateK hN k).map_smul] at hcov
  -- Minkowski with unit weights and translation invariance
  have hmink := MassGap.ObserverEnergyCoarseN.state_pow_sum_le (stateK hN k) (box (L + l))
    (fun y => transObs y X) (fun _ => (1 : ℝ)) (fun _ _ => one_pos) q
    (D := stateK hN k (X ^ (2 * q + 2)))
    (fun y _ => by
      rw [one_pow, mul_one, ← transObs_pow, MassGap.ContinuumNontrivial.stateK_transObs])
  rw [Finset.sum_const, card_box, nsmul_eq_mul, mul_one] at hmink
  -- the unit box inside the unit cube
  have hX1 : stateK hN k (X ^ (2 * q + 2)) ≤ stateK hN k (cubeSum a 1 F ^ (2 * q + 2)) := by
    refine (stateK hN k).mono (fun U => ?_)
    simp only [ContinuousMap.pow_apply]
    exact pow_le_pow_left₀ (hX0 U) (boxSum_le_cubeSum ha zero_le_one F hF U) _
  -- the ratio
  have hratio : (((2 * (L + l) + 1) ^ 4 : ℕ) : ℝ) ≤ (2 * R + 1) ^ 4 * c := by
    have h := box_ratio_le ha hR
    rw [← hLdef, ← hldef] at h
    have h0 : (0 : ℝ) ≤ 2 * ((L + l : ℕ) : ℝ) + 1 := by positivity
    calc (((2 * (L + l) + 1) ^ 4 : ℕ) : ℝ) = (2 * ((L + l : ℕ) : ℝ) + 1) ^ 4 := by push_cast; ring
      _ ≤ ((2 * R + 1) * (2 * (l : ℝ) + 1)) ^ 4 := pow_le_pow_left₀ h0 h 4
      _ = (2 * R + 1) ^ 4 * c := by rw [mul_pow, hcdef]
  have hB0 : 0 ≤ stateK hN k (cubeSum a 1 F ^ (2 * q + 2)) :=
    (stateK hN k).nonneg _ (fun U => by
      rw [ContinuousMap.pow_apply]; exact (even_two_mul (q + 1)).pow_nonneg _)
  have hcm : 0 < c ^ (2 * q + 2) := pow_pos hc _
  have hfin : c ^ (2 * q + 2) * stateK hN k (cubeSum a R F ^ (2 * q + 2))
      ≤ c ^ (2 * q + 2) * (((2 * R + 1) ^ 4) ^ (2 * q + 2)
          * stateK hN k (cubeSum a 1 F ^ (2 * q + 2))) := by
    calc c ^ (2 * q + 2) * stateK hN k (cubeSum a R F ^ (2 * q + 2))
        ≤ stateK hN k (X ^ (2 * q + 2)) * (((2 * (L + l) + 1) ^ 4 : ℕ) : ℝ) ^ (2 * q + 2) :=
          hcov.trans hmink
      _ ≤ stateK hN k (cubeSum a 1 F ^ (2 * q + 2)) * ((2 * R + 1) ^ 4 * c) ^ (2 * q + 2) :=
          mul_le_mul hX1 (pow_le_pow_left₀ (Nat.cast_nonneg _) hratio _)
            (pow_nonneg (Nat.cast_nonneg _) _) hB0
      _ = c ^ (2 * q + 2) * (((2 * R + 1) ^ 4) ^ (2 * q + 2)
            * stateK hN k (cubeSum a 1 F ^ (2 * q + 2))) := by rw [mul_pow]; ring
  exact le_of_mul_le_mul_left hfin hcm

#print axioms state_cubeSum_pow_le

end Cover

/-! ## 3. E from one cube -/

section OneCube

variable {N : ℕ}

/-- **Bounded moments of the unit-cube energy**: for every `p`, `ν_k(E_1^{2p})` is bounded eventually,
`E_1 = cubeSum a_k 1 (O ∘ V_k)`.

DERIVED: `1` is the unit cube; `2` makes the power even. -/
def UnitCubeMomentBound (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop,
    stateK hN k (cubeSum (dySpacing N k) 1 (W.fieldMap k O).1 ^ (2 * p)) ≤ C

/-- **E at every cube from E at the unit cube**, for a non-negative field: the bound at `[-R, R]⁴`
is `((2R + 1)⁴)^{2p}` times the unit-cube bound (`state_cubeSum_pow_le`).

DERIVED: `0` is the excluded colour count, the lower end of `R` and the sign of the field; `1`, `2`,
`4` as in `state_cubeSum_pow_le`. -/
theorem cubeMomentBound_of_unit (hN : N ≠ 0) (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)}
    (hO : ∀ U, 0 ≤ O.1 U) (h : UnitCubeMomentBound hN W O) : CubeMomentBound hN W O := by
  intro R hR p
  obtain ⟨C, hC⟩ := h p
  refine ⟨((2 * R + 1) ^ 4) ^ (2 * p) * C, hC.mono (fun k hk => ?_)⟩
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hO (W.V k U)
  exact (state_cubeSum_pow_le hN k ha hR _ hF p).trans
    (mul_le_mul_of_nonneg_left hk (pow_nonneg (pow_nonneg (by linarith) 4) _))

#print axioms cubeMomentBound_of_unit

/-- `CubeMomentBound` gives the unit-cube bound: the converse of `cubeMomentBound_of_unit`.

DERIVED: `0` the lower end of `R`; `1` the unit cube. -/
theorem unitCubeMomentBound_of_cube (hN : N ≠ 0) (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)}
    (h : CubeMomentBound hN W O) : UnitCubeMomentBound hN W O :=
  fun p => h 1 zero_le_one p

#print axioms unitCubeMomentBound_of_cube

/-- **One exponential moment of the unit-cube energy**: some `t > 0` has `ν_k(e^{t E_1})` bounded
eventually.

DERIVED: `0` is the lower end of `t`; `1` the unit cube. -/
def UnitCubeExpBound (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop,
    stateK hN k (expC (t • cubeSum (dySpacing N k) 1 (W.fieldMap k O).1)) ≤ C

/-- `CubeExpBound` at the unit cube.

DERIVED: `0` the lower end of `R`; `1` the unit cube. -/
theorem unitCubeExpBound_of_cubeExpBound (hN : N ≠ 0) (W : ConfFlow N)
    {O : LField (MassGap.SUN.SU N)} (h : CubeExpBound hN W O) : UnitCubeExpBound hN W O :=
  h 1 zero_le_one

#print axioms unitCubeExpBound_of_cubeExpBound

/-- **Every cube moment from one exponential moment of the unit cube**, uniformly: there are `t > 0`
and `C ≥ 0` with, eventually in the step, for every `R ≥ 0` and `p`,
`ν_k(E_R^{2p}) ≤ ((2R + 1)⁴)^{2p} (2p)! t^{-2p} C` (`state_cubeSum_pow_le`,
`ObserverEnergyBox.state_pow_le_exp`). The step from which it holds does not depend on `R` or `p`.

DERIVED: `0` is the excluded colour count, the lower end of `t`, `C`, `R` and the sign of the field;
`1`, `2`, `4` as in `state_cubeSum_pow_le`. -/
theorem cubeMoments_of_unitExp (hN : N ≠ 0) (W : ConfFlow N) {O : LField (MassGap.SUN.SU N)}
    (hO : ∀ U, 0 ≤ O.1 U) (h : UnitCubeExpBound hN W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ R : ℝ, 0 ≤ R → ∀ p : ℕ,
      stateK hN k (cubeSum (dySpacing N k) R (W.fieldMap k O).1 ^ (2 * p))
        ≤ ((2 * R + 1) ^ 4) ^ (2 * p) * (((2 * p).factorial : ℝ) / t ^ (2 * p) * C) := by
  obtain ⟨t, C, ht, hC⟩ := h
  refine ⟨t, |C|, ht, abs_nonneg C, ?_⟩
  filter_upwards [hC] with k hk
  intro R hR p
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hF : ∀ U, 0 ≤ (W.fieldMap k O).1 U := fun U => hO (W.V k U)
  refine (state_cubeSum_pow_le hN k ha hR _ hF p).trans
    (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (pow_nonneg (by linarith) 4) _))
  exact (state_pow_le_exp (stateK hN k) _ (cubeSum_nonneg _ _ hF) ht (2 * p)).trans
    (mul_le_mul_of_nonneg_left (hk.trans (le_abs_self C))
      (div_nonneg (by positivity) (pow_pos ht _).le))

#print axioms cubeMoments_of_unitExp

end OneCube

/-! ## 4. The growth condition -/

section Growth

variable {N : ℕ}

/-- **OS0 uniform in the supports, from one exponential moment of the unit cube.** For a non-negative
field `O` of `D` with `UnitCubeExpBound`, there are `t > 0`, `C ≥ 0` such that for every `n` and every
family of test functions with `|gᵢ| ≤ Mᵢ` supported in `[-Rᵢ, Rᵢ]⁴`,
`|S_n(g₁, …, gₙ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ Mᵢ (2Rᵢ + 1)⁴`. At each step the factor `i` has
`2n`-th moment at most `(Mᵢ (2Rᵢ + 1)⁴)^{2n} (2n)! t^{-2n} C` (`cubeMoments_of_unitExp`), and
`ObserverOS.abs_state_prod_le` combines them; the bound holds at `Mᵢ + ε` and passes to `ε = 0`.

DERIVED: `0` is the excluded colour count, the lower end of `ε`, `t`, `C` and the limit point; `1` the
spacing bound and `abs_state_prod_le`'s; `2` makes the power even and with `1` is the box side; `4` the
spacetime dimension. -/
theorem abs_contSF_energy0_growth (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ (n : ℕ) (f : Fin n → TestFn) (R M : Fin n → ℝ),
      (∀ i, IsTest (f i).1 (R i) (M i)) →
        |contSF hN (energy0 W D hD) (fun i => (O, f i))|
          ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
            * ∏ i, M i * (2 * R i + 1) ^ 4 := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExp hN W (hpos O hO) h
  refine ⟨t, C, ht, hC0, fun n f R M hM => ?_⟩
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hM0 : ∀ i, 0 ≤ M i := fun i => (hM i).M_nonneg
  have hR0 : ∀ i, 0 ≤ R i := fun i => (hM i).1
  set c : ℝ := ((2 * n).factorial : ℝ) / t ^ (2 * n) * C with hcdef
  have key : ∀ ε : ℝ, 0 < ε → |contSF hN (energy0 W D hD) (fun i => (O, f i))|
      ≤ (1 + n * c) * ∏ i, (M i + ε) * (2 * R i + 1) ^ 4 := by
    intro ε hε
    have hstep : ∀ᶠ k in atTop, |latSF hN (energy0 W D hD) k (fun i => (O, f i))|
        ≤ (1 + n * c) * ∏ i, (M i + ε) * (2 * R i + 1) ^ 4 := by
      filter_upwards [hev, (tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk hk1
      have hb := abs_state_prod_le (stateK hN k)
        (fun i => smear (dySpacing N k) ((energy0 W D hD).map k O).1 (f i))
        (fun i => (M i + ε) * (2 * R i + 1) ^ 4)
        (fun i => mul_pos (by linarith [hM0 i]) (pow_pos (by linarith [hR0 i]) 4)) (c := c)
        (fun i => by
          rw [Fintype.card_fin]
          calc stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 (f i) ^ (2 * n))
              ≤ (M i + ε) ^ (2 * n) * stateK hN k (cubeSum (dySpacing N k) (R i)
                  (W.fieldMap k O).1 ^ (2 * n)) :=
                moment_smear_energy0_le hN W hD hpos hO hk1.le (f i)
                  (isTest_mono (hM i) (by linarith)) n
            _ ≤ (M i + ε) ^ (2 * n) * (((2 * R i + 1) ^ 4) ^ (2 * n) * c) :=
                mul_le_mul_of_nonneg_left (hk (R i) (hR0 i) n)
                  (pow_nonneg (by linarith [hM0 i]) _)
            _ = c * ((M i + ε) * (2 * R i + 1) ^ 4) ^ (2 * n) := by rw [mul_pow]; ring)
      rw [Fintype.card_fin] at hb
      show |latSk hN k (fun i => (energy0 W D hD).field k ((O, f i) : SField N))| ≤ _
      rw [latSk_eq]
      exact hb
    obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hstep
    have hlim : contSF hN (energy0 W D hD) (fun i => (O, f i)) = x := hx.limUnder_eq
    rw [hlim]
    exact le_of_tendsto hx.abs (hstep.filter_mono ultra_le)
  have hcont : Continuous (fun ε : ℝ => (1 + n * c) * ∏ i, (M i + ε) * (2 * R i + 1) ^ 4) :=
    continuous_const.mul (continuous_finset_prod _
      (fun i _ => (continuous_const.add continuous_id).mul continuous_const))
  have ht' : Tendsto (fun ε : ℝ => (1 + n * c) * ∏ i, (M i + ε) * (2 * R i + 1) ^ 4) (𝓝[>] 0)
      (𝓝 ((1 + n * c) * ∏ i, (M i + 0) * (2 * R i + 1) ^ 4)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hfin := ge_of_tendsto ht' (eventually_nhdsWithin_of_forall (fun ε hε => key ε hε))
  simpa only [add_zero] using hfin

#print axioms abs_contSF_energy0_growth

/-- **The factorial bound**: for `t > 0` and `C ≥ 0`,
`1 + n (2n)! t^{-2n} C ≤ (1 + C) (8 (1 + t⁻¹)²)ⁿ (n!)²`, from `(2n)! = C(2n, n) (n!)² ≤ 4ⁿ (n!)²`,
`n ≤ 2ⁿ` and `t⁻¹ ≤ 1 + t⁻¹`.

DERIVED: `8 = 2 · 4` collects `n ≤ 2ⁿ` and `C(2n, n) ≤ 2^{2n} = 4ⁿ`; `2` the square of the factorial
and the even power; `1` the unit term; `0` the sign of `t` and `C`. -/
theorem growth_const_le {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (n : ℕ) :
    1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)
      ≤ (1 + C) * (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2 := by
  have hfac : ((2 * n).factorial : ℝ) ≤ 4 ^ n * (n.factorial : ℝ) ^ 2 := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    have h2 : (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
    have h3 : 2 * n - n = n := by omega
    rw [h3] at h1
    have h4 : (2 * n).factorial ≤ 4 ^ n * n.factorial ^ 2 := by
      rw [← h1, show (4 : ℕ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
      calc (2 * n).choose n * n.factorial * n.factorial
          = (2 * n).choose n * n.factorial ^ 2 := by ring
        _ ≤ 2 ^ (2 * n) * n.factorial ^ 2 := Nat.mul_le_mul_right _ h2
    exact_mod_cast h4
  have hn2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hti : 0 ≤ t⁻¹ := (inv_pos.mpr ht).le
  have ht2 : (t ^ (2 * n))⁻¹ ≤ ((1 + t⁻¹) ^ 2) ^ n := by
    rw [← inv_pow, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hti 2) (pow_le_pow_left₀ hti (by linarith) 2) n
  have hx1 : (1 : ℝ) ≤ (n.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos n)
  have hγ1 : (1 : ℝ) ≤ 8 * (1 + t⁻¹) ^ 2 := by
    have : (1 : ℝ) ≤ (1 + t⁻¹) ^ 2 := one_le_pow₀ (by linarith)
    linarith
  have hγ : (2 : ℝ) ^ n * 4 ^ n * ((1 + t⁻¹) ^ 2) ^ n = (8 * (1 + t⁻¹) ^ 2) ^ n := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have hA : (n : ℝ) * (((2 * n).factorial : ℝ) / t ^ (2 * n))
      ≤ (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2 := by
    rw [div_eq_mul_inv]
    calc (n : ℝ) * (((2 * n).factorial : ℝ) * (t ^ (2 * n))⁻¹)
        ≤ 2 ^ n * ((4 ^ n * (n.factorial : ℝ) ^ 2) * ((1 + t⁻¹) ^ 2) ^ n) :=
          mul_le_mul hn2 (mul_le_mul hfac ht2 (inv_nonneg.mpr (by positivity)) (by positivity))
            (by positivity) (by positivity)
      _ = (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2 := by rw [← hγ]; ring
  have hB : (1 : ℝ) ≤ (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hγ1) (one_le_pow₀ hx1)
  calc 1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)
      = 1 + (n * (((2 * n).factorial : ℝ) / t ^ (2 * n))) * C := by ring
    _ ≤ (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2
          + (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2 * C :=
        add_le_add hB (mul_le_mul_of_nonneg_right hA hC0)
    _ = (1 + C) * (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2 := by ring

#print axioms growth_const_le

/-- **`TemperedGrowth` for the observer's energy density, from one exponential moment of the unit
cube.** For a non-negative field `O` of a reflection-closed class `D` with `UnitCubeExpBound` (in
particular with `CubeExpBound`, `unitCubeExpBound_of_cubeExpBound`), one `α = 1 + C`,
`γ = 8 (1 + t⁻¹)²`, `β = 2` bound every Schwinger function of `O`:
`|S_n(g₁, …, gₙ)| ≤ α γⁿ (n!)^β ∏ᵢ Mᵢ (2Rᵢ + 3)⁴` (`abs_contSF_energy0_growth`, `growth_const_le`,
and `2Rᵢ + 1 ≤ 2Rᵢ + 3`).

DERIVED: `8`, `2`, `1` are `growth_const_le`'s; `3`, `4` are `TemperedGrowth`'s volume factor; `0` the
sign of `Mᵢ`, `Rᵢ`, `t`, `C`; `4` in `Fin 4` is the spacetime dimension. -/
theorem temperedGrowth_energy0 (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) : TemperedGrowth hN (energy0 W D hD) O := by
  obtain ⟨t, C, ht, hC0, hb⟩ := abs_contSF_energy0_growth hN W hD hpos hO h
  unfold TemperedGrowth
  refine ⟨1 + C, 8 * (1 + t⁻¹) ^ 2, 2, fun n f R M hM => ?_⟩
  rw [Real.rpow_two]
  have hM0 : ∀ i, 0 ≤ M i := fun i => (hM i).M_nonneg
  have hR0 : ∀ i, 0 ≤ R i := fun i => (hM i).1
  have hP : ∏ i, M i * (2 * R i + 1) ^ 4 ≤ ∏ i, M i * (2 * R i + 3) ^ 4 :=
    Finset.prod_le_prod (fun i _ => mul_nonneg (hM0 i) (pow_nonneg (by linarith [hR0 i]) 4))
      (fun i _ => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [hR0 i]) (by linarith) 4) (hM0 i))
  have hP0 : 0 ≤ ∏ i, M i * (2 * R i + 3) ^ 4 :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (hM0 i) (pow_nonneg (by linarith [hR0 i]) 4))
  have hK0 : 0 ≤ 1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C) :=
    add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0))
  calc |contSF hN (energy0 W D hD) (fun i => (O, f i))|
      ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
          * ∏ i, M i * (2 * R i + 1) ^ 4 := hb n f R M hM
    _ ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
          * ∏ i, M i * (2 * R i + 3) ^ 4 := mul_le_mul_of_nonneg_left hP hK0
    _ ≤ (1 + C) * (8 * (1 + t⁻¹) ^ 2) ^ n * (n.factorial : ℝ) ^ 2
          * ∏ i, M i * (2 * R i + 3) ^ 4 :=
        mul_le_mul_of_nonneg_right (growth_const_le ht hC0 n) hP0

#print axioms temperedGrowth_energy0

/-- **`TemperedGrowth` on the whole class from (E) in its exponential cube form**: every field of a
non-negative reflection-closed class with `CubeExpBound` has the cube-uniform growth condition.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` the sign of the fields. -/
theorem temperedGrowth_energy0_of_cubeExp (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hexp : ∀ O ∈ D, CubeExpBound hN W O) :
    ∀ O ∈ D, TemperedGrowth hN (energy0 W D hD) O :=
  fun O hO => temperedGrowth_energy0 hN W hD hpos hO
    (unitCubeExpBound_of_cubeExpBound hN W (hexp O hO))

#print axioms temperedGrowth_energy0_of_cubeExp

end Growth

end MassGap.ObserverOSGrowth
