import Mathlib
import MassGap.StrongCoupling
import MassGap.GaugeInvariantAlgebra

/-!
# Coordinates, locality and constants for the strong-coupling pairing bound

The pairing bound of a local observable `x` against its reflection and its `m`-th translate along `τ`
(`PeriodicStrongCoupling.periodic_connected_shift_abs_le_obs`) places `θx` and `Sᵐx` in two cubes of
plaquettes and reads the cluster bound `StrongCoupling.wilsonCorrConnObs_abs_le_of_not_mem_ball` on
them. This module holds the pieces of that placement that do not depend on the lattice carrying the
state:

* `iterate_ishiftLink_coord`, `ireflLink_coord` — the coordinates of a link under the `m`-fold shift
  and under the reflection at `c`;
* `isLocalOn_iterate_ishiftObsL`, `norm_iterate_ishiftObsL_le` — the `m`-th translate of an
  observable local on `S` is local on the shifted `S` and has no larger sup norm;
* `exists_cube_posHalf` — a finite link set in the positive half `HalfSpaceAlgebra.posHalf τ p` lies
  strictly inside a cube based one step below the plane;
* `coreConstG_mono_C`, `coreConstG_le_of_le` — the cluster constant
  `StrongCoupling.coreConstG C K β u` is monotone in `C` and in the anchor size `u`, below the
  geometric threshold `coreRate K β < 1`.
-/

namespace MassGap.GeneralDecay

/-- The `τ` coordinate of `GibbsSpec.ishift μ x`: `x τ + 1` when `μ = τ`, and `x τ` otherwise.

DERIVED: the `1` is `ishift`'s lattice step; `4` is the dimension. -/
theorem ishift_coord (μ τ : Fin 4) (x : MassGap.GibbsSpec.ISite) :
    (MassGap.GibbsSpec.ishift μ x) τ = if μ = τ then x τ + 1 else x τ := by
  by_cases h : μ = τ
  · subst h; simp [MassGap.GibbsSpec.ishift]
  · simp [MassGap.GibbsSpec.ishift, Ne.symm h, h]

#print axioms ishift_coord

/-! ## Coordinates under the shift and the reflection -/

/-- The `m`-fold shift along `τ` keeps a link's direction and adds `m` to its `τ`-coordinate.

DERIVED: the `4` is the spacetime dimension; the `0` is the unchanged coordinates' increment. -/
theorem iterate_ishiftLink_coord (τ : Fin 4) (m : ℕ) (l : MassGap.InfiniteLattice.ILink) :
    ((MassGap.InfiniteShift.ishiftLink τ)^[m] l).1 = l.1
      ∧ ∀ i : Fin 4, ((MassGap.InfiniteShift.ishiftLink τ)^[m] l).2 i
          = l.2 i + (if i = τ then (m : ℤ) else 0) := by
  induction m with
  | zero => exact ⟨rfl, fun i => by simp⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨ih.1, fun i => ?_⟩
    show (MassGap.GibbsSpec.ishift τ ((MassGap.InfiniteShift.ishiftLink τ)^[m] l).2) i = _
    rw [ishift_coord, ih.2 i]
    by_cases h : i = τ
    · subst h; simp; ring
    · have h' : ¬ τ = i := fun e => h e.symm
      simp [h, h']

#print axioms iterate_ishiftLink_coord

/-- The reflection at `c` keeps a link's direction and every coordinate off `τ`; on `τ` it sends
`y` to `c − y`, or to `c − 1 − y` for a link along `τ`.

DERIVED: the `1` is the one-step offset of a `τ`-link's reflection; the `4` is the dimension. -/
theorem ireflLink_coord (τ : Fin 4) (c : ℤ) (l : MassGap.InfiniteLattice.ILink) :
    (MassGap.LatticeReflection.ireflLink τ c l).1 = l.1
      ∧ ∀ i : Fin 4, (MassGap.LatticeReflection.ireflLink τ c l).2 i
          = if i = τ then (if l.1 = τ then c - 1 - l.2 τ else c - l.2 τ) else l.2 i := by
  refine ⟨rfl, fun i => ?_⟩
  unfold MassGap.LatticeReflection.ireflLink MassGap.LatticeReflection.ireflSite
  by_cases hi : i = τ
  · subst hi; by_cases hl : l.1 = i <;> simp [hl]
  · by_cases hl : l.1 = τ <;> simp [hl, hi]

#print axioms ireflLink_coord

/-! ## Locality of the translate -/

/-- **The `m`-th translate of an observable local on `S` is local on the `m`-fold shifted `S`.**
`InfiniteShift.isLocalOn_ishiftObs` iterated.

DERIVED: the `4` is the spacetime dimension. -/
theorem isLocalOn_iterate_ishiftObsL (τ : Fin 4) {N : ℕ}
    {S : Finset MassGap.InfiniteLattice.ILink}
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hx : MassGap.InfiniteLattice.IsLocalOn S (x : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ))
    (m : ℕ) :
    MassGap.InfiniteLattice.IsLocalOn (S.image (MassGap.InfiniteShift.ishiftLink τ)^[m])
      (((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
        : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ) := by
  classical
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ', ← Finset.image_image]
    exact MassGap.InfiniteShift.isLocalOn_ishiftObs τ ih

#print axioms isLocalOn_iterate_ishiftObsL

/-- The `m`-th translate does not enlarge the sup norm. `WilsonTransferReduction.norm_ishiftObsL_le`
iterated.

DERIVED: the `4` is the spacetime dimension. -/
theorem norm_iterate_ishiftObsL_le (τ : Fin 4) {N : ℕ}
    (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (m : ℕ) :
    ‖(⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x‖ ≤ ‖x‖ := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans (MassGap.WilsonTransferReduction.norm_ishiftObsL_le τ _) ih

#print axioms norm_iterate_ishiftObsL_le

/-! ## A cube around a support in the positive half -/

/-- **Every finite link set in the positive half lies strictly inside a cube based one step below the
plane.** Each coordinate of each link is bounded by `M`, the largest coordinate sum; the cube starts at
`p − 1` along `τ` and at `−M − 1` elsewhere, with side `2M + |p| + 1`.

DERIVED: the `1`s are the one step below the plane and the strict-inside margin; `2M` covers the
range `[−M, M]`; the `4` is the dimension. -/
theorem exists_cube_posHalf (τ : Fin 4) (p : ℤ) (S : Finset MassGap.InfiniteLattice.ILink)
    (hS : (S : Set MassGap.InfiniteLattice.ILink) ⊆ MassGap.HalfSpaceAlgebra.posHalf τ p) :
    ∃ (x₀ : MassGap.GibbsSpec.ISite) (R : ℕ), x₀ τ = p - 1 ∧ 1 ≤ R ∧
      ∀ l ∈ S, ∀ i : Fin 4, x₀ i + 1 ≤ l.2 i ∧ l.2 i ≤ x₀ i + R := by
  classical
  let M : ℕ := S.sup (fun l => ∑ i : Fin 4, (l.2 i).natAbs)
  have hM : ∀ l ∈ S, ∀ i : Fin 4, (l.2 i).natAbs ≤ M := by
    intro l hl i
    exact le_trans (Finset.single_le_sum (f := fun j : Fin 4 => (l.2 j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      (Finset.le_sup (f := fun l : MassGap.InfiniteLattice.ILink => ∑ i : Fin 4, (l.2 i).natAbs) hl)
  refine ⟨fun i => if i = τ then p - 1 else -(M : ℤ) - 1, 2 * M + p.natAbs + 1, by simp, by omega,
    fun l hl i => ?_⟩
  have hb := hM l hl i
  have hτ : p ≤ l.2 τ := hS (Finset.mem_coe.mpr hl)
  have hbτ := hM l hl τ
  by_cases hi : i = τ
  · subst hi; simp only [if_true]; constructor <;> omega
  · simp only [hi, if_false]; constructor <;> omega

#print axioms exists_cube_posHalf

/-- **`coreConstG` is monotone in its per-term constant**, below the geometric threshold.

DERIVED: the `0` is the sign of the prefactor's other factors; the `1` is the geometric threshold. -/
theorem coreConstG_mono_C {C C' : ℝ} (h : C ≤ C') {K : ℕ} {β : ℝ}
    (hr : MassGap.StrongCoupling.coreRate K β < 1) (u : ℕ) :
    MassGap.StrongCoupling.coreConstG C K β u ≤ MassGap.StrongCoupling.coreConstG C' K β u := by
  unfold MassGap.StrongCoupling.coreConstG MassGap.StrongCoupling.corePrefactorG
  have hd : (0 : ℝ) ≤ (1 - MassGap.StrongCoupling.coreRate K β)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ hd
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)

#print axioms coreConstG_mono_C

/-! ## The cluster constant grows with the anchor size -/

/-- **`coreConstG` grows with the anchor size `u`**, below the geometric threshold: the prefactor is
`C · Aᵘ · Eᵘ` with `A = 4 (K + 1)² ≥ 1` and `E = e^{4βK} ≥ 1`.

DERIVED: the `4`, `1` and `2` are `corePrefactorG`'s; the `0`s are the sign hypotheses; the `1` in
`< 1` is the geometric threshold. -/
theorem coreConstG_le_of_le {C : ℝ} (hC : 0 ≤ C) {β : ℝ} (hβ : 0 ≤ β) {K : ℕ}
    (hr : MassGap.StrongCoupling.coreRate K β < 1) {u U : ℕ} (h : u ≤ U) :
    MassGap.StrongCoupling.coreConstG C K β u ≤ MassGap.StrongCoupling.coreConstG C K β U := by
  unfold MassGap.StrongCoupling.coreConstG MassGap.StrongCoupling.corePrefactorG
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hA : (1 : ℝ) ≤ 4 * ((K : ℝ) + 1) ^ 2 := by nlinarith
  have hE : (1 : ℝ) ≤ Real.exp (4 * β * (K : ℝ)) := Real.one_le_exp (by positivity)
  have hd : (0 : ℝ) ≤ (1 - MassGap.StrongCoupling.coreRate K β)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ hd
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA h) hC)
    (pow_le_pow_right₀ hE h) (by positivity) (mul_nonneg hC (by positivity))

#print axioms coreConstG_le_of_le

end MassGap.GeneralDecay
