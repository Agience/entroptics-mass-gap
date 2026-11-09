import Mathlib
import MassGap.ObserverOS
import MassGap.ObserverAxisN
import MassGap.SO4Planes

noncomputable section

/-!
# MassGap.ObserverRotationDense — `SO(4)` for the observer's energy density from one rotation

The observer's energy-density theory is `ObserverOS.energy0 W D hD` (`a⁻⁴ (O ∘ V_k)` on a
reflection-closed class `D` of non-negative fields). This module reduces its full `SO(4)` invariance,
`ObserverRotation.ObserverSO4` at the `HypScalar` fields of `D`, to (E) and invariance under the one
rotation `ObserverRotation.pyth`.

## 1. Continuity in the rotation, from (E)

`rotTest_isTest`: a test function supported in `[-R, R]⁴` rotated by an orthogonal matrix is supported
in `[-4R, 4R]⁴` (every entry of an orthogonal matrix is at most `1`, `abs_entry_le_one`).
`orbitContinuous_energy0`: given (E) in its cube form, `A ↦ S(f₁ ∘ A, …, fₙ ∘ A)` is continuous on
`SO(4)` for uniformly continuous test functions. For `A` near `B` entrywise, `|A y − B y|` is small
uniformly on the common support box, so `f ∘ A` and `f ∘ B` are close in sup norm by uniform
continuity, and `ObserverOS.abs_contSF_energy0_sub_le` turns sup-norm closeness into closeness of the
limits, with the constant of the cube moments on one box.

## 2. The invariance monoid

`invMonoid hN Φ Φs`: the orthogonal matrices `A` with `S(F ∘ A) = S(F)` for every family of
`Φs`-fields with uniformly continuous test functions. It is a submonoid: `rotFam A (rotFam B F) =
rotFam (B * A) F` (`rotFam_rotFam`), and a rotated uniformly continuous test function is uniformly
continuous (`uniformContinuous_rotTest`).

## 3. `SO(4)` from `pyth`

`observerSO4_of_pyth`: for any flow, orbit continuity, invariance under the signed permutation
matrices and invariance under `pyth` give `ObserverSO4`. The monoid `D = invMonoid ⊓ SO(4)` contains
`pyth`, the reflection `refl1 = diag(1, −1, 1, 1)` conjugates `pyth` to `rot01 (−pythAngle)`, so `D`
contains `rot01 (k · pythAngle)` for every `k ∈ ℤ`; their closure contains every rotation of the
`(0, 1)` plane (`SO4Planes.rot01_mem_closure`). The signed permutation `cyc4` (`e₀ ↦ e₁ ↦ e₂ ↦ e₃ ↦
−e₀`, in `SO(4)`) conjugates the `(0, 1)` rotations to the `(1, 2)` rotations and those to the
`(2, 3)` rotations (`r12_conj`, `r23_conj`). The closure of `D` is a submonoid containing the three
families, so it contains `SO(4)` (`SO4Planes.so4_le_of_planes`), and `observerSO4_of_dense` closes.

`observerSO4_energy0`: for the energy density of any configuration flow commuting with the axis
permutations, (E) and invariance under `pyth` give `ObserverSO4` at the `HypScalar` fields of `D`. The
signed permutations come from `ObserverAxisN.signed_of_axisCov` through `energy0`'s agreement on `D`
with the energy density of every field (`latSF_energy0_eq`). `observer2_so4` is the instance at the
`SU(2)` APE observer. The one
input that is not proved is the hypothesis `hpyth`: the limit is invariant under `pyth`.
-/

namespace MassGap.ObserverRotationDense

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumHypercubic MassGap.ContinuumFlow MassGap.ObserverRotation MassGap.ObserverOS
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyBox MassGap.SO4Planes MassGap.ObserverAxisN
  Filter
open scoped Topology Matrix

/-! ## 1. Rotated test functions -/

section Rotated

variable {N : ℕ}

/-- **Every entry of an orthogonal matrix is at most `1`**: the columns are unit vectors.

DERIVED: `1` the column norm; `4` the dimension. -/
theorem abs_entry_le_one {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) (j k : Fin 4) :
    |A j k| ≤ 1 := by
  have h := congrFun (congrFun hA k) k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have h2 : A j k * A j k ≤ 1 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun j => A j k * A j k) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ j)
  exact (sq_le_one_iff_abs_le_one _).mp (by rw [sq]; exact h2)

#print axioms abs_entry_le_one

/-- **The support of a rotated test function**: radius `R` becomes `4R`.

DERIVED: `4` bounds a column sum of `|A|`. -/
theorem rotTest_isTest {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) {f : TestFn} {R M : ℝ}
    (hf : IsTest f.1 R M) : IsTest (rotTest A f).1 (4 * R) M := by
  refine ⟨by linarith [hf.1], fun y => by rw [rotTest_apply A hA]; exact hf.2.1 _,
    fun y hy i => ?_⟩
  rw [rotTest_apply A hA] at hy
  have h1 := rotTest_support A hA y (fun j => hf.2.2 _ hy j) i
  have h2 : ∑ j, |A j i| ≤ 4 := by
    rw [Fin.sum_univ_four]
    linarith [abs_entry_le_one hA 0 i, abs_entry_le_one hA 1 i, abs_entry_le_one hA 2 i,
      abs_entry_le_one hA 3 i]
  calc |y i| ≤ (∑ j, |A j i|) * R := h1
    _ ≤ 4 * R := mul_le_mul_of_nonneg_right h2 hf.1

#print axioms rotTest_isTest

/-- **A rotated uniformly continuous test function is uniformly continuous**: `f ∘ A` with `A` a
continuous linear map.

DERIVED: no numeral. -/
theorem uniformContinuous_rotTest {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) {f : TestFn}
    (hf : UniformContinuous f.1) : UniformContinuous (rotTest A f).1 := by
  have e : (rotTest A f).1 = f.1 ∘ (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) := by
    funext y
    simp [rotTest_apply A hA, Matrix.toLin'_apply]
  rw [e]
  exact hf.comp (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).uniformContinuous

#print axioms uniformContinuous_rotTest

/-- The product of two orthogonal matrices is orthogonal.

DERIVED: `1` the identity. -/
theorem transpose_mul_self_mul {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1)
    (hB : Bᵀ * B = 1) : (B * A)ᵀ * (B * A) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ, hB, Matrix.one_mul, hA]

#print axioms transpose_mul_self_mul

/-- **Rotating twice**: `(f ∘ B) ∘ A = f ∘ (B A)`.

DERIVED: no numeral. -/
theorem rotTest_rotTest {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1)
    (f : TestFn) : rotTest A (rotTest B f) = rotTest (B * A) f :=
  Subtype.ext (funext fun y => by
    rw [rotTest_apply A hA, rotTest_apply B hB, rotTest_apply (B * A) (transpose_mul_self_mul hA hB),
      Matrix.mulVec_mulVec])

#print axioms rotTest_rotTest

/-- DERIVED: `1` the identity. -/
theorem rotTest_one (f : TestFn) : rotTest 1 f = f :=
  Subtype.ext (funext fun y => by
    rw [rotTest_apply 1 (by rw [Matrix.transpose_one, Matrix.one_mul]), Matrix.one_mulVec])

#print axioms rotTest_one

/-- DERIVED: no numeral. -/
theorem rotFam_rotFam {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1)
    {ι : Type} (F : ι → SField N) : rotFam A (rotFam B F) = rotFam (B * A) F :=
  funext fun i => Prod.ext rfl (rotTest_rotTest hA hB (F i).2)

#print axioms rotFam_rotFam

/-- DERIVED: `1` the identity. -/
theorem rotFam_one {ι : Type} (F : ι → SField N) : rotFam 1 F = F :=
  funext fun i => Prod.ext rfl (rotTest_one (F i).2)

#print axioms rotFam_one

end Rotated

/-! ## 2. Continuity in the rotation, from (E) -/

section Continuity

variable {N : ℕ}

/-- **Orbit continuity of the energy density, from (E).** For a family of fields of a non-negative
reflection-closed class with bounded cube moments and uniformly continuous test functions,
`A ↦ S(f₁ ∘ A, …, fₙ ∘ A)` is continuous on `SO(4)`.

DERIVED: `0` the excluded colour count and the signs of `ε`, `δ`, `θ`; `1` keeps `K + 1`, `R + 1`
positive; `2` halves `ε` and makes the moment power even; `4` the dimension, bounding the rotated
support and the entries of `A − B` summed over a row. -/
theorem orbitContinuous_energy0 (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {ι : Type}
    [Fintype ι] (F : ι → SField N) (hG : ∀ i, (F i).1 ∈ D)
    (hU : ∀ i, UniformContinuous (F i).2.1) : OrbitContinuous hN (energy0 W D hD) F := by
  classical
  have hB := uniformBoundF_energy0 hN W D hD hpos hcube
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 4 * ∑ i, R0 i := ⟨_, rfl⟩
  have hR0s : ∀ i, R0 i ≤ ∑ i, R0 i := fun i =>
    Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ i, R0 i := Finset.sum_nonneg (fun i _ => (hRM i).1)
  have hR0 : 0 ≤ R := by rw [hRdef]; linarith
  have hT : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, Aᵀ * A = 1 → ∀ i,
      IsTest (rotTest A (F i).2).1 R (M i) := by
    intro A hA i
    have h := rotTest_isTest hA (hRM i)
    exact ⟨hR0, h.2.1, fun y hy j => (h.2.2 y hy j).trans (by rw [hRdef]; linarith [hR0s i])⟩
  have hC : ∀ i, ∃ C : ℝ, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k (F i).1).1 ^ (2 * Fintype.card ι)) ≤ C :=
    fun i => hcube _ (hG i) R hR0 _
  choose C hC using hC
  have hc : ∀ i, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k (F i).1).1 ^ (2 * Fintype.card ι)) ≤ ∑ i, |C i| := fun i =>
    (hC i).mono (fun k hk => hk.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))))
  have hc0 : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = (1 + Fintype.card ι * ∑ i, |C i|) * ∑ a, ∏ i ∈ Finset.univ \ {a}, M i := ⟨_, rfl⟩
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun a _ => Finset.prod_nonneg (fun i _ => (hRM i).M_nonneg)))
  unfold OrbitContinuous
  intro B hBs
  have hBo : Bᵀ * B = 1 := transpose_mul_self_of_mem hBs
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hK1 : 0 < K + 1 := by linarith
  set δ : ℝ := ε / 2 / (K + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hη : ∀ i, ∃ η : ℝ, 0 < η ∧
      ∀ a b : Fin 4 → ℝ, dist a b < η → dist ((F i).2.1 a) ((F i).2.1 b) < δ := by
    intro i
    obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp (hU i) _ hδ
    exact ⟨η, hη, fun a b hab => h hab⟩
  choose η hη0 hηf using hη
  have hθ : ∀ i, 0 < η i / (4 * (R + 1)) := fun i => by have := hη0 i; positivity
  have hev : ∀ i (j k : Fin 4), ∀ᶠ A in 𝓝 B,
      |(A : Matrix (Fin 4) (Fin 4) ℝ) j k - B j k| < η i / (4 * (R + 1)) := by
    intro i j k
    have ht : Tendsto (fun A : Matrix (Fin 4) (Fin 4) ℝ => A j k) (𝓝 B) (𝓝 (B j k)) :=
      (continuous_id.matrix_elem j k).tendsto B
    exact (Metric.tendsto_nhds.mp ht _ (hθ i)).mono fun A hA => by rwa [Real.dist_eq] at hA
  have hev2 : ∀ᶠ A in 𝓝 B, ∀ i (j k : Fin 4),
      |(A : Matrix (Fin 4) (Fin 4) ℝ) j k - B j k| < η i / (4 * (R + 1)) :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      Filter.eventually_all.mpr fun k => hev i j k
  have hself : ∀ᶠ A in 𝓝[(Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ))] B,
      A ∈ (Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set (Matrix (Fin 4) (Fin 4) ℝ)) :=
    self_mem_nhdsWithin
  filter_upwards [hself, hev2.filter_mono nhdsWithin_le_nhds] with A hAs hAc
  have hA : Aᵀ * A = 1 := transpose_mul_self_of_mem hAs
  have hclose : ∀ i y, |(rotFam A F i).2.1 y - (rotFam B F i).2.1 y| ≤ δ := by
    intro i y
    show |(rotTest A (F i).2).1 y - (rotTest B (F i).2).1 y| ≤ δ
    by_cases h0 : (rotTest A (F i).2).1 y = 0 ∧ (rotTest B (F i).2).1 y = 0
    · rw [h0.1, h0.2, sub_self, abs_zero]; exact hδ.le
    · have hy : ∀ k, |y k| ≤ R := by
        intro k
        by_cases hA0 : (rotTest A (F i).2).1 y = 0
        · have hB0 : (rotTest B (F i).2).1 y ≠ 0 := fun h => h0 ⟨hA0, h⟩
          exact (hT B hBo i).2.2 y hB0 k
        · exact (hT A hA i).2.2 y hA0 k
      rw [rotTest_apply A hA, rotTest_apply B hBo]
      have hd : dist (A.mulVec y) (B.mulVec y) < η i := by
        rw [dist_pi_lt_iff (hη0 i)]
        intro j
        rw [Real.dist_eq]
        have e : A.mulVec y j - B.mulVec y j = ∑ k, (A j k - B j k) * y k := by
          simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, sub_mul]
        rw [e]
        have hle : ∀ k, |(A j k - B j k) * y k| ≤ η i / (4 * (R + 1)) * R := by
          intro k
          rw [abs_mul]
          exact mul_le_mul (hAc i j k).le (hy k) (abs_nonneg _) (hθ i).le
        have h1 : |∑ k, (A j k - B j k) * y k| ≤ 4 * (η i / (4 * (R + 1)) * R) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Fin.sum_univ_four]
          linarith [hle 0, hle 1, hle 2, hle 3]
        have h2 : 4 * (η i / (4 * (R + 1)) * (R + 1)) = η i := by field_simp
        have h3 : 4 * (η i / (4 * (R + 1)) * R)
            = 4 * (η i / (4 * (R + 1)) * (R + 1)) - 4 * (η i / (4 * (R + 1))) := by ring
        linarith [hθ i]
      have := hηf i _ _ hd
      rw [Real.dist_eq] at this
      exact this.le
  have hdiff := abs_contSF_energy0_sub_le hN W hD hpos hB (rotFam B F) (rotFam A F) (fun i => rfl)
    hG hR0 hc M (fun i => hT B hBo i) (fun i => hT A hA i) hclose
  have hsum : (1 + Fintype.card ι * ∑ i, |C i|) * ∑ a, δ * ∏ i ∈ Finset.univ \ {a}, M i
      = δ * K := by
    rw [hKdef, ← Finset.mul_sum]
    ring
  rw [hsum] at hdiff
  rw [Real.dist_eq]
  have hδK : δ * K < ε := by
    rw [hδdef, div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  exact lt_of_le_of_lt hdiff hδK

#print axioms orbitContinuous_energy0

end Continuity

/-! ## 3. The invariance monoid and `SO(4)` from `pyth` -/

section Monoid

variable {N : ℕ}

/-- **The invariance monoid**: orthogonal matrices whose action on the test functions leaves the
flowed limit unchanged on every family of `Φs`-fields with uniformly continuous test functions.

DERIVED: `1` the identity of `Aᵀ A`. -/
def invMonoid (hN : N ≠ 0) (Φ : Flow N) (Φs : Set (LField (MassGap.SUN.SU N))) :
    Submonoid (Matrix (Fin 4) (Fin 4) ℝ) where
  carrier := {A | Aᵀ * A = 1 ∧ ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
    (∀ i, (F i).1 ∈ Φs) → (∀ i, UniformContinuous (F i).2.1) → contSF hN Φ (rotFam A F) = contSF hN Φ F}
  one_mem' := ⟨by rw [Matrix.transpose_one, Matrix.one_mul], fun ι _ F _ _ => by rw [rotFam_one]⟩
  mul_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    refine ⟨transpose_mul_self_mul hb ha, fun ι _ F hF hU => ?_⟩
    rw [← rotFam_rotFam hb ha]
    rw [hbi ι (rotFam a F) hF (fun i => uniformContinuous_rotTest ha (hU i))]
    exact hai ι F hF hU

/-- The reflection of the axis `1`.

DERIVED: `1` and `-1` the signs. -/
def refl1 : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The signed cyclic permutation `e₀ ↦ e₁ ↦ e₂ ↦ e₃ ↦ −e₀`.

DERIVED: `1` and `-1` the signs. -/
def cyc4 : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0]

/-- The transpose of `cyc4`.

DERIVED: `1` and `-1` the signs. -/
def cyc4T : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0]

/-- The index permutation of `cyc4`: `(cyc4 y) i = sg i · y (σ i)` with `σ = (3, 0, 1, 2)`.

DERIVED: `0`–`3` the axes. -/
def cycPerm : Equiv.Perm (Fin 4) := ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

/-- The index permutation of `cyc4T`.

DERIVED: `0`–`3` the axes. -/
def cycPermT : Equiv.Perm (Fin 4) := ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

/-- DERIVED: `1` and `-1` the signs. -/
theorem refl1_signed : ∃ (σ : Equiv.Perm (Fin 4)) (sg : Fin 4 → ℝ), (∀ i, sg i = 1 ∨ sg i = -1) ∧
    ∀ y i, refl1.mulVec y i = sg i * y (σ i) := by
  refine ⟨Equiv.refl _, ![1, -1, 1, 1], fun i => by fin_cases i <;> simp, fun y i => ?_⟩
  fin_cases i <;> simp [refl1, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

#print axioms refl1_signed

/-- DERIVED: `1` and `-1` the signs. -/
theorem cyc4_signed : ∃ (σ : Equiv.Perm (Fin 4)) (sg : Fin 4 → ℝ), (∀ i, sg i = 1 ∨ sg i = -1) ∧
    ∀ y i, cyc4.mulVec y i = sg i * y (σ i) := by
  refine ⟨cycPerm, ![-1, 1, 1, 1], fun i => by fin_cases i <;> simp, fun y i => ?_⟩
  fin_cases i <;> simp [cyc4, cycPerm, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

#print axioms cyc4_signed

/-- DERIVED: `1` and `-1` the signs. -/
theorem cyc4T_signed : ∃ (σ : Equiv.Perm (Fin 4)) (sg : Fin 4 → ℝ), (∀ i, sg i = 1 ∨ sg i = -1) ∧
    ∀ y i, cyc4T.mulVec y i = sg i * y (σ i) := by
  refine ⟨cycPermT, ![1, 1, 1, -1], fun i => by fin_cases i <;> simp, fun y i => ?_⟩
  fin_cases i <;> simp [cyc4T, cycPermT, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

#print axioms cyc4T_signed

/-- DERIVED: `1` the identity. -/
theorem refl1_orth : refl1ᵀ * refl1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [refl1, Matrix.mul_apply, Fin.sum_univ_four]

#print axioms refl1_orth

/-- **`cyc4 ∈ SO(4)`.**

DERIVED: `1` the identity and the determinant. -/
theorem cyc4_mem : cyc4 ∈ SO4 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cyc4, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, cyc4, Fin.succAbove]
    all_goals norm_num

#print axioms cyc4_mem

/-- **`cyc4ᵀ ∈ SO(4)`.**

DERIVED: `1` the identity and the determinant. -/
theorem cyc4T_mem : cyc4T ∈ SO4 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cyc4T, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, cyc4T, Fin.succAbove]
    all_goals norm_num

#print axioms cyc4T_mem

/-- **`refl1` conjugates `pyth` to the opposite rotation.**

DERIVED: `3/5`, `4/5` the entries of `pyth`. -/
theorem rot01_neg_pyth : rot01 (-pythAngle) = refl1 * pyth * refl1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot01, r01, refl1, pyth, Real.cos_neg, Real.sin_neg, cos_pythAngle, sin_pythAngle,
      Matrix.mul_apply, Fin.sum_univ_four]

#print axioms rot01_neg_pyth

/-- **`cyc4` conjugates the `(0, 1)` rotations to the `(1, 2)` rotations.**

DERIVED: no numeral. -/
theorem r12_conj (c s : ℝ) : r12 c s = cyc4 * r01 c s * cyc4T := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [r12, r01, cyc4, cyc4T, Matrix.mul_apply, Fin.sum_univ_four]

#print axioms r12_conj

/-- **`cyc4` conjugates the `(1, 2)` rotations to the `(2, 3)` rotations.**

DERIVED: no numeral. -/
theorem r23_conj (c s : ℝ) : r23 c s = cyc4 * r12 c s * cyc4T := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [r23, r12, cyc4, cyc4T, Matrix.mul_apply, Fin.sum_univ_four]

#print axioms r23_conj

/-- **`SO(4)` from orbit continuity, the signed permutations and `pyth`.** For any flow and class of
fields: if every orbit is continuous on `SO(4)`, the limit is invariant under every orthogonal signed
permutation matrix and under `pyth`, then it is invariant under all of `SO(4)`.

DERIVED: `0` the excluded colour count; `1` the radius of the circle; `4` the dimension. -/
theorem observerSO4_of_pyth (hN : N ≠ 0) (Φ : Flow N) (Φs : Set (LField (MassGap.SUN.SU N)))
    (hcont : ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ Φs) →
      (∀ i, UniformContinuous (F i).2.1) → OrbitContinuous hN Φ F)
    (hsign : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, Aᵀ * A = 1 →
      (∃ (σ : Equiv.Perm (Fin 4)) (sg : Fin 4 → ℝ), (∀ i, sg i = 1 ∨ sg i = -1) ∧
        ∀ y i, A.mulVec y i = sg i * y (σ i)) →
      ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ Φs) →
        (∀ i, UniformContinuous (F i).2.1) → contSF hN Φ (rotFam A F) = contSF hN Φ F)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ Φs) →
      (∀ i, UniformContinuous (F i).2.1) → contSF hN Φ (rotFam pyth F) = contSF hN Φ F) :
    ObserverSO4 hN Φ Φs := by
  set I := invMonoid hN Φ Φs with hI
  set D := I ⊓ SO4 with hDdef
  have hpI : pyth ∈ I := ⟨transpose_mul_self_of_mem pyth_mem, hpyth⟩
  have hrI : refl1 ∈ I := ⟨refl1_orth, hsign refl1 refl1_orth refl1_signed⟩
  have hcI : cyc4 ∈ I := ⟨transpose_mul_self_of_mem cyc4_mem, hsign cyc4
    (transpose_mul_self_of_mem cyc4_mem) cyc4_signed⟩
  have hcTI : cyc4T ∈ I := ⟨transpose_mul_self_of_mem cyc4T_mem, hsign cyc4T
    (transpose_mul_self_of_mem cyc4T_mem) cyc4T_signed⟩
  have hrotSO : ∀ x : ℝ, rot01 x ∈ SO4 := fun x => r01_mem (by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq x)
  have hnegI : rot01 (-pythAngle) ∈ I := by
    rw [rot01_neg_pyth]
    exact I.mul_mem (I.mul_mem hrI hpI) hrI
  have hkD : ∀ k : ℤ, rot01 (k * pythAngle) ∈ D := by
    intro k
    refine ⟨?_, hrotSO _⟩
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [show ((n : ℤ) : ℝ) * pythAngle = (n : ℝ) * pythAngle by push_cast; ring, rot01_nat_mul,
        ← pyth_eq_rot01]
      exact I.pow_mem hpI n
    · rw [show ((-(n : ℤ) : ℤ) : ℝ) * pythAngle = (n : ℝ) * (-pythAngle) by push_cast; ring,
        rot01_nat_mul]
      exact I.pow_mem hnegI n
  set G := D.topologicalClosure with hGdef
  have hcG : cyc4 ∈ G := D.le_topologicalClosure ⟨hcI, cyc4_mem⟩
  have hcTG : cyc4T ∈ G := D.le_topologicalClosure ⟨hcTI, cyc4T_mem⟩
  have h01 : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → r01 c s ∈ G := by
    intro c s h
    obtain ⟨θ, hc, hs⟩ := exists_angle h
    have e : r01 c s = rot01 θ := by rw [rot01, hc, hs]
    rw [e]
    refine closure_mono ?_ (rot01_mem_closure θ)
    rintro _ ⟨k, rfl⟩
    exact hkD k
  have h12 : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → r12 c s ∈ G := by
    intro c s h
    rw [r12_conj]
    exact G.mul_mem (G.mul_mem hcG (h01 c s h)) hcTG
  have h23 : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → r23 c s ∈ G := by
    intro c s h
    rw [r23_conj]
    exact G.mul_mem (G.mul_mem hcG (h12 c s h)) hcTG
  refine observerSO4_of_dense hN Φ Φs (D : Set (Matrix (Fin 4) (Fin 4) ℝ)) (fun A hA => hA.2)
    (fun A hA => so4_le_of_planes G h01 h12 h23 hA) hcont (fun A hA => hA.1.2)

#print axioms observerSO4_of_pyth

end Monoid

/-! ## 4. The observer's energy density -/

section Energy

variable {N : ℕ}

/-- The energy density of every field: `a⁻⁴ (O ∘ V_k)`.

DERIVED: `4` the dimension of the factor. -/
abbrev energyAll (W : ConfFlow N) : Flow N :=
  Flow.ofConfScaled W (canonZ N) (s0 N) (canonZ_refl N) (s0_refl N)

/-- **`energy0` agrees with `energyAll` on families of fields of `D`**, at every step.

DERIVED: `0` the excluded colour count. -/
theorem latSF_energy0_eq (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {ι : Type}
    [Fintype ι] (F : ι → SField N) (hG : ∀ i, (F i).1 ∈ D) (k : ℕ) :
    latSF hN (energy0 W D hD) k F = latSF hN (energyAll W) k F := by
  have hfam : (fun i => (energy0 W D hD).field k (F i)) = fun i => (energyAll W).field k (F i) := by
    funext i
    show ((energy0 W D hD).map k (F i).1, (F i).2) = ((energyAll W).map k (F i).1, (F i).2)
    congr 1
    show scaleField ((W.fieldMap k (F i).1).sub (sOn D (s0 N) k (F i).1)) (zOn D k (F i).1)
      = scaleField ((W.fieldMap k (F i).1).sub (s0 N k (F i).1)) (canonZ N k (F i).1)
    rw [zOn_of_mem (hG i), sOn_of_mem (hG i)]
  show latSk hN k (fun i => (energy0 W D hD).field k (F i))
    = latSk hN k (fun i => (energyAll W).field k (F i))
  rw [hfam]

#print axioms latSF_energy0_eq

/-- The same in the limit.

DERIVED: `0` the excluded colour count. -/
theorem contSF_energy0_eq (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {ι : Type}
    [Fintype ι] (F : ι → SField N) (hG : ∀ i, (F i).1 ∈ D) :
    contSF hN (energy0 W D hD) F = contSF hN (energyAll W) F := by
  unfold contSF
  congr 1
  funext k
  exact latSF_energy0_eq hN W hD F hG k

#print axioms contSF_energy0_eq

/-- **`SO(4)` for the observer's energy density from (E) and one rotation.** For any configuration
flow commuting with the axis permutations and any non-negative reflection-closed class `D` with
bounded cube moments: if the limit is invariant under `pyth` on families of `HypScalar` fields of `D`
with uniformly continuous test functions, it is invariant under all of `SO(4)` on them.

DERIVED: `0` the excluded colour count; `4` the dimension. -/
theorem observerSO4_energy0 (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ D ∧ HypScalar (F i).1) →
      (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W D hD) (rotFam pyth F) = contSF hN (energy0 W D hD) F) :
    ObserverSO4 hN (energy0 W D hD) {O | O ∈ D ∧ HypScalar O} := by
  refine observerSO4_of_pyth hN _ _ (fun ι _ F hF hU => orbitContinuous_energy0 hN W hD hpos hcube F
    (fun i => (hF i).1) hU) (fun A hA hAs ι _ F hF hU => ?_) hpyth
  rw [contSF_energy0_eq hN W hD (rotFam A F) (fun i => (hF i).1),
    contSF_energy0_eq hN W hD F (fun i => (hF i).1)]
  exact signed_of_axisCov hN _ (scaled_axisCov W hW (s0 N) (s0_refl N) (fun _ _ _ => rfl)) A hAs F
    (rotFam A F) (fun i => (hF i).2) (fun i => rfl) (fun i y => rotTest_apply A hA (F i).2 y)

#print axioms observerSO4_energy0

/-- **The `SU(2)` APE observer**: (E) and invariance under `pyth` give `SO(4)`.

DERIVED: `2` the rank; `1/6` the dominance bound. -/
theorem observer2_so4 {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 6) (n R : ℕ → ℕ)
    {D : Set (LField (MassGap.SUN.SU 2))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU 2)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, CubeMomentBound ObserverClay.two_ne (ObserverFlow.obsConfFlow c hc0 hc n R) O)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField 2), (∀ i, (F i).1 ∈ D ∧ HypScalar (F i).1) →
      (∀ i, UniformContinuous (F i).2.1) →
        contSF ObserverClay.two_ne (energy0 (ObserverFlow.obsConfFlow c hc0 hc n R) D hD)
            (rotFam pyth F)
          = contSF ObserverClay.two_ne (energy0 (ObserverFlow.obsConfFlow c hc0 hc n R) D hD) F) :
    ObserverSO4 ObserverClay.two_ne (energy0 (ObserverFlow.obsConfFlow c hc0 hc n R) D hD)
      {O | O ∈ D ∧ HypScalar O} :=
  observerSO4_energy0 ObserverClay.two_ne _ (fun k e U => obsConfFlow_iaxis hc0 hc n R k e U) hD hpos
    hcube hpyth

#print axioms observer2_so4

end Energy

end MassGap.ObserverRotationDense
