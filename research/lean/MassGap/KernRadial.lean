import Mathlib
import MassGap.CompKernel
import MassGap.ShellLorentz
import MassGap.ObserverSymField

/-!
# MassGap.KernRadial — the action of `O(4)` on the regular class, and radiality of `kern2`

`CompKernel.kern2` is the smeared two-point kernel of the observer's energy-density composites,
`kern2 A B z = S(A, (O', g(· − z)))`, with `S = contSF (energy0 W D hD)`. This module puts the
rotations on the regular class, proves how `kern2` transforms under them, and reads radiality off
`ShellLorentz.radial_iff_orthInv`. Declarations are in the namespace `MassGap.KernRadial`.

DERIVED (module-wide): `Fin 4` the spacetime index; `Fin 2` the two factors of the form; `1` the
identity matrix and the determinant of a rotation; `-1` the determinant of a reflection.

## 1. The action (defined)

`rotSF M A = (O, f ∘ M)` (`ObserverRotation.rotTest`), and the action of `R ∈ O(4)` is
`act R A = rotSF Rᵀ A = (O, f ∘ R⁻¹)`. The field `O` is kept: the energy-density composites are
carried as scalars, so a rotation moves only the test function.

* `rotTest_translate`: `(f(· − v)) ∘ M = (f ∘ M)(· − Mᵀ v)` for `Mᵀ M = 1`.
* `act_translate`: `act R (g(· − z)) = (act R g)(· − R z)`.

## 2. How `kern2` transforms (proved)

* `kern2_rot`: if the limit is invariant under `M` on the family `(A, (O', g(· − z)))`, then
  `kern2 (rotSF M A) (rotSF M B) (Mᵀ z) = kern2 A B z`. This is the whole reduction: covariance of
  `kern2` is invariance of the continuum Schwinger function of that one two-factor family.
* `kern2_signed` (unconditional): for a configuration flow commuting with the axis permutations,
  `HypScalar` fields of `D` and `M` a signed permutation matrix, the identity of `kern2_rot` holds with
  no further input (`ObserverAxisN.signed_of_axisCov`).
* `O4Inv`: invariance of the limit under every orthogonal `R` on a class `Φs` with uniformly
  continuous test functions. `o4Inv_of_so4`: `ObserverRotation.ObserverSO4` and invariance under the
  reflection `refl1` give `O4Inv` (a matrix of determinant `−1` is `refl1 · (refl1 R)` with
  `refl1 R ∈ SO(4)`). `o4Inv_energy0`: for the observer, `O4Inv` on `D ∩ HypScalar` from the cube-moment bound `hcube`, a flow
  commuting with the axis permutations, and invariance under the one rotation `pyth`
  (`ObserverRotationDense.observerSO4_energy0`; `refl1` is signed, so its part is unconditional).
* `kern2_cov`: under `O4Inv`, `kern2 (act R A) (act R B) (R z) = kern2 A B z` for every `R ∈ O(4)`.

## 3. Radiality (proved, conditional on `pyth`)

* `kern2_orthInv`, `kern2_radial`: under `O4Inv`, for fields of `Φs` with uniformly continuous
  `O(4)`-invariant test functions (`f ∘ R = f` for all `R ∈ O(4)`), `kern2 A B` is `OrthInv`, hence
  `Radial` (`ShellLorentz.radial_iff_orthInv`).
* `kern2_radial_of_pyth`: the same for the observer's energy density on `D ∩ HypScalar` from the cube-moment bound `hcube`, the
  axis-commuting flow and `pyth` invariance. `kern2_radial_symPlaq`: at `D = SymPlaqClass`, from the cube-moment bound `hcube` on
  the plaquette class and `pyth` invariance (`ObserverSymField.observerSO4_symPlaq`).

## What does not follow, plainly

* Radiality is not unconditional. The tree proves invariance under the signed permutations only
  (`kern2_signed`); the rotations of `SO(4)` that are not signed permutations rest on invariance of
  the limit under `pyth`. At `D = SymPlaqClass` the tree reduces that to `ObserverAxioms.PythLatticeFlow`
  (the rotation-breaking part of the lattice readings vanishes along `ultra`), which is not proved; for
  other `D` the `pyth` invariance is a bare hypothesis.
* `CovC` is not the input here and does not give it. `CovC` (and `FlowCovN.FlowCovLim`, equivalent to it
  under `ExpandMatch` by `FlowSym.flowSym_iff_covC_wardT`) is a statement about `contC` of the composite
  family `CRen N z μ`; `kern2` reads `contSF (energy0 W D hD)`. No theorem of the tree identifies the two
  limits, so `covC_twoPoint` does not transport to `kern2`. The input `kern2` needs is `pyth` invariance
  of `contSF (energy0 W D hD)`.
* For test functions that are not `O(4)` invariant, `kern2 A B` is covariant (`kern2_cov`), not
  radial. Radiality of the pointwise kernel `S` of `ShellLorentz` step (b) needs that kernel, which is
  not built (`CompKernel`, "What does not follow").
* "Scalar" here is `HypScalar` (invariance of the lattice field under the hypercubic group) with the
  field kept under rotation; it is not `ShellLorentz.Scalar`, which is a property of a `Composites`
  representation.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.KernRadial

open Matrix
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverEnergyBox
  MassGap.ObserverRotation MassGap.ObserverRotationDense MassGap.ObserverAxisN
  MassGap.ObserverSymField MassGap.CompKernel MassGap.ShellLorentz
open MassGap.ShellTranslate (uniformContinuous_translate)

noncomputable section

variable {N : ℕ}

/-! ## 1. The action on the regular class -/

/-- **A smeared field with its test function composed with `M`**: `(O, f ∘ M)`.
DERIVED: no numeral. -/
def rotSF (M : Matrix (Fin 4) (Fin 4) ℝ) (A : SField N) : SField N := (A.1, rotTest M A.2)

/-- **The action of `R ∈ O(4)`**: `(O, f ∘ R⁻¹)`, with `R⁻¹ = Rᵀ`. The field is kept (scalar).
DERIVED: no numeral. -/
def act (R : Matrix (Fin 4) (Fin 4) ℝ) (A : SField N) : SField N := rotSF Rᵀ A

/-- **Orthogonality in transpose form.** DERIVED: `1` the identity. -/
theorem mem_orth_iff (R : Matrix (Fin 4) (Fin 4) ℝ) :
    R ∈ Matrix.orthogonalGroup (Fin 4) ℝ ↔ Rᵀ * R = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff']

/-- **A translated test function, rotated.** DERIVED: `1` the identity. -/
theorem rotTest_translate (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * M = 1) (f : TestFn)
    (v : Fin 4 → ℝ) : rotTest M (f.translate v) = (rotTest M f).translate (Mᵀ *ᵥ v) := by
  have hMM : M * Mᵀ = 1 := mul_eq_one_comm.mp hM
  apply Subtype.ext
  funext y
  rw [rotTest_apply M hM]
  show f.1 (M *ᵥ y - v) = (rotTest M f).1 (y - Mᵀ *ᵥ v)
  rw [rotTest_apply M hM, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]

/-- **The action commutes with translation, moving the shift by `R`.** DERIVED: `1` the identity. -/
theorem act_translate (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : Rᵀ * R = 1) (B : SField N)
    (z : Fin 4 → ℝ) : act R (B.1, B.2.translate z) = (B.1, (act R B).2.translate (R *ᵥ z)) := by
  have hM : Rᵀᵀ * Rᵀ = 1 := by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hR
  show (B.1, rotTest Rᵀ (B.2.translate z)) = (B.1, (rotTest Rᵀ B.2).translate (R *ᵥ z))
  rw [rotTest_translate Rᵀ hM, Matrix.transpose_transpose]

/-! ## 2. How `kern2` transforms -/

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)

/-- **Covariance of `kern2` from invariance of one two-factor family.** DERIVED: `Fin 2` the two
factors. -/
theorem kern2_rot (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * M = 1) (A B : SField N)
    (z : Fin 4 → ℝ)
    (hinv : contSF hN (energy0 W D hD) (rotFam M (![A, (B.1, B.2.translate z)] : Fin 2 → SField N))
      = contSF hN (energy0 W D hD) (![A, (B.1, B.2.translate z)] : Fin 2 → SField N)) :
    kern2 hN W hD (rotSF M A) (rotSF M B) (Mᵀ *ᵥ z) = kern2 hN W hD A B z := by
  unfold kern2
  rw [← hinv]
  congr 1
  funext i
  fin_cases i
  · rfl
  · show (B.1, (rotTest M B.2).translate (Mᵀ *ᵥ z)) = (B.1, rotTest M (B.2.translate z))
    rw [rotTest_translate M hM]

/-- **The hypercubic rotations, unconditionally.** For a configuration flow commuting with the axis
permutations, `HypScalar` fields of `D` and a signed permutation matrix `M`, `kern2` is covariant.
DERIVED: `Fin 2` the two factors; `1` and `-1` the signs. -/
theorem kern2_signed
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : Mᵀ * M = 1)
    (hsg : ∃ (σ : Equiv.Perm (Fin 4)) (sg : Fin 4 → ℝ), (∀ i, sg i = 1 ∨ sg i = -1) ∧
      ∀ y i, M.mulVec y i = sg i * y (σ i))
    (A B : SField N) (hA : A.1 ∈ D) (hB : B.1 ∈ D) (hAs : HypScalar A.1) (hBs : HypScalar B.1)
    (z : Fin 4 → ℝ) :
    kern2 hN W hD (rotSF M A) (rotSF M B) (Mᵀ *ᵥ z) = kern2 hN W hD A B z := by
  set F : Fin 2 → SField N := ![A, (B.1, B.2.translate z)] with hF
  have hFD : ∀ i, (F i).1 ∈ D := Fin.forall_fin_two.mpr ⟨hA, hB⟩
  have hFH : ∀ i, HypScalar (F i).1 := Fin.forall_fin_two.mpr ⟨hAs, hBs⟩
  refine kern2_rot hN W hD M hM A B z ?_
  rw [contSF_energy0_eq hN W hD (rotFam M F) hFD, contSF_energy0_eq hN W hD F hFD]
  exact signed_of_axisCov hN _ (scaled_axisCov W hW (s0 N) (s0_refl N) (fun _ _ _ => rfl)) M hsg F
    (rotFam M F) hFH (fun i => rfl) (fun i y => rotTest_apply M hM (F i).2 y)

/-- **Invariance of the limit under every orthogonal matrix** on families of `Φs`-fields with
uniformly continuous test functions. DERIVED: `1` the identity; `4` the dimension. -/
def O4Inv (Φ : Flow N) (Φs : Set (LField (MassGap.SUN.SU N))) : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
    (∀ i, (F i).1 ∈ Φs) → (∀ i, UniformContinuous (F i).2.1) → contSF hN Φ (rotFam R F) = contSF hN Φ F

/-- DERIVED: `1` the identity. -/
theorem refl1_mul_self : refl1 * refl1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [refl1, Matrix.mul_apply, Fin.sum_univ_four]

/-- DERIVED: `-1` the determinant of a reflection. -/
theorem det_refl1 : refl1.det = -1 := by
  have e : refl1 = Matrix.diagonal (![1, -1, 1, 1] : Fin 4 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [refl1]
  have h2 : (![1, -1, 1, 1] : Fin 4 → ℝ) 2 = 1 := rfl
  have h3 : (![1, -1, 1, 1] : Fin 4 → ℝ) 3 = 1 := rfl
  rw [e, Matrix.det_diagonal, Fin.prod_univ_four, h2, h3]
  norm_num

/-- **`O(4)` from `SO(4)` and one reflection.** DERIVED: `1` and `-1` the two determinants. -/
theorem o4Inv_of_so4 (Φ : Flow N) (Φs : Set (LField (MassGap.SUN.SU N)))
    (hSO : ObserverSO4 hN Φ Φs)
    (hrefl : ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ Φs) →
      (∀ i, UniformContinuous (F i).2.1) → contSF hN Φ (rotFam refl1 F) = contSF hN Φ F) :
    O4Inv hN Φ Φs := by
  intro R hR ι _ F hF hU
  have hRO : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ := (mem_orth_iff R).mpr hR
  have hdet : R.det * R.det = 1 := by
    have h := congrArg Matrix.det hR
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rcases mul_self_eq_one_iff.mp hdet with h1 | h1
  · exact hSO R (Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨hRO, h1⟩) ι F hF hU
  · have hrR : (refl1 * R)ᵀ * (refl1 * R) = 1 := transpose_mul_self_mul hR refl1_orth
    have hSOm : refl1 * R ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ :=
      Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨(mem_orth_iff _).mpr hrR, by
        rw [Matrix.det_mul, det_refl1, h1]; norm_num⟩
    have e : rotFam R F = rotFam (refl1 * R) (rotFam refl1 F) := by
      rw [rotFam_rotFam hrR refl1_orth, ← Matrix.mul_assoc, refl1_mul_self, Matrix.one_mul]
    rw [e, hSO _ hSOm ι (rotFam refl1 F) hF (fun i => uniformContinuous_rotTest refl1_orth (hU i))]
    exact hrefl ι F hF hU

/-- **`O(4)` for the observer's energy density from the cube-moment bound `hcube` and `pyth`.** DERIVED: `0` the excluded colour
count; `4` the dimension. -/
theorem o4Inv_energy0
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ D ∧ HypScalar (F i).1) →
      (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W D hD) (rotFam pyth F) = contSF hN (energy0 W D hD) F) :
    O4Inv hN (energy0 W D hD) {O | O ∈ D ∧ HypScalar O} := by
  refine o4Inv_of_so4 hN _ _ (observerSO4_energy0 hN W hW hD hpos hcube hpyth)
    (fun ι _ F hF _ => ?_)
  rw [contSF_energy0_eq hN W hD (rotFam refl1 F) (fun i => (hF i).1),
    contSF_energy0_eq hN W hD F (fun i => (hF i).1)]
  exact signed_of_axisCov hN _ (scaled_axisCov W hW (s0 N) (s0_refl N) (fun _ _ _ => rfl)) refl1
    refl1_signed F (rotFam refl1 F) (fun i => (hF i).2) (fun i => rfl)
    (fun i y => rotTest_apply refl1 refl1_orth (F i).2 y)

/-- **`kern2` is `O(4)` covariant under `O4Inv`.** DERIVED: `Fin 2` the two factors; `1` the
identity. -/
theorem kern2_cov {Φs : Set (LField (MassGap.SUN.SU N))} (hO4 : O4Inv hN (energy0 W D hD) Φs)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : Rᵀ * R = 1) (A B : SField N) (hA : A.1 ∈ Φs)
    (hB : B.1 ∈ Φs) (hAu : UniformContinuous A.2.1) (hBu : UniformContinuous B.2.1)
    (z : Fin 4 → ℝ) :
    kern2 hN W hD (act R A) (act R B) (R *ᵥ z) = kern2 hN W hD A B z := by
  have hM : Rᵀᵀ * Rᵀ = 1 := by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hR
  have h := kern2_rot hN W hD Rᵀ hM A B z (hO4 Rᵀ hM (Fin 2) _
    (Fin.forall_fin_two.mpr ⟨hA, hB⟩)
    (Fin.forall_fin_two.mpr ⟨hAu, uniformContinuous_translate hBu z⟩))
  rwa [Matrix.transpose_transpose] at h

/-! ## 3. Radiality -/

/-- **`kern2` is `O(4)` invariant** for `O(4)`-invariant test functions, under `O4Inv`.
DERIVED: `1` the identity. -/
theorem kern2_orthInv {Φs : Set (LField (MassGap.SUN.SU N))} (hO4 : O4Inv hN (energy0 W D hD) Φs)
    (A B : SField N) (hA : A.1 ∈ Φs) (hB : B.1 ∈ Φs) (hAu : UniformContinuous A.2.1)
    (hBu : UniformContinuous B.2.1)
    (hfA : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R A.2 = A.2)
    (hfB : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R B.2 = B.2) :
    OrthInv (kern2 hN W hD A B) := by
  intro R hRO x
  have hR : Rᵀ * R = 1 := (mem_orth_iff R).mp hRO
  have hM : Rᵀᵀ * Rᵀ = 1 := by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hR
  have eA : act R A = A := Prod.ext rfl (hfA Rᵀ hM)
  have eB : act R B = B := Prod.ext rfl (hfB Rᵀ hM)
  have h := kern2_cov hN W hD hO4 R hR A B hA hB hAu hBu x
  rwa [eA, eB] at h

/-- **`kern2` is radial** for `O(4)`-invariant test functions, under `O4Inv`
(`ShellLorentz.radial_iff_orthInv`). DERIVED: `1` the identity. -/
theorem kern2_radial {Φs : Set (LField (MassGap.SUN.SU N))} (hO4 : O4Inv hN (energy0 W D hD) Φs)
    (A B : SField N) (hA : A.1 ∈ Φs) (hB : B.1 ∈ Φs) (hAu : UniformContinuous A.2.1)
    (hBu : UniformContinuous B.2.1)
    (hfA : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R A.2 = A.2)
    (hfB : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R B.2 = B.2) :
    Radial (kern2 hN W hD A B) :=
  (radial_iff_orthInv _).mpr (kern2_orthInv hN W hD hO4 A B hA hB hAu hBu hfA hfB)

/-- **Radiality of `kern2` for the observer's energy density, from the cube-moment bound `hcube` and `pyth`.** DERIVED: `0` the
excluded colour count; `1` the identity. -/
theorem kern2_radial_of_pyth
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ D ∧ HypScalar (F i).1) →
      (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W D hD) (rotFam pyth F) = contSF hN (energy0 W D hD) F)
    (A B : SField N) (hA : A.1 ∈ D) (hB : B.1 ∈ D) (hAs : HypScalar A.1) (hBs : HypScalar B.1)
    (hAu : UniformContinuous A.2.1) (hBu : UniformContinuous B.2.1)
    (hfA : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R A.2 = A.2)
    (hfB : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R B.2 = B.2) :
    Radial (kern2 hN W hD A B) :=
  kern2_radial hN W hD (o4Inv_energy0 hN W hD hW hpos hcube hpyth) A B ⟨hA, hAs⟩ ⟨hB, hBs⟩ hAu hBu
    hfA hfB

/-- **Radiality on the symmetrised plaquette class**, from the cube-moment bound `hcube` on the plaquette class and `pyth`.
DERIVED: `0` the excluded colour count; `1` the identity. -/
theorem kern2_radial_symPlaq
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
      (∀ i, (F i).1 ∈ SymPlaqClass N ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (rotFam pyth F)
          = contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) F)
    (A B : SField N) (hA : A.1 ∈ SymPlaqClass N) (hB : B.1 ∈ SymPlaqClass N)
    (hAu : UniformContinuous A.2.1) (hBu : UniformContinuous B.2.1)
    (hfA : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R A.2 = A.2)
    (hfB : ∀ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 → rotTest R B.2 = B.2) :
    Radial (kern2 hN W (symPlaq_refl N) A B) :=
  kern2_radial_of_pyth hN W (symPlaq_refl N) hW (symPlaq_nonneg hN) (symPlaq_cube hN W hW hcube)
    hpyth A B hA hB (symPlaq_hypScalar A.1 hA) (symPlaq_hypScalar B.1 hB) hAu hBu hfA hfB

end

end MassGap.KernRadial

#print axioms MassGap.KernRadial.mem_orth_iff
#print axioms MassGap.KernRadial.rotTest_translate
#print axioms MassGap.KernRadial.act_translate
#print axioms MassGap.KernRadial.kern2_rot
#print axioms MassGap.KernRadial.kern2_signed
#print axioms MassGap.KernRadial.refl1_mul_self
#print axioms MassGap.KernRadial.det_refl1
#print axioms MassGap.KernRadial.o4Inv_of_so4
#print axioms MassGap.KernRadial.o4Inv_energy0
#print axioms MassGap.KernRadial.kern2_cov
#print axioms MassGap.KernRadial.kern2_orthInv
#print axioms MassGap.KernRadial.kern2_radial
#print axioms MassGap.KernRadial.kern2_radial_of_pyth
#print axioms MassGap.KernRadial.kern2_radial_symPlaq
