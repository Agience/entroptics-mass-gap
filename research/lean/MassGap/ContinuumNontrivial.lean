import Mathlib
import MassGap.ContinuumSep
import MassGap.ShortDistanceY

noncomputable section

/-!
# MassGap.ContinuumNontrivial — `ConnectedTwoPointNonzero` from a lattice kernel limit and requirement Y

`ContinuumSep.exists_orth_ne_zero_sep` turns `ContinuumSep.ConnectedTwoPointNonzero hN ρ τ`
(`S(θQ ∪ Q) − S(Q)² ≠ 0` for one separated positive-time monomial `Q`) into a non-zero vector of the
reconstructed Hilbert space orthogonal to the vacuum. This file derives that hypothesis for the
connected composites `Renorm.connected hN Z` from a stated limit of the lattice two-point kernel.

## The monomial

`Q = mono1 (O, cubeTest t ℓ)`: one factor, the local gauge-invariant field `O` smeared against the
indicator of the cube `[t, t + ℓ]⁴` (`cubeTest`). Its support lies in `y_τ ≥ t`, so `Q` is a
separated positive-time monomial at margin `t` (`sepPos_mono1`).

## The Riemann-sum identity

`latSkR_mono1_pair`: at step `k`, with `a = dySpacing N k` and reflection-compatible data,

    latSkR(θQ ∪ Q) = ∑_{x, y} (a⁴ f(θ(a x))) (a⁴ f(a y)) · latKernel k x y,

a finite double sum over the box of `ContinuumField.smear_eq_sum`, where
`latKernel k x y = Z_k(O)² · ν_k(T_x θ(O − c) · T_y (O − c))`. For the connected composites
(`c = ν_k(O)`) the kernel is `Z_k(O)²` times the connected two-point function
`ThreePointN.cov2 ν_k (T_x θO) (T_y O)` (`latKernel_connected`); at `Z_k = a⁻⁴` (`rhoA`) it is that
function divided by `a⁸` (`latKernel_rhoA`), the normalisation of `ShortDistanceY.latticeTwoPoint`.

## The vacuum term

`kern_empty_mono1`: for the connected composites `S(Q) = 0` exactly. Every lattice term
`ν_k(T_x (O − ν_k O))` vanishes by translation invariance of the periodic state, so the sequence is
identically `0`.

## The open input

`KernelConvergesSep hN ρ τ O G₂`: for every separation `d > 0` and radius `R`, `latKernel k x y`
converges to `G₂(a x, a y)` uniformly over lattice pairs whose physical points are `d`-separated in
sup-distance and lie in `[-R, R]⁴`. Only separated points enter, as in `UniformBoundSep`. With
`G₂ p q = G(|p − q|)` it also carries rotation invariance of the limit and the identification of the
radial profile `G`.

## The result

* `kern_mono1_ge`: if `g₀ ≤ G₂ ≤ g₁` on the pairs `(θ-cube) × cube` with `g₀ > 0`, then
  `S(θQ ∪ Q) ≥ (g₀/2)(ℓ/2)⁸ > 0`. The lattice sequence is bounded eventually (so it converges along
  `ultra` and `kern` is that limit, with no `UniformBoundSep` needed) and eventually at least `(g₀/2)(ℓ/2)⁸`:
  the kernel is within `g₀/2` of `G₂` on the support (`double_sum_lower`, `double_sum_upper`), and the
  two Riemann sums of the cube indicator lie between `(ℓ/2)⁴` (`riemann_cube_ge`, `riemann_refl_cube_ge`, a
  lattice sub-box count) and `(2(|t| + |ℓ|) + 3)⁴` (`riemann_le`).
* `connectedTwoPointNonzero_of_kernel`: hence `ConnectedTwoPointNonzero`.
* `af_bounds_on_interval`: `ShortDistanceY.AFShortDistance G` bounds `G` above and below by positive
  constants on every `[r₁, r₂] ⊂ (0, δ)`.
* `connectedTwoPointNonzero_of_af`: `KernelConvergesSep` towards `G(|p − q|)` and
  `AFShortDistance G` give `ConnectedTwoPointNonzero` for `Renorm.connected hN Z`;
  `connectedTwoPointNonzero_rhoA` at `Z_k = a⁻⁴`; `exists_orth_ne_zero_of_af` gives the vector.

## Scope

`KernelConvergesSep` is a hypothesis, not proved here. The Riemann sums are bounded, not taken to the
integral `∬ f(θx) f(y) G₂(x, y)`; the lower bound is what the non-vanishing needs.
-/

namespace MassGap.ContinuumNontrivial

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The cube test function -/

section Cube

/-- The closed cube `[t, t + ℓ]⁴`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def timeCube (t ℓ : ℝ) : Set (Fin 4 → ℝ) := {y | ∀ i, t ≤ y i ∧ y i ≤ t + ℓ}

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem mem_timeCube {t ℓ : ℝ} {y : Fin 4 → ℝ} :
    y ∈ timeCube t ℓ ↔ ∀ i, t ≤ y i ∧ y i ≤ t + ℓ := Iff.rfl

#print axioms mem_timeCube

/-- The indicator of the cube `[t, t + ℓ]⁴`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. CHOSEN: the value `1` on the cube; any positive
constant serves. -/
def cubeInd (t ℓ : ℝ) : (Fin 4 → ℝ) → ℝ := Set.indicator (timeCube t ℓ) (fun _ => 1)

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is `cubeInd`'s value on the cube. -/
theorem cubeInd_of_mem {t ℓ : ℝ} {y : Fin 4 → ℝ} (h : y ∈ timeCube t ℓ) : cubeInd t ℓ y = 1 :=
  Set.indicator_of_mem h _

#print axioms cubeInd_of_mem

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the value off the cube. -/
theorem cubeInd_of_not_mem {t ℓ : ℝ} {y : Fin 4 → ℝ} (h : y ∉ timeCube t ℓ) :
    cubeInd t ℓ y = 0 :=
  Set.indicator_of_notMem h _

#print axioms cubeInd_of_not_mem

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign. -/
theorem cubeInd_nonneg (t ℓ : ℝ) (y : Fin 4 → ℝ) : 0 ≤ cubeInd t ℓ y := by
  by_cases h : y ∈ timeCube t ℓ
  · rw [cubeInd_of_mem h]
    exact zero_le_one
  · exact le_of_eq (cubeInd_of_not_mem h).symm

#print axioms cubeInd_nonneg

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the value off the cube. -/
theorem mem_timeCube_of_cubeInd_ne {t ℓ : ℝ} {y : Fin 4 → ℝ} (h : cubeInd t ℓ y ≠ 0) :
    y ∈ timeCube t ℓ := by
  by_contra h'
  exact h (cubeInd_of_not_mem h')

#print axioms mem_timeCube_of_cubeInd_ne

/-- Every coordinate of a point of the cube is at most `|t| + |ℓ|` in absolute value.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem abs_le_of_mem_timeCube {t ℓ : ℝ} {y : Fin 4 → ℝ} (h : y ∈ timeCube t ℓ) (i : Fin 4) :
    |y i| ≤ |t| + |ℓ| := by
  obtain ⟨h1, h2⟩ := mem_timeCube.mp h i
  have ht := abs_le.mp (le_refl |t|)
  have hl := abs_le.mp (le_refl |ℓ|)
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2, hl.1, hl.2]

#print axioms abs_le_of_mem_timeCube

/-- The cube indicator is a test function: support in `[-(|t| + |ℓ|), |t| + |ℓ|]⁴`, bound `1`.

DERIVED: `1` is the indicator's value, its sup bound; `0` is the value off the cube, in the proof. -/
theorem isTest_cubeInd (t ℓ : ℝ) : IsTest (cubeInd t ℓ) (|t| + |ℓ|) 1 := by
  refine ⟨add_nonneg (abs_nonneg t) (abs_nonneg ℓ), fun y => ?_,
    fun y hy i => abs_le_of_mem_timeCube (mem_timeCube_of_cubeInd_ne hy) i⟩
  by_cases h : y ∈ timeCube t ℓ
  · have h1 : |cubeInd t ℓ y| = 1 := by rw [cubeInd_of_mem h, abs_one]
    exact le_of_eq h1
  · have h0 : |cubeInd t ℓ y| = 0 := by rw [cubeInd_of_not_mem h, abs_zero]
    rw [h0]
    exact zero_le_one

#print axioms isTest_cubeInd

/-- **The cube test function** `1_{[t, t+ℓ]⁴}`.

DERIVED: `4` is the spacetime dimension; `1` is the sup bound of `isTest_cubeInd`. -/
def cubeTest (t ℓ : ℝ) : TestFn := ⟨cubeInd t ℓ, |t| + |ℓ|, 1, isTest_cubeInd t ℓ⟩

/-- DERIVED: `1` is the sup bound of the indicator. -/
theorem isTest_cubeTest (t ℓ : ℝ) : IsTest (cubeTest t ℓ).1 (|t| + |ℓ|) 1 := isTest_cubeInd t ℓ

#print axioms isTest_cubeTest

/-- The reflected test function keeps the support radius and the bound.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem isTest_reflect (τ : Fin 4) {f : TestFn} {R M : ℝ} (hf : IsTest f.1 R M) :
    IsTest (f.reflect τ).1 R M :=
  ⟨hf.1, fun y => hf.2.1 (reflR τ y), fun y hy i => by
    rw [← abs_reflR τ y i]
    exact hf.2.2 (reflR τ y) hy i⟩

#print axioms isTest_reflect

end Cube

/-! ## 2. The one-factor monomial -/

section Mono1

/-- The monomial with the single factor `p`.

DERIVED: `1` is the number of factors. -/
def mono1 (p : SField N) : Mono N := ⟨1, fun _ => p⟩

/-- DERIVED: `1` is the number of factors, through `Fin.prod_univ_one`. -/
theorem zmono_mono1 (ρ : Renorm N) (k : ℕ) (O : LField (MassGap.SUN.SU N)) (f : TestFn) :
    ρ.zmono k (mono1 (O, f)) = ρ.Z k O := by
  show (∏ _i : Fin 1, ρ.Z k O) = ρ.Z k O
  exact Fin.prod_univ_one _

#print axioms zmono_mono1

/-- DERIVED: `1` is the number of factors, through `Fin.prod_univ_one`. -/
theorem prodSmear_mono1 (ρ : Renorm N) (k : ℕ) (a : ℝ) (O : LField (MassGap.SUN.SU N))
    (f : TestFn) :
    prodSmear a (ρ.mono k (mono1 (O, f))) = smear a (O.sub (ρ.c k O)).1 f := by
  show (∏ _i : Fin 1, smear a (O.sub (ρ.c k O)).1 f) = smear a (O.sub (ρ.c k O)).1 f
  exact Fin.prod_univ_one _

#print axioms prodSmear_mono1

/-- The renormalised observable of the one-factor monomial.

DERIVED: no numeral. -/
theorem Yv_mono1 (ρ : Renorm N) (k : ℕ) (O : LField (MassGap.SUN.SU N)) (f : TestFn) :
    Yv ρ k (mono1 (O, f)) = ρ.Z k O • smear (dySpacing N k) (O.sub (ρ.c k O)).1 f := by
  show ρ.zmono k (mono1 (O, f)) • prodSmear (dySpacing N k) (ρ.mono k (mono1 (O, f))) = _
  rw [zmono_mono1, prodSmear_mono1]

#print axioms Yv_mono1

/-- **The cube monomial is a separated positive-time monomial** at margin `t`: its one test function
vanishes below `y_τ = t`, and one factor has no pair to separate.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is the number of factors. -/
theorem sepPos_mono1 (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) :
    ContinuumSep.sepPos τ t (mono1 (O, cubeTest t ℓ)) :=
  ⟨fun _ y hy => (mem_timeCube.mp (mem_timeCube_of_cubeInd_ne (t := t) (ℓ := ℓ) (y := y) hy) τ).1,
    fun i j hij => absurd (Subsingleton.elim (α := Fin 1) i j) hij⟩

#print axioms sepPos_mono1

/-- The cube monomial as an element of `SepMono N τ`, at margin `t > 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the margin. -/
def sepCube (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) {t : ℝ} (ht : 0 < t) (ℓ : ℝ) :
    ContinuumSep.SepMono N τ :=
  ⟨mono1 (O, cubeTest t ℓ), t, ht, sepPos_mono1 τ O t ℓ⟩

end Mono1

/-! ## 3. Translation and reflection invariance of the step states -/

section StateK

/-- DERIVED: `0` is the excluded colour count. The four unit shifts enter through
`PeriodicState.periodicState_shift`. -/
theorem stateK_transObs (hN : N ≠ 0) (k : ℕ) (x : ISite) (F : C(Cfg N, ℝ)) :
    stateK hN k (transObs x F) = stateK hN k F :=
  state_transObs (ν := stateK hN k) (fun τ => PeriodicState.periodicState_shift hN _ τ) x F

#print axioms stateK_transObs

/-- DERIVED: `0` is the excluded colour count and the reflection constant, the plane `x_τ = 0`;
`4` in `Fin 4` is the spacetime dimension. -/
theorem stateK_refl (hN : N ≠ 0) (k : ℕ) (τ : Fin 4) (F : C(Cfg N, ℝ)) :
    stateK hN k (LatticeReflection.ireflObs τ 0 F) = stateK hN k F :=
  PeriodicState.periodicState_reflInvariant hN (dyBeta (one_le_of_ne_zero hN) k) τ 0 F

#print axioms stateK_refl

/-- **A connected smeared field has mean zero at every step**: `ν_k(smear (O − ν_k O) f) = 0`, term
by term by translation invariance.

DERIVED: `0` is the excluded colour count and the value. -/
theorem stateK_smear_connected (hN : N ≠ 0) (k : ℕ) (O : LField (MassGap.SUN.SU N)) (f : TestFn) :
    stateK hN k (smear (dySpacing N k) (O.sub (stateK hN k O.1)).1 f) = 0 := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum (dySpacing_pos (one_le_of_ne_zero hN) k) _ f hf (Finset.Subset.refl _),
    (stateK hN k).map_sum]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [(stateK hN k).map_smul, stateK_transObs]
  show _ * stateK hN k (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))) = 0
  rw [(stateK hN k).map_sub, (stateK hN k).map_smul, (stateK hN k).map_one, mul_one, sub_self,
    mul_zero]

#print axioms stateK_smear_connected

end StateK

/-! ## 4. The lattice kernel and the Riemann-sum identity -/

section Kernel

/-- **The lattice two-point kernel of step `k`** between the reflected field at site `x` and the
field at site `y`: `Z_k(O)² · ν_k(T_x θ(O − c_k O) · T_y (O − c_k O))`, `θ = ireflObs τ 0`.

DERIVED: `2` is the two factors of `θQ ∪ Q`, each carrying `Z_k(O)`; `0` is the excluded colour
count and the reflection constant; `4` in `Fin 4` is the spacetime dimension. -/
noncomputable def latKernel (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (k : ℕ) (x y : ISite) : ℝ :=
  ρ.Z k O ^ 2 * stateK hN k
    (transObs x (LatticeReflection.ireflObs τ 0 (O.sub (ρ.c k O)).1)
      * transObs y (O.sub (ρ.c k O)).1)

/-- **The Riemann-sum identity.** For reflection-compatible data and a test function `f` supported
in `[-R, R]⁴`, at step `k` with `a = dySpacing N k`,
`latSkR(θQ ∪ Q) = ∑_{x,y ∈ box} (a⁴ (θf)(a x)) (a⁴ f(a y)) · latKernel k x y` for `Q = mono1 (O, f)`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension and the
exponent of the cell volume `a⁴`. -/
theorem latSkR_mono1_pair (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hR : ρ.ReflCompat τ) (k : ℕ)
    (O : LField (MassGap.SUN.SU N)) (f : TestFn) {R M : ℝ} (hf : IsTest f.1 R M) :
    latSkR hN ρ k (pairFam τ (mono1 (O, f)) (mono1 (O, f)))
      = ∑ x ∈ box ⌈R / dySpacing N k⌉₊, ∑ y ∈ box ⌈R / dySpacing N k⌉₊,
          (dySpacing N k ^ 4 * (f.reflect τ).1 (site (dySpacing N k) x))
            * (dySpacing N k ^ 4 * f.1 (site (dySpacing N k) y)) * latKernel hN ρ τ O k x y := by
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  rw [latSkR_pairFam hN ρ τ hR k, latSk_eq, latS_pairFam _ ha, zmono_mono1, prodSmear_mono1,
    ireflObs_smear ha τ,
    smear_eq_sum ha _ (f.reflect τ) (isTest_reflect τ hf) (Finset.Subset.refl _),
    smear_eq_sum ha _ f hf (Finset.Subset.refl _), Finset.sum_mul_sum, (stateK hN k).map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [(stateK hN k).map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [smul_mul_smul_comm, (stateK hN k).map_smul]
  unfold latKernel
  ring

#print axioms latSkR_mono1_pair

/-- **For the connected composites the kernel is the connected two-point function**:
`latKernel k x y = Z_k(O)² · cov2 ν_k (T_x θO) (T_y O)`.

DERIVED: `2` is `latKernel`'s; `0` is the excluded colour count and the reflection constant; `4` in
`Fin 4` is the spacetime dimension. -/
theorem latKernel_connected (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (O : LField (MassGap.SUN.SU N)) (k : ℕ) (x y : ISite) :
    latKernel hN (Renorm.connected hN Z) τ O k x y
      = Z k O ^ 2 * ThreePointN.cov2 (stateK hN k)
          (transObs x (LatticeReflection.ireflObs τ 0 O.1)) (transObs y O.1) := by
  have e1 : LatticeReflection.ireflObs τ 0 (1 : C(Cfg N, ℝ)) = 1 := rfl
  have hA : transObs x (LatticeReflection.ireflObs τ 0 (O.sub (stateK hN k O.1)).1)
      = ThreePointN.cen (stateK hN k) (transObs x (LatticeReflection.ireflObs τ 0 O.1)) := by
    rw [ThreePointN.cen, stateK_transObs, stateK_refl]
    show transObs x (LatticeReflection.ireflObs τ 0 (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))))
      = _
    simp only [map_sub, map_smul]
    rw [e1, transObs_one]
  have hB : transObs y (O.sub (stateK hN k O.1)).1
      = ThreePointN.cen (stateK hN k) (transObs y O.1) := by
    rw [ThreePointN.cen, stateK_transObs]
    show transObs y (O.1 - stateK hN k O.1 • (1 : C(Cfg N, ℝ))) = _
    simp only [map_sub, map_smul]
    rw [transObs_one]
  show Z k O ^ 2 * stateK hN k
      (transObs x (LatticeReflection.ireflObs τ 0 (O.sub (stateK hN k O.1)).1)
        * transObs y (O.sub (stateK hN k O.1)).1) = _
  rw [hA, hB]
  rfl

#print axioms latKernel_connected

/-- **The explicit renormalisation**: the connected composites `a⁻⁴ (O − ν_k O)` at
`a = dySpacing N k`, for every field.

DERIVED: `4` is the canonical dimension of `tr F²` in four dimensions, one `a⁻⁴` per insertion; `0`
is the excluded colour count in `hN`.
CHOSEN: the constant `1` in front of `a⁻⁴`; a coupling normalisation rescales `latKernel` by its
square and is absorbed into the limit `G₂`. -/
noncomputable def rhoA (hN : N ≠ 0) : Renorm N :=
  Renorm.connected hN (fun j _ => (dySpacing N j ^ 4)⁻¹)

/-- **At `rhoA` the kernel is the lattice connected two-point function divided by `a⁸`**, the
normalisation of `ShortDistanceY.latticeTwoPoint`.

DERIVED: `8 = 2·4`, one `a⁻⁴` per insertion; `0` is the excluded colour count and the reflection
constant; `4` in `Fin 4` is the spacetime dimension. -/
theorem latKernel_rhoA (hN : N ≠ 0) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)) (k : ℕ)
    (x y : ISite) :
    latKernel hN (rhoA hN) τ O k x y
      = ThreePointN.cov2 (stateK hN k)
          (transObs x (LatticeReflection.ireflObs τ 0 O.1)) (transObs y O.1) / dySpacing N k ^ 8 := by
  have h := latKernel_connected hN (fun j _ => (dySpacing N j ^ 4)⁻¹) τ O k x y
  have e : latKernel hN (rhoA hN) τ O k x y
      = latKernel hN (Renorm.connected hN (fun j _ => (dySpacing N j ^ 4)⁻¹)) τ O k x y := rfl
  rw [e, h]
  show (dySpacing N k ^ 4)⁻¹ ^ 2 * ThreePointN.cov2 (stateK hN k)
      (transObs x (LatticeReflection.ireflObs τ 0 O.1)) (transObs y O.1) = _
  ring

#print axioms latKernel_rhoA

end Kernel

/-! ## 5. The vacuum term vanishes -/

section Vacuum

/-- For the connected composites the lattice one-point function of the cube monomial vanishes at every
step.

DERIVED: `0` is the excluded colour count, the reflection constant and the value; `4` in `Fin 4` is
the spacetime dimension. -/
theorem latSkR_empty_mono1 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (k : ℕ) (O : LField (MassGap.SUN.SU N)) (f : TestFn) :
    latSkR hN (Renorm.connected hN Z) k (pairFam τ (emptyMono N) (mono1 (O, f))) = 0 := by
  have e1 : LatticeReflection.ireflObs τ 0 (1 : C(Cfg N, ℝ)) = 1 := rfl
  rw [latSkR_pairFam_eq hN _ τ (Renorm.connected_reflCompat hN Z τ hZ) k, Yv_empty, Yv_mono1, e1,
    one_mul, (stateK hN k).map_smul]
  show Z k O * stateK hN k (smear (dySpacing N k) (O.sub (stateK hN k O.1)).1 f) = 0
  rw [stateK_smear_connected, mul_zero]

#print axioms latSkR_empty_mono1

/-- **`S(Q) = 0` for the connected composites**: `kern ρ τ ∅ Q = 0` for `Q = mono1 (O, f)`, the
`ultra` limit of the identically zero sequence.

DERIVED: `0` is the excluded colour count and the value; `4` in `Fin 4` is the spacetime dimension. -/
theorem kern_empty_mono1 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (O : LField (MassGap.SUN.SU N)) (f : TestFn) :
    kern hN (Renorm.connected hN Z) τ (emptyMono N) (mono1 (O, f)) = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hfun : (fun k => latSkR hN (Renorm.connected hN Z) k (pairFam τ (emptyMono N) (mono1 (O, f))))
      = fun _ => (0 : ℝ) := funext (fun k => latSkR_empty_mono1 hN Z τ hZ k O f)
  show limUnder (ultra : Filter ℕ)
      (fun k => latSkR hN (Renorm.connected hN Z) k (pairFam τ (emptyMono N) (mono1 (O, f)))) = 0
  rw [hfun]
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨0, tendsto_const_nhds⟩) tendsto_const_nhds

#print axioms kern_empty_mono1

end Vacuum

/-! ## 6. Double sums against a nonnegative product weight -/

section DoubleSum

/-- **A kernel bounded below on the support bounds the double sum below**: for `u, v ≥ 0` and
`g ≤ K x y` wherever `u x ≠ 0` and `v y ≠ 0`, `g (∑u)(∑v) ≤ ∑∑ u x v y K x y`.

DERIVED: `0` is the sign of the weights and the vanishing weight. -/
theorem double_sum_lower {ι : Type*} (s : Finset ι) (u v : ι → ℝ) (K : ι → ι → ℝ) {g : ℝ}
    (hu : ∀ x ∈ s, 0 ≤ u x) (hv : ∀ y ∈ s, 0 ≤ v y)
    (hK : ∀ x ∈ s, ∀ y ∈ s, u x ≠ 0 → v y ≠ 0 → g ≤ K x y) :
    g * ((∑ x ∈ s, u x) * ∑ y ∈ s, v y) ≤ ∑ x ∈ s, ∑ y ∈ s, u x * v y * K x y := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun x hx => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun y hy => ?_)
  by_cases hux : u x = 0
  · rw [hux]
    simp
  by_cases hvy : v y = 0
  · rw [hvy]
    simp
  calc g * (u x * v y) = u x * v y * g := by ring
    _ ≤ u x * v y * K x y :=
        mul_le_mul_of_nonneg_left (hK x hx y hy hux hvy) (mul_nonneg (hu x hx) (hv y hy))

#print axioms double_sum_lower

/-- **A kernel bounded above on the support bounds the double sum above**: for `u, v ≥ 0` and
`K x y ≤ g` wherever `u x ≠ 0` and `v y ≠ 0`, `∑∑ u x v y K x y ≤ g (∑u)(∑v)`.

DERIVED: `0` is the sign of the weights and the vanishing weight. -/
theorem double_sum_upper {ι : Type*} (s : Finset ι) (u v : ι → ℝ) (K : ι → ι → ℝ) {g : ℝ}
    (hu : ∀ x ∈ s, 0 ≤ u x) (hv : ∀ y ∈ s, 0 ≤ v y)
    (hK : ∀ x ∈ s, ∀ y ∈ s, u x ≠ 0 → v y ≠ 0 → K x y ≤ g) :
    ∑ x ∈ s, ∑ y ∈ s, u x * v y * K x y ≤ g * ((∑ x ∈ s, u x) * ∑ y ∈ s, v y) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun x hx => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun y hy => ?_)
  by_cases hux : u x = 0
  · rw [hux]
    simp
  by_cases hvy : v y = 0
  · rw [hvy]
    simp
  calc u x * v y * K x y ≤ u x * v y * g :=
        mul_le_mul_of_nonneg_left (hK x hx y hy hux hvy) (mul_nonneg (hu x hx) (hv y hy))
    _ = g * (u x * v y) := by ring

#print axioms double_sum_upper

end DoubleSum

/-! ## 7. Riemann sums of the cube indicator -/

section Riemann

/-- **Upper bound on a Riemann sum**, uniform in the spacing: at `0 < a ≤ 1`, for `g` bounded by
`M` with support in `[-R, R]⁴`, `∑_{x ∈ box} a⁴ g(a x) ≤ M (2R + 3)⁴`.

DERIVED: `0` is the sign of `a`; `1` bounds `a`; `4` is the dimension and the cell-volume exponent;
`2` and `3` are `ContinuumField.norm_smear_le`'s: `2K + 1` sites per axis and
`a(2⌈R/a⌉ + 1) < 2R + 3a`. -/
theorem riemann_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {g : (Fin 4 → ℝ) → ℝ} {R M : ℝ}
    (hg : IsTest g R M) :
    ∑ x ∈ box ⌈R / a⌉₊, a ^ 4 * g (site a x) ≤ M * (2 * R + 3) ^ 4 := by
  have hM : 0 ≤ M := hg.M_nonneg
  have h4 : 0 ≤ a ^ 4 := pow_nonneg ha.le 4
  have hterm : ∀ x ∈ box ⌈R / a⌉₊, a ^ 4 * g (site a x) ≤ a ^ 4 * M :=
    fun x _ => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hg.2.1 _)) h4
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul, card_box] at hsum
  have hK : (⌈R / a⌉₊ : ℝ) < R / a + 1 := Nat.ceil_lt_add_one (div_nonneg hg.1 ha.le)
  have hK2 : ((⌈R / a⌉₊ : ℝ) - 1) * a < R := by
    have h1 : (⌈R / a⌉₊ : ℝ) - 1 < R / a := by linarith
    exact (lt_div_iff₀ ha).mp h1
  have hlin : a * (2 * (⌈R / a⌉₊ : ℝ) + 1) ≤ 2 * R + 3 := by nlinarith
  have hpow : (a * (2 * (⌈R / a⌉₊ : ℝ) + 1)) ^ 4 ≤ (2 * R + 3) ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg ha.le (by positivity)) hlin 4
  calc ∑ x ∈ box ⌈R / a⌉₊, a ^ 4 * g (site a x)
      ≤ (((2 * ⌈R / a⌉₊ + 1) ^ 4 : ℕ) : ℝ) * (a ^ 4 * M) := hsum
    _ = (a * (2 * (⌈R / a⌉₊ : ℝ) + 1)) ^ 4 * M := by push_cast; ring
    _ ≤ (2 * R + 3) ^ 4 * M := mul_le_mul_of_nonneg_right hpow hM
    _ = M * (2 * R + 3) ^ 4 := by ring

#print axioms riemann_le

/-- **Lower bound on a Riemann sum by a count**: for `g ≥ 0` with support in `[-R, R]⁴` and a finite
set `S` of sites on which `g(a x) ≥ 1`, `|S| a⁴ ≤ ∑_{x ∈ box} a⁴ g(a x)`.

DERIVED: `0` is the sign of `a` and of `g`; `1` is the level of `g` on `S`; `4` is the dimension
and the cell-volume exponent. -/
theorem card_mul_le_riemann {a : ℝ} (ha : 0 < a) {g : (Fin 4 → ℝ) → ℝ} {R M : ℝ}
    (hg : IsTest g R M) (hg0 : ∀ y, 0 ≤ g y) (S : Finset ISite)
    (hS : ∀ x ∈ S, 1 ≤ g (site a x)) :
    (S.card : ℝ) * a ^ 4 ≤ ∑ x ∈ box ⌈R / a⌉₊, a ^ 4 * g (site a x) := by
  have h4 : 0 ≤ a ^ 4 := pow_nonneg ha.le 4
  have hsub : S ⊆ box ⌈R / a⌉₊ :=
    fun x hx => mem_box_of_ne ha hg x (lt_of_lt_of_le one_pos (hS x hx)).ne'
  calc (S.card : ℝ) * a ^ 4 = ∑ x ∈ S, a ^ 4 * 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ x ∈ S, a ^ 4 * g (site a x) :=
        Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hS x hx) h4)
    _ ≤ ∑ x ∈ box ⌈R / a⌉₊, a ^ 4 * g (site a x) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => mul_nonneg h4 (hg0 _))

#print axioms card_mul_le_riemann

/-- The lattice sites `x` with `a x` in the cube: `⌊ℓ/a⌋` consecutive integers from `⌈t/a⌉` on each
axis.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def cubeSites (a t ℓ : ℝ) : Finset ISite :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Ico ⌈t / a⌉ (⌈t / a⌉ + (⌊ℓ / a⌋₊ : ℤ)))

/-- DERIVED: `4` is the number of axes. -/
theorem card_cubeSites (a t ℓ : ℝ) : (cubeSites a t ℓ).card = ⌊ℓ / a⌋₊ ^ 4 := by
  unfold cubeSites
  rw [Fintype.card_piFinset_const, Int.card_Ico]
  simp

#print axioms card_cubeSites

/-- Every site of `cubeSites a t ℓ` is mapped into the cube.

DERIVED: `0` is the sign of `a` and of `ℓ`; `1` is the indicator's value and the rounding slack of
`⌈·⌉` and of the strict upper end of `Finset.Ico`. -/
theorem cubeInd_site_of_mem {a t ℓ : ℝ} (ha : 0 < a) (hℓ : 0 ≤ ℓ) {x : ISite}
    (hx : x ∈ cubeSites a t ℓ) : cubeInd t ℓ (site a x) = 1 := by
  refine cubeInd_of_mem (mem_timeCube.mpr (fun i => ?_))
  have hi := Fintype.mem_piFinset.mp hx i
  rw [Finset.mem_Ico] at hi
  obtain ⟨h1, h2⟩ := hi
  have c1 : t / a ≤ ((⌈t / a⌉ : ℤ) : ℝ) := Int.le_ceil _
  have c2 : ((⌈t / a⌉ : ℤ) : ℝ) < t / a + 1 := Int.ceil_lt_add_one _
  have m1 : ((⌊ℓ / a⌋₊ : ℕ) : ℝ) ≤ ℓ / a := Nat.floor_le (div_nonneg hℓ ha.le)
  have h1' : ((⌈t / a⌉ : ℤ) : ℝ) ≤ ((x i : ℤ) : ℝ) := Int.cast_le.mpr h1
  have h2i : x i + 1 ≤ ⌈t / a⌉ + (⌊ℓ / a⌋₊ : ℤ) := by omega
  have h2' : ((x i : ℤ) : ℝ) + 1 ≤ ((⌈t / a⌉ : ℤ) : ℝ) + ((⌊ℓ / a⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast h2i
  have hlo : t / a ≤ ((x i : ℤ) : ℝ) := le_trans c1 h1'
  have hhi : ((x i : ℤ) : ℝ) ≤ (t + ℓ) / a := by
    rw [add_div]
    linarith
  constructor
  · have h := (div_le_iff₀ ha).mp hlo
    show t ≤ a * ((x i : ℤ) : ℝ)
    linarith
  · have h := (le_div_iff₀ ha).mp hhi
    show a * ((x i : ℤ) : ℝ) ≤ t + ℓ
    linarith

#print axioms cubeInd_site_of_mem

/-- The count of `cubeSites` times the cell volume is at least `(ℓ/2)⁴` once `a < ℓ/2`:
`a ⌊ℓ/a⌋ > ℓ − a > ℓ/2`.

DERIVED: `0` is the sign of `a`; `4` is the dimension; `1` is the rounding slack of `⌊·⌋`.
CHOSEN: `ℓ/2`, the half side; any fraction of `ℓ` below `1` serves once `a` is below the rest. -/
theorem cube_count_ge {a ℓ : ℝ} (ha : 0 < a) (haℓ : a < ℓ / 2) :
    (ℓ / 2) ^ 4 ≤ ((⌊ℓ / a⌋₊ ^ 4 : ℕ) : ℝ) * a ^ 4 := by
  have h1 := Nat.lt_floor_add_one (ℓ / a)
  have h2 : ℓ < ((⌊ℓ / a⌋₊ : ℝ) + 1) * a := (div_lt_iff₀ ha).mp h1
  have hm : ℓ / 2 ≤ a * (⌊ℓ / a⌋₊ : ℝ) := by linarith
  have hpos : 0 ≤ ℓ / 2 := by linarith
  calc (ℓ / 2) ^ 4 ≤ (a * (⌊ℓ / a⌋₊ : ℝ)) ^ 4 := pow_le_pow_left₀ hpos hm 4
    _ = ((⌊ℓ / a⌋₊ ^ 4 : ℕ) : ℝ) * a ^ 4 := by push_cast; ring

#print axioms cube_count_ge

/-- **The Riemann sum of the cube indicator is at least `(ℓ/2)⁴`** once `a < ℓ/2`.

DERIVED: `0` is the sign of `a` and `ℓ`; `4` is the dimension and the cell-volume exponent.
CHOSEN: `ℓ/2`, as in `cube_count_ge`. -/
theorem riemann_cube_ge {a t ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (haℓ : a < ℓ / 2) :
    (ℓ / 2) ^ 4 ≤ ∑ x ∈ box ⌈(|t| + |ℓ|) / a⌉₊, a ^ 4 * (cubeTest t ℓ).1 (site a x) := by
  have h := card_mul_le_riemann ha (isTest_cubeTest t ℓ) (fun y => cubeInd_nonneg t ℓ y)
    (cubeSites a t ℓ) (fun x hx => (cubeInd_site_of_mem ha hℓ.le hx).symm.le)
  rw [card_cubeSites] at h
  exact le_trans (cube_count_ge ha haℓ) h

#print axioms riemann_cube_ge

/-- The reflected cube indicator is `1` at the reflected sites of `cubeSites`.

DERIVED: `0` is the sign of `a` and `ℓ` and the reflection constant; `1` is the indicator's value;
`4` in `Fin 4` is the spacetime dimension. -/
theorem one_le_refl_cube (τ : Fin 4) {a t ℓ : ℝ} (ha : 0 < a) (hℓ : 0 ≤ ℓ) {x₀ : ISite}
    (hx₀ : x₀ ∈ cubeSites a t ℓ) :
    1 ≤ ((cubeTest t ℓ).reflect τ).1 (site a (LatticeReflection.ireflSite τ 0 x₀)) := by
  show 1 ≤ cubeInd t ℓ (reflR τ (site a (LatticeReflection.ireflSite τ 0 x₀)))
  rw [site_ireflSite, reflR_reflR]
  exact (cubeInd_site_of_mem ha hℓ hx₀).symm.le

#print axioms one_le_refl_cube

/-- **The Riemann sum of the reflected cube indicator is at least `(ℓ/2)⁴`** once `a < ℓ/2`: the
reflection permutes the sites (`reflSitePerm`), so the reflected sub-box has the same count.

DERIVED: `0` is the sign of `a` and `ℓ`; `4` is the dimension and the cell-volume exponent, and
`4` in `Fin 4`. CHOSEN: `ℓ/2`, as in `cube_count_ge`. -/
theorem riemann_refl_cube_ge (τ : Fin 4) {a t ℓ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (haℓ : a < ℓ / 2) :
    (ℓ / 2) ^ 4
      ≤ ∑ x ∈ box ⌈(|t| + |ℓ|) / a⌉₊, a ^ 4 * ((cubeTest t ℓ).reflect τ).1 (site a x) := by
  have h := card_mul_le_riemann ha (isTest_reflect τ (isTest_cubeTest t ℓ))
    (fun y => cubeInd_nonneg t ℓ (reflR τ y))
    ((cubeSites a t ℓ).map (reflSitePerm τ).toEmbedding)
    (fun x hx => by
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_map.mp hx
      exact one_le_refl_cube τ ha hℓ.le hx₀)
  rw [Finset.card_map, card_cubeSites] at h
  exact le_trans (cube_count_ge ha haℓ) h

#print axioms riemann_refl_cube_ge

end Riemann

/-! ## 8. The physical region and the open input -/

section Region

/-- The pairs `(p, q)` with `θp` in the cube and `q` in the cube: `p` ranges over the reflected cube
(the support of `θf`), `q` over the cube.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def pairRegion (τ : Fin 4) (t ℓ : ℝ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {pq | reflR τ pq.1 ∈ timeCube t ℓ ∧ pq.2 ∈ timeCube t ℓ}

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem mem_pairRegion {τ : Fin 4} {t ℓ : ℝ} {p q : Fin 4 → ℝ} :
    (p, q) ∈ pairRegion τ t ℓ ↔ reflR τ p ∈ timeCube t ℓ ∧ q ∈ timeCube t ℓ := Iff.rfl

#print axioms mem_pairRegion

/-- The pairs at sup-distance at least `d` (some coordinate differs by at least `d`, as in
`ContinuumSep.sepBy`) with both points in `[-R, R]⁴`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def sepBoxSet (d R : ℝ) : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ)) :=
  {pq | (∃ i, d ≤ |pq.1 i - pq.2 i|) ∧ ∀ i, |pq.1 i| ≤ R ∧ |pq.2 i| ≤ R}

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem mem_sepBoxSet {d R : ℝ} {p q : Fin 4 → ℝ} :
    (p, q) ∈ sepBoxSet d R ↔ (∃ i, d ≤ |p i - q i|) ∧ ∀ i, |p i| ≤ R ∧ |q i| ≤ R := Iff.rfl

#print axioms mem_sepBoxSet

/-- On the region the time coordinates differ by at least `2t`: `p_τ ≤ −t` and `q_τ ≥ t`.

DERIVED: `2` is the two margins `t`, one on each side of the plane; `4` in `Fin 4` is the spacetime
dimension. -/
theorem two_mul_le_abs_sub {τ : Fin 4} {t ℓ : ℝ} {p q : Fin 4 → ℝ}
    (h : (p, q) ∈ pairRegion τ t ℓ) : 2 * t ≤ |p τ - q τ| := by
  obtain ⟨h1, h2⟩ := mem_pairRegion.mp h
  have a1 := (mem_timeCube.mp h1 τ).1
  have a2 := (mem_timeCube.mp h2 τ).1
  have e : reflR τ p τ = -p τ := by simp only [reflR, Function.update_self]
  rw [e] at a1
  rw [abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

#print axioms two_mul_le_abs_sub

/-- **The region is separated and bounded**: `pairRegion τ t ℓ ⊆ sepBoxSet (2t) (|t| + |ℓ|)`.

DERIVED: `2` as in `two_mul_le_abs_sub`; `4` in `Fin 4` is the spacetime dimension. -/
theorem pairRegion_subset {τ : Fin 4} {t ℓ : ℝ} {p q : Fin 4 → ℝ}
    (h : (p, q) ∈ pairRegion τ t ℓ) : (p, q) ∈ sepBoxSet (2 * t) (|t| + |ℓ|) :=
  mem_sepBoxSet.mpr ⟨⟨τ, two_mul_le_abs_sub h⟩, fun i =>
    ⟨by
      rw [← abs_reflR τ p i]
      exact abs_le_of_mem_timeCube (mem_pairRegion.mp h).1 i,
     abs_le_of_mem_timeCube (mem_pairRegion.mp h).2 i⟩⟩

#print axioms pairRegion_subset

/-- **Uniform convergence of the lattice kernel on a set of physical pairs (stated, not proved).**
For every `ε > 0`, eventually in the step, `|latKernel k x y − G₂(a x, a y)| ≤ ε` for every pair of
sites whose physical points `(a x, a y)`, `a = dySpacing N k`, lie in `A`.

DERIVED: `0` is the excluded colour count and the sign of `ε`; `4` in `Fin 4` is the spacetime
dimension. -/
def KernelLimitOn (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) (A : Set ((Fin 4 → ℝ) × (Fin 4 → ℝ))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x y : ISite,
    (site (dySpacing N k) x, site (dySpacing N k) y) ∈ A →
      |latKernel hN ρ τ O k x y - G₂ (site (dySpacing N k) x) (site (dySpacing N k) y)| ≤ ε

/-- **The open input: the lattice kernel converges on separated bounded pairs (stated, not
proved).** For every separation `d > 0` and radius `R`, `latKernel → G₂` uniformly on
`sepBoxSet d R`. Coincident points are outside every such set.

DERIVED: `0` is the excluded colour count and the sign of `d`; `4` in `Fin 4` is the spacetime
dimension. -/
def KernelConvergesSep (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ d R : ℝ, 0 < d → KernelLimitOn hN ρ τ O G₂ (sepBoxSet d R)

end Region

/-! ## 9. The connected two-point function of the cube monomial is positive -/

section Positive

/-- **Eventual two-sided bounds on the lattice sequence.** Under `KernelConvergesSep` and
`g₀ ≤ G₂ ≤ g₁` on `pairRegion τ t ℓ` with `g₀ > 0`, eventually in the step
`(g₀/2)(ℓ/2)⁴(ℓ/2)⁴ ≤ latSkR(θQ ∪ Q) ≤ (|g₁| + g₀)((2R + 3)⁴)²`, `R = |t| + |ℓ|`,
`Q = mono1 (O, cubeTest t ℓ)`.

DERIVED: `0` is the excluded colour count and the signs; `4` in `Fin 4` is the spacetime dimension
and the exponent of each Riemann-sum bound; `2` in `2t` is `two_mul_le_abs_sub`'s; `1`, `2`, `3` in
`1 * (2R + 3)⁴` are `riemann_le`'s at the indicator's bound `1`. CHOSEN: `g₀/2`, the distance from
`G₂` allowed to the kernel, and `ℓ/2`, as in `cube_count_ge`. -/
theorem eventually_bounds (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (O : LField (MassGap.SUN.SU N))
    (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ)
    (hconv : KernelConvergesSep hN (Renorm.connected hN Z) τ O G₂) {t ℓ g₀ g₁ : ℝ}
    (ht : 0 < t) (hℓ : 0 < ℓ) (hg₀ : 0 < g₀)
    (hG : ∀ p q, (p, q) ∈ pairRegion τ t ℓ → g₀ ≤ G₂ p q ∧ G₂ p q ≤ g₁) :
    ∀ᶠ k in atTop,
      g₀ / 2 * ((ℓ / 2) ^ 4 * (ℓ / 2) ^ 4)
          ≤ latSkR hN (Renorm.connected hN Z) k
              (pairFam τ (mono1 (O, cubeTest t ℓ)) (mono1 (O, cubeTest t ℓ)))
        ∧ latSkR hN (Renorm.connected hN Z) k
              (pairFam τ (mono1 (O, cubeTest t ℓ)) (mono1 (O, cubeTest t ℓ)))
          ≤ (|g₁| + g₀) * ((1 * (2 * (|t| + |ℓ|) + 3) ^ 4) * (1 * (2 * (|t| + |ℓ|) + 3) ^ 4)) := by
  filter_upwards [hconv (2 * t) (|t| + |ℓ|) (by linarith) (g₀ / 2) (half_pos hg₀),
    (tendsto_dySpacing N).eventually (gt_mem_nhds (lt_min one_pos (half_pos hℓ)))] with k hk hks
  have ha : 0 < dySpacing N k := dySpacing_pos (one_le_of_ne_zero hN) k
  have ha1 : dySpacing N k ≤ 1 := (lt_of_lt_of_le hks (min_le_left _ _)).le
  have haℓ : dySpacing N k < ℓ / 2 := lt_of_lt_of_le hks (min_le_right _ _)
  rw [latSkR_mono1_pair hN (Renorm.connected hN Z) τ (Renorm.connected_reflCompat hN Z τ hZ) k O
    (cubeTest t ℓ) (isTest_cubeTest t ℓ)]
  have hKb : ∀ x ∈ box ⌈(|t| + |ℓ|) / dySpacing N k⌉₊, ∀ y ∈ box ⌈(|t| + |ℓ|) / dySpacing N k⌉₊,
      dySpacing N k ^ 4 * ((cubeTest t ℓ).reflect τ).1 (site (dySpacing N k) x) ≠ 0 →
      dySpacing N k ^ 4 * (cubeTest t ℓ).1 (site (dySpacing N k) y) ≠ 0 →
      g₀ / 2 ≤ latKernel hN (Renorm.connected hN Z) τ O k x y
        ∧ latKernel hN (Renorm.connected hN Z) τ O k x y ≤ |g₁| + g₀ := by
    intro x _ y _ hx hy
    have hx' : reflR τ (site (dySpacing N k) x) ∈ timeCube t ℓ :=
      mem_timeCube_of_cubeInd_ne (t := t) (ℓ := ℓ) (y := reflR τ (site (dySpacing N k) x))
        (right_ne_zero_of_mul hx)
    have hy' : site (dySpacing N k) y ∈ timeCube t ℓ :=
      mem_timeCube_of_cubeInd_ne (t := t) (ℓ := ℓ) (y := site (dySpacing N k) y)
        (right_ne_zero_of_mul hy)
    have hreg : (site (dySpacing N k) x, site (dySpacing N k) y) ∈ pairRegion τ t ℓ :=
      mem_pairRegion.mpr ⟨hx', hy'⟩
    have hclose := hk x y (pairRegion_subset hreg)
    obtain ⟨hG1, hG2⟩ := hG _ _ hreg
    obtain ⟨hc1, hc2⟩ := abs_le.mp hclose
    have hg1 : g₁ ≤ |g₁| := le_abs_self g₁
    constructor <;> linarith
  have hu : ∀ x ∈ box ⌈(|t| + |ℓ|) / dySpacing N k⌉₊,
      0 ≤ dySpacing N k ^ 4 * ((cubeTest t ℓ).reflect τ).1 (site (dySpacing N k) x) :=
    fun x _ => mul_nonneg (pow_nonneg ha.le 4) (cubeInd_nonneg t ℓ (reflR τ (site (dySpacing N k) x)))
  have hv : ∀ y ∈ box ⌈(|t| + |ℓ|) / dySpacing N k⌉₊,
      0 ≤ dySpacing N k ^ 4 * (cubeTest t ℓ).1 (site (dySpacing N k) y) :=
    fun y _ => mul_nonneg (pow_nonneg ha.le 4) (cubeInd_nonneg t ℓ (site (dySpacing N k) y))
  have hU1 := riemann_refl_cube_ge τ (t := t) ha hℓ haℓ
  have hV1 := riemann_cube_ge (t := t) ha hℓ haℓ
  have hU2 := riemann_le ha ha1 (isTest_reflect τ (isTest_cubeTest t ℓ))
  have hV2 := riemann_le ha ha1 (isTest_cubeTest t ℓ)
  have hUnn := Finset.sum_nonneg hu
  have hVnn := Finset.sum_nonneg hv
  have hlow := double_sum_lower (box ⌈(|t| + |ℓ|) / dySpacing N k⌉₊)
    (fun x => dySpacing N k ^ 4 * ((cubeTest t ℓ).reflect τ).1 (site (dySpacing N k) x))
    (fun y => dySpacing N k ^ 4 * (cubeTest t ℓ).1 (site (dySpacing N k) y))
    (latKernel hN (Renorm.connected hN Z) τ O k) hu hv
    (fun x hx y hy h1 h2 => (hKb x hx y hy h1 h2).1)
  have hup := double_sum_upper (box ⌈(|t| + |ℓ|) / dySpacing N k⌉₊)
    (fun x => dySpacing N k ^ 4 * ((cubeTest t ℓ).reflect τ).1 (site (dySpacing N k) x))
    (fun y => dySpacing N k ^ 4 * (cubeTest t ℓ).1 (site (dySpacing N k) y))
    (latKernel hN (Renorm.connected hN Z) τ O k) hu hv
    (fun x hx y hy h1 h2 => (hKb x hx y hy h1 h2).2)
  have hB0 : 0 ≤ 1 * (2 * (|t| + |ℓ|) + 3) ^ 4 := by positivity
  exact ⟨le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hU1 hV1 (pow_nonneg (half_pos hℓ).le 4) hUnn) (half_pos hg₀).le) hlow,
    le_trans hup (mul_le_mul_of_nonneg_left (mul_le_mul hU2 hV2 hVnn hB0)
      (add_nonneg (abs_nonneg g₁) hg₀.le))⟩

#print axioms eventually_bounds

/-- **The reflected two-point function of the cube monomial is bounded below**: under
`KernelConvergesSep` and `g₀ ≤ G₂ ≤ g₁` on `pairRegion τ t ℓ` with `g₀ > 0`,
`(g₀/2)(ℓ/2)⁴(ℓ/2)⁴ ≤ S(θQ ∪ Q)`. The lattice sequence is eventually bounded, so it converges along
`ultra` to `kern` (no `UniformBoundSep` is used), and the eventual lower bound passes to the limit.

DERIVED: `0` is the excluded colour count and the signs; `4` in `Fin 4` is the spacetime dimension
and the exponent of each Riemann-sum bound. CHOSEN: `g₀/2` and `ℓ/2`, as in `eventually_bounds`. -/
theorem kern_mono1_ge (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (O : LField (MassGap.SUN.SU N))
    (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ)
    (hconv : KernelConvergesSep hN (Renorm.connected hN Z) τ O G₂) {t ℓ g₀ g₁ : ℝ}
    (ht : 0 < t) (hℓ : 0 < ℓ) (hg₀ : 0 < g₀)
    (hG : ∀ p q, (p, q) ∈ pairRegion τ t ℓ → g₀ ≤ G₂ p q ∧ G₂ p q ≤ g₁) :
    g₀ / 2 * ((ℓ / 2) ^ 4 * (ℓ / 2) ^ 4)
      ≤ kern hN (Renorm.connected hN Z) τ (mono1 (O, cubeTest t ℓ)) (mono1 (O, cubeTest t ℓ)) := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hev := eventually_bounds hN Z τ hZ O G₂ hconv ht hℓ hg₀ hG
  have hL0 : 0 ≤ g₀ / 2 * ((ℓ / 2) ^ 4 * (ℓ / 2) ^ 4) :=
    mul_nonneg (half_pos hg₀).le (mul_nonneg (pow_nonneg (half_pos hℓ).le 4)
      (pow_nonneg (half_pos hℓ).le 4))
  have hC0 : 0 ≤ (|g₁| + g₀) * ((1 * (2 * (|t| + |ℓ|) + 3) ^ 4) * (1 * (2 * (|t| + |ℓ|) + 3) ^ 4)) :=
    mul_nonneg (add_nonneg (abs_nonneg g₁) hg₀.le) (by positivity)
  have hbdd : ∀ᶠ k in atTop,
      |latSkR hN (Renorm.connected hN Z) k
          (pairFam τ (mono1 (O, cubeTest t ℓ)) (mono1 (O, cubeTest t ℓ)))|
        ≤ (|g₁| + g₀) * ((1 * (2 * (|t| + |ℓ|) + 3) ^ 4) * (1 * (2 * (|t| + |ℓ|) + 3) ^ 4)) := by
    filter_upwards [hev] with k hk
    exact abs_le.mpr ⟨(neg_nonpos.mpr hC0).trans (hL0.trans hk.1), hk.2⟩
  obtain ⟨L, hL⟩ := exists_tendsto_ultra _ _ hbdd
  have htend : Tendsto
      (fun k => latSkR hN (Renorm.connected hN Z) k
        (pairFam τ (mono1 (O, cubeTest t ℓ)) (mono1 (O, cubeTest t ℓ))))
      (ultra : Filter ℕ)
      (𝓝 (kern hN (Renorm.connected hN Z) τ (mono1 (O, cubeTest t ℓ)) (mono1 (O, cubeTest t ℓ)))) :=
    tendsto_nhds_limUnder ⟨L, hL⟩
  exact ge_of_tendsto htend ((hev.mono (fun k hk => hk.1)).filter_mono ultra_le)

#print axioms kern_mono1_ge

/-- **`ConnectedTwoPointNonzero` from the kernel limit.** At `N ≠ 0`, for reflection-compatible `Z`,
a local gauge-invariant field `O` and a limit `G₂` with `KernelConvergesSep`, if `g₀ ≤ G₂ ≤ g₁` on
`pairRegion τ t ℓ` for some `t, ℓ, g₀ > 0`, then `ConnectedTwoPointNonzero` holds for
`Renorm.connected hN Z`, witnessed by the cube monomial `Q = mono1 (O, cubeTest t ℓ)` at margin `t`
(`sepCube`): `S(θQ ∪ Q) > 0` (`kern_mono1_ge`) and `S(Q) = 0` (`kern_empty_mono1`).

DERIVED: `0` is the excluded colour count and the signs; `4` in `Fin 4` is the spacetime dimension. -/
theorem connectedTwoPointNonzero_of_kernel (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (O : LField (MassGap.SUN.SU N))
    (G₂ : (Fin 4 → ℝ) → (Fin 4 → ℝ) → ℝ)
    (hconv : KernelConvergesSep hN (Renorm.connected hN Z) τ O G₂) {t ℓ g₀ g₁ : ℝ}
    (ht : 0 < t) (hℓ : 0 < ℓ) (hg₀ : 0 < g₀)
    (hG : ∀ p q, (p, q) ∈ pairRegion τ t ℓ → g₀ ≤ G₂ p q ∧ G₂ p q ≤ g₁) :
    ContinuumSep.ConnectedTwoPointNonzero hN (Renorm.connected hN Z) τ := by
  have hpos := kern_mono1_ge hN Z τ hZ O G₂ hconv ht hℓ hg₀ hG
  have hL : 0 < g₀ / 2 * ((ℓ / 2) ^ 4 * (ℓ / 2) ^ 4) :=
    mul_pos (half_pos hg₀) (mul_pos (pow_pos (half_pos hℓ) 4) (pow_pos (half_pos hℓ) 4))
  refine ⟨sepCube τ O ht ℓ, ?_⟩
  show kern hN (Renorm.connected hN Z) τ (mono1 (O, cubeTest t ℓ)) (mono1 (O, cubeTest t ℓ))
      - kern hN (Renorm.connected hN Z) τ (emptyMono N) (mono1 (O, cubeTest t ℓ)) ^ 2 ≠ 0
  rw [kern_empty_mono1 hN Z τ hZ O (cubeTest t ℓ), zero_pow two_ne_zero, sub_zero]
  exact (lt_of_lt_of_le hL hpos).ne'

#print axioms connectedTwoPointNonzero_of_kernel

end Positive

/-! ## 10. Requirement Y supplies the bounds -/

section AF

/-- The Euclidean distance on `ℝ⁴`.

DERIVED: `2` is the square in the Euclidean norm; `4` in `Fin 4` is the spacetime dimension. -/
def eDist (p q : Fin 4 → ℝ) : ℝ := Real.sqrt (∑ i, (p i - q i) ^ 2)

/-- On the region the Euclidean distance is at least `2t`.

DERIVED: `2` as in `two_mul_le_abs_sub`; `4` in `Fin 4` is the spacetime dimension. -/
theorem eDist_ge {τ : Fin 4} {t ℓ : ℝ} {p q : Fin 4 → ℝ} (h : (p, q) ∈ pairRegion τ t ℓ) :
    2 * t ≤ eDist p q := by
  have h1 : (p τ - q τ) ^ 2 ≤ ∑ i, (p i - q i) ^ 2 :=
    Finset.single_le_sum (f := fun i => (p i - q i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ τ)
  calc 2 * t ≤ |p τ - q τ| := two_mul_le_abs_sub h
    _ = Real.sqrt ((p τ - q τ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ eDist p q := Real.sqrt_le_sqrt h1

#print axioms eDist_ge

/-- On the region the Euclidean distance is at most `4(|t| + |ℓ|)`: each coordinate difference is at
most `2(|t| + |ℓ|)`, and there are four coordinates.

DERIVED: `4 = 2·2`, the factor `2` of each coordinate difference and `√4 = 2` from the four
coordinates; `4` in `Fin 4` is the spacetime dimension. -/
theorem eDist_le {τ : Fin 4} {t ℓ : ℝ} {p q : Fin 4 → ℝ} (h : (p, q) ∈ pairRegion τ t ℓ) :
    eDist p q ≤ 4 * (|t| + |ℓ|) := by
  obtain ⟨h1, h2⟩ := mem_pairRegion.mp h
  have hb : ∀ i, (p i - q i) ^ 2 ≤ (2 * (|t| + |ℓ|)) ^ 2 := by
    intro i
    have hp : |p i| ≤ |t| + |ℓ| := by
      rw [← abs_reflR τ p i]
      exact abs_le_of_mem_timeCube h1 i
    have hq : |q i| ≤ |t| + |ℓ| := abs_le_of_mem_timeCube h2 i
    obtain ⟨hp1, hp2⟩ := abs_le.mp hp
    obtain ⟨hq1, hq2⟩ := abs_le.mp hq
    exact sq_le_sq' (by linarith) (by linarith)
  have hsum : ∑ i, (p i - q i) ^ 2 ≤ ∑ _i : Fin 4, (2 * (|t| + |ℓ|)) ^ 2 :=
    Finset.sum_le_sum (fun i _ => hb i)
  have hc : ∑ _i : Fin 4, (2 * (|t| + |ℓ|)) ^ 2 = (4 * (|t| + |ℓ|)) ^ 2 := by
    rw [Fin.sum_univ_four]
    ring
  have hnn : 0 ≤ 4 * (|t| + |ℓ|) := by positivity
  calc eDist p q ≤ Real.sqrt ((4 * (|t| + |ℓ|)) ^ 2) := Real.sqrt_le_sqrt (hsum.trans hc.le)
    _ = 4 * (|t| + |ℓ|) := Real.sqrt_sq hnn

#print axioms eDist_le

/-- **Requirement Y bounds `G` on every short interval.** From `ShortDistanceY.AFShortDistance G`
there is `0 < δ ≤ 1` such that for all `0 < r₁ ≤ r₂ < δ` there are `g₀ > 0` and `g₁` with
`g₀ ≤ G r ≤ g₁` on `[r₁, r₂]`: there `r⁸ G(r) (log r)²` lies within `C/2` of `C > 0`, and `r⁸`,
`(log r)²` are bounded above and below by positive constants on `[r₁, r₂] ⊂ (0, 1)`.

DERIVED: `8` and the square on the logarithm are `AFShortDistance`'s; `0` is the point approached
and the signs; `1` is where `log` vanishes. CHOSEN: `C/2`, the neighbourhood of `C` used, whence the
bounds `C/2` and `3C/2`; any fraction of `C` below `1` serves. -/
theorem af_bounds_on_interval {G : ℝ → ℝ} (hY : ShortDistanceY.AFShortDistance G) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ ≤ r₂ → r₂ < δ →
      ∃ g₀ g₁ : ℝ, 0 < g₀ ∧ ∀ r : ℝ, r₁ ≤ r → r ≤ r₂ → g₀ ≤ G r ∧ G r ≤ g₁ := by
  obtain ⟨C, hC, hlim⟩ := hY
  obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim (C / 2) (half_pos hC)
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun r₁ r₂ hr₁ h12 hr₂ => ?_⟩
  have hr₂δ : r₂ < δ := lt_of_lt_of_le hr₂ (min_le_left _ _)
  have hr₂1 : r₂ < 1 := lt_of_lt_of_le hr₂ (min_le_right _ _)
  have hr₂0 : 0 < r₂ := lt_of_lt_of_le hr₁ h12
  have hl₁ : Real.log r₁ < 0 := Real.log_neg hr₁ (lt_of_le_of_lt h12 hr₂1)
  have hl₂ : Real.log r₂ < 0 := Real.log_neg hr₂0 hr₂1
  have hL₁ : 0 < Real.log r₁ ^ 2 := by
    nlinarith [mul_pos (neg_pos.mpr hl₁) (neg_pos.mpr hl₁)]
  have hL₂ : 0 < Real.log r₂ ^ 2 := by
    nlinarith [mul_pos (neg_pos.mpr hl₂) (neg_pos.mpr hl₂)]
  have hD₀ : 0 < r₂ ^ 8 * Real.log r₁ ^ 2 := mul_pos (pow_pos hr₂0 8) hL₁
  have hD₁ : 0 < r₁ ^ 8 * Real.log r₂ ^ 2 := mul_pos (pow_pos hr₁ 8) hL₂
  refine ⟨C / 2 / (r₂ ^ 8 * Real.log r₁ ^ 2), 3 * C / 2 / (r₁ ^ 8 * Real.log r₂ ^ 2),
    div_pos (half_pos hC) hD₀, fun r hr1 hr2 => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le hr₁ hr1
  have hrδ : r < δ := by linarith
  have hr1' : r < 1 := by linarith
  have hF : dist (r ^ 8 * G r * Real.log r ^ 2) C < C / 2 :=
    hball (show r ∈ Set.Ioi (0 : ℝ) from hr0)
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hr0]; exact hrδ)
  rw [Real.dist_eq] at hF
  obtain ⟨hF1, hF2⟩ := abs_lt.mp hF
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1'
  have hlr1 : Real.log r₁ ≤ Real.log r := Real.log_le_log hr₁ hr1
  have hlr2 : Real.log r ≤ Real.log r₂ := Real.log_le_log hr0 hr2
  have hsqA : Real.log r ^ 2 ≤ Real.log r₁ ^ 2 := by
    have h := sq_le_sq' (a := Real.log r) (b := -Real.log r₁) (by linarith) (by linarith)
    rwa [neg_sq] at h
  have hsqB : Real.log r₂ ^ 2 ≤ Real.log r ^ 2 := by
    have h := sq_le_sq' (a := Real.log r₂) (b := -Real.log r) (by linarith) (by linarith)
    rwa [neg_sq] at h
  have hDle : r ^ 8 * Real.log r ^ 2 ≤ r₂ ^ 8 * Real.log r₁ ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ hr0.le hr2 8) hsqA (sq_nonneg _) (pow_nonneg hr₂0.le 8)
  have hDge : r₁ ^ 8 * Real.log r₂ ^ 2 ≤ r ^ 8 * Real.log r ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ hr₁.le hr1 8) hsqB (sq_nonneg _) (pow_nonneg hr0.le 8)
  have hFeq : r ^ 8 * G r * Real.log r ^ 2 = G r * (r ^ 8 * Real.log r ^ 2) := by ring
  rw [hFeq] at hF1 hF2
  have hD : 0 < r ^ 8 * Real.log r ^ 2 := lt_of_lt_of_le hD₁ hDge
  have hGpos : 0 < G r := by
    by_contra hneg
    push_neg at hneg
    have h0 := mul_le_mul_of_nonneg_right hneg hD.le
    linarith
  constructor
  · rw [div_le_iff₀ hD₀]
    have h := mul_le_mul_of_nonneg_left hDle hGpos.le
    linarith
  · rw [le_div_iff₀ hD₁]
    have h := mul_le_mul_of_nonneg_left hDge hGpos.le
    linarith

#print axioms af_bounds_on_interval

/-- **`ConnectedTwoPointNonzero` from a radial kernel limit bounded on an interval.** If the lattice
kernel converges on separated pairs to `G(|p − q|)` and `g₀ ≤ G ≤ g₁` on `[2t, 4(|t| + |ℓ|)]` with
`t, ℓ, g₀ > 0`, then `ConnectedTwoPointNonzero` holds for `Renorm.connected hN Z`.

DERIVED: `2` and `4` in the interval are `eDist_ge`'s and `eDist_le`'s; `0` is the excluded colour
count and the signs; `4` in `Fin 4` is the spacetime dimension. -/
theorem connectedTwoPointNonzero_of_radial (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (O : LField (MassGap.SUN.SU N))
    (G : ℝ → ℝ)
    (hconv : KernelConvergesSep hN (Renorm.connected hN Z) τ O (fun p q => G (eDist p q)))
    {t ℓ g₀ g₁ : ℝ} (ht : 0 < t) (hℓ : 0 < ℓ) (hg₀ : 0 < g₀)
    (hG : ∀ r, 2 * t ≤ r → r ≤ 4 * (|t| + |ℓ|) → g₀ ≤ G r ∧ G r ≤ g₁) :
    ContinuumSep.ConnectedTwoPointNonzero hN (Renorm.connected hN Z) τ :=
  connectedTwoPointNonzero_of_kernel hN Z τ hZ O _ hconv ht hℓ hg₀
    (fun _ _ h => hG _ (eDist_ge h) (eDist_le h))

#print axioms connectedTwoPointNonzero_of_radial

/-- **Headline: `ConnectedTwoPointNonzero` from the kernel limit and requirement Y.** At `N ≠ 0`,
for reflection-compatible `Z` and a local gauge-invariant field `O`: if the lattice kernel of the
connected composites converges on separated bounded pairs to `G(|p − q|)`
(`KernelConvergesSep`, the open input) and `G` satisfies `ShortDistanceY.AFShortDistance`, then
`ContinuumSep.ConnectedTwoPointNonzero hN (Renorm.connected hN Z) τ`. The witness is the cube
monomial `mono1 (O, cubeTest (δ/16) (δ/16))`, `δ` from `af_bounds_on_interval`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The proof's
`16` is CHOSEN: at `t = ℓ = δ/16` the separations lie in `[δ/8, δ/2] ⊂ (0, δ)`; any divisor above
`8` serves. -/
theorem connectedTwoPointNonzero_of_af (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O) (O : LField (MassGap.SUN.SU N))
    (G : ℝ → ℝ)
    (hconv : KernelConvergesSep hN (Renorm.connected hN Z) τ O (fun p q => G (eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ContinuumSep.ConnectedTwoPointNonzero hN (Renorm.connected hN Z) τ := by
  obtain ⟨δ, hδ, -, hbd⟩ := af_bounds_on_interval hY
  have hs : 0 < δ / 16 := by linarith
  have habs : |δ / 16| = δ / 16 := abs_of_pos hs
  obtain ⟨g₀, g₁, hg₀, hG⟩ := hbd (2 * (δ / 16)) (4 * (|δ / 16| + |δ / 16|)) (by linarith)
    (by rw [habs]; linarith) (by rw [habs]; linarith)
  exact connectedTwoPointNonzero_of_radial hN Z τ hZ O G hconv hs hs hg₀ hG

#print axioms connectedTwoPointNonzero_of_af

/-- **Headline at the explicit renormalisation `rhoA`** (`Z_k = a⁻⁴`, connected subtraction), where
the kernel is the lattice connected two-point function over `a⁸` (`latKernel_rhoA`).

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem connectedTwoPointNonzero_rhoA (hN : N ≠ 0) (τ : Fin 4) (O : LField (MassGap.SUN.SU N))
    (G : ℝ → ℝ) (hconv : KernelConvergesSep hN (rhoA hN) τ O (fun p q => G (eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ContinuumSep.ConnectedTwoPointNonzero hN (rhoA hN) τ :=
  connectedTwoPointNonzero_of_af hN (fun j _ => (dySpacing N j ^ 4)⁻¹) τ (fun _ _ => rfl) O G
    hconv hY

#print axioms connectedTwoPointNonzero_rhoA

/-- **The reconstructed space is not spanned by the vacuum.** Under `UniformBoundSep`, the kernel
limit `KernelConvergesSep` towards `G(|p − q|)` and `ShortDistanceY.AFShortDistance G`, at every dyadic
step `m` the Hilbert space of `ContinuumSep.continuum_reconstruction_sep` for
`Renorm.connected hN Z` has a non-zero vector orthogonal to the vacuum and not a complex multiple of
it.

DERIVED: `0` is the excluded colour count, the vanishing vacuum pairing and the zero vector; `4` in
`Fin 4` is the spacetime dimension. -/
theorem exists_orth_ne_zero_of_af (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) (m : ℕ)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : KernelConvergesSep hN (Renorm.connected hN Z) τ O (fun p q => G (eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ∃ u : GNSHilbert.H (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB
        (Renorm.connected_reflCompat hN Z τ hZ) m).toReflForm,
      inner ℂ (GNSHilbert.Omega (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB
          (Renorm.connected_reflCompat hN Z τ hZ) m).toReflForm
        (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB
          (Renorm.connected_reflCompat hN Z τ hZ) m).vac) u = (0 : ℂ) ∧ u ≠ 0
      ∧ ∀ a : ℂ, u ≠ a • GNSHilbert.Omega (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ
          hB (Renorm.connected_reflCompat hN Z τ hZ) m).toReflForm
        (ContinuumSep.contTransferSep hN (Renorm.connected hN Z) τ hB
          (Renorm.connected_reflCompat hN Z τ hZ) m).vac :=
  ContinuumSep.exists_orth_ne_zero_sep hN (Renorm.connected hN Z) τ hB
    (Renorm.connected_reflCompat hN Z τ hZ) m (connectedTwoPointNonzero_of_af hN Z τ hZ O G hconv hY)

#print axioms exists_orth_ne_zero_of_af

end AF

end MassGap.ContinuumNontrivial
