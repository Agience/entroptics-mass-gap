import Mathlib
import MassGap.ObserverOSSchwartz
import MassGap.WightmanTestFn

noncomputable section

/-!
# MassGap.ObserverOSTempered — the observer's Schwinger functions as continuous multilinear functionals on Schwartz space

`ObserverOSSchwartz.schwSF` extends the Schwinger functions of the energy density `energy0` from test
functions to decaying functions, as the limit of cube truncations, with the growth bound
`|S_n(g)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 ‖gᵢ‖₅`. Here they are made into a continuous
multilinear functional on `WightmanData.TestFn = 𝓢(E4, ℝ)`, the Schwartz class of the tree's
Wightman structure, `E4 = EuclideanSpace ℝ (Fin 4)`.

## Multilinearity

`contSF_update_add_test`, `contSF_update_smul_test`: for a family `(O, fᵢ)` of one field, the limit
Schwinger function is additive and homogeneous in each test function, given the cube moments of `O`
alone. At each step `latSF` is linear in each slot (`ObserverOS.latSF_update`, `smear_testAdd`,
`smear_testSmul`), and every family of test functions converges along the ultrafilter
(`tendsto_latSF_test`: a test function supported in `[-R, R]⁴` with `|f| ≤ M` has
`‖f‖₅ ≤ (1 + R)⁵ M`, `decayBound_of_isTest`). `ObserverOS.contSF_update_add` needs
`UniformBoundF` on the whole class; this route needs only the one field.

`decAdd`, `decSmul` are the vector operations on `Decaying`; truncation commutes with them
(`trunc_decAdd`, `trunc_decSmul`), and `schwSF_update_add`, `schwSF_update_smul` follow by passing to
the limit in `R`.

## Euclidean Schwartz functions

`ofE4 φ = φ ∘ toLp`, `toLp : (Fin 4 → ℝ) → E4` the coordinate identification. Since
`‖y‖_∞ ≤ ‖toLp y‖₂` (`norm_le_norm_toLp`), Mathlib's `one_add_le_sup_seminorm_apply` gives
`‖ofE4 φ‖_K ≤ e4Norm K φ = 2^K ∑_{(k,l) ≤ (K,0)} p_{k,l}(φ)` (`decayBound_e4`), `p_{k,l}` the
Schwartz seminorms of `𝓢(E4, ℝ)`. `e4Norm K` is continuous on `𝓢(E4, ℝ)` (`continuous_e4Norm`,
`schwartz_withSeminorms`).

## Continuity

`continuous_of_bound_by`: a real multilinear map on a topological additive group bounded by
`K ∏ᵢ q(mᵢ)`, `q ≥ 0` continuous with `q 0 = 0`, is continuous (the telescoping bound of Mathlib's
`MultilinearMap.norm_image_sub_le_of_bound'` with `q` in place of the norm). With `q = e4Norm 5` this
makes `schwCML n : ContinuousMultilinearMap ℝ (fun _ : Fin n => WightmanData.TestFn) ℝ`, whose
value at `φ` is `schwSF` of `ofE4 ∘ φ`, and `abs_schwCML_le` is OS0 in the linear-growth form
`|S_n(φ)| ≤ α γⁿ (n!)² ∏ᵢ 8192 e4Norm 5 (φᵢ)`.

## OS0

`𝓢(E4, ℝ)` carries the Fréchet topology of its seminorm family and no norm generating it. `schwCML n`
is OS0 in the distributional form of Osterwalder–Schrader: each `S_n` is a continuous multilinear
functional on `𝓢(ℝ⁴)ⁿ` with factorial growth in `n`.
-/

namespace MassGap.ObserverOSTempered

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
  MassGap.ObserverEnergyMoments MassGap.ObserverEnergyBox
  MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz Filter
open scoped Topology

/-! ## 1. Multilinearity of `contSF` on one field -/

section ContSF

variable {N : ℕ}

/-- **Every test function decays**: `|f| ≤ M` supported in `[-R, R]⁴` gives `‖f‖₅ ≤ (1 + R)⁵ M`.

DERIVED: `5` the order of the weighted norm; `1` the weight's unit term; `0` the vanishing value. -/
theorem decayBound_of_isTest {f : (Fin 4 → ℝ) → ℝ} {R M : ℝ} (h : IsTest f R M) :
    DecayBound 5 f ((1 + R) ^ 5 * M) := by
  intro y
  have hR := h.1
  have hM := h.M_nonneg
  have hy0 := norm_nonneg y
  by_cases h0 : f y = 0
  · rw [h0, abs_zero, mul_zero]
    exact mul_nonneg (pow_nonneg (by linarith) 5) hM
  · have hy : ‖y‖ ≤ R := (pi_norm_le_iff_of_nonneg hR).mpr
      (fun i => by rw [Real.norm_eq_abs]; exact h.2.2 y h0 i)
    exact mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 5) (h.2.1 y) (abs_nonneg _)
      (pow_nonneg (by linarith) 5)

#print axioms decayBound_of_isTest

/-- **Every family of test functions of one field converges along the ultrafilter**, under the cube
moments of that field (`ObserverOSSchwartz.tendsto_latSF_decay`, `decayBound_of_isTest`).

DERIVED: `5` the order of the weighted norm. -/
theorem tendsto_latSF_test (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAt hN W O t C)
    (n : ℕ) (f : Fin n → TestFn) :
    Tendsto (fun k => latSF hN (energy0 W D hD) k (fun i => (O, f i))) (ultra : Filter ℕ)
      (𝓝 (contSF hN (energy0 W D hD) (fun i => (O, f i)))) := by
  have hex : ∀ i, ∃ R M : ℝ, IsTest (f i).1 R M := fun i => (f i).2
  choose R M hRM using hex
  exact tendsto_latSF_decay hN W hD hpos hO ht hC0 hev n f _
    (fun i => decayBound_of_isTest (hRM i))

#print axioms tendsto_latSF_test

/-- Replacing one test function of a one-field family is replacing one entry of the family.

DERIVED: no numeral. -/
theorem family_update {n : ℕ} [DecidableEq (Fin n)] (O : LField (MassGap.SUN.SU N))
    (f : Fin n → TestFn) (j : Fin n) (x : TestFn) :
    (fun i => ((O, Function.update f j x i) : SField N))
      = Function.update (fun i => ((O, f i) : SField N)) j (O, x) := by
  funext i
  exact Function.apply_update (fun _ (g : TestFn) => ((O, g) : SField N)) f j x i

#print axioms family_update

/-- **The limit is additive in each test function**, for one field with the cube moments.

DERIVED: `0` is the excluded colour count. -/
theorem contSF_update_add_test (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAt hN W O t C)
    {n : ℕ} [DecidableEq (Fin n)] (f : Fin n → TestFn) (j : Fin n) (a b : TestFn) :
    contSF hN (energy0 W D hD) (fun i => (O, Function.update f j (testAdd a b) i))
      = contSF hN (energy0 W D hD) (fun i => (O, Function.update f j a i))
        + contSF hN (energy0 W D hD) (fun i => (O, Function.update f j b i)) := by
  have h1 := tendsto_latSF_test hN W hD hpos hO ht hC0 hev n (Function.update f j (testAdd a b))
  have h2 := tendsto_latSF_test hN W hD hpos hO ht hC0 hev n (Function.update f j a)
  have h3 := tendsto_latSF_test hN W hD hpos hO ht hC0 hev n (Function.update f j b)
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine tendsto_nhds_unique h1 ((h2.add h3).congr (fun k => ?_))
  rw [family_update, family_update, family_update, latSF_update, latSF_update, latSF_update]
  show _ = stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 (testAdd a b) * _)
  rw [smear_testAdd (dySpacing_pos (one_le_of_ne_zero hN) k), add_mul, (stateK hN k).map_add]

#print axioms contSF_update_add_test

/-- **The limit is homogeneous in each test function**, for one field with the cube moments.

DERIVED: `0` is the excluded colour count. -/
theorem contSF_update_smul_test (hN : N ≠ 0) (W : ConfFlow N)
    {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C) (hev : CubeMomentsAt hN W O t C)
    {n : ℕ} [DecidableEq (Fin n)] (f : Fin n → TestFn) (j : Fin n) (c : ℝ) (a : TestFn) :
    contSF hN (energy0 W D hD) (fun i => (O, Function.update f j (testSmul c a) i))
      = c * contSF hN (energy0 W D hD) (fun i => (O, Function.update f j a i)) := by
  have h1 := tendsto_latSF_test hN W hD hpos hO ht hC0 hev n (Function.update f j (testSmul c a))
  have h2 := tendsto_latSF_test hN W hD hpos hO ht hC0 hev n (Function.update f j a)
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  refine tendsto_nhds_unique h1 ((h2.const_mul c).congr (fun k => ?_))
  rw [family_update, family_update, latSF_update, latSF_update]
  show _ = stateK hN k (smear (dySpacing N k) ((energy0 W D hD).map k O).1 (testSmul c a) * _)
  rw [smear_testSmul (dySpacing_pos (one_le_of_ne_zero hN) k), smul_mul_assoc,
    (stateK hN k).map_smul]

#print axioms contSF_update_smul_test

end ContSF

/-! ## 2. Multilinearity of `schwSF` -/

section SchwSF

variable {N : ℕ}

/-- The sum of two decaying functions.

DERIVED: `6` the decay order of `Decaying`; `1` the weight's unit term. -/
def decAdd (g h : Decaying) : Decaying :=
  ⟨fun y => g.1 y + h.1 y, by
    obtain ⟨B, hB⟩ := g.2
    obtain ⟨B', hB'⟩ := h.2
    exact ⟨B + B', fun y => by
      have h1 := hB y
      have h2 := hB' y
      have hp : 0 ≤ (1 + ‖y‖) ^ 6 := pow_nonneg (by linarith [norm_nonneg y]) 6
      calc (1 + ‖y‖) ^ 6 * |g.1 y + h.1 y| ≤ (1 + ‖y‖) ^ 6 * (|g.1 y| + |h.1 y|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) hp
        _ ≤ B + B' := by rw [mul_add]; linarith⟩⟩

/-- A real multiple of a decaying function.

DERIVED: `6` the decay order of `Decaying`. -/
def decSmul (c : ℝ) (g : Decaying) : Decaying :=
  ⟨fun y => c * g.1 y, by
    obtain ⟨B, hB⟩ := g.2
    exact ⟨|c| * B, fun y => by
      rw [abs_mul, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg c)⟩⟩

/-- Truncation is additive.

DERIVED: no numeral. -/
theorem trunc_decAdd (g h : Decaying) (R : ℕ) :
    trunc (decAdd g h) R = testAdd (trunc g R) (trunc h R) :=
  Subtype.ext (funext (fun y => by
    show cubeInd (R : ℝ) y * (g.1 y + h.1 y) = cubeInd (R : ℝ) y * g.1 y + cubeInd (R : ℝ) y * h.1 y
    ring))

#print axioms trunc_decAdd

/-- Truncation is homogeneous.

DERIVED: no numeral. -/
theorem trunc_decSmul (c : ℝ) (g : Decaying) (R : ℕ) :
    trunc (decSmul c g) R = testSmul c (trunc g R) :=
  Subtype.ext (funext (fun y => by
    show cubeInd (R : ℝ) y * (c * g.1 y) = c * (cubeInd (R : ℝ) y * g.1 y)
    ring))

#print axioms trunc_decSmul

/-- Truncating a family with one entry replaced.

DERIVED: no numeral. -/
theorem trunc_family_update {n : ℕ} [DecidableEq (Fin n)] (O : LField (MassGap.SUN.SU N))
    (g : Fin n → Decaying) (j : Fin n) (z : Decaying) (R : ℕ) :
    (fun i => ((O, trunc (Function.update g j z i) R) : SField N))
      = (fun i => ((O, Function.update (fun i => trunc (g i) R) j (trunc z R) i) : SField N)) := by
  funext i
  congr 1
  exact Function.apply_update (fun _ (w : Decaying) => trunc w R) g j z i

#print axioms trunc_family_update

/-- **`schwSF` is additive in each decaying function**, given one exponential moment of the unit cube.

DERIVED: no numeral. -/
theorem schwSF_update_add (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) {n : ℕ} [DecidableEq (Fin n)] (g : Fin n → Decaying)
    (j : Fin n) (x y : Decaying) :
    schwSF hN W D hD O (Function.update g j (decAdd x y))
      = schwSF hN W D hD O (Function.update g j x) + schwSF hN W D hD O (Function.update g j y) := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExp hN W (hpos O hO) h
  have h1 := tendsto_schwSF hN W hD hpos hO h (Function.update g j (decAdd x y))
  have h2 := tendsto_schwSF hN W hD hpos hO h (Function.update g j x)
  have h3 := tendsto_schwSF hN W hD hpos hO h (Function.update g j y)
  refine tendsto_nhds_unique h1 ((h2.add h3).congr (fun R => ?_))
  show contSF hN (energy0 W D hD) (fun i => (O, trunc (Function.update g j x i) R))
      + contSF hN (energy0 W D hD) (fun i => (O, trunc (Function.update g j y i) R))
    = contSF hN (energy0 W D hD) (fun i => (O, trunc (Function.update g j (decAdd x y) i) R))
  rw [trunc_family_update, trunc_family_update, trunc_family_update, trunc_decAdd]
  exact (contSF_update_add_test hN W hD hpos hO ht hC0 hev (fun i => trunc (g i) R) j
    (trunc x R) (trunc y R)).symm

#print axioms schwSF_update_add

/-- **`schwSF` is homogeneous in each decaying function**, given one exponential moment of the unit
cube.

DERIVED: no numeral. -/
theorem schwSF_update_smul (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) {n : ℕ} [DecidableEq (Fin n)] (g : Fin n → Decaying)
    (j : Fin n) (c : ℝ) (x : Decaying) :
    schwSF hN W D hD O (Function.update g j (decSmul c x))
      = c * schwSF hN W D hD O (Function.update g j x) := by
  obtain ⟨t, C, ht, hC0, hev⟩ := cubeMoments_of_unitExp hN W (hpos O hO) h
  have h1 := tendsto_schwSF hN W hD hpos hO h (Function.update g j (decSmul c x))
  have h2 := tendsto_schwSF hN W hD hpos hO h (Function.update g j x)
  refine tendsto_nhds_unique h1 ((h2.const_mul c).congr (fun R => ?_))
  show c * contSF hN (energy0 W D hD) (fun i => (O, trunc (Function.update g j x i) R))
    = contSF hN (energy0 W D hD) (fun i => (O, trunc (Function.update g j (decSmul c x) i) R))
  rw [trunc_family_update, trunc_family_update, trunc_decSmul]
  exact (contSF_update_smul_test hN W hD hpos hO ht hC0 hev (fun i => trunc (g i) R) j c
    (trunc x R)).symm

#print axioms schwSF_update_smul

end SchwSF

/-! ## 3. Euclidean Schwartz functions -/

section Euclid

/-- **The sup norm is at most the Euclidean norm**: `‖y‖_∞ ≤ ‖toLp y‖₂` on `ℝ⁴`.

DERIVED: `2` the Euclidean exponent; `4` in `Fin 4` the spacetime dimension. -/
theorem norm_le_norm_toLp (y : Fin 4 → ℝ) :
    ‖y‖ ≤ ‖(WithLp.toLp 2 y : MassGap.WightmanData.E4)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => ?_)
  have := PiLp.norm_apply_le (WithLp.toLp 2 y : MassGap.WightmanData.E4) i
  rwa [PiLp.toLp_apply] at this

#print axioms norm_le_norm_toLp

/-- **The weighted norm of a Euclidean Schwartz function**: `2^K ∑_{(k,l) ≤ (K,0)} p_{k,l}(φ)`,
`p_{k,l}` Mathlib's Schwartz seminorms on `𝓢(E4, ℝ)`.

DERIVED: `2`, `0` are `SchwartzMap.one_add_le_sup_seminorm_apply`'s. -/
def e4Norm (K : ℕ) (φ : MassGap.WightmanData.TestFn) : ℝ :=
  2 ^ K * ∑ m ∈ Finset.Iic (K, 0), SchwartzMap.seminorm ℝ m.1 m.2 φ

/-- `e4Norm K` is continuous on `𝓢(E4, ℝ)`: a finite sum of the seminorms defining its topology.

DERIVED: `2` the factor of `e4Norm`. -/
theorem continuous_e4Norm (K : ℕ) : Continuous (e4Norm K) :=
  continuous_const.mul (continuous_finsetSum _ (fun m _ =>
    (schwartz_withSeminorms ℝ MassGap.WightmanData.E4 ℝ).continuous_seminorm m))

#print axioms continuous_e4Norm

/-- DERIVED: `0` the sign. -/
theorem e4Norm_nonneg (K : ℕ) (φ : MassGap.WightmanData.TestFn) : 0 ≤ e4Norm K φ :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun m _ => apply_nonneg _ _))

#print axioms e4Norm_nonneg

/-- DERIVED: `0` the zero function. -/
theorem e4Norm_zero (K : ℕ) : e4Norm K 0 = 0 := by
  unfold e4Norm
  simp

#print axioms e4Norm_zero

/-- The sup of finitely many seminorms is at most their sum.

DERIVED: `0` the derivative order and the sign. -/
theorem sup_seminorm_le_sum (K : ℕ) (φ : MassGap.WightmanData.TestFn) :
    (Finset.Iic (K, 0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) φ
      ≤ ∑ m ∈ Finset.Iic (K, 0), SchwartzMap.seminorm ℝ m.1 m.2 φ := by
  apply Seminorm.finset_sup_apply_le
  · exact Finset.sum_nonneg (fun m _ => apply_nonneg _ _)
  · intro m hm
    exact Finset.single_le_sum (f := fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2 φ)
      (fun m _ => apply_nonneg _ _) hm

#print axioms sup_seminorm_le_sum

/-- Mathlib's weighted bound at derivative order `0` on `𝓢(E4, ℝ)`.

DERIVED: `2`, `0` are `SchwartzMap.one_add_le_sup_seminorm_apply`'s. -/
theorem one_add_pow_mul_abs_le (K : ℕ) (φ : MassGap.WightmanData.TestFn)
    (x : MassGap.WightmanData.E4) :
    (1 + ‖x‖) ^ K * |φ x|
      ≤ 2 ^ K * (Finset.Iic (K, 0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) φ := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (K, 0)) (k := K) (n := 0)
    le_rfl le_rfl φ x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h

#print axioms one_add_pow_mul_abs_le

/-- **A Euclidean Schwartz function, read in sup-norm coordinates, has every weighted bound**:
`(1 + ‖y‖_∞)^K |φ(toLp y)| ≤ e4Norm K φ` (`one_add_pow_mul_abs_le`, `norm_le_norm_toLp`,
`sup_seminorm_le_sum`).

DERIVED: `2` the Euclidean exponent and the factor `2^K`; `1` the weight's unit term; `0` the sign. -/
theorem decayBound_e4 (K : ℕ) (φ : MassGap.WightmanData.TestFn) :
    DecayBound K (fun y => φ (WithLp.toLp 2 y)) (e4Norm K φ) := fun y => by
  have h := one_add_pow_mul_abs_le K φ (WithLp.toLp 2 y)
  have hsup := sup_seminorm_le_sum K φ
  have hw : (1 + ‖y‖) ^ K ≤ (1 + ‖(WithLp.toLp 2 y : MassGap.WightmanData.E4)‖) ^ K :=
    pow_le_pow_left₀ (by linarith [norm_nonneg y]) (by linarith [norm_le_norm_toLp y]) K
  have h2 : (0 : ℝ) ≤ 2 ^ K := by positivity
  have h3 := mul_le_mul_of_nonneg_left hsup h2
  have h4 := mul_le_mul_of_nonneg_right hw (abs_nonneg (φ (WithLp.toLp 2 y)))
  show (1 + ‖y‖) ^ K * |φ (WithLp.toLp 2 y)| ≤ 2 ^ K * ∑ m ∈ Finset.Iic (K, 0),
    SchwartzMap.seminorm ℝ m.1 m.2 φ
  linarith

#print axioms decayBound_e4

/-- **A Euclidean Schwartz function as a decaying function** on `Fin 4 → ℝ`.

DERIVED: `6` the decay order of `Decaying`; `2` the Euclidean exponent. -/
def ofE4 (φ : MassGap.WightmanData.TestFn) : Decaying :=
  ⟨fun y => φ (WithLp.toLp 2 y), e4Norm 6 φ, decayBound_e4 6 φ⟩

/-- DERIVED: no numeral. -/
theorem ofE4_add (φ ψ : MassGap.WightmanData.TestFn) :
    ofE4 (φ + ψ) = decAdd (ofE4 φ) (ofE4 ψ) :=
  Subtype.ext (funext (fun y => by
    show (φ + ψ) (WithLp.toLp 2 y) = φ (WithLp.toLp 2 y) + ψ (WithLp.toLp 2 y)
    simp))

#print axioms ofE4_add

/-- DERIVED: no numeral. -/
theorem ofE4_smul (c : ℝ) (φ : MassGap.WightmanData.TestFn) :
    ofE4 (c • φ) = decSmul c (ofE4 φ) :=
  Subtype.ext (funext (fun y => by
    show (c • φ) (WithLp.toLp 2 y) = c * φ (WithLp.toLp 2 y)
    simp))

#print axioms ofE4_smul

/-- DERIVED: no numeral. -/
theorem ofE4_update {n : ℕ} [DecidableEq (Fin n)] (φ : Fin n → MassGap.WightmanData.TestFn)
    (j : Fin n) (x : MassGap.WightmanData.TestFn) :
    (fun i => ofE4 (Function.update φ j x i)) = Function.update (fun i => ofE4 (φ i)) j (ofE4 x) :=
  funext (fun i => Function.apply_update (fun _ => ofE4) φ j x i)

#print axioms ofE4_update

end Euclid

/-! ## 4. Continuity of a multilinear map bounded by a continuous gauge -/

section Continuity

/-- **A multilinear map bounded by a product of a continuous gauge is continuous.** For
`T : V^n → ℝ` multilinear with `|T m| ≤ K ∏ᵢ q(mᵢ)`, `q ≥ 0` continuous and `q 0 = 0`: telescoping
through the hybrids `s.piecewise m₂ m₁` (as in `MultilinearMap.norm_image_sub_le_of_bound'`) gives
`|T m₁ − T m₂| ≤ K ∑ₐ q(m₁ₐ − m₂ₐ) ∏_{j ≠ a} max(q m₁ⱼ, q m₂ⱼ)`, a continuous function of `m₁`
vanishing at `m₂`.

DERIVED: `0` the sign of `q` and `K` and the gauge at the origin. -/
theorem continuous_of_bound_by {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] {n : ℕ} (T : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (q : V → ℝ)
    (hq : Continuous q) (hq0 : ∀ v, 0 ≤ q v) (hqz : q 0 = 0) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ m, |T m| ≤ K * ∏ i, q (m i)) : Continuous T := by
  classical
  have diff : ∀ m₁ m₂ : (Fin n → V), |T m₁ - T m₂|
      ≤ K * ∑ a, ∏ j, (if j = a then q (m₁ a - m₂ a) else max (q (m₁ j)) (q (m₂ j))) := by
    intro m₁ m₂
    have A : ∀ s : Finset (Fin n), |T m₁ - T (s.piecewise m₂ m₁)|
        ≤ K * ∑ a ∈ s, ∏ j, (if j = a then q (m₁ a - m₂ a) else max (q (m₁ j)) (q (m₂ j))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his Hrec =>
        have I : |T (s.piecewise m₂ m₁) - T ((insert i s).piecewise m₂ m₁)|
            ≤ K * ∏ j, (if j = i then q (m₁ i - m₂ i) else max (q (m₁ j)) (q (m₂ j))) := by
          have eA : (insert i s).piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₂ i) :=
            Finset.piecewise_insert s m₂ m₁ i
          have eB : s.piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₁ i) := by
            simp [his]
          rw [eB, eA, ← T.map_update_sub]
          refine (H _).trans (mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod (fun j _ => hq0 _) (fun j _ => ?_)) hK)
          by_cases hji : j = i
          · subst hji
            simp
          · rw [Function.update_of_ne hji, if_neg hji]
            by_cases h' : j ∈ s
            · rw [Finset.piecewise_eq_of_mem s m₂ m₁ h']; exact le_max_right _ _
            · rw [Finset.piecewise_eq_of_notMem s m₂ m₁ h']; exact le_max_left _ _
        calc |T m₁ - T ((insert i s).piecewise m₂ m₁)|
            ≤ |T m₁ - T (s.piecewise m₂ m₁)|
              + |T (s.piecewise m₂ m₁) - T ((insert i s).piecewise m₂ m₁)| := abs_sub_le _ _ _
          _ ≤ _ := add_le_add Hrec I
          _ = K * ∑ a ∈ insert i s,
                ∏ j, (if j = a then q (m₁ a - m₂ a) else max (q (m₁ j)) (q (m₂ j))) := by
              rw [Finset.sum_insert his, mul_add, add_comm]
    have := A Finset.univ
    rwa [Finset.piecewise_univ] at this
  refine continuous_iff_continuousAt.2 (fun m₀ => ?_)
  let g : (Fin n → V) → ℝ := fun m =>
    K * ∑ a, ∏ j, (if j = a then q (m a - m₀ a) else max (q (m j)) (q (m₀ j)))
  have hg : Continuous g := by
    refine continuous_const.mul (continuous_finsetSum _ (fun a _ =>
      continuous_finsetProd _ (fun j _ => ?_)))
    by_cases hja : j = a
    · simp only [if_pos hja]
      exact hq.comp ((continuous_apply a).sub continuous_const)
    · simp only [if_neg hja]
      exact (hq.comp (continuous_apply j)).max continuous_const
  have hzero : ∀ a, ∏ j, (if j = a then q (m₀ a - m₀ a) else max (q (m₀ j)) (q (m₀ j))) = 0 :=
    fun a => Finset.prod_eq_zero (Finset.mem_univ a) (by rw [if_pos rfl, sub_self, hqz])
  have hg0 : g m₀ = 0 := by
    show K * ∑ a, ∏ j, (if j = a then q (m₀ a - m₀ a) else max (q (m₀ j)) (q (m₀ j))) = 0
    rw [Finset.sum_congr rfl (fun a _ => hzero a), Finset.sum_const_zero, mul_zero]
  have hlim : Tendsto g (𝓝 m₀) (𝓝 0) := by
    have := hg.tendsto m₀
    rwa [hg0] at this
  have habs : Tendsto (fun m => |T m - T m₀|) (𝓝 m₀) (𝓝 0) :=
    squeeze_zero (fun m => abs_nonneg _) (fun m => diff m m₀) hlim
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

#print axioms continuous_of_bound_by

end Continuity

/-! ## 5. The Schwinger functions on `𝓢(E4, ℝ)` -/

section Schwinger

variable {N : ℕ}

/-- **The Schwinger functions of the energy density on Euclidean Schwartz functions, as a
multilinear map**: `φ ↦ schwSF (ofE4 ∘ φ)`, additive and homogeneous in each slot
(`schwSF_update_add`, `schwSF_update_smul`), given one exponential moment of the unit cube.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def schwMulti (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) (n : ℕ) :
    MultilinearMap ℝ (fun _ : Fin n => MassGap.WightmanData.TestFn) ℝ where
  toFun φ := schwSF hN W D hD O (fun i => ofE4 (φ i))
  map_update_add' φ j a b := by
    show schwSF hN W D hD O (fun i => ofE4 (Function.update φ j (a + b) i))
      = schwSF hN W D hD O (fun i => ofE4 (Function.update φ j a i))
        + schwSF hN W D hD O (fun i => ofE4 (Function.update φ j b i))
    rw [ofE4_update, ofE4_update, ofE4_update, ofE4_add]
    exact schwSF_update_add hN W hD hpos hO h _ j _ _
  map_update_smul' φ j c a := by
    show schwSF hN W D hD O (fun i => ofE4 (Function.update φ j (c • a) i))
      = c • schwSF hN W D hD O (fun i => ofE4 (Function.update φ j a i))
    rw [ofE4_update, ofE4_update, ofE4_smul, smul_eq_mul]
    exact schwSF_update_smul hN W hD hpos hO h _ j c _

/-- DERIVED: no numeral. -/
theorem schwMulti_apply (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn) :
    schwMulti hN W hD hpos hO h n φ = schwSF hN W D hD O (fun i => ofE4 (φ i)) := rfl

#print axioms schwMulti_apply

/-- **The growth bound on Euclidean Schwartz functions**: there are `t > 0`, `C ≥ 0` with
`|S_n(φ)| ≤ (1 + n (2n)! t^{-2n} C) ∏ᵢ 8192 e4Norm 5 (φᵢ)` for every `n` and `φ`
(`ObserverOSSchwartz.abs_schwSF_le`, `decayBound_e4`).

DERIVED: `5`, `8192` are `abs_schwSF_le`'s; `0` the sign of `t`, `C`; `2`, `1` the factorial
constant. -/
theorem abs_schwMulti_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) :
    ∃ t C : ℝ, 0 < t ∧ 0 ≤ C ∧ ∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
      |schwMulti hN W hD hpos hO h n φ|
        ≤ (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C)) * ∏ i, 8192 * e4Norm 5 (φ i) := by
  obtain ⟨t, C, ht, hC0, hb⟩ := abs_schwSF_le hN W hD hpos hO h
  exact ⟨t, C, ht, hC0, fun n φ => hb n _ _ (fun i => decayBound_e4 5 (φ i))⟩

#print axioms abs_schwMulti_le

/-- **OS0 in the Schwartz topology: the Schwinger functions are continuous multilinear functionals on
`𝓢(E4, ℝ)ⁿ`.** `schwMulti` with continuity from `continuous_of_bound_by` at the gauge
`q = 8192 · e4Norm 5`, continuous on `𝓢(E4, ℝ)` (`continuous_e4Norm`).

DERIVED: `8192`, `5` are `abs_schwMulti_le`'s; `0` the gauge at the origin and the signs. -/
def schwCML (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => MassGap.WightmanData.TestFn) ℝ where
  toMultilinearMap := schwMulti hN W hD hpos hO h n
  cont := by
    obtain ⟨t, C, ht, hC0, hb⟩ := abs_schwMulti_le hN W hD hpos hO h
    refine continuous_of_bound_by (schwMulti hN W hD hpos hO h n) (fun φ => 8192 * e4Norm 5 φ)
      (continuous_const.mul (continuous_e4Norm 5))
      (fun φ => mul_nonneg (by norm_num) (e4Norm_nonneg 5 φ))
      (by rw [e4Norm_zero, mul_zero])
      (1 + n * (((2 * n).factorial : ℝ) / t ^ (2 * n) * C))
      (add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos ht _).le) hC0)))
      (fun φ => hb n φ)

/-- DERIVED: no numeral. -/
theorem schwCML_apply (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn) :
    schwCML hN W hD hpos hO h n φ = schwSF hN W D hD O (fun i => ofE4 (φ i)) := rfl

#print axioms schwCML_apply

/-- **OS0 in the linear-growth form on `𝓢(E4, ℝ)`**: one `α = 1 + C`, `γ = 8 (1 + t⁻¹)²` with
`|S_n(φ₁, …, φₙ)| ≤ α γⁿ (n!)² ∏ᵢ 8192 e4Norm 5 (φᵢ)` for every `n`, `e4Norm 5` a finite sum of
Schwartz seminorms of `𝓢(E4, ℝ)` (`abs_schwMulti_le`, `ObserverOSGrowth.growth_const_le`).

DERIVED: `8`, `2`, `1` are `growth_const_le`'s; `5`, `8192` as in `abs_schwMulti_le`; `0` the sign. -/
theorem abs_schwCML_le (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) :
    ∃ α γ : ℝ, ∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
      |schwCML hN W hD hpos hO h n φ|
        ≤ α * γ ^ n * (n.factorial : ℝ) ^ 2 * ∏ i, 8192 * e4Norm 5 (φ i) := by
  obtain ⟨t, C, ht, hC0, hb⟩ := abs_schwMulti_le hN W hD hpos hO h
  refine ⟨1 + C, 8 * (1 + t⁻¹) ^ 2, fun n φ => ?_⟩
  have hP0 : 0 ≤ ∏ i, 8192 * e4Norm 5 (φ i) :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (e4Norm_nonneg 5 (φ i)))
  exact (hb n φ).trans (mul_le_mul_of_nonneg_right (growth_const_le ht hC0 n) hP0)

#print axioms abs_schwCML_le

/-- **On compactly supported Euclidean data the functional is the limit Schwinger function**: if
`φᵢ ∘ toLp` is a test function `fᵢ`, then `S_n(φ) = contSF (O, fᵢ)` (`schwSF_eq_contSF`).

DERIVED: `2` the Euclidean exponent. -/
theorem schwCML_eq_contSF (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D)
    (h : UnitCubeExpBound hN W O) {n : ℕ} (φ : Fin n → MassGap.WightmanData.TestFn)
    (f : Fin n → TestFn) (hφf : ∀ i, (fun y => φ i (WithLp.toLp 2 y)) = (f i).1) :
    schwCML hN W hD hpos hO h n φ = contSF hN (energy0 W D hD) (fun i => (O, f i)) :=
  schwSF_eq_contSF hN W hD hpos hO h (fun i => ofE4 (φ i)) f hφf

#print axioms schwCML_eq_contSF

end Schwinger

end MassGap.ObserverOSTempered
