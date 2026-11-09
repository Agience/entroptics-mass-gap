import Mathlib
import MassGap.ShellTranslate

/-!
# MassGap.ShellJoint — the joint spectral measure of energy and momentum for one vector

`ShellMomentum.clay_zero_momentum_sector` reads the Clay gap from Källén–Lehmann data under the
identification `hσ : σ 0 = rateMeasure (X.time 1) (P0 T u)`. Both sides of `hσ` are readings of one
object the tree did not have: the joint spectral measure of the time translation and the spatial
translations for the vector `u`. This module builds it by Gelfand duality, without Bochner's theorem,
reads its time marginal and its momentum transform, places the zero-momentum vector inside it, and
then shows what `hσ` asks of that vector. Declarations are in the namespace `MassGap.ShellJoint`.

## What the tree has

* `ShellMeasure.vecMeasure a u`, `rateMeasure a u`: the spectral and rate measures of one vector for
  one positive contraction, by the continuous functional calculus and Riesz–Markov–Kakutani.
* `ShellTranslate.realT`, packaged as `realRep : UnitaryRep (spatial τ) FlowH`: a strongly continuous
  unitary representation of the spatial vectors, commuting with `timeT` (`commute_realT_timeT`),
  fixing the vacuum (`realT_vac`), the identity on `V⊥` (`realT_orth`).
* Mathlib: commutative C⋆-algebras and the Gelfand transform `gelfandStarTransform : A ≃⋆ₐ[ℂ]
  C(characterSpace ℂ A, ℂ)`, the closed star subalgebra instance `StarSubalgebra.cstarAlgebra`,
  `StarAlgHomClass.map_cfc`, and `RealRMK.rieszMeasure` on compact Hausdorff spaces. No Bochner, SNAG
  or Stone theorem is used.

## 1. The joint algebra (proved)

`JointData E G`: a self-adjoint `a` with spectrum in `[0, 1]` and a `UnitaryRep G E` commuting with
it. `star_U`: `U(x)⋆ = U(−x)`. The generators `{a} ∪ U(G)` commute pairwise and are closed under
`star`, so the norm closure `alg J` of the star algebra they generate lies in its own commutant
(`alg_mul_comm`, from `topologicalClosure_adjoin_le_centralizer_centralizer`); it is a commutative
unital C⋆-algebra (`CommCStarAlgebra (alg J)`). `Chars J` is its character space, compact Hausdorff,
with its Borel σ-algebra.

## 2. The joint measure (proved)

`op J F = (gelfandStarTransform)⁻¹ F` for `F ∈ C(Chars J, ℂ)`. The vector state
`f ↦ Re ⟪u, op (f) u⟫` is positive (`f = |√f|²` gives `⟪u, op(f) u⟫ = ‖op(√f) u‖²`), and
`jointMeasure J u` is its Riesz–Markov–Kakutani measure, finite on the compact space.

* `integral_jointMeasure`: `∫ f dμ_u = Re ⟪u, op(f) u⟫` for real continuous `f`;
  `integral_complex`: `∫ F dμ_u = ⟪u, op(F) u⟫` for complex continuous `F` (the real and imaginary
  parts are self-adjoint).
* `jointMeasure_real_univ`: the total mass is `‖u‖²`.
* `inner_U_eq_integral`: `⟪u, U(x) u⟫ = ∫ χ(U x) dμ_u(χ)` — the momentum transform. The momentum of
  a character is the map `x ↦ χ(U x)`, a unitary character of `G`. Plainly, its continuity in `x` is
  is not available: the character space can hold characters of `G` that are not continuous (the
  algebra is norm closed and `x ↦ U x` is only strongly continuous; the Bohr compactification
  phenomenon). The identification `χ(U x) = e^{i p·x}` with `p ∈ ℝ³` is therefore
  not made here; everything below is stated on the characters themselves.
* `vecMeasure_eq_map`: `vecMeasure a u` is the push-forward of `μ_u` under the time coordinate
  `χ ↦ clamp (Re χ(a))`; `rateMeasure_eq_joint`: `rateMeasure a u` is the push-forward of `μ_u`
  restricted to `{χ(a) > 0}` under `χ ↦ −log χ(a)`. The time marginal is the rate measure; nothing
  is chosen. The identity uses `χ(cfc g a) = g(χ(a))` (`gelfand_cfc`, `StarAlgHomClass.map_cfc`) and
  `ι(cfc g a) = cfc g a` for the inclusion `ι` (`coe_cfc_aB`).

## 3. The zero-momentum vector inside the joint measure (proved)

`fixSp J`: the vectors fixed by every `U x`; `zeroProj J` its orthogonal projection.

* `commute_starProjection'`: an operator `T` with `T K ⊆ K` and `T⋆ K ⊆ K` commutes with the
  projection on `K`; so every element of `alg J` commutes with `zeroProj J` (`commute_zeroProj`).
* `integral_split`: `∫ F dμ_u = ∫ F dμ_{P₀u} + ∫ F dμ_{u − P₀u}` for every continuous `F`.
* `ae_eq_of_eigen`: if `b u = c u` for `b ∈ alg J`, then `χ(b) = c` for `μ_u`-almost every `χ`
  (`∫ |χ(b) − c|² dμ_u = ‖(b − c) u‖²`). `ae_fix`: the joint measure of a fixed vector lives on
  `χ(U x) = 1`, for each `x`.
* `zero_momentum_slice`: for every `u`, `μ_{P₀u}` lives on `χ(U x) = 1` for each `x`, the joint
  measure splits as above, and `rateMeasure a (P₀ u)` is the time marginal of `μ_{P₀u}`.
  Plainly, the converse half, that `μ_{u − P₀u}` gives no weight to the set of characters trivial on
  every `U x`, is not proved here; it needs the projection on the intersection of the fixed spaces as
  a limit along finite families (the mean ergodic theorem of `ShellMomentum` gives one translation).

## 4. What `hσ` asks (proved; the physical reading is argued)

* `kl_zero_slice_ne_zero`: under `KallenLehmann σ ρ`, `ρ (Iic 0) = 0` and `SpecBottom ρ M2`, the
  zero-momentum sector `σ 0` is not the zero measure.
* `hσ_forces_zero_momentum_vector`: so `hσ` of `clay_zero_momentum_sector` forces `P0 T u ≠ 0`: the
  vector must have a non-zero component that is exactly translation invariant.
* Argued, not formalised: in a translation-invariant continuum theory the vacuum is the only
  normalisable vector fixed by the spatial translations (an atom of the joint (H, P) measure at
  (E, 0), E > 0, would be carried by Lorentz covariance to uncountably many atoms), so `P0 T u = 0` for `u` in the vacuum complement and
  `hσ` cannot hold; the momentum-`0` sector of Källén–Lehmann is the density of the joint measure at
  `p = 0` (its disintegration in `p`), not the restriction to the set `p = 0`, which is the measure
  of `P₀u` built here. On the tree's `observerRealSpatial` data `P0` contains all of `V⊥`, where
  `realT` is the identity (`tree_orth_zero_momentum`), so there `P0 T u ≠ 0` is possible without
  any physical zero-momentum state.

## 5. Load tests (proved)

* `eigen_point`: a joint eigenvector `a v = λ v`, `U x v = c_x v` has joint measure on
  `χ(a) = λ`, `χ(U x) = c_x`, of mass `‖v‖²`. `vacuum_rate`: with `λ = 1` its rate marginal is
  `μ_v(univ) δ₀`.
* `planeWave_dirac`: the free plane wave `x ↦ e^{i p·x}` on `ℂ` (`ShellTranslate.planeWave`) with the
  scalar time step `e^{−ω}`: the joint measure of `1` lives on `χ(U x) = e^{i p·x}` for every `x`
  (the Dirac momentum `p`) and `∫ χ(U x) dμ = e^{i p·x}`.
* `treeData`: the tree's instance, `timeT 1` with `realRep`. `tree_vacuum`: the tree's vacuum sits at
  the point `χ(timeT 1) = 1`, `χ(realT x) = 1` (rate `0`, momentum `0`), and its rate marginal is
  `μ(univ) δ₀`. `tree_joint`: the time marginal of the tree's joint measure is
  `rateMeasure (timeT 1) u`, and its momentum transform is `⟪u, realT x u⟫`.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ShellJoint

open Real Filter Topology MeasureTheory Set WeakDual
open scoped CompactlySupported
open MassGap.BandShell (shell SpecBottom)
open MassGap.ShellMeasure (vecMeasure rateMeasure clamp continuous_clamp measurable_rate
  KallenLehmann klWeight measurable_shell measurable_klWeight)
open MassGap.ShellMomentum (integral_vecMeasure commute_starProjection inner_split
  rateMeasure_zero_vec SpatialData)
open MassGap.ShellGap (spectrum_Icc_of_nonneg spectrum_time)
open MassGap.ObserverOSReconstructionS (OSDataS)

noncomputable section

/-! ## 1. The joint algebra -/

/-- **Joint data**: a positive contraction `a` (self-adjoint, spectrum in `[0, 1]`) and a strongly
continuous unitary representation of `G` commuting with it. DERIVED: `0`, `1` the ends of the
spectrum interval. -/
structure JointData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (G : Type*) [AddCommGroup G] [TopologicalSpace G] where
  /-- The time step. -/
  a : E →L[ℂ] E
  sa : IsSelfAdjoint a
  hsp : spectrum ℝ a ⊆ Icc 0 1
  /-- The translations. -/
  R : MassGap.ShellTranslate.UnitaryRep G E
  comm : ∀ x, Commute (R.U x) a

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {G : Type*} [AddCommGroup G] [TopologicalSpace G] (J : JointData E G)

/-- **A translation is an isometry**: `U(x)⋆ U(x) = 1`. DERIVED: `1` the identity. -/
theorem star_mul_self_U (x : G) : star (J.R.U x) * J.R.U x = 1 := by
  refine ContinuousLinearMap.ext fun z => ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, J.R.inner_U, ContinuousLinearMap.one_apply]

/-- **The adjoint of a translation is the inverse translation.** DERIVED: `1` the identity. -/
theorem star_U (x : G) : star (J.R.U x) = J.R.U (-x) := by
  have h1 : J.R.U x * J.R.U (-x) = 1 := by rw [← J.R.map_add, add_neg_cancel, J.R.map_zero]
  calc star (J.R.U x) = star (J.R.U x) * (J.R.U x * J.R.U (-x)) := by rw [h1, mul_one]
    _ = J.R.U (-x) := by rw [← mul_assoc, star_mul_self_U, one_mul]

/-- **Translations commute.** DERIVED: no numeral. -/
theorem U_comm (x y : G) : J.R.U x * J.R.U y = J.R.U y * J.R.U x := by
  rw [← J.R.map_add, ← J.R.map_add, add_comm]

/-- **The generators** `{a} ∪ U(G)`. DERIVED: no numeral. -/
def gens : Set (E →L[ℂ] E) := insert J.a (Set.range J.R.U)

/-- DERIVED: no numeral. -/
theorem star_mem_gens {g : E →L[ℂ] E} (hg : g ∈ gens J) : star g ∈ gens J := by
  rcases hg with rfl | ⟨x, rfl⟩
  · rw [J.sa.star_eq]; exact Set.mem_insert _ _
  · rw [star_U]; exact Set.mem_insert_of_mem _ ⟨-x, rfl⟩

/-- **The generators commute pairwise.** DERIVED: no numeral. -/
theorem gens_comm {g h : E →L[ℂ] E} (hg : g ∈ gens J) (hh : h ∈ gens J) : g * h = h * g := by
  rcases hg with rfl | ⟨x, rfl⟩ <;> rcases hh with rfl | ⟨y, rfl⟩
  · rfl
  · exact (J.comm y).eq.symm
  · exact (J.comm x).eq
  · exact U_comm J x y

/-- DERIVED: no numeral. -/
theorem mem_centralizer_gens {z : E →L[ℂ] E} (hz : z ∈ gens J) :
    z ∈ StarSubalgebra.centralizer ℂ (gens J) := by
  rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, Set.mem_centralizer_iff]
  rintro m (hm | hm)
  · exact gens_comm J hm hz
  · have hm' : star m ∈ gens J := Set.mem_star.mp hm
    rw [← star_star m]
    exact gens_comm J (star_mem_gens J hm') hz

/-- **The joint algebra**: the norm closure of the star algebra generated by `a` and the
translations. DERIVED: no numeral. -/
def alg : StarSubalgebra ℂ (E →L[ℂ] E) := (StarAlgebra.adjoin ℂ (gens J)).topologicalClosure

/-- DERIVED: no numeral. -/
theorem alg_le_centralizer : alg J ≤ StarSubalgebra.centralizer ℂ (gens J) :=
  StarSubalgebra.topologicalClosure_minimal
    (StarAlgebra.adjoin_le fun _ hz => mem_centralizer_gens J hz)
    (by rw [StarSubalgebra.coe_centralizer]; exact Set.isClosed_centralizer _)

/-- **The joint algebra is commutative.** DERIVED: no numeral. -/
theorem alg_mul_comm {x y : E →L[ℂ] E} (hx : x ∈ alg J) (hy : y ∈ alg J) : x * y = y * x := by
  have h1 := alg_le_centralizer J hx
  have h2 := StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer ℂ (gens J) hy
  rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, Set.mem_centralizer_iff] at h2
  exact h2 x (Or.inl h1)

instance : CStarAlgebra (alg J) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := StarSubalgebra.isClosed_topologicalClosure _)

instance : NormedCommRing (alg J) :=
  { SubringClass.toNormedRing (alg J) with
    mul_comm := fun x y => Subtype.ext (alg_mul_comm J x.2 y.2) }

instance : CommCStarAlgebra (alg J) where

/-- **The time step in the joint algebra.** DERIVED: no numeral. -/
def aB : alg J :=
  ⟨J.a, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _))⟩

/-- **A translation in the joint algebra.** DERIVED: no numeral. -/
def UB (x : G) : alg J :=
  ⟨J.R.U x, StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ⟨x, rfl⟩))⟩

/-- DERIVED: no numeral. -/
theorem sa_aB : IsSelfAdjoint (aB J) := Subtype.ext J.sa.star_eq

/-- **The characters of the joint algebra.** DERIVED: no numeral. -/
abbrev Chars : Type _ := characterSpace ℂ (alg J)

instance : MeasurableSpace (Chars J) := borel _

instance : BorelSpace (Chars J) := ⟨rfl⟩

/-! ## 2. The joint measure -/

/-- **The operator of a continuous function on the characters** (inverse Gelfand transform).
DERIVED: no numeral. -/
def op (F : C(Chars J, ℂ)) : E →L[ℂ] E := ((gelfandStarTransform (alg J)).symm F : alg J)

/-- DERIVED: no numeral. -/
theorem op_add (F H : C(Chars J, ℂ)) : op J (F + H) = op J F + op J H := by
  simp only [op, map_add]; rfl

/-- DERIVED: no numeral. -/
theorem op_smul (c : ℂ) (F : C(Chars J, ℂ)) : op J (c • F) = c • op J F := by
  simp only [op, map_smul]; rfl

/-- DERIVED: no numeral. -/
theorem op_mul (F H : C(Chars J, ℂ)) : op J (F * H) = op J F * op J H := by
  simp only [op, map_mul]; rfl

/-- DERIVED: no numeral. -/
theorem op_star (F : C(Chars J, ℂ)) : op J (star F) = star (op J F) := by
  simp only [op, map_star]; rfl

/-- DERIVED: `1` the unit. -/
theorem op_one : op J 1 = 1 := by
  simp only [op, map_one]; rfl

/-- DERIVED: no numeral. -/
theorem op_G (b : alg J) : op J (gelfandStarTransform (alg J) b) = b := by
  simp only [op, StarAlgEquiv.symm_apply_apply]

/-- **A real function as a complex one.** DERIVED: no numeral. -/
def liftR (f : C(Chars J, ℝ)) : C(Chars J, ℂ) :=
  ⟨fun χ => (f χ : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

/-- **The vector state** `f ↦ Re ⟪u, op(f) u⟫` on real continuous functions. DERIVED: no numeral. -/
def stateLin (u : E) : C_c(Chars J, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ u (op J (liftR J f.toContinuousMap) u)).re
  map_add' f g := by
    have h : liftR J (f + g).toContinuousMap
        = liftR J f.toContinuousMap + liftR J g.toContinuousMap :=
      ContinuousMap.ext fun χ => by simp [liftR]
    rw [h, op_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' c f := by
    have h : liftR J (c • f).toContinuousMap = (c : ℂ) • liftR J f.toContinuousMap :=
      ContinuousMap.ext fun χ => by simp [liftR]
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [h, op_smul, ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]

/-- **The vector state is positive**: `f = |√f|²` gives `⟪u, op(f) u⟫ = ‖op(√f) u‖²`.
DERIVED: `0` the order's bottom. -/
theorem stateLin_nonneg (u : E) (f : C_c(Chars J, ℝ)) (hf : 0 ≤ f) : 0 ≤ stateLin J u f := by
  have hf' : ∀ χ, 0 ≤ f χ := fun χ => by
    simpa using (CompactlySupportedContinuousMap.le_def.mp hf χ)
  let H : C(Chars J, ℂ) := ⟨fun χ => ((Real.sqrt (f χ) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp f.continuous)⟩
  have hH : liftR J f.toContinuousMap = star H * H := ContinuousMap.ext fun χ => by
    show ((f χ : ℝ) : ℂ) = (starRingEnd ℂ) ((Real.sqrt (f χ) : ℝ) : ℂ) * ((Real.sqrt (f χ) : ℝ) : ℂ)
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf' χ)]
  show 0 ≤ (inner ℂ u (op J (liftR J f.toContinuousMap) u)).re
  rw [hH, op_mul, op_star, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- DERIVED: no numeral. -/
def stateMap (u : E) : C_c(Chars J, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (stateLin J u) (stateLin_nonneg J u)

/-- **The joint spectral measure of `u`**: the Riesz–Markov–Kakutani measure of the vector state on
the characters of the joint algebra. DERIVED: no numeral. -/
def jointMeasure (u : E) : Measure (Chars J) := RealRMK.rieszMeasure (stateMap J u)

instance (u : E) : IsFiniteMeasure (jointMeasure J u) := by
  unfold jointMeasure; infer_instance

/-- **The joint spectral theorem for real functions**: `∫ f dμ_u = Re ⟪u, op(f) u⟫`.
DERIVED: no numeral. -/
theorem integral_jointMeasure (u : E) (f : C(Chars J, ℝ)) :
    ∫ χ, f χ ∂(jointMeasure J u) = (inner ℂ u (op J (liftR J f) u)).re := by
  have h := RealRMK.integral_rieszMeasure (stateMap J u) ⟨f, HasCompactSupport.of_compactSpace _⟩
  exact h

/-- **A self-adjoint operator has real expectations.** DERIVED: no numeral. -/
theorem inner_re_of_sa {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) (u : E) :
    (((inner ℂ u (T u)).re : ℝ) : ℂ) = inner ℂ u (T u) := by
  have h : (starRingEnd ℂ) (inner ℂ u (T u)) = inner ℂ u (T u) := by
    rw [inner_conj_symm, MassGap.ShellTranslate.inner_sa hT]
  exact Complex.conj_eq_iff_re.mp h

/-- DERIVED: no numeral. -/
theorem sa_op_liftR (f : C(Chars J, ℝ)) : IsSelfAdjoint (op J (liftR J f)) := by
  have h : star (liftR J f) = liftR J f := ContinuousMap.ext fun χ => by
    show (starRingEnd ℂ) ((f χ : ℝ) : ℂ) = ((f χ : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  show star (op J (liftR J f)) = op J (liftR J f)
  rw [← op_star, h]

/-- **The joint spectral theorem**: `∫ F dμ_u = ⟪u, op(F) u⟫` for every complex continuous `F` on
the characters. DERIVED: no numeral. -/
theorem integral_complex (u : E) (F : C(Chars J, ℂ)) :
    ∫ χ, F χ ∂(jointMeasure J u) = inner ℂ u (op J F u) := by
  let Fr : C(Chars J, ℝ) := ⟨fun χ => (F χ).re, Complex.continuous_re.comp F.continuous⟩
  let Fi : C(Chars J, ℝ) := ⟨fun χ => (F χ).im, Complex.continuous_im.comp F.continuous⟩
  have hF : F = liftR J Fr + Complex.I • liftR J Fi := ContinuousMap.ext fun χ => by
    show F χ = ((F χ).re : ℂ) + Complex.I * ((F χ).im : ℂ)
    rw [mul_comm]; exact (Complex.re_add_im (F χ)).symm
  have i1 : Integrable (fun χ => ((Fr χ : ℝ) : ℂ)) (jointMeasure J u) :=
    (liftR J Fr).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun χ => ((Fi χ : ℝ) : ℂ) * Complex.I) (jointMeasure J u) :=
    ((liftR J Fi).continuous.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc ∫ χ, F χ ∂(jointMeasure J u)
      = ∫ χ, (((Fr χ : ℝ) : ℂ) + ((Fi χ : ℝ) : ℂ) * Complex.I) ∂(jointMeasure J u) :=
        integral_congr_ae (Eventually.of_forall fun χ => (Complex.re_add_im (F χ)).symm)
    _ = ((∫ χ, Fr χ ∂(jointMeasure J u) : ℝ) : ℂ)
          + ((∫ χ, Fi χ ∂(jointMeasure J u) : ℝ) : ℂ) * Complex.I := by
        rw [integral_add i1 i2, integral_mul_const, integral_complex_ofReal,
          integral_complex_ofReal]
    _ = inner ℂ u (op J F u) := by
        rw [integral_jointMeasure, integral_jointMeasure, inner_re_of_sa (sa_op_liftR J Fr),
          inner_re_of_sa (sa_op_liftR J Fi)]
        conv_rhs => rw [hF]
        rw [op_add, op_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          inner_add_right, inner_smul_right]
        ring

/-- **The total mass is `‖u‖²`.** DERIVED: `1` the unit; `2` the square. -/
theorem jointMeasure_real_univ (u : E) : (jointMeasure J u).real univ = ‖u‖ ^ 2 := by
  have h := integral_jointMeasure J u 1
  have h1 : liftR J 1 = 1 := ContinuousMap.ext fun χ => by simp [liftR]
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h
  rw [h1, op_one, ContinuousLinearMap.one_apply] at h
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) u

/-- **The momentum transform**: `⟪u, U(x) u⟫ = ∫ χ(U x) dμ_u(χ)`. DERIVED: no numeral. -/
theorem inner_U_eq_integral (u : E) (x : G) :
    inner ℂ u (J.R.U x u) = ∫ χ, χ (UB J x) ∂(jointMeasure J u) := by
  have h := integral_complex J u (gelfandStarTransform (alg J) (UB J x))
  rw [op_G] at h
  exact h.symm

/-- **The time coordinate of a character**, `χ(a)` read on `[0, 1]`. DERIVED: `0`, `1` the ends
of the spectrum interval. -/
def tclamp (χ : Chars J) : Icc (0 : ℝ) 1 := clamp (χ (aB J)).re

/-- DERIVED: no numeral. -/
theorem continuous_tclamp : Continuous (tclamp J) :=
  continuous_clamp.comp
    (Complex.continuous_re.comp (map_continuous (gelfandStarTransform (alg J) (aB J))))

/-- **Characters commute with the functional calculus of the time step**: the Gelfand transform of
`g(a)` is `χ ↦ g(χ(a))`. DERIVED: no numeral. -/
theorem gelfand_cfc {k : ℝ → ℝ} (hk : Continuous k) (f : C(Chars J, ℝ))
    (hf : ∀ χ, f χ = k (χ (aB J)).re) :
    gelfandStarTransform (alg J) (cfc k (aB J)) = liftR J f := by
  refine ContinuousMap.ext fun χ => ?_
  show χ (cfc k (aB J)) = ((f χ : ℝ) : ℂ)
  have hz : IsSelfAdjoint (χ (aB J)) := (sa_aB J).map χ
  rw [StarAlgHomClass.map_cfc χ k (aB J) hk.continuousOn (map_continuous χ) (sa_aB J) hz, hf χ]
  have hre : algebraMap ℝ ℂ (χ (aB J)).re = χ (aB J) := by
    rw [Complex.coe_algebraMap]; exact Complex.conj_eq_iff_re.mp hz
  calc cfc k (χ (aB J)) = cfc k (algebraMap ℝ ℂ (χ (aB J)).re) := by rw [hre]
    _ = algebraMap ℝ ℂ (k (χ (aB J)).re) := cfc_algebraMap _ _
    _ = ((k (χ (aB J)).re : ℝ) : ℂ) := by rw [Complex.coe_algebraMap]

/-- **The inclusion commutes with the functional calculus.** DERIVED: no numeral. -/
theorem coe_cfc_aB {k : ℝ → ℝ} (hk : Continuous k) :
    ((cfc k (aB J) : alg J) : E →L[ℂ] E) = cfc k J.a := by
  have h := StarAlgHom.map_cfc (alg J).subtype k (aB J) hk.continuousOn continuous_subtype_val
    (sa_aB J) J.sa
  exact h

/-- **The time marginal of the joint measure is the spectral measure of `a`**: `vecMeasure a u` is
the push-forward of `μ_u` under the time coordinate. DERIVED: `0`, `1` the ends of the spectrum
interval. -/
theorem vecMeasure_eq_map (u : E) : vecMeasure J.a u = (jointMeasure J u).map (tclamp J) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun h => ?_
  rw [integral_vecMeasure J.hsp u h, integral_map (continuous_tclamp J).measurable.aemeasurable
    h.continuous.aestronglyMeasurable]
  have hk : Continuous (fun y : ℝ => h (clamp y)) := h.continuous.comp continuous_clamp
  let g : C(Chars J, ℝ) := ⟨fun χ => h (clamp (χ (aB J)).re),
    hk.comp (Complex.continuous_re.comp (map_continuous (gelfandStarTransform (alg J) (aB J))))⟩
  have hop : op J (liftR J g) = cfc (fun y : ℝ => h (clamp y)) J.a := by
    rw [← gelfand_cfc J hk g (fun _ => rfl), op_G, coe_cfc_aB J hk]
  have e := integral_jointMeasure J u g
  rw [hop] at e
  exact e.symm

/-- **The time marginal is the rate measure**: `rateMeasure a u` is the push-forward of `μ_u`
restricted to `χ(a) > 0` under `χ ↦ −log χ(a)`. DERIVED: `0` the excluded kernel point. -/
theorem rateMeasure_eq_joint (u : E) :
    rateMeasure J.a u = ((jointMeasure J u).restrict {χ | 0 < (tclamp J χ).1}).map
      (fun χ => -Real.log (tclamp J χ).1) := by
  have hm := (continuous_tclamp J).measurable
  unfold rateMeasure
  rw [vecMeasure_eq_map, Measure.restrict_map hm (measurableSet_lt measurable_const
    measurable_subtype_coe), Measure.map_map measurable_rate hm]
  rfl

/-! ## 3. The zero-momentum vector inside the joint measure -/

/-- **The fixed vectors** of every translation. DERIVED: no numeral. -/
def fixSp : Submodule ℂ E where
  carrier := {z | ∀ x, J.R.U x z = z}
  add_mem' hz hw x := by rw [map_add, hz x, hw x]
  zero_mem' x := map_zero _
  smul_mem' c z hz x := by rw [map_smul, hz x]

/-- DERIVED: no numeral. -/
theorem mem_fixSp {z : E} : z ∈ fixSp J ↔ ∀ x, J.R.U x z = z := Iff.rfl

/-- DERIVED: no numeral. -/
theorem isClosed_fixSp : IsClosed (fixSp J : Set E) := by
  show IsClosed {z : E | ∀ x, J.R.U x z = z}
  rw [Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_eq (J.R.U x).continuous continuous_id

instance : CompleteSpace (fixSp J) := (isClosed_fixSp J).completeSpace_coe

/-- **The zero-momentum projection** of the joint data. DERIVED: no numeral. -/
def zeroProj : E →L[ℂ] E := (fixSp J).starProjection

/-- **An operator reducing a closed subspace commutes with its projection**: `T K ⊆ K` and
`T⋆ K ⊆ K`. DERIVED: `0` the vanishing pairings. -/
theorem commute_starProjection' (K : Submodule ℂ E) [K.HasOrthogonalProjection] {T : E →L[ℂ] E}
    (hK : ∀ x ∈ K, T x ∈ K) (hK' : ∀ x ∈ K, star T x ∈ K) : Commute T K.starProjection := by
  show T * K.starProjection = K.starProjection * T
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  refine (Submodule.eq_starProjection_of_mem_orthogonal (hK _ (K.starProjection_apply_mem x))
    ?_).symm
  rw [← map_sub]
  have hw := Submodule.sub_starProjection_mem_orthogonal (K := K) x
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro k hk
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
  exact hw _ (hK' k hk)

/-- DERIVED: no numeral. -/
theorem U_mem_fixSp (x : G) {z : E} (hz : z ∈ fixSp J) : J.R.U x z ∈ fixSp J := by
  rw [show J.R.U x z = z from hz x]; exact hz

/-- DERIVED: no numeral. -/
theorem a_mem_fixSp {z : E} (hz : z ∈ fixSp J) : J.a z ∈ fixSp J := (mem_fixSp J).mpr fun y => by
  rw [← ContinuousLinearMap.mul_apply, (J.comm y).eq, ContinuousLinearMap.mul_apply, hz y]

/-- **Every generator commutes with the zero-momentum projection.** DERIVED: no numeral. -/
theorem commute_gens_zeroProj {g : E →L[ℂ] E} (hg : g ∈ gens J) : Commute g (zeroProj J) := by
  rcases hg with rfl | ⟨x, rfl⟩
  · exact commute_starProjection (fixSp J) J.sa fun z hz => a_mem_fixSp J hz
  · refine commute_starProjection' (fixSp J) (fun z hz => U_mem_fixSp J x hz) fun z hz => ?_
    rw [star_U]; exact U_mem_fixSp J (-x) hz

/-- DERIVED: no numeral. -/
theorem alg_le_centralizer_zeroProj : alg J ≤ StarSubalgebra.centralizer ℂ {zeroProj J} := by
  refine StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le fun g hg => ?_)
    (by rw [StarSubalgebra.coe_centralizer]; exact Set.isClosed_centralizer _)
  have hc := commute_gens_zeroProj J hg
  have hsP : star (zeroProj J) = zeroProj J := (isSelfAdjoint_starProjection (fixSp J)).star_eq
  rw [SetLike.mem_coe, ← SetLike.mem_coe, StarSubalgebra.coe_centralizer, Set.mem_centralizer_iff]
  rintro m (hm | hm)
  · rw [Set.mem_singleton_iff.mp hm]; exact hc.eq.symm
  · have hm' : m = zeroProj J := by
      rw [← star_star m, Set.mem_singleton_iff.mp (Set.mem_star.mp hm), hsP]
    rw [hm']; exact hc.eq.symm

/-- **Every element of the joint algebra commutes with the zero-momentum projection.**
DERIVED: no numeral. -/
theorem commute_zeroProj {b : E →L[ℂ] E} (hb : b ∈ alg J) : Commute b (zeroProj J) := by
  have h := alg_le_centralizer_zeroProj J hb
  rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, Set.mem_centralizer_iff] at h
  exact (h (zeroProj J) (Or.inl (Set.mem_singleton _))).symm

/-- **The joint measure splits along the zero-momentum projection**:
`∫ F dμ_u = ∫ F dμ_{P₀u} + ∫ F dμ_{u − P₀u}`. DERIVED: no numeral. -/
theorem integral_split (u : E) (F : C(Chars J, ℂ)) :
    ∫ χ, F χ ∂(jointMeasure J u) = ∫ χ, F χ ∂(jointMeasure J (zeroProj J u))
      + ∫ χ, F χ ∂(jointMeasure J (u - zeroProj J u)) := by
  rw [integral_complex, integral_complex, integral_complex]
  exact inner_split (isSelfAdjoint_starProjection _) (fixSp J).isIdempotentElem_starProjection
    (commute_zeroProj J ((gelfandStarTransform (alg J)).symm F).2) u

/-- **An eigenvector's joint measure lives on the eigenvalue**: `b u = c u` gives `χ(b) = c` for
`μ_u`-almost every `χ`, from `∫ |χ(b) − c|² dμ_u = ‖(b − c) u‖² = 0`. DERIVED: `0` the vanishing
norm; `1` the unit. -/
theorem ae_eq_of_eigen (v : E) (b : alg J) (c : ℂ) (hv : (b : E →L[ℂ] E) v = c • v) :
    ∀ᵐ χ ∂(jointMeasure J v), χ b = c := by
  set d : alg J := b - c • 1 with hd
  have hdv : (d : E →L[ℂ] E) v = 0 := by
    show ((b : E →L[ℂ] E) - c • (1 : E →L[ℂ] E)) v = 0
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, hv, sub_self]
  let f : C(Chars J, ℝ) := ⟨fun χ => Complex.normSq (χ d),
    Complex.continuous_normSq.comp (map_continuous (gelfandStarTransform (alg J) d))⟩
  have hf : liftR J f = gelfandStarTransform (alg J) (star d * d) := ContinuousMap.ext fun χ => by
    show ((Complex.normSq (χ d) : ℝ) : ℂ) = χ (star d * d)
    rw [map_mul, map_star, Complex.normSq_eq_conj_mul_self]; rfl
  have hint := integral_jointMeasure J v f
  rw [hf, op_G] at hint
  have h0 : ∫ χ, f χ ∂(jointMeasure J v) = 0 := by
    rw [hint]
    show (inner ℂ v ((star (d : E →L[ℂ] E) * (d : E →L[ℂ] E)) v)).re = 0
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hdv, inner_zero_left, Complex.zero_re]
  have hae := (integral_eq_zero_iff_of_nonneg (fun χ : Chars J => Complex.normSq_nonneg (χ d))
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp h0
  filter_upwards [hae] with χ hχ
  have h1 : χ d = 0 := Complex.normSq_eq_zero.mp hχ
  rw [hd, map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_eq_zero] at h1
  exact h1

/-- **A fixed vector's joint measure lives on the trivial character of each translation.**
DERIVED: `1` the trivial value. -/
theorem ae_fix {v : E} (hv : v ∈ fixSp J) (x : G) :
    ∀ᵐ χ ∂(jointMeasure J v), χ (UB J x) = 1 :=
  ae_eq_of_eigen J v (UB J x) 1 (by rw [one_smul]; exact hv x)

/-- **The zero-momentum slice**: the joint measure of `P₀u` lives on `χ(U x) = 1` for each `x`, the
joint measure of `u` is that of `P₀u` plus that of `u − P₀u` on every continuous function, and
`rateMeasure a (P₀u)` is the time marginal of `μ_{P₀u}`. DERIVED: `0` the excluded kernel point;
`1` the trivial value. -/
theorem zero_momentum_slice (u : E) :
    (∀ x, ∀ᵐ χ ∂(jointMeasure J (zeroProj J u)), χ (UB J x) = 1)
      ∧ (∀ F : C(Chars J, ℂ), ∫ χ, F χ ∂(jointMeasure J u)
          = ∫ χ, F χ ∂(jointMeasure J (zeroProj J u))
            + ∫ χ, F χ ∂(jointMeasure J (u - zeroProj J u)))
      ∧ rateMeasure J.a (zeroProj J u)
          = ((jointMeasure J (zeroProj J u)).restrict {χ | 0 < (tclamp J χ).1}).map
              (fun χ => -Real.log (tclamp J χ).1) :=
  ⟨fun x => ae_fix J ((fixSp J).starProjection_apply_mem u) x, integral_split J u,
    rateMeasure_eq_joint J _⟩

/-! ### Load tests -/

/-- **A joint eigenvector is a point of the joint spectrum**: `a v = λ v`, `U x v = c_x v` give
`χ(a) = λ` and `χ(U x) = c_x` almost everywhere, with total mass `‖v‖²`. DERIVED: `2` the square. -/
theorem eigen_point (v : E) (lam : ℂ) (c : G → ℂ) (ha : J.a v = lam • v)
    (hU : ∀ x, J.R.U x v = c x • v) :
    (∀ᵐ χ ∂(jointMeasure J v), χ (aB J) = lam) ∧ (∀ x, ∀ᵐ χ ∂(jointMeasure J v), χ (UB J x) = c x)
      ∧ (jointMeasure J v).real univ = ‖v‖ ^ 2 :=
  ⟨ae_eq_of_eigen J v (aB J) lam ha, fun x => ae_eq_of_eigen J v (UB J x) (c x) (hU x),
    jointMeasure_real_univ J v⟩

/-- **A vector fixed by the time step has rate measure `μ(univ) δ₀`.** DERIVED: `0` the rate of
the fixed point; `1` the fixed value. -/
theorem vacuum_rate (v : E) (ha : J.a v = v) :
    rateMeasure J.a v = (jointMeasure J v univ) • Measure.dirac 0 := by
  have h1 : ∀ᵐ χ ∂(jointMeasure J v), χ (aB J) = 1 :=
    ae_eq_of_eigen J v (aB J) 1 (by rw [one_smul]; exact ha)
  have ht : ∀ᵐ χ ∂(jointMeasure J v), (tclamp J χ).1 = 1 := by
    filter_upwards [h1] with χ hχ
    show (clamp (χ (aB J)).re).1 = 1
    rw [hχ, Complex.one_re, clamp, projIcc_right]
  have hset : {χ : Chars J | 0 < (tclamp J χ).1} =ᵐ[jointMeasure J v] (univ : Set (Chars J)) := by
    filter_upwards [ht] with χ hχ
    simp only [eq_iff_iff]
    show (0 < (tclamp J χ).1) ↔ True
    rw [hχ]; exact iff_of_true zero_lt_one trivial
  have hfun : (fun χ => -Real.log (tclamp J χ).1) =ᵐ[jointMeasure J v] fun _ => (0 : ℝ) := by
    filter_upwards [ht] with χ hχ
    rw [hχ, Real.log_one, neg_zero]
  rw [rateMeasure_eq_joint, Measure.restrict_congr_set hset, Measure.restrict_univ,
    Measure.map_congr hfun, Measure.map_const]

end Generic

/-! ## 4. What `hσ` asks -/

/-- **The Källén–Lehmann zero-momentum sector is not zero**: with `ρ (Iic 0) = 0` and a spectral
bottom, `σ 0 = shell(·, 0)_* (ρ / (2 √s))` charges something. DERIVED: `0` the zero momentum and the
bottom of the `s`-line; `1` a positive width for the spectral bottom (every positive width gives the
same contradiction); `2` as in `klWeight`. -/
theorem kl_zero_slice_ne_zero {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} (hkl : KallenLehmann σ ρ)
    (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ} (hb : SpecBottom ρ M2) : σ 0 ≠ 0 := by
  intro h0
  rw [hkl 0 le_rfl] at h0
  have hw : ∫⁻ s, klWeight 0 s ∂ρ = 0 := by
    have h := congrArg (fun μ : Measure ℝ => μ univ) h0
    rw [Measure.map_apply (measurable_shell 0) MeasurableSet.univ, preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    simpa using h
  have hae := (lintegral_eq_zero_iff (measurable_klWeight 0)).mp hw
  have hpos : ρ (Ioi 0) = 0 := by
    refine measure_mono_null (fun s hs => ?_) (ae_iff.mp hae)
    have hs0 : 0 < shell s 0 := Real.sqrt_pos.mpr (by simpa using hs)
    show ¬ klWeight 0 s = (0 : ℝ → ENNReal) s
    simp only [Pi.zero_apply, klWeight, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos one_pos (mul_pos two_pos hs0)
  have huniv : ρ univ = 0 := by
    rw [← Iic_union_Ioi (a := (0 : ℝ))]
    exact measure_union_null hρ0 hpos
  have h1 := hb.2 1 one_pos
  rw [measure_mono_null (subset_univ _) huniv] at h1
  exact lt_irrefl _ h1

/-- **`hσ` forces a translation-invariant component**: under the Källén–Lehmann data of
`ShellMomentum.clay_zero_momentum_sector`, `σ 0 = rateMeasure (X.time 1) (P0 T u)` implies
`P0 T u ≠ 0`. DERIVED: `0` the zero vector and the zero momentum; `1` the unit step. -/
theorem hσ_forces_zero_momentum_vector {X : OSDataS} (T : SpatialData X) (u : X.H)
    {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} (hkl : KallenLehmann σ ρ) (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ}
    (hb : SpecBottom ρ M2) (hσ : σ 0 = rateMeasure (X.time 1) (MassGap.ShellMomentum.P0 T u)) :
    MassGap.ShellMomentum.P0 T u ≠ 0 := by
  intro h0
  rw [h0, rateMeasure_zero_vec (spectrum_time X zero_le_one)] at hσ
  exact kl_zero_slice_ne_zero hkl hρ0 hb hσ

/-! ## 5. Load tests: the plane wave and the tree -/

section Plane

open MassGap.ShellTranslate (spatial planeWave phase)

/-- **The free plane wave** of momentum `p` with the scalar time step `e^{−ω}` on `ℂ`.
DERIVED: `ω ≥ 0` the mode's rate, a free variable of the test, not a chosen value. -/
def planeData (τ : Fin 4) (p : Fin 4 → ℝ) {ω : ℝ} (hω : 0 ≤ ω) : JointData ℂ (spatial τ) where
  a := algebraMap ℝ (ℂ →L[ℂ] ℂ) (Real.exp (-ω))
  sa := cfc_predicate_algebraMap (A := ℂ →L[ℂ] ℂ) _
  hsp := MassGap.ShellGap.spectrum_scalar hω
  R := planeWave τ p
  comm _ := Algebra.commute_algebraMap_right _ _

/-- **The plane wave has a Dirac momentum**: its joint measure lives on `χ(U x) = e^{i p·x}` for
every `x`, and `∫ χ(U x) dμ = e^{i p·x}`. DERIVED: `1` the unit vector of `ℂ`. -/
theorem planeWave_dirac (τ : Fin 4) (p : Fin 4 → ℝ) {ω : ℝ} (hω : 0 ≤ ω) (x : spatial τ) :
    (∀ᵐ χ ∂(jointMeasure (planeData τ p hω) 1),
        χ (UB (planeData τ p hω) x) = Complex.exp ((phase p x : ℂ) * Complex.I))
      ∧ ∫ χ, χ (UB (planeData τ p hω) x) ∂(jointMeasure (planeData τ p hω) 1)
          = Complex.exp ((phase p x : ℂ) * Complex.I) := by
  have hU : ((UB (planeData τ p hω) x : alg (planeData τ p hω)) : ℂ →L[ℂ] ℂ) 1
      = Complex.exp ((phase p x : ℂ) * Complex.I) • (1 : ℂ) := rfl
  refine ⟨ae_eq_of_eigen _ 1 _ _ hU, ?_⟩
  rw [← inner_U_eq_integral]
  show inner ℂ (1 : ℂ) (Complex.exp ((phase p x : ℂ) * Complex.I) • (1 : ℂ))
    = Complex.exp ((phase p x : ℂ) * Complex.I)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_one]
  simp

end Plane

section Tree

variable {N : ℕ}

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumTimeGroup MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate (spatial realT realRep realT_vac realT_orth commute_realT_timeT Jd)

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
  (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

include hpos hcube

/-- **The tree's joint data**: the unit time translation `timeT 1` and the real spatial
translations `realRep` on the observer's reconstruction space. DERIVED: `0` the sign of the time;
`1` the unit time. -/
def treeData : JointData (FlowH hN (energy0 W D hD) hB τ hpp) (spatial τ) where
  a := timeT hN (energy0 W D hD) hB τ hpp 1
  sa := (timeT_nonneg_norm hN (energy0 W D hD) hB τ hpp 1 zero_le_one).2.1
  hsp := spectrum_Icc_of_nonneg (timeT_nonneg_norm hN (energy0 W D hD) hB τ hpp 1 zero_le_one).1
    (timeT_nonneg_norm hN (energy0 W D hD) hB τ hpp 1 zero_le_one).2.2
  R := realRep hN W hD hpos hcube hB τ hpp
  comm x := commute_realT_timeT hN W hD hpos hcube hB τ hpp x 1

/-- **The tree's joint measure reads both translations**: its time marginal is
`rateMeasure (timeT 1) u`, its momentum transform is `⟪u, realT x u⟫`, its mass `‖u‖²`.
DERIVED: `0` the excluded kernel point; `1` the unit time; `2` the square. -/
theorem tree_joint (u : FlowH hN (energy0 W D hD) hB τ hpp) :
    rateMeasure (timeT hN (energy0 W D hD) hB τ hpp 1) u
        = ((jointMeasure (treeData hN W hD hpos hcube hB τ hpp) u).restrict
            {χ | 0 < (tclamp (treeData hN W hD hpos hcube hB τ hpp) χ).1}).map (fun χ => -Real.log (tclamp (treeData hN W hD hpos hcube hB τ hpp) χ).1)
      ∧ (∀ x, inner ℂ u (realT hN W hD hpos hcube hB τ hpp x u)
          = ∫ χ, χ (UB (treeData hN W hD hpos hcube hB τ hpp) x) ∂(jointMeasure (treeData hN W hD hpos hcube hB τ hpp) u))
      ∧ (jointMeasure (treeData hN W hD hpos hcube hB τ hpp) u).real univ = ‖u‖ ^ 2 :=
  ⟨rateMeasure_eq_joint (treeData hN W hD hpos hcube hB τ hpp) u, fun x => inner_U_eq_integral (treeData hN W hD hpos hcube hB τ hpp) u x,
    jointMeasure_real_univ (treeData hN W hD hpos hcube hB τ hpp) u⟩

/-- **The tree's vacuum is the point (rate `0`, momentum `0`)**: `χ(timeT 1) = 1` and
`χ(realT x) = 1` almost everywhere, and its rate marginal is `μ(univ) δ₀`. DERIVED: `0` the rate of
the vacuum; `1` the unit time and the trivial value. -/
theorem tree_vacuum :
    (∀ᵐ χ ∂(jointMeasure (treeData hN W hD hpos hcube hB τ hpp) (vacT hN (energy0 W D hD) hB τ hpp)),
        χ (aB (treeData hN W hD hpos hcube hB τ hpp)) = 1)
      ∧ (∀ x, ∀ᵐ χ ∂(jointMeasure (treeData hN W hD hpos hcube hB τ hpp)
          (vacT hN (energy0 W D hD) hB τ hpp)), χ (UB (treeData hN W hD hpos hcube hB τ hpp) x) = 1)
      ∧ rateMeasure (timeT hN (energy0 W D hD) hB τ hpp 1) (vacT hN (energy0 W D hD) hB τ hpp)
          = (jointMeasure (treeData hN W hD hpos hcube hB τ hpp)
              (vacT hN (energy0 W D hD) hB τ hpp) univ) • Measure.dirac 0 := by
  have ha : (treeData hN W hD hpos hcube hB τ hpp).a (vacT hN (energy0 W D hD) hB τ hpp)
      = vacT hN (energy0 W D hD) hB τ hpp :=
    timeT_vacT hN (energy0 W D hD) hB τ hpp zero_le_one
  have hU : ∀ x, (treeData hN W hD hpos hcube hB τ hpp).R.U x (vacT hN (energy0 W D hD) hB τ hpp)
      = vacT hN (energy0 W D hD) hB τ hpp :=
    fun x => realT_vac hN W hD hpos hcube hB τ hpp x
  refine ⟨ae_eq_of_eigen (treeData hN W hD hpos hcube hB τ hpp) _ (aB (treeData hN W hD hpos hcube hB τ hpp)) 1 (by rw [one_smul]; exact ha),
    fun x => ae_eq_of_eigen (treeData hN W hD hpos hcube hB τ hpp) _ (UB (treeData hN W hD hpos hcube hB τ hpp) x) 1 (by rw [one_smul]; exact hU x),
    vacuum_rate (treeData hN W hD hpos hcube hB τ hpp) _ ha⟩

/-- **On the tree, every vector of `V⊥` sits at momentum `0`**: `realT` is the identity there
(`realT_orth`), so its joint measure lives on `χ(realT x) = 1`. This is the `V⊥` part of `P0` for
the tree's `observerRealSpatial`, which is not a physical zero-momentum statement. DERIVED: `0` the
vanishing image; `1` the trivial value. -/
theorem tree_orth_zero_momentum {z : FlowH hN (energy0 W D hD) hB τ hpp}
    (hz : Jd hN (energy0 W D hD) hB D τ hpp z = 0) (x : spatial τ) :
    ∀ᵐ χ ∂(jointMeasure (treeData hN W hD hpos hcube hB τ hpp) z), χ (UB (treeData hN W hD hpos hcube hB τ hpp) x) = 1 :=
  ae_fix (treeData hN W hD hpos hcube hB τ hpp) ((mem_fixSp (treeData hN W hD hpos hcube hB τ hpp)).mpr fun y => realT_orth hN W hD hpos hcube hB τ hpp y hz) x

end Tree

end

end MassGap.ShellJoint

#print axioms MassGap.ShellJoint.star_mul_self_U
#print axioms MassGap.ShellJoint.star_U
#print axioms MassGap.ShellJoint.alg_mul_comm
#print axioms MassGap.ShellJoint.op_G
#print axioms MassGap.ShellJoint.stateLin_nonneg
#print axioms MassGap.ShellJoint.jointMeasure
#print axioms MassGap.ShellJoint.integral_jointMeasure
#print axioms MassGap.ShellJoint.integral_complex
#print axioms MassGap.ShellJoint.jointMeasure_real_univ
#print axioms MassGap.ShellJoint.inner_U_eq_integral
#print axioms MassGap.ShellJoint.gelfand_cfc
#print axioms MassGap.ShellJoint.coe_cfc_aB
#print axioms MassGap.ShellJoint.vecMeasure_eq_map
#print axioms MassGap.ShellJoint.rateMeasure_eq_joint
#print axioms MassGap.ShellJoint.commute_starProjection'
#print axioms MassGap.ShellJoint.commute_zeroProj
#print axioms MassGap.ShellJoint.integral_split
#print axioms MassGap.ShellJoint.ae_eq_of_eigen
#print axioms MassGap.ShellJoint.ae_fix
#print axioms MassGap.ShellJoint.zero_momentum_slice
#print axioms MassGap.ShellJoint.eigen_point
#print axioms MassGap.ShellJoint.vacuum_rate
#print axioms MassGap.ShellJoint.kl_zero_slice_ne_zero
#print axioms MassGap.ShellJoint.hσ_forces_zero_momentum_vector
#print axioms MassGap.ShellJoint.planeData
#print axioms MassGap.ShellJoint.planeWave_dirac
#print axioms MassGap.ShellJoint.treeData
#print axioms MassGap.ShellJoint.tree_joint
#print axioms MassGap.ShellJoint.tree_vacuum
#print axioms MassGap.ShellJoint.tree_orth_zero_momentum
