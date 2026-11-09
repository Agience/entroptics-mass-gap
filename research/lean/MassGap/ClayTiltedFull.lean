import Mathlib
import MassGap.ShortDistanceRunning
import MassGap.ContinuumHypercubic
import MassGap.ContinuumSepClass
import MassGap.ObserverRotation
import MassGap.ObserverRotationDense

noncomputable section

/-!
# MassGap.ClayTiltedFull — rotation clauses on `C³` families and bounded readings on the class

This module states the rotation clauses on families whose test functions are `C³`, and bounds the
lattice readings of separated families of class test functions.

* Rotation, on the `C³` part. A rotated `C³` test function is `C³` (`contDiff_rotTest`); finite
  spatial variation is stated along the lattice axes and is not preserved by a rotation, so the
  rotation clauses quantify over families whose test functions are `C³`, all of which are uniformly
  continuous (`uniformContinuous_of_contDiff`). `PythInvariantSmoothAlong` is (P) there,
  `RotationOpenSmoothAlong` is `RotationOpenAlong` there (`rotationOpenSmooth_of_rotationOpen`), and
  `OrbitContinuousSmoothAlong` is continuity on `SO(4)` of `A ↦ contS (F ∘ A)` there.
* Bounded readings. `contSAlong` is a `limUnder`, unspecified on an unbounded sequence.
  `exists_abs_latSkR_le_of_diagBoundClass`: E on a class bounds the lattice readings of every
  separated family of class test functions, positive-time or not: a dyadic time translation
  (`latSkRAlong_translate`) makes the family a class monomial `Q`, its reading is that of `θ∅ ∪ Q`,
  and Cauchy–Schwarz against the empty monomial bounds it by E on `Q`. So the `ultra` limit exists
  and is `contSAlong` (`tendsto_contSAlong_of_diagBoundClass`). `SmoothSepBoundedAlong` is this on
  separated `C³` families, as the proposition `SmoothSepBoundedAlong`.

DERIVED (module-wide): `0` the time axis and the reflection plane; `3` the order of the derivatives;
`4` the dimension of a rotation.
-/

namespace MassGap.ClayTiltedFull

open Filter Topology MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.NonTrivialCanonical
  MassGap.ContinuumSepClass MassGap.ShortDistanceRunning
  MassGap.ContinuumHypercubic MassGap.ObserverRotation MassGap.ObserverRotationDense
  MassGap.SO4Planes
open scoped Matrix

variable {N : ℕ}

/-! ## 4. The rotation clause on the `C³` part -/

/-- A `C³` test function is uniformly continuous: it is continuous with compact support. -/
theorem uniformContinuous_of_contDiff {f : TestFn} (hf : ContDiff ℝ 3 f.1) : UniformContinuous f.1 := by
  obtain ⟨R, Mf, hR, hMf, hRs⟩ := f.2
  have hcs : HasCompactSupport f.1 := by
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : Fin 4 → ℝ) R)
      (isCompact_closedBall 0 R) (fun y hy => ?_)
    by_contra hne
    apply hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hR).mpr (fun i => ?_)
    rw [Real.norm_eq_abs]
    exact hRs y hne i
  exact hcs.uniformContinuous_of_continuous hf.continuous

/-- **A rotated `C³` test function is `C³`.** -/
theorem contDiff_rotTest {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : Aᵀ * A = 1) {f : TestFn}
    (hf : ContDiff ℝ 3 f.1) : ContDiff ℝ 3 (rotTest A f).1 := by
  have e : (rotTest A f).1 = f.1 ∘ (LinearMap.toContinuousLinearMap (Matrix.toLin' A)) := by
    funext y
    simp [rotTest_apply A hA, Matrix.toLin'_apply]
  rw [e]
  exact hf.comp (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).contDiff

/-- **(P) on `C³` families (named hypothesis).** `pyth` leaves `contS` unchanged on every separated
family of `HypScalar` fields whose test functions are `C³`. CHOSEN: `3` the order of differentiability
of the test functions; the proofs here use only continuity, so a lower order would serve and `3`
narrows the families covered. -/
def PythInvariantSmoothAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, HypScalar (F i).1) →
    (∀ i, ContDiff ℝ 3 (F i).2.1) → (∃ d : ℝ, 0 < d ∧ ContinuumSep.FamSep d F) →
      contSAlong hN βs ρ (rotFam pyth F) = contSAlong hN βs ρ F

/-- **Orbit continuity on `C³` families (named hypothesis).** For every separated family of `HypScalar`
fields whose test functions are `C³`, `A ↦ contS (rotFam A F)` is continuous on `SO(4)`.
CHOSEN: `3` the order of differentiability, as in `PythInvariantSmoothAlong`. -/
def OrbitContinuousSmoothAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, HypScalar (F i).1) →
    (∀ i, ContDiff ℝ 3 (F i).2.1) → (∃ d : ℝ, 0 < d ∧ ContinuumSep.FamSep d F) →
      ContinuousOn (fun A : Matrix (Fin 4) (Fin 4) ℝ => contSAlong hN βs ρ (rotFam A F))
        (SO4 : Set (Matrix (Fin 4) (Fin 4) ℝ))

/-- **`RotationOpenAlong` on `C³` families.** For every `Rot ∈ SO(4)` that is not a signed permutation
and every family of `HypScalar` fields whose test functions are `C³`, which with its rotated family is
`d`-separated for some `d > 0`, composing every test function with `Rot` leaves `contS` unchanged.
CHOSEN: `3` the order of differentiability, as in `PythInvariantSmoothAlong`. -/
def RotationOpenSmoothAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) : Prop :=
  ∀ Rot : Matrix (Fin 4) (Fin 4) ℝ, Rot ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ →
    (¬ ∃ (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ), (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ y i, Rot.mulVec y i = s i * y (σ i)) →
    ∀ (ι : Type) [Fintype ι] (F F' : ι → SField N), (∀ i, HypScalar (F i).1) →
      (∀ i, ContDiff ℝ 3 (F i).2.1) →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.FamSep d F ∧ ContinuumSep.FamSep d F') →
      (∀ i, (F' i).1 = (F i).1) → (∀ i y, (F' i).2.1 y = (F i).2.1 (Rot.mulVec y)) →
      contSAlong hN βs ρ F' = contSAlong hN βs ρ F

/-- **`RotationOpenAlong` gives its `C³` part.** -/
theorem rotationOpenSmooth_of_rotationOpen (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N)
    (h : RotationOpenAlong hN βs ρ) : RotationOpenSmoothAlong hN βs ρ :=
  fun Rot hRot hns ι _ F F' hΦ hS hsep hf ht =>
    h Rot hRot hns ι F F' hΦ (fun i => uniformContinuous_of_contDiff (hS i)) hsep hf ht

/-! ## 5. Boundedness of separated families of class test functions -/

section Bounded

open MassGap.InfiniteLattice

/-- **Lattice translation invariance of the renormalised readings.** At every step `k ≥ m`,
translating every test function by `site (dySpacing N m) n` leaves the reading unchanged: it is the
lattice translation by `2^(k-m) n`, under which the periodic state is invariant. -/
theorem latSkRAlong_translate (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) {ι : Type} [Fintype ι]
    (F : ι → SField N) {m k : ℕ} (hk : m ≤ k) (n : ISite) :
    latSkRAlong hN βs ρ k (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) n)))
      = latSkRAlong hN βs ρ k F := by
  show ρ.pref k F * latS (stateAlong hN βs k) (dySpacing N k) (fun i => ((ρ.field k (F i)).1,
      (ρ.field k (F i)).2.translate (site (dySpacing N m) n)))
    = ρ.pref k F * latS (stateAlong hN βs k) (dySpacing N k) (fun i => ρ.field k (F i))
  rw [site_dySpacing N hk n]
  congr 1
  exact latS_translate _ (fun τ => PeriodicState.periodicState_shift hN _ τ)
    (dySpacing_pos (one_le_of_ne_zero hN) k) _ _

/-- **E on a class bounds every separated family of class test functions.** A family whose test
functions lie in the class and are pairwise `d`-separated, `d > 0`, is translated forward in time by
one dyadic vector until every support lies in `y₀ ≥ d`; it is then a class monomial `Q`, and its
reading is the reflected pair `θ∅ ∪ Q` (`latSkRAlong_translate`, `latSkRAlong_comp_equiv`). Cauchy–
Schwarz against the empty monomial (`pairBoundClass_of_diagBoundClass`) bounds it by the square root
of E on `Q`. The family need not be positive-time or split into reflected halves. -/
theorem exists_abs_latSkR_le_of_diagBoundClass (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N)
    (hR : ρ.ReflCompat 0) {𝒯 : TestClass} (hD : DiagBoundClassAlong hN βs ρ 0 𝒯)
    {ι : Type} [Fintype ι] (F : ι → SField N) {d : ℝ} (hd : 0 < d) (hF : ContinuumSep.FamSep d F)
    (h𝒯 : ∀ i, 𝒯.mem (F i).2) :
    ∃ C : ℝ, ∀ᶠ k in atTop, |latSkRAlong hN βs ρ k F| ≤ C := by
  classical
  set n := Fintype.card ι
  obtain ⟨e⟩ : Nonempty (Fin n ≃ ι) := ⟨(Fintype.equivFin ι).symm⟩
  have hex : ∀ i, ∃ R M : ℝ, IsTest (F i).2.1 R M := fun i => (F i).2.2
  choose R M hRM using hex
  set R₀ : ℝ := ∑ i, R i with hR₀def
  have hR₀ : ∀ i y, (F i).2.1 y ≠ 0 → |y 0| ≤ R₀ := fun i y hy =>
    ((hRM i).2.2 y hy 0).trans
      (Finset.single_le_sum (f := R) (fun j _ => (hRM j).1) (Finset.mem_univ i))
  have ha := dySpacing_pos (one_le_of_ne_zero hN) 0
  obtain ⟨T, hT⟩ := exists_nat_ge ((R₀ + d) / dySpacing N 0)
  set v : Fin 4 → ℝ := timeVec N 0 0 (T : ℤ) with hvdef
  have hv0 : R₀ + d ≤ v 0 := by
    rw [hvdef, ContinuumReconstruction.timeVec_self]
    have := (div_le_iff₀ ha).mp hT
    push_cast
    linarith
  set Q : Mono N := ⟨n, fun i => ((F (e i)).1, (F (e i)).2.translate v)⟩ with hQdef
  have hQsep : ContinuumSep.sepPos 0 d Q := by
    refine ⟨fun i y hy => ?_, fun i j hij => ContinuumSep.sepBy_translate
      (hF (e i) (e j) (e.injective.ne hij)) v⟩
    have h1 := hR₀ (e i) (y - v) hy
    have h2 : (y - v) 0 = y 0 - v 0 := rfl
    rw [h2] at h1
    linarith [(abs_le.mp h1).1]
  set P : ClassMono N 0 𝒯 := ⟨⟨Q, d, hd, hQsep⟩, fun i => 𝒯.translate_mem _ v (h𝒯 (e i))⟩
  obtain ⟨C, hC⟩ := pairBoundClass_of_diagBoundClass hN βs ρ 0 𝒯 hR hD (emptyClass N 0 𝒯) P
  have hC0 := hC 0 0
  rw [Function.iterate_zero_apply, Function.iterate_zero_apply] at hC0
  have hQF : ∀ k, latSkRAlong hN βs ρ k (pairFam 0 (emptyMono N) Q) = latSkRAlong hN βs ρ k F := by
    intro k
    have h1 := latSkRAlong_comp_equiv hN βs ρ k (Equiv.emptySum (Fin 0) (Fin n)).symm
      (pairFam 0 (emptyMono N) Q)
    have e1 : (pairFam 0 (emptyMono N) Q ∘ (Equiv.emptySum (Fin 0) (Fin n)).symm)
        = fun i => (((F ∘ e) i).1, ((F ∘ e) i).2.translate
            (site (dySpacing N 0) (axisVec 0 (T : ℤ)))) := by
      funext i
      rfl
    rw [e1, latSkRAlong_translate hN βs ρ (F ∘ e) (Nat.zero_le k), latSkRAlong_comp_equiv] at h1
    exact h1.symm
  exact ⟨C, hC0.mono fun k hk => by
    have hk' : |latSkRAlong hN βs ρ k (pairFam 0 (emptyMono N) Q)| ≤ C := hk
    rwa [hQF] at hk'⟩

/-- **The limit exists on every separated family of class test functions**: under E on the class,
`contSAlong` is the `ultra` limit of the lattice readings, not an unspecified value. -/
theorem tendsto_contSAlong_of_diagBoundClass (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N)
    (hR : ρ.ReflCompat 0) {𝒯 : TestClass} (hD : DiagBoundClassAlong hN βs ρ 0 𝒯)
    {ι : Type} [Fintype ι] (F : ι → SField N) {d : ℝ} (hd : 0 < d) (hF : ContinuumSep.FamSep d F)
    (h𝒯 : ∀ i, 𝒯.mem (F i).2) :
    Tendsto (fun k => latSkRAlong hN βs ρ k F) (ultra : Filter ℕ) (𝓝 (contSAlong hN βs ρ F)) := by
  obtain ⟨C, hC⟩ := exists_abs_latSkR_le_of_diagBoundClass hN βs ρ hR hD F hd hF h𝒯
  obtain ⟨x, hx⟩ := exists_tendsto_ultra _ _ hC
  exact tendsto_nhds_limUnder ⟨x, hx⟩

/-- **Bounded readings on separated `C³` families.** Every family whose test functions are `C³` and
pairwise `d`-separated for some `d > 0` has lattice readings eventually bounded along the tower, and
`contSAlong` of it is their `ultra` limit. CHOSEN: `3` the order of differentiability, as in
`PythInvariantSmoothAlong`. -/
def SmoothSepBoundedAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (ρ : Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, ContDiff ℝ 3 (F i).2.1) →
    (∃ d : ℝ, 0 < d ∧ ContinuumSep.FamSep d F) →
      (∃ C : ℝ, ∀ᶠ k in atTop, |latSkRAlong hN βs ρ k F| ≤ C) ∧
        Tendsto (fun k => latSkRAlong hN βs ρ k F) (ultra : Filter ℕ) (𝓝 (contSAlong hN βs ρ F))

end Bounded

end MassGap.ClayTiltedFull

#print axioms MassGap.ClayTiltedFull.contDiff_rotTest
#print axioms MassGap.ClayTiltedFull.rotationOpenSmooth_of_rotationOpen
#print axioms MassGap.ClayTiltedFull.latSkRAlong_translate
#print axioms MassGap.ClayTiltedFull.exists_abs_latSkR_le_of_diagBoundClass
#print axioms MassGap.ClayTiltedFull.tendsto_contSAlong_of_diagBoundClass
