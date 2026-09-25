import Mathlib
import MassGap.PeriodicState
import MassGap.GaugeInvariantAlgebra

/-!
# MassGap.ContinuumField — smeared gauge-invariant fields at lattice spacing `a`

The lattice half of requirement E: lattice observables placed at the sites of `ℤ⁴`, weighted by a
test function on `ℝ⁴` sampled at the scaled sites `a·x`, with the three covariances the continuum
axioms need and a norm bound that does not depend on the spacing.

## Contents

1. `transConf`, `transObs` — translation of `ℤ⁴` by an arbitrary lattice vector, on configurations
   and on observables. `state_transObs`: a state invariant under the unit shift in each of the four
   directions is invariant under every lattice translation (`PeriodicState.periodicState_shift` is
   that hypothesis at the periodic state).
2. `ireflObs_transObs` — the time reflection about the plane `x_τ = 0` (reflection constant `0`)
   conjugates a translation by `x` into the translation by the reflected vector.
   `isIGaugeInvariant_transObs`, `isIGaugeInvariant_ireflObs` — both maps preserve gauge invariance.
3. `LField` — continuous gauge-invariant observables local on a finite set of links; `LField.refl`;
   `LField.sub O r = O - r·1`, the renormalisation subtraction, with `LField.refl_sub`.
4. `TestFn` — bounded real functions on `ℝ⁴` with bounded support (`IsTest f R M`: support in the
   cube `[-R, R]⁴`, `|f| ≤ M`); `TestFn.translate`, `TestFn.reflect`.
5. `smear a F f = ∑ᶠ x : ℤ⁴, (a⁴ · f(a·x)) • (F translated by x)` — the block average of `F`
   weighted by `f` at spacing `a`, a finite sum (`smear_eq_sum`).
   * `norm_smear_le`: `‖smear a F f‖ ≤ ‖F‖ · M · (2R + 3)⁴` at every `0 < a ≤ 1` — uniform in the
     spacing;
   * `smear_translate`: translating `f` by the physical vector `a·n` is translating the smeared field
     by the lattice vector `n`;
   * `ireflObs_smear`: reflecting the smeared field is smearing the reflected observable against the
     reflected test function;
   * `smear_mem_halfSpaceAlg`: a test function supported at times `≥ δ > 0` smears into the
     half-space algebra `halfSpaceAlg τ 0` once `a · D ≤ δ`, `D` the depth of the observable's
     support below its base plane.

## Scope

The weight `a⁴` is the Riemann-sum measure of the lattice cell, and `smear` is the block average of
the lattice observable it is given; field-strength factors and subtractions are data of
`ContinuumSchwinger.Renorm`. The test functions need not be continuous; every statement here holds
on that larger class.
-/

namespace MassGap.ContinuumField

open MassGap MassGap.InfiniteLattice

/-! ## 1. Translations by lattice vectors -/

section Translation

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- A configuration translated by the lattice vector `x`: the value at `l` becomes the old value at
the link with the same direction based at `l.2 + x`.

DERIVED: no numeral; `4` enters through `ISite = Fin 4 → ℤ`, the spacetime dimension. -/
def transConf (x : ISite) (U : IConf G) : IConf G := fun l => U (l.1, l.2 + x)

/-- `transConf x` is continuous: each output coordinate is an input coordinate.

DERIVED: no numeral. -/
theorem continuous_transConf (x : ISite) : Continuous (transConf (G := G) x) :=
  continuous_pi fun l => continuous_apply (l.1, l.2 + x)

/-- Translation of observables by the lattice vector `x`: precomposition with `transConf x`.

DERIVED: no numeral. -/
def transObs (x : ISite) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨transConf x, continuous_transConf x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- DERIVED: no numeral. -/
@[simp] theorem transObs_apply (x : ISite) (F : C(IConf G, ℝ)) (U : IConf G) :
    transObs x F U = F (transConf x U) := rfl

/-- Translation is multiplicative, being precomposition.

DERIVED: no numeral. -/
theorem transObs_mul (x : ISite) (F H : C(IConf G, ℝ)) :
    transObs x (F * H) = transObs x F * transObs x H := rfl

/-- Translation fixes the unit observable.

DERIVED: `1` is the unit observable. -/
theorem transObs_one (x : ISite) : transObs x (1 : C(IConf G, ℝ)) = 1 := rfl

/-- Translation carries a finite product to the product of the translates.

DERIVED: no numeral. -/
theorem transObs_prod {ι : Type*} (x : ISite) (s : Finset ι) (F : ι → C(IConf G, ℝ)) :
    transObs x (∏ i ∈ s, F i) = ∏ i ∈ s, transObs x (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact transObs_one x
  | insert b s hb ih => rw [Finset.prod_insert hb, transObs_mul, ih, Finset.prod_insert hb]

#print axioms transObs_prod

/-- Two translations compose to the translation by the sum.

DERIVED: no numeral. -/
theorem transObs_transObs (x y : ISite) (F : C(IConf G, ℝ)) :
    transObs x (transObs y F) = transObs (x + y) F := by
  ext U
  show F (transConf y (transConf x U)) = F (transConf (x + y) U)
  congr 1
  funext l
  show U (l.1, l.2 + y + x) = U (l.1, l.2 + (x + y))
  rw [add_assoc, add_comm y x]

#print axioms transObs_transObs

/-- Translation by the zero vector is the identity.

DERIVED: `0` is the zero vector. -/
theorem transObs_zero (F : C(IConf G, ℝ)) : transObs 0 F = F := by
  ext U
  show F (transConf 0 U) = F U
  congr 1
  funext l
  show U (l.1, l.2 + 0) = U l
  rw [add_zero]

#print axioms transObs_zero

/-- Translation does not increase the sup norm.

DERIVED: no numeral. -/
theorem norm_transObs_le (x : ISite) (F : C(IConf G, ℝ)) : ‖transObs x F‖ ≤ ‖F‖ :=
  (ContinuousMap.norm_le (transObs x F) (norm_nonneg F)).mpr
    (fun U => F.norm_coe_le_norm (transConf x U))

#print axioms norm_transObs_le

/-- The lattice vector `n` times the unit vector of direction `τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the value off the axis. -/
def axisVec (τ : Fin 4) (n : ℤ) : ISite := fun j => if j = τ then n else 0

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem axisVec_add (τ : Fin 4) (m n : ℤ) : axisVec τ (m + n) = axisVec τ m + axisVec τ n := by
  funext j
  by_cases h : j = τ <;> simp [axisVec, h]

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem axisVec_sub (τ : Fin 4) (m n : ℤ) : axisVec τ (m - n) = axisVec τ m - axisVec τ n := by
  funext j
  by_cases h : j = τ <;> simp [axisVec, h]

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the zero vector and the zero integer.
-/
theorem axisVec_zero (τ : Fin 4) : axisVec τ 0 = 0 := by
  funext j
  by_cases h : j = τ <;> simp [axisVec, h]

/-- The unit shift `ishift τ` is the translation by the unit vector of direction `τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is one lattice step, `ishift`'s own. -/
theorem ishift_eq_add (τ : Fin 4) (y : ISite) : ishift τ y = y + axisVec τ 1 := by
  funext j
  by_cases h : j = τ
  · subst h
    simp [ishift, axisVec]
  · simp [ishift, axisVec, h, Function.update_of_ne h]

#print axioms ishift_eq_add

/-- The unit shift on observables is `transObs` at the unit vector.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is one lattice step. -/
theorem ishiftObsL_eq_transObs (τ : Fin 4) (F : C(IConf G, ℝ)) :
    MassGap.ReflectionShift.ishiftObsL τ F = transObs (axisVec τ 1) F := by
  ext U
  show F (MassGap.InfiniteShift.ishiftConf τ U) = F (transConf (axisVec τ 1) U)
  congr 1
  funext l
  show U (l.1, ishift τ l.2) = U (l.1, l.2 + axisVec τ 1)
  rw [ishift_eq_add]

#print axioms ishiftObsL_eq_transObs

/-- **Invariance under every lattice translation.** A state invariant under the unit shift along
each of the four directions is invariant under `transObs x` for every `x : ℤ⁴`. The set of vectors
under which `ν` is invariant is an additive subgroup; it contains the unit vectors, hence every
`axisVec τ n`, hence every `x = ∑_τ axisVec τ (x τ)`.

DERIVED: `4` is the spacetime dimension; `1` is the unit step; `0` is the zero vector. -/
theorem state_transObs {ν : MassGap.DLRLimit.State (IConf G)}
    (hsh : ∀ (τ : Fin 4) (F : C(IConf G, ℝ)),
      ν (MassGap.ReflectionShift.ishiftObsL τ F) = ν F)
    (x : ISite) (F : C(IConf G, ℝ)) : ν (transObs x F) = ν F := by
  let H : AddSubgroup ISite :=
    { carrier := {z | ∀ F : C(IConf G, ℝ), ν (transObs z F) = ν F}
      add_mem' := by
        intro a b ha hb
        have ha' : ∀ F : C(IConf G, ℝ), ν (transObs a F) = ν F := ha
        have hb' : ∀ F : C(IConf G, ℝ), ν (transObs b F) = ν F := hb
        show ∀ F : C(IConf G, ℝ), ν (transObs (a + b) F) = ν F
        intro F
        rw [← transObs_transObs, ha', hb']
      zero_mem' := by
        show ∀ F : C(IConf G, ℝ), ν (transObs 0 F) = ν F
        intro F
        rw [transObs_zero]
      neg_mem' := by
        intro a ha
        have ha' : ∀ F : C(IConf G, ℝ), ν (transObs a F) = ν F := ha
        show ∀ F : C(IConf G, ℝ), ν (transObs (-a) F) = ν F
        intro F
        have h := ha' (transObs (-a) F)
        rw [transObs_transObs, add_neg_cancel, transObs_zero] at h
        exact h.symm }
  have h1 : ∀ τ : Fin 4, axisVec τ 1 ∈ H := by
    intro τ
    show ∀ F : C(IConf G, ℝ), ν (transObs (axisVec τ 1) F) = ν F
    intro F
    rw [← ishiftObsL_eq_transObs]
    exact hsh τ F
  have hax : ∀ (τ : Fin 4) (n : ℤ), axisVec τ n ∈ H := by
    intro τ n
    refine Int.induction_on n ?_ ?_ ?_
    · rw [axisVec_zero]; exact H.zero_mem
    · intro i hi
      rw [axisVec_add]
      exact H.add_mem hi (h1 τ)
    · intro i hi
      rw [axisVec_sub]
      exact H.sub_mem hi (h1 τ)
  have hdecomp : x = ∑ τ : Fin 4, axisVec τ (x τ) := by
    funext j
    simp [axisVec, Finset.sum_apply]
  have hx : x ∈ H := by
    rw [hdecomp]
    exact H.sum_mem (fun τ _ => hax τ (x τ))
  have hx' : ∀ F : C(IConf G, ℝ), ν (transObs x F) = ν F := hx
  exact hx' F

#print axioms state_transObs

end Translation

/-! ## 2. The time reflection against translations and the gauge action -/

section Reflection

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- `ireflSite τ c (z + x) = ireflSite τ c z + ireflSite τ 0 x`: the reflection is affine, its linear
part being the reflection about `0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant of the linear
part. -/
theorem ireflSite_add (τ : Fin 4) (c : ℤ) (z x : ISite) :
    LatticeReflection.ireflSite τ c (z + x)
      = LatticeReflection.ireflSite τ c z + LatticeReflection.ireflSite τ 0 x := by
  funext j
  by_cases h : j = τ
  · subst h
    simp only [LatticeReflection.ireflSite, Function.update_self, Pi.add_apply]
    ring
  · simp only [LatticeReflection.ireflSite, Pi.add_apply, Function.update_of_ne h]

#print axioms ireflSite_add

/-- The link reflection of a translated link.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant of the linear
part. -/
theorem ireflLink_add (τ : Fin 4) (c : ℤ) (μ : Fin 4) (z x : ISite) :
    LatticeReflection.ireflLink τ c (μ, z + x)
      = ((LatticeReflection.ireflLink τ c (μ, z)).1,
         (LatticeReflection.ireflLink τ c (μ, z)).2 + LatticeReflection.ireflSite τ 0 x) := by
  by_cases h : μ = τ
  · simp only [LatticeReflection.ireflLink, if_pos h, ireflSite_add]
  · simp only [LatticeReflection.ireflLink, if_neg h, ireflSite_add]

#print axioms ireflLink_add

/-- `θ ∘ T_{ρx} = T_x ∘ θ` on configurations, `θ` the reflection about `x_τ = 0` and `ρ` its linear
part.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant. -/
theorem ireflConf_transConf (τ : Fin 4) (x : ISite) (U : IConf G) :
    LatticeReflection.ireflConf τ 0 (transConf (LatticeReflection.ireflSite τ 0 x) U)
      = transConf x (LatticeReflection.ireflConf τ 0 U) := by
  funext l
  obtain ⟨μ, z⟩ := l
  show (if μ = τ then
          (U ((LatticeReflection.ireflLink τ 0 (μ, z)).1,
            (LatticeReflection.ireflLink τ 0 (μ, z)).2 + LatticeReflection.ireflSite τ 0 x))⁻¹
        else U ((LatticeReflection.ireflLink τ 0 (μ, z)).1,
            (LatticeReflection.ireflLink τ 0 (μ, z)).2 + LatticeReflection.ireflSite τ 0 x))
      = (if μ = τ then (U (LatticeReflection.ireflLink τ 0 (μ, z + x)))⁻¹
        else U (LatticeReflection.ireflLink τ 0 (μ, z + x)))
  rw [ireflLink_add]

#print axioms ireflConf_transConf

/-- **The reflection conjugates a translation into the reflected translation**:
`θ (T_x F) = T_{ρx} (θ F)`, `θ = ireflObs τ 0`, `ρ = ireflSite τ 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the reflection constant, the mirror plane
`x_τ = 0`. -/
theorem ireflObs_transObs (τ : Fin 4) (x : ISite) (F : C(IConf G, ℝ)) :
    LatticeReflection.ireflObs τ 0 (transObs x F)
      = transObs (LatticeReflection.ireflSite τ 0 x) (LatticeReflection.ireflObs τ 0 F) := by
  ext U
  show F (transConf x (LatticeReflection.ireflConf τ 0 U))
    = F (LatticeReflection.ireflConf τ 0 (transConf (LatticeReflection.ireflSite τ 0 x) U))
  rw [ireflConf_transConf]

#print axioms ireflObs_transObs

/-- Translation is covariant for the local gauge action.

DERIVED: no numeral. -/
theorem transConf_igaugeTransform (x : ISite) (g : ISite → G) (U : IConf G) :
    transConf x (GaugeInvariantAlgebra.igaugeTransform g U)
      = GaugeInvariantAlgebra.igaugeTransform (fun y => g (y + x)) (transConf x U) := by
  funext l
  show g (l.2 + x) * U (l.1, l.2 + x) * (g (ishift l.1 (l.2 + x)))⁻¹
    = g (l.2 + x) * U (l.1, l.2 + x) * (g (ishift l.1 l.2 + x))⁻¹
  rw [ishift_eq_add, ishift_eq_add, add_right_comm]

#print axioms transConf_igaugeTransform

/-- Translation preserves gauge invariance.

DERIVED: no numeral. -/
theorem isIGaugeInvariant_transObs {F : C(IConf G, ℝ)}
    (hF : GaugeInvariantAlgebra.IsIGaugeInvariant F) (x : ISite) :
    GaugeInvariantAlgebra.IsIGaugeInvariant (transObs x F) := by
  intro g U
  show F (transConf x (GaugeInvariantAlgebra.igaugeTransform g U)) = F (transConf x U)
  rw [transConf_igaugeTransform]
  exact hF _ _

#print axioms isIGaugeInvariant_transObs

/-- The reflected configuration on a `τ`-link.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is the link-length offset of `ireflLink`. -/
theorem ireflConf_apply_axis (τ : Fin 4) (c : ℤ) (V : IConf G) {l : ILink} (h : l.1 = τ) :
    LatticeReflection.ireflConf τ c V l
      = (V (l.1, LatticeReflection.ireflSite τ (c - 1) l.2))⁻¹ := by
  show (if l.1 = τ then (V (LatticeReflection.ireflLink τ c l))⁻¹
      else V (LatticeReflection.ireflLink τ c l)) = _
  rw [if_pos h, LatticeReflection.ireflLink_eq_axis τ c h]

/-- The reflected configuration on a link transverse to `τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem ireflConf_apply_transverse (τ : Fin 4) (c : ℤ) (V : IConf G) {l : ILink}
    (h : l.1 ≠ τ) :
    LatticeReflection.ireflConf τ c V l = V (l.1, LatticeReflection.ireflSite τ c l.2) := by
  show (if l.1 = τ then (V (LatticeReflection.ireflLink τ c l))⁻¹
      else V (LatticeReflection.ireflLink τ c l)) = _
  rw [if_neg h, LatticeReflection.ireflLink_eq_transverse τ c h]

/-- The reflection is covariant for the local gauge action, the gauge function being reflected.

DERIVED: `4` in `Fin 4` is the spacetime dimension. The link-length offset enters in the proof,
through `ireflConf_apply_axis`. -/
theorem ireflConf_igaugeTransform (τ : Fin 4) (c : ℤ) (g : ISite → G) (U : IConf G) :
    LatticeReflection.ireflConf τ c (GaugeInvariantAlgebra.igaugeTransform g U)
      = GaugeInvariantAlgebra.igaugeTransform (fun y => g (LatticeReflection.ireflSite τ c y))
          (LatticeReflection.ireflConf τ c U) := by
  funext l
  by_cases h : l.1 = τ
  · rw [ireflConf_apply_axis τ c (GaugeInvariantAlgebra.igaugeTransform g U) h]
    show (g (LatticeReflection.ireflSite τ (c - 1) l.2)
          * U (l.1, LatticeReflection.ireflSite τ (c - 1) l.2)
          * (g (ishift l.1 (LatticeReflection.ireflSite τ (c - 1) l.2)))⁻¹)⁻¹
        = g (LatticeReflection.ireflSite τ c l.2) * LatticeReflection.ireflConf τ c U l
          * (g (LatticeReflection.ireflSite τ c (ishift l.1 l.2)))⁻¹
    rw [ireflConf_apply_axis τ c U h, h, LatticeReflection.ishift_ireflSite_axis,
      LatticeReflection.ireflSite_ishift_axis]
    group
  · rw [ireflConf_apply_transverse τ c (GaugeInvariantAlgebra.igaugeTransform g U) h]
    show g (LatticeReflection.ireflSite τ c l.2) * U (l.1, LatticeReflection.ireflSite τ c l.2)
          * (g (ishift l.1 (LatticeReflection.ireflSite τ c l.2)))⁻¹
        = g (LatticeReflection.ireflSite τ c l.2) * LatticeReflection.ireflConf τ c U l
          * (g (LatticeReflection.ireflSite τ c (ishift l.1 l.2)))⁻¹
    rw [ireflConf_apply_transverse τ c U h, LatticeReflection.ireflSite_ishift_of_ne h]

#print axioms ireflConf_igaugeTransform

/-- The reflection preserves gauge invariance.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem isIGaugeInvariant_ireflObs {F : C(IConf G, ℝ)}
    (hF : GaugeInvariantAlgebra.IsIGaugeInvariant F) (τ : Fin 4) (c : ℤ) :
    GaugeInvariantAlgebra.IsIGaugeInvariant (LatticeReflection.ireflObs τ c F) := by
  intro g U
  show F (LatticeReflection.ireflConf τ c (GaugeInvariantAlgebra.igaugeTransform g U))
    = F (LatticeReflection.ireflConf τ c U)
  rw [ireflConf_igaugeTransform]
  exact hF _ _

#print axioms isIGaugeInvariant_ireflObs

/-- `ireflObs τ c` is an involution.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem ireflObs_ireflObs (τ : Fin 4) (c : ℤ) (F : C(IConf G, ℝ)) :
    LatticeReflection.ireflObs τ c (LatticeReflection.ireflObs τ c F) = F :=
  (LatticeReflection.latticeReflection (G := G) τ c).θ_involutive F

end Reflection

/-! ## 3. Local gauge-invariant fields -/

section Fields

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- A local gauge-invariant field: a continuous observable of `ℤ⁴`, local on some finite set of
links and invariant under the local gauge group. The plaquette observables
`GaugeInvariantAlgebra.iplaqObs q` are examples.

DERIVED: no numeral. -/
abbrev LField (G : Type) [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G] : Type :=
  {O : C(IConf G, ℝ) //
    (∃ S : Finset ILink, IsLocalOn S (O : IConf G → ℝ))
      ∧ GaugeInvariantAlgebra.IsIGaugeInvariant O}

/-- The reflected field `θ O`, `θ = ireflObs τ 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the body's `0` is the reflection constant. -/
def LField.refl (τ : Fin 4) (O : LField G) : LField G :=
  ⟨LatticeReflection.ireflObs τ 0 O.1,
    ⟨by
      obtain ⟨S, hS⟩ := O.2.1
      exact ⟨S.image (LatticeReflection.ireflLink τ 0),
        HalfSpaceAlgebra.isLocalOn_ireflObs τ 0 hS⟩,
     isIGaugeInvariant_ireflObs O.2.2 τ 0⟩⟩

/-- Subtracting a constant keeps locality.

DERIVED: `1` is the unit observable. -/
theorem isLocalOn_sub_const {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hF : IsLocalOn S (F : IConf G → ℝ)) (r : ℝ) :
    IsLocalOn S ((F - r • (1 : C(IConf G, ℝ)) : C(IConf G, ℝ)) : IConf G → ℝ) := by
  intro U V h
  show F U - r * 1 = F V - r * 1
  rw [hF U V h]

/-- The field `O - r·1`: the renormalisation subtraction of a constant.

DERIVED: `1` is the unit observable. -/
def LField.sub (O : LField G) (r : ℝ) : LField G :=
  ⟨O.1 - r • (1 : C(IConf G, ℝ)),
    ⟨by
      obtain ⟨S, hS⟩ := O.2.1
      exact ⟨S, isLocalOn_sub_const hS r⟩,
     fun g U => by
      show O.1 (GaugeInvariantAlgebra.igaugeTransform g U) - r * 1 = O.1 U - r * 1
      rw [O.2.2 g U]⟩⟩

/-- Reflection commutes with the subtraction of a constant.

DERIVED: `4` in `Fin 4` is the spacetime dimension. The reflection constant and the unit observable
enter through `LField.refl` and `LField.sub`. -/
theorem LField.refl_sub (τ : Fin 4) (O : LField G) (r : ℝ) :
    (O.sub r).refl τ = (O.refl τ).sub r :=
  Subtype.ext (by
    show LatticeReflection.ireflObs τ 0 (O.1 - r • (1 : C(IConf G, ℝ)))
      = LatticeReflection.ireflObs τ 0 O.1 - r • (1 : C(IConf G, ℝ))
    rw [map_sub, map_smul]
    rfl)

/-- `‖F - r·1‖ ≤ ‖F‖ + |r|`.

DERIVED: `1` is the unit observable, of norm at most one. -/
theorem norm_sub_smul_one_le (F : C(IConf G, ℝ)) (r : ℝ) :
    ‖F - r • (1 : C(IConf G, ℝ))‖ ≤ ‖F‖ + |r| := by
  refine (norm_sub_le _ _).trans (add_le_add (le_refl _) ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : ‖(1 : C(IConf G, ℝ))‖ ≤ 1 :=
    (ContinuousMap.norm_le _ zero_le_one).mpr (fun x => by simp)
  calc |r| * ‖(1 : C(IConf G, ℝ))‖ ≤ |r| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg r)
    _ = |r| := mul_one _

/-- A translated observable is local on the translated support.

DERIVED: no numeral. -/
theorem isLocalOn_transObs {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hF : IsLocalOn S (F : IConf G → ℝ)) (x : ISite) :
    IsLocalOn (S.image (fun l : ILink => (l.1, l.2 + x))) (transObs x F : IConf G → ℝ) := by
  intro U V h
  show F (transConf x U) = F (transConf x V)
  refine hF _ _ (fun l hl => ?_)
  show U (l.1, l.2 + x) = V (l.1, l.2 + x)
  exact h _ (Finset.mem_image_of_mem _ hl)

#print axioms isLocalOn_transObs

/-- A translate lies in the half-space algebra of the plane `x_τ = 0` once every translated support
link is at or beyond the plane.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the plane, in `halfSpaceAlg τ 0` and as
the least time coordinate of a translated link. -/
theorem transObs_mem_halfSpaceAlg {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hF : IsLocalOn S (F : IConf G → ℝ)) (τ : Fin 4) (x : ISite)
    (hx : ∀ l ∈ S, 0 ≤ l.2 τ + x τ) :
    transObs x F ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
  refine HalfSpaceAlgebra.mem_halfSpaceAlg.mpr
    ⟨S.image (fun l : ILink => (l.1, l.2 + x)), ?_, isLocalOn_transObs hF x⟩
  intro l hl
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hl)
  show (0 : ℤ) ≤ (m.2 + x) τ
  exact hx m hm

#print axioms transObs_mem_halfSpaceAlg

/-- Every finite link set has a depth `D` below the plane `x_τ = 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. The plane enters as the depth `-(l.2 τ)` of a
link below it. -/
theorem exists_depth (τ : Fin 4) (S : Finset ILink) : ∃ D : ℕ, ∀ l ∈ S, -(l.2 τ) ≤ (D : ℤ) :=
  ⟨S.sup (fun l => (-(l.2 τ)).toNat), fun l hl =>
    le_trans (Int.self_le_toNat _)
      (by exact_mod_cast Finset.le_sup (f := fun l : ILink => (-(l.2 τ)).toNat) hl)⟩

end Fields

/-! ## 4. Test functions on `ℝ⁴` -/

/-- `f` is bounded by `M` and supported in the cube `[-R, R]⁴`.

DERIVED: `4` in `Fin 4 → ℝ` is the spacetime dimension; the body's `0` is the sign of `R` and the
value off the support. -/
def IsTest (f : (Fin 4 → ℝ) → ℝ) (R M : ℝ) : Prop :=
  0 ≤ R ∧ (∀ y, |f y| ≤ M) ∧ ∀ y, f y ≠ 0 → ∀ i, |y i| ≤ R

/-- DERIVED: `4` in `Fin 4 → ℝ` is the spacetime dimension; `0` is the sign of `M`. -/
theorem IsTest.M_nonneg {f : (Fin 4 → ℝ) → ℝ} {R M : ℝ} (h : IsTest f R M) : 0 ≤ M :=
  (abs_nonneg _).trans (h.2.1 0)

/-- Test functions: bounded functions on `ℝ⁴` with bounded support.

DERIVED: `4` is the spacetime dimension. -/
abbrev TestFn : Type := {f : (Fin 4 → ℝ) → ℝ // ∃ R M : ℝ, IsTest f R M}

/-- The scaled site `a·x` of `ℝ⁴`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def site (a : ℝ) (x : ISite) : Fin 4 → ℝ := fun i => a * (x i : ℝ)

/-- DERIVED: no numeral. -/
theorem site_sub (a : ℝ) (x y : ISite) : site a x - site a y = site a (x - y) := by
  funext i
  simp only [site, Pi.sub_apply, Int.cast_sub]
  ring

/-- DERIVED: `0` is the zero vector. -/
theorem site_zero (a : ℝ) : site a 0 = 0 := by
  funext i
  simp [site]

/-- DERIVED: no numeral. -/
theorem site_add (a : ℝ) (x y : ISite) : site a x + site a y = site a (x + y) := by
  funext i
  simp only [site, Pi.add_apply, Int.cast_add]
  ring

/-- DERIVED: no numeral. -/
theorem site_neg (a : ℝ) (x : ISite) : -site a x = site a (-x) := by
  funext i
  simp only [site, Pi.neg_apply, Int.cast_neg]
  ring

/-- The time reflection of `ℝ⁴`, `y_τ ↦ -y_τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def reflR (τ : Fin 4) (y : Fin 4 → ℝ) : Fin 4 → ℝ := Function.update y τ (-y τ)

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem abs_reflR (τ : Fin 4) (y : Fin 4 → ℝ) (i : Fin 4) : |reflR τ y i| = |y i| := by
  by_cases h : i = τ
  · subst h
    simp only [reflR, Function.update_self, abs_neg]
  · simp only [reflR, Function.update_of_ne h]

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem reflR_reflR (τ : Fin 4) (y : Fin 4 → ℝ) : reflR τ (reflR τ y) = y := by
  funext i
  by_cases h : i = τ
  · subst h
    simp only [reflR, Function.update_self, neg_neg]
  · simp only [reflR, Function.update_of_ne h]

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem reflR_sub (τ : Fin 4) (y w : Fin 4 → ℝ) : reflR τ (y - w) = reflR τ y - reflR τ w := by
  funext i
  by_cases h : i = τ
  · subst h
    simp only [reflR, Function.update_self, Pi.sub_apply]
    ring
  · simp only [reflR, Function.update_of_ne h, Pi.sub_apply]

/-- The scaled reflected site is the reflected scaled site.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the lattice reflection constant, the
plane `x_τ = 0`. -/
theorem site_ireflSite (a : ℝ) (τ : Fin 4) (x : ISite) :
    site a (LatticeReflection.ireflSite τ 0 x) = reflR τ (site a x) := by
  funext i
  by_cases h : i = τ
  · subst h
    simp only [site, reflR, LatticeReflection.ireflSite, Function.update_self]
    rw [Int.cast_sub, Int.cast_zero]
    ring
  · simp only [site, reflR, LatticeReflection.ireflSite, Function.update_of_ne h]

/-- The test function translated by `v`: `y ↦ f (y - v)`, supported in `[-(R + ∑|vᵢ|), R + ∑|vᵢ|]⁴`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def TestFn.translate (f : TestFn) (v : Fin 4 → ℝ) : TestFn :=
  ⟨fun y => f.1 (y - v), by
    obtain ⟨R, M, hR, hM, hs⟩ := f.2
    refine ⟨R + ∑ i, |v i|, M, add_nonneg hR (Finset.sum_nonneg fun i _ => abs_nonneg (v i)),
      fun y => hM (y - v), fun y hy i => ?_⟩
    have h1 : |(y - v) i| ≤ R := hs (y - v) hy i
    have h2 : |v i| ≤ ∑ j, |v j| :=
      Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j))
        (Finset.mem_univ i)
    have h3 : y i = (y - v) i + v i := by simp
    rw [h3]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)⟩

/-- The time-reflected test function `y ↦ f (reflR τ y)`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def TestFn.reflect (τ : Fin 4) (f : TestFn) : TestFn :=
  ⟨fun y => f.1 (reflR τ y), by
    obtain ⟨R, M, hR, hM, hs⟩ := f.2
    exact ⟨R, M, hR, fun y => hM _, fun y hy i => by
      rw [← abs_reflR τ y i]; exact hs _ hy i⟩⟩

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem TestFn.translate_translate (f : TestFn) (v w : Fin 4 → ℝ) :
    (f.translate v).translate w = f.translate (v + w) := by
  apply Subtype.ext
  funext y
  show f.1 (y - w - v) = f.1 (y - (v + w))
  rw [sub_sub, add_comm w v]

/-- DERIVED: `0` is the zero vector. -/
theorem TestFn.translate_zero (f : TestFn) : f.translate 0 = f := by
  apply Subtype.ext
  funext y
  show f.1 (y - 0) = f.1 y
  rw [sub_zero]

/-- The reflection of a translate is the translate of the reflection by the reflected vector.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem TestFn.reflect_translate (τ : Fin 4) (f : TestFn) (v : Fin 4 → ℝ) :
    (f.translate v).reflect τ = (f.reflect τ).translate (reflR τ v) := by
  apply Subtype.ext
  funext y
  show f.1 (reflR τ y - v) = f.1 (reflR τ (y - reflR τ v))
  rw [reflR_sub, reflR_reflR]

/-- Positive-time support: `f` vanishes below the time `δ > 0` in direction `τ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the body's `0` is the reflection plane, below
which `f` vanishes by the margin `δ`. -/
def PosTime (τ : Fin 4) (f : TestFn) : Prop := ∃ δ : ℝ, 0 < δ ∧ ∀ y, f.1 y ≠ 0 → δ ≤ y τ

/-- Translating forward in time keeps positive-time support.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of the time component. -/
theorem PosTime.translate {τ : Fin 4} {f : TestFn} (hf : PosTime τ f) {v : Fin 4 → ℝ}
    (hv : 0 ≤ v τ) : PosTime τ (f.translate v) := by
  obtain ⟨δ, hδ, hs⟩ := hf
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h := hs (y - v) hy
  have : (y - v) τ = y τ - v τ := rfl
  rw [this] at h
  linarith

/-! ## 5. Smeared fields -/

section Smear

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- **The smeared field at spacing `a`**: `∑ᶠ x ∈ ℤ⁴, (a⁴ · f(a·x)) • T_x F`. For a test function
the sum is finite (`smear_eq_sum`).

DERIVED: `4` is the spacetime dimension, the exponent of the lattice cell volume `a⁴`. -/
noncomputable def smear (a : ℝ) (F : C(IConf G, ℝ)) (f : TestFn) : C(IConf G, ℝ) :=
  ∑ᶠ x : ISite, (a ^ 4 * f.1 (site a x)) • transObs x F

/-- The lattice box `[-K, K]⁴`.

DERIVED: `4` is the dimension. -/
noncomputable def box (K : ℕ) : Finset ISite := Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(K : ℤ)) (K : ℤ))

/-- DERIVED: `2 K + 1` sites per axis, `4` axes. -/
theorem card_box (K : ℕ) : (box K).card = (2 * K + 1) ^ 4 := by
  unfold box
  rw [Fintype.card_piFinset_const, Int.card_Icc]
  congr 1
  omega

/-- A site where the weight is non-zero lies in the box `[-⌈R/a⌉, ⌈R/a⌉]⁴`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of `a` and the vanishing value.
-/
theorem mem_box_of_ne {a : ℝ} (ha : 0 < a) {f : (Fin 4 → ℝ) → ℝ} {R M : ℝ} (hf : IsTest f R M)
    (x : ISite) (hx : f (site a x) ≠ 0) : x ∈ box ⌈R / a⌉₊ := by
  unfold box
  rw [Fintype.mem_piFinset]
  intro i
  have h1 : |a * (x i : ℝ)| ≤ R := hf.2.2 _ hx i
  rw [abs_mul, abs_of_pos ha] at h1
  have h2 : |(x i : ℝ)| ≤ R / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact h1
  have h3 : |(x i : ℝ)| ≤ (⌈R / a⌉₊ : ℝ) := h2.trans (Nat.le_ceil _)
  have h4 : |x i| ≤ (⌈R / a⌉₊ : ℤ) := by exact_mod_cast h3
  rw [Finset.mem_Icc]
  exact abs_le.mp h4

/-- DERIVED: `0` is the sign of `a`; `4` is the spacetime dimension, the exponent of the cell volume
`a ^ 4`. -/
theorem support_weight_subset {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (f : TestFn)
    {R M : ℝ} (hf : IsTest f.1 R M) :
    Function.support (fun x : ISite => (a ^ 4 * f.1 (site a x)) • transObs x F)
      ⊆ ((box ⌈R / a⌉₊ : Finset ISite) : Set ISite) := by
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  refine mem_box_of_ne ha hf x (fun h0 => hx ?_)
  rw [h0, mul_zero, zero_smul]

/-- DERIVED: `0` is the sign of `a`; `4` is the spacetime dimension, the exponent of the cell volume
`a ^ 4`. -/
theorem hasFiniteSupport_weight {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (f : TestFn) :
    Function.HasFiniteSupport (fun x : ISite => (a ^ 4 * f.1 (site a x)) • transObs x F) := by
  obtain ⟨R, M, hf⟩ := f.2
  exact (box ⌈R / a⌉₊).finite_toSet.subset (support_weight_subset ha F f hf)

/-- The smeared field as a finite sum over any box containing the support.

DERIVED: `0` is the sign of `a`; `4` is the cell-volume exponent. -/
theorem smear_eq_sum {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (f : TestFn) {R M : ℝ}
    (hf : IsTest f.1 R M) {s : Finset ISite} (hs : box ⌈R / a⌉₊ ⊆ s) :
    smear a F f = ∑ x ∈ s, (a ^ 4 * f.1 (site a x)) • transObs x F :=
  finsum_eq_sum_of_support_subset (fun x : ISite => (a ^ 4 * f.1 (site a x)) • transObs x F)
    ((support_weight_subset ha F f hf).trans (Finset.coe_subset.mpr hs))

/-- **The smeared field is bounded uniformly in the spacing**: at every `0 < a ≤ 1`,
`‖smear a F f‖ ≤ ‖F‖ · M · (2R + 3)⁴` for `f` bounded by `M` with support in `[-R, R]⁴`. The box has
`(2⌈R/a⌉ + 1)⁴` sites, each weighted by at most `a⁴ M ‖F‖`, and `a(2⌈R/a⌉ + 1) ≤ 2R + 3a ≤ 2R + 3`.

DERIVED: `0` is the sign of `a`; `4` is the dimension; `2 K + 1` sites per axis; `3` collects
`a(2⌈R/a⌉ + 1) < 2R + 3a` at `a ≤ 1`; `1` bounds the spacing. -/
theorem norm_smear_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (F : C(IConf G, ℝ)) (f : TestFn)
    {R M : ℝ} (hf : IsTest f.1 R M) :
    ‖smear a F f‖ ≤ ‖F‖ * (M * (2 * R + 3) ^ 4) := by
  rw [smear_eq_sum ha F f hf (Finset.Subset.refl _)]
  have hM : 0 ≤ M := hf.M_nonneg
  have h4 : 0 ≤ a ^ 4 := pow_nonneg ha.le 4
  have hterm : ∀ x ∈ box ⌈R / a⌉₊,
      ‖(a ^ 4 * f.1 (site a x)) • transObs x F‖ ≤ a ^ 4 * M * ‖F‖ := by
    intro x _
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg h4]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hf.2.1 _) h4) (norm_transObs_le x F)
      (norm_nonneg _) (mul_nonneg h4 hM)
  have hsum := (norm_sum_le (box ⌈R / a⌉₊)
    (fun x => (a ^ 4 * f.1 (site a x)) • transObs x F)).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, nsmul_eq_mul, card_box] at hsum
  have hK : (⌈R / a⌉₊ : ℝ) < R / a + 1 := Nat.ceil_lt_add_one (div_nonneg hf.1 ha.le)
  have hK2 : ((⌈R / a⌉₊ : ℝ) - 1) * a < R := by
    have h1 : (⌈R / a⌉₊ : ℝ) - 1 < R / a := by linarith
    exact (lt_div_iff₀ ha).mp h1
  have hlin : a * (2 * (⌈R / a⌉₊ : ℝ) + 1) ≤ 2 * R + 3 := by nlinarith
  have hpow : (a * (2 * (⌈R / a⌉₊ : ℝ) + 1)) ^ 4 ≤ (2 * R + 3) ^ 4 :=
    pow_le_pow_left₀ (mul_nonneg ha.le (by positivity)) hlin 4
  calc ‖∑ x ∈ box ⌈R / a⌉₊, (a ^ 4 * f.1 (site a x)) • transObs x F‖
      ≤ (((2 * ⌈R / a⌉₊ + 1) ^ 4 : ℕ) : ℝ) * (a ^ 4 * M * ‖F‖) := hsum
    _ = (a * (2 * (⌈R / a⌉₊ : ℝ) + 1)) ^ 4 * (M * ‖F‖) := by push_cast; ring
    _ ≤ (2 * R + 3) ^ 4 * (M * ‖F‖) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hM (norm_nonneg F))
    _ = ‖F‖ * (M * (2 * R + 3) ^ 4) := by ring

#print axioms norm_smear_le

/-- **Translation covariance**: smearing against `f` translated by the physical vector `a·n` is
translating the smeared field by the lattice vector `n`.

DERIVED: `0` is the sign of `a`. -/
theorem smear_translate {a : ℝ} (ha : 0 < a) (F : C(IConf G, ℝ)) (f : TestFn) (n : ISite) :
    smear a F (f.translate (site a n)) = transObs n (smear a F f) := by
  have hL : smear a F (f.translate (site a n))
      = ∑ᶠ y : ISite, (a ^ 4 * (f.translate (site a n)).1 (site a (y + n)))
          • transObs (y + n) F :=
    (finsum_comp_equiv (Equiv.addRight n)
      (f := fun x : ISite => (a ^ 4 * (f.translate (site a n)).1 (site a x)) • transObs x F)).symm
  have hR : transObs n (smear a F f)
      = ∑ᶠ y : ISite, transObs n ((a ^ 4 * f.1 (site a y)) • transObs y F) :=
    map_finsum (transObs n) (hasFiniteSupport_weight ha F f)
  rw [hL, hR]
  refine finsum_congr (fun y => ?_)
  rw [map_smul, transObs_transObs]
  have hs : (f.translate (site a n)).1 (site a (y + n)) = f.1 (site a y) := by
    show f.1 (site a (y + n) - site a n) = f.1 (site a y)
    rw [site_sub, add_sub_cancel_right]
  rw [hs, add_comm n y]

#print axioms smear_translate

/-- The reflection of `ℤ⁴` as a permutation.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the body's `0` is the reflection constant. -/
def reflSitePerm (τ : Fin 4) : Equiv.Perm ISite :=
  (LatticeReflection.ireflSite_involutive τ 0).toPerm _

/-- **Reflection covariance**: `θ (smear a F f) = smear a (θ F) (f reflected)`, `θ = ireflObs τ 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the sign of `a` and the reflection
constant, the plane `x_τ = 0`. -/
theorem ireflObs_smear {a : ℝ} (ha : 0 < a) (τ : Fin 4) (F : C(IConf G, ℝ)) (f : TestFn) :
    LatticeReflection.ireflObs τ 0 (smear a F f)
      = smear a (LatticeReflection.ireflObs τ 0 F) (f.reflect τ) := by
  have hL : LatticeReflection.ireflObs τ 0 (smear a F f)
      = ∑ᶠ x : ISite, LatticeReflection.ireflObs τ 0 ((a ^ 4 * f.1 (site a x)) • transObs x F) :=
    map_finsum (LatticeReflection.ireflObs τ 0) (hasFiniteSupport_weight ha F f)
  have hR : smear a (LatticeReflection.ireflObs τ 0 F) (f.reflect τ)
      = ∑ᶠ x : ISite, (a ^ 4 * (f.reflect τ).1 (site a (reflSitePerm τ x)))
          • transObs (reflSitePerm τ x) (LatticeReflection.ireflObs τ 0 F) :=
    (finsum_comp_equiv (reflSitePerm τ)
      (f := fun x : ISite => (a ^ 4 * (f.reflect τ).1 (site a x))
        • transObs x (LatticeReflection.ireflObs τ 0 F))).symm
  rw [hL, hR]
  refine finsum_congr (fun x => ?_)
  rw [map_smul, ireflObs_transObs]
  have he : reflSitePerm τ x = LatticeReflection.ireflSite τ 0 x := rfl
  have hc : (f.reflect τ).1 (site a (reflSitePerm τ x)) = f.1 (site a x) := by
    show f.1 (reflR τ (site a (reflSitePerm τ x))) = f.1 (site a x)
    rw [he, site_ireflSite, reflR_reflR]
  rw [hc, he]

#print axioms ireflObs_smear

/-- **Positive-time smeared fields lie in the half-space algebra.** If `F` is local on `S` of depth
`D` below `x_τ = 0` and `f` vanishes below the time `δ`, then at every spacing with `a·D ≤ δ` the
smeared field is in `halfSpaceAlg τ 0`.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the plane and the sign of `a`. -/
theorem smear_mem_halfSpaceAlg {a : ℝ} (ha : 0 < a) (τ : Fin 4) {F : C(IConf G, ℝ)}
    {S : Finset ILink} (hS : IsLocalOn S (F : IConf G → ℝ)) {D : ℕ}
    (hD : ∀ l ∈ S, -(l.2 τ) ≤ (D : ℤ)) {δ : ℝ} (haD : a * D ≤ δ) (f : TestFn)
    (hδ : ∀ y, f.1 y ≠ 0 → δ ≤ y τ) :
    smear a F f ∈ HalfSpaceAlgebra.halfSpaceAlg (G := G) τ 0 := by
  obtain ⟨R, M, hf⟩ := f.2
  rw [smear_eq_sum ha F f hf (Finset.Subset.refl _)]
  refine Submodule.sum_mem _ (fun x _ => ?_)
  by_cases h0 : f.1 (site a x) = 0
  · rw [h0, mul_zero, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (transObs_mem_halfSpaceAlg hS τ x ?_)
    intro l hl
    have h1 : δ ≤ a * (x τ : ℝ) := hδ _ h0
    have h2 : (D : ℝ) ≤ (x τ : ℝ) := by
      by_contra hlt
      push_neg at hlt
      have := mul_lt_mul_of_pos_left hlt ha
      linarith
    have h3 : (D : ℤ) ≤ x τ := by exact_mod_cast h2
    have h4 := hD l hl
    omega

#print axioms smear_mem_halfSpaceAlg

end Smear

end MassGap.ContinuumField
