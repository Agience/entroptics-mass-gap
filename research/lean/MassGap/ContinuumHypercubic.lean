import Mathlib
import MassGap.ContinuumSep
import MassGap.WilsonHypercubic
import MassGap.SUN

noncomputable section

/-!
# MassGap.ContinuumHypercubic — the hypercubic group, continuity in the test functions, and what
rotation invariance leaves open

## 1. Axis permutations on `ℤ⁴`

`iaxisSite e x = x ∘ e.symm` relabels the directions of a site by `e : Equiv.Perm (Fin 4)`;
`iaxisLink`, `iaxisConf`, `iaxisObs` carry it to links, configurations and observables.
`pullback_iaxisConf`: on a periodic configuration it is the pullback of
`WilsonHypercubic.axisLink e`, the link permutation of the Wilson system's `axisSymmetry`.
`torusState_axis`: every periodic Wilson state is invariant (from `SUN.su_expect_invariant`);
`periodicState_axis`: so is their ultrafilter limit `PeriodicState.periodicState`. Together with
`PeriodicState.periodicState_reflInvariant` the periodic state is invariant under the hypercubic
group `W(B₄)` of `ℤ⁴`: axis permutations and axis reflections.

## 2. The hypercubic group on the Schwinger functions

`lfieldAxis e` acts on local gauge-invariant fields (locality `isLocalOn_iaxisObs`, gauge invariance
`isIGaugeInvariant_iaxisObs`), `testPermute e f = f ∘ permR e` with `permR e y = y ∘ e` on test
functions, and `iaxisObs_smear`: `iaxisObs e (smear a F f) = smear a (iaxisObs e F) (f ∘ permR e)`.
`contS_axis`: `contS` is invariant under `sfieldAxis e` at axis-compatible data (`axisCompat`).
With `ContinuumSchwinger.contS_reflect`, `contS_hyp` gives invariance under every word in the
generators, whose action on test functions is `f ↦ f ∘ hypR w`; `hypR_signed` shows `hypR w` is a
signed permutation of the coordinates and `exists_word_signed` that every signed permutation is
one. `contS_signed`: for fields fixed by the lattice hypercubic group (`HypScalar`), composing every
test function with any signed permutation `y ↦ (sᵢ y_{σ i})ᵢ` of `ℝ⁴` leaves `contS` unchanged.

## 3. Continuity in the test functions, and all of `ℝ⁴`

`SupContinuousSep hN ρ` (stated): `contS` is continuous in the sup norm of the test functions on
`d`-separated families supported in a common cube. `LatticeEquicontSep hN ρ` (stated): the same,
eventually in the step, for the lattice functions `latSkR`. `supContinuousSep_of_equicont`: under
`ContinuumSep.UniformBoundSep` the second gives the first. `latticeEquicontSep_of_bounded`: at bounded
renormalisation data the lattice functions are Lipschitz in the sup norm (`norm_smear_sub_le`,
`norm_prod_sub_prod_le`, `abs_latS_sub_le`), so both hold there (`supContinuousSep_of_bounded`).

`contS_translate_real`: under `SupContinuousSep`, `contS_translate` extends from the dyadic subgroup
to every `v ∈ ℝ⁴`, for separated families of uniformly continuous test functions: the dyadic
vectors are dense (`exists_dyadic_of_eventually`) and a uniformly continuous test function moves
little in the sup norm under a small translation.

At a growing field-strength factor `Z` the lattice Lipschitz bound carries `∏ Z`, so
`UniformBoundSep` does not give `LatticeEquicontSep`: the bound of `UniformBoundSep` is per family,
not uniform over the test functions of a sup-norm ball.

## 4. Rotations

`RotationInvariantSep hN ρ Φ` (stated) is `ContinuumSchwinger.RotationInvariant` restricted to
separated families with uniformly continuous test functions; `rotationInvariantSep_of_rotationInvariant`
shows it is weaker. `rotation_hypercubic` proves its conclusion for every matrix acting as a signed
permutation, at `HypScalar` fields. What is open is the conclusion for the rotations of `SO(4)` that
are not signed permutations: the restoration of rotation symmetry in the limit.

The restriction to uniformly continuous test functions is needed. `TestFn` admits bounded
discontinuous functions, on which the lattice Riemann sums need not converge to the integral: at bare
data the unit field `1` gives `contS [(1, f)] = lim aₖ⁴ ∑ₓ f(aₖ x)`, which for the indicator `f` of
the points of `[0, 1]⁴` with coordinates in `aRun N 1 · ℤ[1/2]` is `1`, and for `f ∘ Rot`, `Rot` the
rotation by `(3/5, 4/5)` in the first two coordinates, is `1/5` (a lattice point is counted iff
`x₁ ≡ 3 x₂ mod 5`). That computation is not formalised here.

## Scope

`SupContinuousSep`, `LatticeEquicontSep` and `RotationInvariantSep` are stated; the first two are
proved at bounded renormalisation data, where the limit is degenerate. The hypercubic invariance is
proved at every renormalisation datum compatible with the lattice symmetries.
-/

namespace MassGap.ContinuumHypercubic

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger Filter
open scoped Topology

/-! ## 1. Axis permutations of `ℤ⁴` -/

section Axis

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- The site with its directions relabelled by `e`: the coordinate in direction `e μ` is the old
coordinate in direction `μ`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def iaxisSite (e : Equiv.Perm (Fin 4)) (x : ISite) : ISite := fun j => x (e.symm j)

/-- `iaxisSite e` as a permutation of `ℤ⁴`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def iaxisSitePerm (e : Equiv.Perm (Fin 4)) : Equiv.Perm ISite where
  toFun := iaxisSite e
  invFun := iaxisSite e.symm
  left_inv x := by
    funext j
    simp [iaxisSite]
  right_inv x := by
    funext j
    simp [iaxisSite]

/-- The link with its direction and base site relabelled by `e`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def iaxisLink (e : Equiv.Perm (Fin 4)) (l : ILink) : ILink := (e l.1, iaxisSite e l.2)

/-- The configuration read through the relabelling: its value at `l` is the old value at
`iaxisLink e l`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def iaxisConf (e : Equiv.Perm (Fin 4)) (U : IConf G) : IConf G := fun l => U (iaxisLink e l)

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem continuous_iaxisConf (e : Equiv.Perm (Fin 4)) : Continuous (iaxisConf (G := G) e) :=
  continuous_pi fun l => continuous_apply (iaxisLink e l)

#print axioms continuous_iaxisConf

/-- The relabelling on observables: precomposition with `iaxisConf e`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def iaxisObs (e : Equiv.Perm (Fin 4)) : C(IConf G, ℝ) →ₗ[ℝ] C(IConf G, ℝ) where
  toFun F := F.comp ⟨iaxisConf e, continuous_iaxisConf e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem iaxisObs_mul (e : Equiv.Perm (Fin 4)) (F H : C(IConf G, ℝ)) :
    iaxisObs e (F * H) = iaxisObs e F * iaxisObs e H := rfl

#print axioms iaxisObs_mul

/-- DERIVED: `1` is the unit observable; `4` in `Fin 4` is the spacetime dimension. -/
theorem iaxisObs_one (e : Equiv.Perm (Fin 4)) : iaxisObs e (1 : C(IConf G, ℝ)) = 1 := rfl

#print axioms iaxisObs_one

/-- The relabelling carries a finite product to the product of the relabelled factors.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem iaxisObs_prod {ι : Type*} (e : Equiv.Perm (Fin 4)) (s : Finset ι)
    (F : ι → C(IConf G, ℝ)) : iaxisObs e (∏ i ∈ s, F i) = ∏ i ∈ s, iaxisObs e (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact iaxisObs_one e
  | insert b s hb ih => rw [Finset.prod_insert hb, iaxisObs_mul, ih, Finset.prod_insert hb]

#print axioms iaxisObs_prod

/-- The unit shift commutes with the relabelling: `ishift (e μ) (iaxisSite e x) =
iaxisSite e (ishift μ x)`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem ishift_iaxisSite (e : Equiv.Perm (Fin 4)) (μ : Fin 4) (x : ISite) :
    ishift (e μ) (iaxisSite e x) = iaxisSite e (ishift μ x) := by
  funext j
  by_cases h : j = e μ
  · subst h
    simp [ishift, iaxisSite]
  · have h' : e.symm j ≠ μ := fun hc => h (by rw [← hc, Equiv.apply_symm_apply])
    simp only [ishift, iaxisSite, Function.update_of_ne h, Function.update_of_ne h']

#print axioms ishift_iaxisSite

/-- The relabelling is additive on sites.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem iaxisSite_add (e : Equiv.Perm (Fin 4)) (x y : ISite) :
    iaxisSite e (x + y) = iaxisSite e x + iaxisSite e y := by
  funext j
  simp only [iaxisSite, Pi.add_apply]

#print axioms iaxisSite_add

/-- The relabelling is covariant for the local gauge action, the gauge function being relabelled.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem iaxisConf_igaugeTransform (e : Equiv.Perm (Fin 4)) (g : ISite → G) (U : IConf G) :
    iaxisConf e (GaugeInvariantAlgebra.igaugeTransform g U)
      = GaugeInvariantAlgebra.igaugeTransform (fun y => g (iaxisSite e y)) (iaxisConf e U) := by
  funext l
  show g (iaxisSite e l.2) * U (e l.1, iaxisSite e l.2) * (g (ishift (e l.1) (iaxisSite e l.2)))⁻¹
    = g (iaxisSite e l.2) * U (e l.1, iaxisSite e l.2) * (g (iaxisSite e (ishift l.1 l.2)))⁻¹
  rw [ishift_iaxisSite]

#print axioms iaxisConf_igaugeTransform

/-- The relabelling preserves gauge invariance.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem isIGaugeInvariant_iaxisObs {F : C(IConf G, ℝ)}
    (hF : GaugeInvariantAlgebra.IsIGaugeInvariant F) (e : Equiv.Perm (Fin 4)) :
    GaugeInvariantAlgebra.IsIGaugeInvariant (iaxisObs e F) := by
  intro g U
  show F (iaxisConf e (GaugeInvariantAlgebra.igaugeTransform g U)) = F (iaxisConf e U)
  rw [iaxisConf_igaugeTransform]
  exact hF _ _

#print axioms isIGaugeInvariant_iaxisObs

/-- A relabelled observable is local on the relabelled support.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem isLocalOn_iaxisObs (e : Equiv.Perm (Fin 4)) {S : Finset ILink} {F : C(IConf G, ℝ)}
    (hF : IsLocalOn S (F : IConf G → ℝ)) :
    IsLocalOn (S.image (iaxisLink e)) (iaxisObs e F : IConf G → ℝ) := by
  intro U V h
  show F (iaxisConf e U) = F (iaxisConf e V)
  refine hF _ _ (fun l hl => ?_)
  show U (iaxisLink e l) = V (iaxisLink e l)
  exact h _ (Finset.mem_image_of_mem _ hl)

#print axioms isLocalOn_iaxisObs

/-- `iaxisConf e ∘ transConf (iaxisSite e x) = transConf x ∘ iaxisConf e`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem iaxisConf_transConf (e : Equiv.Perm (Fin 4)) (x : ISite) (U : IConf G) :
    iaxisConf e (transConf (iaxisSite e x) U) = transConf x (iaxisConf e U) := by
  funext l
  show U (e l.1, iaxisSite e l.2 + iaxisSite e x) = U (e l.1, iaxisSite e (l.2 + x))
  rw [iaxisSite_add]

#print axioms iaxisConf_transConf

/-- **The relabelling conjugates a translation into the relabelled translation**:
`iaxisObs e (transObs x F) = transObs (iaxisSite e x) (iaxisObs e F)`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem iaxisObs_transObs (e : Equiv.Perm (Fin 4)) (x : ISite) (F : C(IConf G, ℝ)) :
    iaxisObs e (transObs x F) = transObs (iaxisSite e x) (iaxisObs e F) := by
  ext U
  show F (transConf x (iaxisConf e U)) = F (iaxisConf e (transConf (iaxisSite e x) U))
  rw [iaxisConf_transConf]

#print axioms iaxisObs_transObs

end Axis

/-! ## 2. The periodic Wilson states are invariant under the axis permutations -/

section Periodic

variable {N : ℕ}

/-- Reducing a relabelled link modulo the extent is relabelling the reduced link with the periodic
`WilsonHypercubic.axisLink e`.

DERIVED: `4` is the spacetime dimension; the `1` in `M + 1` is `finMod`'s successor writing the
extent. -/
theorem linkMod_iaxisLink (M : ℕ) (e : Equiv.Perm (Fin 4)) (l : ILink) :
    linkMod M (iaxisLink e l) = WilsonHypercubic.axisLink (n := M + 1) e (linkMod M l) :=
  Prod.ext rfl (funext fun _ => rfl)

#print axioms linkMod_iaxisLink

/-- **The periodic pullback intertwines the relabellings**: relabelling a pulled-back configuration
on `ℤ⁴` is pulling back the configuration reindexed by the link permutation of
`WilsonHypercubic.axisSymmetry N e`.

DERIVED: `4` is the spacetime dimension; the `1` in `M + 1` is `finMod`'s successor. -/
theorem pullback_iaxisConf (M : ℕ) (e : Equiv.Perm (Fin 4))
    (W : WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) :
    iaxisConf e (pullback M W)
      = pullback M (MassGap.LatticeGauge.Symmetry.reindex
          (MassGap.WilsonHypercubic.axisSymmetry (d := 4) (n := M + 1) N e).onLink W) := by
  funext l
  show W (linkMod M (iaxisLink e l)) = W (WilsonHypercubic.axisLink (n := M + 1) e (linkMod M l))
  rw [linkMod_iaxisLink]

#print axioms pullback_iaxisConf

/-- **Every periodic Wilson state is invariant under the axis permutations**:
`torusState hN M β (iaxisObs e f) = torusState hN M β f` at every extent, coupling and `e`.
`pullback_iaxisConf` and `SUN.su_expect_invariant` at `WilsonHypercubic.axisSymmetry N e`.

DERIVED: `4` is the spacetime dimension; the `1` in `M + 1` is `finMod`'s successor; `0` is the
excluded rank in `hN`. -/
theorem torusState_axis (hN : N ≠ 0) (M : ℕ) (β : ℝ) (e : Equiv.Perm (Fin 4))
    (f : C(IConf (MassGap.SUN.SU N), ℝ)) :
    PeriodicState.torusState hN M β (iaxisObs e f) = PeriodicState.torusState hN M β f := by
  have hobs : PeriodicState.torusObs M (iaxisObs e f)
      = fun W => PeriodicState.torusObs M f (MassGap.LatticeGauge.Symmetry.reindex
          (MassGap.WilsonHypercubic.axisSymmetry (d := 4) (n := M + 1) N e).onLink W) := by
    funext W
    show f (iaxisConf e (pullback M W)) = f (pullback M (MassGap.LatticeGauge.Symmetry.reindex
          (MassGap.WilsonHypercubic.axisSymmetry (d := 4) (n := M + 1) N e).onLink W))
    rw [pullback_iaxisConf]
  show MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β
      (PeriodicState.torusObs M (iaxisObs e f))
    = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (PeriodicState.torusObs M f)
  rw [hobs]
  exact MassGap.SUN.su_expect_invariant
    (MassGap.WilsonHypercubic.axisSymmetry (d := 4) (n := M + 1) N e) β
    (PeriodicState.torusObs M f)

#print axioms torusState_axis

/-- **The periodic infinite-volume state is invariant under the axis permutations.** Each
`torusState hN (2k + 1) β` is (`torusState_axis`), so the two sequences agree and share their limit
along `periodicUltra hN β`.

DERIVED: the extent index `2k + 1` is `periodicState`'s family; `4` is the spacetime dimension; `0`
is the excluded rank in `hN`. -/
theorem periodicState_axis (hN : N ≠ 0) (β : ℝ) (e : Equiv.Perm (Fin 4))
    (f : C(IConf (MassGap.SUN.SU N), ℝ)) :
    PeriodicState.periodicState hN β (iaxisObs e f) = PeriodicState.periodicState hN β f := by
  haveI : ((PeriodicState.periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot :=
    (PeriodicState.periodicUltra hN β).neBot'
  refine tendsto_nhds_unique (PeriodicState.tendsto_periodicState hN β (iaxisObs e f)) ?_
  exact (PeriodicState.tendsto_periodicState hN β f).congr
    (fun k => (torusState_axis hN (2 * k + 1) β e f).symm)

#print axioms periodicState_axis

/-- The state of step `k` is invariant under the axis permutations.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem stateK_axis (hN : N ≠ 0) (k : ℕ) (e : Equiv.Perm (Fin 4)) (F : C(Cfg N, ℝ)) :
    stateK hN k (iaxisObs e F) = stateK hN k F :=
  periodicState_axis hN _ e F

#print axioms stateK_axis

end Periodic

/-! ## 3. The relabelling on fields, test functions and smeared fields -/

section Smear

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- The relabelled field `iaxisObs e O`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def lfieldAxis (e : Equiv.Perm (Fin 4)) (O : LField G) : LField G :=
  ⟨iaxisObs e O.1,
    ⟨by
      obtain ⟨S, hS⟩ := O.2.1
      exact ⟨S.image (iaxisLink e), isLocalOn_iaxisObs e hS⟩,
     isIGaugeInvariant_iaxisObs O.2.2 e⟩⟩

/-- The relabelling commutes with the subtraction of a constant.

DERIVED: `4` in `Fin 4` is the spacetime dimension. The unit observable enters through `LField.sub`.
-/
theorem lfieldAxis_sub (e : Equiv.Perm (Fin 4)) (O : LField G) (r : ℝ) :
    lfieldAxis e (O.sub r) = (lfieldAxis e O).sub r :=
  Subtype.ext (by
    show iaxisObs e (O.1 - r • (1 : C(IConf G, ℝ))) = iaxisObs e O.1 - r • (1 : C(IConf G, ℝ))
    rw [map_sub, map_smul, iaxisObs_one])

#print axioms lfieldAxis_sub

/-- The relabelling of `ℝ⁴` read by test functions: `(permR e y)_i = y_{e i}`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def permR (e : Equiv.Perm (Fin 4)) (y : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => y (e i)

/-- The test function `y ↦ f (permR e y)`, with the same support radius and bound.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def testPermute (e : Equiv.Perm (Fin 4)) (f : TestFn) : TestFn :=
  ⟨fun y => f.1 (permR e y), by
    obtain ⟨R, M, hR, hM, hs⟩ := f.2
    refine ⟨R, M, hR, fun y => hM _, fun y hy i => ?_⟩
    have h : |y (e (e.symm i))| ≤ R := hs (permR e y) hy (e.symm i)
    rwa [Equiv.apply_symm_apply] at h⟩

/-- The scaled relabelled site, read through `permR e`, is the scaled site.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem permR_site_iaxisSite (e : Equiv.Perm (Fin 4)) (a : ℝ) (x : ISite) :
    permR e (site a (iaxisSite e x)) = site a x := by
  funext i
  show a * ((x (e.symm (e i)) : ℤ) : ℝ) = a * ((x i : ℤ) : ℝ)
  rw [Equiv.symm_apply_apply]

#print axioms permR_site_iaxisSite

/-- **Relabelling covariance of the smeared field**:
`iaxisObs e (smear a F f) = smear a (iaxisObs e F) (testPermute e f)`.

DERIVED: `0` is the sign of `a`; `4` in `Fin 4` is the spacetime dimension; the cell-volume exponent
`4` enters through `smear`. -/
theorem iaxisObs_smear {a : ℝ} (ha : 0 < a) (e : Equiv.Perm (Fin 4)) (F : C(IConf G, ℝ))
    (f : TestFn) : iaxisObs e (smear a F f) = smear a (iaxisObs e F) (testPermute e f) := by
  have hL : iaxisObs e (smear a F f)
      = ∑ᶠ x : ISite, iaxisObs e ((a ^ 4 * f.1 (site a x)) • transObs x F) :=
    map_finsum (iaxisObs e) (hasFiniteSupport_weight ha F f)
  have hR : smear a (iaxisObs e F) (testPermute e f)
      = ∑ᶠ x : ISite, (a ^ 4 * (testPermute e f).1 (site a (iaxisSitePerm e x)))
          • transObs (iaxisSitePerm e x) (iaxisObs e F) :=
    (finsum_comp_equiv (iaxisSitePerm e)
      (f := fun x : ISite => (a ^ 4 * (testPermute e f).1 (site a x))
        • transObs x (iaxisObs e F))).symm
  rw [hL, hR]
  refine finsum_congr (fun x => ?_)
  rw [map_smul, iaxisObs_transObs]
  have he : iaxisSitePerm e x = iaxisSite e x := rfl
  have hc : (testPermute e f).1 (site a (iaxisSitePerm e x)) = f.1 (site a x) := by
    show f.1 (permR e (site a (iaxisSitePerm e x))) = f.1 (site a x)
    rw [he, permR_site_iaxisSite]
  rw [hc, he]

#print axioms iaxisObs_smear

end Smear

/-! ## 4. The hypercubic group on the Schwinger functions -/

section Schwinger

variable {N : ℕ}

/-- The relabelled smeared-field datum.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def sfieldAxis (e : Equiv.Perm (Fin 4)) (p : SField N) : SField N :=
  (lfieldAxis e p.1, testPermute e p.2)

/-- **Lattice relabelling invariance**: in a state invariant under `iaxisObs e`, relabelling every
field and every test function leaves the lattice Schwinger function unchanged.

DERIVED: `0` is the sign of `a`; `4` in `Fin 4` is the spacetime dimension. -/
theorem latS_axis (ν : MassGap.DLRLimit.State (Cfg N)) (e : Equiv.Perm (Fin 4))
    (hinv : ∀ F : C(Cfg N, ℝ), ν (iaxisObs e F) = ν F) {a : ℝ} (ha : 0 < a) {ι : Type}
    [Fintype ι] (F : ι → SField N) :
    latS ν a (fun i => sfieldAxis e (F i)) = latS ν a F := by
  have h1 : (∏ i, smear a (sfieldAxis e (F i)).1.1 (sfieldAxis e (F i)).2)
      = iaxisObs e (∏ i, smear a (F i).1.1 (F i).2) := by
    rw [iaxisObs_prod]
    exact Finset.prod_congr rfl (fun i _ => (iaxisObs_smear ha e (F i).1.1 (F i).2).symm)
  show ν (∏ i, smear a (sfieldAxis e (F i)).1.1 (sfieldAxis e (F i)).2)
    = ν (∏ i, smear a (F i).1.1 (F i).2)
  rw [h1]
  exact hinv _

#print axioms latS_axis

/-- The renormalisation data do not see the relabelling `e`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def axisCompat (ρ : Renorm N) (e : Equiv.Perm (Fin 4)) : Prop :=
  ∀ (k : ℕ) (O : LField (MassGap.SUN.SU N)),
    ρ.Z k (lfieldAxis e O) = ρ.Z k O ∧ ρ.c k (lfieldAxis e O) = ρ.c k O

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem bare_axisCompat (e : Equiv.Perm (Fin 4)) : axisCompat (Renorm.bare N) e :=
  fun _ _ => ⟨rfl, rfl⟩

#print axioms bare_axisCompat

/-- The subtraction `ν_k(O)` of the connected composites is relabelling compatible because the
periodic state is relabelling invariant (`stateK_axis`).

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem connected_axisCompat (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (e : Equiv.Perm (Fin 4)) (hZ : ∀ k O, Z k (lfieldAxis e O) = Z k O) :
    axisCompat (Renorm.connected hN Z) e :=
  fun k O => ⟨hZ k O, stateK_axis hN k e O.1⟩

#print axioms connected_axisCompat

/-- **OS1, the axis permutations**: relabelling every field and every test function by `e`
(`f ↦ f ∘ permR e`) leaves the continuum Schwinger function unchanged, at axis-compatible data. The
identity equates `limUnder` values of sequences that agree term by term, and needs no bound.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem contS_axis (hN : N ≠ 0) (ρ : Renorm N) (e : Equiv.Perm (Fin 4)) (hR : axisCompat ρ e)
    {ι : Type} [Fintype ι] (F : ι → SField N) :
    contS hN ρ (fun i => sfieldAxis e (F i)) = contS hN ρ F := by
  unfold contS
  congr 1
  funext k
  have hpref : ρ.pref k (fun i => sfieldAxis e (F i)) = ρ.pref k F :=
    Finset.prod_congr rfl (fun i _ => (hR k (F i).1).1)
  have hfam : (fun i => ρ.field k (sfieldAxis e (F i)))
      = fun i => sfieldAxis e (ρ.field k (F i)) := by
    funext i
    show ((lfieldAxis e (F i).1).sub (ρ.c k (lfieldAxis e (F i).1)), testPermute e (F i).2)
      = (lfieldAxis e ((F i).1.sub (ρ.c k (F i).1)), testPermute e (F i).2)
    rw [(hR k (F i).1).2, lfieldAxis_sub]
  show ρ.pref k (fun i => sfieldAxis e (F i)) * latSk hN k (fun i => ρ.field k (sfieldAxis e (F i)))
    = ρ.pref k F * latSk hN k (fun i => ρ.field k (F i))
  rw [hpref, hfam, latSk_eq, latSk_eq,
    latS_axis (stateK hN k) e (stateK_axis hN k e) (dySpacing_pos (one_le_of_ne_zero hN) k)
      (fun i => ρ.field k (F i))]

#print axioms contS_axis

/-- The generators of the hypercubic group: an axis permutation (`Sum.inl e`) or the reflection of
one axis (`Sum.inr τ`).

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the excluded colour count. -/
def genField : (Equiv.Perm (Fin 4) ⊕ Fin 4) → SField N → SField N
  | Sum.inl e => sfieldAxis e
  | Sum.inr τ => SField.refl τ

/-- A word in the generators acting on a smeared-field datum; the head of the list acts last.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the excluded colour count. -/
def hypField : List (Equiv.Perm (Fin 4) ⊕ Fin 4) → SField N → SField N
  | [], p => p
  | g :: w, p => genField g (hypField w p)

/-- **OS1, the hypercubic group**: every word in the axis permutations and axis reflections leaves
the continuum Schwinger function unchanged, at data compatible with every generator.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem contS_hyp (hN : N ≠ 0) (ρ : Renorm N) (hRefl : ∀ τ : Fin 4, ρ.ReflCompat τ)
    (hAxis : ∀ e : Equiv.Perm (Fin 4), axisCompat ρ e) (w : List (Equiv.Perm (Fin 4) ⊕ Fin 4))
    {ι : Type} [Fintype ι] (F : ι → SField N) :
    contS hN ρ (fun i => hypField w (F i)) = contS hN ρ F := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g with
    | inl e => exact (contS_axis hN ρ e (hAxis e) (fun i => hypField w (F i))).trans ih
    | inr τ => exact (contS_reflect hN ρ τ (hRefl τ) (fun i => hypField w (F i))).trans ih

#print axioms contS_hyp

/-- The map of `ℝ⁴` a generator's test function is read through.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def genR : (Equiv.Perm (Fin 4) ⊕ Fin 4) → (Fin 4 → ℝ) → (Fin 4 → ℝ)
  | Sum.inl e => permR e
  | Sum.inr τ => reflR τ

/-- The map of `ℝ⁴` a word's test function is read through: `hypR (g :: w) = hypR w ∘ genR g`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def hypR : List (Equiv.Perm (Fin 4) ⊕ Fin 4) → (Fin 4 → ℝ) → (Fin 4 → ℝ)
  | [], y => y
  | g :: w, y => hypR w (genR g y)

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem hypR_cons (g : Equiv.Perm (Fin 4) ⊕ Fin 4) (w : List (Equiv.Perm (Fin 4) ⊕ Fin 4))
    (y : Fin 4 → ℝ) : hypR (g :: w) y = hypR w (genR g y) := rfl

#print axioms hypR_cons

/-- **A word acts on test functions by `f ↦ f ∘ hypR w`.**

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem hypField_test (w : List (Equiv.Perm (Fin 4) ⊕ Fin 4)) :
    ∀ (p : SField N) (y : Fin 4 → ℝ), (hypField w p).2.1 y = p.2.1 (hypR w y) := by
  induction w with
  | nil => intro p y; rfl
  | cons g w ih =>
    intro p y
    cases g with
    | inl e => exact ih p (permR e y)
    | inr τ => exact ih p (reflR τ y)

#print axioms hypField_test

/-- **Every word acts on `ℝ⁴` as a signed permutation of the coordinates**:
`hypR w y = (sᵢ · y_{σ i})ᵢ` with every `sᵢ = ±1`.

DERIVED: `1` and `-1` are the signs; `4` in `Fin 4` is the spacetime dimension. -/
theorem hypR_signed (w : List (Equiv.Perm (Fin 4) ⊕ Fin 4)) :
    ∃ (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ), (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ y i, hypR w y i = s i * y (σ i) := by
  induction w with
  | nil =>
    refine ⟨Equiv.refl _, fun _ => 1, fun _ => Or.inl rfl, fun y i => ?_⟩
    show y i = 1 * y i
    rw [one_mul]
  | cons g w ih =>
    obtain ⟨σ, s, hs, h⟩ := ih
    cases g with
    | inl e =>
      refine ⟨σ.trans e, s, hs, fun y i => ?_⟩
      rw [hypR_cons, h]
      rfl
    | inr τ =>
      refine ⟨σ, fun i => s i * (if σ i = τ then -1 else 1), fun i => ?_, fun y i => ?_⟩
      · show s i * (if σ i = τ then -1 else 1) = 1 ∨ s i * (if σ i = τ then -1 else 1) = -1
        by_cases hτ : σ i = τ
        · rw [if_pos hτ]
          rcases hs i with h1 | h1
          · right; rw [h1]; ring
          · left; rw [h1]; ring
        · rw [if_neg hτ, mul_one]
          exact hs i
      · rw [hypR_cons, h]
        show s i * reflR τ y (σ i) = s i * (if σ i = τ then -1 else 1) * y (σ i)
        by_cases hτ : σ i = τ
        · rw [if_pos hτ, hτ]
          simp only [reflR, Function.update_self]
          ring
        · rw [if_neg hτ]
          simp only [reflR, Function.update_of_ne hτ]
          ring

#print axioms hypR_signed

/-- The reflections of a list of distinct axes act by negating exactly those coordinates.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem hypR_refls : ∀ L : List (Fin 4), L.Nodup → ∀ (z : Fin 4 → ℝ) (i : Fin 4),
    hypR (L.map Sum.inr) z i = if i ∈ L then -z i else z i := by
  intro L
  induction L with
  | nil =>
    intro _ z i
    simp [hypR]
  | cons τ L ih =>
    intro hL z i
    rw [List.nodup_cons] at hL
    rw [List.map_cons, hypR_cons, ih hL.2 (genR (Sum.inr τ) z) i]
    have hg : genR (Sum.inr τ) z = reflR τ z := rfl
    rw [hg]
    by_cases h : i = τ
    · rw [h, if_neg hL.1, if_pos (List.mem_cons_self : τ ∈ τ :: L)]
      simp only [reflR, Function.update_self]
    · have hr : reflR τ z i = z i := by simp only [reflR, Function.update_of_ne h]
      rw [hr]
      have hm : i ∈ τ :: L ↔ i ∈ L := by simp [h]
      by_cases hi : i ∈ L
      · rw [if_pos hi, if_pos (hm.mpr hi)]
      · rw [if_neg hi, if_neg (fun h' => hi (hm.mp h'))]

#print axioms hypR_refls

/-- **Every signed permutation of the coordinates is a word**: for `σ` and signs `sᵢ = ±1` there is
`w` with `hypR w y = (sᵢ · y_{σ i})ᵢ`, the permutation followed by the reflections of the axes with
`sᵢ = -1`.

DERIVED: `1` and `-1` are the signs; `4` is the spacetime dimension, the length of `finRange`. -/
theorem exists_word_signed (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    ∃ w : List (Equiv.Perm (Fin 4) ⊕ Fin 4), ∀ y i, hypR w y i = s i * y (σ i) := by
  refine ⟨Sum.inl σ :: ((List.finRange 4).filter (fun i => decide (s i = -1))).map Sum.inr,
    fun y i => ?_⟩
  rw [hypR_cons, hypR_refls _ ((List.nodup_finRange 4).filter _)]
  have hg : genR (Sum.inl σ) y i = y (σ i) := rfl
  rw [hg]
  have hmem : i ∈ (List.finRange 4).filter (fun i => decide (s i = -1)) ↔ s i = -1 := by
    simp [List.mem_filter, List.mem_finRange]
  rcases hs i with h | h
  · have hn : ¬ (i ∈ (List.finRange 4).filter (fun i => decide (s i = -1))) := by
      rw [hmem, h]
      norm_num
    rw [if_neg hn, h, one_mul]
  · rw [if_pos (hmem.mpr h), h, neg_one_mul]

#print axioms exists_word_signed

/-- A field fixed by the lattice hypercubic group: every axis permutation and every axis reflection
about the origin leave it unchanged. Sums over the orientations of the plaquettes around a site
(clover sums) are examples; a single plaquette is not.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def HypScalar (O : LField (MassGap.SUN.SU N)) : Prop :=
  (∀ e : Equiv.Perm (Fin 4), lfieldAxis e O = O) ∧ ∀ τ : Fin 4, LField.refl τ O = O

/-- A word leaves a `HypScalar` field unchanged.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem hypField_fst (w : List (Equiv.Perm (Fin 4) ⊕ Fin 4)) (p : SField N)
    (hp : HypScalar p.1) : (hypField w p).1 = p.1 := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g with
    | inl e =>
      show lfieldAxis e (hypField w p).1 = p.1
      rw [ih]
      exact hp.1 e
    | inr τ =>
      show LField.refl τ (hypField w p).1 = p.1
      rw [ih]
      exact hp.2 τ

#print axioms hypField_fst

/-- **The hypercubic group `W(B₄)` on the test functions.** For fields fixed by the lattice
hypercubic group, composing every test function with a signed permutation `y ↦ (sᵢ y_{σ i})ᵢ` of
`ℝ⁴`, fields unchanged, leaves the continuum Schwinger function unchanged, at data compatible with
every generator.

DERIVED: `0` is the excluded colour count; `1` and `-1` are the signs; `4` in `Fin 4` is the
spacetime dimension. -/
theorem contS_signed (hN : N ≠ 0) (ρ : Renorm N) (hRefl : ∀ τ : Fin 4, ρ.ReflCompat τ)
    (hAxis : ∀ e : Equiv.Perm (Fin 4), axisCompat ρ e) (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) {ι : Type} [Fintype ι] (F F' : ι → SField N)
    (hΦ : ∀ i, HypScalar (F i).1) (hfield : ∀ i, (F' i).1 = (F i).1)
    (htest : ∀ i y, (F' i).2.1 y = (F i).2.1 (fun j => s j * y (σ j))) :
    contS hN ρ F' = contS hN ρ F := by
  obtain ⟨w, hw⟩ := exists_word_signed σ s hs
  have hF' : F' = fun i => hypField w (F i) := by
    funext i
    refine Prod.ext ?_ (Subtype.ext (funext fun y => ?_))
    · rw [hfield i, hypField_fst w (F i) (hΦ i)]
    · rw [htest i y, hypField_test w (F i) y]
      exact congrArg (F i).2.1 (funext fun j => (hw y j).symm)
  rw [hF']
  exact contS_hyp hN ρ hRefl hAxis w F

#print axioms contS_signed

end Schwinger

/-! ## 5. Continuity in the test functions -/

section Continuity

/-- `‖∏ Aᵢ − ∏ Bᵢ‖ ≤ (∑ Dᵢ) ∏ Kᵢ` in `C(X, ℝ)` when `‖Aᵢ‖, ‖Bᵢ‖ ≤ Kᵢ`, `1 ≤ Kᵢ` and
`‖Aᵢ − Bᵢ‖ ≤ Dᵢ`: one factor exchanged at a time.

DERIVED: `1` is the unit, below every `Kᵢ`, so that `∏ Kᵢ` bounds every sub-product. -/
theorem norm_prod_sub_prod_le {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}
    (s : Finset ι) (A B : ι → C(X, ℝ)) (K D : ι → ℝ) (hK1 : ∀ i, 1 ≤ K i)
    (hA : ∀ i, ‖A i‖ ≤ K i) (hB : ∀ i, ‖B i‖ ≤ K i) (hD : ∀ i, ‖A i - B i‖ ≤ D i) :
    ‖∏ i ∈ s, A i - ∏ i ∈ s, B i‖ ≤ (∑ i ∈ s, D i) * ∏ i ∈ s, K i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb, Finset.sum_insert hb, Finset.prod_insert hb]
    have hKs : 0 ≤ ∏ i ∈ s, K i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hK1 i))
    have hBs : ‖∏ i ∈ s, B i‖ ≤ ∏ i ∈ s, K i :=
      (norm_prod_le_prod s B).trans
        (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hB i))
    have hDb : 0 ≤ D b := (norm_nonneg _).trans (hD b)
    have hsplit : A b * ∏ i ∈ s, A i - B b * ∏ i ∈ s, B i
        = A b * (∏ i ∈ s, A i - ∏ i ∈ s, B i) + (A b - B b) * ∏ i ∈ s, B i := by ring
    rw [hsplit]
    have h1 : D b * ∏ i ∈ s, K i ≤ D b * (K b * ∏ i ∈ s, K i) := by
      refine mul_le_mul_of_nonneg_left ?_ hDb
      calc ∏ i ∈ s, K i = 1 * ∏ i ∈ s, K i := (one_mul _).symm
        _ ≤ K b * ∏ i ∈ s, K i := mul_le_mul_of_nonneg_right (hK1 b) hKs
    calc ‖A b * (∏ i ∈ s, A i - ∏ i ∈ s, B i) + (A b - B b) * ∏ i ∈ s, B i‖
        ≤ ‖A b‖ * ‖∏ i ∈ s, A i - ∏ i ∈ s, B i‖ + ‖A b - B b‖ * ‖∏ i ∈ s, B i‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ K b * ((∑ i ∈ s, D i) * ∏ i ∈ s, K i) + D b * ∏ i ∈ s, K i :=
          add_le_add (mul_le_mul (hA b) ih (norm_nonneg _) (zero_le_one.trans (hK1 b)))
            (mul_le_mul (hD b) hBs (norm_nonneg _) hDb)
      _ ≤ (D b + ∑ i ∈ s, D i) * (K b * ∏ i ∈ s, K i) := by linarith [h1]

#print axioms norm_prod_sub_prod_le

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]

/-- **The smeared field is Lipschitz in the sup norm of the test function, uniformly in the
spacing**: at `0 < a ≤ 1`, for `f`, `g` supported in `[-R, R]⁴` with `|f − g| ≤ δ`,
`‖smear a F f − smear a F g‖ ≤ ‖F‖ · δ · (2R + 3)⁴`. The difference is the smear of `f − g`, a test
function bounded by `δ` on the same cube, and `norm_smear_le` applies.

DERIVED: `0` is the sign of `a`; `1` bounds `a`; `2`, `3`, `4` are `norm_smear_le`'s. -/
theorem norm_smear_sub_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (F : C(IConf G, ℝ)) (f g : TestFn)
    {R Mf Mg δ : ℝ} (hf : IsTest f.1 R Mf) (hg : IsTest g.1 R Mg)
    (hfg : ∀ y, |f.1 y - g.1 y| ≤ δ) :
    ‖smear a F f - smear a F g‖ ≤ ‖F‖ * (δ * (2 * R + 3) ^ 4) := by
  have hT : IsTest (fun y => f.1 y - g.1 y) R δ := by
    refine ⟨hf.1, hfg, fun y hy i => ?_⟩
    have hy' : f.1 y - g.1 y ≠ 0 := hy
    by_cases hfy : f.1 y = 0
    · have hgy : g.1 y ≠ 0 := by
        intro hg0
        apply hy'
        rw [hfy, hg0, sub_zero]
      exact hg.2.2 y hgy i
    · exact hf.2.2 y hfy i
  have hsub : smear a F f - smear a F g = smear a F ⟨fun y => f.1 y - g.1 y, R, δ, hT⟩ := by
    rw [smear_eq_sum ha F f hf (Finset.Subset.refl _), smear_eq_sum ha F g hg (Finset.Subset.refl _),
      smear_eq_sum ha F ⟨fun y => f.1 y - g.1 y, R, δ, hT⟩ hT (Finset.Subset.refl _),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show (a ^ 4 * f.1 (site a x)) • transObs x F - (a ^ 4 * g.1 (site a x)) • transObs x F
      = (a ^ 4 * (f.1 (site a x) - g.1 (site a x))) • transObs x F
    rw [mul_sub, sub_smul]
  rw [hsub]
  exact norm_smear_le ha ha1 F ⟨fun y => f.1 y - g.1 y, R, δ, hT⟩ hT

#print axioms norm_smear_sub_le

end Continuity

section ContinuityS

variable {N : ℕ}

/-- **The lattice Schwinger functions are Lipschitz in the test functions**: for test functions
`gᵢ` within `δ` of `fᵢ` in the sup norm, all supported in `[-R, R]⁴`, `|fᵢ| ≤ Mᵢ`, `|gᵢ| ≤ Mᵢ + 1`,
`|latS ν a (O, g) − latS ν a (O, f)| ≤ (∑ ‖Oᵢ‖ δ (2R + 3)⁴) · ∏ (‖Oᵢ‖ (Mᵢ + 1)(2R + 3)⁴ + 1)`.

DERIVED: `0` is the sign of `a`; `1` bounds `a`, is the slack `Mᵢ + 1` on the second bound, and the
unit added to make every factor at least one (`norm_prod_sub_prod_le`); `2`, `3`, `4` are
`norm_smear_le`'s. -/
theorem abs_latS_sub_le (ν : MassGap.DLRLimit.State (Cfg N)) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {ι : Type} [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (f g : ι → TestFn) {R δ : ℝ}
    (M : ι → ℝ) (hf : ∀ i, IsTest (f i).1 R (M i)) (hg : ∀ i, IsTest (g i).1 R (M i + 1))
    (hfg : ∀ i y, |(g i).1 y - (f i).1 y| ≤ δ) :
    |latS ν a (fun i => (O i, g i)) - latS ν a (fun i => (O i, f i))|
      ≤ (∑ i, ‖(O i).1‖ * (δ * (2 * R + 3) ^ 4))
        * ∏ i, (‖(O i).1‖ * ((M i + 1) * (2 * R + 3) ^ 4) + 1) := by
  have hX : ∀ i, 0 ≤ ‖(O i).1‖ * ((M i + 1) * (2 * R + 3) ^ 4) := fun i =>
    mul_nonneg (norm_nonneg _) (mul_nonneg (hg i).M_nonneg (by positivity))
  show |ν (∏ i, smear a (O i).1 (g i)) - ν (∏ i, smear a (O i).1 (f i))| ≤ _
  refine (ν.abs_sub_le _ _).trans ?_
  refine norm_prod_sub_prod_le Finset.univ (fun i => smear a (O i).1 (g i))
    (fun i => smear a (O i).1 (f i))
    (fun i => ‖(O i).1‖ * ((M i + 1) * (2 * R + 3) ^ 4) + 1)
    (fun i => ‖(O i).1‖ * (δ * (2 * R + 3) ^ 4))
    (fun i => le_add_of_nonneg_left (hX i)) (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · show ‖smear a (O i).1 (g i)‖ ≤ ‖(O i).1‖ * ((M i + 1) * (2 * R + 3) ^ 4) + 1
    exact (norm_smear_le ha ha1 _ _ (hg i)).trans (le_add_of_nonneg_right zero_le_one)
  · show ‖smear a (O i).1 (f i)‖ ≤ ‖(O i).1‖ * ((M i + 1) * (2 * R + 3) ^ 4) + 1
    refine (norm_smear_le ha ha1 _ _ (hf i)).trans
      ((mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)).trans (le_add_of_nonneg_right zero_le_one))
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · show ‖smear a (O i).1 (g i) - smear a (O i).1 (f i)‖ ≤ ‖(O i).1‖ * (δ * (2 * R + 3) ^ 4)
    exact norm_smear_sub_le ha ha1 _ _ _ (hg i) (hf i) (hfg i)

#print axioms abs_latS_sub_le

/-- **The renormalised lattice functions are Lipschitz in the test functions at bounded data**,
eventually in the step: for `F'` with the fields of `F` and test functions within `δ` of them,

`|latSkR F' − latSkR F| ≤ ∏ Bᶻ · (∑ (‖O‖ + Bᶜ) δ (2R + 3)⁴) · ∏ ((‖O‖ + Bᶜ)(M + 1)(2R + 3)⁴ + 1)`.

DERIVED: `0` is the excluded colour count and the sign of `δ`; `1`, `2`, `3`, `4` as in
`abs_latS_sub_le`. The spacing bound enters in the proof, where `dySpacing N k` falls below one. -/
theorem eventually_abs_latSkR_sub_le (hN : N ≠ 0) (ρ : Renorm N)
    (BZ Bc : LField (MassGap.SUN.SU N) → ℝ) (hZ : ∀ k O, |ρ.Z k O| ≤ BZ O)
    (hc : ∀ k O, |ρ.c k O| ≤ Bc O) {ι : Type} [Fintype ι] (F F' : ι → SField N) {R δ : ℝ}
    (hδ : 0 ≤ δ) (M : ι → ℝ) (hF : ∀ i, IsTest (F i).2.1 R (M i))
    (hF' : ∀ i, IsTest (F' i).2.1 R (M i + 1)) (hfield : ∀ i, (F' i).1 = (F i).1)
    (hclose : ∀ i y, |(F' i).2.1 y - (F i).2.1 y| ≤ δ) :
    ∀ᶠ k in atTop, |latSkR hN ρ k F' - latSkR hN ρ k F|
      ≤ (∏ i, BZ (F i).1) * ((∑ i, (‖(F i).1.1‖ + Bc (F i).1) * (δ * (2 * R + 3) ^ 4))
          * ∏ i, ((‖(F i).1.1‖ + Bc (F i).1) * ((M i + 1) * (2 * R + 3) ^ 4) + 1)) := by
  filter_upwards [(tendsto_dySpacing N).eventually (gt_mem_nhds one_pos)] with k hk1
  have ha := dySpacing_pos (one_le_of_ne_zero hN) k
  have hpref : ρ.pref k F' = ρ.pref k F :=
    Finset.prod_congr rfl (fun i _ => congrArg (ρ.Z k) (hfield i))
  have hfam' : (fun i => ρ.field k (F' i))
      = fun i => ((F i).1.sub (ρ.c k (F i).1), (F' i).2) := by
    funext i
    show ((F' i).1.sub (ρ.c k (F' i).1), (F' i).2) = ((F i).1.sub (ρ.c k (F i).1), (F' i).2)
    rw [hfield i]
  have hfam : (fun i => ρ.field k (F i))
      = fun i => ((F i).1.sub (ρ.c k (F i).1), (F i).2) := rfl
  show |ρ.pref k F' * latSk hN k (fun i => ρ.field k (F' i))
      - ρ.pref k F * latSk hN k (fun i => ρ.field k (F i))| ≤ _
  rw [hpref, hfam', hfam, ← mul_sub, abs_mul, latSk_eq, latSk_eq]
  have hL := abs_latS_sub_le (stateK hN k) ha hk1.le (fun i => (F i).1.sub (ρ.c k (F i).1))
    (fun i => (F i).2) (fun i => (F' i).2) M hF hF' hclose
  have hX0 : 0 ≤ (2 * R + 3) ^ 4 := by positivity
  have hA : ∀ i, ‖((F i).1.sub (ρ.c k (F i).1)).1‖ ≤ ‖(F i).1.1‖ + Bc (F i).1 := fun i =>
    (norm_sub_smul_one_le (F i).1.1 (ρ.c k (F i).1)).trans (by linarith [hc k (F i).1])
  have hM1 : ∀ i, 0 ≤ (M i + 1) * (2 * R + 3) ^ 4 := fun i => mul_nonneg (hF' i).M_nonneg hX0
  have hA0 : ∀ i, 0 ≤ ‖(F i).1.1‖ + Bc (F i).1 := fun i =>
    add_nonneg (norm_nonneg _) ((abs_nonneg _).trans (hc 0 (F i).1))
  have hQ : (∑ i, ‖((F i).1.sub (ρ.c k (F i).1)).1‖ * (δ * (2 * R + 3) ^ 4))
        * ∏ i, (‖((F i).1.sub (ρ.c k (F i).1)).1‖ * ((M i + 1) * (2 * R + 3) ^ 4) + 1)
      ≤ (∑ i, (‖(F i).1.1‖ + Bc (F i).1) * (δ * (2 * R + 3) ^ 4))
        * ∏ i, ((‖(F i).1.1‖ + Bc (F i).1) * ((M i + 1) * (2 * R + 3) ^ 4) + 1) :=
    mul_le_mul
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hA i) (mul_nonneg hδ hX0)))
      (Finset.prod_le_prod
        (fun i _ => add_nonneg (mul_nonneg (norm_nonneg _) (hM1 i)) zero_le_one)
        (fun i _ => add_le_add (mul_le_mul_of_nonneg_right (hA i) (hM1 i)) le_rfl))
      (Finset.prod_nonneg (fun i _ => add_nonneg (mul_nonneg (norm_nonneg _) (hM1 i)) zero_le_one))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hA0 i) (mul_nonneg hδ hX0)))
  have hP : |ρ.pref k F| ≤ ∏ i, BZ (F i).1 := by
    unfold Renorm.pref
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hZ k _)
  exact mul_le_mul hP (hL.trans hQ) (abs_nonneg _)
    (Finset.prod_nonneg (fun i _ => (abs_nonneg _).trans (hZ 0 _)))

#print axioms eventually_abs_latSkR_sub_le

/-- **Equicontinuity of the lattice functions on separated families (stated).** For every family
`F`, cube radius `R`, separation `d > 0` and `ε > 0` there is `δ > 0` such that every `F'` with the
fields of `F`, test functions within `δ` of those of `F` in the sup norm, both families supported in
`[-R, R]⁴` and `d`-separated, has `|latSkR F' − latSkR F| ≤ ε` eventually in the step. Proved at
bounded renormalisation data (`latticeEquicontSep_of_bounded`). At a growing field-strength factor
the lattice Lipschitz bound carries `∏ Z`, and the statement is open.

DERIVED: `0` is the excluded colour count and the sign of `d`, `ε`, `δ` and the support value. -/
def LatticeEquicontSep (hN : N ≠ 0) (ρ : Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N) (R d ε : ℝ), 0 < d → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ F' : ι → SField N, (∀ i, (F' i).1 = (F i).1) →
      (∀ i y, |(F' i).2.1 y - (F i).2.1 y| ≤ δ) →
      (∀ i y, (F i).2.1 y ≠ 0 → ∀ j, |y j| ≤ R) → (∀ i y, (F' i).2.1 y ≠ 0 → ∀ j, |y j| ≤ R) →
      ContinuumSep.FamSep d F → ContinuumSep.FamSep d F' →
      ∀ᶠ k in atTop, |latSkR hN ρ k F' - latSkR hN ρ k F| ≤ ε

/-- **Continuity of the continuum Schwinger functions in the test functions, on separated families
(stated).** For every family `F`, cube radius `R`, separation `d > 0` and `ε > 0` there is `δ > 0`
such that every `F'` with the fields of `F` and test functions within `δ` of those of `F` in the sup
norm, both families supported in `[-R, R]⁴` and `d`-separated, has `|contS F' − contS F| ≤ ε`.

DERIVED: `0` is the excluded colour count and the sign of `d`, `ε`, `δ` and the support value. -/
def SupContinuousSep (hN : N ≠ 0) (ρ : Renorm N) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N) (R d ε : ℝ), 0 < d → 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ F' : ι → SField N, (∀ i, (F' i).1 = (F i).1) →
      (∀ i y, |(F' i).2.1 y - (F i).2.1 y| ≤ δ) →
      (∀ i y, (F i).2.1 y ≠ 0 → ∀ j, |y j| ≤ R) → (∀ i y, (F' i).2.1 y ≠ 0 → ∀ j, |y j| ≤ R) →
      ContinuumSep.FamSep d F → ContinuumSep.FamSep d F' →
      |contS hN ρ F' - contS hN ρ F| ≤ ε

/-- **Equicontinuity of the lattice functions gives continuity of the limit**, under
`UniformBoundSep`: both separated families converge along `ultra` (`tendsto_contS_sep`) and the
eventual bound passes to the limit.

DERIVED: `0` is the excluded colour count. -/
theorem supContinuousSep_of_equicont (hN : N ≠ 0) (ρ : Renorm N)
    (hB : ContinuumSep.UniformBoundSep hN ρ) (hE : LatticeEquicontSep hN ρ) :
    SupContinuousSep hN ρ := by
  intro ι _ F R d ε hd hε
  obtain ⟨δ, hδ, hk⟩ := hE ι F R d ε hd hε
  refine ⟨δ, hδ, fun F' hf hc hRF hRF' hsF hsF' => ?_⟩
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  exact le_of_tendsto
    (((ContinuumSep.tendsto_contS_sep hN ρ hB F' hd hsF').sub
      (ContinuumSep.tendsto_contS_sep hN ρ hB F hd hsF)).abs)
    ((hk F' hf hc hRF hRF' hsF hsF').filter_mono ultra_le)

#print axioms supContinuousSep_of_equicont

/-- **At bounded renormalisation data the lattice functions are equicontinuous**, on every family,
separated or not: `eventually_abs_latSkR_sub_le` at `δ = min 1 (ε / (L + 1))`, `L` the Lipschitz
constant at radius `max R 0`.

DERIVED: `0` is the excluded colour count and the sign of `L`, `δ`, `ε`; `1` caps `δ`, so that
`|F'| ≤ M + 1`, and makes `L + 1` positive; `2`, `3`, `4` are `norm_smear_le`'s. -/
theorem latticeEquicontSep_of_bounded (hN : N ≠ 0) (ρ : Renorm N)
    (hZ : ∀ O, ∃ B : ℝ, ∀ k, |ρ.Z k O| ≤ B) (hc : ∀ O, ∃ B : ℝ, ∀ k, |ρ.c k O| ≤ B) :
    LatticeEquicontSep hN ρ := by
  intro ι _ F R d ε _ hε
  choose BZ hBZ using hZ
  choose Bc hBc using hc
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  have hBZ0 : ∀ O, 0 ≤ BZ O := fun O => (abs_nonneg _).trans (hBZ O 0)
  have hBc0 : ∀ O, 0 ≤ Bc O := fun O => (abs_nonneg _).trans (hBc O 0)
  have hX0 : 0 ≤ (2 * max R 0 + 3) ^ 4 := by positivity
  have hA0 : ∀ i, 0 ≤ ‖(F i).1.1‖ + Bc (F i).1 := fun i => add_nonneg (norm_nonneg _) (hBc0 _)
  have hM0 : ∀ i, 0 ≤ M i + 1 := fun i => by linarith [(hRM i).M_nonneg]
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (∏ i, BZ (F i).1)
      * ((∑ i, (‖(F i).1.1‖ + Bc (F i).1) * (2 * max R 0 + 3) ^ 4)
        * ∏ i, ((‖(F i).1.1‖ + Bc (F i).1) * ((M i + 1) * (2 * max R 0 + 3) ^ 4) + 1)) :=
    ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => hBZ0 _))
      (mul_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hA0 i) hX0))
        (Finset.prod_nonneg (fun i _ =>
          add_nonneg (mul_nonneg (hA0 i) (mul_nonneg (hM0 i) hX0)) zero_le_one)))
  have hpos : 0 < L + 1 := by linarith
  refine ⟨min 1 (ε / (L + 1)), lt_min one_pos (div_pos hε hpos),
    fun F' hfield hclose hRF hRF' _ _ => ?_⟩
  have hδ1 : min 1 (ε / (L + 1)) ≤ 1 := min_le_left _ _
  have hδε : min 1 (ε / (L + 1)) ≤ ε / (L + 1) := min_le_right _ _
  have hδ0 : 0 ≤ min 1 (ε / (L + 1)) := le_min zero_le_one (div_nonneg hε.le hpos.le)
  have hFT : ∀ i, IsTest (F i).2.1 (max R 0) (M i) := fun i =>
    ⟨le_max_right _ _, (hRM i).2.1, fun y hy j => (hRF i y hy j).trans (le_max_left _ _)⟩
  have hF'T : ∀ i, IsTest (F' i).2.1 (max R 0) (M i + 1) := by
    intro i
    refine ⟨le_max_right _ _, fun y => ?_, fun y hy j => (hRF' i y hy j).trans (le_max_left _ _)⟩
    have h1 := hclose i y
    have h2 := (hRM i).2.1 y
    have h3 : |(F' i).2.1 y| ≤ |(F' i).2.1 y - (F i).2.1 y| + |(F i).2.1 y| := by
      have h4 := abs_add_le ((F' i).2.1 y - (F i).2.1 y) ((F i).2.1 y)
      rwa [sub_add_cancel] at h4
    linarith
  filter_upwards [eventually_abs_latSkR_sub_le hN ρ BZ Bc (fun k O => hBZ O k)
    (fun k O => hBc O k) F F' hδ0 M hFT hF'T hfield hclose] with k hk
  refine hk.trans ?_
  have hsum : (∑ i, (‖(F i).1.1‖ + Bc (F i).1) * (min 1 (ε / (L + 1)) * (2 * max R 0 + 3) ^ 4))
      = min 1 (ε / (L + 1)) * ∑ i, (‖(F i).1.1‖ + Bc (F i).1) * (2 * max R 0 + 3) ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  have hmul : (∏ i, BZ (F i).1)
        * ((min 1 (ε / (L + 1)) * ∑ i, (‖(F i).1.1‖ + Bc (F i).1) * (2 * max R 0 + 3) ^ 4)
          * ∏ i, ((‖(F i).1.1‖ + Bc (F i).1) * ((M i + 1) * (2 * max R 0 + 3) ^ 4) + 1))
      = min 1 (ε / (L + 1)) * L := by
    rw [hLdef]
    ring
  rw [hmul]
  calc min 1 (ε / (L + 1)) * L ≤ ε / (L + 1) * L := mul_le_mul_of_nonneg_right hδε hL0
    _ = ε * L / (L + 1) := by rw [div_mul_eq_mul_div]
    _ ≤ ε := by
      rw [div_le_iff₀ hpos, mul_add, mul_one]
      linarith

#print axioms latticeEquicontSep_of_bounded

/-- **Continuity in the test functions at bounded renormalisation data.**

DERIVED: `0` is the excluded colour count. -/
theorem supContinuousSep_of_bounded (hN : N ≠ 0) (ρ : Renorm N)
    (hZ : ∀ O, ∃ B : ℝ, ∀ k, |ρ.Z k O| ≤ B) (hc : ∀ O, ∃ B : ℝ, ∀ k, |ρ.c k O| ≤ B) :
    SupContinuousSep hN ρ :=
  supContinuousSep_of_equicont hN ρ
    (ContinuumSep.uniformBoundSep_of_uniformBound hN ρ (uniformBound_of_bounded hN ρ hZ hc))
    (latticeEquicontSep_of_bounded hN ρ hZ hc)

#print axioms supContinuousSep_of_bounded

/-- **The dyadic vectors are dense in `ℝ⁴`**: a property holding near `v` holds at some
`dySpacing N m · n`, `n ∈ ℤ⁴`. With `m` such that `dySpacing N m < r` and `nⱼ = ⌊vⱼ / dySpacing N m⌋`,
every coordinate of `dySpacing N m · n` is within `dySpacing N m` of `vⱼ`.

DERIVED: `1` is the least colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem exists_dyadic_of_eventually (hN1 : 1 ≤ N) {v : Fin 4 → ℝ} {P : (Fin 4 → ℝ) → Prop}
    (h : ∀ᶠ w in 𝓝 v, P w) : ∃ (m : ℕ) (n : ISite), P (site (dySpacing N m) n) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp h
  obtain ⟨m, hm⟩ := ((tendsto_dySpacing N).eventually (gt_mem_nhds hr)).exists
  have ha := dySpacing_pos hN1 m
  refine ⟨m, fun j => ⌊v j / dySpacing N m⌋, hball ?_⟩
  rw [dist_pi_lt_iff hr]
  intro j
  rw [Real.dist_eq]
  show |dySpacing N m * ((⌊v j / dySpacing N m⌋ : ℤ) : ℝ) - v j| < r
  have h1 : ((⌊v j / dySpacing N m⌋ : ℤ) : ℝ) * dySpacing N m ≤ v j :=
    (le_div_iff₀ ha).mp (Int.floor_le _)
  have h2 : v j < (((⌊v j / dySpacing N m⌋ : ℤ) : ℝ) + 1) * dySpacing N m :=
    (div_lt_iff₀ ha).mp (Int.lt_floor_add_one _)
  rw [abs_sub_lt_iff]
  constructor <;> linarith

#print axioms exists_dyadic_of_eventually

/-- **OS1 on all of `ℝ⁴`**: under `SupContinuousSep`, for a `d`-separated family of uniformly
continuous test functions, translating every test function by any `v ∈ ℝ⁴` leaves the continuum
Schwinger function unchanged. For `ε > 0`, a dyadic `w` near `v` moves every test function by at most
the `δ` of `SupContinuousSep` at the family translated by `v`, and `contS_translate` at `w`.

DERIVED: `0` is the excluded colour count and the sign of `d` and `ε`; `1` bounds the distance of `w`
to `v`, which keeps both translates in one cube; `4` in `Fin 4` is the spacetime dimension. -/
theorem contS_translate_real (hN : N ≠ 0) (ρ : Renorm N) (hC : SupContinuousSep hN ρ)
    {ι : Type} [Fintype ι] (F : ι → SField N) (hU : ∀ i, UniformContinuous (F i).2.1)
    {d : ℝ} (hd : 0 < d) (hsep : ContinuumSep.FamSep d F) (v : Fin 4 → ℝ) :
    contS hN ρ (fun i => ((F i).1, (F i).2.translate v)) = contS hN ρ F := by
  have hN1 := one_le_of_ne_zero hN
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, R0 i + ∑ j, |v j| + 1 := ⟨_, rfl⟩
  have hbox : ∀ u : Fin 4 → ℝ, dist u v < 1 →
      ∀ i y, ((F i).2.translate u).1 y ≠ 0 → ∀ j, |y j| ≤ R := by
    intro u hu i y hy j
    have h1 : |y j - u j| ≤ R0 i := (hRM i).2.2 (y - u) hy j
    have h2 : dist (u j) (v j) < 1 := (dist_le_pi_dist u v j).trans_lt hu
    rw [Real.dist_eq] at h2
    have h3 : |u j| - |v j| ≤ |u j - v j| := abs_sub_abs_le_abs_sub (u j) (v j)
    have h4 : R0 i ≤ ∑ i, R0 i :=
      Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
    have h5 : |v j| ≤ ∑ j, |v j| :=
      Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg (v j)) (Finset.mem_univ j)
    have h6 : |y j| ≤ |y j - u j| + |u j| := by
      have h7 := abs_add_le (y j - u j) (u j)
      rwa [sub_add_cancel] at h7
    rw [hRdef]
    linarith
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  rw [Real.dist_eq]
  obtain ⟨δ, hδ, key⟩ := hC ι (fun i => ((F i).1, (F i).2.translate v)) R d ε hd hε
  have hη : ∀ i, ∃ η : ℝ, 0 < η ∧
      ∀ a b : Fin 4 → ℝ, dist a b < η → dist ((F i).2.1 a) ((F i).2.1 b) < δ := by
    intro i
    obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp (hU i) δ hδ
    exact ⟨η, hη, fun a b hab => h hab⟩
  choose η hη0 hηf using hη
  have hev1 : ∀ i, ∀ᶠ w in 𝓝 v, dist w v < η i := fun i =>
    Metric.eventually_nhds_iff.mpr ⟨η i, hη0 i, by intro w hw; exact hw⟩
  have hev2 : ∀ᶠ w in 𝓝 v, dist w v < 1 :=
    Metric.eventually_nhds_iff.mpr ⟨1, one_pos, by intro w hw; exact hw⟩
  have hev3 : ∀ᶠ w in 𝓝 v, ∀ i, dist w v < η i := Filter.eventually_all.mpr hev1
  have hev : ∀ᶠ w in 𝓝 v, (∀ i, dist w v < η i) ∧ dist w v < 1 := hev3.and hev2
  obtain ⟨m, n, hw, hw1⟩ := exists_dyadic_of_eventually hN1 hev
  have hsepv : ContinuumSep.FamSep d (fun i => ((F i).1, (F i).2.translate v)) :=
    fun i j hij => ContinuumSep.sepBy_translate (hsep i j hij) v
  have hsepw : ContinuumSep.FamSep d
      (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) n))) :=
    fun i j hij => ContinuumSep.sepBy_translate (hsep i j hij) _
  have hk := key (fun i => ((F i).1, (F i).2.translate (site (dySpacing N m) n))) (fun i => rfl)
    (fun i y => by
      have h := hηf i (y - site (dySpacing N m) n) (y - v) (by rw [dist_sub_left]; exact hw i)
      rw [Real.dist_eq] at h
      exact h.le)
    (hbox v (by rw [dist_self]; exact one_pos)) (hbox _ hw1) hsepv hsepw
  rw [contS_translate hN ρ F m n, abs_sub_comm] at hk
  exact hk

#print axioms contS_translate_real

/-- **OS1 on all of `ℝ⁴` at bounded renormalisation data.**

DERIVED: `0` is the excluded colour count and the sign of `d`; `4` in `Fin 4` is the spacetime
dimension. -/
theorem contS_translate_real_of_bounded (hN : N ≠ 0) (ρ : Renorm N)
    (hZ : ∀ O, ∃ B : ℝ, ∀ k, |ρ.Z k O| ≤ B) (hc : ∀ O, ∃ B : ℝ, ∀ k, |ρ.c k O| ≤ B)
    {ι : Type} [Fintype ι] (F : ι → SField N) (hU : ∀ i, UniformContinuous (F i).2.1)
    {d : ℝ} (hd : 0 < d) (hsep : ContinuumSep.FamSep d F) (v : Fin 4 → ℝ) :
    contS hN ρ (fun i => ((F i).1, (F i).2.translate v)) = contS hN ρ F :=
  contS_translate_real hN ρ (supContinuousSep_of_bounded hN ρ hZ hc) F hU hd hsep v

#print axioms contS_translate_real_of_bounded

end ContinuityS

/-! ## 6. Rotations -/

section Rotation

variable {N : ℕ}

/-- **Euclidean rotation invariance on separated families of uniformly continuous test functions
(stated, not proved).** For every `Rot ∈ SO(4)` and every family whose fields lie in `Φ`, whose test
functions are uniformly continuous, and which with its rotated family is `d`-separated for some
`d > 0`, composing every test function with `Rot` leaves the continuum Schwinger function unchanged.
It is `ContinuumSchwinger.RotationInvariant` with two hypotheses added
(`rotationInvariantSep_of_rotationInvariant`). The hypercubic instances hold at `HypScalar` fields
(`rotation_hypercubic`); the rotations of `SO(4)` that are not signed permutations are open.

DERIVED: `0` is the excluded colour count and the sign of `d`; `4` is the dimension, of `SO(4)`. -/
def RotationInvariantSep (hN : N ≠ 0) (ρ : Renorm N) (Φ : Set (LField (MassGap.SUN.SU N))) :
    Prop :=
  ∀ Rot : Matrix (Fin 4) (Fin 4) ℝ, Rot ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] (F F' : ι → SField N), (∀ i, (F i).1 ∈ Φ) →
      (∀ i, UniformContinuous (F i).2.1) →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.FamSep d F ∧ ContinuumSep.FamSep d F') →
      (∀ i, (F' i).1 = (F i).1) → (∀ i y, (F' i).2.1 y = (F i).2.1 (Rot.mulVec y)) →
      contS hN ρ F' = contS hN ρ F

/-- **`RotationInvariantSep` is weaker than `RotationInvariant`.**

DERIVED: `0` is the excluded colour count. -/
theorem rotationInvariantSep_of_rotationInvariant (hN : N ≠ 0) (ρ : Renorm N)
    (Φ : Set (LField (MassGap.SUN.SU N))) (h : RotationInvariant hN ρ Φ) :
    RotationInvariantSep hN ρ Φ := by
  intro Rot hRot ι _ F F' hΦ _ _ hf ht
  exact h Rot hRot ι F F' hΦ hf ht

#print axioms rotationInvariantSep_of_rotationInvariant

/-- **The hypercubic rotations.** For every matrix acting on `ℝ⁴` as a signed permutation of the
coordinates, `Rot y = (sᵢ y_{σ i})ᵢ`, and every family of `HypScalar` fields, composing every test
function with `Rot`, fields unchanged, leaves the continuum Schwinger function unchanged, at data
compatible with every generator. No continuity or separation is used. This is the conclusion of
`RotationInvariantSep` on the signed permutation matrices of `SO(4)`, and of `O(4)`.

DERIVED: `0` is the excluded colour count; `1` and `-1` are the signs; `4` is the dimension. -/
theorem rotation_hypercubic (hN : N ≠ 0) (ρ : Renorm N) (hRefl : ∀ τ : Fin 4, ρ.ReflCompat τ)
    (hAxis : ∀ e : Equiv.Perm (Fin 4), axisCompat ρ e) (Rot : Matrix (Fin 4) (Fin 4) ℝ)
    (hRot : ∃ (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ), (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ y i, Rot.mulVec y i = s i * y (σ i))
    {ι : Type} [Fintype ι] (F F' : ι → SField N) (hΦ : ∀ i, HypScalar (F i).1)
    (hfield : ∀ i, (F' i).1 = (F i).1) (htest : ∀ i y, (F' i).2.1 y = (F i).2.1 (Rot.mulVec y)) :
    contS hN ρ F' = contS hN ρ F := by
  obtain ⟨σ, s, hs, hR⟩ := hRot
  refine contS_signed hN ρ hRefl hAxis σ s hs F F' hΦ hfield (fun i y => ?_)
  rw [htest i y]
  exact congrArg (F i).2.1 (funext fun j => hR y j)

#print axioms rotation_hypercubic

/-- **What rotation invariance leaves open (stated).** `RotationInvariantSep` at the `HypScalar`
fields, for the rotations that do not act as signed permutations: the hypercubic ones are
`rotation_hypercubic`.

DERIVED: `0` is the excluded colour count and the sign of `d`; `1` and `-1` are the signs; `4` is the
dimension, of `SO(4)`. -/
def RotationOpen (hN : N ≠ 0) (ρ : Renorm N) : Prop :=
  ∀ Rot : Matrix (Fin 4) (Fin 4) ℝ, Rot ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ →
    (¬ ∃ (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ), (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ y i, Rot.mulVec y i = s i * y (σ i)) →
    ∀ (ι : Type) [Fintype ι] (F F' : ι → SField N), (∀ i, HypScalar (F i).1) →
      (∀ i, UniformContinuous (F i).2.1) →
      (∃ d : ℝ, 0 < d ∧ ContinuumSep.FamSep d F ∧ ContinuumSep.FamSep d F') →
      (∀ i, (F' i).1 = (F i).1) → (∀ i y, (F' i).2.1 y = (F i).2.1 (Rot.mulVec y)) →
      contS hN ρ F' = contS hN ρ F

/-- **The open part is all that is missing**: at data compatible with every generator,
`RotationOpen` gives `RotationInvariantSep` at the `HypScalar` fields.

DERIVED: `0` is the excluded colour count; `4` is the dimension, of `SO(4)`. -/
theorem rotationInvariantSep_of_open (hN : N ≠ 0) (ρ : Renorm N)
    (hRefl : ∀ τ : Fin 4, ρ.ReflCompat τ) (hAxis : ∀ e : Equiv.Perm (Fin 4), axisCompat ρ e)
    (hO : RotationOpen hN ρ) : RotationInvariantSep hN ρ {O | HypScalar O} := by
  intro Rot hRot ι _ F F' hΦ hU hsep hf ht
  by_cases hsgn : ∃ (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℝ), (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ y i, Rot.mulVec y i = s i * y (σ i)
  · exact rotation_hypercubic hN ρ hRefl hAxis Rot hsgn F F' hΦ hf ht
  · exact hO Rot hRot hsgn ι F F' hΦ hU hsep hf ht

#print axioms rotationInvariantSep_of_open

end Rotation

end MassGap.ContinuumHypercubic
