import Mathlib
import MassGap.LinkGram
import MassGap.ReflectionStrong
import MassGap.WilsonTransfer
import MassGap.ReadRoute

/-!
# MassGap.PeriodicState — an infinite-volume state at every coupling, from periodic lattices

The transfer data on the gauge-invariant half-space algebra of `ℤ⁴`
(`GaugeInvariantAlgebra.gaugeInvTransferData`) and its positivity read four facts off a state `ν`:
reflection invariance and reflection positivity at the constant `2p` (mirror plane `x_τ = p`),
invariance under the unit shift along `τ`, and reflection positivity at the constant `2p - 1` (mirror
between `x_τ = p - 1` and `x_τ = p`). This module produces one `ν` carrying
all four at every `β ≥ 0`, with no uniqueness, convergence or boundary-decay input.

## The construction

`torusState hN M β` is the periodic Wilson Gibbs state of extent `M + 1`, read on `ℤ⁴` observables
through `InfiniteLattice.pullback`: `f ↦ ReflectPositive.EW N β (fun W => f (pullback M W))`.
`periodicState hN β` is a limit of `torusState hN (2k + 1) β` along an ultrafilter finer than
`atTop` (`DLRLimit.exists_limit_state`, weak-* compactness); `tendsto_periodicState` states that
convergence.

Each periodic state has the four facts exactly or eventually in the extent. The two invariances pass
to a limit along any non-trivial filter; the two positivities pass along any non-trivial filter
finer than `atTop`:

* **shift invariance, exact at every extent** — `pullback_ishiftConf` intertwines the `ℤ⁴` shift with
  the periodic one, and `WilsonTransfer.expect_shift_invariant` is the periodic Gibbs state's own
  invariance (`torusState_shift`);
* **reflection invariance at every constant, exact** — `pullback_ireflConf` intertwines
  `LatticeReflection.ireflConf τ c` with `Reflect.reflConf τ (finMod M c)`, and
  `Reflect.expect_reflect_invariant` is the periodic invariance (`torusState_reflInvariant`);
* **reflection positivity at `2p`, eventually** — an observable of `halfSpaceAlg τ p` is local on a
  finite set of depth `K` above the plane; at half-extent `k + 1 > K` it reads the periodic slab
  `blkS ∪ blkR` about `finMod p`, where `ReflectionStrong.wilson_expect_nonneg_module` holds at every
  real `β` (`torusState_reflPositive_even_eventually`);
* **reflection positivity at `2p - 1`, eventually** — the same observable reads the periodic link
  slab `oblkS` about `finMod (p - 1)` once `k > K`, where `LinkGram.gram_refl_positive` holds at
  `0 ≤ β` (`torusState_reflPositive_odd_eventually`).

The periodic lattice is stable under every mirror and every translation, so no second family and no
identification of two limits is needed. `ReflectionHalfSpace.eq_empty_of_stable_two_mirrors` says a
finite set of `ℤ⁴` links stable under two adjacent mirrors is empty; the periodic states are not
indexed by finite sets of `ℤ⁴` links, so it does not apply.

## What it gives

`periodic_gap_of_reads`: at every `β ≥ 0`, if every vector of the gauge-invariant GNS space built on
`periodicState hN β` that is orthogonal to the vacuum reads below the floor at aperture `2k + 1`, the
vacuum complement is contracted at rate `ρ < 1` with `ρ^{k+1} = 12(1 − 3^{−1/4})/8` — the conclusion
of `WilsonReadGap.wilson_gap_of_reads`, at the periodic state in place of the `mixCube` limit.
`periodic_clay_gap_of_reads` is the spectral form alone, without the contraction and the non-zero
vacuum complement that `ReadRoute.ClayGapAt` carries; `PeriodicContent.PeriodicClayGapAt` adds both
at the periodic state. Besides `N ≠ 0` and `0 ≤ β`, the reads are the only hypothesis.

`gaugeInv_gap_of_reads_of_state_facts` is the gap from the four facts of any state;
`gaugeInv_gap_of_reads_of_common_limit` is it for a state that is a limit of the even free cube
family along one filter and of the odd one along another — the free-boundary form, whose common-limit
hypothesis compactness does not supply.

## Scope

`periodicState hN β` is a limit of periodic Wilson Gibbs states along an ultrafilter. Nothing here
shows that it is the `atTop` limit of the free-boundary states `FreeLimit.exists_tendsto_stateFree`
produces at strong coupling, nor that it satisfies the DLR equations, nor that its vacuum complement
is non-zero; the gap statements do not use any of these.

The invariance facts use only the symmetry of the weight and of Haar measure. The positivity facts
use the Wilson structure: the action split, and at the odd constant the crossing kernel at `β ≥ 0`.
-/

namespace MassGap.PeriodicState

open MassGap MassGap.InfiniteLattice MassGap.GNSHilbert

variable {N : ℕ}

/-! ## 1. Reduction modulo the extent is additive -/

section Arithmetic

/-- `finMod M 0 = 0`.

DERIVED: `0` is the additive identity on both sides, in `ℤ` and in `Fin (M + 1)`; the `1` in
`M + 1` is `InfiniteLattice.finMod`'s successor writing the extent. -/
theorem finMod_zero (M : ℕ) : finMod M 0 = 0 := by
  apply Fin.ext
  simp [finMod]

#print axioms finMod_zero

/-- `finMod M (x + y) = finMod M x + finMod M y`: reduction modulo the extent is additive. Integer
induction on `y` from `finMod_zero` and `InfiniteLattice.finMod_add_one`.

DERIVED: no numeral in the statement; `M` is the caller's. -/
theorem finMod_add (M : ℕ) (x y : ℤ) : finMod M (x + y) = finMod M x + finMod M y := by
  induction y with
  | zero => rw [add_zero, finMod_zero, add_zero]
  | succ i ih => rw [← add_assoc, finMod_add_one, finMod_add_one, ih, add_assoc]
  | pred i ih =>
    have h1 : finMod M (x + (-(i : ℤ) - 1)) + 1 = finMod M (x + -(i : ℤ)) := by
      rw [← finMod_add_one]
      congr 1
      ring
    have h2 : finMod M (-(i : ℤ) - 1) + 1 = finMod M (-(i : ℤ)) := by
      rw [← finMod_add_one]
      congr 1
      ring
    rw [eq_sub_of_add_eq h1, ih, eq_sub_of_add_eq h2, add_sub_assoc]

#print axioms finMod_add

/-- `finMod M 1 = 1`.

DERIVED: `1` is the unit step, in `ℤ` and in `Fin (M + 1)`, and the successor in `M + 1`. -/
theorem finMod_one (M : ℕ) : finMod M 1 = 1 := by
  have h := finMod_add_one M 0
  rwa [zero_add, finMod_zero, zero_add] at h

#print axioms finMod_one

/-- `finMod M (-x) = -finMod M x`.

DERIVED: no numeral in the statement. -/
theorem finMod_neg (M : ℕ) (x : ℤ) : finMod M (-x) = -finMod M x := by
  have h := finMod_add M x (-x)
  rw [add_neg_cancel, finMod_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

#print axioms finMod_neg

/-- `finMod M (x - y) = finMod M x - finMod M y`.

DERIVED: no numeral in the statement. -/
theorem finMod_sub (M : ℕ) (x y : ℤ) : finMod M (x - y) = finMod M x - finMod M y := by
  rw [sub_eq_add_neg x y, finMod_add, finMod_neg, sub_eq_add_neg]

#print axioms finMod_sub

/-- The level `ActionSplit.lv (finMod M y) (finMod M x)` of a reduced coordinate above a reduced
base is `x - y`, cast to `ℤ`, whenever `0 ≤ x - y < M + 1`.

DERIVED: `0` is the lower end of the residue range, and `1` the successor writing the extent
`M + 1`; both are `InfiniteLattice.finMod`'s. -/
theorem lv_finMod (M : ℕ) (x y : ℤ) (h0 : 0 ≤ x - y) (h1 : x - y < (M : ℤ) + 1) :
    ((MassGap.ActionSplit.lv (finMod M y) (finMod M x) : ℕ) : ℤ) = x - y := by
  have hsub : finMod M x - finMod M y = finMod M (x - y) := (finMod_sub M x y).symm
  show (((finMod M x - finMod M y).val : ℕ) : ℤ) = x - y
  rw [hsub]
  show ((((x - y) % ((M : ℤ) + 1)).toNat : ℕ) : ℤ) = x - y
  rw [Int.emod_eq_of_lt h0 h1, Int.toNat_of_nonneg h0]

#print axioms lv_finMod

/-- Every finite link set has a depth bound above a plane: a `K` with `l.2 τ - p ≤ K` for every
`l ∈ S`.

DERIVED: `4` is the spacetime dimension, the range of `τ`; `2` is the projection `l.2` onto the base
site, not a numeral. -/
theorem exists_depth_bound (τ : Fin 4) (p : ℤ) (S : Finset ILink) :
    ∃ K : ℕ, ∀ l ∈ S, l.2 τ - p ≤ (K : ℤ) :=
  ⟨S.sup (fun l => (l.2 τ - p).toNat), fun l hl =>
    le_trans (Int.self_le_toNat _)
      (by exact_mod_cast Finset.le_sup (f := fun l : ILink => (l.2 τ - p).toNat) hl)⟩

#print axioms exists_depth_bound

end Arithmetic

/-! ## 2. The periodic pullback intertwines the lattice symmetries -/

section Covariance

/-- `siteMod M (ireflSite τ c x) = reflSite τ (finMod M c) (siteMod M x)`: reducing a reflected site
is reflecting the reduced site about the reduced constant.

DERIVED: `4` is the spacetime dimension, the range of `τ`. -/
theorem siteMod_ireflSite (M : ℕ) (τ : Fin 4) (c : ℤ) (x : ISite) :
    siteMod M (MassGap.LatticeReflection.ireflSite τ c x)
      = MassGap.Reflect.reflSite τ (finMod M c) (siteMod M x) := by
  funext j
  by_cases h : j = τ
  · rw [h]
    show finMod M (MassGap.LatticeReflection.ireflSite τ c x τ)
      = MassGap.Reflect.reflSite τ (finMod M c) (siteMod M x) τ
    rw [MassGap.LatticeReflection.ireflSite_axis, MassGap.Reflect.reflSite_axis]
    exact finMod_sub M c (x τ)
  · show finMod M (MassGap.LatticeReflection.ireflSite τ c x j)
      = MassGap.Reflect.reflSite τ (finMod M c) (siteMod M x) j
    rw [MassGap.Reflect.reflSite_of_ne h]
    show finMod M (Function.update x τ (c - x τ) j) = finMod M (x j)
    rw [Function.update_of_ne h]

#print axioms siteMod_ireflSite

/-- `linkMod M (ireflLink τ c l) = reflLink τ (finMod M c) (linkMod M l)`: both reflect the base
about `c - 1` on a `τ`-link and about `c` otherwise, and `finMod M (c - 1) = finMod M c - 1`.

DERIVED: `4` is the spacetime dimension, the range of `τ`. -/
theorem linkMod_ireflLink (M : ℕ) (τ : Fin 4) (c : ℤ) (l : ILink) :
    linkMod M (MassGap.LatticeReflection.ireflLink τ c l)
      = MassGap.Reflect.reflLink τ (finMod M c) (linkMod M l) := by
  by_cases h : l.1 = τ
  · rw [MassGap.LatticeReflection.ireflLink_eq_axis τ c h]
    have h' : (linkMod M l).1 = τ := h
    unfold MassGap.Reflect.reflLink
    rw [if_pos h']
    show (l.1, siteMod M (MassGap.LatticeReflection.ireflSite τ (c - 1) l.2))
      = (l.1, MassGap.Reflect.reflSite τ (finMod M c - 1) (siteMod M l.2))
    rw [siteMod_ireflSite, finMod_sub, finMod_one]
  · rw [MassGap.LatticeReflection.ireflLink_eq_transverse τ c h]
    have h' : (linkMod M l).1 ≠ τ := h
    unfold MassGap.Reflect.reflLink
    rw [if_neg h']
    show (l.1, siteMod M (MassGap.LatticeReflection.ireflSite τ c l.2))
      = (l.1, MassGap.Reflect.reflSite τ (finMod M c) (siteMod M l.2))
    rw [siteMod_ireflSite]

#print axioms linkMod_ireflLink

/-- `ireflConf τ c (pullback M W) = pullback M (reflConf τ (finMod M c) W)`: the periodic
configuration's reflection about `c` on `ℤ⁴` is the pullback of the periodic reflection about
`finMod M c`, dagger included.

DERIVED: `4` is the spacetime dimension; the `1` in `M + 1` is `finMod`'s successor. -/
theorem pullback_ireflConf (M : ℕ) (τ : Fin 4) (c : ℤ)
    (W : WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) :
    MassGap.LatticeReflection.ireflConf τ c (pullback M W)
      = pullback M (MassGap.Reflect.reflConf τ (finMod M c) W) := by
  funext l
  show (if l.1 = τ then (W (linkMod M (MassGap.LatticeReflection.ireflLink τ c l)))⁻¹
      else W (linkMod M (MassGap.LatticeReflection.ireflLink τ c l)))
    = (if (linkMod M l).1 = τ
        then (W (MassGap.Reflect.reflLink τ (finMod M c) (linkMod M l)))⁻¹
        else W (MassGap.Reflect.reflLink τ (finMod M c) (linkMod M l)))
  rw [linkMod_ireflLink]
  rfl

#print axioms pullback_ireflConf

/-- `linkMod M (ishiftLink μ l) = shiftLink μ (linkMod M l)`, from
`InfiniteLattice.siteMod_ishift`.

DERIVED: `4` is the spacetime dimension, the range of `μ`. -/
theorem linkMod_ishiftLink (M : ℕ) (μ : Fin 4) (l : ILink) :
    linkMod M (MassGap.InfiniteShift.ishiftLink μ l)
      = MassGap.WilsonTransfer.shiftLink μ (linkMod M l) := by
  show (l.1, siteMod M (ishift μ l.2)) = (l.1, WilsonHypercubic.shift μ (siteMod M l.2))
  rw [siteMod_ishift]

#print axioms linkMod_ishiftLink

/-- `ishiftConf μ (pullback M W) = pullback M (shiftConf μ W)`: the unit shift on `ℤ⁴` of a periodic
configuration is the pullback of the periodic shift.

DERIVED: `4` is the spacetime dimension; the `1` in `M + 1` is `finMod`'s successor. -/
theorem pullback_ishiftConf (M : ℕ) (μ : Fin 4)
    (W : WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) :
    MassGap.InfiniteShift.ishiftConf μ (pullback M W)
      = pullback M (MassGap.WilsonTransfer.shiftConf μ W) := by
  funext l
  show W (linkMod M (MassGap.InfiniteShift.ishiftLink μ l))
    = W (MassGap.WilsonTransfer.shiftLink μ (linkMod M l))
  rw [linkMod_ishiftLink]

#print axioms pullback_ishiftConf

/-- `pullback M` is measurable: each coordinate of the image is a coordinate of the source.

DERIVED: no numeral in the statement. -/
theorem measurable_pullback (M : ℕ) :
    Measurable (pullback (G := MassGap.SUN.SU N) M) :=
  measurable_pi_lambda _ (fun l => measurable_pi_apply (linkMod M l))

#print axioms measurable_pullback

end Covariance

/-! ## 3. The periodic Wilson state on `ℤ⁴` observables -/

section Torus

/-- A continuous observable of `ℤ⁴` read on the periodic lattice of extent `M + 1`:
`W ↦ f (pullback M W)`.

DERIVED: `4` is the spacetime dimension; the `1` in `M + 1` is `finMod`'s successor. -/
noncomputable def torusObs (M : ℕ) (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    (WilsonHypercubic.Link 4 (M + 1) → MassGap.SUN.SU N) → ℝ :=
  fun W => f (pullback M W)

/-- `torusObs M f` is measurable: `f` is continuous and `pullback M` is measurable.

DERIVED: no numeral in the statement. -/
theorem measurable_torusObs (M : ℕ) (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Measurable (torusObs M f) :=
  f.continuous.measurable.comp (measurable_pullback M)

#print axioms measurable_torusObs

/-- **The periodic Wilson Gibbs state of extent `M + 1`, on `ℤ⁴` observables.**
`f ↦ ReflectPositive.EW N β (torusObs M f)`, the `SU(N)` Wilson Gibbs expectation on the periodic
four-dimensional lattice of extent `M + 1` of `f` read through `pullback M`. Additivity is
`WilsonReal.wilsonSystem_expect_add` with the integrability of bounded measurable observables,
homogeneity `wilsonSystem_expect_smul`, positivity `wilsonSystem_expect_nonneg`, and normalisation
`wilsonSystem_expect_one`.

DERIVED: `4` is the spacetime dimension; the `1` in `M + 1` is `finMod`'s successor; `0` is the
excluded rank in `hN`. -/
noncomputable def torusState (hN : N ≠ 0) (M : ℕ) (β : ℝ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) where
  toFun f := MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M f)
  map_add' f g := by
    obtain ⟨Cf, hCf⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
    obtain ⟨Cg, hCg⟩ := MassGap.InfiniteLattice.bounded_of_continuous g.continuous
    exact MassGap.WilsonReal.wilsonSystem_expect_add
      (WilsonHypercubic.bd (d := 4) (n := M + 1)) β (torusObs M f) (torusObs M g)
      (MassGap.WilsonReal.wilsonSystem_mul_boltz_integrable hN _ β _
        (measurable_torusObs M f) Cf (fun W => hCf _))
      (MassGap.WilsonReal.wilsonSystem_mul_boltz_integrable hN _ β _
        (measurable_torusObs M g) Cg (fun W => hCg _))
  map_smul' c f :=
    MassGap.WilsonReal.wilsonSystem_expect_smul
      (WilsonHypercubic.bd (d := 4) (n := M + 1)) β c (torusObs M f)
  nonneg' f hf :=
    MassGap.WilsonReal.wilsonSystem_expect_nonneg hN
      (WilsonHypercubic.bd (d := 4) (n := M + 1)) β (torusObs M f) (fun W => hf _)
  one' := MassGap.WilsonReal.wilsonSystem_expect_one hN
    (WilsonHypercubic.bd (d := 4) (n := M + 1)) β

#print axioms torusState

/-- `torusObs M (ishiftObsL τ f)` is `torusObs M f` precomposed with the periodic shift, by
`pullback_ishiftConf`.

DERIVED: `4` is the spacetime dimension. -/
theorem torusObs_shift (M : ℕ) (τ : Fin 4)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    torusObs M (MassGap.ReflectionShift.ishiftObsL τ f)
      = fun W => torusObs M f (MassGap.WilsonTransfer.shiftConf τ W) := by
  funext W
  show f (MassGap.InfiniteShift.ishiftConf τ (pullback M W))
    = f (pullback M (MassGap.WilsonTransfer.shiftConf τ W))
  rw [pullback_ishiftConf]

#print axioms torusObs_shift

/-- `torusObs M (θ_c f)` is `torusObs M f` precomposed with the periodic reflection about
`finMod M c`, by `pullback_ireflConf`.

DERIVED: `4` is the spacetime dimension. -/
theorem torusObs_refl (M : ℕ) (τ : Fin 4) (c : ℤ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    torusObs M ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ c).θ f)
      = fun W => torusObs M f (MassGap.Reflect.reflConf τ (finMod M c) W) := by
  funext W
  show f (MassGap.LatticeReflection.ireflConf τ c (pullback M W))
    = f (pullback M (MassGap.Reflect.reflConf τ (finMod M c) W))
  rw [pullback_ireflConf]

#print axioms torusObs_refl

/-- `torusObs M (θ_c f * f) = fun W => torusObs M f W * torusObs M f (reflConf τ (finMod M c) W)`:
the reflection pairing of `f` on `ℤ⁴`, read on the periodic lattice.

DERIVED: `4` is the spacetime dimension. -/
theorem torusObs_refl_mul (M : ℕ) (τ : Fin 4) (c : ℤ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    torusObs M
        ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ c).θ f * f)
      = fun W => torusObs M f W * torusObs M f (MassGap.Reflect.reflConf τ (finMod M c) W) := by
  funext W
  show f (MassGap.LatticeReflection.ireflConf τ c (pullback M W)) * f (pullback M W)
    = f (pullback M W) * f (pullback M (MassGap.Reflect.reflConf τ (finMod M c) W))
  rw [pullback_ireflConf, mul_comm]

#print axioms torusObs_refl_mul

/-- **Every periodic state is shift invariant**: `torusState hN M β (ishiftObsL τ f) =
torusState hN M β f`, at every extent, coupling and direction. `torusObs_shift` and
`WilsonTransfer.expect_shift_invariant`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem torusState_shift (hN : N ≠ 0) (M : ℕ) (β : ℝ) (τ : Fin 4)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    torusState hN M β (MassGap.ReflectionShift.ishiftObsL τ f) = torusState hN M β f := by
  show MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β
      (torusObs M (MassGap.ReflectionShift.ishiftObsL τ f))
    = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M f)
  rw [torusObs_shift]
  exact MassGap.WilsonTransfer.expect_shift_invariant N τ β (torusObs M f)

#print axioms torusState_shift

/-- **Every periodic state is reflection invariant at every constant**: `IsReflectionInvariant
(latticeReflection τ c) (torusState hN M β)` for every `τ` and every `c : ℤ`, of either parity.
`torusObs_refl` and `Reflect.expect_reflect_invariant` at `finMod M c`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem torusState_reflInvariant (hN : N ≠ 0) (M : ℕ) (β : ℝ) (τ : Fin 4) (c : ℤ) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ c)
      (torusState hN M β) := by
  intro f
  show MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β
      (torusObs M ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ c).θ f))
    = MassGap.ReflectPositive.EW (d := 4) (n := M + 1) N β (torusObs M f)
  rw [torusObs_refl]
  exact MassGap.Reflect.expect_reflect_invariant N τ (finMod M c) β (torusObs M f)

#print axioms torusState_reflInvariant

end Torus

/-! ## 4. Reflection positivity of the periodic states, eventually in the extent -/

section Positivity

/-- **An observable of the half-space reads the periodic site slab.** If `f` is local on a finite
`S` inside `posHalf τ p` whose links are based at most `k` above the plane (`l.2 τ - p ≤ k`, so a
`τ`-link reaches `k + 1`), then `torusObs (2k + 1) f` belongs to
`LogConvex.localObs (blkS τ a (k + 1)) (blkR τ a (k + 1))` at `a = finMod (2k + 1) p`: it is
measurable, bounded, and determined by the slab and its two planes.

DERIVED: the extent `2k + 1 + 1 = 2(k + 1)` is even because a periodic reflection needs a plane and
its opposite half the extent apart (`ReflectionStrong.wilson_expect_nonneg_module`'s `n = 2m`), and
`k + 1` is that half-extent; `4` is the spacetime dimension. -/
theorem torusObs_mem_localObs_even (k : ℕ) (τ : Fin 4) (p : ℤ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (S : Finset ILink)
    (hS : (S : Set ILink) ⊆ MassGap.HalfSpaceAlgebra.posHalf τ p)
    (hloc : IsLocalOn S (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ))
    (hk : ∀ l ∈ S, l.2 τ - p ≤ (k : ℤ)) :
    torusObs (2 * k + 1) f
      ∈ MassGap.LogConvex.localObs
          (MassGap.ActionSplit.blkS τ (finMod (2 * k + 1) p) (k + 1))
          (MassGap.ActionSplit.blkR τ (finMod (2 * k + 1) p) (k + 1)) := by
  refine MassGap.LogConvex.mem_localObs.mpr
    ⟨measurable_torusObs (2 * k + 1) f, ?_, fun W W' hSeq hReq => ?_⟩
  · obtain ⟨C, hC⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
    exact ⟨C, fun W => hC _⟩
  · show f (pullback (2 * k + 1) W) = f (pullback (2 * k + 1) W')
    refine hloc (pullback (2 * k + 1) W) (pullback (2 * k + 1) W') (fun l hl => ?_)
    have hp : p ≤ l.2 τ := hS (Finset.mem_coe.mpr hl)
    have hle : l.2 τ - p ≤ (k : ℤ) := hk l hl
    have hlv : ((MassGap.ActionSplit.lv (finMod (2 * k + 1) p)
        (finMod (2 * k + 1) (l.2 τ)) : ℕ) : ℤ) = l.2 τ - p :=
      lv_finMod (2 * k + 1) (l.2 τ) p (by omega) (by push_cast; omega)
    have hb : MassGap.ActionSplit.lv (finMod (2 * k + 1) p) ((linkMod (2 * k + 1) l).2 τ) ≤ k := by
      show MassGap.ActionSplit.lv (finMod (2 * k + 1) p) (finMod (2 * k + 1) (l.2 τ)) ≤ k
      omega
    have hmem : linkMod (2 * k + 1) l
        ∈ MassGap.ActionSplit.blkS τ (finMod (2 * k + 1) p) (k + 1)
          ∪ MassGap.ActionSplit.blkR τ (finMod (2 * k + 1) p) (k + 1) := by
      rw [MassGap.ActionSplit.mem_blkS_union_blkR]
      split_ifs <;> omega
    show W (linkMod (2 * k + 1) l) = W' (linkMod (2 * k + 1) l)
    rcases Finset.mem_union.mp hmem with h | h
    · exact hSeq _ h
    · exact hReq _ h

#print axioms torusObs_mem_localObs_even

/-- **An observable of the half-space reads the periodic link slab.** If `f` is local on a finite
`S` inside `posHalf τ p` with `l.2 τ - p + 1 ≤ k` on `S`, then `torusObs (2k + 1) f` takes equal
values at any two periodic configurations that agree on `OddLagSplit.oblkS τ a (k + 1)` at
`a = finMod (2k + 1) (p - 1)`.

DERIVED: the extent `2k + 1 + 1 = 2(k + 1)` is even, with half-extent `k + 1`, for the same reason as
in `torusObs_mem_localObs_even`; `1` in `p - 1` makes `a + a + 1` the reduction of the link-reflection
constant `2p - 1` (mirror between `x_τ = p - 1` and `x_τ = p`), and in `l.2 τ - p + 1` it is the
level of `x_τ = p` above the base `p - 1`; `4` is the spacetime dimension. -/
theorem torusObs_local_oblkS (k : ℕ) (τ : Fin 4) (p : ℤ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) (S : Finset ILink)
    (hS : (S : Set ILink) ⊆ MassGap.HalfSpaceAlgebra.posHalf τ p)
    (hloc : IsLocalOn S (f : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ))
    (hk : ∀ l ∈ S, l.2 τ - p + 1 ≤ (k : ℤ)) :
    ∀ W W' : WilsonHypercubic.Link 4 (2 * k + 1 + 1) → MassGap.SUN.SU N,
      (∀ l ∈ MassGap.OddLagSplit.oblkS τ (finMod (2 * k + 1) (p - 1)) (k + 1), W l = W' l) →
        torusObs (2 * k + 1) f W = torusObs (2 * k + 1) f W' := by
  intro W W' hSeq
  show f (pullback (2 * k + 1) W) = f (pullback (2 * k + 1) W')
  refine hloc (pullback (2 * k + 1) W) (pullback (2 * k + 1) W') (fun l hl => ?_)
  have hp : p ≤ l.2 τ := hS (Finset.mem_coe.mpr hl)
  have hle : l.2 τ - p + 1 ≤ (k : ℤ) := hk l hl
  have hlv : ((MassGap.ActionSplit.lv (finMod (2 * k + 1) (p - 1))
      (finMod (2 * k + 1) (l.2 τ)) : ℕ) : ℤ) = l.2 τ - (p - 1) :=
    lv_finMod (2 * k + 1) (l.2 τ) (p - 1) (by omega) (by push_cast; omega)
  have hb0 : 0 < MassGap.ActionSplit.lv (finMod (2 * k + 1) (p - 1))
      ((linkMod (2 * k + 1) l).2 τ) := by
    show 0 < MassGap.ActionSplit.lv (finMod (2 * k + 1) (p - 1)) (finMod (2 * k + 1) (l.2 τ))
    omega
  have hb1 : MassGap.ActionSplit.lv (finMod (2 * k + 1) (p - 1))
      ((linkMod (2 * k + 1) l).2 τ) < k + 1 := by
    show MassGap.ActionSplit.lv (finMod (2 * k + 1) (p - 1)) (finMod (2 * k + 1) (l.2 τ)) < k + 1
    omega
  have hmem : linkMod (2 * k + 1) l
      ∈ MassGap.OddLagSplit.oblkS τ (finMod (2 * k + 1) (p - 1)) (k + 1) := by
    rw [MassGap.OddLagSplit.mem_oblkS]
    split_ifs
    · exact ⟨hb0, hb1⟩
    · exact ⟨hb0, hb1.le⟩
  show W (linkMod (2 * k + 1) l) = W' (linkMod (2 * k + 1) l)
  exact hSeq _ hmem

#print axioms torusObs_local_oblkS

/-- **Site-reflection positivity of the periodic states, eventually.** For `f` in
`halfSpaceAlg τ p`, at every real `β`, eventually in `k`:
`0 ≤ torusState hN (2k + 1) β (θ_{2p} f * f)`. At half-extent `k + 1` beyond the depth of `f`'s
support, `torusObs_mem_localObs_even` places `f` in the periodic slab algebra about
`finMod (2k + 1) p`, `ReflectionStrong.wilson_expect_nonneg_module` is the positivity there, and
`finMod (2k + 1) (2p) = finMod p + finMod p` matches the two reflection constants.

DERIVED: `2` in `2 * p` is the plane-to-constant doubling; the extent index `2k + 1` makes the
periodic extent `2(k + 1)` even; `0` is the excluded rank in `hN` and the sign concluded; `4` is the
spacetime dimension. -/
theorem torusState_reflPositive_even_eventually (hN : N ≠ 0) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hf : f ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) :
    ∀ᶠ k : ℕ in Filter.atTop,
      0 ≤ torusState hN (2 * k + 1) β
        ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p)).θ f
          * f) := by
  obtain ⟨S, hS, hloc⟩ := MassGap.HalfSpaceAlgebra.mem_halfSpaceAlg.mp hf
  obtain ⟨K, hK⟩ := exists_depth_bound τ p S
  refine Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
  have hkS : ∀ l ∈ S, l.2 τ - p ≤ (k : ℤ) := fun l hl => by
    have := hK l hl
    omega
  have hrp := MassGap.ReflectionStrong.wilson_expect_nonneg_module hN τ (finMod (2 * k + 1) p)
    (k + 1) (by omega) (by omega) β (torusObs_mem_localObs_even k τ p f S hS hloc hkS)
  have ha : finMod (2 * k + 1) (2 * p) = finMod (2 * k + 1) p + finMod (2 * k + 1) p := by
    rw [two_mul p, finMod_add]
  show 0 ≤ MassGap.ReflectPositive.EW (d := 4) (n := 2 * k + 1 + 1) N β
    (torusObs (2 * k + 1)
      ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p)).θ f * f))
  rw [torusObs_refl_mul, ha]
  exact hrp

#print axioms torusState_reflPositive_even_eventually

/-- **Link-reflection positivity of the periodic states, eventually.** For `f` in
`halfSpaceAlg τ p`, at `0 ≤ β`, eventually in `k`:
`0 ≤ torusState hN (2k + 1) β (θ_{2p-1} f * f)`. Beyond the depth of `f`'s support,
`torusObs_local_oblkS` makes `f` read only the periodic link slab about `finMod (2k + 1) (p - 1)`,
`LinkGram.gram_refl_positive` is the positivity there, and
`finMod (2k + 1) (2p - 1) = finMod (p - 1) + finMod (p - 1) + 1` matches the two constants.

DERIVED: `2` and `1` in `2 * p - 1` are the plane-to-constant doubling and the half-step to the link
plane; the extent index `2k + 1` makes the periodic extent `2(k + 1)` even; `0` is the excluded rank
in `hN`, the sign of the coupling in `hβ` and the sign concluded; `4` is the spacetime dimension. -/
theorem torusState_reflPositive_odd_eventually (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4)
    (p : ℤ) (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
    (hf : f ∈ MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) :
    ∀ᶠ k : ℕ in Filter.atTop,
      0 ≤ torusState hN (2 * k + 1) β
        ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p - 1)).θ f
          * f) := by
  obtain ⟨S, hS, hloc⟩ := MassGap.HalfSpaceAlgebra.mem_halfSpaceAlg.mp hf
  obtain ⟨K, hK⟩ := exists_depth_bound τ p S
  refine Filter.eventually_atTop.mpr ⟨K + 1, fun k hk => ?_⟩
  have hkS : ∀ l ∈ S, l.2 τ - p + 1 ≤ (k : ℤ) := fun l hl => by
    have := hK l hl
    omega
  obtain ⟨C, hC⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  have hrp := MassGap.LinkGram.gram_refl_positive (d := 4) (n := 2 * k + 1 + 1) τ
    (finMod (2 * k + 1) (p - 1)) (k + 1) (torusObs (2 * k + 1) f)
    (measurable_torusObs (2 * k + 1) f) (fun W => hC _)
    (torusObs_local_oblkS k τ p f S hS hloc hkS) hN (by omega) (by omega) (by omega) hβ
  have ha : finMod (2 * k + 1) (2 * p - 1)
      = finMod (2 * k + 1) (p - 1) + finMod (2 * k + 1) (p - 1) + 1 := by
    rw [show (2 * p - 1 : ℤ) = (p - 1) + (p - 1) + 1 by ring, finMod_add, finMod_add, finMod_one]
  show 0 ≤ MassGap.ReflectPositive.EW (d := 4) (n := 2 * k + 1 + 1) N β
    (torusObs (2 * k + 1)
      ((MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p - 1)).θ f
        * f))
  rw [torusObs_refl_mul, ha]
  exact hrp

#print axioms torusState_reflPositive_odd_eventually

end Positivity

/-! ## 5. The four facts pass to every limit of the periodic states -/

section Limit

/-- A limit of the periodic states `torusState hN (2k + 1) β` along any non-trivial filter is
reflection invariant about every constant `c`: each periodic state is
(`torusState_reflInvariant`), and `InfiniteReflection.isReflectionInvariant_of_tendsto` passes it to
the limit.

DERIVED: the extent index `2k + 1` is the even-extent family; `4` is the spacetime dimension; `0` is
the excluded rank in `hN`. -/
theorem reflInvariant_of_tendsto_torus (hN : N ≠ 0) (β : ℝ) (τ : Fin 4) (c : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    {l : Filter ℕ} [l.NeBot]
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ c) ν :=
  MassGap.InfiniteReflection.isReflectionInvariant_of_tendsto htend _
    (Filter.Eventually.of_forall (fun k => torusState_reflInvariant hN (2 * k + 1) β τ c))

#print axioms reflInvariant_of_tendsto_torus

/-- A limit of the periodic states along any non-trivial filter is invariant under the unit shift
along every direction: `ν (ishiftObsL τ f) = ν f`. Each periodic state is (`torusState_shift`), so
the two sequences `k ↦ torusState (ishiftObsL τ f)` and `k ↦ torusState f` coincide and share their
limit.

DERIVED: the extent index `2k + 1` is the even-extent family; `4` is the spacetime dimension; `0` is
the excluded rank in `hN`. -/
theorem shift_of_tendsto_torus (hN : N ≠ 0) (β : ℝ) (τ : Fin 4)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    {l : Filter ℕ} [l.NeBot]
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f) l (nhds (ν f))) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f := by
  intro f
  refine tendsto_nhds_unique (htend (MassGap.ReflectionShift.ishiftObsL τ f)) ?_
  exact (htend f).congr (fun k => (torusState_shift hN (2 * k + 1) β τ f).symm)

#print axioms shift_of_tendsto_torus

/-- A limit of the periodic states along a non-trivial filter finer than `atTop` is reflection
positive at the constant `2p` (mirror plane `x_τ = p`) on `halfSpaceAlg τ p`, at every real `β`:
`torusState_reflPositive_even_eventually` and
`InfiniteReflection.reflPositive_of_eventually_pointwise`.

DERIVED: `2` in `2 * p` is the plane-to-constant doubling; the extent index `2k + 1` is the
even-extent family; `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem reflPositive_even_of_tendsto_torus (hN : N ≠ 0) (β : ℝ) (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ Filter.atTop)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  MassGap.InfiniteReflection.reflPositive_of_eventually_pointwise htend _ _
    (fun f hf => (torusState_reflPositive_even_eventually hN β τ p f hf).filter_mono hl)

#print axioms reflPositive_even_of_tendsto_torus

/-- A limit of the periodic states along a non-trivial filter finer than `atTop` is reflection
positive at the constant `2p - 1` (mirror between `x_τ = p - 1` and `x_τ = p`) on
`halfSpaceAlg τ p`, at `0 ≤ β`:
`torusState_reflPositive_odd_eventually` and
`InfiniteReflection.reflPositive_of_eventually_pointwise`.

DERIVED: `2` and `1` in `2 * p - 1` are the plane-to-constant doubling and the half-step to the link
plane; the extent index `2k + 1` is the even-extent family; `4` is the spacetime dimension; `0` is
the excluded rank in `hN` and the sign of the coupling in `hβ`. -/
theorem reflPositive_odd_of_tendsto_torus (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    {l : Filter ℕ} [l.NeBot] (hl : l ≤ Filter.atTop)
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f) l (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν :=
  MassGap.InfiniteReflection.reflPositive_of_eventually_pointwise htend _ _
    (fun f hf => (torusState_reflPositive_odd_eventually hN hβ τ p f hf).filter_mono hl)

#print axioms reflPositive_odd_of_tendsto_torus

/-- **A limit of the periodic Wilson states exists at every coupling.** There are an ultrafilter
`u` on `ℕ` finer than `atTop` and a state `ν` with `torusState hN (2k + 1) β f → ν f` along `u` at
every continuous `f`: `DLRLimit.exists_limit_state`, weak-* compactness.

DERIVED: the extent index `2k + 1` is the even-extent family; `0` is the excluded rank in `hN`. -/
theorem exists_periodic_limit (hN : N ≠ 0) (β : ℝ) :
    ∃ (u : Ultrafilter ℕ)
      (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ℕ) ≤ Filter.atTop ∧
        ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
          Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f) (u : Filter ℕ)
            (nhds (ν f)) :=
  MassGap.DLRLimit.exists_limit_state Filter.atTop (fun k : ℕ => torusState hN (2 * k + 1) β)

#print axioms exists_periodic_limit

/-- The ultrafilter of `exists_periodic_limit`.

DERIVED: `0` is the excluded rank in `hN`. -/
noncomputable def periodicUltra (hN : N ≠ 0) (β : ℝ) : Ultrafilter ℕ :=
  (exists_periodic_limit hN β).choose

/-- **A periodic infinite-volume state at coupling `β`**: the state of `exists_periodic_limit`, a
limit of `torusState hN (2k + 1) β` along `periodicUltra hN β`, both fixed by `Classical.choose`.
Not shown to satisfy the DLR equations of `GibbsSpec`, nor to be the only such limit.

DERIVED: `0` is the excluded rank in `hN`. -/
noncomputable def periodicState (hN : N ≠ 0) (β : ℝ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :=
  (exists_periodic_limit hN β).choose_spec.choose

/-- `periodicUltra hN β` is finer than `atTop`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem periodicUltra_le (hN : N ≠ 0) (β : ℝ) :
    ((periodicUltra (N := N) hN β : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.atTop :=
  (exists_periodic_limit hN β).choose_spec.choose_spec.1

#print axioms periodicUltra_le

/-- **What `periodicState` is**: at every continuous `f`,
`torusState hN (2k + 1) β f → periodicState hN β f` along `periodicUltra hN β` — a limit of the
`SU(N)` Wilson Gibbs states of the periodic lattices of extent `2(k + 1)`.

DERIVED: the extent index `2k + 1` is the even-extent family; `0` is the excluded rank in `hN`. -/
theorem tendsto_periodicState (hN : N ≠ 0) (β : ℝ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f)
      ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ) (nhds (periodicState hN β f)) :=
  (exists_periodic_limit hN β).choose_spec.choose_spec.2 f

#print axioms tendsto_periodicState

/-- `periodicState hN β` is reflection invariant about every constant `c`, in every direction `τ`,
at every real `β`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem periodicState_reflInvariant (hN : N ≠ 0) (β : ℝ) (τ : Fin 4) (c : ℤ) :
    MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ c)
      (periodicState hN β) := by
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  exact reflInvariant_of_tendsto_torus hN β τ c (periodicState hN β) (tendsto_periodicState hN β)

#print axioms periodicState_reflInvariant

/-- `periodicState hN β` is invariant under the unit shift along every direction `τ`, at every
real `β`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`. -/
theorem periodicState_shift (hN : N ≠ 0) (β : ℝ) (τ : Fin 4) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      periodicState hN β (MassGap.ReflectionShift.ishiftObsL τ f) = periodicState hN β f := by
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  exact shift_of_tendsto_torus hN β τ (periodicState hN β) (tendsto_periodicState hN β)

#print axioms periodicState_shift

/-- `periodicState hN β` is reflection positive at the constant `2p` (mirror plane `x_τ = p`) on
`halfSpaceAlg τ p`, at every real `β`.

DERIVED: `2` in `2 * p` is the plane-to-constant doubling; `4` is the spacetime dimension; `0` is
the excluded rank in `hN`. -/
theorem periodicState_reflPositive (hN : N ≠ 0) (β : ℝ) (τ : Fin 4) (p : ℤ) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p)
      (periodicState hN β) := by
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  exact reflPositive_even_of_tendsto_torus hN β τ p (periodicState hN β) (periodicUltra_le hN β)
    (tendsto_periodicState hN β)

#print axioms periodicState_reflPositive

/-- `periodicState hN β` is reflection positive at the constant `2p - 1` (mirror between
`x_τ = p - 1` and `x_τ = p`) on `halfSpaceAlg τ p`, at every `0 ≤ β`.

DERIVED: `2` and `1` in `2 * p - 1` are the plane-to-constant doubling and the half-step to the link
plane; `4` is the spacetime dimension; `0` is the excluded rank in `hN` and the sign of the coupling
in `hβ`. -/
theorem periodicState_reflPositive_odd (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (τ : Fin 4) (p : ℤ) :
    MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p)
      (periodicState hN β) := by
  haveI : ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ).NeBot := (periodicUltra hN β).neBot'
  exact reflPositive_odd_of_tendsto_torus hN hβ τ p (periodicState hN β) (periodicUltra_le hN β)
    (tendsto_periodicState hN β)

#print axioms periodicState_reflPositive_odd

end Limit

/-! ## 6. The gap from the reads, at every coupling -/

section Gap

/-- **The gauge-invariant transfer gap from the reads, for any state with the four facts.** For a
state `ν` reflection invariant and reflection positive about `2p`, shift invariant along `τ`, and
reflection positive about `2p - 1`: if every vector of the gauge-invariant GNS space orthogonal to
the vacuum reads below the floor at aperture `2k + 1`, that complement is contracted at rate
`ρ < 1` with `ρ^{k+1} = 12(1 − 3^{−1/4})/8`. `WilsonTransferReduction.positiveTransfer_of_state_facts`
gives `PositiveTransfer` from the fourth fact, `GaugeInvariantAlgebra.positiveTransfer_gaugeInv`
restricts it, and `SpectralGap.opT_gap_of_reads` is the gap.

DERIVED: `4` is the spacetime dimension; `2` in `2 * p` is the plane-to-constant doubling and `1` in
`2 * p - 1` the half-step to the link plane; `0` is the orthogonality and the lower end of `ρ`; `1` is
the upper bound on `ρ` and the `+ 1` of `k + 1`, the aperture `2k + 1`'s; `12`, `8`, `3`, `1` and `4`
spell the cap. -/
theorem gaugeInv_gap_of_reads_of_state_facts (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (hodd : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p - 1))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (k : ℕ)
    (hread : MassGap.SpectralGap.ReadsClear
      (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))
      (Omega (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm
        (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).vac) k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : H (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm,
        inner ℂ (Omega
          (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).toReflForm
          (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).vac) u = 0 →
        ∀ m : ℕ,
          ‖((opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu)) ^ m) u‖
            ≤ ρ ^ m * ‖u‖ :=
  MassGap.SpectralGap.opT_gap_of_reads _
    (MassGap.GaugeInvariantAlgebra.positiveTransfer_gaugeInv τ p ν hinv hpos hnu
      (MassGap.WilsonTransferReduction.positiveTransfer_of_state_facts τ p ν hinv hpos hnu hodd))
    k hread

#print axioms gaugeInv_gap_of_reads_of_state_facts

/-- `ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend`, the transfer data
`WilsonReadGap.wilson_gap_of_reads` is stated on, equals `gaugeInvTransferData τ p ν hinv hpos hnu`
for any three proofs `hinv`, `hpos`, `hnu`, by `rfl`: it is `gaugeInvTransferData` at the three facts
read off `htend`, and proofs of one proposition are definitionally equal. So
`gaugeInv_gap_of_reads_of_state_facts` is about the same operator when the facts come from `htend`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`; `1` is the all-identity
boundary configuration of the free states; `2` in `2 * p` is the plane-to-constant doubling. -/
example (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection (G := MassGap.SUN.SU N) τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) :
    MassGap.ClayCapstone.wilsonGaugeInvMixCubeData τ p hN β ν htend
      = MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu :=
  rfl

/-- **The gap from the reads for a common limit of the two free cube families.** The free-boundary
form: `ν` is the limit of the even cube family `symCube τ (2p)` along `lE` and of the odd family
`symCube τ (2p - 1)` along `lO`, both non-trivial and finer than `atTop`, at `0 ≤ β`. The four facts
come from `ReflectionHalfSpace.wilson_reflInvariant_of_tendsto`,
`wilson_reflPositive_even_of_tendsto`, `wilson_nu_T_of_tendsto` and
`wilson_reflPositive_odd_of_tendsto`, and `gaugeInv_gap_of_reads_of_state_facts` gives the gap.
Convergence of `mixCube` along `atTop` (`WilsonReadGap.wilson_gap_of_reads`'s `htend`) gives both
hypotheses at `lE = lO = atTop`, through `ReflectionHalfSpace.tendsto_symCube_even_of_mixCube` and
`tendsto_symCube_odd_of_mixCube`. That one state is a limit of both families is a hypothesis here;
compactness gives each family its own limit and does not identify them.

DERIVED: `4` is the spacetime dimension; `2` in `2 * p` is the plane-to-constant doubling and `1` in
`2 * p - 1` the half-step to the link plane; `0` is the excluded rank in `hN`, the sign of the
coupling, the orthogonality and the lower end of `ρ`; `1` is the all-identity boundary configuration
of the free states, the upper bound on `ρ` and the `+ 1` of `k + 1`, the aperture `2k + 1`'s; `12`,
`8`, `3`, `1` and `4` spell the cap. -/
theorem gaugeInv_gap_of_reads_of_common_limit (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β) (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (lE lO : Filter ℕ) [lE.NeBot] [lO.NeBot] (hlE : lE ≤ Filter.atTop) (hlO : lO ≤ Filter.atTop)
    (hEven : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.symCube τ (2 * p) n) 1 f)
        lE (nhds (ν f)))
    (hOdd : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.symCube τ (2 * p - 1) n) 1 f)
        lO (nhds (ν f)))
    (k : ℕ)
    (hread : MassGap.SpectralGap.ReadsClear
      (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
        (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
        (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE hEven)
        (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)))
      (Omega (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
          (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
          (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE
            hEven)
          (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)).toReflForm
        (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
          (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
          (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE
            hEven)
          (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)).vac)
      k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : H (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
          (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
          (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE
            hEven)
          (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven
            hOdd)).toReflForm,
        inner ℂ (Omega (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
            (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
            (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE
              hEven)
            (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven
              hOdd)).toReflForm
          (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
            (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
            (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE
              hEven)
            (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven
              hOdd)).vac) u = 0 →
        ∀ m : ℕ, ‖((opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
            (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
            (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE
              hEven)
            (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven
              hOdd))) ^ m) u‖ ≤ ρ ^ m * ‖u‖ :=
  gaugeInv_gap_of_reads_of_state_facts τ p ν
    (MassGap.ReflectionHalfSpace.wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν lE hEven)
    (MassGap.ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto τ p hN β 1 ν lE hlE hEven)
    (MassGap.ReflectionHalfSpace.wilson_nu_T_of_tendsto τ p hN β ν lE lO hEven hOdd)
    (MassGap.ReflectionHalfSpace.wilson_reflPositive_odd_of_tendsto τ p hN hβ 1 ν lO hlO hOdd)
    k hread

#print axioms gaugeInv_gap_of_reads_of_common_limit

/-- **The gauge-invariant transfer data at the periodic state**: `gaugeInvTransferData` at
`periodicState hN β`, with its three facts `periodicState_reflInvariant` (at `2p`),
`periodicState_reflPositive` and `periodicState_shift`.

DERIVED: `4` is the spacetime dimension; `2` in `2 * p` is the plane-to-constant doubling; `0` is the
excluded rank in `hN`. -/
noncomputable def periodicGaugeInvData (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) :
    MassGap.Transfer.TransferData
      ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p) :=
  MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p (periodicState hN β)
    (periodicState_reflInvariant hN β τ (2 * p))
    (periodicState_reflPositive hN β τ p)
    (periodicState_shift hN β τ)

/-- **`PositiveTransfer` at the periodic state, at every `0 ≤ β`.** From
`periodicState_reflPositive_odd` through `WilsonTransferReduction.positiveTransfer_of_state_facts`
and `GaugeInvariantAlgebra.positiveTransfer_gaugeInv`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN` and the sign of the
coupling in `hβ`. -/
theorem periodic_positiveTransfer (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) :
    PositiveTransfer (periodicGaugeInvData τ p hN β) :=
  MassGap.GaugeInvariantAlgebra.positiveTransfer_gaugeInv τ p (periodicState hN β)
    (periodicState_reflInvariant hN β τ (2 * p)) (periodicState_reflPositive hN β τ p)
    (periodicState_shift hN β τ)
    (MassGap.WilsonTransferReduction.positiveTransfer_of_state_facts τ p (periodicState hN β)
      (periodicState_reflInvariant hN β τ (2 * p)) (periodicState_reflPositive hN β τ p)
      (periodicState_shift hN β τ) (periodicState_reflPositive_odd hN hβ τ p))

#print axioms periodic_positiveTransfer

/-- **The transfer gap from the reads, at every `β ≥ 0`, at the periodic state.** At the
gauge-invariant transfer data built on `periodicState hN β`: if every vector of that GNS space
orthogonal to the vacuum reads below the floor at aperture `2k + 1`, that complement is contracted
at rate `ρ < 1` with `ρ^{k+1} = 12(1 − 3^{−1/4})/8`. Besides `N ≠ 0` and `0 ≤ β`, the reads are the
only hypothesis, and `ReadsClear` is the gap stated as a read (`SpectralGap`). Nothing is known
about `periodicUltra` beyond `periodicUltra_le`, so a statement about the periodic states that holds
eventually in `k` along `atTop` reaches `periodicState`; along `periodicUltra` itself the margin
inequality is exactly the limit statement (`PeriodicReduce.torusSlack_iff`), but no set of `k` is
known to belong to that ultrafilter except the tails.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`, the lower end of `β` and
of `ρ`, and the orthogonality; `1` is the upper bound on `ρ` and the `+ 1` of `k + 1`, the aperture
`2k + 1`'s; `12`, `8`, `3`, `1` and `4` spell the cap. -/
theorem periodic_gap_of_reads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (k : ℕ)
    (hread : MassGap.SpectralGap.ReadsClear (opT (periodicGaugeInvData τ p hN β))
      (Omega (periodicGaugeInvData τ p hN β).toReflForm (periodicGaugeInvData τ p hN β).vac) k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      ∀ u : H (periodicGaugeInvData τ p hN β).toReflForm,
        inner ℂ (Omega (periodicGaugeInvData τ p hN β).toReflForm
          (periodicGaugeInvData τ p hN β).vac) u = 0 →
        ∀ m : ℕ, ‖((opT (periodicGaugeInvData τ p hN β)) ^ m) u‖ ≤ ρ ^ m * ‖u‖ :=
  gaugeInv_gap_of_reads_of_state_facts τ p (periodicState hN β)
    (periodicState_reflInvariant hN β τ (2 * p)) (periodicState_reflPositive hN β τ p)
    (periodicState_shift hN β τ) (periodicState_reflPositive_odd hN hβ τ p) k hread

#print axioms periodic_gap_of_reads

/-- **The spectral statement from the reads, at every `β ≥ 0`, at the periodic state.** Under the
same reads there is `0 < ρ < 1` with `ρ^{k+1} = 12(1 − 3^{−1/4})/8` such that the transfer operator
at `periodicGaugeInvData τ p hN β` is self-adjoint, `0 < -log ρ`, its spectrum lies in
`{1} ∪ [0, exp (-(-log ρ))]`, and `1` is its greatest element. `ReadRoute.gapAt_of_reads` and
`ClayCapstone.clay_gap_of_gapAt`.

Scope: no conjunct makes `1` a simple eigenvalue — the identity on a space of dimension at least
`2` satisfies the three about `opT` — and no conjunct says the vacuum complement is non-zero. The
contraction that makes `1` simple is `periodic_gap_of_reads`'s; `PeriodicContent.PeriodicClayGapAt`
carries it together with the non-zero complement, as `ReadRoute.ClayGapAt` does at the `mixCube`
limit state.
Where the GNS space is spanned by the vacuum — at `N = 1`, which `hN` admits — `hread` holds with
nothing to read and every conjunct holds with nothing to contract.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank in `hN`, the lower end of `β`, of
`ρ` and of the spectrum, and the sign of the gap; `1` is the vacuum eigenvalue and the upper bound on
`ρ`, and the `+ 1` of `k + 1`, the aperture `2k + 1`'s; `12`, `8`, `3`, `1` and `4` spell the cap. -/
theorem periodic_clay_gap_of_reads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (k : ℕ)
    (hread : MassGap.SpectralGap.ReadsClear (opT (periodicGaugeInvData τ p hN β))
      (Omega (periodicGaugeInvData τ p hN β).toReflForm (periodicGaugeInvData τ p hN β).vac) k) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ^ (k + 1) = 12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8) ∧
      IsSelfAdjoint (opT (periodicGaugeInvData τ p hN β))
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ (opT (periodicGaugeInvData τ p hN β))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ (opT (periodicGaugeInvData τ p hN β))) 1 := by
  obtain ⟨ρ, hρpos, hρ1, hρk, hg⟩ := MassGap.ReadRoute.gapAt_of_reads
    (periodicGaugeInvData τ p hN β) (periodic_positiveTransfer τ p hN hβ) k hread
  exact ⟨ρ, hρpos, hρ1, hρk, MassGap.ClayCapstone.clay_gap_of_gapAt _ hρpos hρ1
    (periodic_positiveTransfer τ p hN hβ) hg⟩

#print axioms periodic_clay_gap_of_reads

end Gap

end MassGap.PeriodicState
