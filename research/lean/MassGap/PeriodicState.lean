import Mathlib
import MassGap.LinkGram
import MassGap.ReflectionStrong
import MassGap.WilsonTransfer
import MassGap.DLRLimit
import MassGap.GNSHilbert
import MassGap.GaugeInvariantAlgebra

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
the dyadic filter `dyadicFilter` (power-of-two extents, finer than `atTop`;
`DLRLimit.exists_limit_state`, weak-* compactness); `tendsto_periodicState` states that convergence.

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
identification of two limits is needed. The periodic states are not indexed by finite sets of `ℤ⁴`
links.

## What it gives

`periodicGaugeInvData τ p hN β` is the gauge-invariant transfer data at `periodicState hN β`, and
`periodic_positiveTransfer` states `PositiveTransfer` for it at every `0 ≤ β`.

## Scope

`periodicState hN β` is a limit of periodic Wilson Gibbs states along an ultrafilter. It satisfies
the DLR equations of the Wilson specification `GibbsSpec.spec` at every `N ≠ 0` and real `β`:
`PeriodicStateDLR.periodicState_dlr` (functional form). Nothing shows that it is the only DLR state
or that its vacuum complement is non-zero; the statements in this module use neither.

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

/-- The extent indices `j ≥ M` whose extent `2j + 2` is a multiple of `c + 1`.

DERIVED: `2j + 2` the extent of index `j`; `1` in `c + 1` keeps the modulus positive. -/
def dvdSet (i : ℕ × ℕ) : Set ℕ := {j | (i.1 + 1) ∣ 2 * j + 2 ∧ i.2 ≤ j}

/-- **The divisibility filter**: generated by the sets `dvdSet (c, M)`, so finer than `atTop` and, along it,
the extent is eventually a multiple of every positive integer.

DERIVED: no numeral. -/
def dvdFilter : Filter ℕ := ⨅ i : ℕ × ℕ, Filter.principal (dvdSet i)

/-- **The divisibility filter is not `⊥`**: the sets are directed (`dvdSet ((c₁+1)(c₂+1) − 1, max M₁ M₂)` lies in
both) and non-empty (`j = (c + 1)(M + 1) − 1`).

DERIVED: `1` the shift of the modulus and of `M`; `2` the extent. -/
theorem dvdFilter_neBot : dvdFilter.NeBot := by
  refine Filter.iInf_neBot_of_directed' ?_ ?_
  · intro a b
    have hP : 1 ≤ (a.1 + 1) * (b.1 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    refine ⟨((a.1 + 1) * (b.1 + 1) - 1, max a.2 b.2), ?_, ?_⟩
    · refine Filter.principal_mono.mpr fun j hj => ⟨?_, le_trans (le_max_left _ _) hj.2⟩
      have h2 : (a.1 + 1) * (b.1 + 1) - 1 + 1 ∣ 2 * j + 2 := hj.1
      rw [Nat.sub_add_cancel hP] at h2
      exact Dvd.dvd.trans (Dvd.intro _ rfl) h2
    · refine Filter.principal_mono.mpr fun j hj => ⟨?_, le_trans (le_max_right _ _) hj.2⟩
      have h2 : (a.1 + 1) * (b.1 + 1) - 1 + 1 ∣ 2 * j + 2 := hj.1
      rw [Nat.sub_add_cancel hP] at h2
      exact Dvd.dvd.trans (Dvd.intro_left _ rfl) h2
  · intro i
    obtain ⟨P, hPd⟩ : ∃ P, P = (i.1 + 1) * (i.2 + 1) := ⟨_, rfl⟩
    have hP : i.2 + 1 ≤ P := by
      rw [hPd]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    refine Filter.principal_neBot_iff.mpr ⟨P - 1, ?_, by omega⟩
    have h : 2 * (P - 1) + 2 = 2 * P := by omega
    show i.1 + 1 ∣ 2 * (P - 1) + 2
    rw [h, hPd]
    exact Dvd.intro (2 * (i.2 + 1)) (by ring)

#print axioms dvdFilter_neBot

/-- The divisibility filter is finer than `atTop`. DERIVED: `0` the modulus index. -/
theorem dvdFilter_le_atTop : dvdFilter ≤ Filter.atTop := by
  intro s hs
  obtain ⟨M, hM⟩ := Filter.mem_atTop_sets.mp hs
  exact Filter.mem_iInf_of_mem (0, M) (Filter.mem_principal.mpr fun j hj => hM j hj.2)

#print axioms dvdFilter_le_atTop

/-- `q` is a power of two: the cell sides the periodic routes may use.

DERIVED: `2` the base. -/
def IsPow2 (q : ℕ) : Prop := ∃ b : ℕ, q = 2 ^ b

theorem IsPow2.pos {q : ℕ} (h : IsPow2 q) : 0 < q := by
  obtain ⟨b, rfl⟩ := h; exact Nat.two_pow_pos b

/-- Indices whose extent `2j + 2` is a power of two.

DERIVED: `2j + 2` the extent of index `j`; `2` the base of the powers. -/
def pow2Set : Set ℕ := {j | ∃ k : ℕ, 2 * j + 2 = 2 ^ k}

/-- **The dyadic extent filter**: `atTop` restricted to power-of-two extents. Along it the extent is
eventually a multiple of every power of two, and the doubling family `{2^k n}` of any power-of-two
seed `n` is a set of it.

DERIVED: no numeral. -/
def dyadicFilter : Filter ℕ := Filter.atTop ⊓ Filter.principal pow2Set

/-- **The dyadic filter is not `⊥`**: `j = 2^(M+1) − 1` has extent `2^(M+2)` and `j ≥ M`.

DERIVED: `1`, `2` the shift and the doubling of the extent. -/
theorem dyadicFilter_neBot : dyadicFilter.NeBot := by
  rw [dyadicFilter, Filter.inf_principal_neBot_iff]
  intro s hs
  obtain ⟨M, hM⟩ := Filter.mem_atTop_sets.mp hs
  refine ⟨2 ^ (M + 1) - 1, hM _ ?_, M + 1 + 1, ?_⟩
  · have : M + 1 < 2 ^ (M + 1) := Nat.lt_two_pow_self
    omega
  · have : 1 ≤ 2 ^ (M + 1) := Nat.one_le_two_pow
    rw [pow_succ]; omega

#print axioms dyadicFilter_neBot

/-- The dyadic filter is finer than `atTop`. DERIVED: no numeral. -/
theorem dyadicFilter_le_atTop : dyadicFilter ≤ Filter.atTop := inf_le_left

#print axioms dyadicFilter_le_atTop

/-- **Along the dyadic filter the extent is eventually a multiple of `2^i`.**

DERIVED: `2j + 2` the extent; `2` the base. -/
theorem dyadic_dvd_pow (i : ℕ) : ∀ᶠ j in dyadicFilter, 2 ^ i ∣ 2 * j + 2 := by
  have h1 : ∀ᶠ j in dyadicFilter, 2 ^ i ≤ 2 * j + 2 :=
    ((Filter.eventually_ge_atTop (2 ^ i)).filter_mono dyadicFilter_le_atTop).mono
      fun j hj => by omega
  have h2 : ∀ᶠ j in dyadicFilter, j ∈ pow2Set :=
    Filter.mem_inf_of_right (Filter.mem_principal_self _)
  filter_upwards [h1, h2] with j hj ⟨k, hk⟩
  rw [hk] at hj ⊢
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hj)

#print axioms dyadic_dvd_pow

/-- **A limit of the periodic Wilson states along an ultrafilter finer than the dyadic filter.** As
`exists_periodic_limit`, with `u ≤ dyadicFilter` in place of `u ≤ atTop`: the periodic state is a
limit over power-of-two extents.

DERIVED: the extent index `2k + 1`; `0` the excluded rank. -/
theorem exists_periodic_limit_dvd (hN : N ≠ 0) (β : ℝ) :
    ∃ (u : Ultrafilter ℕ)
      (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ℕ) ≤ dyadicFilter ∧
        ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
          Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f) (u : Filter ℕ)
            (nhds (ν f)) :=
  haveI := dyadicFilter_neBot
  MassGap.DLRLimit.exists_limit_state dyadicFilter (fun k : ℕ => torusState hN (2 * k + 1) β)

#print axioms exists_periodic_limit_dvd

/-- The ultrafilter of `exists_periodic_limit_dvd`.

DERIVED: `0` is the excluded rank in `hN`. -/
noncomputable def periodicUltra (hN : N ≠ 0) (β : ℝ) : Ultrafilter ℕ :=
  (exists_periodic_limit_dvd hN β).choose

/-- **A periodic infinite-volume state at coupling `β`**: the state of `exists_periodic_limit_dvd`, a
limit of `torusState hN (2k + 1) β` along `periodicUltra hN β`, both fixed by `Classical.choose`.
It satisfies the DLR equations of `GibbsSpec` (`PeriodicStateDLR.periodicState_dlr`); it is not shown to be the only such limit.

DERIVED: `0` is the excluded rank in `hN`. -/
noncomputable def periodicState (hN : N ≠ 0) (β : ℝ) :
    MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :=
  (exists_periodic_limit_dvd hN β).choose_spec.choose

/-- `periodicUltra hN β` is finer than `atTop`.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem periodicUltra_le (hN : N ≠ 0) (β : ℝ) :
    ((periodicUltra (N := N) hN β : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.atTop :=
  le_trans (exists_periodic_limit_dvd hN β).choose_spec.choose_spec.1 dyadicFilter_le_atTop

#print axioms periodicUltra_le

/-- `periodicUltra hN β` is finer than the dyadic filter.

DERIVED: `0` is the excluded rank in `hN`. -/
theorem periodicUltra_le_dyadic (hN : N ≠ 0) (β : ℝ) :
    ((periodicUltra (N := N) hN β : Ultrafilter ℕ) : Filter ℕ) ≤ dyadicFilter :=
  (exists_periodic_limit_dvd hN β).choose_spec.choose_spec.1

#print axioms periodicUltra_le_dyadic

/-- **Along `periodicUltra hN β` the extent is eventually a multiple of every power of two.**

DERIVED: `2j + 2` the extent of index `j`; `2` the base. -/
theorem periodicUltra_dvd (hN : N ≠ 0) (β : ℝ) (i : ℕ) :
    ∀ᶠ j in ((periodicUltra (N := N) hN β : Ultrafilter ℕ) : Filter ℕ), 2 ^ i ∣ 2 * j + 2 :=
  (dyadic_dvd_pow i).filter_mono (periodicUltra_le_dyadic hN β)

#print axioms periodicUltra_dvd

/-- **What `periodicState` is**: at every continuous `f`,
`torusState hN (2k + 1) β f → periodicState hN β f` along `periodicUltra hN β` — a limit of the
`SU(N)` Wilson Gibbs states of the periodic lattices of extent `2(k + 1)`.

DERIVED: the extent index `2k + 1` is the even-extent family; `0` is the excluded rank in `hN`. -/
theorem tendsto_periodicState (hN : N ≠ 0) (β : ℝ)
    (f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ)) :
    Filter.Tendsto (fun k : ℕ => torusState hN (2 * k + 1) β f)
      ((periodicUltra hN β : Ultrafilter ℕ) : Filter ℕ) (nhds (periodicState hN β f)) :=
  (exists_periodic_limit_dvd hN β).choose_spec.choose_spec.2 f

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

/-! ## 6. The transfer data at the periodic state -/

section Gap

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

end Gap

end MassGap.PeriodicState
