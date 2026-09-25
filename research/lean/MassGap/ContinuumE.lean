import Mathlib
import MassGap.PlaneVariance
import MassGap.GeneralDecay
import MassGap.SpectralGap
import MassGap.ZeroMode

/-!
# MassGap.ContinuumE — requirement E: what composes from the lattice, and what the continuum still needs

Requirement E of the Clay statement is a quantum field theory on `ℝ⁴` satisfying the
Osterwalder–Schrader axioms (equivalently the Wightman axioms). No declaration in this tree constructs
one: there are no Schwinger functions on `ℝ⁴`, no measure on a space of distributions, and no Euclidean
group action other than the lattice's own reflections and unit shifts. This module composes the
lattice results that bear on E and states, as theorems, where the composition stops.

## 1. Lattice Osterwalder–Schrader data at one coupling

`wilson_lattice_os`: at `0 < β` with `coreRate 64 β < 1` and `ν` the `atTop` limit of the free
mixed-cube states, the following hold together. Reflection positivity of `ν` on the half-space
algebra for the reflection about the plane `x_τ = p` (reflection constant `2p`), a diagonal
condition on a submodule that by bilinearity gives the Gram condition with real coefficients;
invariance of `ν` under that reflection; invariance of `ν` under the unit shift along `τ`;
`PositiveTransfer` of the gauge-invariant transfer data; the contraction of every vector orthogonal
to the vacuum by `coreRate 64 β`; exponential decay of the connected reflected-shifted pairing of
every continuous observable local on a finite set in the half-space; and, at `2 ≤ N`, a non-zero
vector orthogonal to the vacuum. The state itself is `FreeLimit.exists_tendsto_stateFree`.

`exists_reflPositive_state`: at every real coupling, along an ultrafilter finer than `atTop`, the
free states on the reflection-symmetric cubes converge at every continuous observable to a state
that is reflection positive on the half-space algebra and invariant, for the reflection about the
plane `x_τ = p` (reflection constant `2p`); the convergence is part of the statement. Invariance
under the unit shift and positivity about the odd plane `x_τ = p − ½` are not claimed of that
state: both need the even and the odd cube families to share one limit
(`ReflectionHalfSpace.wilson_positiveTransfer_of_common_subsequential_limit`), which convergence
along `atTop` supplies and which is proved only at strong coupling.

## 2. The read of one vector

`transferRead D hP v hv k` is the `Moment.Read` at aperture `2k + 1` whose correlation at lag `d` is
the real part of the inner product of `v` with `opT D` raised to the circle distance of `d`, applied
to `v`. `readsClear_iff`: `SpectralGap.ReadsClear` at the vacuum holds exactly when every non-zero
vector orthogonal to the vacuum has this one read clearing the floor: two inequalities (positive
cosine average, tension below the floor) on one read per such vector. It holds with nothing to check
exactly when the vacuum complement is zero, as for Wilson data at `N = 1`.

## 3. The physical gap along a family of couplings, at one window

`wilson_physical_gap_of_reads`: for Wilson transfer data at couplings `β j ≥ 0`, each with its limit
state, and apertures `2 k_j + 1` spanning one physical extent `L = 2 (k_j + 1) sp_j`, if every
member's vectors orthogonal to the vacuum read below the floor, then every member contracts that
complement by a constant `ρ_j` whose physical rate `−log ρ_j / sp_j` is the one number
`−2 log(12(1 − 3^{−1/4})/8)/L`, a lower bound on that member's exact physical gap. It is
`SpectralGap.physical_gap_of_reads` at the Wilson operator. The members are unrelated: each
conclusion uses only its own member's hypotheses, and what they share is the window `L`. The spacing
`sp_j` is a parameter: nothing ties it to `β j`.

## 4. The one-sided bound is met at one fixed coupling

At one coupling in the strong-coupling region the lattice contraction constant `ρ` is fixed. Then
`wilson_screen_rate_eventually` gives, for every `κ`, the fixed-screen rate hypothesis
`κ/(Nap + 1) ≤ −log ρ` at every large aperture `Nap`, and `wilson_physical_decay_at_fixed_coupling`
turns it into decay at physical rate at least `κ/L` of every vector orthogonal to the vacuum. The
lower bound therefore holds with every `κ` along a family whose coupling never moves, while the
physical rate `−log ρ / a` of that family diverges as the spacing vanishes
(`physical_rate_tendsto_atTop_of_fixed_rate`) and is bounded by no constant
(`not_bounded_physical_rate_of_fixed_rate`); since `−log ρ` bounds the exact lattice gap from below,
the exact physical gap of that family is unbounded as well. A continuum theory needs, besides the
lower bound, an upper bound uniform in the spacing on the exact physical gap at the same window.

## 5. Two closed conditions

`gram_nonneg_of_tendsto`: the Gram form of reflection positivity, with real coefficients, at every
finite family survives a pointwise limit. `clustering_of_tendsto`: a clustering bound whose
constants do not depend on the spacing index survives a pointwise limit. Both are statements about
real numbers; they apply once lattice Schwinger values at physical positions exist, which no
declaration here defines.

## What E still needs, beyond this module

* the infinite-volume state along `atTop` at weak coupling (convergence of the free box states, or
  uniqueness of the DLR state), at a sequence of couplings tending to infinity;
* `SpectralGap.ReadsClear` at every member of such a sequence, at apertures of one physical extent;
* an upper bound, uniform in the spacing, on the exact physical gap `−log ‖T|_{Ω⊥}‖ / a` at the same
  window, so that the limit is not ultralocal;
* continuum fields: gauge-invariant local observables placed at points of `ℝ⁴` and smeared against
  test functions, with their renormalisation, and bounds on their correlations uniform in the spacing;
* Euclidean invariance of the limit: translations in all four directions and rotations;
* a reconstruction that ties its output to its input (`WightmanData.os_reconstruction_wightman` is
  an axiom whose type does not relate the two).
-/

namespace MassGap.ContinuumE

open Filter MeasureTheory
open MassGap MassGap.Transfer MassGap.ReflectionHalfSpace MassGap.ClayCapstone

/-! ## 1. Lattice Osterwalder–Schrader data at one coupling -/

section LatticeOS

variable {N : ℕ}

/-- **`PositiveTransfer` of the gauge-invariant Wilson transfer data, at every `β ≥ 0` at which the
free mixed-cube states converge along `atTop`.** That convergence is proved where
`coreRate 64 β < 1` (`FreeLimit.exists_tendsto_stateFree`). The positivity of the full half-space
data at the `atTop` limit state (`ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit`)
restricted to the gauge-invariant algebra (`GaugeInvariantAlgebra.positiveTransfer_gaugeInv`). The
three state facts are the ones `ClayCapstone.wilsonGaugeInvMixCubeData` is built from, so the
conclusion is about that data.

DERIVED: `4` is the spacetime dimension, the `Fin 4` the lattice is indexed by; `0` is the excluded
gauge rank in `hN` and the lower end of the coupling in `hβ`; `1` is the all-identity boundary
configuration of the free box states. -/
theorem positiveTransfer_wilsonGaugeInv (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.GNSHilbert.PositiveTransfer (wilsonGaugeInvMixCubeData τ p hN β ν htend) :=
  MassGap.GaugeInvariantAlgebra.positiveTransfer_gaugeInv τ p ν
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))
    (wilson_positiveTransfer_of_mixCube_limit τ p hN hβ ν htend)

#print axioms positiveTransfer_wilsonGaugeInv

/-- **The lattice Osterwalder–Schrader data at one coupling in the strong-coupling region.** At
`0 < β` with `coreRate 64 β < 1` and `ν` the `atTop` limit of the free mixed-cube states, seven
statements hold together:

1. reflection positivity of `ν` on the half-space algebra, for the reflection about the plane
   `x_τ = p` (reflection constant `2p`): `0 ≤ ν(θf · f)` for every `f` in that submodule, which by
   bilinearity gives the Gram condition with real coefficients on every finite family in the
   submodule; the Gram form is not a conjunct;
2. invariance of `ν` under the reflection about the plane `x_τ = p` (reflection constant `2p`);
3. invariance of `ν` under the unit shift along `τ`;
4. `PositiveTransfer` of the gauge-invariant transfer data;
5. every vector of the gauge-invariant GNS space orthogonal to the vacuum is contracted by the
   transfer operator by the factor `coreRate 64 β`;
6. for every continuous `x` local on a finite set of links in the half-space `posHalf τ p`, there is
   `U` with `|ν(θx · Sᵐx) − ν(θx) ν(Sᵐx)| ≤ coreConstG (2‖x‖²) 64 β U · coreRate 64 β^(m + 2 − U)` for
   every `m` with `U ≤ m + 2`;
7. at `2 ≤ N`, a non-zero vector of that GNS space orthogonal to the vacuum.

These are lattice forms, in the direction `τ` only, of reflection positivity, time-reflection and
time-translation invariance, positivity of the transfer operator, a gap on the vacuum complement of
the pre-Hilbert quotient `GNS` (the spectral statement on its completion is
`StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling`), decay of the connected pairing of one
observable's reflection with its own shift from lag `U − 2` on (in the proof of
`GeneralDecay.nu_connected_shift_abs_le_obs`, `U = 32 (R + 2)⁴`, with the support strictly inside a
cube of side `R` based one step below the plane, `GeneralDecay.exists_cube_posHalf`), and a non-zero
vacuum complement. Invariance under shifts along the other three directions and under the
hypercubic group is not claimed of `ν`. The rate is in lattice units at one coupling. The region
`coreRate 64 β < 1` is `β` below about `2.9 · 10⁻⁵`.

DERIVED: `4` is the spacetime dimension; `16 * 4` is `StrongCoupling.touchDeg_bd_le`'s degree bound
`16 · dim` at `dim = 4`, where `coreRate` and `coreConstG` are evaluated; `0` is the excluded gauge
rank, the lower end of the coupling and the orthogonality, and also the zero vector in `y ≠ 0`; `1`
is the all-identity boundary configuration of the free box states and the threshold `coreRate` falls
below; `2` is the doubling that turns the plane `x_τ = p` into the reflection constant `2 * p`, the
factor in `2 * (‖x‖ * ‖x‖)`, the offset `m + 2` of the decay exponent, and the least rank `2 ≤ N` at
which a plaquette variance is positive. -/
theorem wilson_lattice_os (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 < β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    MassGap.InfiniteReflection.ReflPositiveOn
        (MassGap.LatticeReflection.latticeReflection τ (2 * p))
        (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν
      ∧ MassGap.InfiniteReflection.IsReflectionInvariant
          (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν
      ∧ (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
          ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
      ∧ MassGap.GNSHilbert.PositiveTransfer (wilsonGaugeInvMixCubeData τ p hN β ν htend)
      ∧ (∀ y : GNS (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
          (inner ℝ (wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0 →
          ‖(wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq y‖
            ≤ MassGap.StrongCoupling.coreRate (16 * 4) β * ‖y‖)
      ∧ (∀ (x : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ))
            (S : Finset MassGap.InfiniteLattice.ILink),
          (S : Set MassGap.InfiniteLattice.ILink) ⊆ MassGap.HalfSpaceAlgebra.posHalf τ p →
          MassGap.InfiniteLattice.IsLocalOn S
            (x : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N) → ℝ) →
          ∃ U : ℕ, ∀ m : ℕ, U ≤ m + 2 →
            |ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x
                  * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x)
              - ν (MassGap.LatticeReflection.ireflObs τ (2 * p) x)
                * ν ((⇑(MassGap.ReflectionShift.ishiftObsL τ))^[m] x)|
              ≤ MassGap.StrongCoupling.coreConstG (2 * (‖x‖ * ‖x‖)) (16 * 4) β U
                * MassGap.StrongCoupling.coreRate (16 * 4) β ^ (m + 2 - U))
      ∧ (2 ≤ N → ∃ y : GNS (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
          y ≠ 0 ∧ (inner ℝ (wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0) :=
  ⟨wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend),
    wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend),
    wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN β ν htend),
    positiveTransfer_wilsonGaugeInv τ p hN hβ.le ν htend,
    fun y hy => MassGap.StrongCouplingGap.norm_Tq_le_of_orth τ p hN hβ hr ν htend y hy,
    fun x _S hS hx =>
      MassGap.GeneralDecay.nu_connected_shift_abs_le_obs hN hβ.le τ p ν htend hr x hS hx,
    fun hN2 => MassGap.PlaneVariance.exists_ne_zero_orth_vacuum τ p hN2 hN hβ.le ν htend⟩

#print axioms wilson_lattice_os

/-- **A reflection-positive limit of the Wilson free box states, at every coupling.** At every real
`β`, along an ultrafilter `u` finer than `atTop` (`DLRLimit.exists_limit_state`), the free states on
`symCube τ (2p) n` with the all-identity boundary converge at every continuous observable to a state
`ν`. That `ν` is reflection positive on `halfSpaceAlg τ p` under the reflection about the plane
`x_τ = p`, reflection constant `2p` (`ReflectionHalfSpace.wilson_reflPositive_even_of_tendsto`), and
invariant under that reflection (`ReflectionHalfSpace.wilson_reflInvariant_of_tendsto`).

The convergence conjunct is what ties `ν` to `β`: without it the two reflection facts hold at every
`β` for evaluation at the identity configuration. Unit-shift invariance and positivity about the
odd plane `x_τ = p − ½` (which `PositiveTransfer` needs) follow once the even and odd cube families
share one limit (`wilson_positiveTransfer_of_common_subsequential_limit`); an ultrafilter limit of
one family gives neither, so at weak coupling that common limit is the open lattice input. At
`N = 1` the half-space algebra is the constants and both reflection facts hold with nothing to
check.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank; `2` is the doubling that
turns the plane `x_τ = p` into the reflection constant `2 * p`; `1` is the all-identity boundary
configuration of the free box states. -/
theorem exists_reflPositive_state (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ) :
    ∃ (u : Ultrafilter ℕ)
      (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ℕ) ≤ Filter.atTop
      ∧ (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
          Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
              MassGap.WilsonAction.measurable_wilsonDensity
              (MassGap.WilsonAction.wilsonDensity_nonneg hN)
              (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1 f)
            (u : Filter ℕ) (nhds (ν f)))
      ∧ MassGap.InfiniteReflection.ReflPositiveOn
          (MassGap.LatticeReflection.latticeReflection τ (2 * p))
          (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν
      ∧ MassGap.InfiniteReflection.IsReflectionInvariant
          (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν := by
  obtain ⟨u, ν, hle, htend⟩ := MassGap.DLRLimit.exists_limit_state Filter.atTop
    (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β (symCube τ (2 * p) n) 1)
  exact ⟨u, ν, hle, htend,
    wilson_reflPositive_even_of_tendsto τ p hN β 1 ν (u : Filter ℕ) hle htend,
    wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν (u : Filter ℕ) htend⟩

#print axioms exists_reflPositive_state

end LatticeOS

/-! ## 2. The read of one vector -/

section Read

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- The transfer correlation of a vector `v` of the GNS completion at lag `c`: the real part of
`⟪v, opTᶜ v⟫`.

DERIVED: no numeral. `c` is the caller's lag. -/
noncomputable def transferCorr (D : TransferData A) (v : MassGap.GNSHilbert.H D.toReflForm)
    (c : ℕ) : ℝ :=
  RCLike.re (inner ℂ v (((MassGap.GNSHilbert.opT D) ^ c) v))

#print axioms transferCorr

/-- Under `PositiveTransfer D` the transfer correlation is nonnegative at every lag: it is the
`c`-th moment of a finite measure on `[0, 1]` (`SpectralRep.exists_moment_measure`), whose integrand
`tᶜ` is nonnegative there.

DERIVED: `0` is the lower bound concluded; the interval ends `0` and `1` are inside the proof. -/
theorem transferCorr_nonneg (D : TransferData A) (hP : MassGap.GNSHilbert.PositiveTransfer D)
    (v : MassGap.GNSHilbert.H D.toReflForm) (c : ℕ) : 0 ≤ transferCorr D v c := by
  obtain ⟨w, _, hmom⟩ := MassGap.SpectralRep.exists_moment_measure (MassGap.GNSHilbert.opT D)
    (MassGap.GNSHilbert.isSelfAdjoint_opT D)
    (fun x hx => ⟨MassGap.GNSHilbert.spectrum_opT_nonneg D hP hx,
      (MassGap.GNSHilbert.spectrum_opT_subset_unit_interval D hx).2⟩) v
  have h : transferCorr D v c = ∫ t, (t : ℝ) ^ c ∂w := hmom c
  rw [h]
  exact integral_nonneg (fun t => pow_nonneg t.2.1 c)

#print axioms transferCorr_nonneg

/-- At lag zero the transfer correlation is the squared norm.

DERIVED: `0` is the lag; `2` is the square of the norm. -/
theorem transferCorr_zero (D : TransferData A) (v : MassGap.GNSHilbert.H D.toReflForm) :
    transferCorr D v 0 = ‖v‖ ^ 2 := by
  unfold transferCorr
  rw [pow_zero, ContinuousLinearMap.one_apply, InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]

#print axioms transferCorr_zero

/-- **The read of one vector.** For `v ≠ 0` under `PositiveTransfer D`, the `Moment.Read` at
aperture `2k + 1` whose correlation at lag `d` is `transferCorr D v (circLag d)`. Nonnegativity is
`transferCorr_nonneg`; the total is positive because the lag-zero term is `‖v‖² > 0`.

DERIVED: `2` and `1` spell the aperture `2k + 1`, and `1` is also the `+ 1` of the lag arity
`Fin (2k + 1 + 1)`; `0` is the contact lag in the proof. -/
noncomputable def transferRead (D : TransferData A) (hP : MassGap.GNSHilbert.PositiveTransfer D)
    (v : MassGap.GNSHilbert.H D.toReflForm) (hv : v ≠ 0) (k : ℕ) : Moment.Read (2 * k + 1) where
  ρ := fun d => transferCorr D v (Moment.circLag d)
  hρ := fun d => transferCorr_nonneg D hP v _
  hpos := by
    have h0 : Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0 := by simp [Moment.circLag]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun d : Fin (2 * k + 1 + 1) => transferCorr D v (Moment.circLag d))
      (fun d _ => transferCorr_nonneg D hP v _) (Finset.mem_univ (0 : Fin (2 * k + 1 + 1))))
    show 0 < transferCorr D v (Moment.circLag (0 : Fin (2 * k + 1 + 1)))
    rw [h0, transferCorr_zero]
    exact pow_pos (norm_pos_iff.mpr hv) 2

#print axioms transferRead

/-- **`ReadsClear` is a condition on one read per vector.** Under `PositiveTransfer D`,
`SpectralGap.ReadsClear (opT D) Ω k` at the vacuum `Ω` holds exactly when every non-zero `v`
orthogonal to `Ω` has `transferRead D hP v hv k` with a positive cosine average and tension below
`¼·log 3`.

Forward: `transferRead` is a read with the required correlation. Backward: a read whose correlation is
`v`'s is `transferRead` itself, a `Moment.Read` being determined by its correlation; and the zero
vector has no read, its correlation summing to zero. So `ReadsClear` is two inequalities (positive
cosine average, tension below the floor) on one read per non-zero vector orthogonal to the vacuum;
it holds with nothing to check exactly when the vacuum complement is zero, as for Wilson data at
`N = 1`.

DERIVED: `0` is the orthogonality and the lower end of the cosine average, and also the zero vector
in `v ≠ 0`; `(1 / 4) * log 3` is the floor `κ₀YM`, its `1`, `4` and `3` the floor's own. -/
theorem readsClear_iff (D : TransferData A) (hP : MassGap.GNSHilbert.PositiveTransfer D) (k : ℕ) :
    SpectralGap.ReadsClear (MassGap.GNSHilbert.opT D)
        (MassGap.GNSHilbert.Omega D.toReflForm D.vac) k ↔
      ∀ v : MassGap.GNSHilbert.H D.toReflForm, ∀ hv : v ≠ 0,
        inner ℂ (MassGap.GNSHilbert.Omega D.toReflForm D.vac) v = 0 →
        0 < ∑ d, (transferRead D hP v hv k).p d * Real.cos ((transferRead D hP v hv k).θ d)
          ∧ (transferRead D hP v hv k).tension < (1 / 4) * Real.log 3 := by
  constructor
  · intro h v hv hΩv
    exact h v hΩv (transferRead D hP v hv k) (fun d => rfl)
  · intro h v hΩv R hR
    have hv : v ≠ 0 := by
      rintro rfl
      have hz : ∀ d, R.ρ d = 0 := fun d => by rw [hR d]; simp
      have hpos := R.hpos
      simp only [hz, Finset.sum_const_zero, lt_self_iff_false] at hpos
    have hReq : R = transferRead D hP v hv k := by
      cases R with
      | mk ρ hρ hpos =>
        have hfun : ρ = fun d => transferCorr D v (Moment.circLag d) := funext fun d => hR d
        subst hfun
        rfl
    rw [hReq]
    exact h v hv hΩv

#print axioms readsClear_iff

end Read

/-! ## 3. The physical gap along a family of couplings, at one window -/

section Family

variable {N : ℕ}

/-- **The Wilson physical gap from the reads, member by member of a family at one window.** For a
family `j : ι` of couplings `β j ≥ 0`, each with its `atTop` limit state `ν j`, and apertures
`2 k_j + 1` spanning one physical extent `L = 2 (k_j + 1) · sp_j`: if every member satisfies
`SpectralGap.ReadsClear` at its vacuum, then at each `j` there is `ρ ∈ (0, 1)` with
`−log ρ / sp_j = −2·log(12(1 − 3^{−1/4})/8)/L`, positive, and `‖opTᵐ u‖ ≤ ρᵐ ‖u‖` for every `u`
orthogonal to the vacuum. So `ρ` is a contraction constant of the vacuum complement whose physical
rate is `κ*/L`, `κ* = −2·log(12(1 − 3^{−1/4})/8)`; the exact physical gap `−log ‖opT|_{Ω⊥}‖ / sp_j`
is at least that.

This is `SpectralGap.physical_gap_of_reads` at the gauge-invariant Wilson transfer operator, whose
self-adjointness, spectrum in `[0, 1]` and fixed vacuum come from `GNSHilbert` and
`positiveTransfer_wilsonGaugeInv`. The right-hand side names no spacing and no coupling, so it is one
number across the family.

Scope. The members are unrelated: the conclusion at `j` uses only the hypotheses at `j`, and the one
value the members share is the window `L` of `hL`. `sp j` is a parameter, not a function of `β j`,
and `ReadsClear` and the limit states are hypotheses. Section 4 shows a conclusion of this form,
decay at a spacing-free physical rate, is met by a family whose coupling does not move, through the
strong-coupling contraction.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank, the lower end of each
coupling, the sign of each spacing, the lower end of `ρ` and of its physical rate, and the
orthogonality; `1` is the all-identity boundary configuration and the upper end of `ρ`; `2 * (k + 1)`
is the number of sites of the aperture `2k + 1`, and the `2` of `−2·log` is that doubling; `12`, `8`,
`3`, `1` and `4` spell the cap `12(1 − 3^{−1/4})/8`. -/
theorem wilson_physical_gap_of_reads (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {ι : Type*}
    (β : ι → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (ν : ι → MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ j, ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) (β j) (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν j f)))
    (k : ι → ℕ)
    (hread : ∀ j, SpectralGap.ReadsClear
      (MassGap.GNSHilbert.opT (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)))
      (MassGap.GNSHilbert.Omega (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)).toReflForm
        (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)).vac) (k j))
    (sp : ι → ℝ) (L : ℝ) (hsp : ∀ j, 0 < sp j)
    (hL : ∀ j, (2 * ((k j : ℝ) + 1)) * sp j = L) (j : ι) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      -Real.log ρ / sp j = -2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) / L ∧
      0 < -Real.log ρ / sp j ∧
      ∀ u : MassGap.GNSHilbert.H (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)).toReflForm,
        inner ℂ (MassGap.GNSHilbert.Omega
          (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)).toReflForm
          (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)).vac) u = 0 →
        ∀ m : ℕ, ‖((MassGap.GNSHilbert.opT
          (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j))) ^ m) u‖ ≤ ρ ^ m * ‖u‖ := by
  have hP := positiveTransfer_wilsonGaugeInv τ p hN (hβ j) (ν j) (htend j)
  exact SpectralGap.physical_gap_of_reads
    (MassGap.GNSHilbert.opT (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)))
    (MassGap.GNSHilbert.isSelfAdjoint_opT (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)))
    (fun x hx => ⟨MassGap.GNSHilbert.spectrum_opT_nonneg
        (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)) hP hx,
      (MassGap.GNSHilbert.spectrum_opT_subset_unit_interval
        (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)) hx).2⟩)
    (MassGap.GNSHilbert.Omega (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)).toReflForm
      (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)).vac)
    (MassGap.GNSHilbert.opT_Omega (wilsonGaugeInvMixCubeData τ p hN (β j) (ν j) (htend j)))
    (k j) (hread j) (sp j) L (hsp j) (hL j)

#print axioms wilson_physical_gap_of_reads

end Family

/-! ## 4. The one-sided bound is met at one fixed coupling -/

section FixedCoupling

/-- Iterating a contraction on an invariant set: if `T` maps `S` into itself and contracts it by
`ρ ≥ 0`, then `Tⁿ` maps `S` into itself and contracts it by `ρⁿ`.

DERIVED: `0` is the sign of `ρ`. -/
theorem norm_iterate_le_of_contract {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (T : E →ₗ[ℝ] E) (S : Set E) (hS : ∀ y ∈ S, T y ∈ S) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hT : ∀ y ∈ S, ‖T y‖ ≤ ρ * ‖y‖) (y : E) (hy : y ∈ S) :
    ∀ n : ℕ, (T ^ n) y ∈ S ∧ ‖(T ^ n) y‖ ≤ ρ ^ n * ‖y‖ := by
  intro n
  induction n with
  | zero => exact ⟨by simpa using hy, by simp⟩
  | succ n ih =>
    obtain ⟨hmem, hle⟩ := ih
    -- `Module.End`'s multiplication is composition, so `(T * Tⁿ) y` is `T (Tⁿ y)` by definition.
    have hsucc : (T ^ (n + 1)) y = T ((T ^ n) y) :=
      congrArg (fun F : E →ₗ[ℝ] E => F y) (pow_succ' T n)
    rw [hsucc]
    refine ⟨hS _ hmem, ?_⟩
    calc ‖T ((T ^ n) y)‖ ≤ ρ * ‖(T ^ n) y‖ := hT _ hmem
      _ ≤ ρ * (ρ ^ n * ‖y‖) := mul_le_mul_of_nonneg_left hle hρ
      _ = ρ ^ (n + 1) * ‖y‖ := by ring

#print axioms norm_iterate_le_of_contract

/-- **Decay in physical time at a fixed screen.** If `T` contracts an invariant set `S` by
`exp(−Δlat)`, and the lattice rate clears the screen's bound, `κ/(Nap + 1) ≤ Δlat`, with the screen
of physical extent `L = (Nap + 1)·a`, then `‖Tⁿ y‖ ≤ exp(−(κ/L)·(n·a)) ‖y‖` on `S`: the decay rate
in the physical time `n·a` is at least `κ/L`, which reads no spacing.
`ZeroMode.gap_phys_of_fixed_screen` is the step from the lattice rate to the physical one.

DERIVED: `0` is the sign of `κ`, `L` and `a`; `1` is the `+ 1` of the screen's lag arity. -/
theorem physical_decay_at_screen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (S : Set E) (hS : ∀ y ∈ S, T y ∈ S)
    {Δlat a κ L : ℝ} {Nap : ℕ} (hκ : 0 < κ) (hL : 0 < L) (ha : 0 < a)
    (hscreen : ((Nap : ℝ) + 1) * a = L) (hrate : κ / ((Nap : ℝ) + 1) ≤ Δlat)
    (hcontract : ∀ y ∈ S, ‖T y‖ ≤ Real.exp (-Δlat) * ‖y‖) :
    ∀ n : ℕ, ∀ y ∈ S, ‖(T ^ n) y‖ ≤ Real.exp (-(κ / L) * ((n : ℝ) * a)) * ‖y‖ := by
  intro n y hy
  have hphys : κ / L ≤ Δlat / a :=
    MassGap.ZeroMode.gap_phys_of_fixed_screen (fun _ => Nap) (fun _ => a) (fun _ => Δlat) κ L hκ hL
      (fun _ => ha) (fun _ => hscreen) (fun _ => hrate) 0
  have hmul : κ / L * a ≤ Δlat := (le_div_iff₀ ha).mp hphys
  have hit := (norm_iterate_le_of_contract T S hS (Real.exp_pos (-Δlat)).le hcontract y hy n).2
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : Real.exp (-Δlat) ^ n ≤ Real.exp (-(κ / L) * ((n : ℝ) * a)) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hprod : (n : ℝ) * (κ / L * a) ≤ (n : ℝ) * Δlat := mul_le_mul_of_nonneg_left hmul hn
    nlinarith [hprod]
  calc ‖(T ^ n) y‖ ≤ Real.exp (-Δlat) ^ n * ‖y‖ := hit
    _ ≤ Real.exp (-(κ / L) * ((n : ℝ) * a)) * ‖y‖ :=
        mul_le_mul_of_nonneg_right hexp (norm_nonneg y)

#print axioms physical_decay_at_screen

variable {N : ℕ}

/-- **At one strong coupling, decay at physical rate at least `κ/L` at every window the lattice rate
clears.** At `0 < β` with `coreRate 64 β < 1` and its limit state, for a screen of physical extent
`L = (Nap + 1)·a` whose bound `κ/(Nap + 1)` the lattice rate `−log coreRate 64 β` clears, every
vector of the gauge-invariant GNS space orthogonal to the vacuum decays as `exp(−(κ/L)·(n·a))`.

`physical_decay_at_screen` at the contraction `StrongCouplingGap.norm_Tq_le_of_orth`, with
`exp(−(−log ρ)) = ρ`; the vacuum complement is invariant under `Tq` by `VolumeRate.inner_vac_Tq`.
With `wilson_screen_rate_eventually` the screen condition holds for every `κ` at every large
aperture, at this one coupling.

DERIVED: `4` is the spacetime dimension; `16 * 4` is `StrongCoupling.touchDeg_bd_le`'s degree bound
`16 · dim` at `dim = 4`; `0` is the excluded gauge rank, the lower end of the coupling, the sign of
`κ`, `L` and `a`, and the orthogonality; `1` is the all-identity boundary configuration, the
threshold `coreRate` falls below, and the `+ 1` of the screen's lag arity. -/
theorem wilson_physical_decay_at_fixed_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 < β) (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    {a κ L : ℝ} {Nap : ℕ} (hκ : 0 < κ) (hL : 0 < L) (ha : 0 < a)
    (hscreen : ((Nap : ℝ) + 1) * a = L)
    (hrate : κ / ((Nap : ℝ) + 1) ≤ -Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β)) :
    ∀ n : ℕ, ∀ y : GNS (wilsonGaugeInvMixCubeData τ p hN β ν htend).toReflForm,
      (inner ℝ (wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0 →
      ‖((wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq ^ n) y‖
        ≤ Real.exp (-(κ / L) * ((n : ℝ) * a)) * ‖y‖ := by
  have hρ0 := MassGap.StrongCouplingGap.coreRate_pos (16 * 4) hβ
  have hexp : Real.exp (-(-Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β)))
      = MassGap.StrongCoupling.coreRate (16 * 4) β := by
    rw [neg_neg, Real.exp_log hρ0]
  intro n y hy
  exact physical_decay_at_screen (wilsonGaugeInvMixCubeData τ p hN β ν htend).Tq
    {y | (inner ℝ (wilsonGaugeInvMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0}
    (fun y hy => MassGap.VolumeRate.inner_vac_Tq (wilsonGaugeInvMixCubeData τ p hN β ν htend)
      (x := y) hy)
    hκ hL ha hscreen hrate
    (fun y hy => by
      rw [hexp]
      exact MassGap.StrongCouplingGap.norm_Tq_le_of_orth τ p hN hβ hr ν htend y hy)
    n y hy

#print axioms wilson_physical_decay_at_fixed_coupling

/-- At a fixed positive lattice rate `Δ₀`, the fixed-screen bound `κ/(Nap + 1) ≤ Δ₀` holds at every
large aperture `Nap`, whatever `κ` is: `κ/(Nap + 1) → 0`.

DERIVED: `0` is the sign of `Δ₀` and the limit of `κ/(Nap + 1)`; `1` is the `+ 1` of the lag
arity. -/
theorem screen_rate_eventually_of_fixed_rate {κ Δ₀ : ℝ} (hΔ : 0 < Δ₀) :
    ∀ᶠ Nap : ℕ in Filter.atTop, κ / ((Nap : ℝ) + 1) ≤ Δ₀ := by
  have hNat : Filter.Tendsto (fun Nap : ℕ => ((Nap : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have ht : Filter.Tendsto (fun Nap : ℕ => κ / ((Nap : ℝ) + 1)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hNat
  exact (ht.eventually (gt_mem_nhds hΔ)).mono (fun _ h => h.le)

#print axioms screen_rate_eventually_of_fixed_rate

/-- **At one strong coupling the screen bound holds with every `κ`.** For `0 < β` with
`coreRate 64 β < 1` and every real `κ`, the bound `κ/(Nap + 1) ≤ −log coreRate 64 β` holds at every
large aperture `Nap`. With `wilson_physical_decay_at_fixed_coupling`, a family that never moves the
coupling and refines the spacing at one window decays at physical rate at least `κ/L`, with every
`κ`.

DERIVED: `16 * 4` is `StrongCoupling.touchDeg_bd_le`'s degree bound `16 · dim` at `dim = 4`; `0` is
the lower end of the coupling; `1` is the threshold `coreRate` falls below and the `+ 1` of the lag
arity. -/
theorem wilson_screen_rate_eventually {β : ℝ} (hβ : 0 < β)
    (hr : MassGap.StrongCoupling.coreRate (16 * 4) β < 1) (κ : ℝ) :
    ∀ᶠ Nap : ℕ in Filter.atTop,
      κ / ((Nap : ℝ) + 1) ≤ -Real.log (MassGap.StrongCoupling.coreRate (16 * 4) β) := by
  have hlog := Real.log_neg (MassGap.StrongCouplingGap.coreRate_pos (16 * 4) hβ) hr
  exact screen_rate_eventually_of_fixed_rate (by linarith)

#print axioms wilson_screen_rate_eventually

/-- **A fixed lattice rate is an unbounded physical rate.** If the spacing is positive and tends to
`0`, and the lattice rate is a fixed `Δ₀ > 0`, then `Δ₀ / spacing s → ∞`. A statement about real
numbers. Read on the fixed-coupling Wilson family (`Δ₀ = −log coreRate 64 β`, a lower bound on the
lattice gap), the exact physical gap diverges as the spacing falls.

DERIVED: `0` is the sign of each spacing and of `Δ₀`, and the spacing's limit. -/
theorem physical_rate_tendsto_atTop_of_fixed_rate (spacing : ℕ → ℝ) (hpos : ∀ s, 0 < spacing s)
    (h0 : Filter.Tendsto spacing Filter.atTop (nhds 0)) {Δ₀ : ℝ} (hΔ : 0 < Δ₀) :
    Filter.Tendsto (fun s => Δ₀ / spacing s) Filter.atTop Filter.atTop := by
  have hw : Filter.Tendsto spacing Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨h0, Filter.Eventually.of_forall (fun s => Set.mem_Ioi.mpr (hpos s))⟩
  have hinv : Filter.Tendsto (fun s => (spacing s)⁻¹) Filter.atTop Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp hw
  simpa [div_eq_mul_inv] using hinv.const_mul_atTop hΔ

#print axioms physical_rate_tendsto_atTop_of_fixed_rate

/-- **A fixed lattice rate admits no uniform upper bound in physical units.** Under the hypotheses
of `physical_rate_tendsto_atTop_of_fixed_rate`, there is no `M` with `Δ₀ / spacing s ≤ M` at every
`s`. This is a statement about the real sequence `Δ₀ / spacing s`. It separates the fixed-coupling
family from a two-sided condition `δ ≤ Δ/a ≤ M` when `Δ` is the exact lattice gap
`−log ‖T|_{Ω⊥}‖`: `−log coreRate 64 β` bounds that gap from below, so the exact physical gap of the
fixed-coupling family is unbounded too. For a `Δ` certified only by a contraction constant, as in
`wilson_physical_gap_of_reads`, the upper half is met by weakening `ρ`.

DERIVED: `0` is the sign of each spacing and of `Δ₀`, and the spacing's limit. -/
theorem not_bounded_physical_rate_of_fixed_rate (spacing : ℕ → ℝ) (hpos : ∀ s, 0 < spacing s)
    (h0 : Filter.Tendsto spacing Filter.atTop (nhds 0)) {Δ₀ : ℝ} (hΔ : 0 < Δ₀) :
    ¬ ∃ M : ℝ, ∀ s, Δ₀ / spacing s ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨s, hs⟩ :=
    ((physical_rate_tendsto_atTop_of_fixed_rate spacing hpos h0 hΔ).eventually_gt_atTop M).exists
  exact absurd (hM s) (not_le.mpr hs)

#print axioms not_bounded_physical_rate_of_fixed_rate

end FixedCoupling

/-! ## 5. Two closed conditions -/

section Closed

/-- **The Gram form of reflection positivity, with real coefficients, survives a pointwise limit.**
If at every index `k` the reflected form `S k` is positive semidefinite on every family
`x : ι → J` of a fixed finite size, `0 ≤ ∑ᵢ ∑ᵢ' cᵢ cᵢ' S k (θ xᵢ) xᵢ'`, and `S (φ k) i j → Sinf i j`
at every pair, then `Sinf` is positive semidefinite on those families. A finite sum of convergent
sequences converges, and `[0, ∞)` is closed.

Scope: a statement about real numbers. `J`, `θ` and `S` are the caller's; that `S k` is a family of
lattice Schwinger values at physical positions is not constructed here.

DERIVED: `0` is the lower bound of the form. -/
theorem gram_nonneg_of_tendsto {J ι : Type*} [Fintype ι] (S : ℕ → J → J → ℝ) (Sinf : J → J → ℝ)
    (θ : J → J) (φ : ℕ → ℕ)
    (htend : ∀ i j, Filter.Tendsto (fun k => S (φ k) i j) Filter.atTop (nhds (Sinf i j)))
    (hRP : ∀ k (x : ι → J) (c : ι → ℝ), 0 ≤ ∑ i, ∑ i', c i * c i' * S k (θ (x i)) (x i'))
    (x : ι → J) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ i', c i * c i' * Sinf (θ (x i)) (x i') := by
  have h : Filter.Tendsto (fun k => ∑ i, ∑ i', c i * c i' * S (φ k) (θ (x i)) (x i'))
      Filter.atTop (nhds (∑ i, ∑ i', c i * c i' * Sinf (θ (x i)) (x i'))) :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun i' _ =>
      (htend (θ (x i)) (x i')).const_mul (c i * c i')))
  exact ge_of_tendsto' h (fun k => hRP (φ k) x c)

#print axioms gram_nonneg_of_tendsto

/-- **A spacing-independent clustering bound survives a pointwise limit.** If at every index `k` the
connected correlation `G k j` of a configuration `j` at physical separation `t j` obeys
`|G k j| ≤ K j · exp(−m · t j)`, with `K`, `m` and `t` not depending on `k`, and `G (φ k) j → Ginf j`,
then `|Ginf j| ≤ K j · exp(−m · t j)`.

`hB` needs correlations of one family of observables across members, at physical separations, with
`K` independent of `k`; sections 3 and 4 bound `‖Tⁿ u‖` on each member's own GNS space and do not
supply it. That `G k j` is a lattice correlation at a physical separation is the caller's.

DERIVED: no numeral. -/
theorem clustering_of_tendsto {J : Type*} (G : ℕ → J → ℝ) (Ginf : J → ℝ) (φ : ℕ → ℕ)
    (htend : ∀ j, Filter.Tendsto (fun k => G (φ k) j) Filter.atTop (nhds (Ginf j)))
    (K t : J → ℝ) {m : ℝ} (hB : ∀ k j, |G k j| ≤ K j * Real.exp (-m * t j)) (j : J) :
    |Ginf j| ≤ K j * Real.exp (-m * t j) :=
  le_of_tendsto' ((htend j).abs) (fun k => hB (φ k) j)

#print axioms clustering_of_tendsto

end Closed

end MassGap.ContinuumE
