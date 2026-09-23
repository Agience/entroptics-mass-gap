import Mathlib
import MassGap.Measure
import MassGap.WilsonHypercubic
import MassGap.ReflectionStrong
import MassGap.InfiniteVolume
import MassGap.WilsonModel

/-!
# MassGap.OSFamily — OS data on the Gibbs correlation, at an extent the index moves

This module builds a `Measure.LatticeYMFamily` whose reflected form is the connected `SU(3)` Wilson
plaquette correlation on a periodic four-dimensional lattice whose extent is the family index.
`WilsonGauge.ymFamilyGauge` and `WilsonModel.ymFamilyTension` are untouched and remain in the tree.

## The reflected form

`Qos β j a` is `connT (extent a) β (j.1 * j.2.1) (plaqBase _) (plaqAt _ (lagOf a j.2.2))`, and
`Qos_eq` identifies it with `WilsonBridge.corrClay (extent a) β (lagOf a j.2.2)`: the connected
correlation on the four-dimensional periodic `SU(3)` lattice of extent `2a + 2`, between the `(0,1)`
plaquette at the origin and the one displaced along direction `2` by the even lag the test
configuration names. No `min` or `max` is applied to it. The coupling `β` is a parameter held fixed
across the family and the index `a` sets the geometry.

For comparison, `WilsonGauge.QG j a` is `min (max _ 0) 1` of a one-plaquette expectation at coupling
`(a : ℝ)` on the single lattice `sysWilson 3 4 nYM` with `WilsonGauge.nYM = 2`.

## What discharges each OS field

* `os_rp` — `Qos_nonneg`, from `ReflectionStrong.corrClay_nonneg_even_lag`. That theorem takes an
  even lag and an even extent `Nap + 1 = 2 * m` with `0 < m`, and no condition on the sign of `β`;
  `Qos_nonneg_at_negative_coupling` instantiates it at `β = -1`. `lagOf` lands on the even
  sublattice by construction (`lagOf_even`), so the family's test configurations reach the even lags
  only. The clause is the single inequality `0 ≤ Q j a`; `LatticeYMFamily` carries no field for a
  Gram condition over a half-space algebra. The tree's Gram statements —
  `ReflectionStrong.wilson_expect_gram_nonneg` in the real case,
  `OSPositivity.wilson_osC_diag_re_nonneg` and `wilson_osC_gram_re_nonneg` in the complex
  sesquilinear case — are at finite volume on a slab and are not inputs here.
* `os_form` — `Qos_abs_le_four`, from `InfiniteVolume.wilsonCorrConn_abs_le_four`, whose only
  hypothesis is that the rank is nonzero. It is discharged as `Q ≤ 4 ≤ resolvedDim · 4`, which
  relates `Q` to the uniform bound and not to the spectrum.
* `os_euc` and `os_perm` — `Qos_actE` and `Qos_actP`. `Qos_depends_only_on_the_lag` records the
  mechanism: the reflected form reads `j` through `j.2.2` alone, and neither `actEOS` nor `actPOS`
  moves that component.
* `os_gap` — `Measure.familyOfSortedCount` derives it from an ordered spectrum and a count on it,
  both supplied by the caller, so it is a statement about that spectrum rather than about the
  measure. `osFamily` supplies `evUnit`, a single-resolved-mode placeholder in the same role as
  `WilsonGauge.evDemo`; `osFamilyTension` supplies `WilsonModel.wOne`, the witness read's
  single-mode spectrum, with `WilsonModel.edgeW` and `WilsonModel.cW`.

## The invariance

`connT` applies the axis relabelling `e` to all three Gibbs expectations the connected correlation is
built from — the product term and both one-point functions — and `connT_eq` removes it again by three
applications of `Symmetry.expect_invariant`: Haar-invariance of the `SU(3)` product measure over
links, composed with invariance of the Wilson action under the lattice's own axis relabelling
(`Symmetry.action_invariant` from `WilsonHypercubic.bd_axis`). The transport is put in by `connT`'s
definition, so `connT_eq` states that a deliberately transported object equals the untransported one;
what it establishes is the mechanism, on an object that has to survive a subtraction.
`WilsonGauge.QG_eq` is the same derivation on one expectation of a one-plaquette observable.

## Scope

* The extent sequence is `extent a = 2a + 2`, even at every index, which is the parity
  `ReflectionStrong`'s reflection geometry requires. It is unbounded (`ext_strictMono`) and the
  plaquette count diverges (`Nmodes_tendsto_volume`). The extent is the same in all four directions
  at once, so `a → ∞` is the infinite-volume limit with no second extent left over.
* `Nmodes a` is the plaquette count of the extent-`(2a+2)` lattice, `4 · 4 · (2a+2)⁴`
  (`Nmodes_eq`). In both assembled families the spectrum ignores its argument and
  `WilsonModel.resolvedDim_wOne` returns `1` at every positive count, so `Nmodes` enters the
  assembled family only through `1 ≤ Nmodes a`; any mode count bounded below by one gives the same
  family. What makes the index the geometry is `extent` inside `Qos`, not `Na`.
* `continuum_of_family` is Bolzano–Weierstrass: `os_continuum` and `os_continuum_tension` produce a
  strictly monotone `φ : ℕ → ℕ` and a pointwise limit `q : J → ℝ`. There is no uniqueness claim, no
  measure on `ℝ⁴` and no reconstruction. `InfiniteVolume.exists_infinite_volume_gapped_limit` has
  geometric decay on a derived coupling interval and is not composed with this family, so nothing
  here states a clustering property of the limit.
* Strict positivity is available at lag zero only: `Qos_pos_at_lag_zero`, from
  `PlaqVariance.corrClay_zero_pos`, with lag zero reachable by `lagOf_zero`.
  `GibbsPositive.ymFamilyGauge_Q_pos` gives `0 < Q` at every test configuration for the clamped
  family; a connected correlation at a general lag has no corresponding theorem in this tree.
* `OddLagSplit.plaqReflPositive_odd`, the tree's odd-lag positivity, carries `0 ≤ β`, `2 ≤ m` and a
  link-locality hypothesis, so it is not an available input for `os_rp` as stated here.
  `CharacterExpansion.NegControl.su3_kernel_neg_of_neg` shows one quadratic form of the character
  expansion is strictly negative at `β < 0`, which is a fact about that expansion and not about a
  lag.

Build: `python research/code/lean_build.py build MassGap.OSFamily`, or the whole tree with
`… build MassGap`. `MassGap.lean` imports this module, and `MassGap.ApertureRoute` imports it
because the flagship's measure field is `osFamilyTension` (the last section of this file).
-/

namespace MassGap.OSFamily

open MassGap.LatticeGauge MassGap.CompactGauge MassGap.Measure
open MeasureTheory Filter Topology

/-! ### The lattice, at an extent the index moves -/

/-- The rank of the Clay problem's gauge group.

DERIVED: the declaration's type is `ℕ` and carries no numeral. The `3` in the body is the rank the
Clay problem names; `SUN.SU` is general in the rank and `SU(3)` is the instantiation the statement
is about. -/
abbrev NYM : ℕ := 3

/-- `SU(3)`, the Clay problem's gauge group, as `SUN.SU NYM`.

DERIVED: the declaration's type is `Type` and carries no numeral; the rank in the body is `NYM`, the
rank the Clay statement names and the rank `WilsonGauge.sysYM` is built at. -/
abbrev G3 : Type := MassGap.SUN.SU NYM

/-- The periodic extent at family index `a`, namely `2a + 2`. Unbounded in `a`
(`ext_strictMono`), unlike `WilsonGauge.nYM`, which is the literal `2` at every index of that
family.

DERIVED: the declaration's type is `ℕ` and carries no numeral. The body is written `2 * a + 1 + 1`
so that the successor form `Nap + 1`, in which `ReflectionStrong.corrClay_nonneg_even_lag` states
its conclusion, is available without conversion. The `2` is a parity rather than a size: reflection
positivity on this lattice is proved at even extent `n = 2 * m`, the reflection needing a plane to
sit on, so `2a + 2` enumerates the even extents from the smallest at which a direction carries two
distinct sites. -/
abbrev extent (a : ℕ) : ℕ := 2 * a + 1 + 1

/-- `extent a = 2 * (a + 1)`: the extent is twice the half-extent, the parity
`ReflectionStrong`'s reflection geometry requires.

DERIVED: `2` is the parity of the reflection and `a + 1` the half-extent, so the `1` is that
half-extent's successor. Both are `extent`'s own. -/
theorem ext_eq_two_mul (a : ℕ) : extent a = 2 * (a + 1) := by
  show 2 * a + 1 + 1 = 2 * (a + 1); ring

/-- `0 < extent a` at every index, which is what the `NeZero` instances on the lattice below
consume.

DERIVED: `0` is the strict lower bound on a cardinality, not a threshold. -/
theorem ext_pos (a : ℕ) : 0 < extent a := Nat.succ_pos _

/-- `extent` is strictly monotone, so the family runs over an unbounded sequence of lattices
rather than repeating one. -/
theorem ext_strictMono : StrictMono extent := by
  intro a b hab
  show 2 * a + 1 + 1 < 2 * b + 1 + 1
  omega

/-- The four-dimensional periodic `SU(3)` Wilson system at extent `n`:
`WilsonHypercubic.sysWilson` at rank `NYM` and dimension `4`, with the extent left as the caller's.
Links are `(direction, site)` pairs and plaquettes `(plane, site)` pairs, the holonomy is the
ordered product around `U_μ(x) U_ν(x+μ̂) U_μ(x+ν̂)⁻¹ U_ν(x)⁻¹`, and the action density is
`1 - (1/3) Re tr` (`WilsonHypercubic.sysWilson_phi`).

DERIVED: the declaration's type is `System G3` and carries no numeral. In the body `4` is the
spacetime dimension and `NYM` the gauge rank, both the Clay problem's own data; the extent is an
argument. -/
noncomputable def sysOS (n : ℕ) [NeZero n] : System G3 :=
  MassGap.WilsonHypercubic.sysWilson NYM 4 n

/-- The lattice's axis-permutation symmetry at extent `n`, derived from the geometry: relabelling
the axes commutes with the unit shift (`WilsonHypercubic.shift_axis`), hence transports the
plaquette boundary word (`WilsonHypercubic.bd_axis`), hence is a `Symmetry` of the gauge system.

DERIVED: `4` is the spacetime dimension, the range of the axis index the permutation `e` acts
on. -/
noncomputable def symOS (n : ℕ) [NeZero n] (e : Equiv.Perm (Fin 4)) : Symmetry (sysOS n) :=
  MassGap.WilsonHypercubic.axisSymmetry NYM (n := n) e

/-- The Wilson plaquette-energy observable of one plaquette of the extent-`n` lattice: the local
action density `1 - (1/3) Re tr` of the ordered-loop holonomy. Its values lie in `[0, 2]`
(`WilsonReal.wilsonPlaqObs_nonneg`, `WilsonReal.wilsonPlaqObs_le_two`).

DERIVED: `4` is the spacetime dimension, appearing in the plaquette type `Plaq 4 n` and in the
boundary word `bd (d := 4)`. `NYM` is the rank, carried from `sysOS`. -/
noncomputable def obsOS (n : ℕ) [NeZero n] (p : MassGap.WilsonHypercubic.Plaq 4 n) :
    (sysOS n).Config → ℝ :=
  MassGap.WilsonReal.wilsonPlaqObs (N := NYM) (MassGap.WilsonHypercubic.bd (d := 4) (n := n)) p

/-! ### The reflected form: a connected Gibbs correlation, transported by the axis symmetry -/

/-- The connected Wilson correlation with every factor transported by the axis symmetry: three
`SU(3)` Gibbs expectations against probability Haar with the Wilson Boltzmann weight at coupling
`β` — the product term and the two one-point functions — each with its observable pulled back along
the axis relabelling `e`. No clamp is applied.

`connT_eq` removes the transport. It is a theorem rather than a `rfl` because the transport sits
inside three separate integrals and only Haar-invariance of the product measure takes it out.

DERIVED: `4` is the spacetime dimension, appearing in the permutation type `Equiv.Perm (Fin 4)` and
in the plaquette type `Plaq 4 n`, carried from `sysOS` and `symOS`. -/
noncomputable def connT (n : ℕ) [NeZero n] (β : ℝ) (e : Equiv.Perm (Fin 4))
    (p₀ p : MassGap.WilsonHypercubic.Plaq 4 n) : ℝ :=
  (sysOS n).expect (probHaar G3) β
      (fun U => obsOS n p₀ (Symmetry.reindex (symOS n e).onLink U)
              * obsOS n p (Symmetry.reindex (symOS n e).onLink U))
    - (sysOS n).expect (probHaar G3) β
        (fun U => obsOS n p₀ (Symmetry.reindex (symOS n e).onLink U))
      * (sysOS n).expect (probHaar G3) β
        (fun U => obsOS n p (Symmetry.reindex (symOS n e).onLink U))

/-- For every axis permutation `e`, the transported connected correlation `connT n β e p₀ p` equals
the untransported `WilsonBridge.wilsonCorrConn` at the same plaquettes and coupling. The proof is
three applications of `Symmetry.expect_invariant`: Haar-invariance of the `SU(3)` product measure
over links, composed with invariance of the Wilson action under the lattice's own axis relabelling
(`Symmetry.action_invariant` from `WilsonHypercubic.bd_axis`), removes the reindex from each of the
three integrals.

`WilsonGauge.QG_eq` is the same statement for one expectation of a one-plaquette observable; here
there are three, and the result is a connected correlation.

DERIVED: `4` is the spacetime dimension, the range of the axis index in `Equiv.Perm (Fin 4)`, in the
plaquette type `Plaq 4 n` and in the boundary word `bd (d := 4)`. It carries no other numeral: the
extent `n`, the coupling `β` and the plaquettes are all arguments. -/
theorem connT_eq (n : ℕ) [NeZero n] (β : ℝ) (e : Equiv.Perm (Fin 4))
    (p₀ p : MassGap.WilsonHypercubic.Plaq 4 n) :
    connT n β e p₀ p
      = MassGap.WilsonBridge.wilsonCorrConn (Nc := NYM)
          (MassGap.WilsonHypercubic.bd (d := 4) (n := n)) p₀ β p := by
  unfold connT
  rw [Symmetry.expect_invariant (sysOS n) (probHaar G3) (symOS n e) β
        (fun V => obsOS n p₀ V * obsOS n p V),
      Symmetry.expect_invariant (sysOS n) (probHaar G3) (symOS n e) β (obsOS n p₀),
      Symmetry.expect_invariant (sysOS n) (probHaar G3) (symOS n e) β (obsOS n p)]
  rfl

/-! ### Test configurations, the lag, and the reflected form -/

/-- Test configurations: a Euclidean component, a permutation component and a lag label, as a
triple. `Qos` reads the lag label only (`Qos_depends_only_on_the_lag`).

DERIVED: the declaration's type is `Type` and carries no numeral; the two `4`s in the body are the
spacetime dimension, the range of the axis index the two permutation components act on. -/
abbrev JOS : Type := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ

/-- The Euclidean action on test configurations: left-multiply the Euclidean component `j.1` and
leave the other two alone.

DERIVED: `4` is the spacetime dimension, so `Equiv.Perm (Fin 4)` is the hypercubic axis group the
lattice already carries (`WilsonHypercubic.axisSymmetry`). It is not a size. -/
def actEOS (g : Equiv.Perm (Fin 4)) (j : JOS) : JOS := (g * j.1, j.2.1, j.2.2)

/-- The permutation action on test configurations: left-multiply the permutation component
`j.2.1` and leave the other two alone.

DERIVED: `4` is the spacetime dimension, as in `actEOS` — the same axis group acting on the other
component. -/
def actPOS (σ : Equiv.Perm (Fin 4)) (j : JOS) : JOS := (j.1, σ * j.2.1, j.2.2)

/-- The separation a test configuration's label `k` names, as a site index of the extent-`extent a`
lattice: `2 * k` reduced modulo the extent.

DERIVED: the declaration's type `Fin (extent a)` carries no numeral. In the body, `2 * k` ranges
over the even sublattice of lags and `%` wraps it into the periodic lattice. The factor `2` is a
parity, not a scale: `ReflectionStrong.corrClay_nonneg_even_lag`'s hypothesis is that the lag is
even, so the even lags are the separations at which `Qos_nonneg` holds with no condition on the sign
of `β`. -/
def lagOf (a k : ℕ) : Fin (extent a) := ⟨2 * k % extent a, Nat.mod_lt _ (ext_pos a)⟩

/-- `(lagOf a k).val` is even, at every index and every label, which is
`ReflectionStrong.corrClay_nonneg_even_lag`'s hypothesis.

DERIVED: the statement carries no numeral; `Even` is Mathlib's predicate. In the proof, `2` is the
parity and `0` the residue an even number leaves. -/
theorem lagOf_even (a k : ℕ) : Even (lagOf a k).val := by
  have hdvd : (2 : ℕ) ∣ extent a := ⟨a + 1, ext_eq_two_mul a⟩
  have hmm : 2 * k % extent a % 2 = 2 * k % 2 := Nat.mod_mod_of_dvd (2 * k) hdvd
  rw [Nat.even_iff]
  show 2 * k % extent a % 2 = 0
  rw [hmm, Nat.mul_mod_right]

/-- The base plaquette: the `(0,1)` plane at the origin of the extent-`n` lattice.

DERIVED: `4` is the spacetime dimension, in the plaquette type `Plaq 4 n`. The `0` and `1` in the
body are the two direction indices spanning a plane — a plane needs two, and which two is a naming
freedom on a lattice whose axes are interchangeable (`WilsonHypercubic.axisSymmetry`). The site is
the origin, `fun _ => 0`, immaterial by periodicity. -/
def plaqBase (n : ℕ) [NeZero n] : MassGap.WilsonHypercubic.Plaq 4 n := ((0, 1), fun _ => 0)

/-- The displaced plaquette: the same `(0,1)` plane, `lag` steps along direction `2`.

DERIVED: `4` is the spacetime dimension, in the plaquette type `Plaq 4 n`. In the body `0` and `1`
span the plane as in `plaqBase`, and `2` is a direction transverse to that plane, which makes the
lag a spatial separation rather than an in-plane offset; such a direction exists because the
dimension exceeds two. -/
def plaqAt (n : ℕ) [NeZero n] (lag : Fin n) : MassGap.WilsonHypercubic.Plaq 4 n :=
  ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 lag)

/-- The reflected Schwinger form. `Qos β j a` is the connected `SU(3)` Wilson plaquette
correlation at coupling `β`, on the four-dimensional periodic lattice of extent `extent a`, between
the `(0,1)` plaquette at the origin and the one displaced along direction `2` by the even lag the
test configuration names, with both observables and the product transported by the axis permutation
`j.1 * j.2.1`. No `min` or `max` is applied.

`WilsonGauge.QG` is `min (max _ 0) 1` of a one-plaquette expectation at coupling `(a : ℝ)`; here the
coupling is the parameter `β` and the index `a` is the extent.

DERIVED: the statement carries no numeral — the plane, the lag axis and the extent carry their notes
at `plaqBase`, `plaqAt`, `lagOf` and `extent`. -/
noncomputable def Qos (β : ℝ) (j : JOS) (a : ℕ) : ℝ :=
  connT (extent a) β (j.1 * j.2.1) (plaqBase (extent a)) (plaqAt (extent a) (lagOf a j.2.2))

/-- `Qos β j a = WilsonBridge.corrClay (extent a) β (lagOf a j.2.2)`. The transport is removed by
`connT_eq`, leaving the connected `SU(3)` correlation on the four-dimensional periodic lattice, with
`β` in the coupling slot and `extent a` in the extent slot. Every other statement about the family
below is proved through this identity.

DERIVED: the statement carries no numeral; `extent` and `lagOf` carry their own notes. -/
theorem Qos_eq (β : ℝ) (j : JOS) (a : ℕ) :
    Qos β j a = MassGap.WilsonBridge.corrClay (extent a) β (lagOf a j.2.2) := by
  unfold Qos
  rw [connT_eq]
  rfl

/-! ### The three OS clauses that are statements about the measure -/

/-- `0 ≤ Qos β j a` at every real coupling, every index and every test configuration — the family's
`os_rp` clause. The input is `ReflectionStrong.corrClay_nonneg_even_lag`, which obtains
nonnegativity of the connected correlation from the half-space module statement, reflection
positivity as a quadratic form on the slab algebra, with no condition on the sign of `β`.
Nonnegativity of the unconnected correlation would follow from positivity of the state alone; it is
the subtraction of the disconnected part that makes this an RP consequence.

DERIVED: `0` is the lower bound in the conclusion. In the proof, `2 * a + 1` is the aperture —
`corrClay_nonneg_even_lag` states its conclusion at extent `Nap + 1`, so `Nap = 2a + 1` and the
extent is `2a + 2` — and `a + 1` is the half-extent the reflection sits at. Both are `extent`'s
own. -/
theorem Qos_nonneg (β : ℝ) (j : JOS) (a : ℕ) : 0 ≤ Qos β j a := by
  rw [Qos_eq]
  exact MassGap.ReflectionStrong.corrClay_nonneg_even_lag (2 * a + 1) (a + 1)
    (ext_eq_two_mul a) (Nat.succ_pos a) β (lagOf_even a j.2.2)

/-- `Qos_nonneg` at the coupling `-1`, a negative value. `OddLagSplit.plaqReflPositive_odd`, the
tree's odd-lag positivity, carries `0 ≤ β`; this statement shows the even-lag input has no such
restriction. `CharacterExpansion.NegControl.su3_kernel_neg_of_neg` shows one quadratic form of the
character expansion is strictly negative at `β < 0`, which is a fact about that expansion rather
than about a lag.

DERIVED: `1` is the magnitude of the coupling `-1`, chosen as a value of the sign the odd-lag route
excludes rather than fitted or measured; any negative value would serve, since `Qos_nonneg` is
quantified over all real `β`. `0` is the lower bound in the conclusion, as in `Qos_nonneg`. -/
theorem Qos_nonneg_at_negative_coupling (j : JOS) (a : ℕ) : 0 ≤ Qos (-1 : ℝ) j a :=
  Qos_nonneg (-1) j a

/-- `|Qos β j a| ≤ 4` at every real coupling, every index and every test configuration, with no
hypothesis and no extent in the constant. `InfiniteVolume.wilsonCorrConn_abs_le_four` supplies it:
the Wilson plaquette density lies in `[0, 2]` and the Gibbs state is a contractive probability state
(`WilsonReal.wilsonSystem_expect_abs_le`), so the unconnected correlation and the disconnected part
both lie in `[0, 4]`.

DERIVED: `4 = 2 · 2` is the square of the Wilson density's range `[0, 2]`, and is
`wilsonCorrConn_abs_le_four`'s own constant rather than one chosen here. The proof discharges that
theorem's rank hypothesis with `3 ≠ 0`. -/
theorem Qos_abs_le_four (β : ℝ) (j : JOS) (a : ℕ) : |Qos β j a| ≤ 4 := by
  unfold Qos
  rw [connT_eq]
  exact MassGap.InfiniteVolume.wilsonCorrConn_abs_le_four (Nc := NYM) (by norm_num) _ _ _ _

/-- `Qos β (actEOS g j) a = Qos β j a` — the family's `os_euc` clause. Both sides reduce by
`Qos_eq` to the same correlation: `actEOS` moves `j.1`, which the right-hand side of `Qos_eq` does
not mention, and `connT_eq` has already removed the transport the Euclidean component supplies
through `Symmetry.expect_invariant`.

DERIVED: `4` is the spacetime dimension, the range of the axis index in the permutation type
`Equiv.Perm (Fin 4)` that `g` inhabits. -/
theorem Qos_actE (β : ℝ) (g : Equiv.Perm (Fin 4)) (j : JOS) (a : ℕ) :
    Qos β (actEOS g j) a = Qos β j a := by
  have hlab : (actEOS g j).2.2 = j.2.2 := rfl
  rw [Qos_eq, hlab, Qos_eq]

/-- `Qos β (actPOS σ j) a = Qos β j a` — the family's `os_perm` clause, by the same route as
`Qos_actE` at the other permutation component `j.2.1`.

DERIVED: `4` is the spacetime dimension, the range of the axis index in the permutation type
`Equiv.Perm (Fin 4)` that `σ` inhabits. -/
theorem Qos_actP (β : ℝ) (σ : Equiv.Perm (Fin 4)) (j : JOS) (a : ℕ) :
    Qos β (actPOS σ j) a = Qos β j a := by
  have hlab : (actPOS σ j).2.2 = j.2.2 := rfl
  rw [Qos_eq, hlab, Qos_eq]

/-! ### The mode count: the lattice's plaquette count, and it diverges -/

/-- The mode count at index `a`: the cardinality of the plaquette type of the extent-`extent a`
lattice, which is the lattice the reflected form is integrated over. `LatticeYMFamily.Na` is
documented as the lattice mode count at spacing index `a`; `WilsonGauge` supplies `NaG a = a + 1`
for that field.

DERIVED: the declaration's type is `ℕ` and carries no numeral; the `4` in the body is the spacetime
dimension in the plaquette type `Plaq 4 (extent a)`. The value is a cardinality. -/
def Nmodes (a : ℕ) : ℕ := Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (extent a))

/-- The mode count in closed form: `Nmodes a = 4 * 4 * (2 * a + 1 + 1) ^ 4`.

DERIVED: `4 * 4` is the number of ordered direction pairs in four dimensions, the exponent `4` is
the number of directions the sites range over, and `(2 * a + 1 + 1)` is `extent a` written out, so
its `2` is the parity and its two `1`s are `extent`'s own successors. The whole identity is
`WilsonHypercubic.card_plaq` at `d = 4`. -/
theorem Nmodes_eq (a : ℕ) : Nmodes a = 4 * 4 * (2 * a + 1 + 1) ^ 4 :=
  MassGap.WilsonHypercubic.card_plaq 4 (extent a)

/-- `0 < Nmodes a` at every index, which is what `hres_wOne` and
`WilsonModel.resolvedDim_wOne` consume.

DERIVED: `0` is the strict lower bound on a cardinality; the numerals in the proof are
`Nmodes_eq`'s. -/
theorem Nmodes_pos (a : ℕ) : 0 < Nmodes a := by
  rw [Nmodes_eq]; positivity

/-- `(Nmodes a : ℝ) → ∞` as `a → ∞`, by `InfiniteVolume.clay_volume_tendsto_atTop` composed with
the index-to-aperture map. The extent is the same in all four directions at once, so the plaquette
count is the volume and `a → ∞` is the infinite-volume limit.

DERIVED: the statement carries no numeral. In the proof `2 * a + 1` is `extent`'s aperture, since
`extent a = (2a + 1) + 1`. -/
theorem Nmodes_tendsto_volume : Tendsto (fun a : ℕ => (Nmodes a : ℝ)) atTop atTop := by
  have hg : Tendsto (fun a : ℕ => 2 * a + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  exact MassGap.InfiniteVolume.clay_volume_tendsto_atTop.comp hg

/-! ### The family

`Measure.familyOfSortedCount` does not take the infrared clause `os_gap` directly. It takes an
ordered spectrum and a bound on how many of its modes clear the noise edge, and derives `os_gap`
from the pair. `WilsonGauge` uses the same constructor, so the spectrum side is the same interface
here as there. -/

/-- The OS data family on the connected Gibbs correlation, at extent `extent a`, from a spectrum
`ev` the caller supplies together with an ordering, a count bound and a resolution bound.

Three of the four OS fields are statements about the `SU(3)` Wilson measure:

* `os_rp` — `Qos_nonneg`, nonnegativity on the even lags at every real `β`;
* `os_form` — `Qos_abs_le_four`, against `B = 4`;
* `os_euc` and `os_perm` — `Qos_actE` and `Qos_actP`, from `Symmetry.expect_invariant`.

`os_gap` is derived by `familyOfSortedCount` from `hsorted` and `hcount`, which are facts about
`ev`. At `osFamily` that spectrum is `evUnit`, at `osFamilyTension` it is `WilsonModel.wOne`.

Two points on how the fields are discharged. `LatticeYMFamily.os_form` is documented as relating the
reflected form to the resolved modes; here it is discharged as `Q ≤ 4 ≤ resolvedDim · 4`, which uses
only the uniform bound and `hres`. And `Na := Nmodes` is the lattice's plaquette count, but the
spectra used below ignore their index argument, so the assembled family uses `Nmodes` only through
`1 ≤ resolvedDim …`; any mode count bounded below by one gives the same family.

DERIVED: `1` is the resolution bound `hres` requires of `resolvedDim` at every index, and it is what
the `os_form` calculation multiplies `4` by. In the proof, `4` is `B`, which is
`InfiniteVolume.wilsonCorrConn_abs_le_four`'s constant — the square of the Wilson density's range
`[0, 2]` — and `4` also appears in `Equiv.Perm (Fin 4)`, the spacetime dimension. -/
noncomputable def osFamilyCounted (β : ℝ)
    (ev : ℕ → ℕ → ℝ) (edge c : ℝ)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((resolvedDim (Finset.range (Nmodes a)) (ev a) edge : ℕ) : ℝ) ≤ c)
    (hres : ∀ a, 1 ≤ resolvedDim (Finset.range (Nmodes a)) (ev a) edge) : LatticeYMFamily :=
  familyOfSortedCount JOS (Equiv.Perm (Fin 4)) actEOS (Equiv.Perm (Fin 4)) actPOS
    Nmodes ev (Qos β) edge c 4 (by norm_num) hsorted hcount
    (fun j a => Qos_nonneg β j a)
    (fun j a => by
      have h1 : (1 : ℝ) ≤ (resolvedDim (Finset.range (Nmodes a)) (ev a) edge : ℝ) := by
        exact_mod_cast hres a
      calc Qos β j a ≤ 4 := le_trans (le_abs_self _) (Qos_abs_le_four β j a)
        _ = 1 * 4 := (one_mul 4).symm
        _ ≤ (resolvedDim (Finset.range (Nmodes a)) (ev a) edge : ℝ) * 4 :=
            mul_le_mul_of_nonneg_right h1 (by norm_num))
    (fun g j a => Qos_actE β g j a)
    (fun σ j a => Qos_actP β σ j a)

/-- `continuum_of_family` applied to `osFamilyCounted`, at every real coupling: a strictly
monotone `φ : ℕ → ℕ` and a limit `q` with pointwise convergence of `Q j (φ k)`, the temperedness
bound `|q j| ≤ ⌈c⌉₊ · B`, nonnegativity of `q`, and invariance of `q` under both group actions.

The sequence this takes a limit of runs over the extent at fixed coupling.
`WilsonGauge.ym_continuum_gauge_counted` takes a limit of a sequence in the coupling at a fixed
volume.

DERIVED: `1` is the resolution bound in `hres`, carried from `osFamilyCounted`. `0` is the lower
bound in the `∀ j, 0 ≤ q j` conjunct, which is the limit of `os_rp`. -/
theorem os_continuum_counted (β : ℝ)
    (ev : ℕ → ℕ → ℝ) (edge c : ℝ)
    (hsorted : ∀ a, ∀ m n : ℕ, m ≤ n → ev a n ≤ ev a m)
    (hcount : ∀ a, ((resolvedDim (Finset.range (Nmodes a)) (ev a) edge : ℕ) : ℝ) ≤ c)
    (hres : ∀ a, 1 ≤ resolvedDim (Finset.range (Nmodes a)) (ev a) edge) :
    ∃ (q : (osFamilyCounted β ev edge c hsorted hcount hres).J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (osFamilyCounted β ev edge c hsorted hcount hres).Q j (φ k))
              atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(osFamilyCounted β ev edge c hsorted hcount hres).c⌉₊ : ℝ)
              * (osFamilyCounted β ev edge c hsorted hcount hres).B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((osFamilyCounted β ev edge c hsorted hcount hres).actE g j) = q j) ∧
      (∀ σ j, q ((osFamilyCounted β ev edge c hsorted hcount hres).actP σ j) = q j) :=
  continuum_of_family (osFamilyCounted β ev edge c hsorted hcount hres)

/-! ### An unconditional instance

The three spectrum hypotheses are discharged at a single-resolved-mode spectrum, which makes
`os_continuum` unconditional. That spectrum is a placeholder rather than a measured or derived
quantity, in the same role `WilsonGauge.evDemo` plays, and it is stated in its own section apart
from the measure side. -/

/-- A spectrum with a single supra-edge mode: the mode at index `0` takes the value `1` and every
other mode takes `0`. The index argument is ignored.

DERIVED: the declaration's type is `ℕ → ℕ → ℝ` and carries no numeral. In the body, `0` is the index
of the single supra-edge mode and `1` and `0` are the two values the spectrum takes; nothing is
compared against them. -/
noncomputable def evUnit (_a n : ℕ) : ℝ := if n = 0 then 1 else 0

/-- `resolvedDim (Finset.range (Nmodes a)) (evUnit a) (1 / 2) = 1` at every index: exactly one
mode of `evUnit` clears the floor `1 / 2`.

DERIVED: `1 / 2` is a value strictly between the two `evUnit` takes; nothing below depends on which
such value is used, and the theorem is stated at this one. `1` is the resulting count. -/
theorem resolvedDim_evUnit (a : ℕ) :
    resolvedDim (Finset.range (Nmodes a)) (evUnit a) (1 / 2) = 1 := by
  have hfilter : (Finset.range (Nmodes a)).filter (fun k => (1 / 2 : ℝ) < evUnit a k) = {0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, evUnit]
    constructor
    · rintro ⟨_, hlt⟩
      by_contra hk
      rw [if_neg hk] at hlt
      linarith
    · rintro rfl
      exact ⟨Nmodes_pos a, by norm_num⟩
  rw [resolvedDim, hfilter, Finset.card_singleton]

/-- `evUnit a` is non-increasing in the mode index, which is `familyOfSortedCount`'s `hsorted`.

DERIVED: the statement carries no numeral. In the proof `0` is the index of the leading mode. -/
theorem evUnit_sorted (a : ℕ) : ∀ m n : ℕ, m ≤ n → evUnit a n ≤ evUnit a m := by
  intro m n hmn
  by_cases hm : m = 0
  · subst hm
    simp only [evUnit, if_pos rfl]
    split <;> norm_num
  · have hn : n ≠ 0 := by
      intro h; exact hm (Nat.le_zero.mp (h ▸ hmn))
    simp [evUnit, if_neg hm, if_neg hn]

/-- The count bound at `c = 1`: at most one mode of `evUnit` clears the floor `1 / 2`. This is
`familyOfSortedCount`'s `hcount`.

DERIVED: `1 / 2` is the floor carried from `resolvedDim_evUnit`; `1` is both the count that theorem
returns and the value of `c` this bounds it by. -/
theorem evUnit_count (a : ℕ) :
    ((resolvedDim (Finset.range (Nmodes a)) (evUnit a) (1 / 2) : ℕ) : ℝ) ≤ 1 := by
  rw [resolvedDim_evUnit]; norm_num

/-- At least one mode of `evUnit` clears the floor `1 / 2`. This is `familyOfSortedCount`'s
`hres`, which `osFamilyCounted`'s `os_form` calculation consumes.

DERIVED: `1 / 2` is the floor carried from `resolvedDim_evUnit`; `1` is the count it returns. -/
theorem evUnit_res (a : ℕ) : 1 ≤ resolvedDim (Finset.range (Nmodes a)) (evUnit a) (1 / 2) := by
  rw [resolvedDim_evUnit]

/-- `osFamilyCounted` at the single-supra-edge-mode spectrum `evUnit`, with floor `1 / 2` and
count `1`: `SU(3)` OS data on the connected Gibbs correlation at extent `extent a`, with no clamp
and no spectrum hypothesis left open.

DERIVED: the declaration's type is `LatticeYMFamily` and carries no numeral. In the body, the floor
`1 / 2` is a value strictly between the two `evUnit` takes, the one `resolvedDim_evUnit` is stated
at, and the count `1` is what that theorem returns. -/
noncomputable def osFamily (β : ℝ) : LatticeYMFamily :=
  osFamilyCounted β evUnit (1 / 2) 1 evUnit_sorted evUnit_count evUnit_res

/-- `continuum_of_family` applied to `osFamily`, at every real coupling: a strictly monotone
`φ : ℕ → ℕ` and a limit `q` with pointwise convergence, the temperedness bound `|q j| ≤ ⌈c⌉₊ · B`,
nonnegativity, and invariance under both group actions.

DERIVED: `0` is the lower bound in the `∀ j, 0 ≤ q j` conjunct, the limit of `os_rp`. The family's
floor and count are `osFamily`'s, documented there. -/
theorem os_continuum (β : ℝ) :
    ∃ (q : (osFamily β).J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (osFamily β).Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(osFamily β).c⌉₊ : ℝ) * (osFamily β).B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((osFamily β).actE g j) = q j) ∧
      (∀ σ j, q ((osFamily β).actP σ j) = q j) :=
  continuum_of_family (osFamily β)

/-! ### What the family's own fields are

Each of these is `rfl`, so they let a reader check the fields without unfolding the constructor. -/

/-- The family's reflected form is `Qos`, the connected correlation.

DERIVED: the statement carries no numeral. -/
theorem osFamily_Q (β : ℝ) : (osFamily β).Q = Qos β := rfl

/-- The family's mode count is `Nmodes`, the lattice's plaquette count.

DERIVED: the statement carries no numeral; `Nmodes` carries its own note. -/
theorem osFamily_Na (β : ℝ) : (osFamily β).Na = Nmodes := rfl

/-- The family's per-mode bound `B` is `4`.

DERIVED: `4` is `InfiniteVolume.wilsonCorrConn_abs_le_four`'s constant, the square of the Wilson
density's range `[0, 2]`, passed to `osFamilyCounted` as `B`. -/
theorem osFamily_B (β : ℝ) : (osFamily β).B = 4 := rfl

/-- The family's reflected form at index `a` is `WilsonBridge.corrClay (extent a) β (lagOf a j.2.2)`:
the index sets the extent and `β` is the coupling.

DERIVED: the statement carries no numeral; `extent` and `lagOf` carry their own notes. -/
theorem osFamily_Q_eq (β : ℝ) (j : JOS) (a : ℕ) :
    (osFamily β).Q j a = MassGap.WilsonBridge.corrClay (extent a) β (lagOf a j.2.2) :=
  Qos_eq β j a

/-! ### The same measure with the tension's infrared input

`osFamily` has infrared cutoff `c = 1`, the count `evUnit` returns. A `WilsonRealization` (in
`MassGap.FullModel`) requires `model.measure.c = params.irCutoff`, and `WilsonModel.paramsTension`
reads its cutoff off the witness read's measured tension
(`WilsonModel.paramsTension_irCutoff : paramsTension.irCutoff = cW`). `osFamilyTension` is therefore
`osFamilyCounted` at the tension's own edge and count.

The measure side is identical between the two: `os_rp`, `os_form`, `os_euc` and `os_perm` are
`Qos_nonneg`, `Qos_abs_le_four`, `Qos_actE` and `Qos_actP` either way — the connected `SU(3)` Wilson
correlation at extent `2a + 2`, with no clamp. What differs is the spectrum `os_gap` is derived
from, which becomes `WilsonModel.wOne`, the spectrum `WilsonModel.ymFamilyTension` uses, counted by
`WilsonModel.count_le_of_tension_uniform` over `Nmodes` rather than over
`WilsonGauge.NaG a = a + 1`. `os_gap` is thus a statement about `wOne`, the witness read's
single-mode spectrum, here as it is in `ymFamilyTension`. -/

/-- The count bound `resolvedDim (Finset.range (Nmodes a)) wOne edgeW ≤ cW`, at the lattice's own
mode count. `WilsonModel.hcountW` is the same statement at `WilsonGauge.NaG`.
`WilsonModel.count_le_of_tension_uniform` is general in `Na` — all it needs of the index set is a
bound on the weight sum, and `WilsonModel.sum_wOne` supplies that at any positive count — so the
bound transfers to `Nmodes`, whose positivity is `Nmodes_pos`.

The right-hand side of `count_le_of_tension_uniform` contains no `Na`, and
`WilsonModel.resolvedDim_wOne` returns `1` at every positive count, so `Nmodes` and
`WilsonGauge.NaG` give the same family. What makes the index the geometry is `extent` inside `Qos`,
not `Na`.

DERIVED: the statement carries no numeral of its own. In the proof, `W := 1` is the witness read's
total weight (`WilsonModel.sum_wOne`), and the numerals inside the bound are `WilsonModel.cW`'s
own. -/
theorem hcount_wOne (a : ℕ) :
    ((resolvedDim (Finset.range (Nmodes a)) ((fun _ => MassGap.WilsonModel.wOne) a)
        MassGap.WilsonModel.edgeW : ℕ) : ℝ) ≤ MassGap.WilsonModel.cW :=
  MassGap.WilsonModel.count_le_of_tension_uniform
    (k := MassGap.WilsonModel.kW) (Na := Nmodes) (w := MassGap.WilsonModel.wOne)
    (lam := MassGap.WilsonModel.lamConst MassGap.WilsonModel.rW) MassGap.WilsonModel.readW
    (fun a d => MassGap.WilsonModel.geoRead_is_sum MassGap.WilsonModel.rW
      MassGap.WilsonModel.rW_nonneg MassGap.WilsonModel.kW (Nmodes a) (Nmodes_pos a) d)
    MassGap.WilsonModel.wOne_nonneg (fun _ => MassGap.WilsonModel.rW_nonneg)
    (fun _ => MassGap.WilsonModel.rW_lt_one.le)
    (lam0 := MassGap.WilsonModel.rW) MassGap.WilsonModel.rW_pos
    MassGap.WilsonModel.rW_lt_one.le (fun _ => le_refl _)
    (edge := MassGap.WilsonModel.edgeW) MassGap.WilsonModel.edgeW_pos
    (W := 1) (fun a => le_of_eq (MassGap.WilsonModel.sum_wOne (Nmodes a) (Nmodes_pos a)))
    MassGap.WilsonModel.readW_cos_pos MassGap.WilsonModel.readW_tension_lt_floor a

/-- At least one mode of `WilsonModel.wOne` clears the witness edge at every index, which is
`osFamilyCounted`'s `hres` and what its `os_form` calculation consumes.

DERIVED: `1` is the count `WilsonModel.resolvedDim_wOne` returns at any positive mode count, not a
threshold. -/
theorem hres_wOne (a : ℕ) :
    1 ≤ resolvedDim (Finset.range (Nmodes a)) ((fun _ => MassGap.WilsonModel.wOne) a)
      MassGap.WilsonModel.edgeW := by
  rw [MassGap.WilsonModel.resolvedDim_wOne (Nmodes a) (Nmodes_pos a) MassGap.WilsonModel.edgeW
    MassGap.WilsonModel.edgeW_pos MassGap.WilsonModel.edgeW_lt_one]

/-- The family the flagship carries: `osFamilyCounted` at the witness read's spectrum
`WilsonModel.wOne`, edge `WilsonModel.edgeW` and count `WilsonModel.cW`. Its `c` is `cW`
(`osFamilyTension_c`), which lets it stand where `WilsonModel.ymFamilyTension` stood in a
`WilsonRealization` without changing `WilsonModel.paramsTension`.

DERIVED: the declaration's type is `LatticeYMFamily` and carries no numeral; `edgeW`, `cW` and
`wOne` carry their notes in `WilsonModel`. -/
noncomputable def osFamilyTension (β : ℝ) : LatticeYMFamily :=
  osFamilyCounted β (fun _ => MassGap.WilsonModel.wOne) MassGap.WilsonModel.edgeW
    MassGap.WilsonModel.cW MassGap.WilsonModel.wOne_sorted hcount_wOne hres_wOne

/-- `(osFamilyTension β).c = WilsonModel.cW`, by `rfl`, so `WilsonRealization.hc` discharges
against `WilsonModel.paramsTension` unchanged.

DERIVED: the statement carries no numeral; `cW` carries its note in `WilsonModel`. -/
theorem osFamilyTension_c (β : ℝ) : (osFamilyTension β).c = MassGap.WilsonModel.cW := rfl

/-- The flagship family's per-mode bound `B` is `4`, the same constant `osFamily_B` records.

DERIVED: `4` is `InfiniteVolume.wilsonCorrConn_abs_le_four`'s constant, the square of the Wilson
density's range `[0, 2]`, passed to `osFamilyCounted` as `B`. -/
theorem osFamilyTension_B (β : ℝ) : (osFamilyTension β).B = 4 := rfl

/-- The flagship family's reflected form at index `a` is
`WilsonBridge.corrClay (extent a) β (lagOf a j.2.2)`, the same identity `osFamily_Q_eq` records.

DERIVED: the statement carries no numeral; `extent` and `lagOf` carry their own notes. -/
theorem osFamilyTension_Q_eq (β : ℝ) (j : JOS) (a : ℕ) :
    (osFamilyTension β).Q j a = MassGap.WilsonBridge.corrClay (extent a) β (lagOf a j.2.2) :=
  Qos_eq β j a

/-- `continuum_of_family` applied to `osFamilyTension`, at every real coupling: a strictly
monotone `φ : ℕ → ℕ` and a limit `q` with pointwise convergence, the temperedness bound
`|q j| ≤ ⌈c⌉₊ · B`, nonnegativity, and invariance under both group actions. The conclusion is
quantified over `β`, so the coupling the flagship's model field is instantiated at does not enter
it.

DERIVED: `0` is the lower bound in the `∀ j, 0 ≤ q j` conjunct, the limit of `os_rp`. The family's
edge and count are `WilsonModel.edgeW` and `WilsonModel.cW`, documented there. -/
theorem os_continuum_tension (β : ℝ) :
    ∃ (q : (osFamilyTension β).J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (osFamilyTension β).Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(osFamilyTension β).c⌉₊ : ℝ) * (osFamilyTension β).B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((osFamilyTension β).actE g j) = q j) ∧
      (∀ σ j, q ((osFamilyTension β).actP σ j) = q j) :=
  continuum_of_family (osFamilyTension β)

/-! ### How the reflected form depends on the test configuration

Two statements about `Qos`'s dependence on `j`, proved in the direction they go. -/

/-- The reflected form reads the test configuration only through the lag label: two test
configurations agreeing on `j.2.2` give the same value, whatever their group components.
`Qos_eq`'s right-hand side mentions `j.2.2` and neither `j.1` nor `j.2.1`.

This is the mechanism behind `Qos_actE` and `Qos_actP`: `actEOS` multiplies `j.1` and `actPOS`
multiplies `j.2.1`, and neither touches `j.2.2`, so both actions move components the reflected form
does not read. `WilsonGauge.QG` satisfies its own invariance clauses the same way. `Qos` is not
constant in `j`, since it varies with the lag, but the lag is the component the two actions leave
fixed.

DERIVED: the statement carries no numeral. -/
theorem Qos_depends_only_on_the_lag (β : ℝ) (j j' : JOS) (a : ℕ) (h : j.2.2 = j'.2.2) :
    Qos β j a = Qos β j' a := by
  rw [Qos_eq, Qos_eq, h]

/-- `lagOf a 0 = 0`: the lag label `0` names the zero separation, so lag zero is in the family's
range of test configurations.

DERIVED: `0` is the label on the left and the separation it names on the right. The proof is
`2 * 0 % extent a = 0`. -/
theorem lagOf_zero (a : ℕ) : lagOf a 0 = 0 := by
  apply Fin.ext
  simp [lagOf]

/-- `0 < Qos β j a` at every index and every real coupling, for test configurations whose lag
label is `0`. At lag zero the connected correlation is the plaquette-energy variance, strictly
positive by `PlaqVariance.corrClay_zero_pos`, and lag zero is reachable by `lagOf_zero`. So `Qos` is
not identically zero.

The hypothesis `hj : j.2.2 = 0` is required: this is a lag-zero statement.
`GibbsPositive.ymFamilyGauge_Q_pos` gives `0 < Q` at every test configuration for the clamped
family, since a one-point plaquette expectation is strictly positive; a connected correlation at a
general lag has no corresponding theorem in this tree.

DERIVED: `0` is the lag label in `hj` and the strict lower bound in the conclusion. In the proof,
`2 * a + 1` is `extent`'s aperture, since `extent a = (2a + 1) + 1`. -/
theorem Qos_pos_at_lag_zero (β : ℝ) (j : JOS) (a : ℕ) (hj : j.2.2 = 0) : 0 < Qos β j a := by
  rw [Qos_eq, hj, lagOf_zero]
  exact MassGap.PlaqVariance.corrClay_zero_pos (2 * a + 1) β

/-- `Qos_pos_at_lag_zero` restated on `osFamilyTension`: `0 < (osFamilyTension β).Q j a` for test
configurations whose lag label is `0`.

DERIVED: `0` is the lag label in `hj` and the strict lower bound in the conclusion, the same two
occurrences as in `Qos_pos_at_lag_zero`. -/
theorem osFamilyTension_pos_at_lag_zero (β : ℝ) (j : JOS) (a : ℕ) (hj : j.2.2 = 0) :
    0 < (osFamilyTension β).Q j a :=
  Qos_pos_at_lag_zero β j a hj

section Audit
#print axioms ext_strictMono
#print axioms connT_eq
#print axioms lagOf_even
#print axioms Qos_eq
#print axioms Qos_nonneg
#print axioms Qos_nonneg_at_negative_coupling
#print axioms Qos_abs_le_four
#print axioms Qos_actE
#print axioms Qos_actP
#print axioms Nmodes_eq
#print axioms Nmodes_pos
#print axioms Nmodes_tendsto_volume
#print axioms osFamilyCounted
#print axioms os_continuum_counted
#print axioms resolvedDim_evUnit
#print axioms evUnit_sorted
#print axioms evUnit_count
#print axioms evUnit_res
#print axioms osFamily
#print axioms os_continuum
#print axioms osFamily_Q
#print axioms osFamily_Na
#print axioms osFamily_B
#print axioms osFamily_Q_eq
#print axioms hcount_wOne
#print axioms hres_wOne
#print axioms osFamilyTension
#print axioms osFamilyTension_c
#print axioms osFamilyTension_B
#print axioms osFamilyTension_Q_eq
#print axioms os_continuum_tension
#print axioms Qos_depends_only_on_the_lag
#print axioms lagOf_zero
#print axioms Qos_pos_at_lag_zero
#print axioms osFamilyTension_pos_at_lag_zero
end Audit

end MassGap.OSFamily
