import Mathlib
import MassGap.Measure
import MassGap.WilsonHypercubic
import MassGap.ReflectionStrong
import MassGap.InfiniteVolume

/-!
# MassGap.OSFamily — the OS data family on the genuine Gibbs correlation, at arbitrary extent

## What this file is for

`WilsonGauge.ymFamilyGauge` supplies a `Measure.LatticeYMFamily` whose reflected form is

    QG j a = min (max (sysYM.expect (probHaar G3) (a : ℝ) (O0 ∘ reindex …)) 0) 1

and three things about that object are weaker than the name "OS0–OS3 at finite spacing" reads.

1. **The `[0,1]` clamp is doing the work.** `os_rp : 0 ≤ QG` holds because `QG` is `max _ 0`, and
   `os_form` at `B = 1` because it is `min _ 1`. Neither clause is a property of the measure; both
   would hold of any function whatever under the same clamp.
2. **One lattice.** `WilsonGauge.nYM := 2`, so `sysYM = sysWilson 3 4 2` and every member of the
   family lives on the same `2⁴` lattice. The index `a` never reaches a second geometry.
3. **The index is fed in as the COUPLING.** `QG j a` passes `(a : ℝ)` to `expect … (a : ℝ) …`, which
   is the Gibbs coupling `β`. So the sequence whose limit `continuum_of_family` takes is a sequence
   in the coupling at fixed volume, not a sequence in the lattice spacing.

This file builds a second family, `osFamily`, beside those — `ymFamilyGauge` and `ymFamilyTension`
are untouched — in which all three are repaired:

* **No clamp.** `Qos` IS the connected Wilson plaquette correlation (`Qos_eq`), and both OS clauses
  are theorems about it: `os_rp` from reflection positivity
  (`ReflectionStrong.corrClay_nonneg_even_lag`, a genuine RP theorem at every real `β` on the even
  lags), `os_form` from `InfiniteVolume.wilsonCorrConn_abs_le_four`, which carries no hypothesis
  beyond `3 ≠ 0`.
* **The extent varies.** Index `a` sets the periodic extent `2a + 2`, so the family runs over an
  unbounded sequence of four-dimensional lattices and the mode count `Nmodes` is that lattice's own
  plaquette count, diverging by `InfiniteVolume.clay_volume_tendsto_atTop` (`Nmodes_tendsto_volume`).
  This is the shape `InfiniteVolume` already uses: `N` is the sequence index and `N → ∞` IS the
  infinite-volume limit, because the extent is the same in all four directions at once. The extent is
  load-bearing — `Qos β j a` is an integral over the extent-`(2a+2)` lattice — but `Nmodes` is not,
  until a measured spectrum replaces `evUnit`; see the note at `osFamilyCounted`.
* **The coupling is a parameter, not the index.** `osFamily` takes `β : ℝ` and holds it fixed across
  the sequence. `Qos_eq` displays exactly that: `β` is `corrClay`'s coupling, `a` is its extent.

## What is kept

`WilsonGauge.QG_eq` derives the invariance from `Symmetry.expect_invariant` — Haar-invariance of the
`SU(3)` product measure composed with the hypercubic lattice's own axis permutation — rather than by
`rfl` through an inert label. That is the one part of the existing family that is a real theorem
about a real measure, and `connT_eq` here is the same derivation on a larger object: the transport is
removed from all THREE Gibbs expectations the connected correlation is built from (the product term
and both one-point functions), by three applications of `Symmetry.expect_invariant`. `os_euc` and
`os_perm` then follow from `Qos_eq`, whose right-hand side no longer mentions the transport.

What that does and does not establish, since the shape invites a misreading: `connT` puts the
transport in BY HAND, so `connT_eq` proves a deliberately transported object equals the untransported
one. What is a theorem is the MECHANISM — that the `SU(3)` product measure does not notice the axis
relabelling — not the existence of an invariant object. Same structure as `WilsonGauge.QG`; the
difference is the object being transported, and that the removal now has to survive a subtraction.

## What OS0–OS3 still lacks, stated plainly

A clamp-free family at arbitrary extent is still not OS0–OS3. What remains open is not hidden by any
definition here:

* **OS3 is positive semidefiniteness over the half-space algebra, not one nonnegative number.**
  `os_rp` asks only `0 ≤ Q j a`. A Gram statement does exist in the tree — the real-valued
  `ReflectionStrong.wilson_expect_gram_nonneg` on `LogConvex.localObs`, and the complex sesquilinear
  `OSPositivity.wilson_osC_diag_re_nonneg` / `wilson_osC_gram_re_nonneg` on `localObsC` (a DIFFERENT
  module, `MassGap.OSPositivity`, which this file does not import) — but only at FINITE volume, on
  the slab `blkS τ a m` / `blkR τ a m`, at an even extent. Nothing here carries any of that into the
  limit, and `LatticeYMFamily` has no field that could hold it.
* **The RP input is even-lag only.** `corrClay_nonneg_even_lag` is unconditional in `β`. The tree's
  only proof for the ODD lags, `OddLagSplit.plaqReflPositive_odd`, carries `0 ≤ β` together with
  `2 ≤ m` and a link-locality hypothesis; nothing shows odd-lag positivity FAILS without them, only
  that this development has not proved it. `lagOf` therefore lands on the even sublattice by
  construction, which is a restriction on which test configurations the family reaches, not a proof
  about the odd ones.
* **OS4 clustering is absent.** Nothing here proves the limit factorises at large separation.
  `InfiniteVolume.exists_infinite_volume_gapped_limit` has geometric decay, but only on a derived
  coupling interval `[0,b)`, and it is not composed with this family.
* **The limit is subsequential, and it is a limit of numbers.** `continuum_of_family` is
  Bolzano–Weierstrass: it produces a subsequence `φ` and a pointwise limit `q : J → ℝ`. There is no
  uniqueness, no measure on `ℝ⁴`, and no reconstruction. That is unchanged from `ymFamilyGauge`; what
  changed is what the sequence is a sequence OF.
* **The spectrum side is unchanged.** `evUnit` is a placeholder single-resolved-mode spectrum, the
  same role `WilsonGauge.evDemo` plays. It makes `osFamily` unconditional; it is not a measured
  spectrum, and `osFamilyCounted` is the constructor a measured one would go through.
* **Non-degeneracy is not carried over.** `GibbsPositive.ymFamilyGauge_Q_pos` proves `0 < Q` for the
  clamped family, because a one-point plaquette expectation is strictly positive. A CONNECTED
  correlation is not, so no such theorem is available here at a general lag. At lag zero it is —
  `PlaqVariance.corrClay_zero_pos` — and lag zero is reachable (`lagOf a 0 = 0`), so the family is
  not the identically-zero one; but that is a remark, not a theorem in this file.
* **This file is not in the root import list.** `MassGap.lean` does not import `MassGap.OSFamily`, so
  a whole-tree `lake build` is SILENT about it. It must be built by name, as below.

Build: `python research/code/lean_build.py build MassGap.OSFamily`.
-/

namespace MassGap.OSFamily

open MassGap.LatticeGauge MassGap.CompactGauge MassGap.Measure
open MeasureTheory Filter Topology

/-! ### The lattice, at an extent the index moves -/

/-- The rank of the Clay problem's gauge group.

DERIVED: `3` is the rank the Clay problem names. It is not this file's choice; `SUN.SU` is general in
the rank and `SU(3)` is the instantiation the statement is about. -/
abbrev NYM : ℕ := 3

/-- `SU(3)`, the Clay problem's gauge group.

DERIVED: the `3` is `NYM`, the rank the Clay statement names and the rank `WilsonGauge.sysYM` is
built at. It is carried, not chosen here. -/
abbrev G3 : Type := MassGap.SUN.SU NYM

/-- **The periodic extent at family index `a`.**

This is the whole of defect (2): `WilsonGauge.nYM` is the literal `2` and every member of that family
sits on the same `2⁴` lattice. Here the extent is a function of the index and is unbounded
(`ext_strictMono`, `Nmodes_tendsto_volume`).

DERIVED: the extent is `2a + 2`, written `2 * a + 1 + 1` so that the successor form `Nap + 1` that
`ReflectionStrong.corrClay_nonneg_even_lag` states its conclusion in is available without conversion.
The `2` is not a size: reflection positivity on this lattice is proved at EVEN extent (`n = 2 * m`,
the reflection has to have a plane to sit on), so the sequence of extents a genuine RP input can be
read at is the even ones, and `2a + 2` enumerates them from the smallest one at which a direction
carries two distinct sites. -/
abbrev extent (a : ℕ) : ℕ := 2 * a + 1 + 1

/-- The extent is twice the half-extent — the parity `ReflectionStrong`'s reflection geometry needs.

DERIVED: `2` is the parity of the reflection, `a + 1` the half-extent. -/
theorem ext_eq_two_mul (a : ℕ) : extent a = 2 * (a + 1) := by
  show 2 * a + 1 + 1 = 2 * (a + 1); ring

/-- The extent is positive at every index, so the lattice exists at every index.

DERIVED: the `0` is the boundary a cardinality cannot cross, not a threshold. -/
theorem ext_pos (a : ℕ) : 0 < extent a := Nat.succ_pos _

/-- **The extent genuinely moves with the index.** This is the statement `WilsonGauge` cannot make. -/
theorem ext_strictMono : StrictMono extent := by
  intro a b hab
  show 2 * a + 1 + 1 < 2 * b + 1 + 1
  omega

/-- **The four-dimensional periodic `SU(3)` Wilson system at extent `n`.**

`WilsonHypercubic.sysWilson` with the Clay problem's rank and dimension, and the extent left as the
caller's. Links are `(direction, site)` pairs and plaquettes `(plane, site)` pairs, the holonomy is
the ordered product around `U_μ(x) U_ν(x+μ̂) U_μ(x+ν̂)⁻¹ U_ν(x)⁻¹`, and the action density is Wilson's
`1 - (1/3) Re tr` (`WilsonHypercubic.sysWilson_phi`), which is what makes `β` move the measure.

DERIVED: `4` is four-dimensional spacetime and `NYM` the gauge rank — the Clay problem's own data.
The extent is an argument. -/
noncomputable def sysOS (n : ℕ) [NeZero n] : System G3 :=
  MassGap.WilsonHypercubic.sysWilson NYM 4 n

/-- The lattice's axis-permutation symmetry at extent `n`, from the geometry rather than asserted:
relabelling the axes commutes with the unit shift (`WilsonHypercubic.shift_axis`), hence transports
the plaquette boundary word (`bd_axis`), hence is a `Symmetry` of the gauge system.

DERIVED: `4` is the dimension whose axes are being permuted. -/
noncomputable def symOS (n : ℕ) [NeZero n] (e : Equiv.Perm (Fin 4)) : Symmetry (sysOS n) :=
  MassGap.WilsonHypercubic.axisSymmetry NYM (n := n) e

/-- The Wilson plaquette-energy observable of one plaquette of the extent-`n` lattice: the physical
local action density `1 - (1/3) Re tr` of the ordered-loop holonomy. Values lie in `[0,2]`
(`WilsonReal.wilsonPlaqObs_nonneg`, `wilsonPlaqObs_le_two`).

DERIVED: `4` is the dimension and `NYM` the rank, both carried from `sysOS`. -/
noncomputable def obsOS (n : ℕ) [NeZero n] (p : MassGap.WilsonHypercubic.Plaq 4 n) :
    (sysOS n).Config → ℝ :=
  MassGap.WilsonReal.wilsonPlaqObs (N := NYM) (MassGap.WilsonHypercubic.bd (d := 4) (n := n)) p

/-! ### The reflected form: a connected Gibbs correlation, transported by the axis symmetry -/

/-- **The connected Wilson correlation with every factor transported by the axis symmetry.**

Three genuine `SU(3)` Gibbs expectations against the canonical probability Haar measure, with the
Wilson Boltzmann weight at coupling `β`: the product term and the two one-point functions, each with
its observable pulled back along the axis relabelling `e`. Nothing is clamped and nothing is cut.

This is the object `connT_eq` removes the transport from, and it is the reason the removal is a
theorem rather than a definition: the transport sits inside three separate integrals and only
Haar-invariance of the product measure takes it out of them.

DERIVED: no literal in this definition. `4` is the dimension, carried from `sysOS`. -/
noncomputable def connT (n : ℕ) [NeZero n] (β : ℝ) (e : Equiv.Perm (Fin 4))
    (p₀ p : MassGap.WilsonHypercubic.Plaq 4 n) : ℝ :=
  (sysOS n).expect (probHaar G3) β
      (fun U => obsOS n p₀ (Symmetry.reindex (symOS n e).onLink U)
              * obsOS n p (Symmetry.reindex (symOS n e).onLink U))
    - (sysOS n).expect (probHaar G3) β
        (fun U => obsOS n p₀ (Symmetry.reindex (symOS n e).onLink U))
      * (sysOS n).expect (probHaar G3) β
        (fun U => obsOS n p (Symmetry.reindex (symOS n e).onLink U))

/-- **THE INVARIANCE, DERIVED — `WilsonGauge.QG_eq`'s content, on the connected correlation.**

For every axis permutation `e`, the transported connected correlation equals the untransported one.
The proof is three applications of `Symmetry.expect_invariant`: Haar-invariance of the `SU(3)`
product measure over links, composed with invariance of the Wilson action under the lattice's own
axis relabelling (`Symmetry.action_invariant` from `WilsonHypercubic.bd_axis`), removes the reindex
from each of the three integrals. No `rfl` on the correlation; the group element acts on a real
measure and the measure does not notice.

`WilsonGauge.QG_eq` does this for ONE expectation of a one-plaquette observable. Here it is three,
and the object it produces is the connected correlation whose decay is a mass rather than a single
plaquette energy.

DERIVED: no literal. -/
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

/-- Test configurations: a Euclidean component, a permutation component, and a lag label.

DERIVED: `4` is the dimension whose axis permutations act. -/
abbrev JOS : Type := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) × ℕ

/-- Euclidean action on test configurations: multiply the Euclidean component.

DERIVED: `4` is the problem's dimension, so `Equiv.Perm (Fin 4)` is the hypercubic axis group the
lattice already carries (`WilsonHypercubic.axisSymmetry`). Not a size of anything. -/
def actEOS (g : Equiv.Perm (Fin 4)) (j : JOS) : JOS := (g * j.1, j.2.1, j.2.2)

/-- Permutation action on test configurations: multiply the permutation component.

DERIVED: `4` is the problem's dimension, as in `actEOS` — the same axis group acting on the other
component. -/
def actPOS (σ : Equiv.Perm (Fin 4)) (j : JOS) : JOS := (j.1, σ * j.2.1, j.2.2)

/-- The separation the test configuration's label names, as a site index of the extent-`extent a`
lattice.

DERIVED: `2 * k` is the even sublattice of lags and the `%` wraps it into the periodic lattice. The
factor `2` is not a scale: `ReflectionStrong.corrClay_nonneg_even_lag` is the RP theorem that holds
at EVERY real coupling, and its hypothesis is that the lag is even, so the even lags are exactly the
separations at which this family's `os_rp` is a theorem rather than an assumption on the sign of
`β`. -/
def lagOf (a k : ℕ) : Fin (extent a) := ⟨2 * k % extent a, Nat.mod_lt _ (ext_pos a)⟩

/-- The lag really is even, at every index and every label — so `corrClay_nonneg_even_lag` applies.

DERIVED: `2` is the parity; `0` is what an even residue is congruent to. -/
theorem lagOf_even (a k : ℕ) : Even (lagOf a k).val := by
  have hdvd : (2 : ℕ) ∣ extent a := ⟨a + 1, ext_eq_two_mul a⟩
  have hmm : 2 * k % extent a % 2 = 2 * k % 2 := Nat.mod_mod_of_dvd (2 * k) hdvd
  rw [Nat.even_iff]
  show 2 * k % extent a % 2 = 0
  rw [hmm, Nat.mul_mod_right]

/-- The base plaquette: the `(0,1)` plane at the origin of the extent-`n` lattice.

DERIVED: `0` and `1` are the two directions spanning a plane — a plane needs two, and which two is a
naming freedom on a lattice whose axes are interchangeable (`WilsonHypercubic.axisSymmetry`). The
site is the origin, immaterial by periodicity. -/
def plaqBase (n : ℕ) [NeZero n] : MassGap.WilsonHypercubic.Plaq 4 n := ((0, 1), fun _ => 0)

/-- The displaced plaquette: the same `(0,1)` plane, `lag` steps along direction `2`.

DERIVED: `0` and `1` span the plane as in `plaqBase`; `2` is a direction transverse to it, which is
what makes the lag a genuine spatial separation rather than an in-plane offset, and which exists
because the dimension exceeds two. -/
def plaqAt (n : ℕ) [NeZero n] (lag : Fin n) : MassGap.WilsonHypercubic.Plaq 4 n :=
  ((0, 1), MassGap.WilsonBridge.siteAtHyper 2 lag)

/-- **THE REFLECTED SCHWINGER FORM — no clamp.**

`Qos β j a` is the connected `SU(3)` Wilson plaquette correlation, at coupling `β`, on the
four-dimensional periodic lattice of extent `extent a`, between the `(0,1)` plaquette at the origin and
the one displaced along direction `2` by the even lag the test configuration names — with both
observables and the product transported by the axis permutation `j.1 * j.2.1`.

Compare `WilsonGauge.QG`, which is `min (max _ 0) 1` of a one-plaquette expectation at coupling
`(a : ℝ)`. Here there is no `min`, no `max`, the coupling is the parameter `β` and the index `a` is
the extent.

DERIVED: no literal; the plane, the lag axis and the extent carry their notes at `plaqBase`,
`plaqAt`, `lagOf` and `extent`. -/
noncomputable def Qos (β : ℝ) (j : JOS) (a : ℕ) : ℝ :=
  connT (extent a) β (j.1 * j.2.1) (plaqBase (extent a)) (plaqAt (extent a) (lagOf a j.2.2))

/-- **The reflected form IS the Clay correlation at extent `extent a` and coupling `β`.**

Everything the family claims rests on this line. Reading it right to left: the transport is gone
(`connT_eq`, i.e. the invariance is derived), what remains is `WilsonBridge.corrClay` — the genuine
connected `SU(3)` correlation on the four-dimensional periodic lattice — the coupling slot holds `β`,
and the extent slot holds `extent a`. The index enters as the geometry and nowhere else.

DERIVED: no literal. -/
theorem Qos_eq (β : ℝ) (j : JOS) (a : ℕ) :
    Qos β j a = MassGap.WilsonBridge.corrClay (extent a) β (lagOf a j.2.2) := by
  unfold Qos
  rw [connT_eq]
  rfl

/-! ### The three OS clauses, each a theorem about the measure -/

/-- **OS2 / `os_rp`: REFLECTION POSITIVITY, not a clamp.**

`0 ≤ Qos β j a` at every real coupling, every extent in the sequence and every test configuration.
The input is `ReflectionStrong.corrClay_nonneg_even_lag`, which obtains nonnegativity of the
CONNECTED correlation from the half-space module statement — reflection positivity as a quadratic
form on the slab algebra — with no sign condition on `β`. Nonnegativity of the UNCONNECTED
correlation would be trivial (a product of nonnegative densities under a positive state); it is the
subtraction of the disconnected floor that makes this RP.

DERIVED: `2 * a + 1` is the APERTURE — `corrClay_nonneg_even_lag` states its conclusion at extent
`Nap + 1`, so `Nap = 2a+1` and the extent is `2a+2` — and `a + 1` is the half-extent the reflection
sits at; both are `extent`'s own. The `0` of `0 ≤ …` is positivity itself. -/
theorem Qos_nonneg (β : ℝ) (j : JOS) (a : ℕ) : 0 ≤ Qos β j a := by
  rw [Qos_eq]
  exact MassGap.ReflectionStrong.corrClay_nonneg_even_lag (2 * a + 1) (a + 1)
    (ext_eq_two_mul a) (Nat.succ_pos a) β (lagOf_even a j.2.2)

/-- **The RP input is not vacuous: it holds where the odd-lag route says nothing.**

`OddLagSplit.plaqReflPositive_odd` carries `0 ≤ β`. This family's `os_rp` does not, and here it is at
a negative coupling. That the sign matters somewhere is visible in
`CharacterExpansion.NegControl.su3_kernel_neg_of_neg`, which shows one quadratic form of the
character expansion is strictly negative at `β < 0` — that is a failure of the EXPANSION route at
negative coupling, not a statement about any lag. So the even-lag restriction in `lagOf` is buying
something: a region of the coupling line the odd-lag route does not reach.

DERIVED: `−1` is a coupling of the sign the odd-lag route excludes, not a fitted or measured value. -/
theorem Qos_nonneg_at_negative_coupling (j : JOS) (a : ℕ) : 0 ≤ Qos (-1 : ℝ) j a :=
  Qos_nonneg (-1) j a

/-- **OS0 / the uniform bound: `|Qos| ≤ 4`, with no hypothesis and no extent in the constant.**

`InfiniteVolume.wilsonCorrConn_abs_le_four` bounds the connected correlation at EVERY extent, EVERY
real coupling and EVERY separation: the Wilson plaquette density lies in `[0,2]` and the Gibbs state
is a contractive probability state (`WilsonReal.wilsonSystem_expect_abs_le`), so the unconnected
correlation lies in `[0,4]` and so does the disconnected floor. Nothing in the constant refers to the
extent, which is exactly what a sequence over extents needs.

DERIVED: `4 = 2 · 2` is the square of the Wilson density's own range `[0,2]` —
`InfiniteVolume.wilsonCorrConn_abs_le_four`'s constant, not a bound chosen here. `3 ≠ 0` is the rank
being a group. -/
theorem Qos_abs_le_four (β : ℝ) (j : JOS) (a : ℕ) : |Qos β j a| ≤ 4 := by
  unfold Qos
  rw [connT_eq]
  exact MassGap.InfiniteVolume.wilsonCorrConn_abs_le_four (Nc := NYM) (by norm_num) _ _ _ _

/-- **OS1 / `os_euc`: Euclidean invariance, DERIVED.** Both sides reduce by `Qos_eq` to the same
correlation, because `connT_eq` has already removed the transport that the Euclidean component
supplies. The group element acts on the `SU(3)` measure and Haar does not notice; that is the whole
content, and it is `Symmetry.expect_invariant`'s.

DERIVED: no literal. -/
theorem Qos_actE (β : ℝ) (g : Equiv.Perm (Fin 4)) (j : JOS) (a : ℕ) :
    Qos β (actEOS g j) a = Qos β j a := by
  have hlab : (actEOS g j).2.2 = j.2.2 := rfl
  rw [Qos_eq, hlab, Qos_eq]

/-- **OS3 / `os_perm`: permutation symmetry, DERIVED** — the same mechanism at the permutation
component.

DERIVED: no literal. -/
theorem Qos_actP (β : ℝ) (σ : Equiv.Perm (Fin 4)) (j : JOS) (a : ℕ) :
    Qos β (actPOS σ j) a = Qos β j a := by
  have hlab : (actPOS σ j).2.2 = j.2.2 := rfl
  rw [Qos_eq, hlab, Qos_eq]

/-! ### The mode count: the lattice's own, and it diverges -/

/-- **The mode count at index `a`: the plaquette count of the extent-`extent a` lattice.**

`LatticeYMFamily.Na` is documented as "lattice mode count at spacing index `a` (`→ ∞`)". In
`WilsonGauge` it is `NaG a = a + 1`, a counter with no lattice attached. Here it is the cardinality
of the plaquette type of the lattice the family's reflected form is actually integrated over.

DERIVED: `4` is the dimension; the count itself is a cardinality, not a chosen number. -/
def Nmodes (a : ℕ) : ℕ := Fintype.card (MassGap.WilsonHypercubic.Plaq 4 (extent a))

/-- The count written out: `4 · 4 · (2a+2)⁴`.

DERIVED: `4 · 4` is the number of ordered direction pairs in four dimensions and `(2a+2)⁴` the site
count — `WilsonHypercubic.card_plaq` at `d = 4`, not a constant chosen here. -/
theorem Nmodes_eq (a : ℕ) : Nmodes a = 4 * 4 * (2 * a + 1 + 1) ^ 4 :=
  MassGap.WilsonHypercubic.card_plaq 4 (extent a)

/-- The count is positive at every index.

DERIVED: the `0` is the boundary a cardinality cannot cross; the numerals are `Nmodes_eq`'s. -/
theorem Nmodes_pos (a : ℕ) : 0 < Nmodes a := by
  rw [Nmodes_eq]; positivity

/-- **The volume diverges along the family**, by `InfiniteVolume.clay_volume_tendsto_atTop` composed
with the index-to-aperture map. This is the sense in which `a → ∞` is the infinite-volume limit: the
extent is the same in all four directions at once, so there is no second extent left to send to
infinity, and the plaquette count is the volume.

DERIVED: `2 * a + 1` is `extent`'s aperture, `extent a = (2a+1) + 1`. -/
theorem Nmodes_tendsto_volume : Tendsto (fun a : ℕ => (Nmodes a : ℝ)) atTop atTop := by
  have hg : Tendsto (fun a : ℕ => 2 * a + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  exact MassGap.InfiniteVolume.clay_volume_tendsto_atTop.comp hg

/-! ### The family

The infrared clause `os_gap` is not supplied directly — `Measure.familyOfSortedCount` refuses to take
it and asks instead for an ORDERED spectrum and a bound on how many of its modes clear the noise
edge, deriving `os_gap` from the pair. That is unchanged from `WilsonGauge`, and deliberately: this
file repairs the MEASURE side, and the spectrum side is the same interface a measured read would come
through. -/

/-- **The OS data family on the genuine Gibbs correlation, at arbitrary extent, from a counted
spectrum.**

Three of the four OS fields are theorems about the `SU(3)` Wilson measure at extent `extent a`:

* `os_rp` — `Qos_nonneg`, reflection positivity on the even lags at every real `β`;
* `os_form` — `Qos_abs_le_four`, the hypothesis-free bound, against `B = 4`;
* `os_euc` / `os_perm` — `Qos_actE` / `Qos_actP`, from `Symmetry.expect_invariant`.

The fourth, `os_gap`, is NOT about the measure: `familyOfSortedCount` derives it from `hsorted` and
`hcount`, which are facts about whatever spectrum the caller supplies. At `osFamily` that spectrum is
the placeholder `evUnit`, so `os_gap` there says nothing about `SU(3)`.

Two things this bound does not claim, stated because the field names suggest otherwise.
`LatticeYMFamily.os_form` is documented as "the reflected form is built from the resolved modes", and
here it is discharged as `Q ≤ 4 ≤ resolvedDim · 4`, which relates `Q` to nothing about the spectrum —
it is OS0's uniform bound and only that. And `Na := Nmodes` is the lattice's genuine plaquette count,
but `evUnit` ignores its argument, so the only thing the assembled family uses of it is
`1 ≤ Nmodes a`; any `Na` bounded below by one would give the identical family. `Nmodes` is honest as
a definition and inert in the family's content until a measured spectrum replaces `evUnit`.

None of the three measure clauses is a clamp, and the index is the extent throughout.

DERIVED: `4` in `B := 4` is `InfiniteVolume.wilsonCorrConn_abs_le_four`'s own constant, the square of
the Wilson density's range `[0,2]`; it is the smallest bound this development has proved for the
object, not a scale chosen here. The `1` in `1 * 4` is arithmetic. `4` in `Equiv.Perm (Fin 4)` is the
dimension. -/
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

/-- **The OS0–OS3 continuum limit of that family**, at every real coupling.

`continuum_of_family` on `osFamilyCounted`: a subsequence and a limit `q` with joint convergence, the
temperedness bound (OS0), nonnegativity (the `os_rp` clause, here sourced from reflection positivity
rather than a clamp) and the Euclidean (OS1) / permutation (OS3) invariances, which flow from
Haar-invariance of the actual `SU(3)` gauge measure composed with the hypercubic lattice's axis
symmetry.

What this is a limit OF has changed from `WilsonGauge.ym_continuum_gauge_counted`: there, a sequence
in the COUPLING at fixed `2⁴` volume; here, a sequence in the EXTENT at fixed coupling.

DERIVED: no literal. -/
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

The three spectrum hypotheses are discharged at a single-resolved-mode spectrum, so that
`os_continuum_counted` is about something. This is the ONE part of the construction that is a
placeholder rather than a measured or derived quantity, and it is the same placeholder
`WilsonGauge.evDemo` is. It is stated separately from the measure side for exactly that reason. -/

/-- A spectrum with a single supra-edge mode: the vacuum at `1`, everything else at `0`.

DERIVED: `1` and `0` are the two values a single-resolved-mode spectrum takes; nothing is compared
against them — they ARE the spectrum, the object under discussion. -/
noncomputable def evUnit (_a n : ℕ) : ℝ := if n = 0 then 1 else 0

/-- **Exactly one mode clears a floor strictly between `0` and `1`, at every index.**

DERIVED: `1 / 2` is any value strictly between the two the spectrum takes; nothing depends on which,
and this theorem is proved at one. `1` is the resulting count. -/
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

/-- **The spectrum is ordered.** A later index never carries more weight than an earlier one.

DERIVED: `0` is the index of the leading mode, not a threshold. -/
theorem evUnit_sorted (a : ℕ) : ∀ m n : ℕ, m ≤ n → evUnit a n ≤ evUnit a m := by
  intro m n hmn
  by_cases hm : m = 0
  · subst hm
    simp only [evUnit, if_pos rfl]
    split <;> norm_num
  · have hn : n ≠ 0 := by
      intro h; exact hm (Nat.le_zero.mp (h ▸ hmn))
    simp [evUnit, if_neg hm, if_neg hn]

/-- At most one mode clears the floor, so the count bound holds at `c = 1`.

DERIVED: `1 / 2` is the floor carried from `resolvedDim_evUnit`; `1` is the count it returns. -/
theorem evUnit_count (a : ℕ) :
    ((resolvedDim (Finset.range (Nmodes a)) (evUnit a) (1 / 2) : ℕ) : ℝ) ≤ 1 := by
  rw [resolvedDim_evUnit]; norm_num

/-- At least one does, so the aperture bound is non-vacuous.

DERIVED: `1 / 2` is the floor carried from `resolvedDim_evUnit`; `1` is the count it returns. -/
theorem evUnit_res (a : ℕ) : 1 ≤ resolvedDim (Finset.range (Nmodes a)) (evUnit a) (1 / 2) := by
  rw [resolvedDim_evUnit]

/-- **THE FAMILY: `SU(3)` OS data on the genuine Gibbs correlation, at arbitrary extent, unclamped.**

`osFamilyCounted` at the single-supra-edge-mode spectrum, so that it is unconditional and there is
one route to the interface rather than two.

DERIVED: the floor `1 / 2` is any value strictly between the two the spectrum takes and
`resolvedDim_evUnit` is proved for this one; the count `1` is what it returns. -/
noncomputable def osFamily (β : ℝ) : LatticeYMFamily :=
  osFamilyCounted β evUnit (1 / 2) 1 evUnit_sorted evUnit_count evUnit_res

/-- **The OS0–OS3 continuum limit of the unclamped, arbitrary-extent family**, at every real
coupling.

DERIVED: no literal. -/
theorem os_continuum (β : ℝ) :
    ∃ (q : (osFamily β).J → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ j, Tendsto (fun k => (osFamily β).Q j (φ k)) atTop (nhds (q j))) ∧
      (∀ j, |q j| ≤ (⌈(osFamily β).c⌉₊ : ℝ) * (osFamily β).B) ∧
      (∀ j, 0 ≤ q j) ∧
      (∀ g j, q ((osFamily β).actE g j) = q j) ∧
      (∀ σ j, q ((osFamily β).actP σ j) = q j) :=
  continuum_of_family (osFamily β)

/-! ### What the family's own fields say

These are `rfl`, and that is the point: they let a reader check the three repairs without reading the
constructor. -/

/-- The family's reflected form is `Qos` — the connected correlation, not a clamp.

DERIVED: no literal. -/
theorem osFamily_Q (β : ℝ) : (osFamily β).Q = Qos β := rfl

/-- The family's mode count is the lattice's plaquette count, not a counter.

DERIVED: no literal. -/
theorem osFamily_Na (β : ℝ) : (osFamily β).Na = Nmodes := rfl

/-- The family's per-mode bound is the proved correlation bound.

DERIVED: `4` is `InfiniteVolume.wilsonCorrConn_abs_le_four`'s constant. -/
theorem osFamily_B (β : ℝ) : (osFamily β).B = 4 := rfl

/-- **The index is the extent and the coupling is the parameter** — the family's reflected form at
index `a` is the Clay correlation on the extent-`(2a+2)` lattice at coupling `β`.

DERIVED: no literal; `extent` carries the extent's note. -/
theorem osFamily_Q_eq (β : ℝ) (j : JOS) (a : ℕ) :
    (osFamily β).Q j a = MassGap.WilsonBridge.corrClay (extent a) β (lagOf a j.2.2) :=
  Qos_eq β j a

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
end Audit

end MassGap.OSFamily
