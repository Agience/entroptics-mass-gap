import Mathlib
import MassGap.ReflectionStrong
import MassGap.InfiniteVolume
import MassGap.PlaqVariance

/-!
# MassGap.CorrVec — the plaquette correlation at a general lattice separation

## The object

`corrSep Nc μ ν β v` is the connected correlation of the `(μ,ν)`-plane plaquette at the origin with
the `(μ,ν)`-plane plaquette at an arbitrary site `v : Fin d → Fin n`, and `corrVec n β v` is its
`SU(3)`, four-dimensional, `(0,1)`-plane instance. `corrVec_restricts_to_corrClay` relates it to the
one-lag object: `corrVec n β (siteAtHyper 2 lag) = corrClay n β lag`, and it is `rfl`.

`WilsonBridge.corrClay n β lag = corrHyper (d := 4) 3 n 0 1 2 β lag` fixes the plaquette plane to the
directions `0` and `1` and puts the second plaquette at `siteAtHyper 2 lag`, a site whose only
nonzero coordinate is along direction `2`. So `corrClay` and everything indexed by it — the moment
read, the aperture, the spectral measure of `MomentMeasure.rieszMeasure` — is indexed by one integer,
the lag along one axis. `corrSep` is indexed by a full site instead.

## What holds at a general separation

* **The extent-free bound**, with no hypothesis beyond a nonzero gauge rank: `corrSep_abs_le_four`
  is `InfiniteVolume.wilsonCorrConn_abs_le_four`, which reads no geometry.
* **Componentwise circle symmetry**: `corrSep_negAt` negates any one coordinate of `v` in a
  direction transverse to the plane and the correlation is unchanged, at every extent and every real
  coupling. `MomentShape.corrHyper_neg` is its one-axis case (`corrSep_siteAtHyper_neg`).
* **Axis permutation.** `corrSep_axis` says relabelling the axes by any `e : Equiv.Perm (Fin d)`
  carries the correlation to the one with plane `(e μ, e ν)` and separation `axisSite e v`. When `e`
  fixes the plane (`corrSep_axis_fix`) the separation's components may be permuted among themselves
  with the correlation unchanged. At the Clay parameters that is `corrVec_swap_transverse`, and
  `corrVec_siteAtHyper_three_eq_two` reads off that the lag along direction `3` and the lag along
  direction `2` are the same number.
* **Nonnegativity**, at single-axis separations only. See the next section.

## How far reflection positivity reaches

The site reflection `Reflect.reflSite τ c x = Function.update x τ (c - x τ)` moves one coordinate.
The Osterwalder–Seiler pairing that `ReflectionStrong` proves nonnegative is `⟨F · (F ∘ Θ)⟩` at a
member `F` of the observable module based at a site `x`, and `Θ` carries that plaquette to the one
based at `reflSite τ c x`. The separation between the two is `reflSite τ c x - x`, whose only nonzero
coordinate is along `τ`. So the one-plaquette pairing gives nonnegativity of the correlation at
one-axis separations: `corrSep_nonneg_even_single_axis` is the statement, with the even-parity and
half-extent hypotheses `ReflectionStrong.corrHyper_nonneg_even_lag_of_module` carries.

A separation with two or more nonzero components is not the reflection of anything through one
hyperplane, and no theorem here bounds `corrSep Nc μ ν β v` below for such a `v`. The reflection
module `LogConvex.localObs` is closed under linear combination and its Gram form is nonnegative,
which gives a positive semidefinite quadratic form over families of sites, and the separations inside
that form do have several nonzero components; extracting a pointwise bound from it is a separate
argument and is not made here.

`corrVec` is a two-point function at finite extent `n` and finite lattice spacing. No pairing of it
against a test function is defined here, and no limit in `n` or in the lattice spacing is taken here.

Foundational footprint only; every declaration is printed in the Audit section at the end.

Build: `python research/code/lean_build.py build MassGap.CorrVec`.
-/

namespace MassGap.CorrVec

open MeasureTheory
open MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.WilsonAction
open MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonHypercubic
open MassGap.WilsonBridge MassGap.Reflect MassGap.ReflectPositive

/-! ## Part 1 — the object -/

section Object

variable {d n Nc : ℕ} [NeZero n]

/-- **The connected plaquette correlation at a general separation.**

`corrSep Nc μ ν β v = ⟨φ_{(μ,ν),0} · φ_{(μ,ν),v}⟩_β − ⟨φ_{(μ,ν),0}⟩_β ⟨φ_{(μ,ν),v}⟩_β`, the
connected two-point function of the `(μ,ν)`-plane plaquette energy at the origin with the one at the
site `v`, on the `d`-dimensional periodic `SU(Nc)` Wilson lattice of extent `n`. It is
`wilsonCorrConn` at the two plaquettes `((μ,ν), 0)` and `((μ,ν), v)`.

`WilsonBridge.corrHyper` is this with `v` forced to be `siteAtHyper τ lag`, a site with one nonzero
coordinate. Here `v` is any site.

DERIVED: the only numeral is the `0` of the origin site `fun _ => 0`, where the first plaquette is
based. The plane, the separation, the extent and the coupling are all the caller's. -/
noncomputable def corrSep (Nc : ℕ) {d n : ℕ} [NeZero n] (μ ν : Fin d) (β : ℝ) (v : Site d n) : ℝ :=
  wilsonCorrConn (Nc := Nc) (bd (d := d) (n := n))
    ((μ, ν), (fun _ => 0 : Site d n)) β ((μ, ν), v)

/-- **`corrHyper` is `corrSep` at a one-axis separation.** The proof is `rfl`, so the two are the
same construction at a restricted argument rather than two objects with a bridge between them.

DERIVED: no numeral. -/
theorem corrHyper_eq_corrSep (Nc : ℕ) {d n : ℕ} [NeZero n] (μ ν τ : Fin d) (β : ℝ) (lag : Fin n) :
    corrHyper (d := d) Nc n μ ν τ β lag = corrSep Nc μ ν β (siteAtHyper τ lag) := rfl

/-- `corrSep` written out as the two-point expectation minus the product of the two one-point
expectations, in the `EW`/`plaqE` notation `ReflectPositive` uses. The proof is `rfl`; this is the
working form for the proofs below.

DERIVED: the only numeral is the `0` of the origin site `fun _ => 0`, carried from `corrSep`. -/
theorem corrSep_unfold (Nc : ℕ) {d n : ℕ} [NeZero n] (μ ν : Fin d) (β : ℝ) (v : Site d n) :
    corrSep Nc μ ν β v
      = EW Nc β (fun U => plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) U
            * plaqE Nc (((μ, ν), v) : Plaq d n) U)
        - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))
          * EW Nc β (plaqE Nc (((μ, ν), v) : Plaq d n)) := rfl

end Object

/-- **The four-dimensional `SU(3)` correlation at a general four-vector separation.** `corrSep` at
the Clay problem's dimension and gauge group, on the lattice `WilsonGauge`'s Osterwalder–Schrader
measure is built on, with the separation a full site of `Fin 4 → Fin n` rather than a single lag.

DERIVED: `3` is the `N` of `SU(3)` and `4` is the dimension — the problem's own data, exactly as in
`WilsonBridge.corrClay`; `0` and `1` span the plaquette plane, and which two directions those are is
a naming freedom `corrSep_axis` below states as a theorem. `n` is the periodic extent and stays the
caller's. -/
noncomputable def corrVec (n : ℕ) [NeZero n] (β : ℝ) (v : Site 4 n) : ℝ :=
  corrSep (d := 4) 3 0 1 β v

/-- **`corrClay` is `corrVec` at a separation along direction `2`.** The proof is `rfl`, so any
 theorem about `corrClay` — reflection positivity at even lag, circle symmetry, log-convexity, the
moment read, the representing measure of `MomentMeasure.rieszMeasure` — is a theorem about `corrVec`
restricted to the separations `siteAtHyper 2 lag`.

DERIVED: `2` is the lag direction `corrClay` itself names, transverse to its `(0,1)` plane; `4` in
`Fin 4` is the lattice dimension, `corrVec`'s own. -/
theorem corrVec_restricts_to_corrClay (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    corrVec n β (siteAtHyper (2 : Fin 4) lag) = corrClay n β lag := rfl

/-- `corrVec` at a separation along any direction `τ : Fin 4` is `corrHyper` with lag axis `τ`, by
`rfl`. Unlike `corrVec_restricts_to_corrClay` the axis is not fixed to `2`.

DERIVED: `3` is the `N` of `SU(3)`, `4` the dimension and `0`, `1` the plane — all `corrVec`'s
own. -/
theorem corrVec_siteAtHyper (n : ℕ) [NeZero n] (β : ℝ) (τ : Fin 4) (lag : Fin n) :
    corrVec n β (siteAtHyper τ lag) = corrHyper (d := 4) 3 n 0 1 τ β lag := rfl

/-! ## Part 2 — the extent-free bound, which carries with no hypothesis

`InfiniteVolume.wilsonCorrConn_abs_le_four` is stated for an arbitrary boundary-word map and an
arbitrary pair of plaquettes: the unconnected correlation lies in `[0,4]` and each one-point function
in `[0,2]`, and no geometry enters. So it applies at a general separation verbatim. -/

section Bound

variable {d n Nc : ℕ} [NeZero n]

/-- **The correlation at any separation is bounded in absolute value by `4`**, at every extent, every
real coupling and every plane. The one hypothesis is `Nc ≠ 0`.

DERIVED: the `0` in `Nc ≠ 0` excludes the empty gauge group. `4` is `2 × 2`, the product of the two
plaquette-energy ranges — `InfiniteVolume.wilsonCorrConn_abs_le_four`'s constant, carried unchanged,
and nothing about the separation enters it. -/
theorem corrSep_abs_le_four (hN : Nc ≠ 0) (μ ν : Fin d) (β : ℝ) (v : Site d n) :
    |corrSep Nc μ ν β v| ≤ 4 :=
  MassGap.InfiniteVolume.wilsonCorrConn_abs_le_four hN _ _ _ _

/-- The same bound at the Clay parameters, with no hypothesis left: `corrSep_abs_le_four`'s `Nc ≠ 0`
is discharged by `SU(3)`.

DERIVED: the statement's numerals are the `4` of `Site 4 n`, the lattice dimension, and the `4` of
the bound, which is `corrSep_abs_le_four`'s constant carried. The `3` of `SU(3)` appears in the proof
and in `corrVec`'s definition, not in this statement. -/
theorem corrVec_abs_le_four (n : ℕ) [NeZero n] (β : ℝ) (v : Site 4 n) :
    |corrVec n β v| ≤ 4 := by
  show |corrSep (d := 4) 3 0 1 β v| ≤ 4
  exact corrSep_abs_le_four (Nc := 3) (by norm_num) 0 1 β v

end Bound

/-! ## Part 3 — a relabelling of the lattice moves the correlation

The general machinery behind the axis-permutation invariance, stated for an arbitrary
boundary-word map so that it is about `wilsonCorrConn` itself rather than about the hypercubic
instance. A `WilsonLattice.wilsonSymmetry` is exactly a pair of permutations that maps boundary words
compatibly; `WilsonLattice.wilson_expect_invariant` moves the Gibbs state along it, and what is added
here is that it moves the connected two-plaquette correlation, which needs the one-point functions to
move too. -/

section Relabel

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- **A relabelled configuration gives the relabelled plaquette's observable.** Reading the
plaquette `q` on `U ∘ σL` is reading `σP q` on `U`, given the compatibility `hbd` between the two
permutations and the boundary-word map. This is the `compat` field of
`WilsonLattice.wilsonSymmetry`, pushed through the (class-function) Wilson density.

DERIVED: no numeral. -/
theorem wilsonPlaqObs_relabel (bd' : Pq → List (Lk × Bool))
    (σL : Equiv.Perm Lk) (σP : Equiv.Perm Pq)
    (hbd : ∀ p, bd' (σP p) = (bd' p).map (fun lo => (σL lo.1, lo.2)))
    (q : Pq) (U : (wilsonSystem bd' (wilsonDensity (N := Nc))).Config) :
    wilsonPlaqObs (N := Nc) bd' q (fun l => U (σL l))
      = wilsonPlaqObs (N := Nc) bd' (σP q) U :=
  congrArg (wilsonDensity (N := Nc))
    ((wilsonSymmetry bd' (wilsonDensity (N := Nc)) σL σP hbd).compat q U)

/-- The Gibbs expectation of an observable is unchanged when the configuration is relabelled by
`σL`. This is `wilson_expect_invariant` with the `Symmetry.reindex` wrapper unfolded to a plain
composition, so that it can be rewritten under.

DERIVED: no numeral. -/
theorem expect_relabel (bd' : Pq → List (Lk × Bool))
    (σL : Equiv.Perm Lk) (σP : Equiv.Perm Pq)
    (hbd : ∀ p, bd' (σP p) = (bd' p).map (fun lo => (σL lo.1, lo.2))) (β : ℝ)
    (O : (wilsonSystem bd' (wilsonDensity (N := Nc))).Config → ℝ) :
    (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (fun U => O (fun l => U (σL l)))
      = (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β O := by
  have h := wilson_expect_invariant (G := MassGap.SUN.SU Nc) bd' (wilsonDensity (N := Nc))
    σL σP hbd (probHaar (MassGap.SUN.SU Nc)) β O
  have hfun : (fun U : (wilsonSystem bd' (wilsonDensity (N := Nc))).Config =>
        O (fun l => U (σL l)))
      = (fun U => O (Symmetry.reindex (wilsonSymmetry bd' (wilsonDensity (N := Nc))
          σL σP hbd).onLink U)) :=
    funext fun U => congrArg O (funext fun _ => rfl)
  rw [hfun]
  exact h

/-- `wilsonCorr` as a Gibbs expectation of the product of the two plaquette observables. The proof is
`rfl`; the lemma exists because `unfold` will not open `wilsonCorr` under the subtraction in
`wilsonCorrConn`, and a rewrite needs the equation as a lemma.

DERIVED: no numeral. -/
theorem wilsonCorr_eq_expect (bd' : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    MassGap.WilsonBridge.wilsonCorr (Nc := Nc) bd' p₀ β p
      = (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
          (fun U => wilsonPlaqObs (N := Nc) bd' p₀ U * wilsonPlaqObs (N := Nc) bd' p U) := rfl

/-- The expectation of the product of two plaquette observables is unchanged when both plaquettes are
moved by `σP`.

DERIVED: no numeral. -/
theorem expect_pair_relabel (bd' : Pq → List (Lk × Bool))
    (σL : Equiv.Perm Lk) (σP : Equiv.Perm Pq)
    (hbd : ∀ p, bd' (σP p) = (bd' p).map (fun lo => (σL lo.1, lo.2))) (β : ℝ) (q₁ q₂ : Pq) :
    (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (fun U => wilsonPlaqObs (N := Nc) bd' (σP q₁) U * wilsonPlaqObs (N := Nc) bd' (σP q₂) U)
      = (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (fun U => wilsonPlaqObs (N := Nc) bd' q₁ U * wilsonPlaqObs (N := Nc) bd' q₂ U) := by
  have h := expect_relabel (Nc := Nc) bd' σL σP hbd β
    (fun U => wilsonPlaqObs (N := Nc) bd' q₁ U * wilsonPlaqObs (N := Nc) bd' q₂ U)
  rw [← h]
  refine congrArg _ (funext fun U => ?_)
  show wilsonPlaqObs (N := Nc) bd' (σP q₁) U * wilsonPlaqObs (N := Nc) bd' (σP q₂) U
      = wilsonPlaqObs (N := Nc) bd' q₁ (fun l => U (σL l))
        * wilsonPlaqObs (N := Nc) bd' q₂ (fun l => U (σL l))
  rw [wilsonPlaqObs_relabel bd' σL σP hbd q₁ U, wilsonPlaqObs_relabel bd' σL σP hbd q₂ U]

/-- The expectation of a single plaquette observable is unchanged when the plaquette is moved by
`σP`.

DERIVED: no numeral. -/
theorem expect_one_relabel (bd' : Pq → List (Lk × Bool))
    (σL : Equiv.Perm Lk) (σP : Equiv.Perm Pq)
    (hbd : ∀ p, bd' (σP p) = (bd' p).map (fun lo => (σL lo.1, lo.2))) (β : ℝ) (q : Pq) :
    (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (wilsonPlaqObs (N := Nc) bd' (σP q))
      = (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
        (wilsonPlaqObs (N := Nc) bd' q) := by
  have h := expect_relabel (Nc := Nc) bd' σL σP hbd β (wilsonPlaqObs (N := Nc) bd' q)
  rw [← h]
  exact congrArg _ (funext fun U => (wilsonPlaqObs_relabel bd' σL σP hbd q U).symm)

/-- **The connected correlation is invariant under a lattice relabelling**, for an arbitrary
boundary-word map: moving both plaquettes by the plaquette permutation `σP` of a `wilsonSymmetry`
leaves `wilsonCorrConn` unchanged. The subtracted product of one-point functions moves too, which is
why the proof needs `expect_one_relabel` as well as `expect_pair_relabel`.

DERIVED: no numeral. -/
theorem wilsonCorrConn_relabel (bd' : Pq → List (Lk × Bool))
    (σL : Equiv.Perm Lk) (σP : Equiv.Perm Pq)
    (hbd : ∀ p, bd' (σP p) = (bd' p).map (fun lo => (σL lo.1, lo.2)))
    (p₀ : Pq) (β : ℝ) (p : Pq) :
    wilsonCorrConn (Nc := Nc) bd' (σP p₀) β (σP p)
      = wilsonCorrConn (Nc := Nc) bd' p₀ β p := by
  unfold wilsonCorrConn
  rw [wilsonCorr_eq_expect bd' (σP p₀) β (σP p), wilsonCorr_eq_expect bd' p₀ β p,
    expect_pair_relabel bd' σL σP hbd β p₀ p, expect_one_relabel bd' σL σP hbd β p₀,
    expect_one_relabel bd' σL σP hbd β p]

end Relabel

/-! ## Part 4 — Euclidean invariance: permuting the axes

`WilsonHypercubic.axisSymmetry` is the discrete Euclidean group of the lattice, and `bd_axis` is the
compatibility hypothesis the relabelling machinery above consumes. Instantiating at it gives a
statement about a full separation rather than a lag. -/

section Axis

variable {d n Nc : ℕ} [NeZero n]

/-- The axis relabelling of a plaquette, computed on its components: the plane directions are moved
by `e` and the base site by `axisSite e`. The proof is `rfl`.

DERIVED: no numeral. -/
theorem axisPlaq_mk (e : Equiv.Perm (Fin d)) (μ ν : Fin d) (x : Site d n) :
    axisPlaq (n := n) e (((μ, ν), x) : Plaq d n) = ((e μ, e ν), axisSite e x) := rfl

/-- The origin is fixed by an axis relabelling, for every permutation `e`.

DERIVED: both `0`s are the coordinate value of the origin site, which permuting the axes cannot
change because every coordinate carries the same value. -/
theorem axisSite_origin (e : Equiv.Perm (Fin d)) :
    axisSite (n := n) e (fun _ => 0 : Site d n) = (fun _ => 0 : Site d n) :=
  funext fun _ => rfl

/-- **A one-axis separation relabels to a one-axis separation along the relabelled axis**, with the
same lag: `axisSite e (siteAtHyper τ lag) = siteAtHyper (e τ) lag`.

DERIVED: no numeral. -/
theorem axisSite_siteAtHyper (e : Equiv.Perm (Fin d)) (τ : Fin d) (lag : Fin n) :
    axisSite (n := n) e (siteAtHyper τ lag) = siteAtHyper (e τ) lag := by
  funext j
  simp only [axisSite, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  by_cases h : j = e τ
  · subst h
    simp [siteAtHyper]
  · have h' : e.symm j ≠ τ := fun hc => h (by rw [← hc]; simp)
    simp [siteAtHyper, Function.update_of_ne h, Function.update_of_ne h']

/-- **Axis-permutation invariance at a general separation.**

Relabelling the lattice axes by any permutation `e` carries the correlation of the `(μ,ν)`-plane at
separation `v` to the correlation of the `(e μ, e ν)`-plane at separation `axisSite e v`, at every
dimension, extent, gauge rank and real coupling, with no further hypothesis. Both sides are Gibbs
expectations of the real `SU(Nc)` Wilson ensemble at the same coupling; the content is that the
action and the product Haar measure are invariant under the relabelling
(`WilsonHypercubic.bd_axis`, then `wilsonCorrConn_relabel`).

DERIVED: no numeral. -/
theorem corrSep_axis (Nc : ℕ) {d n : ℕ} [NeZero n] (e : Equiv.Perm (Fin d)) (μ ν : Fin d) (β : ℝ)
    (v : Site d n) :
    corrSep Nc (e μ) (e ν) β (axisSite e v) = corrSep Nc μ ν β v := by
  have h := wilsonCorrConn_relabel (Nc := Nc) (bd (d := d) (n := n))
    (axisLink e) (axisPlaq e) (bd_axis e)
    (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) β (((μ, ν), v) : Plaq d n)
  rw [axisPlaq_mk e μ ν (fun _ => 0 : Site d n), axisPlaq_mk e μ ν v,
    axisSite_origin (n := n) e] at h
  exact h

/-- **The separation's components may be permuted among themselves.**

For a permutation `e` that fixes both directions spanning the plaquette plane, the plane does not
move and the statement is about the separation alone: `corrSep Nc μ ν β (axisSite e v)` equals
`corrSep Nc μ ν β v`. The hypotheses `e μ = μ` and `e ν = ν` are pointwise, not setwise, so a
permutation that swaps `μ` with `ν` is not covered.

DERIVED: no numeral. -/
theorem corrSep_axis_fix (Nc : ℕ) {d n : ℕ} [NeZero n] (e : Equiv.Perm (Fin d)) {μ ν : Fin d}
    (hμ : e μ = μ) (hν : e ν = ν) (β : ℝ) (v : Site d n) :
    corrSep Nc μ ν β (axisSite e v) = corrSep Nc μ ν β v := by
  have h := corrSep_axis Nc e μ ν β v
  rwa [hμ, hν] at h

end Axis

/-- **Swapping the two transverse directions, at the Clay parameters.** Exchanging directions `2` and
`3` — the two directions transverse to the `(0,1)` plaquette plane — leaves the `SU(3)`
four-dimensional correlation unchanged at every separation, every extent and every real coupling.
`corrSep_axis_fix` at the transposition, with `e 0 = 0` and `e 1 = 1` discharged by `decide`.

DERIVED: `2` and `3` are the two directions of `Fin 4` that are not `0` or `1`, the complement of the
plaquette plane; their transposition is the only nontrivial permutation of `Fin 4` fixing the plane
pointwise, so it is not one choice among several. `4` in `Fin 4` and `Site 4 n` is the lattice
dimension, `corrVec`'s own. -/
theorem corrVec_swap_transverse (n : ℕ) [NeZero n] (β : ℝ) (v : Site 4 n) :
    corrVec n β (axisSite (Equiv.swap (2 : Fin 4) 3) v) = corrVec n β v := by
  have h0 : Equiv.swap (2 : Fin 4) 3 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have h1 : Equiv.swap (2 : Fin 4) 3 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  show corrSep (d := 4) 3 0 1 β (axisSite (Equiv.swap (2 : Fin 4) 3) v)
      = corrSep (d := 4) 3 0 1 β v
  exact corrSep_axis_fix 3 (Equiv.swap (2 : Fin 4) 3) h0 h1 β v

/-- **The lag along direction `3` is the same number as the lag along direction `2`**, at every
extent, every real coupling and every lag. So the direction `corrClay` names is a representative of
an orbit of the axis symmetry rather than a distinguished choice.

DERIVED: `2` and `3` are the two directions transverse to `corrVec`'s `(0,1)` plane, as in
`corrVec_swap_transverse`; `4` in `Fin 4` is the lattice dimension. -/
theorem corrVec_siteAtHyper_three_eq_two (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    corrVec n β (siteAtHyper (3 : Fin 4) lag) = corrVec n β (siteAtHyper (2 : Fin 4) lag) := by
  have hswap : Equiv.swap (2 : Fin 4) 3 2 = 3 := Equiv.swap_apply_left 2 3
  have h := corrVec_swap_transverse n β (siteAtHyper (2 : Fin 4) lag)
  rwa [axisSite_siteAtHyper (n := n) (Equiv.swap (2 : Fin 4) 3) 2 lag, hswap] at h

/-- The same statement read against `corrClay`: the lag-`lag` correlation along direction `3` is the
Clay correlation. It is `corrVec_siteAtHyper_three_eq_two` composed with
`corrVec_restricts_to_corrClay`.

DERIVED: `3` is the fourth lattice direction, transverse to `corrVec`'s `(0,1)` plane; `4` in
`Fin 4` is the lattice dimension. -/
theorem corrVec_siteAtHyper_three (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    corrVec n β (siteAtHyper (3 : Fin 4) lag) = corrClay n β lag :=
  corrVec_siteAtHyper_three_eq_two n β lag

/-! ## Part 5 — componentwise circle symmetry

The site reflection `Reflect.reflSite τ c` negates one coordinate about `c`. At `c = 0` it fixes the
origin, so it carries the pair (origin, `v`) to the pair (origin, `v` with its `τ`-component
negated), and `Reflect.expect_reflect_invariant` says the Gibbs state does not notice. This is
`MomentShape.corrHyper_neg` with the separation no longer confined to one axis. -/

section Circle

variable {d n Nc : ℕ} [NeZero n]

/-- **A plaquette whose plane misses the reflection axis keeps its plane and moves its base site.**
Both plane directions must differ from the axis `τ`; the base site then moves by `reflSite τ c`. This
is the third branch of `Reflect.reflPlaq`, at an arbitrary base rather than the origin
(`ReflectPositive.reflPlaq_origin`) or a one-axis site (`LogConvex.reflPlaq_siteAtHyper`).

DERIVED: no numeral. -/
theorem reflPlaq_transverse {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c : Fin n) (x : Site d n) :
    reflPlaq τ c (((μ, ν), x) : Plaq d n) = ((μ, ν), reflSite τ c x) := by
  simp only [reflPlaq, hμ, hν, if_false]

/-- The expectation of the product of two plaquette energies is unchanged when both plaquettes are
reflected at the same axis and constant. No hypothesis on the plaquettes.

DERIVED: no numeral. -/
theorem EW_pair_refl (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (q₁ q₂ : Plaq d n) :
    EW Nc β (fun U => plaqE Nc (reflPlaq τ c q₁) U * plaqE Nc (reflPlaq τ c q₂) U)
      = EW Nc β (fun U => plaqE Nc q₁ U * plaqE Nc q₂ U) := by
  have h : EW Nc β (fun U => plaqE Nc q₁ (reflConf τ c U) * plaqE Nc q₂ (reflConf τ c U))
      = EW Nc β (fun U => plaqE Nc q₁ U * plaqE Nc q₂ U) :=
    expect_reflect_invariant (n := n) Nc τ c β
      (fun U => plaqE Nc q₁ U * plaqE Nc q₂ U)
  rw [← h]
  exact congrArg (EW Nc β)
    (funext fun U => by rw [plaqE_reflConf Nc τ c q₁ U, plaqE_reflConf Nc τ c q₂ U])

/-- The expectation of a single plaquette energy is unchanged when the plaquette is reflected.

DERIVED: no numeral. -/
theorem EW_one_refl (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (q : Plaq d n) :
    EW Nc β (plaqE Nc (reflPlaq τ c q)) = EW Nc β (plaqE Nc q) := by
  have h : EW Nc β (fun U => plaqE Nc q (reflConf τ c U)) = EW Nc β (plaqE Nc q) :=
    expect_reflect_invariant (n := n) Nc τ c β (plaqE Nc q)
  rw [← h]
  exact congrArg (EW Nc β) (funext fun U => (plaqE_reflConf Nc τ c q U).symm)

/-- **The connected correlation is invariant under reflecting both plaquettes**, at any reflection
axis and constant, any plane and any pair of sites, with no hypothesis on the extent, the gauge rank
or the coupling. The reflection is not a `LatticeGauge.Symmetry` — it carries the dagger — so this is
not an instance of `wilsonCorrConn_relabel`; it comes from `Reflect.expect_reflect_invariant`, which
reaches the same conclusion through `System.expect_invariant_of_mp`.

DERIVED: no numeral. -/
theorem wilsonCorrConn_refl (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (p₀ p : Plaq d n) :
    wilsonCorrConn (Nc := Nc) (bd (d := d) (n := n)) (reflPlaq τ c p₀) β (reflPlaq τ c p)
      = wilsonCorrConn (Nc := Nc) (bd (d := d) (n := n)) p₀ β p := by
  show EW Nc β (fun U => plaqE Nc (reflPlaq τ c p₀) U * plaqE Nc (reflPlaq τ c p) U)
      - EW Nc β (plaqE Nc (reflPlaq τ c p₀)) * EW Nc β (plaqE Nc (reflPlaq τ c p))
    = EW Nc β (fun U => plaqE Nc p₀ U * plaqE Nc p U)
      - EW Nc β (plaqE Nc p₀) * EW Nc β (plaqE Nc p)
  rw [EW_pair_refl Nc τ c β p₀ p, EW_one_refl Nc τ c β p₀, EW_one_refl Nc τ c β p]

/-- **Negating one component of a separation.** `negAt τ v` is `v` with its `τ`-coordinate replaced by
its negative, every other coordinate fixed — the componentwise version of `lag ↦ -lag`.

The negation is `Fin n`'s own, which is modular, so it is the circle inversion of that coordinate
rather than a sign convention.

DERIVED: no numeral. -/
def negAt {d n : ℕ} (τ : Fin d) (v : Site d n) : Site d n :=
  Function.update v τ (-(v τ))

/-- The site reflection at constant zero is the componentwise negation `negAt`.

DERIVED: the `0` is the reflection constant at which `reflSite τ c x = c - x τ` reduces to a plain
negation; it is not a choice of origin but the value that makes the two definitions agree. -/
theorem reflSite_zero_eq_negAt (τ : Fin d) (v : Site d n) :
    reflSite τ (0 : Fin n) v = negAt τ v := by
  funext j
  by_cases h : j = τ
  · subst h; simp [reflSite, negAt]
  · simp [reflSite, negAt, Function.update_of_ne h]

/-- Negating any one component of the origin leaves the origin.

DERIVED: both `0`s are the coordinate value of the origin site; the identity holds because `-0 = 0`
in `Fin n`. -/
theorem negAt_origin (τ : Fin d) : negAt (n := n) τ (fun _ => 0 : Site d n) = (fun _ => 0) := by
  funext j
  by_cases h : j = τ
  · subst h; simp [negAt]
  · simp [negAt, Function.update_of_ne h]

/-- Negating the `τ`-component of a one-axis separation along `τ` is negating its lag:
`negAt τ (siteAtHyper τ lag) = siteAtHyper τ (-lag)`.

DERIVED: no numeral. -/
theorem negAt_siteAtHyper (τ : Fin d) (lag : Fin n) :
    negAt (n := n) τ (siteAtHyper τ lag) = siteAtHyper τ (-lag) := by
  funext j
  by_cases h : j = τ
  · subst h; simp [negAt, siteAtHyper]
  · simp [negAt, siteAtHyper, Function.update_of_ne h]

/-- **Componentwise circle symmetry at a general separation.**

Negating any one coordinate of the separation, in a direction `τ` transverse to the plaquette plane,
leaves the correlation unchanged — at every extent, every gauge rank, every real coupling and every
plane. The two hypotheses are `μ ≠ τ` and `ν ≠ τ`; there is no hypothesis on the parity of the
component, on the sign of the coupling, or on the other components.

`MomentShape.corrHyper_neg` is the case in which the separation has only that one component
(`corrSep_siteAtHyper_neg` below).

DERIVED: no numeral. -/
theorem corrSep_negAt (Nc : ℕ) {d n : ℕ} [NeZero n] {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ)
    (β : ℝ) (v : Site d n) :
    corrSep Nc μ ν β (negAt τ v) = corrSep Nc μ ν β v := by
  have h := wilsonCorrConn_refl (Nc := Nc) τ (0 : Fin n) β
    (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) (((μ, ν), v) : Plaq d n)
  rw [reflPlaq_transverse hμ hν (0 : Fin n) (fun _ => 0 : Site d n),
    reflPlaq_transverse hμ hν (0 : Fin n) v,
    reflSite_zero_eq_negAt τ (fun _ => 0 : Site d n), reflSite_zero_eq_negAt τ v,
    negAt_origin (n := n) τ] at h
  exact h

/-- The one-axis case: `corrSep` at the one-axis separation with lag `-lag` equals the one at lag
`lag`. This is `MomentShape.corrHyper_neg` recovered from `corrSep_negAt`.

DERIVED: no numeral. -/
theorem corrSep_siteAtHyper_neg (Nc : ℕ) {d n : ℕ} [NeZero n] {μ ν τ : Fin d}
    (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) (lag : Fin n) :
    corrSep Nc μ ν β (siteAtHyper τ (-lag)) = corrSep Nc μ ν β (siteAtHyper τ lag) := by
  rw [← negAt_siteAtHyper (n := n) τ lag]
  exact corrSep_negAt Nc hμ hν β _

end Circle

/-- **Componentwise circle symmetry at the Clay parameters.** Either transverse component of a
four-vector separation may be negated, at every extent and every real coupling.

DERIVED: `0` and `1` are `corrVec`'s plane, and the two hypotheses `0 ≠ τ`, `1 ≠ τ` say exactly that
`τ` is one of the two remaining directions; `4` in `Fin 4` and `Site 4 n` is the lattice dimension.
The `3` of `SU(3)` is in `corrVec`'s definition, not in this statement. -/
theorem corrVec_negAt (n : ℕ) [NeZero n] {τ : Fin 4} (h0 : (0 : Fin 4) ≠ τ) (h1 : (1 : Fin 4) ≠ τ)
    (β : ℝ) (v : Site 4 n) :
    corrVec n β (negAt τ v) = corrVec n β v := by
  show corrSep (d := 4) 3 0 1 β (negAt τ v) = corrSep (d := 4) 3 0 1 β v
  exact corrSep_negAt (d := 4) 3 h0 h1 β v

/-! ## Part 6 — nonnegativity and positive mass, at the single-axis separations

Reflection positivity through one hyperplane pairs a plaquette observable with its own mirror image,
and the mirror of a site differs from it in one coordinate. So the pairing bounds the correlation at
a separation supported on the reflection axis, and the statements below say no more than that. -/

section Nonneg

variable {d n Nc : ℕ} [NeZero n]

/-- **Nonnegative at a single-axis separation with even lag**, at every real coupling, on an
even-extent lattice `n = 2 * m` with `0 < m`, gauge rank `Nc ≠ 0`, and both plane directions
different from the lag axis `τ`. This is
`ReflectionStrong.corrHyper_nonneg_even_lag_of_module` transported to the general-separation object.
The separation has one nonzero coordinate because a reflection through one hyperplane moves one
coordinate; nothing here bounds `corrSep` at a separation with two or more nonzero components.

DERIVED: the statement's numerals are the `0` in `Nc ≠ 0`, the `2` in `n = 2 * m`, the `0` in
`0 < m` and the `0` the correlation is bounded below by. The `2` is the two halves a reflection
hyperplane cuts the periodic lattice into, the reflection geometry's own; `Even lag.val` carries no
numeral of its own. -/
theorem corrSep_nonneg_even_single_axis (hN : Nc ≠ 0) (τ : Fin d) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) {μ ν : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    {lag : Fin n} (hlag : Even lag.val) :
    0 ≤ corrSep Nc μ ν β (siteAtHyper τ lag) :=
  MassGap.ReflectionStrong.corrHyper_nonneg_even_lag_of_module hN τ m hm hm0 hμ hν β hlag

end Nonneg

/-- **The Clay correlation is nonnegative at a single-axis separation with even lag, along either
transverse direction**, at even extent `Nap + 1 = 2 * m` with `0 < m` and at every real coupling.
The axis `τ` is quantified over and constrained only by `0 ≠ τ` and `1 ≠ τ`, so it may be either
direction transverse to `corrVec`'s plane.

DERIVED: the statement's numerals are the `1` in `Nap + 1`, the lag arity and the extent, the `2` in
`2 * m` saying that extent is even, the `0` in `0 < m`, the `4` of `Fin 4` and the `0` and `1` of
`corrVec`'s plane appearing in the hypotheses on `τ`, and the `0` the correlation is bounded below
by. The `3` of `SU(3)` is in the proof, not in the statement. -/
theorem corrVec_nonneg_even_single_axis (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {τ : Fin 4} (h0 : (0 : Fin 4) ≠ τ) (h1 : (1 : Fin 4) ≠ τ)
    {lag : Fin (Nap + 1)} (hlag : Even lag.val) :
    0 ≤ corrVec (Nap + 1) β (siteAtHyper τ lag) := by
  show (0 : ℝ) ≤ corrSep (d := 4) 3 0 1 β (siteAtHyper τ lag)
  exact corrSep_nonneg_even_single_axis (Nc := 3) (by norm_num) τ m hm hm0 h0 h1 β hlag

/-- **Strictly positive at zero separation**, at every extent and every real coupling: the
correlation at the zero four-vector is the plaquette-energy variance, strictly positive by
`PlaqVariance.corrClay_zero_pos`. So `corrVec` is not identically zero and the nonnegativity
statements above are not vacuous.

DERIVED: the statement's numerals are the `0` the correlation is bounded below by, the `1` in `N + 1`
making the extent positive so that `Fin` is inhabited, the `4` of `Site 4 (N + 1)`, the lattice
dimension, and the `0` of the origin site `fun _ => 0`, which is the zero separation. The direction
`2` used in the proof to name that site is immaterial: by `LogConvex.siteAtHyper_zero` the site at
lag zero is the origin whichever direction is named. -/
theorem corrVec_zero_pos (N : ℕ) (β : ℝ) : 0 < corrVec (N + 1) β (fun _ => 0 : Site 4 (N + 1)) := by
  have hzero : siteAtHyper (d := 4) (n := N + 1) (2 : Fin 4) 0 = (fun _ => 0 : Site 4 (N + 1)) :=
    MassGap.LogConvex.siteAtHyper_zero (2 : Fin 4)
  rw [← hzero, corrVec_restricts_to_corrClay]
  exact MassGap.PlaqVariance.corrClay_zero_pos N β

section Audit
#print axioms corrSep
#print axioms corrHyper_eq_corrSep
#print axioms corrSep_unfold
#print axioms corrVec
#print axioms corrVec_restricts_to_corrClay
#print axioms corrVec_siteAtHyper
#print axioms corrSep_abs_le_four
#print axioms corrVec_abs_le_four
#print axioms wilsonPlaqObs_relabel
#print axioms expect_relabel
#print axioms wilsonCorr_eq_expect
#print axioms expect_pair_relabel
#print axioms expect_one_relabel
#print axioms wilsonCorrConn_relabel
#print axioms axisPlaq_mk
#print axioms axisSite_origin
#print axioms axisSite_siteAtHyper
#print axioms corrSep_axis
#print axioms corrSep_axis_fix
#print axioms corrVec_swap_transverse
#print axioms corrVec_siteAtHyper_three_eq_two
#print axioms corrVec_siteAtHyper_three
#print axioms reflPlaq_transverse
#print axioms EW_pair_refl
#print axioms EW_one_refl
#print axioms wilsonCorrConn_refl
#print axioms negAt
#print axioms reflSite_zero_eq_negAt
#print axioms negAt_origin
#print axioms negAt_siteAtHyper
#print axioms corrSep_negAt
#print axioms corrSep_siteAtHyper_neg
#print axioms corrVec_negAt
#print axioms corrSep_nonneg_even_single_axis
#print axioms corrVec_nonneg_even_single_axis
#print axioms corrVec_zero_pos
end Audit

end MassGap.CorrVec
