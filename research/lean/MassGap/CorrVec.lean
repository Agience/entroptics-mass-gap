import Mathlib
import MassGap.ReflectionStrong
import MassGap.InfiniteVolume
import MassGap.PlaqVariance

/-!
# MassGap.CorrVec — the plaquette correlation at a GENERAL lattice separation

## What was narrow

`WilsonBridge.corrClay n β lag = corrHyper (d := 4) 3 n 0 1 2 β lag`: the plaquette plane is spanned
by directions `0` and `1`, and the second plaquette sits at `siteAtHyper 2 lag`, a site whose only
nonzero coordinate is along direction `2`. So the whole development downstream of it — the moment
read, the aperture, the spectral measure of `MomentMeasure.rieszMeasure` — is indexed by ONE integer,
the lag along one axis. A Schwinger function is a function of a four-vector separation, and a
one-axis family is a restriction of one, not one.

## What is here

`corrSep Nc μ ν β v` is the connected correlation of the `(μ,ν)`-plane plaquette at the ORIGIN with
the `(μ,ν)`-plane plaquette at an ARBITRARY site `v : Fin d → Fin n`, and `corrVec n β v` is its
`SU(3)`, four-dimensional, `(0,1)`-plane instance. `corrVec_restricts_to_corrClay` is the statement
that makes it an extension rather than a new object: `corrVec n β (siteAtHyper 2 lag) = corrClay n β
lag`, and it is `rfl`.

Four pieces of structure carry, and the file says which and how far:

* **The extent-free bound** carries with no hypothesis beyond a nonzero gauge rank: `corrSep_abs_le_four` is
  `InfiniteVolume.wilsonCorrConn_abs_le_four`, which never looked at the geometry.
* **Componentwise circle symmetry** carries: `corrSep_negAt` negates ANY ONE coordinate of `v` in a
  direction transverse to the plane and the correlation is unchanged, at every extent and every real
  coupling. `MomentShape.corrHyper_neg` is its one-axis case (`corrSep_siteAtHyper_neg`).
* **Axis permutation — the first genuinely four-dimensional statement.** `corrSep_axis` says
  relabelling the axes by any `e : Equiv.Perm (Fin d)` carries the correlation to the one with plane
  `(e μ, e ν)` and separation `axisSite e v`. When `e` fixes the plane (`corrSep_axis_fix`) the
  separation's components may be permuted among themselves with the correlation unchanged. At the
  Clay parameters that is `corrVec_swap_transverse`, and one of its consequences is
  `corrVec_siteAtHyper_three_eq_two`: the lag along direction `3` and the lag along direction `2`
  are the same number, which no theorem in the tree previously proved, though corrHyper could always express it.
* **Nonnegativity and positive mass carry ONLY on the single-axis separations, and that is not a gap
  in the proof but the shape of the input.** See the next section.

## How far reflection positivity reaches, stated exactly

The site reflection is `Reflect.reflSite τ c x = Function.update x τ (c - x τ)` — it moves ONE
coordinate. The Osterwalder–Seiler pairing that `ReflectionStrong` proves nonnegative is
`⟨F · (F ∘ Θ)⟩` read at ONE member of the module (the module statement itself ranges over all of localObs) `F` based at a site `x`, and `Θ` carries that
plaquette to the one based at `reflSite τ c x`. The separation between the two is therefore
`reflSite τ c x - x`, whose only nonzero coordinate is along `τ`. So the one-plaquette pairing
produces nonnegativity of the correlation at one-axis separations and at no others:
`corrSep_nonneg_even_single_axis` is the statement, with the even-parity and half-extent hypotheses
`ReflectionStrong.corrHyper_nonneg_even_lag_of_module` already carries.

What is NOT claimed, and what would be needed to claim it: a separation with two or more nonzero
components is not the reflection of anything through one hyperplane, so nothing here bounds
`corrSep Nc μ ν β v` below for such a `v`. The reflection module `LogConvex.localObs` is
closed under linear combination and its Gram form is nonnegative, which gives a positive
SEMIDEFINITE QUADRATIC FORM over families of sites — and the separations appearing inside that form
do have several nonzero components. Extracting a pointwise lower bound at a general separation from
that quadratic form is a separate argument and is not attempted here.

## What a Schwinger function still needs after this file

Three things, none of them touched here and none of them small.

1. **Smearing.** A Schwinger function is a distribution: it is paired with test functions on
   spacetime, not evaluated at lattice sites. Nothing here defines a pairing of `corrVec` against a
   test function, and the lattice-to-continuum embedding that such a pairing needs does not exist in
   the tree.
2. **The continuum limit.** `corrVec` lives at finite extent `n` and finite lattice spacing. The
   limit `n → ∞` is `InfiniteVolume`'s subject in the ONE-axis variable only; the joint limit at a
   scaled general separation, and the lattice spacing going to zero with a renormalised coupling,
   are both absent. `Measure.continuum_of_family` is deliberately untouched.
3. **The `k`-point functions for `k > 2`.** `corrVec` is a TWO-point function. OS reconstruction
   consumes the whole family `{S_k}` with its symmetry, positivity and cluster properties; a
   two-point function alone reconstructs a free field and nothing else.

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

/-- **The connected plaquette correlation at a GENERAL separation.**

`corrSep Nc μ ν β v = ⟨φ_{(μ,ν),0} · φ_{(μ,ν),v}⟩_β − ⟨φ_{(μ,ν),0}⟩_β ⟨φ_{(μ,ν),v}⟩_β`, the
connected two-point function of the `(μ,ν)`-plane plaquette energy at the origin with the one at the
site `v`, on the `d`-dimensional periodic `SU(Nc)` Wilson lattice of extent `n`.

`WilsonBridge.corrHyper` is this with `v` forced to be `siteAtHyper τ lag` — a site with one nonzero
coordinate. Here `v` is any site, which is what a two-point Schwinger function needs and what a
single lag index cannot express.

DERIVED: no literal sets a scale. The origin is immaterial by periodicity of the lattice; the plane
and the separation are the caller's. -/
noncomputable def corrSep (Nc : ℕ) {d n : ℕ} [NeZero n] (μ ν : Fin d) (β : ℝ) (v : Site d n) : ℝ :=
  wilsonCorrConn (Nc := Nc) (bd (d := d) (n := n))
    ((μ, ν), (fun _ => 0 : Site d n)) β ((μ, ν), v)

/-- **`corrHyper` is `corrSep` at a one-axis separation** — definitionally, so the two objects are
not merely related but the same construction at a restricted argument. -/
theorem corrHyper_eq_corrSep (Nc : ℕ) {d n : ℕ} [NeZero n] (μ ν τ : Fin d) (β : ℝ) (lag : Fin n) :
    corrHyper (d := d) Nc n μ ν τ β lag = corrSep Nc μ ν β (siteAtHyper τ lag) := rfl

/-- `corrSep` written out as the two-point function minus the product of one-point functions, in the
notation `ReflectPositive` uses. Definitional; it is the working form for every proof below. -/
theorem corrSep_unfold (Nc : ℕ) {d n : ℕ} [NeZero n] (μ ν : Fin d) (β : ℝ) (v : Site d n) :
    corrSep Nc μ ν β v
      = EW Nc β (fun U => plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n) U
            * plaqE Nc (((μ, ν), v) : Plaq d n) U)
        - EW Nc β (plaqE Nc (((μ, ν), (fun _ => 0 : Site d n)) : Plaq d n))
          * EW Nc β (plaqE Nc (((μ, ν), v) : Plaq d n)) := rfl

end Object

/-- **The four-dimensional `SU(3)` correlation at a general four-vector separation.**

The Clay problem's dimension and gauge group, on the lattice `WilsonGauge`'s Osterwalder–Schrader
measure is built on, with the separation a full site of `Fin 4 → Fin n` rather than a single lag.

DERIVED: `3` is `SU(3)` and `4` is four dimensions — the problem's own data, exactly as in
`WilsonBridge.corrClay`; `0` and `1` span the plaquette plane and which two directions those are is a
naming freedom (`corrSep_axis` below turns that freedom into a theorem). `n` is the periodic extent
and stays the caller's. -/
noncomputable def corrVec (n : ℕ) [NeZero n] (β : ℝ) (v : Site 4 n) : ℝ :=
  corrSep (d := 4) 3 0 1 β v

/-- **THE RESTRICTION: `corrClay` is `corrVec` at a separation along direction `2`.**

This is the statement that makes the generalisation an extension of the development rather than a
second object beside it. Every theorem the tree proves about `corrClay` — reflection positivity at
even lag, circle symmetry, log-convexity, the moment read, the representing measure of
`MomentMeasure.rieszMeasure` — is a theorem about `corrVec` restricted to the one-axis separations,
and it is `rfl`, so nothing is lost in the transport.

DERIVED: `2` is the lag direction `corrClay` itself names, transverse to its `(0,1)` plane. -/
theorem corrVec_restricts_to_corrClay (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    corrVec n β (siteAtHyper (2 : Fin 4) lag) = corrClay n β lag := rfl

/-- `corrVec` at a separation along any direction `τ` is `corrHyper` with lag axis `τ`.

DERIVED: `3` is `SU(3)`, `4` the dimension and `0`, `1` the plane — all `corrVec`'s own. -/
theorem corrVec_siteAtHyper (n : ℕ) [NeZero n] (β : ℝ) (τ : Fin 4) (lag : Fin n) :
    corrVec n β (siteAtHyper τ lag) = corrHyper (d := 4) 3 n 0 1 τ β lag := rfl

/-! ## Part 2 — the extent-free bound, which carries with no hypothesis

`InfiniteVolume.wilsonCorrConn_abs_le_four` is stated for an arbitrary boundary-word map and an
arbitrary pair of plaquettes: the unconnected correlation lies in `[0,4]` and each one-point function
in `[0,2]`, and no geometry enters. So it applies at a general separation verbatim. -/

section Bound

variable {d n Nc : ℕ} [NeZero n]

/-- **The correlation at ANY separation is bounded by `4`**, at every extent, every real coupling and
every plane. No hypothesis beyond a nonzero gauge rank.

DERIVED: `4` is `2 × 2`, the product of the two plaquette-energy ranges — it is
`InfiniteVolume.wilsonCorrConn_abs_le_four`'s constant, carried unchanged, and nothing about the
separation enters it. -/
theorem corrSep_abs_le_four (hN : Nc ≠ 0) (μ ν : Fin d) (β : ℝ) (v : Site d n) :
    |corrSep Nc μ ν β v| ≤ 4 :=
  MassGap.InfiniteVolume.wilsonCorrConn_abs_le_four hN _ _ _ _

/-- The same at the Clay parameters.

DERIVED: `4` is the bound above; `3` is `SU(3)`, whose rank is nonzero, which is the only hypothesis
the general statement had. -/
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
here is that it moves the CONNECTED two-plaquette correlation, which needs the one-point functions to
move too. -/

section Relabel

variable {Nc : ℕ} {Lk Pq : Type} [Fintype Lk] [Fintype Pq]

/-- **A relabelled configuration gives the relabelled plaquette's observable.** The `compat` field of
`WilsonLattice.wilsonSymmetry`, pushed through the (class-function) Wilson density. -/
theorem wilsonPlaqObs_relabel (bd' : Pq → List (Lk × Bool))
    (σL : Equiv.Perm Lk) (σP : Equiv.Perm Pq)
    (hbd : ∀ p, bd' (σP p) = (bd' p).map (fun lo => (σL lo.1, lo.2)))
    (q : Pq) (U : (wilsonSystem bd' (wilsonDensity (N := Nc))).Config) :
    wilsonPlaqObs (N := Nc) bd' q (fun l => U (σL l))
      = wilsonPlaqObs (N := Nc) bd' (σP q) U :=
  congrArg (wilsonDensity (N := Nc))
    ((wilsonSymmetry bd' (wilsonDensity (N := Nc)) σL σP hbd).compat q U)

/-- The Gibbs expectation is unchanged when the configuration is relabelled — `wilson_expect_invariant`
with the `Symmetry.reindex` wrapper removed, so it can be rewritten under. -/
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

/-- `wilsonCorr` as a Gibbs expectation of the product of the two plaquette observables.
Definitional; it is here because `unfold` will not open `wilsonCorr` under the subtraction in
`wilsonCorrConn`, and a rewrite needs the equation as a lemma. -/
theorem wilsonCorr_eq_expect (bd' : Pq → List (Lk × Bool)) (p₀ : Pq) (β : ℝ) (p : Pq) :
    MassGap.WilsonBridge.wilsonCorr (Nc := Nc) bd' p₀ β p
      = (wilsonSystem bd' (wilsonDensity (N := Nc))).expect (probHaar (MassGap.SUN.SU Nc)) β
          (fun U => wilsonPlaqObs (N := Nc) bd' p₀ U * wilsonPlaqObs (N := Nc) bd' p U) := rfl

/-- The two-plaquette expectation moves with the relabelling. -/
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

/-- The one-plaquette expectation moves with the relabelling. -/
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

/-- **THE CONNECTED CORRELATION IS INVARIANT UNDER A LATTICE RELABELLING**, at any geometry: moving
both plaquettes by the plaquette permutation of a `wilsonSymmetry` leaves the connected two-point
function unchanged. The disconnected part moves too, which is why this needs `expect_one_relabel` and
is not a restatement of `wilson_expect_invariant`. -/
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
compatibility hypothesis the relabelling machinery above consumes. Instantiating at it gives the
first statement in the development that is about a four-dimensional separation rather than a lag. -/

section Axis

variable {d n Nc : ℕ} [NeZero n]

/-- The axis relabelling of a plaquette, computed on its components. -/
theorem axisPlaq_mk (e : Equiv.Perm (Fin d)) (μ ν : Fin d) (x : Site d n) :
    axisPlaq (n := n) e (((μ, ν), x) : Plaq d n) = ((e μ, e ν), axisSite e x) := rfl

/-- The origin is fixed by an axis relabelling. -/
theorem axisSite_origin (e : Equiv.Perm (Fin d)) :
    axisSite (n := n) e (fun _ => 0 : Site d n) = (fun _ => 0 : Site d n) :=
  funext fun _ => rfl

/-- **A one-axis separation relabels to a one-axis separation along the relabelled axis.** -/
theorem axisSite_siteAtHyper (e : Equiv.Perm (Fin d)) (τ : Fin d) (lag : Fin n) :
    axisSite (n := n) e (siteAtHyper τ lag) = siteAtHyper (e τ) lag := by
  funext j
  simp only [axisSite, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  by_cases h : j = e τ
  · subst h
    simp [siteAtHyper]
  · have h' : e.symm j ≠ τ := fun hc => h (by rw [← hc]; simp)
    simp [siteAtHyper, Function.update_of_ne h, Function.update_of_ne h']

/-- **EUCLIDEAN INVARIANCE AT A GENERAL SEPARATION.**

Relabelling the lattice axes by any permutation `e` carries the correlation of the `(μ,ν)`-plane at
separation `v` to the correlation of the `(e μ, e ν)`-plane at separation `axisSite e v`. Both sides
are Gibbs expectations of the real `SU(Nc)` Wilson ensemble at the same coupling; the content is that
the action and the product Haar measure are invariant under the relabelling
(`WilsonHypercubic.bd_axis`, then `wilsonCorrConn_relabel`).

This is the discrete Euclidean symmetry of the hypercubic lattice acting on a FOUR-VECTOR separation.
The one-axis object `corrHyper` could not state it: a permutation acting on a single lag index has
nothing to permute. -/
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

For a permutation that FIXES the two directions spanning the plaquette plane, the plane does not move
and the statement is about the separation alone: `corrSep` depends on `v` only up to the axis
permutations that preserve the plane. This is the invariance a two-point Schwinger function is
required to have, restricted to the lattice's own symmetry group. -/
theorem corrSep_axis_fix (Nc : ℕ) {d n : ℕ} [NeZero n] (e : Equiv.Perm (Fin d)) {μ ν : Fin d}
    (hμ : e μ = μ) (hν : e ν = ν) (β : ℝ) (v : Site d n) :
    corrSep Nc μ ν β (axisSite e v) = corrSep Nc μ ν β v := by
  have h := corrSep_axis Nc e μ ν β v
  rwa [hμ, hν] at h

end Axis

/-- **THE FOUR-DIMENSIONAL STATEMENT, AT THE CLAY PARAMETERS.** Exchanging directions `2` and `3` —
the two directions transverse to the `(0,1)` plaquette plane — leaves the `SU(3)` four-dimensional
correlation unchanged at EVERY separation, every extent and every real coupling.

DERIVED: `2` and `3` are the two directions of `Fin 4` that are not `0` or `1`, i.e. the complement of
the plaquette plane; the transposition of them is the only nontrivial permutation of `Fin 4` that
fixes the plane pointwise, so it is not one choice among several. The `0` and `1` are `corrVec`'s own
plane. -/
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
extent, every real coupling and every lag — so `corrClay`, which names direction `2`, was naming a
representative of an orbit and not a choice that could have mattered.

Nothing in the tree could state this before: it is the axis symmetry acting on a separation, and a
one-index lag has no axis to act on.

DERIVED: `2` and `3` are the two directions transverse to `corrVec`'s `(0,1)` plane, as in
`corrVec_swap_transverse`. -/
theorem corrVec_siteAtHyper_three_eq_two (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    corrVec n β (siteAtHyper (3 : Fin 4) lag) = corrVec n β (siteAtHyper (2 : Fin 4) lag) := by
  have hswap : Equiv.swap (2 : Fin 4) 3 2 = 3 := Equiv.swap_apply_left 2 3
  have h := corrVec_swap_transverse n β (siteAtHyper (2 : Fin 4) lag)
  rwa [axisSite_siteAtHyper (n := n) (Equiv.swap (2 : Fin 4) 3) 2 lag, hswap] at h

/-- The same statement read against `corrClay`: the lag-`lag` correlation along direction `3` IS the
Clay correlation.

DERIVED: `3` is the fourth lattice direction, `2` the one `corrClay` names. -/
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
The third branch of `Reflect.reflPlaq`, for an arbitrary base rather than the origin
(`ReflectPositive.reflPlaq_origin`) or a one-axis site (`LogConvex.reflPlaq_siteAtHyper`). -/
theorem reflPlaq_transverse {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (c : Fin n) (x : Site d n) :
    reflPlaq τ c (((μ, ν), x) : Plaq d n) = ((μ, ν), reflSite τ c x) := by
  simp only [reflPlaq, hμ, hν, if_false]

/-- The two-plaquette expectation is unchanged when BOTH plaquettes are reflected. -/
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

/-- The one-plaquette expectation is unchanged when the plaquette is reflected. -/
theorem EW_one_refl (Nc : ℕ) {d n : ℕ} [NeZero n] (τ : Fin d) (c : Fin n) (β : ℝ)
    (q : Plaq d n) :
    EW Nc β (plaqE Nc (reflPlaq τ c q)) = EW Nc β (plaqE Nc q) := by
  have h : EW Nc β (fun U => plaqE Nc q (reflConf τ c U)) = EW Nc β (plaqE Nc q) :=
    expect_reflect_invariant (n := n) Nc τ c β (plaqE Nc q)
  rw [← h]
  exact congrArg (EW Nc β) (funext fun U => (plaqE_reflConf Nc τ c q U).symm)

/-- **THE CONNECTED CORRELATION IS INVARIANT UNDER REFLECTING BOTH PLAQUETTES**, at any reflection
axis and constant, any plane and any pair of sites. The reflection is not a `LatticeGauge.Symmetry`
— it carries the dagger — so this is not an instance of `wilsonCorrConn_relabel`; it comes from
`Reflect.expect_reflect_invariant`, which reaches the same conclusion through
`System.expect_invariant_of_mp`. -/
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

DERIVED: nothing numeric; the negation is `Fin n`'s own, which is modular, so it is the circle
inversion of that coordinate rather than a sign convention. -/
def negAt {d n : ℕ} (τ : Fin d) (v : Site d n) : Site d n :=
  Function.update v τ (-(v τ))

/-- The reflection at constant zero IS the componentwise negation. -/
theorem reflSite_zero_eq_negAt (τ : Fin d) (v : Site d n) :
    reflSite τ (0 : Fin n) v = negAt τ v := by
  funext j
  by_cases h : j = τ
  · subst h; simp [reflSite, negAt]
  · simp [reflSite, negAt, Function.update_of_ne h]

/-- Negating a component of the origin leaves the origin. -/
theorem negAt_origin (τ : Fin d) : negAt (n := n) τ (fun _ => 0 : Site d n) = (fun _ => 0) := by
  funext j
  by_cases h : j = τ
  · subst h; simp [negAt]
  · simp [negAt, Function.update_of_ne h]

/-- Negating the one nonzero component of a one-axis separation is negating its lag. -/
theorem negAt_siteAtHyper (τ : Fin d) (lag : Fin n) :
    negAt (n := n) τ (siteAtHyper τ lag) = siteAtHyper τ (-lag) := by
  funext j
  by_cases h : j = τ
  · subst h; simp [negAt, siteAtHyper]
  · simp [negAt, siteAtHyper, Function.update_of_ne h]

/-- **COMPONENTWISE CIRCLE SYMMETRY AT A GENERAL SEPARATION.**

Negating ANY ONE coordinate of the separation, in a direction transverse to the plaquette plane,
leaves the correlation unchanged — at every extent, every real coupling and every plane. No
hypothesis on the parity of the component, on the sign of the coupling, or on the other components.

`MomentShape.corrHyper_neg` is the special case in which the separation had only that one component
to begin with (`corrSep_siteAtHyper_neg` below). -/
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

/-- The one-axis case, which is `MomentShape.corrHyper_neg` recovered from the general statement. -/
theorem corrSep_siteAtHyper_neg (Nc : ℕ) {d n : ℕ} [NeZero n] {μ ν τ : Fin d}
    (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) (lag : Fin n) :
    corrSep Nc μ ν β (siteAtHyper τ (-lag)) = corrSep Nc μ ν β (siteAtHyper τ lag) := by
  rw [← negAt_siteAtHyper (n := n) τ lag]
  exact corrSep_negAt Nc hμ hν β _

end Circle

/-- **Componentwise circle symmetry at the Clay parameters.** Either transverse component of a
four-vector separation may be negated.

DERIVED: `3` is `SU(3)` and `0`, `1` span `corrVec`'s plane; `τ` is the caller's and the two
hypotheses say exactly that it is one of the two remaining directions. -/
theorem corrVec_negAt (n : ℕ) [NeZero n] {τ : Fin 4} (h0 : (0 : Fin 4) ≠ τ) (h1 : (1 : Fin 4) ≠ τ)
    (β : ℝ) (v : Site 4 n) :
    corrVec n β (negAt τ v) = corrVec n β v := by
  show corrSep (d := 4) 3 0 1 β (negAt τ v) = corrSep (d := 4) 3 0 1 β v
  exact corrSep_negAt (d := 4) 3 h0 h1 β v

/-! ## Part 6 — nonnegativity and positive mass: exactly the single-axis separations

Reflection positivity through one hyperplane pairs a plaquette observable with its own mirror image,
and the mirror of a site differs from it in ONE coordinate. So what the pairing bounds below is the
correlation at a separation supported on the reflection axis, and the statements below say no more
than that. The module docstring records what would be needed to go further. -/

section Nonneg

variable {d n Nc : ℕ} [NeZero n]

/-- **NONNEGATIVE AT A SINGLE-AXIS SEPARATION**, at every real coupling, on an even-extent lattice and
at an even component. This is `ReflectionStrong.corrHyper_nonneg_even_lag_of_module` transported to
the general-separation object, and it is the FULL reach of the one-plaquette reflection argument: the
separation has one nonzero coordinate because a reflection through one hyperplane moves one
coordinate.

DERIVED: `2` in `n = 2 * m` is the two halves a reflection hyperplane cuts the periodic lattice into,
which is the reflection geometry's own and not a choice made here. -/
theorem corrSep_nonneg_even_single_axis (hN : Nc ≠ 0) (τ : Fin d) (m : ℕ) (hm : n = 2 * m)
    (hm0 : 0 < m) {μ ν : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ)
    {lag : Fin n} (hlag : Even lag.val) :
    0 ≤ corrSep Nc μ ν β (siteAtHyper τ lag) :=
  MassGap.ReflectionStrong.corrHyper_nonneg_even_lag_of_module hN τ m hm hm0 hμ hν β hlag

end Nonneg

/-- **The Clay correlation is nonnegative at every single-axis, even separation, along EITHER
transverse direction**, at every real coupling.

That it holds along direction `3` as well as direction `2` is the axis symmetry doing work: it is
`corrSep_nonneg_even_single_axis` at `τ = 3`, and `corrVec_siteAtHyper_three_eq_two` says the two
numbers are equal rather than merely both nonnegative.

DERIVED: `3` is `SU(3)`, whose rank is nonzero; `2` in `Nap + 1 = 2 * m` is the two halves of the
reflection geometry; `0` and `1` are `corrVec`'s plane, and the hypotheses say `τ` is neither. -/
theorem corrVec_nonneg_even_single_axis (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ)
    {τ : Fin 4} (h0 : (0 : Fin 4) ≠ τ) (h1 : (1 : Fin 4) ≠ τ)
    {lag : Fin (Nap + 1)} (hlag : Even lag.val) :
    0 ≤ corrVec (Nap + 1) β (siteAtHyper τ lag) := by
  show (0 : ℝ) ≤ corrSep (d := 4) 3 0 1 β (siteAtHyper τ lag)
  exact corrSep_nonneg_even_single_axis (Nc := 3) (by norm_num) τ m hm hm0 h0 h1 β hlag

/-- **POSITIVE MASS AT ZERO SEPARATION**, at every extent and every real coupling: the correlation at
the zero four-vector is the plaquette-energy VARIANCE, strictly positive by
`PlaqVariance.corrClay_zero_pos`. So the general-separation object is not identically zero and the
nonnegativity statements above are not vacuous.

DERIVED: `2` is the direction whose zero lag is used to name the zero separation; by
`LogConvex.siteAtHyper_zero` the site is the origin whichever direction is named, so nothing depends
on it. -/
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
