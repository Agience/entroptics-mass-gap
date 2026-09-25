import Mathlib
import MassGap.GNSCompare
import MassGap.ReflectionHalfSpace
import MassGap.Mixing
import MassGap.WilsonState
import MassGap.GaugeInvariantAlgebra

/-!
# MassGap.ClayCapstone — what the transfer chain delivers, and on which algebra

`GNSCompare` was a terminal leaf: nothing imported it, so the chain from reflection positivity to the
transfer spectrum was built and unused. `ReflectionHalfSpace` holds the Wilson side. This module was
the first to import both, and it states what they give.

## The routes, in the order they were found

* `clay_gap_of_rayleigh` — from `PositiveTransfer` and a vacuum Rayleigh ceiling `Λ < 1`.
  `clay_gap_of_lambdaTwo` asks the same as a bound on one real number, `SecondEigenvalue.lambdaTwo`;
  `clay_gap_on_interval` runs `Mixing.interior_mixing_of_analytic_grid` into it for a whole coupling
  interval, which a continuum limit wants.
* `clay_gap_of_gapAt` — **shorter**, and the form the rest of the tree produces.
  `TransferGap.GapAt` needs no Rayleigh statement and no subdominant supremum, and
  `ReflectionHalfSpace.gapAt_of_finite_volume_connected` builds it from a finite-volume
  connected-correlator inequality. `wilson_clay_gap_of_gapAt` is its `SU(N)` instance.
* `wilson_clay_gap_at_zero_coupling` — the chain closed end to end at `β = 0` with **no open
  input**, which is what shows the hypotheses above are jointly satisfiable.
* `gaugeInv_clay_gap_of_pairing` — the same on the **gauge-invariant** algebra, where reflection
  positivity and `PositiveTransfer` restrict for free and a pairing inequality is the only input.

## Which algebra, and why it matters

`WilsonTransferReduction.transferData_of_state_facts` builds on `HalfSpaceAlgebra.halfSpaceAlg`, a
locality predicate containing `halfLinkObs l f` — an arbitrary continuous function of a single link
variable. A gap bound there must hold for observables that are not gauge invariant, while
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` bounds a plaquette pair. The two do not
meet. `GaugeInvariantAlgebra` supplies the smaller algebra where they do.

Everything else on the route is proved: `GNSCompare.inner_Tq_nonneg_of_positiveTransfer`,
`SecondEigenvalue.norm_Tq_le_of_rayleigh`, `GNSCompare.gapAt_of_positiveTransfer_of_rayleigh`,
`GapToOperator.spectrum_opT_subset`, `GNSHilbert.spectrum_opT_nonneg`,
`GNSHilbert.isGreatest_one_spectrum_opT`, `GNSHilbert.spectrum_opT_subset_unit_interval`.

## Why there is no `ε`

Clay asks for `spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ` at some `Δ > 0`. Through `T = exp (-H)` that reads
`spectrum ℝ T ⊆ {1} ∪ Set.Icc 0 (Real.exp (-Δ))`, with `0` **admitted**: a theory whose energies are
unbounded has a transfer spectrum accumulating at zero. `Reconstruction.reconstruct_qm_core` asks
instead for `Set.Icc ε (Real.exp (-Δ))` with `0 < ε`, and the tree says three times over what that
costs — `TransferInvertibility.energies_bounded_of_spectral_hypothesis` makes it a ceiling on the
energies, `isUnit_of_spectral_hypothesis` makes it `IsUnit T`, and `spectral_hypothesis_fails_for_compact`
says a compact `T` on an infinite-dimensional space meets it at no `ε`. So `ε` is not an obligation
awaiting discharge; it is what `Reconstruction.hamiltonian`'s `cfc (fun x => -Real.log x)` needs to
have a continuous function on the spectrum, `-Real.log` being discontinuous at `0`.

## Scope

This is the spectral containment for the transfer operator, not `MassFinite.clayMass`. Reading it as
a statement about a Hamiltonian needs an unbounded functional calculus, which `Reconstruction` does
not carry. And `hray` is the mass gap's quantitative content: nothing here produces a `Λ`.
-/

namespace MassGap.ClayCapstone

open MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.GNSCompare

/-- **The gap from two inputs.** For any `TransferData` carrying `PositiveTransfer` and a vacuum
Rayleigh ceiling `Λ < 1`, the GNS transfer operator is self-adjoint, its spectrum lies in
`{1} ∪ Set.Icc 0 (exp (-Δ))` at `Δ = -Real.log Λ > 0`, and `1` is its greatest element.

The four conjuncts are the spectral content of a mass gap: a vacuum at the top of the spectrum, a
band strictly below it, and a positive `Δ` separating them. `Δ` is the band's own width read
logarithmically — no threshold is chosen anywhere on the route.

`GNSHilbert.spectrum_opT_subset_unit_interval` says the containment is not vacuous by construction:
the spectrum sits in `[-1, 1]` before any hypothesis, so `Λ < 1` is the entire content.

This is PACKAGING, and the packaging is the point of the module rather than new mathematics. The two
substantial conjuncts are `GNSCompare.spectrum_opT_gap_form` verbatim; the other two are
`GNSHilbert.isSelfAdjoint_opT` and `GNSHilbert.isGreatest_one_spectrum_opT`, both unconditional. It
is stated here so that `wilson_clay_gap_of_rayleigh` below has one name to instantiate, and so that
the hypothesis list a reader has to satisfy is visible in one signature.

DERIVED: `1` is the vacuum eigenvalue and the contraction constant — the same number, which is why
`Λ < 1` is content rather than choice; `0` is the bottom of the spectrum, from
`GNSHilbert.spectrum_opT_nonneg`, and the lower end of `hΛ`; `2` is the Rayleigh quotient's exponent
in `hray`. -/
theorem clay_gap_of_rayleigh {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) {Λ : ℝ} (hΛ : 0 < Λ) (h1 : Λ < 1)
    (hP : PositiveTransfer D)
    (hray : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 →
      (inner ℝ (D.Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    IsSelfAdjoint (opT D)
      ∧ 0 < -Real.log Λ
      ∧ spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log Λ)))
      ∧ IsGreatest (spectrum ℝ (opT D)) 1 := by
  obtain ⟨hΔ, hsp⟩ := spectrum_opT_gap_form D hΛ h1 hP hray
  exact ⟨isSelfAdjoint_opT D, hΔ, hsp, isGreatest_one_spectrum_opT D⟩

#print axioms clay_gap_of_rayleigh

/-- **The gap from `GapAt` directly, at one coupling.**

`TransferGap.GapAt D r` is the tree's own gap predicate, and `GapToOperator.spectrum_opT_subset`
already carries it to `spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc (-r) r`. With
`GNSHilbert.spectrum_opT_nonneg` cutting the bottom, that is the Clay containment. No Rayleigh
ceiling is needed as a separate hypothesis — `GapAt` is the same content in the form the rest of the
tree produces.

**This matters because it is what the finite-volume work already feeds.**
`ReflectionHalfSpace.gapAt_of_finite_volume_connected` produces `GapAt` for the Wilson transfer data
from a finite-volume connected-correlator inequality, which is R1's `hfin`. So the route from R1 to
the gap needs no Rayleigh statement and no subdominant supremum at all.

**And it needs no coupling interval.** `clay_gap_on_interval` gives the gap uniformly in β, which a
continuum limit wants; the gap at ONE coupling is strictly weaker and is what a lattice mass gap
asks for. The Lipschitz modulus and the grid are a route, not a requirement.

DERIVED: `1` is the vacuum eigenvalue and the contraction constant; `0` is the bottom of the
spectrum and the lower end of `hr`. -/
theorem clay_gap_of_gapAt {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hP : PositiveTransfer D) (hg : MassGap.TransferGap.GapAt D r) :
    IsSelfAdjoint (opT D)
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ (opT D)) 1 := by
  refine ⟨isSelfAdjoint_opT D, by simpa using Real.log_neg hr h1, ?_,
    isGreatest_one_spectrum_opT D⟩
  rw [neg_neg, Real.exp_log hr]
  intro x hx
  rcases MassGap.GapToOperator.spectrum_opT_subset D hr.le hg hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Set.mem_Ici.mp (spectrum_opT_nonneg D hP hx), h.2⟩

#print axioms clay_gap_of_gapAt

/-- **The gap on the gauge-invariant algebra.** The same conclusion as `clay_gap_of_gapAt`, at the
transfer data `GaugeInvariantAlgebra.gaugeInvTransferData` built on observables that are local in the
positive half **and** invariant under the local gauge group on `ℤ⁴`.

Two of the three inputs come from the `halfSpaceAlg` development at no cost, because both
hypotheses quantify over the algebra and a smaller algebra inherits them:
`GaugeInvariantAlgebra.reflPositiveOn_gaugeInv` restricts reflection positivity, and
`positiveTransfer_gaugeInv` restricts positivity of the transfer. **Only `GapAt` below one is left**,
and it is asked here of an algebra containing no `HalfSpaceAlgebra.halfLinkObs l f` — no arbitrary
continuous function of a single link variable — which is what put the bound out of reach of
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow`, a plaquette-pair result.

`GaugeInvariantAlgebra.mem_gaugeInvHalfSpaceAlg_of_classFun` shows the algebra is not the constants,
so this is not a statement about an empty class.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`; `1` is
the vacuum eigenvalue and the contraction constant; `0` is the bottom of the spectrum and the lower
end of `hr`. -/
theorem gaugeInv_clay_gap_of_gapAt {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G]
    [CompactSpace G] (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(MassGap.InfiniteLattice.IConf G, ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (hP : MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu))
    {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hg : MassGap.TransferGap.GapAt
      (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu) r) :
    IsSelfAdjoint (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ
          (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ
          (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))) 1 :=
  clay_gap_of_gapAt _ hr h1
    (MassGap.GaugeInvariantAlgebra.positiveTransfer_gaugeInv τ p ν hinv hpos hnu hP) hg

#print axioms gaugeInv_clay_gap_of_gapAt

/-- **The gauge-invariant route, in one signature.**

Every link is proved; this composes them so the remaining obligation sits in one hypothesis list
instead of across three modules. `hfin` says: for every observable local in the positive half and
invariant under the local gauge group on `ℤ⁴`, moving the reflection plane out by two costs a factor
`r²` in the mean-subtracted pairing.

What is discharged rather than assumed: reflection positivity and `PositiveTransfer`, both restricted
from the `halfSpaceAlg` development by
`GaugeInvariantAlgebra.reflPositiveOn_gaugeInv` and `positiveTransfer_gaugeInv`, since each
quantifies over the algebra; the `GapAt` characterisation, by
`GaugeInvariantAlgebra.gaugeInv_gapAt_iff_subtracted_pairing`; and the whole delivery half.

**`hfin` is the only input, and it is the physics.** It is asked here of an algebra containing no
`HalfSpaceAlgebra.halfLinkObs l f` — no arbitrary continuous function of a single link variable —
which is the shape `StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow`, a plaquette-pair
bound, can speak to. `GaugeInvariantAlgebra.mem_gaugeInvHalfSpaceAlg_of_classFun` shows the algebra
is not the constants, so this is not a statement about an empty class.

DERIVED: `4` is the spacetime dimension; `2` is the plane-to-constant doubling in `2 * p`, the two
planes' separation in `2 * p - 2`, and the exponent in the pairing bound; `1` is the vacuum
eigenvalue, the contraction constant and the unit observable; `0` is the bottom of the spectrum and
the lower end of `hr`. -/
theorem gaugeInv_clay_gap_of_pairing {G : Type} [Group G] [TopologicalSpace G] [ContinuousInv G]
    [CompactSpace G] (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(MassGap.InfiniteLattice.IConf G, ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (hP : MassGap.GNSHilbert.PositiveTransfer
      (MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu))
    {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hfin : ∀ F ∈ MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p,
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p - 2) (F - ν F • 1) * (F - ν F • 1))
        ≤ r ^ 2 * ν (MassGap.LatticeReflection.ireflObs τ (2 * p) (F - ν F • 1)
          * (F - ν F • 1))) :
    IsSelfAdjoint (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ
          (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ
          (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))) 1 :=
  gaugeInv_clay_gap_of_gapAt τ p ν hinv hpos hnu hP hr h1
    ((MassGap.GaugeInvariantAlgebra.gaugeInv_gapAt_iff_subtracted_pairing
      τ p ν hinv hpos hnu r).mpr hfin)

#print axioms gaugeInv_clay_gap_of_pairing

/-- **The gap from a bound on one real number.**

`clay_gap_of_rayleigh` asks for a bound quantified over vectors. This asks for the same content as a
bound on `SecondEigenvalue.lambdaTwo` — the subdominant eigenvalue read variationally, a single real
number — and that is the shape the remaining work produces:
`Mixing.interior_mixing_of_analytic_grid` concludes `ρ₁ β < 1` about a function `ℝ → ℝ` of the
coupling, not about vectors.

`SecondEigenvalue.rayleigh_le_of_lambdaTwo_le` is the bridge and it was already in the tree, with no
consumers. This is its first.

`V` is any submodule containing the vacuum complement, given by `hV`, so no orthogonal complement is
built at the call site. `hbdd` is not decorative: `sSup` of a set unbounded above is a junk value,
and without it `hlam` would constrain nothing.

**So the remaining obligation has the shape of a number.** To finish the chain it is enough to
exhibit a `V` containing the vacuum complement on which the transfer form's Rayleigh supremum is
bounded and below one. `StrongCouplingGap.wilson_gaugeInv_clay_gap_strong_coupling` does that at
strong coupling, on the vacuum complement, through per-vector decay.

DERIVED: `1` is the vacuum eigenvalue and the contraction constant; `0` is the bottom of the
spectrum and the lower end of `hΛ`; `2` is the Rayleigh quotient's exponent. All are
`clay_gap_of_rayleigh`'s, carried unchanged. -/
theorem clay_gap_of_lambdaTwo {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (V : Submodule ℝ (GNS D.toReflForm))
    (hV : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 → y ∈ V)
    (hbdd : BddAbove (MassGap.SecondEigenvalue.rayleighSet D.Tq V))
    {Λ : ℝ} (hΛ : 0 < Λ) (h1 : Λ < 1) (hP : PositiveTransfer D)
    (hlam : MassGap.SecondEigenvalue.lambdaTwo D.Tq V ≤ Λ) :
    IsSelfAdjoint (opT D)
      ∧ 0 < -Real.log Λ
      ∧ spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log Λ)))
      ∧ IsGreatest (spectrum ℝ (opT D)) 1 := by
  refine clay_gap_of_rayleigh D hΛ h1 hP (fun y hy => ?_)
  refine le_trans (MassGap.SecondEigenvalue.rayleigh_le_of_lambdaTwo_le D.Tq V hbdd (hV y hy)) ?_
  exact mul_le_mul_of_nonneg_right hlam (by positivity)

#print axioms clay_gap_of_lambdaTwo

/-- **A transfer operator's Rayleigh set is always bounded above.**

`Transfer.TransferData.Tq_norm_le` makes `Tq` a norm-contraction, from the `T_contract` field, so
`SecondEigenvalue.bddAbove_rayleighSet_of_norm_le` applies at every `V`.

So the `hbdd` hypothesis carried by `clay_gap_of_lambdaTwo`, `clay_gap_of_form_decay`,
`clay_gap_of_two_point_decay` and `gaugeInv_clay_gap_of_state_decay` is not an open assumption on
this route — it is discharged here, for any transfer data and any submodule.

DERIVED: no numeral occurs; `V` is the caller's. -/
theorem bddAbove_rayleighSet_Tq {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (V : Submodule ℝ (GNS D.toReflForm)) :
    BddAbove (MassGap.SecondEigenvalue.rayleighSet D.Tq V) :=
  MassGap.SecondEigenvalue.bddAbove_rayleighSet_of_norm_le D.Tq V
    (MassGap.Transfer.TransferData.Tq_norm_le D)

#print axioms bddAbove_rayleighSet_Tq

/-- **The GNS norm of an iterate IS the reflection form at the iterated representative.**

`HalfLineTransfer.Tq_pow_mk` moves the iterate onto the representative and
`Transfer.GNS.norm_mk_mul_norm_mk` reads the norm as the form. Stated here rather than beside
`Tq_pow_mk` because this is where it is consumed.

This is the translation the estimate side needs: `SecondEigenvalue.lambdaTwo_le_of_iterate_bound`
asks for decay of `‖Tq ^ n y‖`, a statement in the GNS space, and this says that quantity is the
reflection form at a translated observable — the object a correlation estimate speaks about.

DERIVED: no numeral occurs. -/
theorem norm_Tq_pow_mk_mul {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (n : ℕ) (x : A) :
    ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖ * ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖
      = D.form ((D.T ^ n) x) ((D.T ^ n) x) := by
  rw [MassGap.HalfLineTransfer.Tq_pow_mk D n x, GNS.norm_mk_mul_norm_mk]

#print axioms norm_Tq_pow_mk_mul

/-- **A bound on the form at even separations bounds the class's iterates.**

`norm_Tq_pow_mk_mul` and `TransferGap.form_pow_diag` give `‖Tqⁿ [x]‖² = form x (T²ⁿ x)`, so
`form x (T²ⁿ x) ≤ K · r²ⁿ` gives `‖Tqⁿ [x]‖ ≤ √(max K 0) · rⁿ`. This is how a bound on the
reflected-shifted state pairing, which is what `GaugeInvariantAlgebra.gaugeInv_form_pow` makes the form,
becomes the per-vector decay `clay_gap_of_absolute_decay` consumes.

DERIVED: `0` is the lower bound on `r` and the floor taken inside the square root; `2` is the
doubling of the separation and the exponent of the square. -/
theorem absolute_decay_of_form_decay {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (x : A) {K r : ℝ} (hr : 0 ≤ r)
    (h : ∀ n : ℕ, D.form x ((D.T ^ (2 * n)) x) ≤ K * r ^ (2 * n)) :
    ∃ K' : ℝ, ∀ n : ℕ, ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖ ≤ K' * r ^ n := by
  refine ⟨Real.sqrt (max K 0), fun n => ?_⟩
  have ha0 : 0 ≤ ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖ := norm_nonneg _
  have hsq : ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖ * ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖
      ≤ max K 0 * (r ^ n) ^ 2 := by
    rw [norm_Tq_pow_mk_mul, MassGap.TransferGap.form_pow_diag]
    calc D.form x ((D.T ^ (2 * n)) x) ≤ K * r ^ (2 * n) := h n
      _ ≤ max K 0 * r ^ (2 * n) := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr _)
      _ = max K 0 * (r ^ n) ^ 2 := by ring
  calc ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖
      = Real.sqrt (‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖ * ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖) :=
        (Real.sqrt_mul_self ha0).symm
    _ ≤ Real.sqrt (max K 0 * (r ^ n) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (max K 0) * r ^ n := by
        rw [Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq (pow_nonneg hr n)]

#print axioms absolute_decay_of_form_decay

/-- **The Clay spectral statement from decay of the reflection form under translation.**

The relative route, stated entirely in terms of the reflection form. `hdec` says the form of an
observable translated `n` steps decays geometrically against its own untranslated form — which is
what a connected-correlation estimate at growing separation asserts, and it is an UPPER bound.

The chain: `norm_Tq_pow_mk_mul` turns `hdec` into decay of `‖Tq ^ n y‖`;
`SecondEigenvalue.lambdaTwo_le_of_iterate_bound` turns that into `lambdaTwo ≤ ρ`, washing out the
constant `C` by Archimedean descent; `clay_gap_of_lambdaTwo` closes.

**No lower bound on the form is required at any point.** That is what separates this from the Gram
and diagonal-dominance route, where the strictly positive diagonal is a demand of the reduction
rather than of the obligation, and where the reflected-pairing no-go applies.

`GaugeInvariantAlgebra.gaugeInv_form_pow` identifies the form with the reflected-shifted pairing in
the state, and `StrongCouplingGap.decay_of_orth` supplies `hdec`'s content at strong coupling.

DERIVED: `0` is the strict lower bound on `C` and `ρ` and the bottom of the spectrum; `1` is the
vacuum eigenvalue and the contraction threshold; `2` is the square in the decay hypothesis, matching
the form's quadratic degree. -/
theorem clay_gap_of_form_decay {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (V : Submodule ℝ (GNS D.toReflForm))
    (hV : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 → y ∈ V)
    (hbdd : BddAbove (MassGap.SecondEigenvalue.rayleighSet D.Tq V))
    (hne : (MassGap.SecondEigenvalue.rayleighSet D.Tq V).Nonempty)
    {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ) (h1 : ρ < 1) (hP : PositiveTransfer D)
    (hdec : ∀ x : A, GNS.mk D.toReflForm x ∈ V → ∀ n : ℕ,
      D.form ((D.T ^ n) x) ((D.T ^ n) x) ≤ (C * ρ ^ n) ^ 2 * D.form x x) :
    IsSelfAdjoint (opT D)
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ (opT D)) 1 := by
  refine clay_gap_of_lambdaTwo D V hV hbdd hρ h1 hP ?_
  refine MassGap.SecondEigenvalue.lambdaTwo_le_of_iterate_bound D.Tq
    D.Tq_isSymmetric V hne hC hρ.le ?_
  intro y hy n
  obtain ⟨x, rfl⟩ := GNS.exists_mk y
  have hu : (0 : ℝ) ≤ ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖ := norm_nonneg _
  have hv : (0 : ℝ) ≤ ‖GNS.mk D.toReflForm x‖ := norm_nonneg _
  have hK : (0 : ℝ) ≤ C * ρ ^ n := by positivity
  have hw : (0 : ℝ) ≤ C * ρ ^ n * ‖GNS.mk D.toReflForm x‖ := mul_nonneg hK hv
  have hbase : ‖GNS.mk D.toReflForm x‖ * ‖GNS.mk D.toReflForm x‖ = D.form x x := by
    rw [GNS.norm_mk_mul_norm_mk]
  have hsq : ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖ * ‖(D.Tq ^ n) (GNS.mk D.toReflForm x)‖
      ≤ (C * ρ ^ n * ‖GNS.mk D.toReflForm x‖) * (C * ρ ^ n * ‖GNS.mk D.toReflForm x‖) := by
    rw [norm_Tq_pow_mk_mul D n x]
    calc D.form ((D.T ^ n) x) ((D.T ^ n) x)
        ≤ (C * ρ ^ n) ^ 2 * D.form x x := hdec x hy n
      _ = (C * ρ ^ n) ^ 2 * (‖GNS.mk D.toReflForm x‖ * ‖GNS.mk D.toReflForm x‖) := by
          rw [hbase]
      _ = (C * ρ ^ n * ‖GNS.mk D.toReflForm x‖)
            * (C * ρ ^ n * ‖GNS.mk D.toReflForm x‖) := by ring
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul_self hu, Real.sqrt_mul_self hw] at hroot

#print axioms clay_gap_of_form_decay

/-- **The Clay spectral statement from contact-relative decay of the two-point function.**

`clay_gap_of_form_decay` with its hypothesis rewritten by `TransferGap.form_pow_diag`, which is an
identity. So the whole relative route now runs from

    ∀ x, mk x ∈ V → ∀ n, D.form x ((D.T ^ (2 * n)) x) ≤ (C · ρ ^ n) ^ 2 · D.form x x

with `ρ < 1`, to the Clay spectral statement.

**Read what that hypothesis says.** `D.form x ((D.T ^ (2 * n)) x)` is the reflected pairing of an
observable with itself translated `2 * n` steps — a two-point function at a separation that grows
with `n`. `D.form x x` is the same observable at separation zero, the contact value. So the
hypothesis is a contact-relative decay law, geometric in the separation, and it is an UPPER bound
throughout. That is the same shape as `NonnegArm.LawAbove`, which the aperture route also reduces
to, reached here by a different chain.

No lower bound on the form appears anywhere in this route, which is what distinguishes it from the
Gram and diagonal-dominance one.

Still open: nothing identifies `D.form x ((D.T ^ (2 * n)) x)` at the Wilson transfer data with the
connected correlators `StrongCoupling` bounds. That is one identification, not an estimate.

DERIVED: `0` is the strict lower bound on `C` and `ρ` and the bottom of the spectrum; `1` is the
vacuum eigenvalue and the contraction threshold; `2` is the doubling in `form_pow_diag`, and the
square in the decay hypothesis. -/
theorem clay_gap_of_two_point_decay {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (V : Submodule ℝ (GNS D.toReflForm))
    (hV : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 → y ∈ V)
    (hbdd : BddAbove (MassGap.SecondEigenvalue.rayleighSet D.Tq V))
    (hne : (MassGap.SecondEigenvalue.rayleighSet D.Tq V).Nonempty)
    {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ) (h1 : ρ < 1) (hP : PositiveTransfer D)
    (hdec : ∀ x : A, GNS.mk D.toReflForm x ∈ V → ∀ n : ℕ,
      D.form x ((D.T ^ (2 * n)) x) ≤ (C * ρ ^ n) ^ 2 * D.form x x) :
    IsSelfAdjoint (opT D)
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ (opT D)) 1 :=
  clay_gap_of_form_decay D V hV hbdd hne hC hρ h1 hP
    (fun x hx n => by
      rw [MassGap.TransferGap.form_pow_diag D n x]
      exact hdec x hx n)

#print axioms clay_gap_of_two_point_decay

/-- **The spectral gap from absolute decay of the transfer iterates, one vector at a time.**

Each vector of `V` may carry its own constant: `‖Tqⁿ y‖ ≤ K_y · ρⁿ`. That is the form a cluster
estimate produces, and `SecondEigenvalue.lambdaTwo_le_of_absolute_iterate_bound` turns it into
`lambdaTwo ≤ ρ` with no lower bound on any pairing, because the constant is chosen after the vector.
`bddAbove_rayleighSet_Tq` discharges the boundedness unconditionally, and `clay_gap_of_lambdaTwo`
gives the spectral conclusion: `opT` self-adjoint, spectrum in `{1} ∪ [0, ρ]`, and `1` the top.

DERIVED: `0` is the lower end of the spectrum and the strict lower bound on `ρ`; `1` is the vacuum
eigenvalue and the strict upper bound on `ρ`. -/
theorem clay_gap_of_absolute_decay {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (V : Submodule ℝ (GNS D.toReflForm))
    (hV : ∀ y : GNS D.toReflForm, (inner ℝ D.vacGNS y : ℝ) = 0 → y ∈ V)
    (hne : (MassGap.SecondEigenvalue.rayleighSet D.Tq V).Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ < 1) (hP : PositiveTransfer D)
    (hdec : ∀ y ∈ V, ∃ K : ℝ, ∀ n : ℕ, ‖(D.Tq ^ n) y‖ ≤ K * ρ ^ n) :
    IsSelfAdjoint (opT D)
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ (opT D)) 1 :=
  clay_gap_of_lambdaTwo D V hV (bddAbove_rayleighSet_Tq D V) hρ h1 hP
    (MassGap.SecondEigenvalue.lambdaTwo_le_of_absolute_iterate_bound D.Tq D.Tq_isSymmetric V hne
      hρ.le hdec)

#print axioms clay_gap_of_absolute_decay

/-- **The Clay spectral statement from decay of the state's reflected two-point function.**

The whole relative route, stated with no GNS construction and no transfer data in the hypothesis.
`GaugeInvariantAlgebra.gaugeInv_form_pow` reads the transfer form as a state pairing, and
`clay_gap_of_two_point_decay` closes.

What `hdec` asks: for each gauge-invariant half-space observable `x` whose class lies in the vacuum
complement, the state's pairing of `ireflObs τ (2 * p) x` with `x` translated `2 * n` steps decays
geometrically against the same pairing at no translation. A contact-relative decay law on the
limiting state, geometric in the separation, an upper bound throughout.

This is the obligation, in the terms the strong-coupling side speaks. Two things still separate it
from `GaugeInvariantAlgebra.stateFree_pairing_abs_le`, and neither is cosmetic: that bound is at
`stateFree` on a finite box rather than at the limiting state `ν`, and it pairs an observable with
the REFLECTED plaquette rather than with a TRANSLATE of itself.

DERIVED: `2` is the reflection plane's spacing, the doubling of `form_pow_diag`, and the square in
the decay law; `0` is the strict lower bound on `C` and `ρ` and the bottom of the spectrum; `1` is
the vacuum eigenvalue and the contraction threshold; `4` is the spacetime dimension. -/
theorem gaugeInv_clay_gap_of_state_decay {G : Type} [Group G] [TopologicalSpace G]
    [ContinuousInv G] [CompactSpace G] (τ : Fin 4) (p : ℤ)
    (ν : MassGap.DLRLimit.State (MassGap.InfiniteLattice.IConf G))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := G) τ p) ν)
    (hnu : ∀ f : C(MassGap.InfiniteLattice.IConf G, ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f)
    (V : Submodule ℝ (GNS (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData
      τ p ν hinv hpos hnu).toReflForm))
    (hV : ∀ y, (inner ℝ (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData
        τ p ν hinv hpos hnu).vacGNS y : ℝ) = 0 → y ∈ V)
    (hbdd : BddAbove (MassGap.SecondEigenvalue.rayleighSet
      (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).Tq V))
    (hne : (MassGap.SecondEigenvalue.rayleighSet
      (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).Tq V).Nonempty)
    {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ) (h1 : ρ < 1)
    (hP : PositiveTransfer (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData
      τ p ν hinv hpos hnu))
    (hdec : ∀ x : ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := G) τ p),
      GNS.mk (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData
        τ p ν hinv hpos hnu).toReflForm x ∈ V → ∀ n : ℕ,
      ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.InfiniteLattice.IConf G, ℝ))
          * (⇑(MassGap.ReflectionShift.ishiftObsL τ))^[2 * n]
            (x : C(MassGap.InfiniteLattice.IConf G, ℝ)))
        ≤ (C * ρ ^ n) ^ 2
          * ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
              (x : C(MassGap.InfiniteLattice.IConf G, ℝ))
            * (x : C(MassGap.InfiniteLattice.IConf G, ℝ)))) :
    IsSelfAdjoint (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))
      ∧ 0 < -Real.log ρ
      ∧ spectrum ℝ
          (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log ρ)))
      ∧ IsGreatest (spectrum ℝ
          (opT (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu))) 1 := by
  refine clay_gap_of_two_point_decay _ V hV hbdd hne hC hρ h1 hP (fun x hx n => ?_)
  have hform0 : (MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν hinv hpos hnu).form x x
      = ν (MassGap.LatticeReflection.ireflObs τ (2 * p)
            (x : C(MassGap.InfiniteLattice.IConf G, ℝ))
          * (x : C(MassGap.InfiniteLattice.IConf G, ℝ))) := by
    simpa using MassGap.GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν hinv hpos hnu x 0
  rw [MassGap.GaugeInvariantAlgebra.gaugeInv_form_pow τ p ν hinv hpos hnu x (2 * n), hform0]
  exact hdec x hx n

#print axioms gaugeInv_clay_gap_of_state_decay

/-! ### The coupling-indexed subdominant ratio -/

/-- **`ρ₁`, defined.** The subdominant Rayleigh supremum of a coupling-indexed family of transfer
data, as a function `ℝ → ℝ` of the coupling.

`Mixing.interior_mixing_of_analytic_grid` concludes `ρ₁ β < 1` on an interval, and its `ρ₁` is an
unconstrained `ℝ → ℝ` — no transfer data, no operator. That is why it has never been instantiated.
This is the function it was written for.

The half-space algebra is a locality predicate and does not depend on the coupling, so the family is
`D : ℝ → TransferData A` over a fixed `A`, and only the GNS space varies, through `D β`. `V` is
dependent for the same reason.

DERIVED: no numeral occurs; the subscript is `SecondEigenvalue.lambdaTwo`'s own reading of the
subdominant eigenvalue. -/
noncomputable def rhoOne {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : ℝ → TransferData A)
    (V : ∀ β : ℝ, Submodule ℝ (GNS (D β).toReflForm)) (β : ℝ) : ℝ :=
  MassGap.SecondEigenvalue.lambdaTwo (D β).Tq (V β)

#print axioms rhoOne

/-- **The mass gap at every coupling in an interval, from a Lipschitz modulus and a grid.**

This is the join. `Mixing.interior_mixing_of_analytic_grid` turns a Lipschitz modulus for `rhoOne`
and a covering of the interval by grid points where `rhoOne γ ≤ (1 - ε) - Lδ` into `rhoOne β < 1`
everywhere on it; `clay_gap_of_lambdaTwo` turns that into the gap. Nothing between the two was
missing except a definition of `ρ₁`.

**What this makes precise is the remaining work.** Every hypothesis here is about `rhoOne` or about
the transfer family, and there is nothing downstream of them:

* `hlip` — a Lipschitz modulus for the subdominant ratio in the coupling. Unproved, and the shape of
  the obstruction is worth naming. `rhoOne D V x` and `rhoOne D V z` are both reals, so the
  hypothesis is well formed, but they are suprema over `GNS (D x).toReflForm` and
  `GNS (D z).toReflForm`, which are **different types**.
  `SecondEigenvalue.lambdaTwo_dist_le` bounds the distance between two subdominant suprema from a
  pointwise bound on the forms, and it needs both on ONE space, so it does not apply here. The GNS
  space genuinely varies with the coupling — a different measure gives a different Hilbert space —
  so a modulus in the coupling needs an identification of those spaces first: a common dense core,
  or a unitary family.
* `hcover` — grid values below `(1 - ε) - Lδ`. Unproved. The measured grid in `research/data` is a
  failure to refute this, not a proof of it, and instantiating `hcover` from measurements would be a
  fit.
* `hP`, `hbdd`, `hV`, `hpos` — structural: positivity of the transfer, boundedness of the Rayleigh
  set, the vacuum complement, and `rhoOne β > 0`.

`hpos` is a hypothesis and not a consequence: `clay_gap_of_lambdaTwo` needs `0 < Λ` so that
`-Real.log Λ` is not `Real.log`'s junk value at zero, and a Rayleigh supremum can vanish. Where it
does vanish the gap is unbounded, which is the degenerate case
`WilsonState.gapAt_zero_at_zero_coupling` exhibits at zero coupling.

DERIVED: `1` is the ceiling `interior_mixing_of_analytic_grid` concludes below, and the vacuum
eigenvalue; `0` is the lower bound on `L`, the strict lower bounds on `ε` and on `rhoOne β`, and the
bottom of the spectrum; `2` is the Rayleigh quotient's exponent. `L`, `δ`, `ε`, `a` and `b` are all
the caller's. -/
theorem clay_gap_on_interval {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : ℝ → TransferData A)
    (V : ∀ β : ℝ, Submodule ℝ (GNS (D β).toReflForm))
    (hV : ∀ (β : ℝ) (y : GNS (D β).toReflForm),
      (inner ℝ (D β).vacGNS y : ℝ) = 0 → y ∈ V β)
    (hbdd : ∀ β : ℝ, BddAbove (MassGap.SecondEigenvalue.rayleighSet (D β).Tq (V β)))
    (hP : ∀ β : ℝ, PositiveTransfer (D β))
    (hpos : ∀ β : ℝ, 0 < rhoOne D V β)
    {a b L δ ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |rhoOne D V x - rhoOne D V y| ≤ L * |x - y|)
    (hcover : ∀ β ∈ Set.Icc a b, ∃ γ ∈ Set.Icc a b,
      |β - γ| ≤ δ ∧ rhoOne D V γ ≤ (1 - ε) - L * δ) :
    ∀ β ∈ Set.Icc a b,
      IsSelfAdjoint (opT (D β))
        ∧ 0 < -Real.log (rhoOne D V β)
        ∧ spectrum ℝ (opT (D β))
            ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log (rhoOne D V β))))
        ∧ IsGreatest (spectrum ℝ (opT (D β))) 1 := by
  intro β hβ
  exact clay_gap_of_lambdaTwo (D β) (V β) (hV β) (hbdd β) (hpos β)
    (MassGap.interior_mixing_of_analytic_grid hL hε hlip hcover β hβ) (hP β) le_rfl

#print axioms clay_gap_on_interval

section Wilson

open MassGap.ReflectionHalfSpace

variable {N : ℕ}

/-- The `TransferData` on the `ℤ⁴` half-space algebra that a convergent family of free-boundary
Wilson states produces, named so the Rayleigh ceiling can be stated about it.

This is `WilsonTransferReduction.transferData_of_state_facts` with its three state facts read off
`htend` exactly as `ReflectionHalfSpace.wilson_positiveTransfer_of_mixCube_limit` reads them, so
that theorem proves `PositiveTransfer` of this definition by unfolding.

DERIVED: `4` is the spacetime dimension, the `Fin 4` the lattice is indexed by; `0` is the excluded
gauge rank in `hN : N ≠ 0`; `2` is the doubling in the reflection plane `2 * p`,
`ReflectionHalfSpace`'s own index convention; `1` is the all-identity boundary configuration. All
are transcribed. -/
noncomputable def wilsonMixCubeData (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    TransferData ↥(MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) :=
  MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))

#print axioms wilsonMixCubeData

/-- **The gauge-invariant transfer data at the free-boundary limit state.**

`wilsonMixCubeData` above is the same construction on the full half-space algebra;
`GaugeInvariantAlgebra.gaugeInvTransferData` takes the same three state facts and lands on
`gaugeInvHalfSpaceAlg`, the observables invariant under a local gauge transformation. That is the
algebra the physical Hilbert space is built from, so this is the data the mass-gap statement should
be read on.

The three facts are produced from `htend` exactly as `wilsonMixCubeData` produces them:
reflection invariance about the plane `2p` from `wilson_reflInvariant_of_tendsto`, reflection
positivity from `wilson_reflPositive_even_of_tendsto`, and shift invariance from
`wilson_nu_T_of_tendsto` — the last DERIVED from reflection invariance about two adjacent planes
rather than assumed.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`; `1` is the
all-identity boundary configuration `htend` is stated at and the Wilson density's vanishing value;
`2` is the doubling in the reflection plane and the density's ceiling. All are inherited. -/
noncomputable def wilsonGaugeInvMixCubeData (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f))) :
    TransferData ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg
      (G := MassGap.SUN.SU N) τ p) :=
  MassGap.GaugeInvariantAlgebra.gaugeInvTransferData τ p ν
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))

#print axioms wilsonGaugeInvMixCubeData

/-- **The gauge-invariant spectral statement from `GapAt` directly.**

`wilson_clay_gap_of_gapAt` on the full half-space algebra, restated on
`GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg`. `GaugeInvariantAlgebra.positiveTransfer_gaugeInv`
carries `PositiveTransfer` across, so the only hypotheses are the thermodynamic limit `htend` and the
gap `hg` at the gauge-invariant data.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`, the lower end of
`hβ` and `hr`, and the bottom of the spectrum; `1` is the all-identity boundary configuration, the
vacuum eigenvalue and the contraction threshold; `2` is the doubling in the reflection plane. -/
theorem wilson_gaugeInv_clay_gap_of_gapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hg : MassGap.TransferGap.GapAt (wilsonGaugeInvMixCubeData τ p hN β ν htend) r) :
    IsSelfAdjoint (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν htend))) 1 :=
  gaugeInv_clay_gap_of_gapAt τ p ν
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend))
    (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN β ν htend))
    (wilson_positiveTransfer_of_mixCube_limit τ p hN hβ ν htend) hr h1 hg

#print axioms wilson_gaugeInv_clay_gap_of_gapAt

/-- **The mass gap for `SU(N)` Wilson theory on `ℤ⁴`, from one quantitative input.**

`hβ` and `htend` are the thermodynamic limit: convergence of the free-boundary states along one
exhausting family of boxes. They give `PositiveTransfer` through
`wilson_positiveTransfer_of_mixCube_limit`, which is
`WilsonTransferReduction.positiveTransfer_iff_odd_reflPositive`'s content at the limiting state. The
only other hypothesis is the vacuum Rayleigh ceiling at some `Λ < 1`.

The conclusion is the spectral statement of a mass gap for the transfer operator of the
infinite-volume theory: self-adjoint, vacuum at the top of the spectrum, everything else at or below
`exp (-Δ)` with `Δ = -Real.log Λ > 0`. The gauge group is `SU N` at arbitrary `N ≠ 0` and the lattice
is `ℤ⁴`; no named axiom is on the route.

What is NOT here: a `Λ`. The Rayleigh ceiling is the mass gap's quantitative content, and nothing in
this tree produces one below `1`. Everything else the chain needed has been discharged.

DERIVED: `4` is the spacetime dimension, the `Fin 4` the lattice is indexed by; `1` is the vacuum
eigenvalue, the contraction constant, and the all-identity boundary configuration `htend` is stated
at; `0` is the bottom of the spectrum, the excluded gauge rank in `hN`, and the lower ends of `hβ`
and `hΛ`; `2` is the Rayleigh exponent and the doubling in the reflection plane. All are
inherited. -/
theorem wilson_clay_gap_of_rayleigh (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    {Λ : ℝ} (hΛ : 0 < Λ) (h1 : Λ < 1)
    (hray : ∀ y : GNS (wilsonMixCubeData τ p hN β ν htend).toReflForm,
      (inner ℝ (wilsonMixCubeData τ p hN β ν htend).vacGNS y : ℝ) = 0 →
      (inner ℝ ((wilsonMixCubeData τ p hN β ν htend).Tq y) y : ℝ) ≤ Λ * ‖y‖ ^ 2) :
    IsSelfAdjoint (opT (wilsonMixCubeData τ p hN β ν htend))
      ∧ 0 < -Real.log Λ
      ∧ spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log Λ)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν htend))) 1 :=
  clay_gap_of_rayleigh _ hΛ h1
    (wilson_positiveTransfer_of_mixCube_limit τ p hN hβ ν htend) hray

#print axioms wilson_clay_gap_of_rayleigh

/-- The three state facts do not affect the transfer data: any two proofs give the same term.

`transferData_of_state_facts` takes `hinv`, `hpos` and `hnu` as arguments, so two callers passing
different proofs would in general build different terms — which would stop
`ReflectionHalfSpace.gapAt_of_finite_volume_connected` and
`wilson_positiveTransfer_of_mixCube_limit` from being about the same operator. They are `Prop`s, so
Lean's definitional proof irrelevance collapses the difference, and this checks that by `rfl`
rather than asserting it. -/
example (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    (hinv : MassGap.InfiniteReflection.IsReflectionInvariant
      (MassGap.LatticeReflection.latticeReflection τ (2 * p)) ν)
    (hpos : MassGap.InfiniteReflection.ReflPositiveOn
      (MassGap.LatticeReflection.latticeReflection τ (2 * p))
      (MassGap.HalfSpaceAlgebra.halfSpaceAlg (G := MassGap.SUN.SU N) τ p) ν)
    (hnu : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      ν (MassGap.ReflectionShift.ishiftObsL τ f) = ν f) :
    wilsonMixCubeData τ p hN β ν htend
      = MassGap.WilsonTransferReduction.transferData_of_state_facts τ p ν hinv hpos hnu :=
  rfl

/-- **R1 to the gap, on the Wilson data, with no ρ₁ machinery.**

`wilson_positiveTransfer_of_mixCube_limit` discharges `PositiveTransfer` from the thermodynamic
limit, and `clay_gap_of_gapAt` needs nothing else but `GapAt` below one. So the only hypothesis is
`hg`, and `ReflectionHalfSpace.gapAt_of_finite_volume_connected` is what produces it — from R1's
`hfin`, a finite-volume connected-correlator inequality along the box family, with no Rayleigh
ceiling, no subdominant supremum and no coupling interval anywhere.

The `example` above checks the two are about the same transfer data.

DERIVED: `4` is the spacetime dimension; `1` is the vacuum eigenvalue, the contraction constant and
the all-identity boundary configuration; `0` is the bottom of the spectrum, the excluded gauge rank
in `hN`, and the lower ends of `hβ` and `hr`; `2` is the doubling in the reflection plane. -/
theorem wilson_clay_gap_of_gapAt (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β (mixCube τ p n) 1 f)
        Filter.atTop (nhds (ν f)))
    {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hg : MassGap.TransferGap.GapAt (wilsonMixCubeData τ p hN β ν htend) r) :
    IsSelfAdjoint (opT (wilsonMixCubeData τ p hN β ν htend))
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν htend))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν htend))) 1 :=
  clay_gap_of_gapAt _ hr h1
    (wilson_positiveTransfer_of_mixCube_limit τ p hN hβ ν htend) hg

#print axioms wilson_clay_gap_of_gapAt

/-- **The thermodynamic limit at zero coupling**, in the form the positivity producer consumes.

`WilsonDLR.tendsto_specState_at_zero` gives a DLR state and convergence along ALL finite regions.
`wilson_positiveTransfer_of_mixCube_limit` wants convergence along the interleaved box sequence, and
`ReflectionHalfSpace.tendsto_mixCube` says that sequence is cofinal, so the first limit restricts to
the second. `WilsonState.stateFree_eq_spec_at_zero_coupling` turns the fixed-boundary states the
first is about into the free-boundary states the second is about, and `WilsonDLR.specState` is
`GibbsSpec.spec` wrapped, so that step is definitional.

`continuous_wilsonDensity` covers the regularity mismatch: `stateFree` carries measurability and
`tendsto_specState_at_zero` asks for continuity, and continuity gives measurability.

DERIVED: `4` is the spacetime dimension; `0` is the coupling and the excluded gauge rank in `hN`;
`1` is the all-identity boundary configuration; `2` is the doubling in the reflection plane and the
bound on the plaquette density. -/
theorem wilson_htend_at_zero_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) :
    ∃ ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
          (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) 0
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν ∧
      ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) 0 (mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f)) := by
  obtain ⟨ν, hdlr, hlim⟩ :=
    MassGap.WilsonDLR.tendsto_specState_at_zero
      (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN)
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) 1
  refine ⟨ν, hdlr, fun f => ?_⟩
  refine Filter.Tendsto.congr (fun n => ?_) ((hlim f).comp (tendsto_mixCube τ p))
  exact (MassGap.WilsonState.stateFree_eq_spec_at_zero_coupling
    MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN) (mixCube τ p n) 1 f).symm

#print axioms wilson_htend_at_zero_coupling

/-- **A DLR state that is a limit of the FREE-boundary family — at every coupling.**

Two unconditional facts compose. `DLRLimit.exists_limit_state` gives a subsequential limit of the
cube family by weak-\* compactness, with no coupling restriction;
`ReflectionHalfSpace.eventually_stateFree_spec_eq` makes the finite-volume states satisfy the DLR
consistency at every interior region for all large boxes, so `DLRLimit.isDLR_of_tendsto` makes the
limit a DLR state.

**Why this is new.** DLR states previously came only from the FIXED-boundary family, through
`GibbsSpec.wilson_dlr_consistent` and `DLRLimit.exists_infinite_volume_gibbs_state`. Reflection
positivity is proved for the FREE-boundary family, which is what the transfer construction consumes.
The only declaration relating the two, `WilsonState.stateFree_eq_spec_at_zero_coupling`, holds at
coupling zero — which is why `wilson_htend_at_zero_coupling` above has no analogue elsewhere. This
gives a DLR state on the free side directly, at every real coupling.

The limit here is along an ultrafilter. At strong coupling it is the full `atTop` limit:
`FreeLimit.exists_tendsto_stateFree` shows the free box states are Cauchy on every observable, so the
ultrafilter limit is their `atTop` limit.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN` and the lower end of
the bound on an observable; `1` is the identity at which the Wilson density vanishes; `2` is the
density's ceiling and the reflection plane's spacing. -/
theorem exists_dlr_limit_of_free_family (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)) :
    ∃ (u : Ultrafilter ℕ) (ν : MassGap.DLRLimit.State
        (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))),
      (u : Filter ℕ) ≤ Filter.atTop
      ∧ (∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
          Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
              MassGap.WilsonAction.measurable_wilsonDensity
              (MassGap.WilsonAction.wilsonDensity_nonneg hN)
              (MassGap.WilsonAction.wilsonDensity_le_two hN) β
              (MassGap.ReflectionHalfSpace.mixCube τ p n) ω f)
            (u : Filter ℕ) (nhds (ν f)))
      ∧ MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
          (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν := by
  obtain ⟨u, ν, hle, htend⟩ := MassGap.DLRLimit.exists_limit_state Filter.atTop
    (fun n => MassGap.ReflectionHalfSpace.stateFree
      MassGap.WilsonAction.measurable_wilsonDensity
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β
      (MassGap.ReflectionHalfSpace.mixCube τ p n) ω)
  refine ⟨u, ν, hle, htend, ?_⟩
  refine MassGap.DLRLimit.isDLR_of_tendsto _ ν htend ?_
  intro V f
  obtain ⟨C₀, hC₀⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  have hC₀0 : (0 : ℝ) ≤ C₀ :=
    le_trans (abs_nonneg (f (fun _ => (1 : MassGap.SUN.SU N)))) (hC₀ _)
  refine Filter.Eventually.filter_mono hle ?_
  exact MassGap.ReflectionHalfSpace.eventually_stateFree_spec_eq
    MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN)
    (MassGap.WilsonAction.wilsonDensity_one hN) β τ p V ω f _
    (fun ω' => MassGap.WilsonDLR.specCM_apply _ _ _ β _ V f ω') hC₀0 hC₀

#print axioms exists_dlr_limit_of_free_family

/-- **Uniqueness of the DLR state gives convergence of the free family along `atTop`.**

`DLRLimit.tendsto_of_unique_dlr` upgrades an ultrafilter limit to convergence along the filter
itself, given the finite-volume consistency and uniqueness. **Before the free-boundary consistency
existed this could not be applied to the free family at all** — it takes that consistency as a
hypothesis, and only the fixed-boundary family had one. It now applies, so uniqueness alone gives
convergence along `atTop`.

**Why that is the whole of the remaining input.** `ReflectionHalfSpace.tendsto_symCube_even_of_mixCube`
and its odd counterpart extract the two cube families from convergence of the interleaved family
along `atTop`, and `wilson_positiveTransfer_of_common_subsequential_limit` then produces
`PositiveTransfer` together with the reflection invariance and translation invariance the transfer
data needs. So uniqueness feeds the whole of that chain.

⚠ AND THE INTERLEAVING DOES NOT AVOID UNIQUENESS, which is worth stating because it looks as though
it might. A single ultrafilter limit of the interleaved family gives only ONE of the two
subsequences: an ultrafilter contains the evens or the odds, not both, so the comap along the other
is the trivial filter. Convergence along `atTop` is what yields both, and that is what uniqueness
buys.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`; `1` is the
all-identity boundary configuration and the identity at which the Wilson density vanishes; `2` is the
density's ceiling. -/
theorem tendsto_free_family_of_unique_dlr (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β : ℝ)
    (ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N))
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (huniq : ∀ ν' : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
        (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β
        (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν' → ν' = ν) :
    ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
      Filter.Tendsto (fun n => MassGap.ReflectionHalfSpace.stateFree
          MassGap.WilsonAction.measurable_wilsonDensity
          (MassGap.WilsonAction.wilsonDensity_nonneg hN)
          (MassGap.WilsonAction.wilsonDensity_le_two hN) β
          (MassGap.ReflectionHalfSpace.mixCube τ p n) ω f)
        Filter.atTop (nhds (ν f)) := by
  refine MassGap.DLRLimit.tendsto_of_unique_dlr _ ν ?_ huniq
  intro V f
  obtain ⟨C₀, hC₀⟩ := MassGap.InfiniteLattice.bounded_of_continuous f.continuous
  have hC₀0 : (0 : ℝ) ≤ C₀ :=
    le_trans (abs_nonneg (f (fun _ => (1 : MassGap.SUN.SU N)))) (hC₀ _)
  exact MassGap.ReflectionHalfSpace.eventually_stateFree_spec_eq
    MassGap.WilsonAction.measurable_wilsonDensity
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN)
    (MassGap.WilsonAction.wilsonDensity_one hN) β τ p V ω f _
    (fun ω' => MassGap.WilsonDLR.specCM_apply _ _ _ β _ V f ω') hC₀0 hC₀

#print axioms tendsto_free_family_of_unique_dlr

/-- **Uniqueness of the DLR state and the gap hypothesis give the Clay spectral statement.**

The composite, with both remaining inputs in one signature. `tendsto_free_family_of_unique_dlr`
turns `huniq` into convergence of the free-boundary family along `atTop`, which is exactly what
`wilson_clay_gap_of_gapAt` consumes; `hg` is the gap hypothesis itself.

**What this makes visible.** Everything else on the route is proved. The reflection invariance,
translation invariance and `PositiveTransfer` that the transfer data needs all follow from that
convergence, through `ReflectionHalfSpace.tendsto_symCube_even_of_mixCube`, its odd counterpart and
`wilson_positiveTransfer_of_common_subsequential_limit`. The free-boundary DLR consistency that makes
`tendsto_of_unique_dlr` applicable at all is `ReflectionHalfSpace.eventually_stateFree_spec_eq`.

**The two inputs, plainly.** `huniq` is uniqueness of the DLR state — `WilsonDLR.dlr_unique_at_zero_eq`
supplies it at coupling zero and nothing supplies it above, no Dobrushin-style machinery exists here,
and it is what fails at a phase transition. `DLRLimit.dlr_eq_of_kernel_near_const` reduces it to an
estimate: that the kernel becomes uniformly constant in its boundary condition as the region grows.
`hg` is `TransferGap.GapAt`, which is the mass gap's quantitative content and which the
strong-coupling side would supply.

Neither is proved here, and the composite does not make them smaller — it makes them exact.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`, the lower end of
`hβ` and `hr`, and the bottom of the spectrum; `1` is the all-identity boundary configuration, the
vacuum eigenvalue and the contraction threshold; `2` is the reflection plane's spacing. -/
theorem wilson_clay_gap_of_unique_dlr (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (huniq : ∀ ν' : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)),
      MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
        (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
        (MassGap.WilsonAction.wilsonDensity_nonneg hN)
        (MassGap.WilsonAction.wilsonDensity_le_two hN) β
        (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν' → ν' = ν)
    {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hg : MassGap.TransferGap.GapAt (wilsonMixCubeData τ p hN β ν
      (tendsto_free_family_of_unique_dlr τ p hN β 1 ν huniq)) r) :
    IsSelfAdjoint (opT (wilsonMixCubeData τ p hN β ν
        (tendsto_free_family_of_unique_dlr τ p hN β 1 ν huniq)))
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν
          (tendsto_free_family_of_unique_dlr τ p hN β 1 ν huniq)))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν
          (tendsto_free_family_of_unique_dlr τ p hN β 1 ν huniq)))) 1 :=
  wilson_clay_gap_of_gapAt τ p hN hβ ν
    (tendsto_free_family_of_unique_dlr τ p hN β 1 ν huniq) hr h1 hg

#print axioms wilson_clay_gap_of_unique_dlr

/-- **Clay from a boundary-decay estimate on the Wilson kernel — no uniqueness hypothesis.**

`DLRLimit.unique_dlr_of_local_kernel_near_const` discharges uniqueness from `hnear`, so no
uniqueness hypothesis appears. What remains is `hnear`, the gap hypothesis `hg`, and the state `ν`
with its DLR property `hdlr` — and those last two are never an obstruction, because
`exists_dlr_limit_of_free_family` produces them at every coupling with no hypothesis at all. They
stay in the signature rather than being existentially bound only because `hg` mentions `ν`.

**What `hnear` says.** For each observable LOCAL on a finite link set, and each `ε > 0`, there is a
region whose kernel is uniformly within `ε` of a constant: the boundary condition stops being
readable off the kernel as the region grows. `WilsonDLR.specCM_apply` rewrites it to
`GibbsSpec.spec`, which is the finite-volume Wilson expectation with the boundary held fixed outside,
so the estimate is a statement purely about the lattice measure, with no states, limits or filters in
it.

⚠ Local, not arbitrary, and that is the correct strength rather than a convenience. A cluster
expansion shows a FIXED local observable stops reading the boundary once the region covers its
support; it does not give a bound uniform over all continuous observables. Passing from the local
ones to all of them is Stone–Weierstrass, already done in `DLRLimit.State.eq_of_eqOn_localObs`.

**This is the genuinely open mathematics.** Nothing in the tree supplies `hnear` at any positive
coupling. `WilsonDLR.local_kernel_near_const_at_zero` supplies it at coupling zero — there the kernel
of a local observable is literally constant in the boundary — so the hypotheses are known to be
jointly satisfiable, and `WilsonDLR.dlr_unique_at_zero_eq` is the corresponding uniqueness. It is
exactly what fails at a phase transition, so no argument that ignores the coupling can give it.
Strong coupling is where it would come from.

**And the other input is `hg`.** `TransferGap.GapAt` is the mass gap's quantitative content, and the
strong-coupling side of this development — `StrongCoupling.wilsonCorrConnF_abs_le_coreConstF_mul_rate_pow`
through `GaugeInvariantAlgebra.gaugeInv_form_pow` — is what would produce it. Two estimates at small
coupling, then, and nothing else that is not already supplied.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`, the lower end of
`hβ`, `hr` and `ε`, and the bottom of the spectrum; `1` is the all-identity boundary configuration,
the vacuum eigenvalue and the contraction threshold; `2` is the Wilson density's ceiling. -/
theorem wilson_clay_gap_of_kernel_near_const (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hdlr : MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
      (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν)
    (hnear : ∀ F ∈ MassGap.DLRLimit.localObsAlg (MassGap.SUN.SU N), ∀ ε : ℝ, 0 < ε →
      ∃ (V : Finset MassGap.GibbsSpec.ILink) (c : ℝ),
        ∀ ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
          |MassGap.WilsonDLR.specCM
              (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
              (MassGap.WilsonAction.wilsonDensity_nonneg hN)
              (MassGap.WilsonAction.wilsonDensity_le_two hN) β
              (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) V F ω - c| ≤ ε)
    {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hg : MassGap.TransferGap.GapAt (wilsonMixCubeData τ p hN β ν
      (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
        (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))) r) :
    IsSelfAdjoint (opT (wilsonMixCubeData τ p hN β ν
        (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν
          (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
            (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonMixCubeData τ p hN β ν
          (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
            (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))) 1 :=
  wilson_clay_gap_of_unique_dlr τ p hN hβ ν
    (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr) hr h1 hg

#print axioms wilson_clay_gap_of_kernel_near_const

/-- **The same two estimates give the gap on the GAUGE-INVARIANT algebra.**

`wilson_clay_gap_of_kernel_near_const` states the spectral conclusion on the full half-space algebra.
This states it on `GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg`, the observables invariant under a
local gauge transformation — which is the algebra the physical Hilbert space is built from, so this
is the form the mass-gap statement should be read in. The hypotheses are identical: the same local
boundary-decay estimate `hnear`, and a gap hypothesis `hg`, here on the gauge-invariant data.

`GaugeInvariantAlgebra.positiveTransfer_gaugeInv` is what carries `PositiveTransfer` across, so
nothing beyond `wilson_positiveTransfer_of_mixCube_limit` is needed on that side.

⚠ `hg` is NOT the same hypothesis as the one in `wilson_clay_gap_of_kernel_near_const` — it is
`GapAt` at the gauge-invariant data, a different transfer operator on a smaller space. Neither
version implies the other here, and nothing in the tree produces either.

DERIVED: `4` is the spacetime dimension; `0` is the excluded gauge rank in `hN`, the lower end of
`hβ`, `hr` and `ε`, and the bottom of the spectrum; `1` is the all-identity boundary configuration,
the vacuum eigenvalue and the contraction threshold; `2` is the doubling in the reflection plane and
the Wilson density's ceiling. -/
theorem wilson_gaugeInv_clay_gap_of_kernel_near_const (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β : ℝ}
    (hβ : 0 ≤ β)
    (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
    (hdlr : MassGap.DLRLimit.IsDLR (MassGap.WilsonDLR.specCM
      (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
      (MassGap.WilsonAction.wilsonDensity_nonneg hN)
      (MassGap.WilsonAction.wilsonDensity_le_two hN) β
      (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N))) ν)
    (hnear : ∀ F ∈ MassGap.DLRLimit.localObsAlg (MassGap.SUN.SU N), ∀ ε : ℝ, 0 < ε →
      ∃ (V : Finset MassGap.GibbsSpec.ILink) (c : ℝ),
        ∀ ω : MassGap.GibbsSpec.IConf (MassGap.SUN.SU N),
          |MassGap.WilsonDLR.specCM
              (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
              (MassGap.WilsonAction.wilsonDensity_nonneg hN)
              (MassGap.WilsonAction.wilsonDensity_le_two hN) β
              (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) V F ω - c| ≤ ε)
    {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hg : MassGap.TransferGap.GapAt (wilsonGaugeInvMixCubeData τ p hN β ν
        (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))) r) :
    IsSelfAdjoint (opT (wilsonGaugeInvMixCubeData τ p hN β ν
        (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))
      ∧ 0 < -Real.log r
      ∧ spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν
        (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))
          ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
      ∧ IsGreatest (spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN β ν
        (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))) 1 :=
  gaugeInv_clay_gap_of_gapAt τ p ν
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN β ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))
    (wilson_reflPositive_even_of_tendsto τ p hN β 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN β ν (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))
    (wilson_nu_T_of_tendsto τ p hN β ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN β ν (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr)))
      (tendsto_symCube_odd_of_mixCube τ p hN β ν (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))))
    (wilson_positiveTransfer_of_mixCube_limit τ p hN hβ ν (tendsto_free_family_of_unique_dlr τ p hN β 1 ν
          (MassGap.DLRLimit.unique_dlr_of_local_kernel_near_const hnear hdlr))) hr h1 hg

#print axioms wilson_gaugeInv_clay_gap_of_kernel_near_const

/-- **The chain closed at zero coupling, with no open input.**

Every hypothesis of `wilson_clay_gap_of_gapAt` is discharged here:

```
  wilson_htend_at_zero_coupling → wilson_positiveTransfer_of_mixCube_limit   PositiveTransfer
                               → WilsonState.gapAt_zero_at_zero_coupling     GapAt … 0
                               → TransferGap.gapAt_mono                      GapAt … r
                               → wilson_clay_gap_of_gapAt                    the gap
```

**What it is for is non-vacuity.** `clay_gap_of_gapAt` and its Wilson instance take hypotheses that
nothing in the tree had ever produced together, and a capstone whose hypotheses are jointly
unsatisfiable proves nothing. This exhibits a case where all of them hold at once.

**What it is not.** `β = 0` is the free theory: the connected pairing vanishes identically, which is
why `gapAt_zero_at_zero_coupling` gives rate `0`, and why `r` stays universally quantified over
`(0,1)` here — the gap is unbounded and no constant is chosen. This says nothing about any positive
coupling.

DERIVED: `4` is the spacetime dimension; `0` is the coupling, the excluded gauge rank in `hN`, the
rate `gapAt_zero_at_zero_coupling` concludes, the bottom of the spectrum, and the lower end of `hr`;
`1` is the vacuum eigenvalue, the contraction constant, and the all-identity boundary; `2` is the
doubling in the reflection plane, the plaquette density's bound, and the Rayleigh exponent. -/
theorem wilson_clay_gap_at_zero_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {r : ℝ} (hr : 0 < r) (h1 : r < 1) :
    ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
      (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) 0 (mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f))),
      IsSelfAdjoint (opT (wilsonMixCubeData τ p hN 0 ν htend))
        ∧ 0 < -Real.log r
        ∧ spectrum ℝ (opT (wilsonMixCubeData τ p hN 0 ν htend))
            ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
        ∧ IsGreatest (spectrum ℝ (opT (wilsonMixCubeData τ p hN 0 ν htend))) 1 := by
  obtain ⟨ν, hdlr, htend⟩ := wilson_htend_at_zero_coupling τ p hN
  refine ⟨ν, htend, wilson_clay_gap_of_gapAt τ p hN le_rfl ν htend hr h1 ?_⟩
  refine MassGap.TransferGap.gapAt_mono (r₁ := 0) (by simpa using sq_nonneg r) ?_
  exact MassGap.WilsonState.gapAt_zero_at_zero_coupling
    (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN)
    (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) hdlr τ p
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN 0 ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend))
    (wilson_reflPositive_even_of_tendsto τ p hN 0 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend))
    (wilson_nu_T_of_tendsto τ p hN 0 ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN 0 ν htend))

#print axioms wilson_clay_gap_at_zero_coupling

/-- **The gauge-invariant statement holds at coupling zero** — the witness that
`wilson_gaugeInv_clay_gap_of_kernel_near_const`'s hypotheses can hold together.

`WilsonState.gapAt_zero_at_zero_coupling` gives rate `0` on the full half-space data at `β = 0`,
`GaugeInvariantAlgebra.gapAt_gaugeInv_of_gapAt` restricts that to the invariant subalgebra — the
quantifier simply runs over fewer observables — and `TransferGap.gapAt_mono` lifts the rate to any
`r`. The thermodynamic limit is `wilson_htend_at_zero_coupling`.

⚠ This is a non-vacuity witness, not a mass gap. At `β = 0` the theory is the product Haar measure:
the rate is `0` because the transfer operator annihilates the vacuum complement outright, and every
`r` in `(0,1)` works because the conclusion is monotone in `r`. What it establishes is that the
hypotheses are jointly satisfiable, which is the one thing a conditional theorem cannot say about
itself. `PowerTail.wilsonCorrAt_at_zero_coupling` makes the zero-coupling read a point mass at lag
zero, so nothing quantitative should be anchored here.

DERIVED: `4` is the spacetime dimension; `0` is the coupling, the excluded gauge rank in `hN`, the
lower ends of `hr` and of the spectrum, and the rate the witness is proved at; `1` is the
all-identity boundary configuration, the vacuum eigenvalue and the contraction threshold; `2` is the
doubling in the reflection plane. -/
theorem wilson_gaugeInv_clay_gap_at_zero_coupling (τ : Fin 4) (p : ℤ) (hN : N ≠ 0)
    {r : ℝ} (hr : 0 < r) (h1 : r < 1) :
    ∃ (ν : MassGap.DLRLimit.State (MassGap.GibbsSpec.IConf (MassGap.SUN.SU N)))
      (htend : ∀ f : C(MassGap.GibbsSpec.IConf (MassGap.SUN.SU N), ℝ),
        Filter.Tendsto (fun n => stateFree (φ := MassGap.WilsonAction.wilsonDensity)
            MassGap.WilsonAction.measurable_wilsonDensity
            (MassGap.WilsonAction.wilsonDensity_nonneg hN)
            (MassGap.WilsonAction.wilsonDensity_le_two hN) 0 (mixCube τ p n) 1 f)
          Filter.atTop (nhds (ν f))),
      IsSelfAdjoint (opT (wilsonGaugeInvMixCubeData τ p hN 0 ν htend))
        ∧ 0 < -Real.log r
        ∧ spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN 0 ν htend))
            ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(-Real.log r)))
        ∧ IsGreatest (spectrum ℝ (opT (wilsonGaugeInvMixCubeData τ p hN 0 ν htend))) 1 := by
  obtain ⟨ν, hdlr, htend⟩ := wilson_htend_at_zero_coupling τ p hN
  refine ⟨ν, htend, wilson_gaugeInv_clay_gap_of_gapAt τ p hN le_rfl ν htend hr h1 ?_⟩
  refine MassGap.TransferGap.gapAt_mono (r₁ := 0) (by simpa using sq_nonneg r) ?_
  refine MassGap.GaugeInvariantAlgebra.gapAt_gaugeInv_of_gapAt τ p ν _ _ _ ?_
  exact MassGap.WilsonState.gapAt_zero_at_zero_coupling
    (MassGap.WilsonAction.continuous_wilsonDensity (N := N))
    (MassGap.WilsonAction.wilsonDensity_nonneg hN)
    (MassGap.WilsonAction.wilsonDensity_le_two hN)
    (MassGap.CompactGauge.probHaar (MassGap.SUN.SU N)) hdlr τ p
    (wilson_reflInvariant_of_tendsto τ (2 * p) hN 0 ν Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend))
    (wilson_reflPositive_even_of_tendsto τ p hN 0 1 ν Filter.atTop le_rfl
      (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend))
    (wilson_nu_T_of_tendsto τ p hN 0 ν Filter.atTop Filter.atTop
      (tendsto_symCube_even_of_mixCube τ p hN 0 ν htend)
      (tendsto_symCube_odd_of_mixCube τ p hN 0 ν htend))

#print axioms wilson_gaugeInv_clay_gap_at_zero_coupling

end Wilson

end MassGap.ClayCapstone
