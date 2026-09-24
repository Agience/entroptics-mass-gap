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
bounded and below one. Nothing in this tree does that, and the measured grid under `research/data`
is a failure to refute it rather than a proof of it.

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

What is still open is `hdec`. `StrongCoupling` bounds connected correlators at growing separation,
which is the same physical content, but no declaration identifies
`D.form ((D.T ^ n) x) ((D.T ^ n) x)` with any correlator it bounds.

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

end Wilson

end MassGap.ClayCapstone
