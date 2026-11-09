import Mathlib
import MassGap.GNSCompare
import MassGap.WilsonState
import MassGap.GaugeInvariantAlgebra

/-!
# MassGap.ClayCapstone — what the transfer chain delivers, and on which algebra

This module imports `GNSCompare` (the chain from reflection positivity to the transfer spectrum) and
`WilsonState`, and states what they give.

## The routes

* `clay_gap_of_gapAt` — from `TransferGap.GapAt`, the gap predicate the rest of the tree produces.
  It needs no Rayleigh statement and no subdominant supremum.
* `gaugeInv_clay_gap_of_gapAt` and `gaugeInv_clay_gap_of_pairing` — the same on the
  **gauge-invariant** algebra, where reflection positivity and `PositiveTransfer` restrict for free
  and a pairing inequality is the only input.

## Which algebra, and why it matters

`WilsonTransferReduction.transferData_of_state_facts` builds on `HalfSpaceAlgebra.halfSpaceAlg`, a
locality predicate containing `halfLinkObs l f` — an arbitrary continuous function of a single link
variable. A gap bound there must hold for observables that are not gauge invariant, while
`StrongCoupling.wilsonCorrConn_abs_le_coreConst_mul_rate_pow` bounds a plaquette pair. The two do not
meet. `GaugeInvariantAlgebra` supplies the smaller algebra where they do.

The route uses `GNSCompare.inner_Tq_nonneg_of_positiveTransfer`, `GapToOperator.spectrum_opT_subset`,
`GNSHilbert.spectrum_opT_nonneg` and `GNSHilbert.isGreatest_one_spectrum_opT`.

## Why there is no `ε`

Clay asks for `spectrum ℝ H ⊆ {0} ∪ Set.Ici Δ` at some `Δ > 0`. Through `T = exp (-H)` that reads
`spectrum ℝ T ⊆ {1} ∪ Set.Icc 0 (Real.exp (-Δ))`, with `0` **admitted**: a theory whose energies are
unbounded has a transfer spectrum accumulating at zero. Requiring `Set.Icc ε (Real.exp (-Δ))` with
`0 < ε` instead would make it a ceiling on the energies and `IsUnit T`, which a compact `T` on an
infinite-dimensional space meets at no `ε`.

## Scope

This is the spectral containment for the transfer operator. Reading it as a statement about a
Hamiltonian needs an unbounded functional calculus, which is not built here. The gap hypothesis is
the mass gap's quantitative content: nothing here produces a `GapAt`.
-/

namespace MassGap.ClayCapstone

open MassGap MassGap.Transfer MassGap.GNSHilbert MassGap.GNSCompare

/-- **The gap from `GapAt` directly, at one coupling.**

`TransferGap.GapAt D r` is the tree's own gap predicate, and `GapToOperator.spectrum_opT_subset`
already carries it to `spectrum ℝ (opT D) ⊆ {1} ∪ Set.Icc (-r) r`. With
`GNSHilbert.spectrum_opT_nonneg` cutting the bottom, that is the Clay containment. No Rayleigh
ceiling is needed as a separate hypothesis — `GapAt` is the same content in the form the rest of the
tree produces.

It needs no coupling interval: the gap at one coupling is what a lattice mass gap asks for.

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

/-- **A transfer operator's Rayleigh set is always bounded above.**

`Transfer.TransferData.Tq_norm_le` makes `Tq` a norm-contraction, from the `T_contract` field, so
`SecondEigenvalue.bddAbove_rayleighSet_of_norm_le` applies at every `V`.

The bound holds for any transfer data and any submodule.

DERIVED: no numeral occurs; `V` is the caller's. -/
theorem bddAbove_rayleighSet_Tq {A : Type*} [AddCommGroup A] [Module ℝ A]
    (D : TransferData A) (V : Submodule ℝ (GNS D.toReflForm)) :
    BddAbove (MassGap.SecondEigenvalue.rayleighSet D.Tq V) :=
  MassGap.SecondEigenvalue.bddAbove_rayleighSet_of_norm_le D.Tq V
    (MassGap.Transfer.TransferData.Tq_norm_le D)

#print axioms bddAbove_rayleighSet_Tq

/-- **The GNS norm of an iterate is the reflection form at the iterated representative.**

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
becomes the per-vector decay `‖Tqⁿ [x]‖ ≤ K' · rⁿ`.

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

/-! ### The coupling-indexed subdominant ratio -/

/-- **`ρ₁`, defined.** The subdominant Rayleigh supremum of a coupling-indexed family of transfer
data, as a function `ℝ → ℝ` of the coupling.

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

end MassGap.ClayCapstone
