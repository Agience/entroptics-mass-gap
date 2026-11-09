import Mathlib
import MassGap.ObserverOSTempered
import MassGap.ContinuumTimeGroup

noncomputable section

/-!
# MassGap.ObserverOSReconstructionS — Schwartz-indexed Euclidean data and the observer's reconstruction

The Schwartz space `𝓢(E4, ℝ)` is not normable, so the observer's Schwinger functions on it
(`ObserverOSTempered.schwCML`) are stated as continuous multilinear maps, with OS0 as continuity.

## What the tree's reconstruction consumes

The reconstruction that the tree builds for a flow (`ContinuumFlow.flow_reconstruction`,
`ContinuumTimeGroup`) is a GNS construction on finite real combinations of margin monomials,
`MarginMono N τ r →₀ ℝ`, a space with no topology. Its inputs are the reflection kernel
`kernF P Q = contSF (pairFam τ P Q)`:

* symmetric (`kernF_symm`) and with non-negative reflected Gram sums (`contSF_gram_nonneg`, OS2);
* covariant under the dyadic time shifts (`kernF_shift`) and bounded under their iterates
  (`kernF_iterate_bound`, from `UniformBoundF`);
* normalised, `S(∅) = 1` (`kernF_empty`).

From these, `GNSHilbert` completes the quotient; the transfer `stepT m` is the shift, `timeT` the
continuous time translations (`ContinuumTimeGroup.flow_time_group`), and the gap comes from (M)
(`flowN_time_group_of_gap`). No lemma of this chain takes a norm, a seminorm or a topology on
the test functions. OS0 in any form, sup norm, weighted sup norm or Schwartz topology, enters
nowhere in the construction of the Hilbert space, the semigroup or the gap; it is a property of the
Schwinger functions that the reconstruction does not read.

## `OSDataS`

`OSDataS` is the Schwartz-indexed variant: Schwinger functions `S n` as continuous multilinear
functionals on `𝓢(E4, ℝ)ⁿ` (OS0 as continuity), with the linear-growth bound in the seminorm
gauge `8192 · e4Norm 5`, permutation symmetry (OS3), and the reconstructed side as data: a complex
Hilbert space, a vacuum, a strongly continuous semigroup of positive self-adjoint contractions fixing
the vacuum and contracting its complement at a rate `gap > 0`, and a non-zero vector orthogonal to the
vacuum.

## The observer inhabits it

`observerOSDataS`: from (E) in its cube form on the class `D` (`CubeMomentBound`, which gives the
uniform bound), one exponential moment of the unit cube for the field `O` (`UnitCubeExpBound`), a
physical-range bound, (M) as the gap of the transfer at one step, and (N), the energy density gives an
`OSDataS`: `S n = schwCML n`, the semigroup and gap from
`ContinuumTimeGroup.flowN_time_group_of_gap`. `observerOSDataS_link` ties the two halves to one
functional, the observer's limit Schwinger function `contSF`: the reconstructed inner products are
`⟪gvecT P, gvecT Q⟫ = contSF (pairFam τ P Q)`, and `S n φ = contSF (O, f)` when `φᵢ ∘ toLp` is the
test function `fᵢ`.

The already-proved axioms of the observer theory stay at the level of `contSF` on test functions:
OS1 for real translations and axis reflections, OS2 and OS3 in `ObserverOS.observer_os`, `SO(4)` from
the `pyth` hypothesis in `ObserverRotationDense.observerSO4_energy0`. Their transport to `S n` on the
Schwartz class is not proved here; `os3` is (`schwSF_comp_perm`).
-/

namespace MassGap.ObserverOSReconstructionS

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverOS MassGap.ObserverOSGrowth MassGap.ObserverOSSchwartz
  MassGap.ObserverOSTempered MassGap.ContinuumTimeGroup MassGap.ObserverEnergyBox Filter
open scoped Topology

/-! ## 1. The structure -/

/-- **Schwartz-indexed Euclidean data with their reconstruction.** OS0 as continuity of each `S n` on
`𝓢(E4, ℝ)ⁿ` together with the linear-growth bound in the gauge `8192 · e4Norm 5`; OS3 as permutation
symmetry; and the reconstructed quantum side: a complex Hilbert space with a vacuum and the
continuous time translations, positive self-adjoint contractions fixing the vacuum and contracting
its complement at the rate `gap > 0`, with a non-zero vector orthogonal to the vacuum.

DERIVED: `8192`, `5` are `ObserverOSTempered.abs_schwCML_le`'s gauge; `2` the square of the
factorial; `0` the time origin, the sign of `gap` and `t`, the vanishing pairing; `1` the identity and
the norm bound; `4` in `E4` is the spacetime dimension. -/
structure OSDataS where
  /-- The Schwinger functions, continuous multilinear on Euclidean Schwartz functions (OS0). -/
  S : (n : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin n => MassGap.WightmanData.TestFn) ℝ
  /-- The growth constants. -/
  α : ℝ
  /-- The growth rate. -/
  γ : ℝ
  /-- **OS0, linear growth**: `|S_n(φ)| ≤ α γⁿ (n!)² ∏ᵢ 8192 e4Norm 5 (φᵢ)`. -/
  growth : ∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
    |S n φ| ≤ α * γ ^ n * (n.factorial : ℝ) ^ 2 * ∏ i, 8192 * e4Norm 5 (φ i)
  /-- **OS3**: symmetry under permutations of the arguments. -/
  os3 : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (φ : Fin n → MassGap.WightmanData.TestFn),
    S n (φ ∘ σ) = S n φ
  /-- The reconstructed Hilbert space. -/
  H : Type
  [nH : NormedAddCommGroup H]
  [iH : InnerProductSpace ℂ H]
  [cH : CompleteSpace H]
  /-- The vacuum. -/
  vac : H
  /-- The time translations. -/
  time : ℝ → H →L[ℂ] H
  /-- The mass gap. -/
  gap : ℝ
  gap_pos : 0 < gap
  time_zero : time 0 = 1
  time_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → time (s + t) = time s * time t
  time_selfAdjoint : ∀ t : ℝ, 0 ≤ t → IsSelfAdjoint (time t) ∧ ‖time t‖ ≤ 1
  time_cont : ∀ y : H, ContinuousOn (fun t => time t y) (Set.Ici 0)
  time_vac : ∀ t : ℝ, 0 ≤ t → time t vac = vac
  /-- **The gap**: the complement of the vacuum is contracted at the rate `gap`. -/
  time_gap : ∀ t : ℝ, 0 ≤ t → ∀ u : H, inner ℂ vac u = 0 →
    ‖time t u‖ ≤ Real.exp (-(gap * t)) * ‖u‖
  /-- **Non-triviality**: a non-zero vector orthogonal to the vacuum. -/
  nontrivial : ∃ u : H, inner ℂ vac u = 0 ∧ u ≠ 0

/-! ## 2. OS3 on the Schwartz class -/

section Perm

variable {N : ℕ}

/-- **`schwSF` is symmetric under permutations**: each truncated family is a permutation of the
other (`ContinuumFlow.contSF_comp_equiv`), with no hypothesis.

DERIVED: no numeral. -/
theorem schwSF_comp_perm (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (O : LField (MassGap.SUN.SU N)) {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : Fin n → Decaying) :
    schwSF hN W D hD O (g ∘ σ) = schwSF hN W D hD O g := by
  unfold schwSF
  congr 1
  funext R
  exact contSF_comp_equiv hN (energy0 W D hD) σ (fun i => (O, trunc (g i) R))

#print axioms schwSF_comp_perm

end Perm

/-! ## 3. The observer's data -/

section Observer

variable {N : ℕ}

/-- **The observer's Schwartz-indexed Euclidean data.** Inputs: (E) on the class `D`
(`CubeMomentBound`), one exponential moment of the unit cube for the field `O`, a physical range
`r` for `energy0`, (M) as the gap of the transfer at one step `m0` at the rate `ρ < 1`, and (N). The
Schwinger functions are `schwCML`, the constants from `abs_schwCML_le`; the Hilbert space, vacuum and
time translations are those of the energy density's flowed reconstruction in the direction `τ`, the
gap the rate of `ContinuumTimeGroup.flowN_time_group_of_gap`.

DERIVED: `0` is the excluded colour count, the sign of `L`, `ρ`, the reference step and the time
origin; `1` the top of `ρ`; `4` in `Fin 4` the spacetime dimension. -/
def observerOSDataS (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) : OSDataS :=
  let hB := uniformBoundF_energy0 hN W D hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ
  let hT := flowN_time_group_of_gap hN (energy0 W D hD) hB τ hphys m0 hL hρ0 hρ1 hg hNT
  let hgr := abs_schwCML_le hN W hD hpos hO h
  let μ := Classical.choose hT
  have hμ := Classical.choose_spec hT
  { S := schwCML hN W hD hpos hO h
    α := Classical.choose hgr
    γ := Classical.choose (Classical.choose_spec hgr)
    growth := Classical.choose_spec (Classical.choose_spec hgr)
    os3 := fun n σ φ => by
      show schwSF hN W D hD O (fun i => ofE4 ((φ ∘ σ) i)) = schwSF hN W D hD O (fun i => ofE4 (φ i))
      exact schwSF_comp_perm hN W D hD O σ (fun i => ofE4 (φ i))
    H := FlowH hN (energy0 W D hD) hB τ hpp
    vac := vacT hN (energy0 W D hD) hB τ hpp
    time := timeT hN (energy0 W D hD) hB τ hpp
    gap := μ
    gap_pos := hμ.1
    time_zero := hμ.2.1.1
    time_add := hμ.2.1.2.1
    time_selfAdjoint := fun t ht => ⟨(hμ.2.1.2.2.2.1 t ht).2.1, (hμ.2.1.2.2.2.1 t ht).2.2⟩
    time_cont := hμ.2.1.2.2.2.2.1
    time_vac := hμ.2.1.2.2.2.2.2.1
    time_gap := hμ.2.1.2.2.2.2.2.2.1
    nontrivial := by
      obtain ⟨u, hu0, hu, _⟩ := hμ.2.2
      exact ⟨u, hu0, hu⟩ }

/-- **The two halves read one functional.** For the observer's data: the reconstructed inner
products of margin monomials are the observer's limit Schwinger functions of the reflected pairs,
`⟪gvecT P, gvecT Q⟫ = contSF (pairFam τ P Q)` (`ContinuumFlow.flow_reconstruction`), and the Schwartz
Schwinger functions on Euclidean data that are test functions are the same limit,
`S n φ = contSF (O, f)` (`ObserverOSTempered.schwCML_eq_contSF`).

DERIVED: `0` is the excluded colour count and the reference step; `2` the Euclidean exponent; `4` in
`Fin 4` the spacetime dimension. -/
theorem observerOSDataS_link (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) :
    (∀ P Q : MarginMono N τ r,
      inner ℂ (gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
          (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) P)
        (gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
          (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) Q)
      = (contSF hN (energy0 W D hD) (pairFam τ P.1 Q.1) : ℂ))
    ∧ (∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn) (f : Fin n → TestFn),
        (∀ i, (fun y => φ i (WithLp.toLp 2 y)) = (f i).1) →
        (observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT).S n φ
          = contSF hN (energy0 W D hD) (fun i => (O, f i))) :=
  ⟨fun P Q => (flow_reconstruction hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube)
      τ (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ) 0).2 P Q,
    fun n φ f hφf => schwCML_eq_contSF hN W hD hpos hO h φ f hφf⟩

#print axioms observerOSDataS_link

/-- **The observer's data carry a gap**: `observerOSDataS` has `gap > 0`, the semigroup contracts the
vacuum complement at that rate, and a non-zero vector is orthogonal to the vacuum; its Schwinger
functions satisfy the linear-growth bound in the Schwartz gauge.

DERIVED: `0` the sign of the gap and of `t`, the vanishing pairing; `2` the square of the factorial;
`8192`, `5` the gauge; `4` in `Fin 4` the spacetime dimension. -/
theorem observerOSDataS_gap (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) :
    let X := observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT
    0 < X.gap ∧ (∀ (n : ℕ) (φ : Fin n → MassGap.WightmanData.TestFn),
      |X.S n φ| ≤ X.α * X.γ ^ n * (n.factorial : ℝ) ^ 2 * ∏ i, 8192 * e4Norm 5 (φ i)) :=
  ⟨(observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT).gap_pos,
    (observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT).growth⟩

#print axioms observerOSDataS_gap

end Observer

end MassGap.ObserverOSReconstructionS
