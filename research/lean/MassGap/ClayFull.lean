import Mathlib
import MassGap.ObserverOSLinked
import MassGap.ObserverSymField
import MassGap.ClassHamiltonian
import MassGap.ContinuumNontrivial
import MassGap.ApertureVolume

/-!
# MassGap.ClayFull — the Clay Yang–Mills statement as one Prop, and what the tree proves of it

Jaffe–Witten: for a compact simple gauge group `G`, a quantum Yang–Mills theory on `ℝ⁴` exists,
satisfying axiomatic properties at least as strong as the Wightman or the Osterwalder–Schrader
axioms, and it has a mass gap `Δ > 0`. `ClayFull` is that statement in the Osterwalder–Schrader form,
for `G = SU(N)`, `N ≥ 2`, the only gauge groups of the tree's lattice.

## The Prop

`ClayFullAt hN W D hD` is about one lattice construction: the periodic Wilson states of `SU(N)` along
the dyadic tower `dyBeta`, read through a configuration flow `W` on the field class `D`. It asks for
`X : ObserverOSLinked.OSDataSLinked N D τ r` (the Schwinger functions as continuous multilinear maps
on `𝓢(ℝ⁴)ⁿ`, their reconstructed Hilbert space, a strongly continuous semigroup of positive
self-adjoint contractions with a gap, and the link between the two) such that

1. **lattice Yang–Mills**: `X.SM` is the observer's limit Schwinger functional
   `ObserverOSEuclidS.schwSFM hN W D hD`, and `X.O ∈ D` is a hypercubic scalar;
2. **OS0** (tempered, with the linear growth condition), **OS3**, reconstruction, vacuum invariance
   and a vector orthogonal to the vacuum: the fields of `OSDataS`, carried by the type;
3. **OS1**: invariance of `X.SM` under every real translation (`TranslationInv`);
4. **O(4)**: invariance under `SO(4)` (`RotationInv`) and under every axis reflection
   (`ReflectionInv`) at the hypercubic scalars of `D`; the two generate `O(4)`;
5. **OS2**: reflection positivity of `X.SM` on margin monomials of decaying functions beyond the
   reach `r` (`OS2`) and at margin `0` (`OS2Zero`);
5'. **the reconstruction is the one of `X.SM`** (`Reconstructs`): the vacuum is the empty
   monomial's vector, the dyadic shift acts as `X.base.time a_m` on the compact vectors, and these
   are dense. Without it the semigroup and the gap of an `OSDataS` are not tied to its Schwinger
   functions;
6. **the gap as a Hamiltonian** (`HamiltonianGap`): the generator `H` of the time semigroup is
   self-adjoint and positive, `H Ω = 0`, `Δ ‖u‖² ≤ re ⟪u, H u⟫` on the vacuum complement with
   `Δ = X.base.gap > 0`, and every vector fixed by one positive time is on the vacuum line;
7. **non-Gaussian** (`NonGaussian`): a non-zero connected three-point function of `X.O`;
8. **the local composite and asymptotic freedom** (`LocalLink`): a renormalisation `Z` whose
   connected composites, on separated positive-time monomials, are vectors of the same Hilbert
   space with `⟪w P, w Q⟫ = S(θP ∪ Q)` and the dyadic time shifts acting as `X.base.time`, and whose
   lattice two-point kernel of `X.O` converges to `G(|p − q|)` with `ShortDistanceY.AFShortDistance G`.

`ClayFull` is `∀ N ≥ 2, ∃ W D hD, ClayFullAt`.

## Typed forms defined here

The tree has no typed form of clauses 6 (on an `OSDataS`), 7 (on the Schwartz-extended functional)
and 8 (one Hilbert space for flowed and local fields). `HamiltonianGap`, `NonGaussian` and
`LocalLink` are their minimal forms. `HamiltonianGap` uses `ClassHamiltonian.generator`. Tensor
fields (`tr F_{μν} F_{ρσ}`) are not in the statement: the OS axioms are stated for the scalar fields
of `D`, and their `O(4)` covariance is invariance. OS0 (continuity on `𝓢(ℝ⁴)ⁿ` and the growth bound)
is carried by `OSDataS` for the one field `X.O`; the other fields of `D` enter `X.SM` on decaying
functions. `LocalLink` ties the local composite to `X` through the time semigroup and, by density
in `Reconstructs`, through the closure of `X`'s vectors; no cross inner product
`⟪w P, X.cvec Q⟫` is stated, since the tree has no mixed flowed–local reading.

## What is proved

* `schwSFM_reflect`: reflection invariance of `schwSFM` at reflection-invariant fields, from
  `ContinuumFlow.contSF_reflect` cut-off by cut-off (`chi` is reflection invariant). New.
* `observer_generator_isSelfAdjoint`: the generator of the flowed time group `timeT` is self-adjoint
  (`timeT` is `ClassHamiltonian.powSemigroup` of `stepT 0`; `stepT_zero_injective`). New.
* `fixed_eq_smul_vac`, `hamiltonianGap_of_selfAdjoint`: clause 6 for every `OSDataS` whose generator
  is self-adjoint.
* `clayFullAt_of_observer`: clauses 1–6 for the energy density of any axis-covariant `W` on
  `SymPlaqClass N`, from (E) on `PlaqClass N` (`CubeMomentBound`), the class moments, one exponential
  moment of the unit cube, a physical range, (M) at one step, (N), `pyth` invariance; the vacuum
  and time-shift parts of `Reconstructs` are proved (`vacT` is the empty monomial's vector,
  `stepT_gvecT`, `timeT_dyadic`); `OS2Zero`, density, clause 7 and clause 8 are four further inputs. `clayFull_of_observer`: the same for every `N ≥ 2`.

`ApertureVolume.clay_two` concludes `ClayRoutes.ClayContinuumPair` for `Renorm.connected hN zOwn`,
a different field reading of the same Wilson states. It supplies no clause of `ClayFull`: its
Hilbert space is the one of `ContinuumSep.contTransferSep` at `zOwn`, not `X.base.H`. Clause 8 at
`Z = zOwn` is the statement that would carry it in.
-/

noncomputable section

namespace MassGap.ClayFull

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup Filter
open scoped Topology Matrix

/-- DERIVED: no numeral. -/
instance instCompleteSpaceOSDataSH (X : OSDataS) : CompleteSpace X.H := X.cH

variable {N : ℕ}

/-! ## 1. The clauses -/

section Clauses

variable {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}

/-- **The connected three-point function** of the field `X.O` at three decaying functions:
`S₃ − S₂S₁ − S₂S₁ − S₂S₁ + 2 S₁S₁S₁`. It vanishes for every Gaussian law.

DERIVED: `1`, `2`, `3` the orders of the Schwinger functions; `2` the cumulant coefficient. -/
def cum3 (X : OSDataSLinked N D τ r) (g h k : Decaying) : ℝ :=
  X.SM (fun _ : Fin 3 => X.O) ![g, h, k]
    - X.SM (fun _ : Fin 2 => X.O) ![g, h] * X.SM (fun _ : Fin 1 => X.O) ![k]
    - X.SM (fun _ : Fin 2 => X.O) ![g, k] * X.SM (fun _ : Fin 1 => X.O) ![h]
    - X.SM (fun _ : Fin 2 => X.O) ![h, k] * X.SM (fun _ : Fin 1 => X.O) ![g]
    + 2 * X.SM (fun _ : Fin 1 => X.O) ![g] * X.SM (fun _ : Fin 1 => X.O) ![h]
      * X.SM (fun _ : Fin 1 => X.O) ![k]

/-- **Non-Gaussian**: some connected three-point function of `X.O` is non-zero.

DERIVED: `0` the Gaussian value. -/
def NonGaussian (X : OSDataSLinked N D τ r) : Prop :=
  ∃ g h k : Decaying, cum3 X g h k ≠ 0

/-- **OS1**: every real translation of continuous decaying functions, fields in `D`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def TranslationInv (X : OSDataSLinked N D τ r) : Prop :=
  ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)), (∀ i, O i ∈ D) →
    ∀ g : ι → Decaying, (∀ i, Continuous (g i).1) → ∀ v : Fin 4 → ℝ,
      X.SM O (fun i => decTr (g i) v) = X.SM O g

/-- **SO(4)** at the hypercubic scalars of `D`.

DERIVED: `4` the dimension. -/
def RotationInv (X : OSDataSLinked N D τ r) : Prop :=
  ∀ A : Matrix (Fin 4) (Fin 4) ℝ, ∀ hA : A ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ,
    ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)),
      (∀ i, O i ∈ D ∧ HypScalar (O i)) → ∀ g : ι → Decaying, (∀ i, Continuous (g i).1) →
        X.SM O (fun i => decRot (g i) (transpose_mul_self_of_mem hA)) = X.SM O g

/-- **The axis reflections** at the hypercubic scalars of `D`. With `RotationInv`, `O(4)`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def ReflectionInv (X : OSDataSLinked N D τ r) : Prop :=
  ∀ σ : Fin 4, ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)),
    (∀ i, O i ∈ D ∧ HypScalar (O i)) → ∀ g : ι → Decaying,
      X.SM O (fun i => decRefl σ (g i)) = X.SM O g

/-- **OS2** on margin monomials of decaying functions with fields in `D`.

DERIVED: `0` the sign. -/
def OS2 (X : OSDataSLinked N D τ r) : Prop :=
  ∀ s : Finset (DMarginMono N τ r), (∀ P ∈ s, ∀ i, (P.1.2 i).1 ∈ D) →
    ∀ c : DMarginMono N τ r → ℝ,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * X.SM (pairFields τ P.1 Q.1) (pairFuns τ P.1 Q.1)

/-- **OS2 at margin `0`**: reflection positivity of `X.SM` on every positive-time monomial of
decaying functions, not only on those beyond the reach `r` of the flow.

DERIVED: `0` the margin and the sign. -/
def OS2Zero (X : OSDataSLinked N D τ r) : Prop :=
  ∀ s : Finset (DMarginMono N τ 0), (∀ P ∈ s, ∀ i, (P.1.2 i).1 ∈ D) →
    ∀ c : DMarginMono N τ 0 → ℝ,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * X.SM (pairFields τ P.1 Q.1) (pairFuns τ P.1 Q.1)

/-- **The reconstruction is the one of `X.SM`**: the vacuum is the empty monomial's vector, the
dyadic shift of a compact margin monomial acts as `X.base.time a_m`, and the compact vectors are
dense.

DERIVED: `0` the empty monomial's length. -/
def Reconstructs (hN : N ≠ 0) (X : OSDataSLinked N D τ r) : Prop :=
  X.base.vac = X.cvec ⟨emptyMargin N τ r, fun i => i.elim0⟩
    ∧ (∀ (m : ℕ) (Q : MarginMonoD N D τ r),
        X.cvec ⟨MarginMono.shift hN τ m Q.1, fun i => Q.2 i⟩
          = X.base.time (dySpacing N m) (X.cvec Q))
    ∧ Dense (Set.range X.cvec)

end Clauses

/-- **The gap as a Hamiltonian.** The generator `H` of `X.time` is self-adjoint and positive,
annihilates the vacuum, has `X.gap ‖u‖² ≤ re ⟪u, H u⟫` on the vacuum complement, and every vector
fixed at one positive time is on the vacuum line.

DERIVED: `0` the bottom, the zero vector and the vanishing pairing; `2` the square of the norm. -/
def HamiltonianGap (X : OSDataS) : Prop :=
  IsSelfAdjoint (ClassHamiltonian.generator X.time)
    ∧ (∀ u : (ClassHamiltonian.generator X.time).domain,
        0 ≤ (inner ℂ (u : X.H) (ClassHamiltonian.generator X.time u)).re)
    ∧ (∃ h : X.vac ∈ (ClassHamiltonian.generator X.time).domain,
        ClassHamiltonian.generator X.time ⟨X.vac, h⟩ = 0)
    ∧ (∀ u : (ClassHamiltonian.generator X.time).domain, inner ℂ X.vac (u : X.H) = 0 →
        X.gap * ‖(u : X.H)‖ ^ 2 ≤ (inner ℂ (u : X.H) (ClassHamiltonian.generator X.time u)).re)
    ∧ (∀ t : ℝ, 0 < t → ∀ u : X.H, X.time t u = u → ∃ c : ℂ, u = c • X.vac)

/-- **The local composite in the same Hilbert space, at short distance asymptotically free.** A
renormalisation `Z`, vectors `w P` of the separated positive-time monomials of `Renorm.connected Z`
in `X.base.H` with `⟪w P, w Q⟫ = S(θP ∪ Q)` and the dyadic shift acting as `X.base.time a_m`, and the
lattice two-point kernel of `X.O` converging to `G(|p − q|)` with `AFShortDistance G`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def LocalLink (hN : N ≠ 0) {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) : Prop :=
  ∃ (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (G : ℝ → ℝ) (w : ContinuumSep.SepMono N τ → X.base.H),
    (∀ P Q : ContinuumSep.SepMono N τ,
      inner ℂ (w P) (w Q) = (ContinuumSep.kernSep hN (Renorm.connected hN Z) τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : ContinuumSep.SepMono N τ),
        w (ContinuumSep.SepMono.shift hN τ m P) = X.base.time (dySpacing N m) (w P))
    ∧ ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ X.O
        (fun p q => G (ContinuumNontrivial.eDist p q))
    ∧ ShortDistanceY.AFShortDistance G

/-- **The Clay statement at one lattice construction**: `SU(N)` Wilson states along `dyBeta`, the
configuration flow `W`, the field class `D`.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
def ClayFullAt (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) : Prop :=
  ∃ (τ : Fin 4) (r : ℝ) (X : OSDataSLinked N D τ r),
    (∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
        X.SM O g = schwSFM hN W D hD O g)
      ∧ X.O ∈ D ∧ HypScalar X.O
      ∧ TranslationInv X ∧ RotationInv X ∧ ReflectionInv X ∧ OS2 X ∧ OS2Zero X
      ∧ Reconstructs hN X ∧ HamiltonianGap X.base ∧ NonGaussian X ∧ LocalLink hN X

/-- **The Clay Yang–Mills statement for `SU(N)`, every `N ≥ 2`**, in the Osterwalder–Schrader form.

DERIVED: `2` the least colour count with a non-abelian `SU(N)`; `4` in `Fin 4` the dimension. -/
def _root_.MassGap.ClayFull : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D),
    ClayFullAt hN W D hD

/-! ## 2. Reflections on decaying functions -/

/-- **Reflection invariance of `schwSFM`** at reflection-invariant fields: the reflected cut-off is
the cut-off of the reflected function (`chi_reflR`), and `contSF_reflect` holds at each cut-off.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem schwSFM_reflect (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) (σ : Fin 4)
    {ι : Type} [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (hO : ∀ i, (O i).refl σ = O i)
    (g : ι → Decaying) :
    schwSFM hN W D hD O (fun i => decRefl σ (g i)) = schwSFM hN W D hD O g := by
  unfold schwSFM
  congr 1
  funext R
  rw [← contSF_reflect hN (energy0 W D hD) σ (fun i => (O i, cut (g i) R))]
  congr 1
  funext i
  show (O i, cut (decRefl σ (g i)) R) = ((O i).refl σ, (cut (g i) R).reflect σ)
  rw [hO i]
  congr 1
  apply Subtype.ext
  funext y
  show chi R y * (g i).1 (reflR σ y) = chi R (reflR σ y) * (g i).1 (reflR σ y)
  rw [chi_reflR]

#print axioms schwSFM_reflect

/-! ## 3. The Hamiltonian of an `OSDataS` -/

/-- **A vector fixed at one positive time is on the vacuum line.** Its component orthogonal to the
vacuum is fixed and contracted by `e^{−Δ t} < 1`.

DERIVED: `0` the time origin, the vanishing pairing and the zero vector. -/
theorem fixed_eq_smul_vac (X : OSDataS) {t : ℝ} (ht : 0 < t) (u : X.H) (hu : X.time t u = u) :
    ∃ c : ℂ, u = c • X.vac := by
  set c : ℂ := inner ℂ X.vac u / inner ℂ X.vac X.vac with hc
  refine ⟨c, ?_⟩
  set w : X.H := u - c • X.vac with hw
  have hw0 : inner ℂ X.vac w = 0 := by
    by_cases hv : X.vac = 0
    · rw [hv, inner_zero_left]
    · have hvv : inner ℂ X.vac X.vac ≠ (0 : ℂ) := inner_self_ne_zero.mpr hv
      rw [hw, inner_sub_right, inner_smul_right, hc, div_mul_cancel₀ _ hvv, sub_self]
  have hTw : X.time t w = w := by
    rw [hw, map_sub, map_smul, X.time_vac t ht.le, hu]
  have hdec := X.time_gap t ht.le w hw0
  rw [hTw] at hdec
  have he : Real.exp (-(X.gap * t)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos (mul_pos X.gap_pos ht))
  have hn : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
  have hw' : w = 0 := norm_eq_zero.mp hn
  rw [hw] at hw'
  exact sub_eq_zero.mp hw'

#print axioms fixed_eq_smul_vac

/-- **The Hamiltonian clause from self-adjointness**: positivity (contractions), `H Ω = 0`, the gap
(`ClassHamiltonian.generator_gap` at `X.time_gap`) and the unique fixed line (`fixed_eq_smul_vac`).

DERIVED: `0` the time origin. -/
theorem hamiltonianGap_of_selfAdjoint (X : OSDataS)
    (hsa : IsSelfAdjoint (ClassHamiltonian.generator X.time)) : HamiltonianGap X :=
  ⟨hsa,
    fun u => ClassHamiltonian.re_inner_generator_nonneg X.time
      (fun t ht => (X.time_selfAdjoint t ht.le).2) u,
    ClassHamiltonian.generator_vac X.time (fun t ht => X.time_vac t ht.le),
    fun u hu => ClassHamiltonian.generator_gap X.time X.gap_pos.le
      (fun t ht v hv => X.time_gap t ht.le v hv) u hu,
    fun _ ht u hu => fixed_eq_smul_vac X ht u hu⟩

#print axioms hamiltonianGap_of_selfAdjoint

/-- **The flowed time group has a self-adjoint generator.** `timeT` is the semigroup of real powers
of `stepT 0`, which is self-adjoint with spectrum in `[0, 1]` and trivial kernel.

DERIVED: `0` the reference step. -/
theorem observer_generator_isSelfAdjoint (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (τ : Fin 4) {r : ℝ} (hpos : Φ.PosPreserving τ r) :
    IsSelfAdjoint (ClassHamiltonian.generator (timeT hN Φ hB τ hpos)) :=
  ClassHamiltonian.powSemigroup_generator_isSelfAdjoint (isSelfAdjoint_stepT hN Φ hB τ hpos 0)
    (spectrum_stepT hN Φ hB τ hpos 0) (stepT_zero_injective hN Φ hB τ hpos)
    (dySpacing_pos (one_le_of_ne_zero hN) 0)

#print axioms observer_generator_isSelfAdjoint

/-! ## 4. The observer's energy density on the symmetrised plaquette class -/

/-- **Clauses 1–6 for the observer, clauses 7–8 as inputs.** For an axis-covariant configuration
flow `W` on `SymPlaqClass N`: (E) on `PlaqClass N`, the class moments `t, C`, one exponential moment
of the unit cube for a field `O` of the class, a physical range `r`, (M) at one step `m0`, (N), and
invariance under `pyth`; with `NonGaussian` and `LocalLink` for the observer's linked data.

DERIVED: `0` the signs and the excluded colour count; `1` the top of `ρ`; `4` in `Fin 4` the
dimension. -/
theorem clayFullAt_of_observer (hN : N ≠ 0) (W : ConfFlow N)
    (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N), W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ SymPlaqClass N) (h : UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r)
    (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube)) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) τ r)
    (hpyth : ∀ (ι : Type) [Fintype ι] (F : ι → SField N),
      (∀ i, (F i).1 ∈ SymPlaqClass N ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (rotFam pyth F)
          = contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) F)
    (hNG : NonGaussian (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT))
    (hLL : LocalLink hN (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT))
    (hOS2Z : OS2Zero (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT))
    (hdense : Dense (Set.range (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
      (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT).cvec)) :
    ClayFullAt hN W (SymPlaqClass N) (symPlaq_refl N) := by
  have hcubeS := symPlaq_cube hN W hW hcube
  have hSO4 := observerSO4_symPlaq hN W hW hcube hpyth
  have hB := uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN) hcubeS
  refine ⟨τ, r, observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN) hcubeS ht hC0 hU hO
    h τ hphys m0 hL hρ0 hρ1 hg hNT, fun ι _ O' g => rfl, hO, symPlaq_hypScalar O hO, ?_, ?_, ?_, ?_,
    hOS2Z, ⟨rfl, ?_, hdense⟩, ?_, hNG, hLL⟩
  · intro ι _ O' hO' g hg' v
    exact schwSFM_translate hN W (symPlaq_refl N) (symPlaq_nonneg hN) hcubeS ht hC0 hU O' hO' g hg' v
  · intro A hA ι _ O' hO' g hg'
    exact schwSFM_rotate hN W (symPlaq_refl N) (symPlaq_nonneg hN) ht hC0 hU hSO4 hA O'
      (fun i => (hO' i).1) (fun i => hO' i) g hg'
  · intro σ ι _ O' hO' g
    exact schwSFM_reflect hN W (SymPlaqClass N) (symPlaq_refl N) σ O' (fun i => (hO' i).2.2 σ) g
  · intro s hs c
    exact schwSFM_gram_nonneg hN W (symPlaq_refl N) (symPlaq_nonneg hN) hcubeS ht hC0 hU τ hphys s hs c
  · intro m Q
    have hpp := Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys τ
    have h1 := timeT_dyadic hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hB τ hpp m 1
    rw [Nat.cast_one, one_mul, pow_one] at h1
    show gvecT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hB τ hpp (MarginMono.shift hN τ m Q.1)
      = timeT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hB τ hpp (dySpacing N m)
          (gvecT hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hB τ hpp Q.1)
    rw [h1, stepT_gvecT]
  · exact hamiltonianGap_of_selfAdjoint _
      (observer_generator_isSelfAdjoint hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hB τ
        (Flow.posPreserving_of_physRange hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) hphys τ))

#print axioms clayFullAt_of_observer

/-- **The observer's inputs at one colour count**, as one Prop: those of `clayFullAt_of_observer`.

DERIVED: `0` the signs; `1` the top of `ρ`; `4` in `Fin 4` the dimension. -/
def ObserverInputs (hN : N ≠ 0) (W : ConfFlow N) : Prop :=
  ∃ (hW : ∀ (k : ℕ) (e : Equiv.Perm (Fin 4)) (U : Cfg N),
        W.V k (iaxisConf e U) = iaxisConf e (W.V k U))
    (hcube : ∀ O ∈ PlaqClass N, CubeMomentBound hN W O) (t C : ℝ) (ht : 0 < t) (hC0 : 0 ≤ C)
    (hU : ClassMoments hN W (SymPlaqClass N) t C) (O : LField (MassGap.SUN.SU N))
    (hO : O ∈ SymPlaqClass N) (h : UnitCubeExpBound hN W O) (τ : Fin 4) (r : ℝ)
    (hphys : (energy0 W (SymPlaqClass N) (symPlaq_refl N)).PhysRange r) (m0 : ℕ) (L : ℝ)
    (hL : 0 < L) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN
      (energy0 W (SymPlaqClass N) (symPlaq_refl N))
      (uniformBoundF_energy0 hN W (SymPlaqClass N) (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube)) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) τ r),
    (∀ (ι : Type) [Fintype ι] (F : ι → SField N),
      (∀ i, (F i).1 ∈ SymPlaqClass N ∧ HypScalar (F i).1) → (∀ i, UniformContinuous (F i).2.1) →
        contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) (rotFam pyth F)
          = contSF hN (energy0 W (SymPlaqClass N) (symPlaq_refl N)) F)
    ∧ NonGaussian (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
    ∧ LocalLink hN (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
    ∧ OS2Zero (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
    ∧ Dense (Set.range (observerOSDataSLinked hN W (symPlaq_refl N) (symPlaq_nonneg hN)
        (symPlaq_cube hN W hW hcube) ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT).cvec)

/-- **`ClayFull` from the observer's inputs at every `N ≥ 2`.**

DERIVED: `2` the least colour count. -/
theorem clayFull_of_observer
    (hin : ∀ N : ℕ, 2 ≤ N → ∃ (hN : N ≠ 0) (W : ConfFlow N), ObserverInputs hN W) : ClayFull := by
  intro N hN2
  obtain ⟨hN, W, hW, hcube, t, C, ht, hC0, hU, O, hO, h, τ, r, hphys, m0, L, hL, ρ, hρ0, hρ1, hg,
    hNT, hpyth, hNG, hLL, hOS2Z, hdense⟩ := hin N hN2
  exact ⟨hN, W, SymPlaqClass N, symPlaq_refl N,
    clayFullAt_of_observer hN W hW hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT hpyth hNG hLL
      hOS2Z hdense⟩

#print axioms clayFull_of_observer

end MassGap.ClayFull

end
