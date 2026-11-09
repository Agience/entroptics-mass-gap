import Mathlib
import MassGap.ShellGap

/-!
# MassGap.ShellMomentum — spatial translations and the zero-momentum sector of the reconstruction

`ShellGap.clay_gap_sq_le` reads the Clay gap from a Källén–Lehmann family under two assumptions:
(a) a finite `ρ` with `KallenLehmann σ ρ`, `SpecBottom ρ M2` and `ρ (Iic 0) = 0`, and (b)
`rateMeasure (X.time 1) u = σ 0` for a vector `u` of the vacuum complement. This module builds the
objects in which (b) is stated: spatial translations on the tree's reconstruction space, the
zero-momentum vector of a vector, and the zero-momentum part of its rate measure. The identification
`rateMeasure (X.time 1) u₀ = σ 0` itself is not proved here. Declarations are in the namespace
`MassGap.ShellMomentum`.

## What the tree has

* The reconstruction space `ContinuumTimeGroup.FlowH` is `GNSHilbert.H` of the reflection form
  `gForm K` on finite real combinations `MarginMono N τ r →₀ ℝ` of margin monomials, with kernel
  `K P Q = kernF P Q = contSF (pairFam τ P Q)`, the flowed Schwinger function of `θP ∪ Q`
  (`ContinuumFlow.flowTransfer`). Vectors of monomials are `gvecT Q`; the time step is
  `Finsupp.mapDomain (MarginMono.shift τ m)`, the time translation `timeT t = powT (stepT 0) (t/a₀)`.
* Translation covariance of the Schwinger functions: `ContinuumFlow.contSF_translate`, invariance of
  `contSF` under the dyadic translations `site (dySpacing N m) n`, `n ∈ ℤ⁴`, of every test function
  at once (OS1 on the dyadic lattice of every scale); `contSF_reflect` for the axis reflections.
  Real (non-dyadic) translations are not proved for a general flow.
* `OSDataS` carries no spatial translations, momentum or joint spectrum of `(H, P)`.
* Mathlib: the von Neumann mean ergodic theorem
  (`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`), orthogonal projections onto
  closed subspaces (`Submodule.starProjection`), the commutation of the continuous functional calculus
  with commuting operators (`Commute.cfc_real`) and uniqueness of finite Borel measures from bounded
  continuous integrals (`ext_of_forall_integral_eq_of_IsFiniteMeasure`). No joint spectral measure of
  commuting operators and no Stone theorem for unitary groups of `ℝ³` at this pin.

## 1. Symmetries of a reflection form are isometries of its Hilbert space (proved)

For a real-linear `S : A → A` that preserves a reflection form, `opS P S` is its complexification
extended to `GNSHilbert.H P`: `inner_opS` (it preserves the inner product), `opS_mul` (composition),
`opS_eq_one` (the identity), `opS_commute_opT` (it commutes with the transfer of a `TransferData`
whose step commutes with `S`) and `opS_Omega` (it fixes the vacuum if `S` fixes the vacuum
observable). This is the OS reconstruction of a symmetry, on the tree's own GNS construction.

## 2. Spatial translations of the tree's reconstruction (proved)

For a direction `τ`, a scale `m` and `n ∈ ℤ⁴` with `n τ = 0`, `spShift` translates every test
function of a margin monomial by the spatial vector `v = site (dySpacing N m) n`; `v τ = 0`, so the
margin is kept. `kernF_spShift`: `kernF (shift_v P) (shift_v Q) = kernF P Q`, because the time
reflection fixes `v` (`reflR_of_zero`) and `contSF_translate` moves every factor of `θP ∪ Q` by `v`.
`spT` is `opS` of `mapDomain spShift` on `FlowH`:

* `inner_spT`: it preserves the inner product; `spT_mul_neg`, `spT_neg_mul`: `spT n` and `spT (−n)`
  are inverse, so `spT` is unitary; `spT_mul`: `spT n spT n' = spT (n + n')`.
* `commute_spT_stepT`: it commutes with every time step (space and time translations commute,
  `Mono.shift_shift`), hence with `timeT t` (`commute_spT_timeT`, through `Commute.cfc_real`).
* `spT_vacT`: it fixes the vacuum. `spT_gvecT`: it moves the vector of `Q` to the vector of the
  translated monomial, and `inner_gvecT_spT`: `⟪gvecT P, spT (gvecT Q)⟫ = S(θP ∪ shift_v Q)`, the
  Schwinger function at spatial separation `v`.

## 3. Spatial data on an `OSDataS` (structure; the tree's instance proved)

`SpatialData X` is the clause `OSDataS` lacks: a family of operators `U i` preserving the inner
product, invertible, commuting with the unit time step and fixing the vacuum. It is the weakest form
used below: the projection results read only `commute` and `U_vac`; the ergodic reading reads
`inner_U` for `‖U i‖ ≤ 1`. `observerSpatial` is the tree's instance on `observerOSDataS`: the dyadic
translations `site (dySpacing N m) n` for every scale `m` and every `n ∈ ℤ⁴` with `n τ = 0`. There is
no ℝ³ translation group, no continuity in the translation and no momentum `p ≠ 0` here; 'zero
momentum' below means invariance under every dyadic translation. `trivialSpatial` is the instance with
no translation.

## 4. The zero-momentum vector (proved)

`zeroMom T` is the closed subspace of vectors fixed by every `U i` (zero momentum in the sense above),
`P0 T` its orthogonal projection
and `P0 T u` the zero-momentum vector of `u`.

* `commute_time_P0`: `P0` commutes with every `X.time t` (`commute_starProjection`: a self-adjoint
  operator preserving a closed subspace commutes with its projection).
* `rateMeasure_split`: `rateMeasure a u = rateMeasure a (P u) + rateMeasure a (u − P u)` for any
  self-adjoint idempotent `P` commuting with `a`; the cross terms of `⟪u, g(a) u⟫` vanish for every
  continuous `g`, and finite measures on `[0, 1]` are fixed by those integrals.
* `zero_momentum_sector`: for `u` in the vacuum complement, `u₀ = P0 T u` is translation invariant,
  in the vacuum complement, its rate measure is the zero-momentum summand of `u`'s rate measure,
  its correlator is the Laplace transform of that summand, and the summand vanishes below the gap.
* `zero_momentum_average` (mean ergodic theorem): for one translation `U i`, the projection `u_i` of
  `u` on the vectors fixed by `U i` has correlator
  `⟪u_i, e^{−tH} u_i⟫ = lim_n (1/n) Σ_{k<n} ⟪u, e^{−tH} U_i^k u⟫`. The fixed space of one translation
  contains the zero-momentum subspace and is larger (it also holds the momenta that are multiples of
  `2π/|v|` along `v`), so this is the spatial average of the translated correlator for one
  translation, not the zero-momentum correlator. At `t = 0` on the tree the average is the average of
  the Schwinger functions at separations `k v` (`inner_gvecT_spT`).
* The full zero-momentum projection `P0 T` is the projection on the vectors fixed by the whole family.
  Its expression as an iterated average over the three spatial directions and all scales is not
  formalised here; the one-translation average is.

## 5. The Källén–Lehmann template with the support clause (conditional on the identification `hσ`)

`KLTemplate'`: `KLTemplate` with `ρ (Iic 0) = 0`. `KLTemplate'.toKLTemplate` forgets the clause.
`clay_zero_momentum_sector`: under `KLTemplate'` data with `SpecBottom ρ M2` and the identification
`σ 0 = rateMeasure (X.time 1) (P0 T u)`, every conclusion of `ShellGap.clay_zero_momentum` holds for
`u₀`. Assumption (b) of `ShellGap` is now the statement that the Källén–Lehmann `σ 0` is the
zero-momentum summand built here. Plainly, that identification does not follow from this module: it
needs the joint spectral measure of `(H, P)` and its Lorentz invariance (OS-II applied to the `O(4)`
covariance `CovC`, analytically continued), the other half of `KLTemplate`. Plainly, for a
translation-invariant continuum theory the identification cannot hold for any u in the vacuum
complement. The only vector fixed by every spatial translation is the vacuum, so `P0 T u = 0` there,
its rate measure is `0`, and `σ 0` is not the zero measure (`ShellJoint.hσ_forces_zero_momentum_vector`).
The momentum-`0` Källén–Lehmann sector is the density at `p = 0` of the joint spectral measure of
`(H, P)` (`ShellJoint.jointMeasure`), not the restriction of that measure to the set `p = 0`.
`clay_zero_momentum_sector` is therefore a statement about data for which `hσ` holds, such as the
tree's `observerRealSpatial`, where `P0` contains all of `V⊥`; for physical data it has no instance.
This reasoning is argued, not formalised.

## 6. Load tests (proved)

* `zeroMom_eq_self`: a translation-invariant vector is its own zero-momentum vector, and its
  zero-momentum sector is its whole rate measure.
* `P0_eq_zero_of_odd`: a vector odd under one translation (`U i u = −u`, phase `π` along `v`)
  has zero-momentum vector `0` and zero-momentum sector `0` (`rateMeasure_zero_vec`).
* `trivialSpatial`: with no translation every vector is zero momentum (`P0_trivial`).
* `free_klTemplate'`: the free field of mass `m > 0` meets `KLTemplate'` with `ρ = δ_{m²}`;
  `massless_dirac_charges`: the measure `δ_0` charges `Iic 0`, so the support clause rules out
  `ρ = δ_0`, the Källén–Lehmann measure of the free field at `m = 0`.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ShellMomentum

open Real Filter Topology MeasureTheory Set
open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumReconstruction
  MassGap.ContinuumFlow MassGap.ContinuumTimeGroup MassGap.OSPositivity
open MassGap.BandShell (shell SpecBottom specBottom_dirac)
open MassGap.ShellMeasure (rateMeasure vecMeasure re_inner_cfc_eq_integral measurable_rate clamp
  continuous_clamp re_inner_powT_eq_laplace KallenLehmann KLTemplate klWeight freeRate
  free_kallenLehmann)
open MassGap.ShellGap (time_eq_powT time_isSelfAdjoint spectrum_time gap_rateBottom
  clay_zero_momentum)
open MassGap.ObserverOSReconstructionS (OSDataS observerOSDataS)

open scoped BoundedContinuousFunction

noncomputable section

/-! ## 1. Symmetries of a reflection form -/

section GNSSym

variable {A : Type*} [AddCommGroup A] [Module ℝ A] (P : Transfer.ReflForm A)

/-- **The complexified symmetry** on `Pre P`: `S` on both components. DERIVED: no numeral. -/
def cS (S : A →ₗ[ℝ] A) : GNSHilbert.Pre P →ₗ[ℂ] GNSHilbert.Pre P where
  toFun z := GNSHilbert.Pre.ofPair P (S (z : A × A).1) (S (z : A × A).2)
  map_add' z w := by refine GNSHilbert.Pre.ext ?_ ?_ <;> simp [map_add]
  map_smul' c z := by refine GNSHilbert.Pre.ext ?_ ?_ <;> simp [map_add, map_smul]

@[simp] theorem cS_fst (S : A →ₗ[ℝ] A) (z : GNSHilbert.Pre P) :
    ((cS P S z : GNSHilbert.Pre P) : A × A).1 = S (z : A × A).1 := rfl

@[simp] theorem cS_snd (S : A →ₗ[ℝ] A) (z : GNSHilbert.Pre P) :
    ((cS P S z : GNSHilbert.Pre P) : A × A).2 = S (z : A × A).2 := rfl

variable {P}

/-- **A form-preserving `S` preserves the complex form.** DERIVED: no numeral. -/
theorem cform_cS {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y)
    (z w : GNSHilbert.Pre P) :
    cform P.toPreForm ((cS P S z : GNSHilbert.Pre P) : A × A) ((cS P S w : GNSHilbert.Pre P) : A × A)
      = cform P.toPreForm (z : A × A) (w : A × A) := by
  refine ceq ?_ ?_
  · simp only [cform_re, cS_fst, cS_snd]
    rw [hS, hS]
  · simp only [cform_im, cS_fst, cS_snd]
    rw [hS, hS]

/-- **`cS` preserves the seminorm.** DERIVED: no numeral. -/
theorem norm_cS {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y)
    (z : GNSHilbert.Pre P) : ‖cS P S z‖ = ‖z‖ := by
  have h : ‖cS P S z‖ * ‖cS P S z‖ = ‖z‖ * ‖z‖ := by
    rw [GNSHilbert.Pre.norm_mul_norm, GNSHilbert.Pre.norm_mul_norm, cS_fst, cS_snd, hS, hS]
  rw [← Real.sqrt_mul_self (norm_nonneg (cS P S z)), h, Real.sqrt_mul_self (norm_nonneg z)]

/-- `cS` as a continuous linear map. DERIVED: `1` the isometry constant. -/
def cSL {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y) :
    GNSHilbert.Pre P →L[ℂ] GNSHilbert.Pre P :=
  LinearMap.mkContinuous (cS P S) 1 fun z => by rw [one_mul]; exact (norm_cS hS z).le

/-- **The symmetry on the Hilbert space**: the extension of `cSL` to the completion.
DERIVED: no numeral. -/
def opS {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y) :
    GNSHilbert.H P →L[ℂ] GNSHilbert.H P :=
  (cSL hS).completion

/-- DERIVED: no numeral. -/
theorem opS_coe {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y)
    (z : GNSHilbert.Pre P) :
    opS hS (z : GNSHilbert.H P) = ((cS P S z : GNSHilbert.Pre P) : GNSHilbert.H P) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- **The symmetry preserves the inner product.** DERIVED: no numeral. -/
theorem inner_opS {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y)
    (x y : GNSHilbert.H P) : inner ℂ (opS hS x) (opS hS y) = inner ℂ x y := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
      exact isClosed_eq (Continuous.inner ((opS hS).continuous.comp continuous_fst)
        ((opS hS).continuous.comp continuous_snd)) (Continuous.inner continuous_fst continuous_snd)
  | ih z w =>
      rw [opS_coe, opS_coe, GNSHilbert.inner_coe, GNSHilbert.inner_coe]
      exact cform_cS hS z w

/-- **Composition**: `S₁ ∘ S₂ = S₃` gives `opS S₁ * opS S₂ = opS S₃`. DERIVED: no numeral. -/
theorem opS_mul {S₁ S₂ S₃ : A →ₗ[ℝ] A} (h₁ : ∀ x y, P.form (S₁ x) (S₁ y) = P.form x y)
    (h₂ : ∀ x y, P.form (S₂ x) (S₂ y) = P.form x y) (h₃ : ∀ x y, P.form (S₃ x) (S₃ y) = P.form x y)
    (h : ∀ x, S₁ (S₂ x) = S₃ x) : opS h₁ * opS h₂ = opS h₃ := by
  refine ContinuousLinearMap.ext fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (opS h₁ * opS h₂).continuous (opS h₃).continuous
  | ih z =>
      rw [ContinuousLinearMap.mul_apply, opS_coe, opS_coe, opS_coe]
      congr 1
      refine GNSHilbert.Pre.ext ?_ ?_
      · simp only [cS_fst]; exact h _
      · simp only [cS_snd]; exact h _

/-- **The identity**: `S = id` gives `opS S = 1`. DERIVED: `1` the identity operator. -/
theorem opS_eq_one {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y)
    (h : ∀ x, S x = x) : opS hS = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (opS hS).continuous (1 : GNSHilbert.H P →L[ℂ] GNSHilbert.H P).continuous
  | ih z =>
      rw [opS_coe, ContinuousLinearMap.one_apply]
      congr 1
      refine GNSHilbert.Pre.ext ?_ ?_
      · simp only [cS_fst]; exact h _
      · simp only [cS_snd]; exact h _

/-- **The symmetry fixes the vacuum** if `S` fixes the vacuum observable. DERIVED: `0` the imaginary
component of the vacuum. -/
theorem opS_Omega {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y) {v : A}
    (hv : S v = v) : opS hS (GNSHilbert.Omega P v) = GNSHilbert.Omega P v := by
  unfold GNSHilbert.Omega
  rw [opS_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · simp only [cS_fst, GNSHilbert.Pre.ofPair_fst]; exact hv
  · simp only [cS_snd, GNSHilbert.Pre.ofPair_snd]; exact map_zero S

/-- **The symmetry commutes with the transfer** whose step commutes with `S`. DERIVED: no numeral. -/
theorem opS_commute_opT (D : Transfer.TransferData A) {S : A →ₗ[ℝ] A}
    (hS : ∀ x y, D.toReflForm.form (S x) (S y) = D.toReflForm.form x y)
    (hST : ∀ x, S (D.T x) = D.T (S x)) : Commute (opS hS) (GNSHilbert.opT D) := by
  show opS hS * GNSHilbert.opT D = GNSHilbert.opT D * opS hS
  refine ContinuousLinearMap.ext fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (opS hS * GNSHilbert.opT D).continuous
        (GNSHilbert.opT D * opS hS).continuous
  | ih z =>
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, GNSHilbert.opT_coe, opS_coe,
        opS_coe, GNSHilbert.opT_coe]
      congr 1
      refine GNSHilbert.Pre.ext ?_ ?_
      · simp only [cS_fst, GNSHilbert.cTL_apply, GNSHilbert.cT_fst]; exact hST _
      · simp only [cS_snd, GNSHilbert.cTL_apply, GNSHilbert.cT_snd]; exact hST _

end GNSSym

/-! ## 2. Spatial translations of the tree's reconstruction -/

section Spatial

variable {N : ℕ}

/-- **The time reflection fixes a spatial vector.** DERIVED: `0` the time component;
`4` in `Fin 4` the spacetime dimension. -/
theorem reflR_of_zero {τ : Fin 4} {v : Fin 4 → ℝ} (h : v τ = 0) : reflR τ v = v := by
  funext i
  by_cases hi : i = τ
  · subst hi; simp [reflR, h]
  · simp [reflR, Function.update_of_ne hi]

/-- DERIVED: `0` the time component; `4` in `Fin 4` the spacetime dimension. -/
theorem site_time_zero {τ : Fin 4} (a : ℝ) {n : Fin 4 → ℤ} (hn : n τ = 0) : site a n τ = 0 := by
  simp [site, hn]

/-- **A spatial translation of a margin monomial**: every test function moved by
`site (dySpacing N m) n`, `n τ = 0`; the margin in direction `τ` is kept.
DERIVED: `0` the time component; `4` in `Fin 4` the spacetime dimension. -/
def spShift (τ : Fin 4) (m : ℕ) (n : Fin 4 → ℤ) (hn : n τ = 0) {r : ℝ} (P : MarginMono N τ r) :
    MarginMono N τ r :=
  ⟨Mono.shift (site (dySpacing N m) n) P.1, by
    obtain ⟨d, hd, hrd, hP⟩ := P.2
    exact ⟨d, hd, hrd, posAt_shift hP (site_time_zero _ hn).symm.le⟩⟩

/-- **The reflected pair of two spatially translated monomials** is the pair with every factor
translated. DERIVED: `0` the time component; `4` in `Fin 4` the spacetime dimension. -/
theorem pairFam_spShift (τ : Fin 4) (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (P Q : Mono N) :
    pairFam τ (Mono.shift (site (dySpacing N m) n) P) (Mono.shift (site (dySpacing N m) n) Q)
      = fun x => ((pairFam τ P Q x).1, (pairFam τ P Q x).2.translate (site (dySpacing N m) n)) := by
  funext x
  cases x with
  | inl i =>
    show ((P.2 i).1.refl τ, ((P.2 i).2.translate (site (dySpacing N m) n)).reflect τ)
      = ((P.2 i).1.refl τ, ((P.2 i).2.reflect τ).translate (site (dySpacing N m) n))
    rw [TestFn.reflect_translate, reflR_of_zero (site_time_zero _ hn)]
  | inr j => rfl

/-- **The reflection kernel is invariant under spatial translations** (OS1 on the dyadic lattice,
`contSF_translate`). DERIVED: `0` the time component; `4` in `Fin 4` the spacetime dimension. -/
theorem kernF_spShift (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0)
    (P Q : Mono N) :
    kernF hN Φ τ (Mono.shift (site (dySpacing N m) n) P) (Mono.shift (site (dySpacing N m) n) Q)
      = kernF hN Φ τ P Q := by
  unfold kernF
  rw [pairFam_spShift τ m hn]
  exact contSF_translate hN Φ (pairFam τ P Q) m n

/-- **Space and time translations commute** on margin monomials. DERIVED: `0` the time component;
`1` the unit step; `4` in `Fin 4` the spacetime dimension. -/
theorem spShift_shift (hN : N ≠ 0) (τ : Fin 4) (m k : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) {r : ℝ}
    (P : MarginMono N τ r) :
    spShift τ m n hn (MarginMono.shift hN τ k P) = MarginMono.shift hN τ k (spShift τ m n hn P) := by
  apply Subtype.ext
  show Mono.shift (site (dySpacing N m) n) (Mono.shift (timeVec N k τ 1) P.1)
    = Mono.shift (timeVec N k τ 1) (Mono.shift (site (dySpacing N m) n) P.1)
  rw [Mono.shift_shift, Mono.shift_shift, add_comm]

/-- **Two spatial translations compose.** DERIVED: `0` the time component; `4` in `Fin 4` the
spacetime dimension. -/
theorem spShift_spShift (τ : Fin 4) (m : ℕ) {n n' : Fin 4 → ℤ} (hn : n τ = 0) (hn' : n' τ = 0)
    (hnn : (n + n') τ = 0) {r : ℝ} (P : MarginMono N τ r) :
    spShift τ m n hn (spShift τ m n' hn' P) = spShift τ m (n + n') hnn P := by
  apply Subtype.ext
  show Mono.shift (site (dySpacing N m) n) (Mono.shift (site (dySpacing N m) n') P.1)
    = Mono.shift (site (dySpacing N m) (n + n')) P.1
  rw [Mono.shift_shift, site_add, add_comm n' n]

/-- **The zero translation is the identity.** DERIVED: `0` the zero vector and the time component;
`4` in `Fin 4` the spacetime dimension. -/
theorem spShift_zero (τ : Fin 4) (m : ℕ) (h0 : (0 : Fin 4 → ℤ) τ = 0) {r : ℝ}
    (P : MarginMono N τ r) : spShift τ m 0 h0 P = P := by
  apply Subtype.ext
  show Mono.shift (site (dySpacing N m) 0) P.1 = P.1
  rw [site_zero, Mono.shift_zero]

/-- **The empty monomial is translation invariant.** DERIVED: `0` the empty family and the time
component; `4` in `Fin 4` the spacetime dimension. -/
theorem spShift_emptyMargin (τ : Fin 4) (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) {r : ℝ} :
    spShift τ m n hn (emptyMargin N τ r) = emptyMargin N τ r :=
  Subtype.ext (congrArg (Sigma.mk 0) (funext fun i => i.elim0))

/-- **The linear spatial translation** on finite combinations. DERIVED: `0` the time component;
`4` in `Fin 4` the spacetime dimension. -/
def spLin (τ : Fin 4) (m : ℕ) (n : Fin 4 → ℤ) (hn : n τ = 0) (r : ℝ) :
    (MarginMono N τ r →₀ ℝ) →ₗ[ℝ] (MarginMono N τ r →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ (spShift τ m n hn)

/-- **A kernel-preserving relabelling preserves the form.** DERIVED: no numeral. -/
theorem gForm_mapDomain_inv {M : Type} (K : M → M → ℝ) (g : M → M)
    (hg : ∀ P Q, K (g P) (g Q) = K P Q) (c d : M →₀ ℝ) :
    gForm K (Finsupp.mapDomain g c) (Finsupp.mapDomain g d) = gForm K c d := by
  rw [gForm_mapDomain]
  unfold gForm
  simp only [hg]

variable (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
  (hpp : Φ.PosPreserving τ r)

/-- **The spatial translation preserves the reflection form.** DERIVED: `0` the reference step and
the time component; `4` in `Fin 4` the spacetime dimension. -/
theorem form_spLin (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (x y : MarginMono N τ r →₀ ℝ) :
    (flowTransfer hN Φ hB τ hpp 0).toReflForm.form (spLin τ m n hn r x) (spLin τ m n hn r y)
      = (flowTransfer hN Φ hB τ hpp 0).toReflForm.form x y := by
  show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
      (Finsupp.mapDomain (spShift τ m n hn) x) (Finsupp.mapDomain (spShift τ m n hn) y)
    = gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) x y
  exact gForm_mapDomain_inv _ _ (fun P Q => kernF_spShift hN Φ τ m hn P.1 Q.1) x y

/-- **The spatial translation on the reconstruction space** `FlowH`, by `site (dySpacing N m) n`.
DERIVED: `0` the reference step and the time component; `4` in `Fin 4` the spacetime dimension. -/
def spT (m : ℕ) (n : Fin 4 → ℤ) (hn : n τ = 0) : FlowH hN Φ hB τ hpp →L[ℂ] FlowH hN Φ hB τ hpp :=
  opS (form_spLin hN Φ hB τ hpp m hn)

/-- **It preserves the inner product.** DERIVED: as in `spT`. -/
theorem inner_spT (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (x y : FlowH hN Φ hB τ hpp) :
    inner ℂ (spT hN Φ hB τ hpp m n hn x) (spT hN Φ hB τ hpp m n hn y) = inner ℂ x y :=
  inner_opS _ x y

/-- **The group law at one scale**: `spT n · spT n' = spT (n + n')`. DERIVED: as in `spT`. -/
theorem spT_mul (m : ℕ) {n n' : Fin 4 → ℤ} (hn : n τ = 0) (hn' : n' τ = 0) (hnn : (n + n') τ = 0) :
    spT hN Φ hB τ hpp m n hn * spT hN Φ hB τ hpp m n' hn' = spT hN Φ hB τ hpp m (n + n') hnn := by
  refine opS_mul _ _ _ fun x => ?_
  show Finsupp.mapDomain (spShift τ m n hn) (Finsupp.mapDomain (spShift τ m n' hn') x)
    = Finsupp.mapDomain (spShift τ m (n + n') hnn) x
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext P
  exact spShift_spShift τ m hn hn' hnn P

/-- **The zero translation is the identity.** DERIVED: `0` the zero vector; `1` the identity. -/
theorem spT_zero (m : ℕ) (h0 : (0 : Fin 4 → ℤ) τ = 0) : spT hN Φ hB τ hpp m 0 h0 = 1 := by
  refine opS_eq_one _ fun x => ?_
  show Finsupp.mapDomain (spShift τ m 0 h0) x = x
  have : spShift τ m 0 h0 = (id : MarginMono N τ r → MarginMono N τ r) :=
    funext fun P => spShift_zero τ m h0 P
  rw [this, Finsupp.mapDomain_id]

/-- **The translation depends on `n` only.** DERIVED: `4` in `Fin 4` the spacetime dimension; `0` the
time component. -/
theorem spT_congr (m : ℕ) {n n' : Fin 4 → ℤ} (hn : n τ = 0) (hn' : n' τ = 0) (h : n = n') :
    spT hN Φ hB τ hpp m n hn = spT hN Φ hB τ hpp m n' hn' := by
  subst h; rfl

/-- DERIVED: `0` the time component. -/
theorem neg_time_zero {n : Fin 4 → ℤ} (hn : n τ = 0) : (-n) τ = 0 := by simp [hn]

/-- **`spT n` and `spT (−n)` are inverse**: the spatial translation is unitary.
DERIVED: `1` the identity; `0` the zero vector; `4` in `Fin 4` the spacetime dimension. -/
theorem spT_mul_neg (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) :
    spT hN Φ hB τ hpp m n hn * spT hN Φ hB τ hpp m (-n) (neg_time_zero τ hn) = 1 := by
  have h0 : (n + -n) τ = 0 := by simp
  have h0' : (0 : Fin 4 → ℤ) τ = 0 := rfl
  rw [spT_mul hN Φ hB τ hpp m hn (neg_time_zero τ hn) h0,
    spT_congr hN Φ hB τ hpp m h0 h0' (add_neg_cancel n), spT_zero]

/-- DERIVED: as in `spT_mul_neg`. -/
theorem spT_neg_mul (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) :
    spT hN Φ hB τ hpp m (-n) (neg_time_zero τ hn) * spT hN Φ hB τ hpp m n hn = 1 := by
  have h0 : (-n + n) τ = 0 := by simp
  have h0' : (0 : Fin 4 → ℤ) τ = 0 := rfl
  rw [spT_mul hN Φ hB τ hpp m (neg_time_zero τ hn) hn h0,
    spT_congr hN Φ hB τ hpp m h0 h0' (neg_add_cancel n), spT_zero]

/-- **The spatial translation commutes with every time step.** DERIVED: `0` the reference step;
`4` in `Fin 4` the spacetime dimension. -/
theorem commute_spT_stepT (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (k : ℕ) :
    Commute (spT hN Φ hB τ hpp m n hn) (stepT hN Φ hB τ hpp k) :=
  opS_commute_opT (flowTransfer hN Φ hB τ hpp k) (form_spLin hN Φ hB τ hpp m hn) fun x => by
    show Finsupp.mapDomain (spShift τ m n hn) (Finsupp.mapDomain (MarginMono.shift hN τ k) x)
      = Finsupp.mapDomain (MarginMono.shift hN τ k) (Finsupp.mapDomain (spShift τ m n hn) x)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext P
    exact spShift_shift hN τ m k hn P

/-- **The spatial translation commutes with every time translation** `timeT t`, a function of the
step-zero transfer in the continuous functional calculus. DERIVED: `0` the reference step. -/
theorem commute_spT_timeT (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (t : ℝ) :
    Commute (spT hN Φ hB τ hpp m n hn) (timeT hN Φ hB τ hpp t) :=
  (Commute.cfc_real (commute_spT_stepT hN Φ hB τ hpp m hn 0).symm
    (fun x : ℝ => x ^ (t / dySpacing N 0))).symm

/-- **The spatial translation fixes the vacuum.** DERIVED: `1` the vacuum coefficient. -/
theorem spT_vacT (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) :
    spT hN Φ hB τ hpp m n hn (vacT hN Φ hB τ hpp) = vacT hN Φ hB τ hpp := by
  refine opS_Omega _ ?_
  show Finsupp.mapDomain (spShift τ m n hn) (Finsupp.single (emptyMargin N τ r) 1)
    = Finsupp.single (emptyMargin N τ r) 1
  rw [Finsupp.mapDomain_single, spShift_emptyMargin]

/-- **The spatial translation moves the vector of a monomial to the vector of its translate.**
DERIVED: `1` the coefficient; `0` the imaginary part. -/
theorem spT_gvecT (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (Q : MarginMono N τ r) :
    spT hN Φ hB τ hpp m n hn (gvecT hN Φ hB τ hpp Q) = gvecT hN Φ hB τ hpp (spShift τ m n hn Q) := by
  unfold gvecT
  rw [spT, opS_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show Finsupp.mapDomain (spShift τ m n hn) (Finsupp.single Q 1)
      = Finsupp.single (spShift τ m n hn Q) 1
    exact Finsupp.mapDomain_single
  · show Finsupp.mapDomain (spShift τ m n hn) 0 = 0
    exact Finsupp.mapDomain_zero

/-- **The translated inner product is the Schwinger function at spatial separation `v`**:
`⟪gvecT P, spT (gvecT Q)⟫ = S(θP ∪ shift_v Q)`. DERIVED: `0` the reference step. -/
theorem inner_gvecT_spT (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0) (P Q : MarginMono N τ r) :
    inner ℂ (gvecT hN Φ hB τ hpp P) (spT hN Φ hB τ hpp m n hn (gvecT hN Φ hB τ hpp Q))
      = (kernF hN Φ τ P.1 (Mono.shift (site (dySpacing N m) n) Q.1) : ℂ) := by
  rw [spT_gvecT]
  exact inner_gVec (flowTransfer hN Φ hB τ hpp 0)
    (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1) (fun _ _ => rfl) P (spShift τ m n hn Q)

end Spatial

/-! ## 3. Spatial data on an `OSDataS` -/

/-- **Spatial translations of an `OSDataS`**: operators preserving the inner product, invertible,
commuting with the unit time step and fixing the vacuum. DERIVED: `1` the unit step and the
identity. -/
structure SpatialData (X : OSDataS) where
  /-- The index of the translations. -/
  ι : Type
  /-- The translations. -/
  U : ι → X.H →L[ℂ] X.H
  /-- Their inverses. -/
  Uinv : ι → X.H →L[ℂ] X.H
  inner_U : ∀ i x y, inner ℂ (U i x) (U i y) = inner ℂ x y
  U_Uinv : ∀ i, U i * Uinv i = 1
  Uinv_U : ∀ i, Uinv i * U i = 1
  /-- **Space and time translations commute.** -/
  commute : ∀ i, Commute (U i) (X.time 1)
  U_vac : ∀ i, U i X.vac = X.vac

/-- **The trivial spatial data**: no translation. DERIVED: `1` the identity. -/
def trivialSpatial (X : OSDataS) : SpatialData X where
  ι := Unit
  U _ := 1
  Uinv _ := 1
  inner_U _ _ _ := by simp
  U_Uinv _ := one_mul 1
  Uinv_U _ := one_mul 1
  commute _ := Commute.one_left _
  U_vac _ := by simp

section Observer

variable {N : ℕ}

/-- **The index of the tree's spatial translations**: a scale `m` and `n ∈ ℤ⁴` with `n τ = 0`.
DERIVED: `0` the time component; `4` in `Fin 4` the spacetime dimension. -/
abbrev SpIdx (τ : Fin 4) : Type := {p : ℕ × (Fin 4 → ℤ) // p.2 τ = 0}

/-- **The tree's spatial data** on `observerOSDataS`: the translations `spT` of every scale and
every spatial `n`. DERIVED: `0` the excluded colour count, the reference step and the time
component; `1` the top of `ρ` and the unit step; `4` in `Fin 4` the spacetime dimension. -/
def observerSpatial (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, ObserverEnergyBox.CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (ObserverOS.energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (ObserverOS.energy0 W D hD)
      (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (ObserverOS.energy0 W D hD) τ r) :
    SpatialData (observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT) :=
  let Φ := ObserverOS.energy0 W D hD
  let hB := ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN Φ hphys τ
  { ι := SpIdx τ
    U := fun i => spT hN Φ hB τ hpp i.1.1 i.1.2 i.2
    Uinv := fun i => spT hN Φ hB τ hpp i.1.1 (-i.1.2) (neg_time_zero τ i.2)
    inner_U := fun i x y => inner_spT hN Φ hB τ hpp i.1.1 i.2 x y
    U_Uinv := fun i => spT_mul_neg hN Φ hB τ hpp i.1.1 i.2
    Uinv_U := fun i => spT_neg_mul hN Φ hB τ hpp i.1.1 i.2
    commute := fun i => commute_spT_timeT hN Φ hB τ hpp i.1.1 i.2 1
    U_vac := fun i => spT_vacT hN Φ hB τ hpp i.1.1 i.2 }

end Observer

/-! ## 4. The zero-momentum vector -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **A self-adjoint operator preserving a closed subspace commutes with its projection.**
DERIVED: `0` the vanishing pairings. -/
theorem commute_starProjection (K : Submodule ℂ E) [K.HasOrthogonalProjection] {a : E →L[ℂ] E}
    (ha : IsSelfAdjoint a) (hK : ∀ x ∈ K, a x ∈ K) : Commute a K.starProjection := by
  have hsym : ∀ x y, inner ℂ (a x) y = inner ℂ x (a y) := by
    intro x y
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha) x y
    simpa using h
  show a * K.starProjection = K.starProjection * a
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  refine (Submodule.eq_starProjection_of_mem_orthogonal (hK _ (K.starProjection_apply_mem x)) ?_).symm
  rw [← map_sub]
  have hw := Submodule.sub_starProjection_mem_orthogonal (K := K) x
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro k hk
  rw [← hsym]
  exact hw _ (hK k hk)

/-- **The cross terms vanish**: for a self-adjoint idempotent `P` commuting with `C`,
`⟪u, C u⟫ = ⟪P u, C P u⟫ + ⟪u − P u, C (u − P u)⟫`. DERIVED: `0` the cross terms. -/
theorem inner_split {P C : E →L[ℂ] E} (hP : IsSelfAdjoint P) (hPP : IsIdempotentElem P)
    (hc : Commute C P) (u : E) :
    inner ℂ u (C u) = inner ℂ (P u) (C (P u)) + inner ℂ (u - P u) (C (u - P u)) := by
  have hsym : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y) := by
    intro x y
    have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP) x y
    simpa using h
  have hPP' : ∀ x, P (P x) = P x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, hPP.eq]
  have hcomm : ∀ x, C (P x) = P (C x) := fun x => by
    rw [← ContinuousLinearMap.mul_apply, hc.eq, ContinuousLinearMap.mul_apply]
  have hPw : P (u - P u) = 0 := by rw [map_sub, hPP', sub_self]
  have h1 : inner ℂ (P u) (C (u - P u)) = 0 := by
    rw [hsym, ← hcomm, hPw, map_zero, inner_zero_right]
  have h2 : inner ℂ (u - P u) (C (P u)) = 0 := by
    rw [hcomm, ← hsym, hPw, inner_zero_left]
  have hu : P u + (u - P u) = u := by abel
  calc inner ℂ u (C u) = inner ℂ (P u + (u - P u)) (C (P u + (u - P u))) := by rw [hu]
    _ = _ := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2, add_zero, zero_add]

/-- **A bounded continuous integral against the spectral measure is a vector state.**
DERIVED: `0`, `1` the ends of the spectrum interval. -/
theorem integral_vecMeasure {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (v : E)
    (f : Icc (0 : ℝ) 1 →ᵇ ℝ) :
    ∫ x, f x ∂(vecMeasure a v) = (inner ℂ v (cfc (fun y => f (clamp y)) a v)).re := by
  rw [re_inner_cfc_eq_integral (g := fun y => f (clamp y)) hsp v (f.continuous.comp continuous_clamp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show f x = f (clamp x.1)
  rw [clamp, projIcc_val]

/-- **The spectral measure splits along a reducing projection.** DERIVED: `0`, `1` the ends of the
spectrum interval. -/
theorem vecMeasure_split {a P : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (hP : IsSelfAdjoint P)
    (hPP : IsIdempotentElem P) (hc : Commute a P) (u : E) :
    vecMeasure a u = vecMeasure a (P u) + vecMeasure a (u - P u) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_add_measure (f.integrable _) (f.integrable _), integral_vecMeasure hsp,
    integral_vecMeasure hsp, integral_vecMeasure hsp,
    inner_split hP hPP (hc.cfc_real (fun y => f (clamp y))) u, Complex.add_re]

/-- **The rate measure splits along a reducing projection**:
`σ_u = σ_{P u} + σ_{u − P u}`. DERIVED: `0`, `1` the ends of the spectrum interval. -/
theorem rateMeasure_split {a P : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) (hP : IsSelfAdjoint P)
    (hPP : IsIdempotentElem P) (hc : Commute a P) (u : E) :
    rateMeasure a u = rateMeasure a (P u) + rateMeasure a (u - P u) := by
  unfold rateMeasure
  rw [vecMeasure_split hsp hP hPP hc u, Measure.restrict_add, Measure.map_add _ _ measurable_rate]

/-- **The zero vector has the zero spectral measure.** DERIVED: `0`, `1` the ends of the spectrum
interval. -/
theorem vecMeasure_zero_vec {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) :
    vecMeasure a (0 : E) = 0 := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_vecMeasure hsp, inner_zero_left, Complex.zero_re, integral_zero_measure]

/-- **The zero vector has the zero rate measure.** DERIVED: `0`, `1` as above. -/
theorem rateMeasure_zero_vec {a : E →L[ℂ] E} (hsp : spectrum ℝ a ⊆ Icc 0 1) :
    rateMeasure a (0 : E) = 0 := by
  unfold rateMeasure
  rw [vecMeasure_zero_vec hsp, Measure.restrict_zero, Measure.map_zero]

end Projection

section OS

variable {X : OSDataS} (T : SpatialData X)

/-- **The zero-momentum subspace**: the vectors fixed by every translation. DERIVED: no numeral. -/
def zeroMom : Submodule ℂ X.H where
  carrier := {x | ∀ i, T.U i x = x}
  add_mem' hx hy i := by rw [map_add, hx i, hy i]
  zero_mem' i := map_zero _
  smul_mem' c x hx i := by rw [map_smul, hx i]

/-- DERIVED: no numeral. -/
theorem mem_zeroMom {x : X.H} : x ∈ zeroMom T ↔ ∀ i, T.U i x = x := Iff.rfl

/-- **The zero-momentum subspace is closed.** DERIVED: no numeral. -/
theorem isClosed_zeroMom : IsClosed (zeroMom T : Set X.H) := by
  show IsClosed {x : X.H | ∀ i, T.U i x = x}
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq (T.U i).continuous continuous_id

instance : CompleteSpace (zeroMom T) := IsClosed.completeSpace_coe (hs := isClosed_zeroMom T)

/-- **The zero-momentum projection.** DERIVED: no numeral. -/
def P0 : X.H →L[ℂ] X.H := (zeroMom T).starProjection

/-- **Each translation commutes with every time translation** `t ≥ 0`. DERIVED: `0` the sign of
`t`; `1` the unit step. -/
theorem commute_U_time (i : T.ι) {t : ℝ} (ht : 0 ≤ t) : Commute (T.U i) (X.time t) := by
  rw [time_eq_powT X ht]
  exact (Commute.cfc_real (T.commute i).symm (fun x : ℝ => x ^ t)).symm

/-- **The time translations preserve the zero-momentum subspace.** DERIVED: `0` the sign of `t`. -/
theorem time_mem_zeroMom {t : ℝ} (ht : 0 ≤ t) {x : X.H} (hx : x ∈ zeroMom T) :
    X.time t x ∈ zeroMom T := (mem_zeroMom T).mpr fun i => by
  rw [← ContinuousLinearMap.mul_apply, (commute_U_time T i ht).eq, ContinuousLinearMap.mul_apply,
    (mem_zeroMom T).mp hx i]

/-- **The zero-momentum projection commutes with every time translation.** DERIVED: `0` the sign
of `t`. -/
theorem commute_time_P0 {t : ℝ} (ht : 0 ≤ t) : Commute (X.time t) (P0 T) :=
  commute_starProjection _ (time_isSelfAdjoint X ht) fun _ hx => time_mem_zeroMom T ht hx

/-- **The vacuum has zero momentum.** DERIVED: no numeral. -/
theorem vac_mem_zeroMom : X.vac ∈ zeroMom T := T.U_vac

/-- **The zero-momentum vector of a complement vector is in the complement.** DERIVED: `0` the
vanishing pairing. -/
theorem inner_vac_P0 {u : X.H} (hu : inner ℂ X.vac u = 0) : inner ℂ X.vac (P0 T u) = 0 := by
  rw [P0, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (vac_mem_zeroMom T)]
  exact hu

/-- **The zero-momentum sector of a vector of the vacuum complement.** `u₀ = P0 u` is translation
invariant and orthogonal to the vacuum; the rate measure of `u` is the rate measure of `u₀` plus that
of `u − u₀`; the correlator of `u₀` is the Laplace transform of its rate measure; and that rate
measure vanishes below the Clay gap. DERIVED: `0` the vanishing pairing and the sign of `t`; `1` the
unit step. -/
theorem zero_momentum_sector (u : X.H) (hu : inner ℂ X.vac u = 0) :
    P0 T u ∈ zeroMom T ∧ inner ℂ X.vac (P0 T u) = 0
      ∧ rateMeasure (X.time 1) u
          = rateMeasure (X.time 1) (P0 T u) + rateMeasure (X.time 1) (u - P0 T u)
      ∧ (∀ t, 0 < t → (inner ℂ (P0 T u) (X.time t (P0 T u))).re
          = ∫ E, Real.exp (-(t * E)) ∂(rateMeasure (X.time 1) (P0 T u)))
      ∧ rateMeasure (X.time 1) (P0 T u) (Iio X.gap) = 0 := by
  have h0 := inner_vac_P0 T hu
  refine ⟨(zeroMom T).starProjection_apply_mem u, h0,
    rateMeasure_split (spectrum_time X zero_le_one) (isSelfAdjoint_starProjection _)
      (zeroMom T).isIdempotentElem_starProjection (commute_time_P0 T zero_le_one) u,
    fun t ht => ?_, gap_rateBottom X _ h0⟩
  rw [time_eq_powT X ht.le]
  exact re_inner_powT_eq_laplace (spectrum_time X zero_le_one) _ ht

/-- **A translation is a contraction** (it preserves the norm). DERIVED: `1` the bound; `2` the
square. -/
theorem norm_U_le (i : T.ι) : ‖T.U i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have h : ‖T.U i x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), T.inner_U]
  rw [one_mul]
  exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h).le

/-- **The averaged correlator**: the correlator against the Birkhoff average is the average of the
translated correlators. DERIVED: no numeral. -/
theorem inner_birkhoffAverage (i : T.ι) (u : X.H) (t : ℝ) (n : ℕ) :
    inner ℂ u (X.time t (birkhoffAverage ℂ (T.U i) _root_.id n u))
      = (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, inner ℂ u (X.time t ((T.U i)^[k] u)) := by
  simp only [birkhoffAverage, birkhoffSum, id, map_smul, map_sum, inner_smul_right, inner_sum]

/-- **The vectors fixed by one translation.** DERIVED: `1` the identity. -/
abbrev Fix (i : T.ι) : Submodule ℂ X.H := (T.U i).eqLocus (1 : X.H →L[ℂ] X.H)

/-- **The time translations preserve the fixed vectors of a translation.** DERIVED: `0` the sign
of `t`; `1` the identity. -/
theorem time_mem_Fix (i : T.ι) {t : ℝ} (ht : 0 ≤ t) {x : X.H} (hx : x ∈ Fix T i) :
    X.time t x ∈ Fix T i := by
  have hx' : T.U i x = x := by simpa using LinearMap.mem_eqLocus.mp hx
  refine LinearMap.mem_eqLocus.mpr ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.one_apply]
  rw [← ContinuousLinearMap.mul_apply, (commute_U_time T i ht).eq, ContinuousLinearMap.mul_apply,
    hx']

/-- **The mean ergodic reading of the one-translation correlator** (von Neumann). For one translation
`U i` and `t ≥ 0`, the projection `u_i` of `u` on the vectors fixed by the single translation `U i`
(not the zero-momentum projection `P0`) has
`⟪u_i, e^{−tH} u_i⟫ = lim_n (1/n) Σ_{k<n} ⟪u, e^{−tH} U_i^k u⟫`. DERIVED: `0` the sign of `t`;
`1` the identity whose fixed points are taken. -/
theorem zero_momentum_average (i : T.ι) (u : X.H) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, inner ℂ u (X.time t ((T.U i)^[k] u)))
      atTop
      (𝓝 (inner ℂ ((Fix T i).starProjection u) (X.time t ((Fix T i).starProjection u)))) := by
  have hcomm := commute_starProjection (Fix T i) (time_isSelfAdjoint X ht)
    fun x hx => time_mem_Fix T i ht hx
  have hc' : ∀ x, (Fix T i).starProjection (X.time t x) = X.time t ((Fix T i).starProjection x) :=
    fun x => by
      have h := congrArg (fun F : X.H →L[ℂ] X.H => F x) hcomm.eq
      simp only [ContinuousLinearMap.mul_apply] at h
      exact h.symm
  have hidem : (Fix T i).starProjection ((Fix T i).starProjection u) = (Fix T i).starProjection u :=
    Submodule.starProjection_eq_self_iff.mpr ((Fix T i).starProjection_apply_mem u)
  have heq : inner ℂ ((Fix T i).starProjection u) (X.time t ((Fix T i).starProjection u))
      = inner ℂ u (X.time t ((Fix T i).starProjection u)) := by
    rw [Submodule.inner_starProjection_left_eq_right, hc', hidem]
  rw [heq]
  have h := (T.U i).tendsto_birkhoffAverage_orthogonalProjection (norm_U_le T i) u
  have hc : Continuous fun v : X.H => inner ℂ u (X.time t v) :=
    continuous_const.inner (X.time t).continuous
  have h2 := (hc.tendsto _).comp h
  exact h2.congr fun n => inner_birkhoffAverage T i u t n

/-! ### Load tests -/

/-- **A translation-invariant vector is its own zero-momentum vector**, and its zero-momentum sector
is its whole rate measure. DERIVED: `1` the unit step. -/
theorem zeroMom_eq_self {u : X.H} (hu : u ∈ zeroMom T) :
    P0 T u = u ∧ rateMeasure (X.time 1) (P0 T u) = rateMeasure (X.time 1) u := by
  have h : P0 T u = u := Submodule.starProjection_eq_self_iff.mpr hu
  exact ⟨h, by rw [h]⟩

/-- **A vector odd under one translation has no zero-momentum part**: `U i u = −u` gives `P0 u = 0`
and a zero zero-momentum sector. DERIVED: `0` the zero vector; `1` the unit step; `2` the doubled
pairing. -/
theorem P0_eq_zero_of_odd {u : X.H} (i : T.ι) (hodd : T.U i u = -u) :
    P0 T u = 0 ∧ rateMeasure (X.time 1) (P0 T u) = 0 := by
  have horth : u ∈ (zeroMom T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    have h1 : inner ℂ (T.U i k) (T.U i u) = inner ℂ k u := T.inner_U i k u
    rw [(mem_zeroMom T).mp hk i, hodd, inner_neg_right] at h1
    have h2 : (2 : ℂ) * inner ℂ k u = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have h : P0 T u = 0 :=
    congrArg Subtype.val (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr horth)
  exact ⟨h, by rw [h]; exact rateMeasure_zero_vec (spectrum_time X zero_le_one)⟩

end OS

/-- **With no translation every vector has zero momentum.** DERIVED: no numeral. -/
theorem P0_trivial (X : OSDataS) (u : X.H) : P0 (trivialSpatial X) u = u :=
  Submodule.starProjection_eq_self_iff.mpr ((mem_zeroMom _).mpr fun _ => by
    show (1 : X.H →L[ℂ] X.H) u = u
    simp)

/-! ## 5. The Källén–Lehmann template with the support clause -/

/-- **The Källén–Lehmann template with the support clause** `ρ (Iic 0) = 0`. DERIVED: `0` the
bottom of the `s`-line. -/
def KLTemplate' (σ : ℝ → Measure ℝ) : Prop :=
  ∃ ρ : Measure ℝ, IsFiniteMeasure ρ ∧ ρ (Iic 0) = 0 ∧ KallenLehmann σ ρ

/-- **It refines `ShellMeasure.KLTemplate`.** DERIVED: no numeral. -/
theorem KLTemplate'.toKLTemplate {σ : ℝ → Measure ℝ} (h : KLTemplate' σ) : KLTemplate σ := by
  obtain ⟨ρ, hf, _, hkl⟩ := h
  exact ⟨ρ, hf, hkl⟩

/-- **The Clay read of the zero-momentum sector.** Given Källén–Lehmann data with the support clause
and the identification of `σ 0` with the zero-momentum sector of `u`, the conclusions of
`ShellGap.clay_zero_momentum` hold for the zero-momentum vector `P0 T u`. DERIVED: `0` the zero
momentum, the signs and the vanishing pairing; `1` the unit step; `2` the square. `hσ` is
undischarged: no instance of `KLTemplate` or `KLTemplate'` for the tree's `σ` is constructed here, and
`free_klTemplate'` is the free field only. -/
theorem clay_zero_momentum_sector {X : OSDataS} (T : SpatialData X) (u : X.H)
    (hu : inner ℂ X.vac u = 0) {σ : ℝ → Measure ℝ} {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hkl : KallenLehmann σ ρ) (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ} (hb : SpecBottom ρ M2)
    (hσ : σ 0 = rateMeasure (X.time 1) (P0 T u)) :
    0 < M2 ∧ X.gap ≤ Real.sqrt M2
      ∧ (∀ t, 0 ≤ t → ‖X.time t (P0 T u)‖ ≤ Real.exp (-(Real.sqrt M2 * t)) * ‖P0 T u‖)
      ∧ Tendsto (fun τ => -Real.log ((inner ℂ (P0 T u) (X.time τ (P0 T u))).re) / τ) atTop
          (𝓝 (Real.sqrt M2))
      ∧ ∀ p2, 0 ≤ p2 → Real.sqrt p2 < shell M2 p2 :=
  clay_zero_momentum X (P0 T u) (inner_vac_P0 T hu) hkl hρ0 hb hσ.symm

/-- **The free field of mass `m > 0` meets the template with the support clause**, `ρ = δ_{m²}`.
DERIVED: `0` the sign of `m²`. -/
theorem free_klTemplate' {m2 : ℝ} (hm : 0 < m2) : KLTemplate' (freeRate m2) := by
  refine ⟨Measure.dirac m2, inferInstance, ?_, free_kallenLehmann m2⟩
  exact (dirac_eq_zero_iff_not_mem measurableSet_Iic).mpr fun h => absurd h (not_le.mpr hm)

/-- **The support clause is not empty**: the massless free `ρ = δ_0` charges `s ≤ 0`.
DERIVED: `0` the massless point. -/
theorem massless_dirac_charges : (Measure.dirac (0 : ℝ)) (Iic 0) ≠ 0 := by
  rw [Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Iic (0 : ℝ) from le_refl (0 : ℝ))]
  exact one_ne_zero

end

end MassGap.ShellMomentum

#print axioms MassGap.ShellMomentum.inner_opS
#print axioms MassGap.ShellMomentum.opS_mul
#print axioms MassGap.ShellMomentum.opS_eq_one
#print axioms MassGap.ShellMomentum.opS_Omega
#print axioms MassGap.ShellMomentum.opS_commute_opT
#print axioms MassGap.ShellMomentum.kernF_spShift
#print axioms MassGap.ShellMomentum.inner_spT
#print axioms MassGap.ShellMomentum.spT_mul
#print axioms MassGap.ShellMomentum.spT_mul_neg
#print axioms MassGap.ShellMomentum.spT_neg_mul
#print axioms MassGap.ShellMomentum.commute_spT_stepT
#print axioms MassGap.ShellMomentum.commute_spT_timeT
#print axioms MassGap.ShellMomentum.spT_vacT
#print axioms MassGap.ShellMomentum.spT_gvecT
#print axioms MassGap.ShellMomentum.inner_gvecT_spT
#print axioms MassGap.ShellMomentum.observerSpatial
#print axioms MassGap.ShellMomentum.commute_starProjection
#print axioms MassGap.ShellMomentum.vecMeasure_split
#print axioms MassGap.ShellMomentum.rateMeasure_split
#print axioms MassGap.ShellMomentum.rateMeasure_zero_vec
#print axioms MassGap.ShellMomentum.commute_time_P0
#print axioms MassGap.ShellMomentum.zero_momentum_sector
#print axioms MassGap.ShellMomentum.zero_momentum_average
#print axioms MassGap.ShellMomentum.zeroMom_eq_self
#print axioms MassGap.ShellMomentum.P0_eq_zero_of_odd
#print axioms MassGap.ShellMomentum.P0_trivial
#print axioms MassGap.ShellMomentum.KLTemplate'.toKLTemplate
#print axioms MassGap.ShellMomentum.clay_zero_momentum_sector
#print axioms MassGap.ShellMomentum.free_klTemplate'
#print axioms MassGap.ShellMomentum.massless_dirac_charges
#print axioms MassGap.ShellMomentum.spT_zero
#print axioms MassGap.ShellMomentum.norm_U_le
#print axioms MassGap.ShellMomentum.inner_vac_P0
#print axioms MassGap.ShellMomentum.isClosed_zeroMom
