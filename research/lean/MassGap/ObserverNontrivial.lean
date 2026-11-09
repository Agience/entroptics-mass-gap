import Mathlib
import MassGap.ClayFull
import MassGap.ClaySplitThreePoint

/-!
# MassGap.ObserverNontrivial — the non-triviality inputs, and the Clay statement on the local composite

## The two non-triviality inputs

`ClayFull.clayFullAt_of_observer` takes two non-triviality statements about the observer's limit:

* `ContinuumFlow.FlowConnectedNonzero`: a margin monomial `Q` with `S(θQ ∪ Q) − S(Q)² ≠ 0`;
* `ClayFull.NonGaussian`: decaying `g, h, k` with a non-zero connected three-point function `cum3` of
  `X.O`. It asks for the third cumulant, not for some cumulant of order at least three.

Both are statements about a limit along `ultra` of Wilson expectations at the dyadic couplings. Each
follows from one lattice statement with a uniform lower bound eventually in the step:

* `flowConnectedNonzero_of_lattice`: under `UniformBoundF`, if
  `|ν_k(θX_Q X_Q) − ν_k(X_Q)²| ≥ c > 0` eventually along `atTop`, then `FlowConnectedNonzero`.
* `schwSFM_decOfTest`: at compactly supported test functions `schwSFM` is `contSF`; the cut-offs are
  eventually the functions themselves (`eventually_cut_decOfTest`).
* `nonGaussian_of_lattice`: for linked data whose functional is `schwSFM`, under `UniformBoundF`, if the
  lattice connected three-point function `latCum3` at three test functions is eventually at least
  `c > 0` in absolute value, then `NonGaussian`.

The lattice lower bounds are not proved here.

## The Clay statement on the local composite

`ClayFullT` supersedes `ClayFull` (refuted by `ObserverAxioms.not_clayFull`) and
`ObserverAxioms.ClayFullAtSpan`. The Osterwalder–Schrader clauses are stated for Clay's objects, the
Schwinger functions `contS (Renorm.connected Z)` of the local composite. A smeared flowed field is
reflection positive only beyond its reach. The flowed observer `X` is the aperture: it carries the
Wilson states (`X.SM = schwSFM`) and the Hamiltonian gap, and `LinkT` embeds the local composite into
its Hilbert space. `ClayFullTAt` asks for:

* the observer's functional and `HamiltonianGap X.base`;
* the link `LinkT`: `⟪w P, w Q⟫ = S_Z(θP ∪ Q)`, the dyadic shift as `X.base.time`, the two-point kernel
  converging to an asymptotically free `G`, and the cross inner product `⟪w P, X.cvec Q⟫ = mixSF(θP ∪ Q)`
  with `mixLat` converging along `ultra`;
* on the local Schwinger functions with fields in a class `DL ∋ X.O`:
  * OS0 on `𝓢(ℝ⁴)ⁿ` with one growth pair for the class (`LocalOS0`). This asks `DL` to be bounded;
  * OS1 (`LocalOS1`);
  * `O(4)` tensor covariance (`LocalTensorCov`) of a Yang–Mills tensor class (`YMTensorClass`): a
    rank-four field with `T_{μνμν} = plaqField((μ, ν), 0)`. A tensor field of rank `p` is a family indexed by
    `Fin p → Fin 4`, and the covariance reads `S(T_α; f ∘ A) = ∑_β ∏ A_{β α} S(T_β; f)`. At rank `0` this is
    invariance (`localTensorCov_rank0`);
  * OS2 at margin `0` (`LocalOS2`) and OS3 (`LocalOS3`);
* the reconstruction space `HL`, the closure of the span of the vectors of `DL`-monomials, which is
  dense by construction. It holds the vacuum, the dyadic shifts keep it, it has the gap, and it holds a
  non-zero vector orthogonal to the vacuum;
* a non-zero connected three-point function of the local composite (`LocalNonGaussian`).

What transfers (`clayFullTAt_of_link`): OS2 at margin `0` from the link (`localOS2_of_inner`), OS3 at every
renormalisation (`localOS3`), shift invariance of `HL` (`time_mem_HL`) and the gap on `HL` (`gap_HL`).
`clayFullTAt_of_observer` adds the functional (by definition) and the Hamiltonian gap
(`observer_hamiltonianGap`) for the observer's linked data.
-/

noncomputable section

namespace MassGap.ObserverNontrivial

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 1. The connected flowed two-point function from a lattice lower bound -/

/-- **`FlowConnectedNonzero` from a lattice lower bound.** Under `UniformBoundF` both readings
converge along `ultra`, which is finer than `atTop`; a lower bound `c > 0` on the absolute value
eventually along `atTop` passes to the limit.

DERIVED: `0` the excluded value and the sign of `c`; `2` the square of the one-point reading. -/
theorem flowConnectedNonzero_of_lattice (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (τ : Fin 4) (r : ℝ) (Q : MarginMono N τ r) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ k in atTop, c ≤ |latSF hN Φ k (pairFam τ Q.1 Q.1)
      - latSF hN Φ k (pairFam τ (emptyMargin N τ r).1 Q.1) ^ 2|) :
    FlowConnectedNonzero hN Φ τ r := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have h1 := tendsto_contSF hN Φ hB (pairFam τ Q.1 Q.1)
  have h2 := tendsto_contSF hN Φ hB (pairFam τ (emptyMargin N τ r).1 Q.1)
  have hT := (h1.sub (h2.pow 2)).abs
  have hle := ge_of_tendsto hT (h.filter_mono ultra_le)
  refine ⟨Q, fun h0 => ?_⟩
  have e : contSF hN Φ (pairFam τ Q.1 Q.1) - contSF hN Φ (pairFam τ (emptyMargin N τ r).1 Q.1) ^ 2
      = 0 := h0
  rw [e, abs_zero] at hle
  linarith

#print axioms flowConnectedNonzero_of_lattice

/-! ## 2. `schwSFM` at compactly supported test functions -/

/-- **The cut-off of a test function is eventually the function**: `chi R = 1` on its support once
`R` exceeds its radius.

DERIVED: `1` the cut-off on the ball; `0` the vanishing value. -/
theorem eventually_cut_decOfTest (f : TestFn) : ∀ᶠ R : ℕ in atTop, cut (decOfTest f) R = f := by
  obtain ⟨R0, M, hRM⟩ := f.2
  filter_upwards [Filter.eventually_ge_atTop ⌈R0⌉₊] with R hR
  refine Subtype.ext (funext (fun y => ?_))
  show chi R y * f.1 y = f.1 y
  by_cases h0 : f.1 y = 0
  · rw [h0, mul_zero]
  · have hy : ‖y‖ ≤ R := by
      refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg R)).mpr (fun j => ?_)
      rw [Real.norm_eq_abs]
      have h1 := hRM.2.2 y h0 j
      have h3 : R0 ≤ (⌈R0⌉₊ : ℝ) := Nat.le_ceil _
      have h4 : (⌈R0⌉₊ : ℝ) ≤ R := by exact_mod_cast hR
      linarith
    rw [chi_eq_one hy, one_mul]

#print axioms eventually_cut_decOfTest

/-- **`schwSFM` at test functions is `contSF`**: the cut-offs are eventually the test functions, so
the limit in the cut-off is attained.

DERIVED: no numeral. -/
theorem schwSFM_decOfTest (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {ι : Type}
    [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (f : ι → TestFn) :
    schwSFM hN W D hD O (fun i => decOfTest (f i))
      = contSF hN (energy0 W D hD) (fun i => (O i, f i)) := by
  have hev : ∀ᶠ R : ℕ in atTop, (fun i => (O i, cut (decOfTest (f i)) R)) = (fun i => (O i, f i)) := by
    have hall : ∀ᶠ R : ℕ in atTop, ∀ i, cut (decOfTest (f i)) R = f i :=
      Filter.eventually_all.mpr (fun i => eventually_cut_decOfTest (f i))
    filter_upwards [hall] with R hR
    funext i
    rw [hR i]
  have hT : Tendsto (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O i, cut (decOfTest (f i)) R)))
      atTop (𝓝 (contSF hN (energy0 W D hD) (fun i => (O i, f i)))) :=
    tendsto_const_nhds.congr' (hev.mono (fun R hR => (congrArg (contSF hN (energy0 W D hD)) hR).symm))
  exact hT.limUnder_eq

#print axioms schwSFM_decOfTest

/-! ## 3. The connected three-point function from a lattice lower bound -/

/-- The lattice reading of `n` insertions of `O` at the test functions `f`.

DERIVED: no numeral. -/
def latN (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N)) (k : ℕ) {n : ℕ}
    (f : Fin n → TestFn) : ℝ :=
  latSF hN Φ k (fun i => (O, f i))

/-- **The lattice connected three-point function** of `O` at `f, g, h`, the expression of `cum3`.

DERIVED: `1`, `2`, `3` the orders; `2` the cumulant coefficient. -/
def latCum3 (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N)) (k : ℕ) (f g h : TestFn) : ℝ :=
  latN hN Φ O k ![f, g, h]
    - latN hN Φ O k ![f, g] * latN hN Φ O k ![h]
    - latN hN Φ O k ![f, h] * latN hN Φ O k ![g]
    - latN hN Φ O k ![g, h] * latN hN Φ O k ![f]
    + 2 * latN hN Φ O k ![f] * latN hN Φ O k ![g] * latN hN Φ O k ![h]

/-- The continuum reading of `n` insertions of `O`.

DERIVED: no numeral. -/
def contN (hN : N ≠ 0) (Φ : Flow N) (O : LField (MassGap.SUN.SU N)) {n : ℕ} (f : Fin n → TestFn) : ℝ :=
  contSF hN Φ (fun i => (O, f i))

/-- A family of decaying functions of test functions is `decOfTest` of the family.

DERIVED: `1`, `2`, `3` the lengths. -/
theorem vec3_decOfTest (f g h : TestFn) :
    (![decOfTest f, decOfTest g, decOfTest h] : Fin 3 → Decaying) = fun i => decOfTest (![f, g, h] i) := by
  funext i
  fin_cases i <;> rfl

/-- DERIVED: `2` the length. -/
theorem vec2_decOfTest (f g : TestFn) :
    (![decOfTest f, decOfTest g] : Fin 2 → Decaying) = fun i => decOfTest (![f, g] i) := by
  funext i
  fin_cases i <;> rfl

/-- DERIVED: `1` the length. -/
theorem vec1_decOfTest (f : TestFn) :
    (![decOfTest f] : Fin 1 → Decaying) = fun i => decOfTest (![f] i) := by
  funext i
  fin_cases i
  rfl

/-- **`NonGaussian` from a lattice lower bound.** For linked data whose functional is `schwSFM` of
the energy density, at test functions `f, g, h`: `cum3` is the `ultra` limit of `latCum3`
(`schwSFM_decOfTest`, `tendsto_contSF`), and a lower bound `c > 0` on `|latCum3|` eventually along
`atTop` keeps it away from `0`.

DERIVED: `0` the sign of `c` and the excluded value; `1`, `2`, `3` the orders. -/
theorem nonGaussian_of_lattice (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      X.SM O g = schwSFM hN W D hD O g)
    (hB : UniformBoundF hN (energy0 W D hD)) (f g h : TestFn) {c : ℝ} (hc : 0 < c)
    (hlat : ∀ᶠ k in atTop, c ≤ |latCum3 hN (energy0 W D hD) X.O k f g h|) : NonGaussian X := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  set Φ := energy0 W D hD with hΦ
  have hS : ∀ {n : ℕ} (u : Fin n → TestFn),
      X.SM (fun _ : Fin n => X.O) (fun i => decOfTest (u i)) = contN hN Φ X.O u := fun u => by
    rw [hSM, schwSFM_decOfTest]
    rfl
  have hL : ∀ {n : ℕ} (u : Fin n → TestFn),
      Tendsto (fun k => latN hN Φ X.O k u) (ultra : Filter ℕ) (𝓝 (contN hN Φ X.O u)) :=
    fun u => tendsto_contSF hN Φ hB (fun i => (X.O, u i))
  have hcum : cum3 X (decOfTest f) (decOfTest g) (decOfTest h)
      = contN hN Φ X.O ![f, g, h]
        - contN hN Φ X.O ![f, g] * contN hN Φ X.O ![h]
        - contN hN Φ X.O ![f, h] * contN hN Φ X.O ![g]
        - contN hN Φ X.O ![g, h] * contN hN Φ X.O ![f]
        + 2 * contN hN Φ X.O ![f] * contN hN Φ X.O ![g] * contN hN Φ X.O ![h] := by
    unfold cum3
    rw [vec3_decOfTest, vec2_decOfTest f g, vec2_decOfTest f h, vec2_decOfTest g h,
      vec1_decOfTest f, vec1_decOfTest g, vec1_decOfTest h, hS, hS, hS, hS, hS, hS, hS]
  have hT : Tendsto (fun k => |latCum3 hN Φ X.O k f g h|) (ultra : Filter ℕ)
      (𝓝 |cum3 X (decOfTest f) (decOfTest g) (decOfTest h)|) := by
    rw [hcum]
    unfold latCum3
    exact ((((((hL ![f, g, h]).sub ((hL ![f, g]).mul (hL ![h]))).sub
      ((hL ![f, h]).mul (hL ![g]))).sub ((hL ![g, h]).mul (hL ![f]))).add
      (((tendsto_const_nhds.mul (hL ![f])).mul (hL ![g])).mul (hL ![h])))).abs
  have hle := ge_of_tendsto hT (hlat.filter_mono ultra_le)
  refine ⟨decOfTest f, decOfTest g, decOfTest h, fun h0 => ?_⟩
  rw [h0, abs_zero] at hle
  linarith

#print axioms nonGaussian_of_lattice

/-! ## 4. Tensor fields and their `O(4)` covariance -/

/-- **A tensor field of rank `p`**: one field for each component `Fin p → Fin 4`.

DERIVED: `4` the dimension. -/
def TensorField (N : ℕ) : Type := Σ p : ℕ, (Fin p → Fin 4) → LField (MassGap.SUN.SU N)

/-- **The transformation coefficient** of the components `α ← β` under `A`: `∏ⱼ A_{βⱼ αⱼ}`.

DERIVED: `4` the dimension. -/
def tcoef (A : Matrix (Fin 4) (Fin 4) ℝ) {p : ℕ} (α β : Fin p → Fin 4) : ℝ :=
  ∏ j, A (β j) (α j)

/-- An orthogonal matrix has `Aᵀ A = 1`.

DERIVED: `4` the dimension. -/
theorem transpose_mul_self_of_orth {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Aᵀ * A = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hA
  simpa using hA

#print axioms transpose_mul_self_of_orth

/-- **The tensor class of Yang–Mills**: its components lie in the class `DL`, and it holds a
rank-four tensor field whose `(μ, ν, μ, ν)` component, `μ < ν`, is the plaquette density at the
origin in the plane `(μ, ν)`, the lattice `tr F_{μν} F_{μν}`; at `(0, 1)` it is `plaqField q0`.

DERIVED: `4` the rank and the dimension; `0`, `1` the plane of `q0`. -/
def YMTensorClass (DL : Set (LField (MassGap.SUN.SU N))) (TD : Set (TensorField N)) : Prop :=
  (∀ T ∈ TD, ∀ α, T.2 α ∈ DL)
    ∧ ∃ T : (Fin 4 → Fin 4) → LField (MassGap.SUN.SU N), (⟨4, T⟩ : TensorField N) ∈ TD
        ∧ T ![0, 1, 0, 1] = ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0
        ∧ ∀ μ ν : Fin 4, μ < ν →
            T ![μ, ν, μ, ν] = ObserverEnergyMoments.plaqField ((μ, ν), (0 : ISite))

/-! ## 5. The Osterwalder–Schrader axioms of the local composite -/

section Local

/-- **OS0 for the local composite on `𝓢(ℝ⁴)ⁿ`**: for every `n` fields of `DL`, a continuous
multilinear map on Euclidean Schwartz functions with the linear growth bound, at one `α`, `γ` for the
class, equal to the local Schwinger function `contS (Renorm.connected Z)` wherever the Schwartz
functions restrict to test functions.

DERIVED: `8192`, `5` the gauge of `OSDataS.growth`; `2` the Euclidean exponent and the square of
the factorial. -/
def LocalOS0 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (DL : Set (LField (MassGap.SUN.SU N))) : Prop :=
  ∃ α γ : ℝ, ∀ (n : ℕ) (O : Fin n → LField (MassGap.SUN.SU N)), (∀ i, O i ∈ DL) →
    ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin n => MassGap.WightmanData.TestFn) ℝ,
      (∀ (φ : Fin n → MassGap.WightmanData.TestFn) (f : Fin n → TestFn),
          (∀ i y, φ i (WithLp.toLp 2 y) = (f i).1 y) →
            T φ = contS hN (Renorm.connected hN Z) (fun i => (O i, f i)))
        ∧ ∀ φ, |T φ| ≤ α * γ ^ n * (n.factorial : ℝ) ^ 2 * ∏ i, 8192 * e4Norm 5 (φ i)

/-- **OS1 for the local composite**: invariance under every real translation, fields in `DL`.

DERIVED: `4` the dimension. -/
def LocalOS1 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (DL : Set (LField (MassGap.SUN.SU N))) : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → SField N), (∀ i, (F i).1 ∈ DL) → ∀ v : Fin 4 → ℝ,
    contS hN (Renorm.connected hN Z) (fun i => ((F i).1, (F i).2.translate v))
      = contS hN (Renorm.connected hN Z) F

/-- **`O(4)` covariance of the local tensor fields of `TD`.** For every orthogonal `A`, every
family of tensor fields of `TD`, components `α` and uniformly continuous test functions `f`:
`S((Tᵢ)_{αᵢ}; fᵢ ∘ A) = ∑_β ∏ᵢ tcoef A αᵢ βᵢ · S((Tᵢ)_{βᵢ}; fᵢ)`, which is the law of
`φ'_μ(y) = A_{μν} φ_ν(A⁻¹ y)` equal to that of `φ`. At rank `0` it is `O(4)` invariance
(`localTensorCov_rank0`).

DERIVED: `4` the dimension. -/
def LocalTensorCov (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (TD : Set (TensorField N)) : Prop :=
  ∀ A : Matrix (Fin 4) (Fin 4) ℝ, A ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (T : ι → TensorField N), (∀ i, T i ∈ TD) →
      ∀ (α : (i : ι) → Fin (T i).1 → Fin 4) (f : ι → TestFn), (∀ i, UniformContinuous (f i).1) →
        contS hN (Renorm.connected hN Z) (fun i => ((T i).2 (α i), rotTest A (f i)))
          = ∑ β : ((i : ι) → Fin (T i).1 → Fin 4),
              (∏ i, tcoef A (α i) (β i))
                * contS hN (Renorm.connected hN Z) (fun i => ((T i).2 (β i), f i))

/-- **At rank `0` tensor covariance is invariance**: the only component is the empty one, with
coefficient `1`.

DERIVED: `0` the rank; `1` the coefficient. -/
theorem localTensorCov_rank0 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (TD : Set (TensorField N)) (hT : LocalTensorCov hN Z TD) {A : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (O : ι → LField (MassGap.SUN.SU N)) (hO : ∀ i, (⟨0, fun _ => O i⟩ : TensorField N) ∈ TD)
    (f : ι → TestFn) (hf : ∀ i, UniformContinuous (f i).1) :
    contS hN (Renorm.connected hN Z) (fun i => (O i, rotTest A (f i)))
      = contS hN (Renorm.connected hN Z) (fun i => (O i, f i)) := by
  have h := hT A hA ι (fun i => ⟨0, fun _ => O i⟩) hO (fun _ => Fin.elim0) f hf
  have hsum : ∀ (F : ((i : ι) → Fin 0 → Fin 4) → ℝ),
      ∑ β : ((i : ι) → Fin 0 → Fin 4), F β = F (fun _ => Fin.elim0) := fun F =>
    Fintype.sum_eq_single _ (fun β hβ => absurd (funext (fun i => funext (fun j => j.elim0))) hβ)
  have e := h.trans (hsum _)
  simpa [tcoef] using e

#print axioms localTensorCov_rank0

/-- **OS2 for the local composite at margin `0`**: on separated positive-time monomials of every
positive separation with fields in `DL`, `0 ≤ ∑ c_P c_Q S_Z(θP ∪ Q)`.

DERIVED: `0` the sign; `4` in `Fin 4` the dimension. -/
def LocalOS2 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4)
    (DL : Set (LField (MassGap.SUN.SU N))) : Prop :=
  ∀ s : Finset (ContinuumSep.SepMono N τ), (∀ P ∈ s, ∀ i, (P.1.2 i).1 ∈ DL) →
    ∀ c : ContinuumSep.SepMono N τ → ℝ,
      0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * ContinuumSep.kernSep hN (Renorm.connected hN Z) τ P Q

/-- **OS3 for the local composite**: permutation symmetry, every reindexing.

DERIVED: no numeral. -/
def LocalOS3 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (F : ι → SField N),
    contS hN (Renorm.connected hN Z) (F ∘ e) = contS hN (Renorm.connected hN Z) F

/-- **OS3 holds for every renormalisation** (`ClaySplitThreePoint.contS_comp_equiv`).

DERIVED: no numeral. -/
theorem localOS3 (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) : LocalOS3 hN Z :=
  fun _ _ _ _ e F => ClaySplitThreePoint.contS_comp_equiv hN (Renorm.connected hN Z) e F

#print axioms localOS3

/-- The local reading of `n` insertions of `O`.

DERIVED: no numeral. -/
def contL (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (O : LField (MassGap.SUN.SU N))
    {n : ℕ} (f : Fin n → TestFn) : ℝ :=
  contS hN (Renorm.connected hN Z) (fun i => (O, f i))

/-- **Non-Gaussian, for the local composite**: some connected three-point function of the local
composite of `O` is non-zero.

DERIVED: `0` the Gaussian value; `1`, `2`, `3` the orders; `2` the cumulant coefficient. -/
def LocalNonGaussian (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ f g h : TestFn,
    contL hN Z O ![f, g, h] - contL hN Z O ![f, g] * contL hN Z O ![h]
      - contL hN Z O ![f, h] * contL hN Z O ![g] - contL hN Z O ![g, h] * contL hN Z O ![f]
      + 2 * contL hN Z O ![f] * contL hN Z O ![g] * contL hN Z O ![h] ≠ 0

end Local

/-! ## 6. The link: local vectors in the observer's space, and the mixed reading -/

/-- **The mixed lattice reading of step `k`**: the factors of `P` reflected and renormalised by
`Renorm.connected Z`, with their field-strength factors, the factors of `Q` flowed by `Φ`:
`∏ᵢ Z_k(θOᵢ) · ν_k(∏ᵢ smear(θOᵢ − ν_k(θOᵢ)) · ∏ⱼ smear(Φ_k O'ⱼ))`.

DERIVED: `0` the excluded colour count; `4` in `Fin 4` the dimension. -/
def mixLat (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (Φ : Flow N) (τ : Fin 4) (k : ℕ)
    (P Q : Mono N) : ℝ :=
  (Renorm.connected hN Z).pref k (fun i => SField.refl τ (P.2 i))
    * latSk hN k (Sum.elim (fun i => (Renorm.connected hN Z).field k (SField.refl τ (P.2 i)))
        (fun j => Φ.field k (Q.2 j)))

/-- **The mixed reading** `S(θP_local ∪ Q_flowed)`: the `ultra` limit of `mixLat`.

DERIVED: `0` the excluded colour count. -/
def mixSF (hN : N ≠ 0) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (Φ : Flow N) (τ : Fin 4)
    (P Q : Mono N) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => mixLat hN Z Φ τ k P Q)

/-- **The link of the local composite to the observer's space.** The vectors `w P` of the separated
positive-time monomials of `Renorm.connected Z` lie in `X.base.H` with
`⟪w P, w Q⟫ = S_Z(θP ∪ Q)` and the dyadic shift acting as `X.base.time a_m`. The lattice two-point
kernel of `X.O` converges to `G(|p − q|)` with `AFShortDistance G`. Against every compact margin
monomial `Q` of `D`, the mixed reading converges along `ultra` and
`⟪w P, X.cvec Q⟫ = mixSF(θP ∪ Q)`.

DERIVED: `4` in `Fin 4` the dimension. -/
def LinkT (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (G : ℝ → ℝ)
    (w : ContinuumSep.SepMono N τ → X.base.H) : Prop :=
  (∀ P Q : ContinuumSep.SepMono N τ,
      inner ℂ (w P) (w Q) = (ContinuumSep.kernSep hN (Renorm.connected hN Z) τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : ContinuumSep.SepMono N τ),
        w (ContinuumSep.SepMono.shift hN τ m P) = X.base.time (dySpacing N m) (w P))
    ∧ ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ X.O
        (fun p q => G (ContinuumNontrivial.eDist p q))
    ∧ ShortDistanceY.AFShortDistance G
    ∧ ∀ (P : ContinuumSep.SepMono N τ) (Q : MarginMonoD N D τ r),
        Tendsto (fun k => mixLat hN Z (energy0 W D hD) τ k P.1 Q.1.1) (ultra : Filter ℕ)
            (𝓝 (mixSF hN Z (energy0 W D hD) τ P.1 Q.1.1))
          ∧ inner ℂ (w P) (X.cvec Q) = (mixSF hN Z (energy0 W D hD) τ P.1 Q.1.1 : ℂ)

/-- DERIVED: no numeral. -/
theorem localLink_of_linkT (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) {Z : ℕ → LField (MassGap.SUN.SU N) → ℝ} {G : ℝ → ℝ}
    {w : ContinuumSep.SepMono N τ → X.base.H} (h : LinkT hN W D hD X Z G w) : LocalLink hN X :=
  ⟨Z, G, w, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

#print axioms localLink_of_linkT

section Reconstruction

variable {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}

/-- The vectors of the separated monomials with fields in `DL`.

DERIVED: no numeral. -/
def genL (X : OSDataSLinked N D τ r) (w : ContinuumSep.SepMono N τ → X.base.H)
    (DL : Set (LField (MassGap.SUN.SU N))) : Set X.base.H :=
  {u | ∃ P : ContinuumSep.SepMono N τ, (∀ i, (P.1.2 i).1 ∈ DL) ∧ w P = u}

/-- **The reconstruction space of the local composite**: the closure of the complex span of the
vectors of `DL`-monomials. It is dense in itself by construction; no density in `X.base.H` is
asked.

DERIVED: no numeral. -/
def HL (X : OSDataSLinked N D τ r) (w : ContinuumSep.SepMono N τ → X.base.H)
    (DL : Set (LField (MassGap.SUN.SU N))) : Submodule ℂ X.base.H :=
  (Submodule.span ℂ (genL X w DL)).topologicalClosure

/-- **The dyadic time shifts keep the local reconstruction space**: they map the generating
vectors to generating vectors (the shift moves only test functions) and are continuous.

DERIVED: no numeral. -/
theorem time_mem_HL (hN : N ≠ 0) (X : OSDataSLinked N D τ r)
    (w : ContinuumSep.SepMono N τ → X.base.H) (DL : Set (LField (MassGap.SUN.SU N)))
    (hsh : ∀ (m : ℕ) (P : ContinuumSep.SepMono N τ),
      w (ContinuumSep.SepMono.shift hN τ m P) = X.base.time (dySpacing N m) (w P))
    (m : ℕ) : ∀ u ∈ HL X w DL, X.base.time (dySpacing N m) u ∈ HL X w DL := by
  intro u hu
  set L : X.base.H →L[ℂ] X.base.H := X.base.time (dySpacing N m) with hL
  have hS : Submodule.span ℂ (genL X w DL)
      ≤ (HL X w DL).comap (L : X.base.H →ₗ[ℂ] X.base.H) := by
    rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    show L (w P) ∈ HL X w DL
    rw [hL, ← hsh m P]
    exact Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨ContinuumSep.SepMono.shift hN τ m P, fun i => hP i, rfl⟩)
  have hC : IsClosed (((HL X w DL).comap (L : X.base.H →ₗ[ℂ] X.base.H) : Submodule ℂ X.base.H)
      : Set X.base.H) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  exact Submodule.topologicalClosure_minimal _ hS hC hu

#print axioms time_mem_HL

/-- **The gap on the local reconstruction space**: the observer's gap, restricted.

DERIVED: `0` the vanishing pairing and the time origin. -/
theorem gap_HL (X : OSDataSLinked N D τ r) (w : ContinuumSep.SepMono N τ → X.base.H)
    (DL : Set (LField (MassGap.SUN.SU N))) :
    ∀ u ∈ HL X w DL, inner ℂ X.base.vac u = 0 → ∀ t : ℝ, 0 ≤ t →
      ‖X.base.time t u‖ ≤ Real.exp (-(X.base.gap * t)) * ‖u‖ :=
  fun u _ hu t ht => X.base.time_gap t ht u hu

#print axioms gap_HL

/-- **OS2 of the local composite at margin `0` from the link**: `∑ c_P c_Q S_Z(θP ∪ Q)` is
`‖∑ c_P w P‖²`.

DERIVED: `0` the sign. -/
theorem localOS2_of_inner (hN : N ≠ 0) (X : OSDataSLinked N D τ r)
    {Z : ℕ → LField (MassGap.SUN.SU N) → ℝ} {w : ContinuumSep.SepMono N τ → X.base.H}
    (hin : ∀ P Q : ContinuumSep.SepMono N τ,
      inner ℂ (w P) (w Q) = (ContinuumSep.kernSep hN (Renorm.connected hN Z) τ P Q : ℂ))
    (DL : Set (LField (MassGap.SUN.SU N))) : LocalOS2 hN Z τ DL := by
  intro s _ c
  set v : X.base.H := ∑ P ∈ s, (c P : ℂ) • w P with hv
  have e : inner ℂ v v = ((∑ P ∈ s, ∑ Q ∈ s,
      c P * c Q * ContinuumSep.kernSep hN (Renorm.connected hN Z) τ P Q : ℝ) : ℂ) := by
    simp only [hv, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hin,
      Complex.conj_ofReal]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  have h0 := inner_self_nonneg (𝕜 := ℂ) (x := v)
  rw [e] at h0
  simpa using h0

#print axioms localOS2_of_inner

end Reconstruction

/-! ## 7. The Clay statement on the local composite -/

/-- **The Clay statement at one lattice construction, on the local composite.** The observer's
linked data `X` (its functional the Wilson states' `schwSFM`, read through the aperture `W` on `D`)
with its Hamiltonian gap. A local composite `Renorm.connected Z` linked to `X` (`LinkT`), whose
class `DL` holds `X.O` and whose tensor class `TD` is Yang–Mills. On the local Schwinger functions:
OS0 on `𝓢(ℝ⁴)ⁿ`, OS1, `O(4)` tensor covariance, OS2 at margin `0`, OS3. The reconstruction space `HL`
(the closure of the span of the `DL`-vectors) holds the vacuum, is kept by the dyadic time shifts, has
the gap, and holds a non-zero vector orthogonal to the vacuum. A connected three-point function of the
local composite is non-zero.

DERIVED: `0` the vanishing pairing, the zero vector and the time origin; `4` in `Fin 4` the
dimension. -/
def ClayFullTAt (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) : Prop :=
  ∃ (τ : Fin 4) (r : ℝ) (X : OSDataSLinked N D τ r) (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (G : ℝ → ℝ) (w : ContinuumSep.SepMono N τ → X.base.H) (DL : Set (LField (MassGap.SUN.SU N)))
    (TD : Set (TensorField N)),
    (∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
        X.SM O g = schwSFM hN W D hD O g)
      ∧ HamiltonianGap X.base ∧ LinkT hN W D hD X Z G w ∧ X.O ∈ DL
      ∧ LocalOS0 hN Z DL ∧ LocalOS1 hN Z DL ∧ YMTensorClass DL TD ∧ LocalTensorCov hN Z TD
      ∧ LocalOS2 hN Z τ DL ∧ LocalOS3 hN Z
      ∧ X.base.vac ∈ HL X w DL
      ∧ (∀ m : ℕ, ∀ u ∈ HL X w DL, X.base.time (dySpacing N m) u ∈ HL X w DL)
      ∧ (∀ u ∈ HL X w DL, inner ℂ X.base.vac u = 0 → ∀ t : ℝ, 0 ≤ t →
          ‖X.base.time t u‖ ≤ Real.exp (-(X.base.gap * t)) * ‖u‖)
      ∧ (∃ u ∈ HL X w DL, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
      ∧ LocalNonGaussian hN Z X.O

/-- **The Clay Yang–Mills statement for `SU(N)`, every `N ≥ 2`, on the local composite.** It
supersedes `ClayFull` (refuted, `ObserverAxioms.not_clayFull`) and `ObserverAxioms.ClayFullAtSpan`.

DERIVED: `2` the least colour count; `4` in `Fin 4` the dimension. -/
def ClayFullT : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D),
    ClayFullTAt hN W D hD

/-- **What transfers.** Given the link, OS2 at margin `0` (`localOS2_of_inner`), OS3
(`localOS3`), the dyadic shift invariance of `HL` (`time_mem_HL`) and the gap on `HL` (`gap_HL`) are
proved. The inputs that remain are the functional and the Hamiltonian gap of `X`, the link, `X.O ∈ DL`,
OS0, OS1, the tensor class and its covariance, the vacuum in `HL`, a non-vacuum vector in `HL`, and
the local three-point function.

DERIVED: `0` the vanishing pairing and the zero vector; `4` in `Fin 4` the dimension. -/
theorem clayFullTAt_of_link (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      X.SM O g = schwSFM hN W D hD O g)
    (hHam : HamiltonianGap X.base) {Z : ℕ → LField (MassGap.SUN.SU N) → ℝ} {G : ℝ → ℝ}
    {w : ContinuumSep.SepMono N τ → X.base.H} (hL : LinkT hN W D hD X Z G w)
    {DL : Set (LField (MassGap.SUN.SU N))} (hODL : X.O ∈ DL) {TD : Set (TensorField N)}
    (h0 : LocalOS0 hN Z DL) (h1 : LocalOS1 hN Z DL) (hTD : YMTensorClass DL TD)
    (hcov : LocalTensorCov hN Z TD) (hvac : X.base.vac ∈ HL X w DL)
    (hnt : ∃ u ∈ HL X w DL, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hNG : LocalNonGaussian hN Z X.O) : ClayFullTAt hN W D hD :=
  ⟨τ, r, X, Z, G, w, DL, TD, hSM, hHam, hL, hODL, h0, h1, hTD, hcov,
    localOS2_of_inner hN X hL.1 DL, localOS3 hN Z, hvac,
    fun m => time_mem_HL hN X w DL hL.2.1 m, gap_HL X w DL, hnt, hNG⟩

#print axioms clayFullTAt_of_link

/-- **The observer's Hamiltonian gap**: for the observer's linked data on any non-negative class
with (E), the generator of the flowed time group is self-adjoint
(`ClayFull.observer_generator_isSelfAdjoint`), which gives `HamiltonianGap`.

DERIVED: `0` the signs and the excluded colour count; `1` the top of `ρ`; `4` in `Fin 4` the
dimension. -/
theorem observer_hamiltonianGap (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) :
    HamiltonianGap (observerOSDataSLinked hN W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1
      hg hNT).base :=
  hamiltonianGap_of_selfAdjoint _
    (observer_generator_isSelfAdjoint hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube)
      τ (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ))

#print axioms observer_hamiltonianGap

/-- **`ClayFullTAt` for the observer.** The observer's linked data supply the functional (by
definition) and the Hamiltonian gap (`observer_hamiltonianGap`); the open inputs are those of
`observerOSDataSLinked` and the local ones of `clayFullTAt_of_link`.

DERIVED: `0` the signs and the excluded colour count; `1` the top of `ρ`; `4` in `Fin 4` the
dimension. -/
theorem clayFullTAt_of_observer (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) (X : OSDataSLinked N D τ r)
    (hX : X = observerOSDataSLinked hN W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
    {Z : ℕ → LField (MassGap.SUN.SU N) → ℝ} {G : ℝ → ℝ}
    {w : ContinuumSep.SepMono N τ → X.base.H} (hLk : LinkT hN W D hD X Z G w)
    {DL : Set (LField (MassGap.SUN.SU N))} (hODL : X.O ∈ DL) {TD : Set (TensorField N)}
    (h0 : LocalOS0 hN Z DL) (h1 : LocalOS1 hN Z DL) (hTD : YMTensorClass DL TD)
    (hcov : LocalTensorCov hN Z TD) (hvac : X.base.vac ∈ HL X w DL)
    (hnt : ∃ u ∈ HL X w DL, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hNG : LocalNonGaussian hN Z X.O) : ClayFullTAt hN W D hD := by
  subst hX
  exact clayFullTAt_of_link hN W D hD _ (fun _ _ _ _ => rfl)
    (observer_hamiltonianGap hN W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT)
    hLk hODL h0 h1 hTD hcov hvac hnt hNG

#print axioms clayFullTAt_of_observer

end MassGap.ObserverNontrivial

end
