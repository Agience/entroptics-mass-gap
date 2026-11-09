import Mathlib
import MassGap.ShellDensity
import MassGap.ClayStatement

/-!
# MassGap.ShellLorentz — the Euclidean Källén–Lehmann form and the zero-momentum density

`ShellDensity.clay_zero_momentum_density` reads the Clay gap under the corrected identification
`hσ' : ZeroDensity τ (nu J u) (σ 0)`: the zero-momentum Källén–Lehmann sector is the density at `p = 0`
of the vector's rate × momentum measure. This module states the Euclidean Källén–Lehmann form of the
joint measure in the tree's terms, proves that a vector whose rate × momentum measure has this form satisfies `hσ'` (with the sector read from the
vector, not chosen), proves what `CovC` gives for a scalar composite (the `O(4)` invariance of its
Schwinger functions as forms on test functions) and that `O(4)` invariance of a function on `ℝ⁴` is
radiality, and names the one step between them as a template. No Minkowski continuation is used.
Declarations are in the namespace `MassGap.ShellLorentz`.

DERIVED: `Fin 4` the four-dimensional spacetime index.

## 1. `O(4)` invariance is radiality (proved)

`nsq x = Σ xᵢ²`; `Radial S`: `S x = S y` whenever `nsq x = nsq y`; `OrthInv S`: `S (R x) = S x` for
every `R ∈ O(4)`.

* `nsq_orth`: an orthogonal matrix keeps `nsq`.
* `house v = 1 − (2/(v·v)) v vᵀ`, the Householder reflection: `house_orth` (it is orthogonal) and
  `house_mulVec` (for `nsq x = nsq y`, `x ≠ y`, it maps `x` to `y`).
* `radial_iff_orthInv`: `Radial S ↔ OrthInv S`. This is the statement "O(4) covariance of a scalar
  two-point function means it depends only on `|x|`".

## 2. What `CovC` gives a scalar composite (proved)

`Scalar C i`: `C.rep R i = single i 1` for every `R ∈ O(4)` (an `O(4)` singlet, trivial under reflections as well as rotations).

* `covC_scalar`: under `CovC`, for every admissible family of scalar composites,
  `contC (fⱼ ∘ R) = contC (fⱼ)`. The limit of the rotated lattice readings is the one-term sum, and
  `contC` of the rotated family is that limit along the same ultrafilter. `ConvC` is not needed.
* `covC_twoPoint`: the two-point form `(f, h) ↦ contC ((i, f), (i, h))` of a scalar composite is
  `O(4)` invariant.

## 3. The Källén–Lehmann joint measure and its zero-momentum density (proved)

`psq p = Σ pⱼ²`. For a finite `ρ` on `s` and a continuous momentum profile `g ≥ 0`:

* `klSec ρ p²`: the sector `shell(·, p²)_* (ρ / (2 shell))`; `kallenLehmann_klSec`:
  `KallenLehmann (klSec ρ) ρ` (one `ρ` for every momentum, by construction).
* `klJoint τ ρ g`: the push-forward of `g(p) dλ(p) × dρ(s) / (2√(s + p²))` under
  `(p, s) ↦ (√(s + p²), p)`; the rate × momentum measure of a Källén–Lehmann superposition, each
  momentum on its shells. `windowed_klJoint`: the windowed rate integral is
  `∫_{B(0, ε)} ∫ g(p) f(√(s + p²)) dρ(s) / (2√(s + p²)) dλ(p)`.
* `klJoint_zeroDensity`: with `ρ (−∞, 0] = 0` and `σ 0` finite (`∫ dρ/(2√s) < ∞`),
  `ZeroDensity τ (klJoint τ ρ g) (klSec (g(0) ρ) 0)`. The inner integral is continuous at `p = 0` by
  dominated convergence (the weight `1/(2√(s + p²))` is below `1/(2√s)`), then
  `ShellDensity.avg_tendsto`. This generalises `ShellDensity.free_zeroDensity` from a point mass `ρ`
  to a finite `ρ`.
* `klJoint_bottom`: a rate bottom `a > 0` of `klJoint τ ρ g` with `g(0) ≠ 0` forces a bottom `b > 0`
  of `ρ`; `klWeight_fin`: such a bottom makes `σ 0` finite. So on the vacuum complement the finiteness
  of `σ 0` is read from the gap, not assumed.
* `klSec_laplaceRep`: each sector is a Laplace transform (`ShellMeasure.LaplaceRep`), so it feeds
  `ShellMeasure.shell_rate_of_kl`.

## 4. The connection to `clay_zero_momentum_density` (proved, under the template)

* `KLJointRep J u ρ`: `nu J u = klJoint τ ρ g` for a continuous `g` with `g(0) ≠ 0`. This is the
  Euclidean Källén–Lehmann theorem for the vector `u`, in the tree's terms; it is the single template
  of this module.
* `clay_zero_momentum_kl`: for `J` with time step `X.time 1`, `u` in the vacuum complement, finite `ρ`
  with `ρ (−∞, 0] = 0` and `SpecBottom ρ M2`, and `KLJointRep J u ρ`: `hσ'` holds with
  `σ = klSec (g(0) ρ)` (read from the vector: `g(0)` is its zero-momentum weight), and every conclusion
  of `clay_zero_momentum_density` follows: `σ 0 (−∞, X.gap) = 0`, `0 < M2`, `X.gap ≤ √M2`,
  `SpecBottom (σ 0) (√M2)`, band excess at every `p²`. `0 < M2` and the finiteness of `σ 0` are not
  hypotheses.

`DyadicDini` is not a hypothesis of `clay_zero_momentum_kl`: the template is stated on `nu`, which is
defined for every vector. It enters the derivation of the template (below), where the momentum
coordinate of `nu` has to be the momentum. `dyadicDini_of_holder`: a Hölder bound
`‖U(s eⱼ) u − u‖ ≤ L sᵅ`, `α > 0`, in each direction gives `DyadicDini` (the series is geometric).

## What is not proved

The template `KLJointRep` for the zero-momentum composite vectors is not discharged. The route from the
route's `CovC` to it, and where each step stands. Steps (b)–(d) are argued on paper and not formalised.

* (a) `CovC` ⇒ the scalar two-point form is `O(4)` invariant: proved (`covC_twoPoint`).
* (b) The form has a kernel, `contC((i, f), (i, h)) = ∫∫ f(x) h(y) S(x − y)` with `S` continuous off
  `0`: not in the tree (the composite Schwinger functions are limits of smeared lattice readings; a
  kernel needs the distribution to be a function away from coincident points). Given (b), invariance
  of the form gives `OrthInv S` on test functions separating points, and `radial_iff_orthInv` makes
  `S` radial: the second half is proved, the first is not built.
* (c) Radial + reflection positive ⇒ `S = ∫ Δ_s dρ(s)` (the Euclidean Källén–Lehmann theorem). Argued
  route: the four-dimensional Fourier transform `Ŝ(k) = F(k²)` is radial; reflection positivity in
  each time direction makes `F(k₀² + p²) = ∫ dμ_p(E)/(k₀² + E²)` (the Laplace representation
  `ShellMeasure.powT_laplaceRep` along the time axis, Fourier transformed); radiality makes this a
  Stieltjes transform `∫ dν(t)/(k² + t)` of one measure for all `p`, and uniqueness of the Stieltjes
  representation gives `μ_p = shell(·, p²)_* (ρ/(2 shell))` with one `ρ`. Mathlib at this pin has no
  Stieltjes inversion and no Bernstein–Widder theorem (searched, not exhaustively); not formalised.
* (d) From (c) to `nu J u = klJoint τ ρ |f̂|²` for the vector `u = φ(f)Ω`: the characteristic
  functions agree (`ShellDensity.inner_U_eq_momentum`, under `DyadicDini`) and a finite measure on
  rate × momentum is fixed by its Laplace–Fourier transform. The uniqueness step is not formalised
  here; `DyadicDini` for `φ(f)Ω` would follow from the Hölder bound of `dyadicDini_of_holder` for field vectors smeared with test functions in space; this is argued, not proved, and not argued for the composites here.

`clay_zero_momentum_kl` replaces the hypotheses `hkl` and `hσ'` of `clay_zero_momentum_density` by the single hypothesis `KLJointRep J u ρ`. `CovC` does not yet yield it.

## 5. Load tests (proved)

* `free_kl_zeroDensity`: the free field, `ρ = δ_{m²}`, `m² > 0`: the zero-momentum density is
  `g(0) δ_m / (2m) = g(0) · freeRate m² 0`, the sector of `ShellMeasure.free_kallenLehmann`.
* `aniso_not_radial`, `aniso_not_orthInv`: the anisotropic kernel `e^{−(2x₀² + x₁² + x₂² + x₃²)}` is not
  radial, hence not `O(4)` invariant: time and space scale differently, which no Källén–Lehmann form
  allows.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ShellLorentz

open Real Filter Topology MeasureTheory Set Matrix
open scoped NNReal ENNReal
open MassGap.BandShell (shell SpecBottom shell_nonneg)
open MassGap.ShellMeasure (rateMeasure KallenLehmann klWeight measurable_shell measurable_klWeight
  LaplaceRep freeRate free_kallenLehmann)
open MassGap.ShellGap (gap_rateBottom)
open MassGap.ShellJoint (JointData)
open MassGap.ShellTranslate (spatial)
open MassGap.ShellDensity (nu ZeroDensity windowed lam lam_ball avg_tendsto nu_Iio_prod
  clay_zero_momentum_density DyadicDini dy ej)
open MassGap.ObserverOSReconstructionS (OSDataS)

noncomputable section

/-! ## 1. `O(4)` invariance is radiality -/

/-- **The squared Euclidean length** `Σ xᵢ²`. DERIVED: `2` the square. -/
def nsq (x : Fin 4 → ℝ) : ℝ := ∑ i, x i ^ 2

/-- DERIVED: `2` the square. -/
theorem nsq_eq_dot (x : Fin 4 → ℝ) : nsq x = x ⬝ᵥ x := by
  simp only [nsq, dotProduct, sq]

/-- **A radial function**: equal values at equal Euclidean length. DERIVED: no numeral. -/
def Radial (S : (Fin 4 → ℝ) → ℝ) : Prop := ∀ x y, nsq x = nsq y → S x = S y

/-- **An `O(4)`-invariant function.** DERIVED: `4` the dimension. -/
def OrthInv (S : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∀ x, S (R *ᵥ x) = S x

/-- **An orthogonal matrix keeps the length.** DERIVED: `1` the identity. -/
theorem nsq_orth {R : Matrix (Fin 4) (Fin 4) ℝ} (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ)
    (x : Fin 4 → ℝ) : nsq (R *ᵥ x) = nsq x := by
  rw [mem_orthogonalGroup_iff'] at hR
  rw [nsq_eq_dot, nsq_eq_dot, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hR, vecMul_one]

/-- **The Householder reflection** `1 − (2/(v·v)) v vᵀ`. DERIVED: `1` the identity; `2` the
reflection (twice the projection). -/
def house (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := 1 - (2 / (v ⬝ᵥ v)) • vecMulVec v v

/-- **The Householder reflection is orthogonal.** DERIVED: `1` the identity; `2` as in `house`. -/
theorem house_orth (v : Fin 4 → ℝ) (hv : v ⬝ᵥ v ≠ 0) :
    house v ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [mem_orthogonalGroup_iff']
  have hT : (house v)ᵀ = house v := by
    rw [house, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  have hVV : vecMulVec v v * vecMulVec v v = (v ⬝ᵥ v) • vecMulVec v v := by
    rw [vecMulVec_mul_vecMulVec]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : 2 / (v ⬝ᵥ v) * (2 / (v ⬝ᵥ v) * (v ⬝ᵥ v)) = 2 / (v ⬝ᵥ v) + 2 / (v ⬝ᵥ v) := by
    field_simp
    ring
  rw [hT, house]
  simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hVV, smul_smul]
  rw [hc, add_smul]
  abel

/-- **The reflection maps `x` to `y` at equal length.** DERIVED: `1` the unit coefficient; `2` as in
`house`. -/
theorem house_mulVec {x y : Fin 4 → ℝ} (hxy : nsq x = nsq y) (hv : (x - y) ⬝ᵥ (x - y) ≠ 0) :
    house (x - y) *ᵥ x = y := by
  have hxx : x ⬝ᵥ x = y ⬝ᵥ y := by rw [← nsq_eq_dot, ← nsq_eq_dot, hxy]
  have hn : (x - y) ⬝ᵥ (x - y) = 2 * ((x - y) ⬝ᵥ x) := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm y x]
    linarith
  have hcoef : 2 / ((x - y) ⬝ᵥ (x - y)) * ((x - y) ⬝ᵥ x) = 1 := by
    rw [hn] at hv ⊢
    have h2 : (x - y) ⬝ᵥ x ≠ 0 := fun h => hv (by rw [h, mul_zero])
    field_simp
  rw [house, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    hcoef, one_smul, sub_sub_cancel]

/-- **An `O(4)`-invariant function is radial**: the Householder reflection carries any `x` to any `y`
of the same length. DERIVED: `0` the vanishing difference. -/
theorem radial_of_orthInv {S : (Fin 4 → ℝ) → ℝ} (h : OrthInv S) : Radial S := by
  intro x y hxy
  by_cases he : x = y
  · rw [he]
  · have hv : (x - y) ⬝ᵥ (x - y) ≠ 0 := fun h0 =>
      he (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h0))
    rw [← house_mulVec hxy hv]
    exact (h _ (house_orth _ hv) x).symm

/-- **`O(4)` invariance is radiality.** DERIVED: no numeral. -/
theorem radial_iff_orthInv (S : (Fin 4 → ℝ) → ℝ) : Radial S ↔ OrthInv S :=
  ⟨fun h R hR x => h _ _ (nsq_orth hR x), radial_of_orthInv⟩

/-! ## 2. What `CovC` gives a scalar composite -/

section Cov

open MassGap.ClayStatement MassGap.ObserverRotation MassGap.ContinuumField

variable {N : ℕ} (hN : N ≠ 0) (C : Composites N)

/-- **A scalar (Lorentz-singlet) composite**: every rotation maps it to itself with coefficient `1`.
DERIVED: `1` the trivial representation; `4` the dimension. -/
def Scalar (i : C.Ix) : Prop :=
  ∀ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, C.rep R i = Finsupp.single i 1

/-- **`CovC` makes the Schwinger functions of scalar composites `O(4)` invariant.** DERIVED: `0` the
non-vanishing coefficient; `1` the trivial representation. -/
theorem covC_scalar (hcov : CovC hN C) {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CDatum C)
    (hF : Adm F) (hs : ∀ j, Scalar C (F j).1) {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    contC hN C (fun j => ((F j).1, rotTest R (F j).2)) = contC hN C F := by
  have h := hcov R hR ι F hF
  have hrep : ∀ j, C.rep R (F j).1 = Finsupp.single (F j).1 1 := fun j => hs j R hR
  have hsupp : (fun j => (C.rep R (F j).1).support) = fun j => {(F j).1} := funext fun j => by
    rw [hrep j]; exact Finsupp.support_single_ne_zero _ one_ne_zero
  rw [hsupp, Fintype.piFinset_singleton] at h
  simp only [Finset.sum_singleton, hrep, Finsupp.single_eq_same, Finset.prod_const_one,
    one_mul] at h
  exact h.limUnder_eq

/-- **The two-point form of a scalar composite is `O(4)` invariant.** DERIVED: `2` the two points. -/
theorem covC_twoPoint (hcov : CovC hN C) {i : C.Ix} (hi : Scalar C i) (f h : TestFn)
    (hF : Adm (![(i, f), (i, h)] : Fin 2 → CDatum C)) {R : Matrix (Fin 4) (Fin 4) ℝ}
    (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    contC hN C (![(i, rotTest R f), (i, rotTest R h)] : Fin 2 → CDatum C)
      = contC hN C (![(i, f), (i, h)] : Fin 2 → CDatum C) := by
  have hc := covC_scalar hN C hcov _ hF (fun j => by fin_cases j <;> simpa using hi) hR
  convert hc using 2
  funext j
  fin_cases j <;> rfl

end Cov

/-! ## 3. The Källén–Lehmann joint measure -/

/-- **The squared spatial momentum** `Σ pⱼ²`. DERIVED: `2` the square. -/
def psq (p : Fin 4 → ℝ) : ℝ := ∑ j, p j ^ 2

/-- DERIVED: `0` the sign. -/
theorem psq_nonneg (p : Fin 4 → ℝ) : 0 ≤ psq p := Finset.sum_nonneg fun j _ => sq_nonneg _

/-- DERIVED: no numeral. -/
theorem continuous_psq : Continuous psq := by unfold psq; fun_prop

/-- DERIVED: `0` the zero momentum. -/
theorem psq_zero : psq 0 = 0 := by simp [psq]

/-- **The Källén–Lehmann sector** `shell(·, p²)_* (ρ / (2 shell))`. DERIVED: no numeral. -/
def klSec (ρ : Measure ℝ) (p2 : ℝ) : Measure ℝ :=
  (ρ.withDensity (klWeight p2)).map (fun s => shell s p2)

/-- **One `ρ` for every momentum.** DERIVED: no numeral. -/
theorem kallenLehmann_klSec (ρ : Measure ℝ) : KallenLehmann (klSec ρ) ρ := fun _ _ => rfl

/-- **The sector scales with `ρ`.** DERIVED: no numeral. -/
theorem klSec_smul (c : ℝ≥0) (ρ : Measure ℝ) (p2 : ℝ) : klSec (c • ρ) p2 = c • klSec ρ p2 := by
  rw [klSec, klSec, ← Measure.coe_nnreal_smul, withDensity_smul_measure, Measure.map_smul,
    Measure.coe_nnreal_smul]

/-- **The joint density** `g(p) / (2√(s + p²))` on momentum × `s`. DERIVED: no numeral. -/
def klDens (g : (Fin 4 → ℝ) → ℝ≥0) (q : (Fin 4 → ℝ) × ℝ) : ℝ≥0∞ :=
  (g q.1 : ℝ≥0∞) * klWeight (psq q.1) q.2

/-- **Each `(p, s)` on its shell**: `(√(s + p²), p)`. DERIVED: no numeral. -/
def klMap (q : (Fin 4 → ℝ) × ℝ) : ℝ × (Fin 4 → ℝ) := (shell q.2 (psq q.1), q.1)

/-- **The Källén–Lehmann rate × momentum measure** with momentum profile `g`. DERIVED: no numeral. -/
def klJoint (τ : Fin 4) (ρ : Measure ℝ) (g : (Fin 4 → ℝ) → ℝ≥0) : Measure (ℝ × (Fin 4 → ℝ)) :=
  (((lam τ).prod ρ).withDensity (klDens g)).map klMap

instance (τ : Fin 4) : SigmaFinite (lam τ) := by
  unfold lam; infer_instance

/-- DERIVED: no numeral. -/
theorem continuous_shellP : Continuous fun q : (Fin 4 → ℝ) × ℝ => shell q.2 (psq q.1) := by
  unfold shell
  exact Real.continuous_sqrt.comp (continuous_snd.add (continuous_psq.comp continuous_fst))

/-- DERIVED: no numeral. -/
theorem measurable_klMap : Measurable klMap := (continuous_shellP.prodMk continuous_fst).measurable

/-- DERIVED: `1`, `2` as in `klWeight`. -/
theorem measurable_klDens {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) : Measurable (klDens g) := by
  have hk : Measurable fun q : (Fin 4 → ℝ) × ℝ => klWeight (psq q.1) q.2 := by
    show Measurable fun q : (Fin 4 → ℝ) × ℝ => ENNReal.ofReal (1 / (2 * shell q.2 (psq q.1)))
    exact ENNReal.measurable_ofReal.comp ((continuous_shellP.measurable.const_mul 2).const_div 1)
  exact (ENNReal.continuous_coe.comp (hg.comp continuous_fst)).measurable.mul hk

/-- **The integrand of a windowed rate integral.** DERIVED: no numeral. -/
def Ik (g : (Fin 4 → ℝ) → ℝ≥0) (f : ℝ → ℝ≥0) (p : Fin 4 → ℝ) (s : ℝ) : ℝ≥0∞ :=
  klDens g (p, s) * (f (shell s (psq p)) : ℝ≥0∞)

/-- DERIVED: no numeral. -/
theorem measurable_Ik {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) {f : ℝ → ℝ≥0} (hf : Continuous f) :
    Measurable fun q : (Fin 4 → ℝ) × ℝ => Ik g f q.1 q.2 :=
  (measurable_klDens hg).mul (ENNReal.continuous_coe.comp (hf.comp continuous_shellP)).measurable

/-- **The weight decreases in the momentum**: `1/(2√(s + p²)) ≤ 1/(2√s)` for `s > 0`.
DERIVED: `0` the signs; `1`, `2` as in `klWeight`. -/
theorem klWeight_anti {s P : ℝ} (hs : 0 < s) (hP : 0 ≤ P) : klWeight P s ≤ klWeight 0 s := by
  unfold klWeight shell
  apply ENNReal.ofReal_le_ofReal
  rw [add_zero]
  have h1 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h2 : Real.sqrt s ≤ Real.sqrt (s + P) := Real.sqrt_le_sqrt (by linarith)
  exact one_div_le_one_div_of_le (mul_pos two_pos h1) (by linarith)

/-- DERIVED: `0` the support bound. -/
theorem ae_pos {ρ : Measure ℝ} (hρ0 : ρ (Iic 0) = 0) : ∀ᵐ s ∂ρ, 0 < s := by
  rw [ae_iff]
  have : {s : ℝ | ¬ 0 < s} = Iic 0 := by ext s; simp [not_lt]
  rw [this]; exact hρ0

/-- **At `s > 0` the integrand is continuous in the momentum.** DERIVED: `0` the sign; `1`, `2` as in
`klWeight`. -/
theorem continuous_Ik {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) {f : ℝ → ℝ≥0} (hf : Continuous f)
    {s : ℝ} (hs : 0 < s) : Continuous fun p => Ik g f p s := by
  have hsh : Continuous fun p : Fin 4 → ℝ => shell s (psq p) := by
    unfold shell; exact Real.continuous_sqrt.comp (continuous_const.add continuous_psq)
  have hne : ∀ p, 2 * shell s (psq p) ≠ 0 := fun p => by
    have := Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg hs (psq_nonneg p))
    exact mul_ne_zero two_ne_zero (ne_of_gt this)
  have hk : Continuous fun p => 1 / (2 * shell s (psq p)) :=
    continuous_const.div (continuous_const.mul hsh) hne
  have e : (fun p => Ik g f p s) = fun p =>
      (((g p * (1 / (2 * shell s (psq p))).toNNReal * f (shell s (psq p)) : ℝ≥0)) : ℝ≥0∞) := by
    funext p
    simp only [Ik, klDens, klWeight, ENNReal.ofReal, ENNReal.coe_mul]
  rw [e]
  exact ENNReal.continuous_coe.comp ((hg.mul (continuous_real_toNNReal.comp hk)).mul (hf.comp hsh))

/-- **The inner integral is continuous at `p = 0` and finite there**, by dominated convergence with
the bound `(g(0) + 1) B / (2√s)`. DERIVED: `0` the zero momentum and the support bound; `1` a margin
above `g(0)` (any positive margin serves; a witness of the proof, not a parameter of the result). -/
theorem kl_inner {ρ : Measure ℝ} (hρ0 : ρ (Iic 0) = 0) (hfin : ∫⁻ s, klWeight 0 s ∂ρ ≠ ⊤)
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) {f : ℝ → ℝ≥0} (hf : Continuous f)
    (hfb : BddAbove (range f)) :
    ContinuousAt (fun p => ∫⁻ s, Ik g f p s ∂ρ) 0 ∧ ∫⁻ s, Ik g f 0 s ∂ρ ≠ ⊤ := by
  obtain ⟨B, hB⟩ := hfb
  have hfB : ∀ x, f x ≤ B := fun x => hB ⟨x, rfl⟩
  have hpos := ae_pos hρ0
  let bound : ℝ → ℝ≥0∞ := fun s => (((g 0 + 1) * B : ℝ≥0) : ℝ≥0∞) * klWeight 0 s
  have hbfin : ∫⁻ s, bound s ∂ρ ≠ ⊤ := by
    simp only [bound]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hle : ∀ p, g p ≤ g 0 + 1 → ∀ s, 0 < s → Ik g f p s ≤ bound s := by
    intro p hp s hs
    have hk : klWeight (psq p) s ≤ klWeight 0 s := klWeight_anti hs (psq_nonneg p)
    simp only [Ik, klDens, bound, ENNReal.coe_mul]
    calc (g p : ℝ≥0∞) * klWeight (psq p) s * (f (shell s (psq p)) : ℝ≥0∞)
        ≤ ((g 0 + 1 : ℝ≥0) : ℝ≥0∞) * klWeight 0 s * (B : ℝ≥0∞) := by
          gcongr
          exact hfB _
      _ = _ := by ring
  have hgG : ∀ᶠ p in 𝓝 (0 : Fin 4 → ℝ), g p ≤ g 0 + 1 :=
    hg.continuousAt.eventually_mem (Iic_mem_nhds (lt_add_one (g 0)))
  have hlim : ∀ᵐ s ∂ρ, Tendsto (fun p => Ik g f p s) (𝓝 0) (𝓝 (Ik g f 0 s)) := by
    filter_upwards [hpos] with s hs
    exact (continuous_Ik hg hf hs).tendsto 0
  refine ⟨?_, ?_⟩
  · exact tendsto_lintegral_filter_of_dominated_convergence bound
      (Eventually.of_forall fun p => (measurable_Ik hg hf).comp measurable_prodMk_left)
      (hgG.mono fun p hp => hpos.mono fun s hs => hle p hp s hs) hbfin hlim
  · refine ne_top_of_le_ne_top hbfin (lintegral_mono_ae ?_)
    filter_upwards [hpos] with s hs using hle 0 le_self_add s hs

/-- **The windowed rate integral of the Källén–Lehmann measure.** DERIVED: `0` the window's centre. -/
theorem windowed_klJoint (τ : Fin 4) (ρ : Measure ℝ) [IsFiniteMeasure ρ] {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Continuous g) {f : ℝ → ℝ≥0} (hf : Continuous f) (ε : ℝ) :
    ∫⁻ s, (f s : ℝ≥0∞) ∂(windowed (klJoint τ ρ g) ε)
      = ∫⁻ p in Metric.ball 0 ε, ∫⁻ s, Ik g f p s ∂ρ ∂lam τ := by
  have hfm : Measurable fun s : ℝ => (f s : ℝ≥0∞) := (ENNReal.continuous_coe.comp hf).measurable
  have hfm2 : Measurable fun q : ℝ × (Fin 4 → ℝ) => (f q.1 : ℝ≥0∞) := hfm.comp measurable_fst
  have hfΦ : Measurable fun q : (Fin 4 → ℝ) × ℝ => (f (klMap q).1 : ℝ≥0∞) :=
    hfm2.comp measurable_klMap
  have hB : MeasurableSet (Metric.ball (0 : Fin 4 → ℝ) ε) := Metric.isOpen_ball.measurableSet
  have hS : MeasurableSet ((univ : Set ℝ) ×ˢ Metric.ball (0 : Fin 4 → ℝ) ε) :=
    MeasurableSet.univ.prod hB
  have hpre : klMap ⁻¹' ((univ : Set ℝ) ×ˢ Metric.ball 0 ε)
      = Metric.ball 0 ε ×ˢ (univ : Set ℝ) := by
    ext q; simp [klMap]
  rw [windowed, lintegral_map hfm measurable_fst, klJoint, Measure.restrict_map measurable_klMap hS,
    lintegral_map hfm2 measurable_klMap, hpre, restrict_withDensity (hB.prod MeasurableSet.univ)]
  refine (lintegral_withDensity_eq_lintegral_mul _ (measurable_klDens hg) hfΦ).trans ?_
  rw [← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod]
  · rfl
  · exact ((measurable_klDens hg).mul hfΦ).aemeasurable

/-- **The Källén–Lehmann measure has zero-momentum density `klSec (g(0) ρ) 0`.** With `ρ (−∞, 0] = 0`
and `σ 0` finite. DERIVED: `0` the zero momentum and the support bound. -/
theorem klJoint_zeroDensity (τ : Fin 4) {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ0 : ρ (Iic 0) = 0)
    (hfin : ∫⁻ s, klWeight 0 s ∂ρ ≠ ⊤) {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) :
    ZeroDensity τ (klJoint τ ρ g) (klSec (g 0 • ρ) 0) := by
  intro f hf hfb
  obtain ⟨hc, htop⟩ := kl_inner hρ0 hfin hg hf hfb
  have hfm : Measurable fun s : ℝ => (f s : ℝ≥0∞) := (ENNReal.continuous_coe.comp hf).measurable
  have hfm3 : Measurable fun s : ℝ => (f (shell s 0) : ℝ≥0∞) := hfm.comp (measurable_shell 0)
  have hR : ∫⁻ s, (f s : ℝ≥0∞) ∂(klSec (g 0 • ρ) 0) = ∫⁻ s, Ik g f 0 s ∂ρ := by
    rw [klSec, lintegral_map hfm (measurable_shell 0),
      lintegral_withDensity_eq_lintegral_mul _ (measurable_klWeight 0) hfm3,
      lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr fun s => ?_
    simp only [Ik, klDens, psq_zero, Pi.mul_apply, mul_assoc]
  have hw : ∀ ε, ∫⁻ s, (f s : ℝ≥0∞) ∂(windowed (klJoint τ ρ g) ε)
      = ∫⁻ p in Metric.ball 0 ε, ∫⁻ s, Ik g f p s ∂ρ ∂lam τ := windowed_klJoint τ ρ hg hf
  simp_rw [hw]
  rw [hR]
  exact avg_tendsto τ hc htop

/-- **A rate bottom of the Källén–Lehmann measure bounds `ρ` away from `0`.** If no mass of
`klJoint τ ρ g` has rate below `a > 0` and `g(0) ≠ 0`, then `ρ (−∞, b) = 0` for some `b > 0`.
DERIVED: `0` the zero momentum, the support bound and the signs; `2` the half of `a` (a witness of the
proof: any radius with `4 r² ≤ a²` serves) and the square; `4` the coordinates of a momentum. -/
theorem klJoint_bottom (τ : Fin 4) {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ0 : ρ (Iic 0) = 0)
    {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0) {a : ℝ} (ha : 0 < a)
    (h : klJoint τ ρ g (Iio a ×ˢ univ) = 0) : ∃ b, 0 < b ∧ ρ (Iio b) = 0 := by
  have hA : MeasurableSet (Iio a ×ˢ (univ : Set (Fin 4 → ℝ))) :=
    measurableSet_Iio.prod MeasurableSet.univ
  have hT : MeasurableSet (klMap ⁻¹' (Iio a ×ˢ (univ : Set (Fin 4 → ℝ)))) := measurable_klMap hA
  have hm : Measurable ((klMap ⁻¹' (Iio a ×ˢ (univ : Set (Fin 4 → ℝ)))).indicator (klDens g)) :=
    (measurable_klDens hg).indicator hT
  rw [klJoint, Measure.map_apply measurable_klMap hA, withDensity_apply _ hT,
    ← lintegral_indicator hT, lintegral_prod _ hm.aemeasurable] at h
  have hae := (lintegral_eq_zero_iff hm.lintegral_prod_right').mp h
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hg.continuousAt.eventually_ne hg0)
  have hr : 0 < min δ (a / 2) := lt_min hδ (by linarith)
  have hlam : (lam τ).restrict (Metric.ball 0 (min δ (a / 2))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, lam_ball τ hr]
    exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  haveI := ae_neBot.mpr hlam
  have hmae : ∀ᵐ p ∂(lam τ).restrict (Metric.ball (0 : Fin 4 → ℝ) (min δ (a / 2))),
      p ∈ Metric.ball (0 : Fin 4 → ℝ) (min δ (a / 2)) :=
    ae_restrict_mem Metric.isOpen_ball.measurableSet
  obtain ⟨p, hp, hp0⟩ := (hmae.and (ae_restrict_of_ae hae)).exists
  simp only [Pi.zero_apply] at hp0
  have hp' : ‖p‖ < min δ (a / 2) := mem_ball_zero_iff.mp hp
  have hi : ∀ i, p i ^ 2 < (a / 2) ^ 2 := fun i => by
    have h1 : |p i| < a / 2 := by
      have := (norm_le_pi_norm p i).trans_lt (hp'.trans_le (min_le_right _ _))
      rwa [Real.norm_eq_abs] at this
    exact sq_lt_sq' (by linarith [neg_abs_le (p i)]) (lt_of_le_of_lt (le_abs_self _) h1)
  have hP : psq p < a ^ 2 := by
    simp only [psq, Fin.sum_univ_four]
    nlinarith [hi 0, hi 1, hi 2, hi 3]
  refine ⟨a ^ 2 - psq p, by linarith, ?_⟩
  have hs := (lintegral_eq_zero_iff (hm.comp measurable_prodMk_left)).mp hp0
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hs, ae_pos hρ0] with s h1 h2
  intro hlt
  have hmem : (p, s) ∈ klMap ⁻¹' (Iio a ×ˢ (univ : Set (Fin 4 → ℝ))) := by
    simp only [mem_preimage, klMap, mem_prod, mem_Iio, mem_univ, and_true]
    unfold shell
    rw [Real.sqrt_lt' ha]
    linarith [mem_Iio.mp hlt]
  have hgp : g p ≠ 0 := hball p (Metric.ball_subset_ball (min_le_left _ _) hp)
  have hk : klWeight (psq p) s ≠ 0 := by
    unfold klWeight shell
    have := Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg h2 (psq_nonneg p))
    exact (ENNReal.ofReal_pos.mpr (one_div_pos.mpr (mul_pos two_pos this))).ne'
  simp only [Function.comp_apply, Pi.zero_apply, indicator_of_mem hmem, klDens] at h1
  exact mul_ne_zero (ENNReal.coe_ne_zero.mpr hgp) hk h1

/-- **A bottom `b > 0` of `ρ` makes `σ 0` finite**: `∫ dρ/(2√s) ≤ ρ(ℝ)/(2√b)`. DERIVED: `0` the zero
momentum; `1`, `2` as in `klWeight`. -/
theorem klWeight_fin {ρ : Measure ℝ} [IsFiniteMeasure ρ] {b : ℝ} (hb : 0 < b) (h : ρ (Iio b) = 0) :
    ∫⁻ s, klWeight 0 s ∂ρ ≠ ⊤ := by
  have hae : ∀ᵐ s ∂ρ, b ≤ s := by
    rw [ae_iff]
    have : {s : ℝ | ¬ b ≤ s} = Iio b := by ext s; simp [not_le]
    rw [this]; exact h
  have hsb := Real.sqrt_pos.mpr hb
  have hle : ∫⁻ s, klWeight 0 s ∂ρ ≤ ∫⁻ _s, ENNReal.ofReal (1 / (2 * Real.sqrt b)) ∂ρ :=
    lintegral_mono_ae (hae.mono fun s hs => by
      unfold klWeight shell
      rw [add_zero]
      exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (mul_pos two_pos hsb)
        (by linarith [Real.sqrt_le_sqrt hs])))
  rw [lintegral_const] at hle
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ρ univ)) hle

/-- **Each sector is finite** for `p² ≥ 0`. DERIVED: `0` the sign. -/
theorem klSec_finite {ρ : Measure ℝ} (hρ0 : ρ (Iic 0) = 0) (hfin : ∫⁻ s, klWeight 0 s ∂ρ ≠ ⊤)
    {p2 : ℝ} (hp : 0 ≤ p2) : IsFiniteMeasure (klSec ρ p2) := by
  refine ⟨?_⟩
  rw [klSec, Measure.map_apply (measurable_shell p2) MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lt_of_le_of_lt (lintegral_mono_ae ((ae_pos hρ0).mono fun s hs => klWeight_anti hs hp))
    hfin.lt_top

/-- **Each sector lives on the rates `E ≥ 0`.** DERIVED: `0` the bottom of the rates. -/
theorem klSec_Iio (ρ : Measure ℝ) (p2 : ℝ) : klSec ρ p2 (Iio 0) = 0 := by
  rw [klSec, Measure.map_apply (measurable_shell p2) measurableSet_Iio]
  have e : (fun s => shell s p2) ⁻¹' Iio 0 = ∅ := by
    ext s
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_lt]
    exact shell_nonneg s p2
  rw [e, measure_empty]

/-- **Each sector is a Laplace transform**, so it feeds `ShellMeasure.shell_rate_of_kl`.
DERIVED: `0` the sign. -/
theorem klSec_laplaceRep {ρ : Measure ℝ} (hρ0 : ρ (Iic 0) = 0) (hfin : ∫⁻ s, klWeight 0 s ∂ρ ≠ ⊤)
    {p2 : ℝ} (hp : 0 ≤ p2) :
    LaplaceRep (fun t => ∫ E, Real.exp (-(t * E)) ∂(klSec ρ p2)) :=
  ⟨klSec ρ p2, klSec_finite hρ0 hfin hp, klSec_Iio ρ p2, fun _ _ => rfl⟩

/-- **A non-zero scalar keeps the spectral bottom.** DERIVED: `0` the scalar's exclusion. -/
theorem specBottom_smul {ρ : Measure ℝ} {M2 : ℝ} {c : ℝ≥0} (hc : c ≠ 0) (hb : SpecBottom ρ M2) :
    SpecBottom (c • ρ) M2 := by
  refine ⟨?_, fun ε hε => ?_⟩
  · rw [Measure.smul_apply, hb.1, smul_zero]
  · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hc) (hb.2 ε hε).ne'

/-! ## 4. The connection to `clay_zero_momentum_density` -/

section Clay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {τ : Fin 4}

/-- **The Euclidean Källén–Lehmann template for one vector** (a named hypothesis, not discharged):
the rate × momentum measure of `u` is the Källén–Lehmann measure of `ρ` with a continuous momentum
profile `g`, `g(0) ≠ 0`. DERIVED: `0` the zero momentum. -/
def KLJointRep (J : JointData E (spatial τ)) (u : E) (ρ : Measure ℝ) : Prop :=
  ∃ g : (Fin 4 → ℝ) → ℝ≥0, Continuous g ∧ g 0 ≠ 0 ∧ nu J u = klJoint τ ρ g

/-- **A Hölder bound in the translations gives the dyadic Dini bound**: `‖U(s eⱼ) u − u‖ ≤ L sᵅ` for
`s ≥ 0`, `α > 0`, makes `Σ_k ‖U(2^{−k} eⱼ) u − u‖²` geometric. DERIVED: `0` the signs; `1/2` the
dyadic scale; `1` the ratio bound; `2` the square. -/
theorem dyadicDini_of_holder (J : JointData E (spatial τ)) (u : E) {L α : ℝ} (hα : 0 < α)
    (h : ∀ j (s : ℝ), 0 ≤ s → ‖J.R.U (s • ej τ j) u - u‖ ≤ L * s ^ α) : DyadicDini J u := by
  intro j
  have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have hq1 : (1 / 2 : ℝ) ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hg : Summable fun k : ℕ => L ^ 2 * (((1 / 2 : ℝ) ^ α) ^ 2) ^ k :=
    (summable_geometric_of_lt_one (sq_nonneg _) (pow_lt_one₀ hq0 hq1 two_ne_zero)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hg
  have hs : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  have hb := h j _ hs
  have e : ((1 / 2 : ℝ) ^ k) ^ α = ((1 / 2 : ℝ) ^ α) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [e] at hb
  calc ‖J.R.U (dy τ j k) u - u‖ ^ 2 ≤ (L * ((1 / 2 : ℝ) ^ α) ^ k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = L ^ 2 * (((1 / 2 : ℝ) ^ α) ^ 2) ^ k := by ring

end Clay

/-- **The Clay read through the Euclidean Källén–Lehmann form.** For joint data `J` on the Clay object
with time step `X.time 1`, `u` in the vacuum complement, a finite `ρ` with `ρ (−∞, 0] = 0` and
`SpecBottom ρ M2`, and `nu J u = klJoint τ ρ g` (`g` continuous, `g(0) ≠ 0`): the corrected
identification holds with `σ = klSec (g(0) ρ)` and every conclusion of `clay_zero_momentum_density`
follows. DERIVED: `0` the zero momentum and the signs; `1` the unit step. -/
theorem clay_zero_momentum_kl {τ : Fin 4} (X : OSDataS) (J : JointData X.H (spatial τ))
    (hJ : J.a = X.time 1) (u : X.H) (hu : inner ℂ X.vac u = 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ0 : ρ (Iic 0) = 0) {g : (Fin 4 → ℝ) → ℝ≥0} (hg : Continuous g) (hg0 : g 0 ≠ 0) {M2 : ℝ}
    (hb : SpecBottom ρ M2) (hKL : nu J u = klJoint τ ρ g) :
    ZeroDensity τ (nu J u) (klSec (g 0 • ρ) 0)
      ∧ klSec (g 0 • ρ) 0 (Iio X.gap) = 0 ∧ 0 < M2 ∧ X.gap ≤ Real.sqrt M2
      ∧ SpecBottom (klSec (g 0 • ρ) 0) (Real.sqrt M2)
      ∧ ∀ p2, 0 ≤ p2 → Real.sqrt p2 < shell M2 p2 := by
  have hr : rateMeasure J.a u (Iio X.gap) = 0 := by rw [hJ]; exact gap_rateBottom X u hu
  have hν := nu_Iio_prod J u X.gap hr
  rw [hKL] at hν
  obtain ⟨b, hb0, hbρ⟩ := klJoint_bottom τ hρ0 hg hg0 X.gap_pos hν
  have hσ' : ZeroDensity τ (nu J u) (klSec (g 0 • ρ) 0) := by
    rw [hKL]; exact klJoint_zeroDensity τ hρ0 (klWeight_fin hb0 hbρ) hg
  have hρ0' : (g 0 • ρ) (Iic 0) = 0 := by rw [Measure.smul_apply, hρ0, smul_zero]
  exact ⟨hσ', clay_zero_momentum_density X J hJ u hu (kallenLehmann_klSec _) hρ0'
    (specBottom_smul hg0 hb) hσ'⟩

/-- **The Clay read under the template.** DERIVED: no numeral. -/
theorem clay_zero_momentum_template {τ : Fin 4} (X : OSDataS) (J : JointData X.H (spatial τ))
    (hJ : J.a = X.time 1) (u : X.H) (hu : inner ℂ X.vac u = 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ0 : ρ (Iic 0) = 0) {M2 : ℝ} (hb : SpecBottom ρ M2) (hT : KLJointRep J u ρ) :
    ∃ σ : ℝ → Measure ℝ, ∃ ρu : Measure ℝ, KallenLehmann σ ρu ∧ ZeroDensity τ (nu J u) (σ 0)
      ∧ σ 0 (Iio X.gap) = 0 ∧ 0 < M2 ∧ X.gap ≤ Real.sqrt M2 ∧ SpecBottom (σ 0) (Real.sqrt M2) := by
  obtain ⟨g, hg, hg0, hKL⟩ := hT
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := clay_zero_momentum_kl X J hJ u hu hρ0 hg hg0 hb hKL
  exact ⟨klSec (g 0 • ρ), g 0 • ρ, kallenLehmann_klSec _, h1, h2, h3, h4, h5⟩

/-! ## 5. Load tests -/

/-- **The free field**: `ρ = δ_{m²}`, `m² > 0`, has zero-momentum density `g(0) · freeRate m² 0`
(`= g(0) δ_m/(2m)`). DERIVED: `0` the zero momentum and the sign. CHOSEN (the test's free data):
`m²` and `g`, every value. -/
theorem free_kl_zeroDensity (τ : Fin 4) {m2 : ℝ} (hm : 0 < m2) {g : (Fin 4 → ℝ) → ℝ≥0}
    (hg : Continuous g) : ZeroDensity τ (klJoint τ (Measure.dirac m2) g) (g 0 • freeRate m2 0) := by
  have hρ0 : Measure.dirac m2 (Iic 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iic,
      indicator_of_notMem (fun h => absurd (mem_Iic.mp h) (not_le.mpr hm))]
  have hfin : ∫⁻ s, klWeight 0 s ∂Measure.dirac m2 ≠ ⊤ := by
    rw [lintegral_dirac]; exact ENNReal.ofReal_ne_top
  have h := klJoint_zeroDensity τ hρ0 hfin hg
  have e : klSec (Measure.dirac m2) 0 = freeRate m2 0 := (free_kallenLehmann m2 0 le_rfl).symm
  rwa [klSec_smul, e] at h

/-- **An anisotropic kernel**: time and space at different scales. DERIVED: `0`–`3` the coordinates;
`2` the square. CHOSEN (a counterexample): the factor `2` on the time coordinate (any factor other than
`1` serves). -/
def aniso (x : Fin 4 → ℝ) : ℝ := Real.exp (-(2 * x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2))

/-- **It is not radial**: `e^{−2}` on the time unit vector, `e^{−1}` on a space unit vector.
DERIVED: `0`, `1` the entries of the unit vectors. -/
theorem aniso_not_radial : ¬ Radial aniso := by
  intro h
  have := h (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0)
    (by simp [nsq])
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  norm_num [aniso, h30, h20, h31, h21] at this

/-- **So it is not `O(4)` invariant.** DERIVED: no numeral. -/
theorem aniso_not_orthInv : ¬ OrthInv aniso := fun h => aniso_not_radial (radial_of_orthInv h)

end

end MassGap.ShellLorentz

#print axioms MassGap.ShellLorentz.nsq_orth
#print axioms MassGap.ShellLorentz.house_orth
#print axioms MassGap.ShellLorentz.house_mulVec
#print axioms MassGap.ShellLorentz.radial_of_orthInv
#print axioms MassGap.ShellLorentz.radial_iff_orthInv
#print axioms MassGap.ShellLorentz.covC_scalar
#print axioms MassGap.ShellLorentz.covC_twoPoint
#print axioms MassGap.ShellLorentz.kallenLehmann_klSec
#print axioms MassGap.ShellLorentz.klSec_smul
#print axioms MassGap.ShellLorentz.klWeight_anti
#print axioms MassGap.ShellLorentz.continuous_Ik
#print axioms MassGap.ShellLorentz.kl_inner
#print axioms MassGap.ShellLorentz.windowed_klJoint
#print axioms MassGap.ShellLorentz.klJoint_zeroDensity
#print axioms MassGap.ShellLorentz.klJoint_bottom
#print axioms MassGap.ShellLorentz.klWeight_fin
#print axioms MassGap.ShellLorentz.klSec_finite
#print axioms MassGap.ShellLorentz.klSec_Iio
#print axioms MassGap.ShellLorentz.klSec_laplaceRep
#print axioms MassGap.ShellLorentz.specBottom_smul
#print axioms MassGap.ShellLorentz.dyadicDini_of_holder
#print axioms MassGap.ShellLorentz.clay_zero_momentum_kl
#print axioms MassGap.ShellLorentz.clay_zero_momentum_template
#print axioms MassGap.ShellLorentz.free_kl_zeroDensity
#print axioms MassGap.ShellLorentz.aniso_not_radial
#print axioms MassGap.ShellLorentz.aniso_not_orthInv
