import Mathlib
import MassGap.PhotonStall
import MassGap.MixExpand
import MassGap.TwistedTraceBound

/-!
# MassGap.HarmonicVertex — the cubic vertex of the plaquette, its momentum rule, and mode coupling

At cubic order the plaquette vertex vanishes for commuting data and is non-zero at the chosen `su(2)` witness.
Commuting fields have no cubic plaquette term: the waves of a Gaussian photon superpose, each Fourier mode
independent. Non-commuting fields have the vertex `tr(F[A, B])`, the `f^{abc}` vertex, which at the witness couples
three distinct modes. The Cartan subspace is the commuting sector; that the cheapest classical sheet lies there is
`NonCartanTwist`, not shown here. Declarations are in `MassGap.HarmonicVertex`.

## 1. The cubic term of the Wilson density (proved; the true matrix exponential)

For a plaquette `U(t) = exp(t x₁) exp(t x₂) exp(t x₃) exp(t x₄)`, with `x₃ = −A₃`, `x₄ = −A₄` the reversed links,
put `F = Σ xᵢ` and `K = Σ_{i<j} [xᵢ, xⱼ]`.

* `exp_jet`, `Jet3.mul`, `holo_jet`: `U(t) = 1 + t F + t² P₂ + t³ P₃ + O(t⁴)`, in any real Banach algebra.
* `P2_eq`: `P₂ = ½F² + ½K`. `bch_second`: `U(t) = exp(t F + ½ t² K) + O(t³)`.
* `tau_P3`: for a cyclic linear functional, `τ(P₃) = ⅙ τ(F³) + ½ τ(F K)`.
* `wilson_expansion`: `1 − (1/N) Re tr U(t) = t c₁ + t² c₂ + t³ c₃ + O(t⁴)`.
* `re_trace_cube_of_skew`: `Re tr F³ = 0` for anti-Hermitian `F`.
* `cubic_eq_commutator`: for anti-Hermitian links `c₃ = −(1/2N) Σ_{i<j} Re tr(F [xᵢ, xⱼ])`, a sum of commutator terms.
* `wilson_su_expansion`: for `su(N)` links, `1 − (1/N) Re tr U(t) = −(t²/2N) Re tr F² + t³ c₃ + O(t⁴)`.
* `cubic_comm`: commuting anti-Hermitian links have `c₃ = 0` identically (`U(1)`, the Cartan subspace).
* `su2_vertex`: on `su(2)`, `tr(X_u [X_v, X_w]) = −½ det(u, v, w)`, the structure constants `f^{abc} = ε^{abc}`.
* `cubic_su2_ne`: CHOSEN `su(2)` triple `(e₁, e₂, e₃, 0)`: `c₃ = 1/8 ≠ 0`.

## 2. The momentum rule (proved)

On the torus `(ℤ/L)^d`, with plane waves `e_k(x)`:

* `sum_wave`: `Σ_x e_k(x) = L^d` at `k = 0` and `0` otherwise.
* `momentum_selection`: the plaquette vertex of three plane waves, summed over sites, is `L^d Γ` when `k₁ + k₂ + k₃ = 0`
  and `0` otherwise, with `Γ` the form factor carrying the plaquette's shift phases.
* `momentum_difference`, `momentum_double`: a wave at `k₁` crossing the conjugate of a wave at `k₂` drives only `k₁ − k₂`
  (the third wave sits at `k₂ − k₁`), and a wave crossing itself drives only `2k₁`.
* `vertex_modes`: for a sum of plane waves the vertex is the triple sum over modes with the rule.
* `formFactor_comm`, `vertex_modes_comm`: for commuting polarizations the coupling is `0`.
* `formFactor_witness`: CHOSEN `L = 2`, `d = 2`, three non-zero momenta summing to `0`, `su(2)` polarizations: the
  symmetrized form factor is `−2`, so the vertex couples distinct modes. The polarizations are not all transverse.

## 3. The mode-coupling read

The additivity defect of a read `Φ` on sets of modes is `modeCoupling Φ S T = Φ(S ∪ T) − Φ(S) − Φ(T)`.

The Gaussian measure independent across modes, the shape of `PhotonStall` (proved for that model):

* `logZ_eq`: `log ∫ exp(−½ Σ λᵢ φᵢ²) dφ = Σᵢ ½ log(2π/λᵢ)`, from the integral.
* `gaussian_additive`: `modeCoupling logZ S T = 0` for disjoint mode sets.
* `dbl_additive`: the doubling defect `PhotonStall.dbl` of such a read is additive over modes at each side.
* `logMGF_eq`: the log moment generating function is `Σᵢ σᵢ Jᵢ²/2`.
* `gaussian_connected3`: the third connected term, the third mixed difference of the generating function, is exactly `0`.
* `gaussian_source_coupling`: sources on disjoint modes do not couple.

The Gaussian-plus-cubic model. CHOSEN: Gaussian weight `dγ`, plus a cubic `V = Σ_{s ∈ 𝒯} v_s Π_{i ∈ s} φᵢ` on sets of
distinct modes (no tadpole term). `exp(−g V)` is not integrable for real `g`, so the model is the formal expansion of
`log Z` in `g`, whose coefficients are cumulants of `V` under `γ`. It is not the Wilson measure.

* `moment_pair`: `∫ φ_s φ_{s'} dγ = δ_{s s'} Π_{i ∈ s} σᵢ`.
* `cubicForm_mean`: the `g¹` term is `0`.
* `cubicForm_second`: the `g²` term is `½ Σ_{s ∈ 𝒯} v_s² Π_{i ∈ s} σᵢ`, the vertex squared over the propagators.
* `cum2W_coupling`, `cum2W_coupling_nonneg`: its additivity defect is the same sum over the triples straddling `S` and
  `T`, and it is non-negative.
* `secondOrder_coupling`, `secondOrder_coupling_nonneg`: Gaussian part plus `g²` term: the defect is `g²/2` times that.
* `cum2W_zero`: at `v = 0` every term vanishes.

The same sum on the torus, in plane waves (defined; not derived from an integral over a complex field):

* `sunset`: `Σ_{m,n,l ∈ S} δ(k_m + k_n + k_l) |Γ_{mnl}|² / (λ_m λ_n λ_l)`, with `Γ` the symmetrized plaquette form factor
  summed over planes.
* `sunset_nonneg`; `sunset_comm`: it vanishes for commuting polarizations.
* `sunset_coupling`, `sunset_coupling_nonneg`: its additivity defect is the sum over straddling triples, and is `≥ 0`.
* `sunset_coupling_witness`: positive at the data of `formFactor_witness`.

## 4. The single-plaquette third moment (proved; `SU(3)`'s value cited)

* `haar_cube_u1`, `haar_cube_su2`: `∫ (Re tr U)³ dHaar = 0`, from the element `−1`. The same for every odd power
  (`haar_odd_u1`, `haar_odd_su2`).
* `haarCum3_two`: the Haar third central moment `MixExpand.haarCum3 2` of the plaquette density is `0`.
* `haar_cube_su3`: `∫ (Re tr U)³ dHaar = ¼ Re ∫ (tr U)³ dHaar`, from the `ℤ₃` centre: triality removes the `χ²χ̄` terms.
  `∫ (tr U)³ dHaar = 1` is the singlet of `3 ⊗ 3 ⊗ 3` (cited, not proved here), which gives `1/4`.

`SU(2)` confines with this moment `0`, so this moment is not the separator.

DERIVED (module-wide): `½`, `⅙` the inverse factorials of the exponential; `4` the links of a plaquette; `3` the order
of the vertex; `2π` the Gaussian integral; `2` in `L = 2` the least extent with real plane waves. CHOSEN: the `su(2)`
triple of `cubic_su2_ne`, the data of `formFactor_witness`, the Gaussian-plus-cubic model of §3 (no tadpole term; a
formal expansion). Cited: `∫ (tr U)³ dHaar = 1` on `SU(3)`.

## What does not follow

* Nothing here bounds the doubling defect `D` or any quantity of the Wilson measure. No separation theorem for `D` is
  proved. The sign of the second-order term is a sign for `log Z` of a model; the sign of its doubling combination
  `2^d Φ(L) − Φ(2L)` is not computed.
* §1 is a Taylor expansion at a fixed link configuration as `t → 0`. It carries no measure and no uniformity in the
  volume.
* The Gaussian-plus-cubic model is not the Wilson measure. In the Wilson action the plaquette also has a quartic term
  at the same order `g²` in `log Z` (the coupling `g² = 1/β` after `A → A/√β`), and a Haar Jacobian and a gauge fixing
  that this model omits, so `sunset` is not the whole `g²` term of the lattice theory.
* Compact `U(1)` is outside the statement that commuting fields do not couple modes: the cubic term vanishes, but
  `1 − cos` has a quartic term in `F`, which couples modes. `cubic_comm` is a statement at cubic order.
* `sunset` is a defined sum: its relation to a complex Gaussian is the shape of `cubicForm_second`, not a theorem here.
  Tadpole terms, where two legs of the vertex contract with each other, are excluded by the choice of `𝒯`.
* `formFactor_witness` is one configuration on the smallest torus, with polarizations not all transverse; no statement
  about the gauge orbit is made, and the sign and size of `sunset` on a growing window are not computed.
* The single-plaquette moment of §4 vanishes for `SU(2)`, which confines, so it does not separate the groups.
-/

noncomputable section

namespace MassGap.HarmonicVertex

open Filter Asymptotics Topology MeasureTheory ProbabilityTheory
open scoped NNReal

/-! ## 1. The cubic term of the Wilson density -/

section Jet

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- **A third-order expansion at `t = 0` with constant term `1`.** DERIVED: `3` the order of the vertex; `4` the first
order dropped. -/
def Jet3 (f : ℝ → 𝔸) (c₁ c₂ c₃ : 𝔸) : Prop :=
  (fun t : ℝ => f t - (1 + t • c₁ + t ^ 2 • c₂ + t ^ 3 • c₃)) =O[𝓝 0] fun t => t ^ 4

/-- The product of two cubic polynomials with constant term `1`, up to degree `3` and the rest. DERIVED: the numerals
are the degrees: `3` the order of the vertex, `4` the first order dropped. -/
theorem poly_mul (t : ℝ) (c₁ c₂ c₃ d₁ d₂ d₃ : 𝔸) :
    (1 + t • c₁ + t ^ 2 • c₂ + t ^ 3 • c₃) * (1 + t • d₁ + t ^ 2 • d₂ + t ^ 3 • d₃)
      = (1 + t • (c₁ + d₁) + t ^ 2 • (c₂ + c₁ * d₁ + d₂) + t ^ 3 • (c₃ + c₂ * d₁ + c₁ * d₂ + d₃))
        + t ^ 4 • ((c₁ * d₃ + c₂ * d₂ + c₃ * d₁) + t • (c₂ * d₃ + c₃ * d₂) + t ^ 2 • (c₃ * d₃)) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul]
  module

/-- A continuous function is bounded at `0`. DERIVED: `1` the constant comparison. -/
theorem bigO_one_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f) :
    f =O[𝓝 0] fun _ => (1 : ℝ) :=
  (hf.tendsto 0).isBigO_one ℝ

/-- **Expansions multiply by the Cauchy product.** DERIVED: no numeral beyond `Jet3`. -/
theorem Jet3.mul {f g : ℝ → 𝔸} {c₁ c₂ c₃ d₁ d₂ d₃ : 𝔸} (hf : Jet3 f c₁ c₂ c₃) (hg : Jet3 g d₁ d₂ d₃) :
    Jet3 (fun t => f t * g t) (c₁ + d₁) (c₂ + c₁ * d₁ + d₂) (c₃ + c₂ * d₁ + c₁ * d₂ + d₃) := by
  have hf' : (fun t : ℝ => f t - (1 + t • c₁ + t ^ 2 • c₂ + t ^ 3 • c₃)) =O[𝓝 0] fun t => t ^ 4 := hf
  have hg' : (fun t : ℝ => g t - (1 + t • d₁ + t ^ 2 • d₂ + t ^ 3 • d₃)) =O[𝓝 0] fun t => t ^ 4 := hg
  have hpf : (fun t : ℝ => 1 + t • c₁ + t ^ 2 • c₂ + t ^ 3 • c₃) =O[𝓝 0] fun _ => (1 : ℝ) :=
    bigO_one_of_continuous (by fun_prop)
  have hpg : (fun t : ℝ => 1 + t • d₁ + t ^ 2 • d₂ + t ^ 3 • d₃) =O[𝓝 0] fun _ => (1 : ℝ) :=
    bigO_one_of_continuous (by fun_prop)
  have ht : (fun t : ℝ => t ^ 4) =O[𝓝 0] fun _ => (1 : ℝ) := bigO_one_of_continuous (by fun_prop)
  have hg1 : g =O[𝓝 0] fun _ => (1 : ℝ) :=
    ((hg'.trans ht).add hpg).congr_left fun t => sub_add_cancel _ _
  have hQ : (fun t : ℝ => (c₁ * d₃ + c₂ * d₂ + c₃ * d₁) + t • (c₂ * d₃ + c₃ * d₂) + t ^ 2 • (c₃ * d₃))
      =O[𝓝 0] fun _ => (1 : ℝ) := bigO_one_of_continuous (by fun_prop)
  have h1 := hf'.mul hg1
  have h2 := hpf.mul hg'
  have h3 := (isBigO_refl (fun t : ℝ => t ^ 4) (𝓝 0)).smul hQ
  simp only [mul_one, one_mul, smul_eq_mul] at h1 h2 h3
  refine ((h1.add h2).add h3).congr_left fun t => ?_
  rw [sub_mul, mul_sub, ← add_sub_assoc, sub_add_cancel, sub_add_eq_add_sub, poly_mul]
  abel

variable [CompleteSpace 𝔸]

/-- **The exponential through third order.** DERIVED: `½`, `⅙` the inverse factorials (`6 = 3!`); `3` the
order of the vertex; `4` the first order dropped. -/
theorem exp_jet (x : 𝔸) :
    Jet3 (fun t : ℝ => NormedSpace.exp (t • x)) x ((1 / 2 : ℝ) • x ^ 2) ((1 / 6 : ℝ) • x ^ 3) := by
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := 𝔸)).isBigO_sub_partialSum_pow 4
  have ht : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => t • x := by fun_prop
    simpa using hc.tendsto 0
  have h2 := h.comp_tendsto ht
  have h3 : (fun t : ℝ => ‖t • x‖ ^ 4) =O[𝓝 0] fun t => t ^ 4 := by
    refine IsBigO.of_bound (‖x‖ ^ 4) (Eventually.of_forall fun t => ?_)
    rw [norm_pow, norm_pow, norm_norm, norm_smul, mul_pow, mul_comm, Real.norm_eq_abs]
  refine (h2.trans (by simpa [Function.comp_def] using h3)).congr_left fun t => ?_
  simp only [Function.comp_apply, zero_add, FormalMultilinearSeries.partialSum,
    Finset.sum_range_succ, Finset.sum_range_zero, NormedSpace.expSeries_apply_eq, smul_pow]
  simp only [Nat.factorial]
  norm_num
  module

/-- **The exponential through second order.** DERIVED: `½` the inverse factorial; `3` the first order dropped. -/
theorem exp_sub_quad (y : ℝ → 𝔸) (hy : Tendsto y (𝓝 0) (𝓝 0)) (hy3 : (fun t => ‖y t‖ ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3) :
    (fun t => NormedSpace.exp (y t) - (1 + y t + (1 / 2 : ℝ) • y t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := 𝔸)).isBigO_sub_partialSum_pow 3
  refine ((h.comp_tendsto hy).trans (by simpa [Function.comp_def] using hy3)).congr_left fun t => ?_
  simp only [Function.comp_apply, zero_add, FormalMultilinearSeries.partialSum,
    Finset.sum_range_succ, Finset.sum_range_zero, NormedSpace.expSeries_apply_eq]
  simp only [Nat.factorial]
  norm_num

end Jet

section Plaq

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The ring commutator. No numeral. -/
def br (x y : A) : A := x * y - y * x

/-- **The first-order plaquette field**, the sum of the four signed link fields. No numeral. -/
def curlF (a b c d : A) : A := a + b + c + d

/-- **The commutator sum** `K = Σ_{i<j} [xᵢ, xⱼ]`, in the order of the plaquette. No numeral. -/
def comK (a b c d : A) : A := br a b + br a c + br a d + br b c + br b d + br c d

/-- **The second-order coefficient of the plaquette.** DERIVED: `½` the inverse factorial. -/
def P2 (a b c d : A) : A :=
  (1 / 2 : ℝ) • (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + (a * b + a * c + a * d + b * c + b * d + c * d)

/-- **The third-order coefficient of the plaquette.** DERIVED: `⅙`, `½` the inverse factorials. -/
def P3 (a b c d : A) : A :=
  (1 / 6 : ℝ) • (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3)
    + (1 / 2 : ℝ) • (a ^ 2 * b + a ^ 2 * c + a ^ 2 * d + b ^ 2 * c + b ^ 2 * d + c ^ 2 * d
        + a * b ^ 2 + a * c ^ 2 + a * d ^ 2 + b * c ^ 2 + b * d ^ 2 + c * d ^ 2)
    + (a * b * c + a * b * d + a * c * d + b * c * d)

/-- **`P₂ = ½F² + ½K`**: the second-order coefficient is the square of the field plus the commutators.
DERIVED: `½` the inverse factorial. -/
theorem P2_eq (a b c d : A) :
    P2 a b c d = (1 / 2 : ℝ) • (curlF a b c d) ^ 2 + (1 / 2 : ℝ) • comK a b c d := by
  simp only [P2, curlF, comK, br, sq, add_mul, mul_add, smul_add, smul_sub]
  module

variable (τ : A →ₗ[ℝ] ℝ) (hτ : ∀ x y, τ (x * y) = τ (y * x))

include hτ

/-- A cyclic functional rotates a right-nested triple word. No numeral. -/
theorem tau_rot (x y z : A) : τ (x * (y * z)) = τ (y * (z * x)) := by
  rw [hτ, mul_assoc]

/-- A cyclic functional kills a commutator. No numeral. -/
theorem tau_br (x y : A) : τ (br x y) = 0 := by
  rw [br, map_sub, hτ, sub_self]

/-- A cyclic functional kills the commutator sum. No numeral. -/
theorem tau_comK (a b c d : A) : τ (comK a b c d) = 0 := by
  simp only [comK, map_add, tau_br τ hτ, add_zero]

/-- **`τ(P₂) = ½ τ(F²)`.** DERIVED: `½` the inverse factorial. -/
theorem tau_P2 (a b c d : A) : τ (P2 a b c d) = (1 / 2) * τ ((curlF a b c d) ^ 2) := by
  rw [P2_eq, map_add, map_smul, map_smul, tau_comK τ hτ, smul_zero, add_zero, smul_eq_mul]

/-- **`τ(P₃) = ⅙ τ(F³) + ½ τ(F K)`**: the plaquette's third-order term is the cube of the field plus the commutator
vertex. DERIVED: `⅙`, `½` the inverse factorials (`6 = 3!`); `3` the order of the vertex. -/
theorem tau_P3 (a b c d : A) :
    τ (P3 a b c d) = (1 / 6) * τ ((curlF a b c d) ^ 3) + (1 / 2) * τ (curlF a b c d * comK a b c d) := by
  have rot := tau_rot τ hτ
  simp only [P3, curlF, comK, br, pow_three, sq, add_mul, mul_add, sub_mul, mul_sub, mul_assoc, map_add, map_sub,
    map_smul, smul_eq_mul]
  simp only [(rot a a b).symm, (rot a a c).symm, (rot a a d).symm, (rot b a a), (rot b a b), (rot b a c), (rot b a d),
    (rot a b b).symm, (rot a b c).symm, (rot b b c).symm, (rot a b d).symm, (rot b b d).symm, (rot c a a), (rot c a b),
    (rot c a c), (rot c a d), (rot a c b).symm, (rot c b b), (rot c b c), (rot c b d), (rot a c c).symm,
    (rot b c c).symm, (rot a c d).symm, (rot b c d).symm, (rot c c d).symm, (rot d a a), (rot d a b), (rot d a c),
    (rot d a d), (rot a d b).symm, (rot d b b), (rot d b c), (rot d b d), (rot a d c).symm, (rot b d c).symm,
    (rot d c c), (rot d c d), (rot a d d).symm, (rot b d d).symm, (rot c d d).symm]
  ring

end Plaq

section Holo

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The plaquette holonomy**, `exp(t x₁) exp(t x₂) exp(t x₃) exp(t x₄)`. No numeral. -/
def holo (a b c d : 𝔸) (t : ℝ) : 𝔸 :=
  NormedSpace.exp (t • a) * NormedSpace.exp (t • b) * NormedSpace.exp (t • c) * NormedSpace.exp (t • d)

/-- **The plaquette through third order.** DERIVED: no numeral beyond `Jet3`. -/
theorem holo_jet (a b c d : 𝔸) : Jet3 (holo a b c d) (curlF a b c d) (P2 a b c d) (P3 a b c d) := by
  have h := ((exp_jet a).mul (exp_jet b)).mul (exp_jet c) |>.mul (exp_jet d)
  have e1 : (a + b + c + d) = curlF a b c d := rfl
  have e2 : ((1 / 2 : ℝ) • a ^ 2 + a * b + (1 / 2 : ℝ) • b ^ 2 + (a + b) * c + (1 / 2 : ℝ) • c ^ 2
      + (a + b + c) * d + (1 / 2 : ℝ) • d ^ 2) = P2 a b c d := by
    simp only [P2, add_mul, smul_add]
    module
  have e3 : ((1 / 6 : ℝ) • a ^ 3 + (1 / 2 : ℝ) • a ^ 2 * b + a * (1 / 2 : ℝ) • b ^ 2 + (1 / 6 : ℝ) • b ^ 3
      + ((1 / 2 : ℝ) • a ^ 2 + a * b + (1 / 2 : ℝ) • b ^ 2) * c + (a + b) * (1 / 2 : ℝ) • c ^ 2
      + (1 / 6 : ℝ) • c ^ 3
      + ((1 / 2 : ℝ) • a ^ 2 + a * b + (1 / 2 : ℝ) • b ^ 2 + (a + b) * c + (1 / 2 : ℝ) • c ^ 2) * d
      + (a + b + c) * (1 / 2 : ℝ) • d ^ 2 + (1 / 6 : ℝ) • d ^ 3) = P3 a b c d := by
    simp only [P3, add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm]
    module
  have h' : Jet3 (holo a b c d) (a + b + c + d)
      ((1 / 2 : ℝ) • a ^ 2 + a * b + (1 / 2 : ℝ) • b ^ 2 + (a + b) * c + (1 / 2 : ℝ) • c ^ 2
      + (a + b + c) * d + (1 / 2 : ℝ) • d ^ 2)
      ((1 / 6 : ℝ) • a ^ 3 + (1 / 2 : ℝ) • a ^ 2 * b + a * (1 / 2 : ℝ) • b ^ 2 + (1 / 6 : ℝ) • b ^ 3
      + ((1 / 2 : ℝ) • a ^ 2 + a * b + (1 / 2 : ℝ) • b ^ 2) * c + (a + b) * (1 / 2 : ℝ) • c ^ 2
      + (1 / 6 : ℝ) • c ^ 3
      + ((1 / 2 : ℝ) • a ^ 2 + a * b + (1 / 2 : ℝ) • b ^ 2 + (a + b) * c + (1 / 2 : ℝ) • c ^ 2) * d
      + (a + b + c) * (1 / 2 : ℝ) • d ^ 2 + (1 / 6 : ℝ) • d ^ 3) := h
  rwa [e1, e2, e3] at h'

/-- **The holonomy is `exp(t F + ½ t² K)` through second order**, the first terms of Baker–Campbell–Hausdorff.
DERIVED: `½` from `P2_eq`; `3` the first order dropped. -/
theorem bch_second (a b c d : 𝔸) :
    (fun t : ℝ => holo a b c d t
        - NormedSpace.exp (t • curlF a b c d + t ^ 2 • (1 / 2 : ℝ) • comK a b c d))
      =O[𝓝 0] fun t => t ^ 3 := by
  set F := curlF a b c d
  set K := comK a b c d
  set y : ℝ → 𝔸 := fun t => t • F + t ^ 2 • (1 / 2 : ℝ) • K with hy
  have hy1 : y =O[𝓝 0] fun t : ℝ => t := by
    have h1 : (fun t : ℝ => t • F) =O[𝓝 0] fun t : ℝ => t :=
      IsBigO.of_bound ‖F‖ (Eventually.of_forall fun t => by rw [norm_smul, mul_comm])
    have h2 : (fun t : ℝ => t ^ 2 • (1 / 2 : ℝ) • K) =O[𝓝 0] fun t : ℝ => t := by
      have h3 := (isBigO_refl (fun t : ℝ => t) (𝓝 0)).smul
        (bigO_one_of_continuous (f := fun t : ℝ => t • (1 / 2 : ℝ) • K) (by fun_prop))
      simp only [smul_eq_mul, mul_one] at h3
      refine h3.congr_left fun t => ?_
      rw [smul_smul, sq]
    exact h1.add h2
  have hyt : Tendsto y (𝓝 0) (𝓝 0) := by
    have hc : Continuous y := by rw [hy]; fun_prop
    simpa [hy] using hc.tendsto 0
  have hy3 : (fun t => ‖y t‖ ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    simpa using (hy1.norm_left).pow 3
  have he := exp_sub_quad y hyt hy3
  have hj : (fun t : ℝ => holo a b c d t - (1 + t • F + t ^ 2 • P2 a b c d + t ^ 3 • P3 a b c d))
      =O[𝓝 0] fun t => t ^ 4 := holo_jet a b c d
  have ht4 : (fun t : ℝ => t ^ 4) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    have := (isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 0)).mul
      (bigO_one_of_continuous (f := fun t : ℝ => t) (by fun_prop))
    simp only [mul_one] at this
    exact this.congr_left fun t => by ring
  have hrest : (fun t : ℝ => t ^ 3 • (P3 a b c d - (F * ((1 / 2 : ℝ) • K) + ((1 / 2 : ℝ) • K) * F)
        * ((1 / 2 : ℝ) • (1 : 𝔸)) - t • ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • K) ^ 2)))
      =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    have := (isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 0)).smul
      (bigO_one_of_continuous (f := fun t : ℝ => P3 a b c d
        - (F * ((1 / 2 : ℝ) • K) + ((1 / 2 : ℝ) • K) * F) * ((1 / 2 : ℝ) • (1 : 𝔸))
        - t • ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • K) ^ 2)) (by fun_prop))
    simpa only [smul_eq_mul, mul_one] using this
  refine ((hj.trans ht4).add (hrest.sub he)).congr_left fun t => ?_
  have hP2 : P2 a b c d = (1 / 2 : ℝ) • F ^ 2 + (1 / 2 : ℝ) • K := P2_eq a b c d
  simp only [hy, hP2, sq, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_sub,
    smul_smul]
  simp only [pow_succ, pow_zero, one_mul]
  module

/-- **The expansion passes through a continuous functional.** DERIVED: no numeral beyond `Jet3`. -/
theorem Jet3.map {f : ℝ → 𝔸} {c₁ c₂ c₃ : 𝔸} (h : Jet3 f c₁ c₂ c₃) (τ : 𝔸 →L[ℝ] ℝ) :
    (fun t => τ (f t) - (τ 1 + t * τ c₁ + t ^ 2 * τ c₂ + t ^ 3 * τ c₃)) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  refine (τ.isBigO_comp _ _ |>.trans h).congr_left fun t => ?_
  simp only [map_sub, map_add, map_smul, smul_eq_mul]

end Holo

section Wilson

open Matrix

/-- The `N × N` complex matrices. No numeral. -/
abbrev Mat (N : ℕ) : Type := Matrix (Fin N) (Fin N) ℂ

variable {N : ℕ}

/-- **The real part of the trace**, as a real-linear functional. No numeral. -/
def reTr (N : ℕ) : Mat N →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ Matrix.traceLinearMap (Fin N) ℝ ℂ

theorem reTr_apply (x : Mat N) : reTr N x = (Matrix.trace x).re := rfl

/-- The real part of the trace is cyclic. No numeral. -/
theorem reTr_comm (x y : Mat N) : reTr N (x * y) = reTr N (y * x) := by
  simp only [reTr_apply, Matrix.trace_mul_comm x y]

/-- **The Wilson density along a plaquette ray**, `1 − (1/N) Re tr U(t)`. DERIVED: the `1`s are the normalization of
`WilsonAction.wilsonDensity`. -/
def wil (a b c d : Mat N) (t : ℝ) : ℝ :=
  open scoped Matrix.Norms.Operator in
  1 - (1 / (N : ℝ)) * (Matrix.trace (holo a b c d t)).re

/-- `wil` is the tree's `wilsonDensity` at any `SU(N)` element equal to the holonomy. No numeral. -/
theorem wilsonDensity_eq_wil (a b c d : Mat N) (t : ℝ) (U : MassGap.SUN.SU N)
    (hU : (U : Mat N) = (open scoped Matrix.Norms.Operator in holo a b c d t)) :
    WilsonAction.wilsonDensity U = wil a b c d t := by
  rw [WilsonAction.wilsonDensity, hU, wil]

/-- **The cubic coefficient of the Wilson density**, `−(1/N) Re tr P₃`. DERIVED: `1/N` the density's normalization. -/
def cubicCoeff (a b c d : Mat N) : ℝ := -(1 / (N : ℝ)) * (Matrix.trace (P3 a b c d)).re

/-- **The Wilson density through third order, for any four matrices.** DERIVED: `4` the first order dropped; `1/N` the
density's normalization; `0` the excluded colour count; `3` the order of the vertex. -/
theorem wilson_expansion (hN : N ≠ 0) (a b c d : Mat N) :
    (fun t : ℝ => wil a b c d t
        - (t * (-(1 / (N : ℝ)) * (Matrix.trace (curlF a b c d)).re)
          + t ^ 2 * (-(1 / (N : ℝ)) * (Matrix.trace (P2 a b c d)).re)
          + t ^ 3 * cubicCoeff a b c d))
      =O[𝓝 0] fun t => t ^ 4 := by
  open scoped Matrix.Norms.Operator in
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let τ : Mat N →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (reTr N)
  have h : (fun t : ℝ => (Matrix.trace (holo a b c d t)).re
      - ((Matrix.trace (1 : Mat N)).re + t * (Matrix.trace (curlF a b c d)).re
        + t ^ 2 * (Matrix.trace (P2 a b c d)).re + t ^ 3 * (Matrix.trace (P3 a b c d)).re))
      =O[𝓝 0] fun t : ℝ => t ^ 4 := (holo_jet a b c d).map τ
  have h' := h.const_mul_left (-(1 / (N : ℝ)))
  refine h'.congr_left fun t => ?_
  simp only [wil, cubicCoeff, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]
  field_simp
  ring

/-- **An anti-Hermitian matrix has a purely imaginary cube trace.** DERIVED: `3` the odd power. -/
theorem re_trace_cube_of_skew {F : Mat N} (hF : Fᴴ = -F) : (Matrix.trace (F ^ 3)).re = 0 := by
  have h : (F ^ 3)ᴴ = -(F ^ 3) := by
    rw [Matrix.conjTranspose_pow, hF]
    exact Odd.neg_pow (by decide) F
  have h2 := Matrix.trace_conjTranspose (F ^ 3)
  rw [h, Matrix.trace_neg] at h2
  have h3 := congrArg Complex.re h2
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at h3
  linarith

/-- The sum of anti-Hermitian matrices is anti-Hermitian. No numeral. -/
theorem curlF_skew {a b c d : Mat N} (ha : aᴴ = -a) (hb : bᴴ = -b) (hc : cᴴ = -c) (hd : dᴴ = -d) :
    (curlF a b c d)ᴴ = -curlF a b c d := by
  simp only [curlF, Matrix.conjTranspose_add, ha, hb, hc, hd]
  abel

/-- **The cubic term is a sum of commutator terms**: for anti-Hermitian links,
`c₃ = −(1/2N) Σ_{i<j} Re tr(F [xᵢ, xⱼ])`. The cube of the field drops out, and what is left is the `f^{abc}` vertex.
DERIVED: `½` the inverse factorial; `1/N` the density's normalization. -/
theorem cubic_eq_commutator {a b c d : Mat N} (ha : aᴴ = -a) (hb : bᴴ = -b) (hc : cᴴ = -c) (hd : dᴴ = -d) :
    cubicCoeff a b c d = -(1 / (2 * (N : ℝ))) *
      ((Matrix.trace (curlF a b c d * br a b)).re + (Matrix.trace (curlF a b c d * br a c)).re
        + (Matrix.trace (curlF a b c d * br a d)).re + (Matrix.trace (curlF a b c d * br b c)).re
        + (Matrix.trace (curlF a b c d * br b d)).re + (Matrix.trace (curlF a b c d * br c d)).re) := by
  have h := tau_P3 (reTr N) reTr_comm a b c d
  simp only [reTr_apply] at h
  rw [re_trace_cube_of_skew (curlF_skew ha hb hc hd), mul_zero, zero_add] at h
  rw [cubicCoeff, h]
  simp only [comK, mul_add, Matrix.trace_add, Complex.add_re]
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  · field_simp

/-- **The Wilson density of `su(N)` links through third order**: no linear term, the quadratic form of the field, and
the commutator vertex. DERIVED: as `wilson_expansion` (`3` the order of the vertex, `4` the first order
dropped), and `P2_eq`. -/
theorem wilson_su_expansion (hN : N ≠ 0) {a b c d : Mat N} (hF : Matrix.trace (curlF a b c d) = 0) :
    (fun t : ℝ => wil a b c d t
        - (t ^ 2 * (-(1 / (2 * (N : ℝ))) * (Matrix.trace ((curlF a b c d) ^ 2)).re)
          + t ^ 3 * cubicCoeff a b c d))
      =O[𝓝 0] fun t => t ^ 4 := by
  have h := wilson_expansion hN a b c d
  refine h.congr_left fun t => ?_
  have h2 := tau_P2 (reTr N) reTr_comm a b c d
  simp only [reTr_apply] at h2
  rw [hF, h2]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [Complex.zero_re, mul_zero, zero_add]
  field_simp

/-- A commutator of commuting elements is `0`. No numeral. -/
theorem br_of_commute {x y : Mat N} (h : Commute x y) : br x y = 0 := by
  rw [br, h.eq, sub_self]

/-- **Commuting links have no cubic term**, identically: `U(1)` (`N = 1`, anti-Hermitian scalars) and the Cartan
subspace. DERIVED: `0` the value. -/
theorem cubic_comm {a b c d : Mat N} (ha : aᴴ = -a) (hb : bᴴ = -b) (hc : cᴴ = -c) (hd : dᴴ = -d)
    (hab : Commute a b) (hac : Commute a c) (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d)
    (hcd : Commute c d) : cubicCoeff a b c d = 0 := by
  rw [cubic_eq_commutator ha hb hc hd, br_of_commute hab, br_of_commute hac, br_of_commute had,
    br_of_commute hbc, br_of_commute hbd, br_of_commute hcd]
  simp

/-- **The `su(2)` element of real coordinates `u`**, `X_u = Σ uₐ eₐ`, with `eₐ = −(i/2) σₐ`. DERIVED: `½` the
normalization `[e₁, e₂] = e₃`; `3` the dimension of `su(2)`. -/
def su2X (u : Fin 3 → ℝ) : Mat 2 :=
  !![-(u 2 : ℂ) * Complex.I / 2, -(u 0 : ℂ) * Complex.I / 2 - (u 1 : ℂ) / 2;
     -(u 0 : ℂ) * Complex.I / 2 + (u 1 : ℂ) / 2, (u 2 : ℂ) * Complex.I / 2]

/-- `su2X` is anti-Hermitian. No numeral. -/
theorem su2X_skew (u : Fin 3 → ℝ) : (su2X u)ᴴ = -su2X u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2X, Matrix.conjTranspose_apply, Complex.ext_iff] <;> ring_nf <;> simp

/-- `su2X` is traceless. No numeral. -/
theorem su2X_trace (u : Fin 3 → ℝ) : Matrix.trace (su2X u) = 0 := by
  simp only [su2X, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **The `su(2)` vertex is the triple product**: `tr(X_u [X_v, X_w]) = −½ det(u, v, w)`, the structure constants
`f^{abc} = ε^{abc}` with `tr(eₐ e_b) = −½ δ_{ab}`. DERIVED: `½` the normalization of `eₐ`; `3` the
dimension of `su(2)`, the coordinates of `u, v, w`. -/
theorem su2_vertex (u v w : Fin 3 → ℝ) :
    Matrix.trace (su2X u * br (su2X v) (su2X w))
      = (-(1 / 2 : ℝ) * (u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0)
          + u 2 * (v 0 * w 1 - v 1 * w 0)) : ℝ) := by
  simp only [su2X, br, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  ring_nf
  simp only [Complex.I_sq, show Complex.I ^ 3 = -Complex.I from by rw [pow_succ, Complex.I_sq]; ring]
  ring

/-- CHOSEN: the first `su(2)` generator. No numeral beyond the basis vector. -/
def e₁ : Mat 2 := su2X ![1, 0, 0]
/-- CHOSEN: the second `su(2)` generator. No numeral beyond the basis vector. -/
def e₂ : Mat 2 := su2X ![0, 1, 0]
/-- CHOSEN: the third `su(2)` generator. No numeral beyond the basis vector. -/
def e₃ : Mat 2 := su2X ![0, 0, 1]

/-- The field of the chosen triple. DERIVED: the coordinates of the sum. -/
theorem curlF_triple : curlF e₁ e₂ e₃ (0 : Mat 2) = su2X ![1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [curlF, e₁, e₂, e₃, su2X] <;> ring

/-- **The cubic term of a chosen `su(2)` triple is `1/8`.** CHOSEN: the links `(e₁, e₂, e₃, 0)`. DERIVED: `−(1/4)(−½)`,
from `su2_vertex`: the three determinants are `1, −1, 1`, and `1/2N = 1/4`; so `8 = 4 · 2`. -/
theorem cubic_su2 : cubicCoeff e₁ e₂ e₃ (0 : Mat 2) = 1 / 8 := by
  have h0 : (0 : Mat 2)ᴴ = -(0 : Mat 2) := by simp
  have hc := cubic_eq_commutator (a := e₁) (b := e₂) (c := e₃) (d := 0) (su2X_skew _) (su2X_skew _)
    (su2X_skew _) h0
  rw [hc, curlF_triple]
  have hb0 : ∀ x : Mat 2, br x 0 = 0 := fun x => by simp [br]
  rw [hb0, hb0, hb0]
  simp only [e₁, e₂, e₃, su2_vertex]
  simp <;> norm_num

/-- **The cubic term does not vanish on `su(2)`.** CHOSEN: the triple of `cubic_su2`. No numeral beyond that. -/
theorem cubic_su2_ne : cubicCoeff e₁ e₂ e₃ (0 : Mat 2) ≠ 0 := by
  rw [cubic_su2]
  norm_num

end Wilson

/-! ## 2. The momentum rule -/

section Momentum

variable {d L : ℕ} [NeZero L]

/-- The torus `(ℤ/L)^d`. No numeral. -/
abbrev Torus (d L : ℕ) : Type := Fin d → ZMod L

/-- **The plane wave** `e_k(x) = exp(2πi k·x / L)`. No numeral. -/
def wave (k x : Torus d L) : ℂ := ZMod.stdAddChar (k ⬝ᵥ x)

theorem wave_add_left (k k' x : Torus d L) : wave (k + k') x = wave k x * wave k' x := by
  simp only [wave, add_dotProduct, AddChar.map_add_eq_mul]

theorem wave_add_right (k x y : Torus d L) : wave k (x + y) = wave k x * wave k y := by
  simp only [wave, dotProduct_add, AddChar.map_add_eq_mul]

theorem wave_zero_left (x : Torus d L) : wave 0 x = 1 := by
  simp [wave]

/-- The unit vector `ê_μ` of the torus. DERIVED: `1` the lattice spacing. -/
def ehat (μ : Fin d) : Torus d L := Pi.single μ 1

theorem wave_ehat (k : Torus d L) (μ : Fin d) : wave k (ehat μ) = ZMod.stdAddChar (k μ) := by
  simp [wave, ehat]

/-- **The sum of a plane wave over the torus.** DERIVED: `L^d` the number of sites. -/
theorem sum_wave (k : Torus d L) :
    ∑ x : Torus d L, wave k x = if k = 0 then (L : ℂ) ^ d else 0 := by
  split_ifs with hk
  · subst hk
    simp [wave_zero_left, ZMod.card]
  · obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    have hne : wave k (ehat μ) ≠ 1 := by
      rw [wave_ehat]
      intro h
      apply hμ
      rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := L))] at h
      exact ZMod.injective_stdAddChar h
    have hshift : ∑ x : Torus d L, wave k (x + ehat μ) = ∑ x : Torus d L, wave k x :=
      Equiv.sum_comp (Equiv.addRight (ehat μ)) (fun x => wave k x)
    simp only [wave_add_right] at hshift
    rw [← Finset.sum_mul] at hshift
    have h0 : (∑ x : Torus d L, wave k x) * (wave k (ehat μ) - 1) = 0 := by
      rw [mul_sub, mul_one, hshift, sub_self]
    exact (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hne)

/-- **The product of three waves sums to the momentum rule.** DERIVED: `L^d` the number of sites. -/
theorem sum_wave_three (k₁ k₂ k₃ : Torus d L) :
    ∑ x : Torus d L, wave k₁ x * wave k₂ x * wave k₃ x
      = if k₁ + k₂ + k₃ = 0 then (L : ℂ) ^ d else 0 := by
  simp only [← wave_add_left, sum_wave]

variable {R : Type*} [Ring R] [Algebra ℂ R] (τ : R →ₗ[ℂ] ℂ)

/-- The field of a plaquette tuple. DERIVED: `0`–`3` the four links of a plaquette. -/
def curl (y : Fin 4 → R) : R := y 0 + y 1 + y 2 + y 3

/-- The bilinear commutator sum of two plaquette tuples, in the order of the plaquette; `pairs x x = K`. DERIVED: `0`–`3` the four links of a plaquette, taken
in ordered pairs. -/
def pairs (z w : Fin 4 → R) : R :=
  (z 0 * w 1 - w 1 * z 0) + (z 0 * w 2 - w 2 * z 0) + (z 0 * w 3 - w 3 * z 0)
    + (z 1 * w 2 - w 2 * z 1) + (z 1 * w 3 - w 3 * z 1) + (z 2 * w 3 - w 3 * z 2)

/-- **The trilinear vertex** `τ(F_y · K(z, w))`, whose diagonal is the commutator term of the plaquette. No numeral. -/
def triV (y z w : Fin 4 → R) : ℂ := τ (curl y * pairs z w)

/-- **The vertex of a link field at one site.** `triV` on the diagonal is `τ(F K)` of `cubic_eq_commutator`. No
numeral. -/
theorem triV_diag (a b c e : R) :
    triV τ ![a, b, c, e] ![a, b, c, e] ![a, b, c, e]
      = τ ((a + b + c + e) * ((a * b - b * a) + (a * c - c * a) + (a * e - e * a)
          + (b * c - c * b) + (b * e - e * b) + (c * e - e * c))) := by
  simp [triV, curl, pairs]

theorem curl_smul (α : ℂ) (y : Fin 4 → R) : curl (α • y) = α • curl y := by
  simp only [curl, Pi.smul_apply, smul_add]

theorem pairs_smul (β γ : ℂ) (z w : Fin 4 → R) : pairs (β • z) (γ • w) = (β * γ) • pairs z w := by
  simp only [pairs, Pi.smul_apply, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  module

/-- The vertex is trilinear under scalars. No numeral. -/
theorem triV_smul (α β γ : ℂ) (y z w : Fin 4 → R) :
    triV τ (α • y) (β • z) (γ • w) = α * β * γ * triV τ y z w := by
  rw [triV, curl_smul, pairs_smul, smul_mul_assoc, mul_smul_comm, smul_smul, map_smul, smul_eq_mul, triV]
  ring

theorem curl_sum {M : Type*} (s : Finset M) (y : M → Fin 4 → R) :
    curl (∑ m ∈ s, y m) = ∑ m ∈ s, curl (y m) := by
  simp only [curl, Finset.sum_apply, Finset.sum_add_distrib]

theorem pairs_sum_left {M : Type*} (s : Finset M) (z : M → Fin 4 → R) (w : Fin 4 → R) :
    pairs (∑ m ∈ s, z m) w = ∑ m ∈ s, pairs (z m) w := by
  simp only [pairs, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem pairs_sum_right {M : Type*} (s : Finset M) (z : Fin 4 → R) (w : M → Fin 4 → R) :
    pairs z (∑ m ∈ s, w m) = ∑ m ∈ s, pairs z (w m) := by
  simp only [pairs, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- **The vertex expands over sums in all three slots.** No numeral. -/
theorem triV_sum {M : Type*} (s : Finset M) (y z w : M → Fin 4 → R) :
    triV τ (∑ m ∈ s, y m) (∑ m ∈ s, z m) (∑ m ∈ s, w m)
      = ∑ m ∈ s, ∑ n ∈ s, ∑ l ∈ s, triV τ (y m) (z n) (w l) := by
  simp only [triV, curl_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pairs_sum_left]
  simp only [pairs_sum_right, Finset.mul_sum, map_sum]

/-- A link field on the torus: `A μ x` is the Lie-algebra link at `x` in direction `μ`. No numeral. -/
abbrev LinkF (R : Type*) (d L : ℕ) : Type _ := Fin d → Torus d L → R

/-- **The signed links of the plaquette at `x` in the plane `(μ, ν)`**: the four links with the reversed ones negated.
DERIVED: `4` the links of a plaquette. -/
def plaqT (μ ν : Fin d) (A : LinkF R d L) (x : Torus d L) : Fin 4 → R :=
  ![A μ x, A ν (x + ehat μ), -A μ (x + ehat ν), -A ν x]

/-- **A plane-wave link field** with polarization `X`, `A_ρ(x) = e_k(x) X_ρ`. No numeral. -/
def waveF (k : Torus d L) (X : Fin d → R) : LinkF R d L := fun ρ x => wave k x • X ρ

/-- **The plaquette tuple of a mode**, with the phases of the shifted links. DERIVED: `4` the links of a plaquette. -/
def modeT (μ ν : Fin d) (k : Torus d L) (X : Fin d → R) : Fin 4 → R :=
  ![X μ, wave k (ehat μ) • X ν, -(wave k (ehat ν) • X μ), -X ν]

/-- A plane wave's plaquette tuple is the wave at `x` times the mode's tuple. No numeral. -/
theorem plaqT_waveF (μ ν : Fin d) (k : Torus d L) (X : Fin d → R) (x : Torus d L) :
    plaqT μ ν (waveF k X) x = wave k x • modeT μ ν k X := by
  ext i
  fin_cases i <;> simp [plaqT, waveF, modeT, wave_add_right, smul_smul, smul_neg]

/-- The plaquette tuple is additive in the field. No numeral. -/
theorem plaqT_sum {M : Type*} (s : Finset M) (μ ν : Fin d) (A : M → LinkF R d L) (x : Torus d L) :
    plaqT μ ν (∑ m ∈ s, A m) x = ∑ m ∈ s, plaqT μ ν (A m) x := by
  ext i
  fin_cases i <;> simp [plaqT, Finset.sum_apply]

/-- **The form factor of three modes**: the plaquette vertex with the site phase removed. No numeral. -/
def formFactor (μ ν : Fin d) (k₁ : Torus d L) (X₁ : Fin d → R) (k₂ : Torus d L) (X₂ : Fin d → R)
    (k₃ : Torus d L) (X₃ : Fin d → R) : ℂ :=
  triV τ (modeT μ ν k₁ X₁) (modeT μ ν k₂ X₂) (modeT μ ν k₃ X₃)

/-- **The momentum rule**: the plaquette vertex of three plane waves, summed over sites, is `L^d` times the form factor
when the momenta sum to `0` on the torus, and `0` otherwise. DERIVED: `L^d` the number of sites. -/
theorem momentum_selection (μ ν : Fin d) (k₁ : Torus d L) (X₁ : Fin d → R) (k₂ : Torus d L) (X₂ : Fin d → R)
    (k₃ : Torus d L) (X₃ : Fin d → R) :
    ∑ x : Torus d L, triV τ (plaqT μ ν (waveF k₁ X₁) x) (plaqT μ ν (waveF k₂ X₂) x) (plaqT μ ν (waveF k₃ X₃) x)
      = (if k₁ + k₂ + k₃ = 0 then (L : ℂ) ^ d else 0) * formFactor τ μ ν k₁ X₁ k₂ X₂ k₃ X₃ := by
  simp only [plaqT_waveF, triV_smul, formFactor]
  rw [← Finset.sum_mul, sum_wave_three]

/-- **The difference rule**: a wave at `k₁` crossing the conjugate of a wave at `k₂` drives only `k₁ − k₂`: the third
wave has momentum `k₂ − k₁` or the vertex is `0`. This is the direct transfer between scales. No numeral. -/
theorem momentum_difference (μ ν : Fin d) (k₁ : Torus d L) (X₁ : Fin d → R) (k₂ : Torus d L) (X₂ : Fin d → R)
    (k₃ : Torus d L) (X₃ : Fin d → R) (h : k₃ ≠ k₂ - k₁) :
    ∑ x : Torus d L,
        triV τ (plaqT μ ν (waveF k₁ X₁) x) (plaqT μ ν (waveF (-k₂) X₂) x) (plaqT μ ν (waveF k₃ X₃) x) = 0 := by
  rw [momentum_selection, if_neg, zero_mul]
  intro h0
  apply h
  have : k₃ = -(k₁ + -k₂) := eq_neg_of_add_eq_zero_right h0
  rw [this]
  abel

/-- **The doubling rule**: a wave crossing itself drives only `2k`: the third wave has momentum `−2k` or the vertex is
`0`. DERIVED: `2` the two crossing waves. -/
theorem momentum_double (μ ν : Fin d) (k₁ : Torus d L) (X₁ X₂ : Fin d → R)
    (k₃ : Torus d L) (X₃ : Fin d → R) (h : k₃ ≠ -(2 • k₁)) :
    ∑ x : Torus d L,
        triV τ (plaqT μ ν (waveF k₁ X₁) x) (plaqT μ ν (waveF k₁ X₂) x) (plaqT μ ν (waveF k₃ X₃) x) = 0 := by
  rw [momentum_selection, if_neg, zero_mul]
  intro h0
  apply h
  rw [two_nsmul]
  exact eq_neg_of_add_eq_zero_right h0

/-- **The vertex of a sum of plane waves is the triple sum over modes with the rule.** DERIVED: `L^d` the number of
sites. -/
theorem vertex_modes {M : Type*} (s : Finset M) (μ ν : Fin d) (k : M → Torus d L) (X : M → Fin d → R) :
    ∑ x : Torus d L,
        triV τ (plaqT μ ν (∑ m ∈ s, waveF (k m) (X m)) x) (plaqT μ ν (∑ m ∈ s, waveF (k m) (X m)) x)
          (plaqT μ ν (∑ m ∈ s, waveF (k m) (X m)) x)
      = ∑ m ∈ s, ∑ n ∈ s, ∑ l ∈ s,
          (if k m + k n + k l = 0 then (L : ℂ) ^ d else 0)
            * formFactor τ μ ν (k m) (X m) (k n) (X n) (k l) (X l) := by
  simp only [plaqT_sum, triV_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact momentum_selection τ μ ν _ _ _ _ _ _

/-- The vertex vanishes when its last two slots commute entry by entry. No numeral. -/
theorem triV_of_commute (y z w : Fin 4 → R) (h : ∀ i j, Commute (z i) (w j)) : triV τ y z w = 0 := by
  have hz : ∀ i j, z i * w j - w j * z i = 0 := fun i j => sub_eq_zero.mpr (h i j).eq
  simp [triV, pairs, hz]

/-- Each entry of a mode's tuple is a scalar times a polarization. No numeral. -/
theorem modeT_entry (μ ν : Fin d) (k : Torus d L) (X : Fin d → R) (i : Fin 4) :
    ∃ (c : ℂ) (ρ : Fin d), modeT μ ν k X i = c • X ρ := by
  fin_cases i
  · exact ⟨1, μ, by simp [modeT]⟩
  · exact ⟨_, ν, rfl⟩
  · exact ⟨-wave k (ehat ν), μ, by simp [modeT]⟩
  · exact ⟨-1, ν, by simp [modeT]⟩

/-- Commuting polarizations give commuting tuples. No numeral. -/
theorem modeT_commute (μ ν : Fin d) (k k' : Torus d L) {X Y : Fin d → R} (h : ∀ ρ σ, Commute (X ρ) (Y σ))
    (i j : Fin 4) : Commute (modeT μ ν k X i) (modeT μ ν k' Y j) := by
  obtain ⟨c, ρ, hc⟩ := modeT_entry μ ν k X i
  obtain ⟨c', σ, hc'⟩ := modeT_entry μ ν k' Y j
  rw [hc, hc']
  exact ((h ρ σ).smul_left c).smul_right c'

/-- **Commuting polarizations have zero form factor.** DERIVED: `0` the value. -/
theorem formFactor_comm (μ ν : Fin d) (k₁ : Torus d L) (X₁ : Fin d → R) (k₂ : Torus d L) {X₂ : Fin d → R}
    (k₃ : Torus d L) {X₃ : Fin d → R} (h : ∀ ρ σ, Commute (X₂ ρ) (X₃ σ)) :
    formFactor τ μ ν k₁ X₁ k₂ X₂ k₃ X₃ = 0 :=
  triV_of_commute τ _ _ _ (modeT_commute μ ν k₂ k₃ h)

/-- **For commuting polarizations the mode coupling of the vertex is `0`.** DERIVED: `0` the value. -/
theorem vertex_modes_comm {M : Type*} (s : Finset M) (μ ν : Fin d) (k : M → Torus d L) (X : M → Fin d → R)
    (h : ∀ m n ρ σ, Commute (X m ρ) (X n σ)) :
    ∑ x : Torus d L,
        triV τ (plaqT μ ν (∑ m ∈ s, waveF (k m) (X m)) x) (plaqT μ ν (∑ m ∈ s, waveF (k m) (X m)) x)
          (plaqT μ ν (∑ m ∈ s, waveF (k m) (X m)) x) = 0 := by
  rw [vertex_modes]
  exact Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun l _ => by
    rw [formFactor_comm τ μ ν _ _ _ _ (h n l), mul_zero]

/-- **The symmetrized vertex**: the six orderings of three tuples, the coefficient of the three modes in the cubic form.
DERIVED: `6` the orderings of three legs. -/
def symV (y z w : Fin 4 → R) : ℂ :=
  triV τ y z w + triV τ y w z + triV τ z y w + triV τ z w y + triV τ w y z + triV τ w z y

/-- The symmetrized vertex vanishes on commuting data. DERIVED: `0` the value. -/
theorem symV_of_commute (y z w : Fin 4 → R) (hyz : ∀ i j, Commute (y i) (z j)) (hyw : ∀ i j, Commute (y i) (w j))
    (hzw : ∀ i j, Commute (z i) (w j)) : symV τ y z w = 0 := by
  have hzy : ∀ i j, Commute (z i) (y j) := fun i j => (hyz j i).symm
  have hwy : ∀ i j, Commute (w i) (y j) := fun i j => (hyw j i).symm
  have hwz : ∀ i j, Commute (w i) (z j) := fun i j => (hzw j i).symm
  simp only [symV, triV_of_commute τ _ _ _ hzw, triV_of_commute τ _ _ _ hwz, triV_of_commute τ _ _ _ hyw,
    triV_of_commute τ _ _ _ hwy, triV_of_commute τ _ _ _ hyz, triV_of_commute τ _ _ _ hzy, add_zero]

/-- The planes of the torus, `μ < ν`. No numeral. -/
def planes (d : ℕ) : Finset (Fin d × Fin d) := Finset.univ.filter fun p => p.1 < p.2

/-- **The symmetrized plaquette form factor of three modes, summed over planes.** No numeral. -/
def vertexG {M : Type*} (k : M → Torus d L) (X : M → Fin d → R) (p : M × M × M) : ℂ :=
  ∑ q ∈ planes d, symV τ (modeT q.1 q.2 (k p.1) (X p.1)) (modeT q.1 q.2 (k p.2.1) (X p.2.1))
    (modeT q.1 q.2 (k p.2.2) (X p.2.2))

/-- The weight of a triple of modes in `sunset`: the vertex squared over the propagators, under the rule. DERIVED: `2`
the square. -/
def sunsetWt {M : Type*} (k : M → Torus d L) (X : M → Fin d → R) (lam : M → ℝ) (p : M × M × M) : ℝ :=
  if k p.1 + k p.2.1 + k p.2.2 = 0 then ‖vertexG τ k X p‖ ^ 2 / (lam p.1 * lam p.2.1 * lam p.2.2) else 0

/-- **The second-order sum on the torus**: `Σ_{m,n,l ∈ S} δ(k_m + k_n + k_l) |Γ_{mnl}|² / (λ_m λ_n λ_l)`, over ordered
triples including repeated modes; it is not the distinct-set sum of `cubicForm_second`. A defined
finite sum: the shape of `cubicForm_second` in plane waves. No numeral. -/
def sunset {M : Type*} (k : M → Torus d L) (X : M → Fin d → R) (lam : M → ℝ) (S : Finset M) : ℝ :=
  ∑ p ∈ S ×ˢ S ×ˢ S, sunsetWt τ k X lam p

theorem sunsetWt_nonneg {M : Type*} (k : M → Torus d L) (X : M → Fin d → R) {lam : M → ℝ} {p : M × M × M}
    (h1 : 0 < lam p.1) (h2 : 0 < lam p.2.1) (h3 : 0 < lam p.2.2) : 0 ≤ sunsetWt τ k X lam p := by
  unfold sunsetWt
  split_ifs
  · positivity
  · exact le_rfl

/-- **The second-order sum is non-negative.** DERIVED: `0` the bound. -/
theorem sunset_nonneg {M : Type*} (k : M → Torus d L) (X : M → Fin d → R) {lam : M → ℝ} (S : Finset M)
    (h : ∀ m ∈ S, 0 < lam m) : 0 ≤ sunset τ k X lam S := by
  refine Finset.sum_nonneg fun p hp => ?_
  simp only [Finset.mem_product] at hp
  exact sunsetWt_nonneg τ k X (h _ hp.1) (h _ hp.2.1) (h _ hp.2.2)

/-- **The second-order sum vanishes for commuting polarizations.** DERIVED: `0` the value. -/
theorem sunset_comm {M : Type*} (k : M → Torus d L) (X : M → Fin d → R) (lam : M → ℝ) (S : Finset M)
    (h : ∀ m n ρ σ, Commute (X m ρ) (X n σ)) : sunset τ k X lam S = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  have hv : vertexG τ k X p = 0 := Finset.sum_eq_zero fun q _ =>
    symV_of_commute τ _ _ _ (modeT_commute _ _ _ _ (h _ _)) (modeT_commute _ _ _ _ (h _ _))
      (modeT_commute _ _ _ _ (h _ _))
  simp [sunsetWt, hv]

end Momentum

/-! ## 3. The mode-coupling read -/

section Coupling

variable {M : Type*} [DecidableEq M]

/-- **The additivity defect of a read on sets of modes.** A read that is a sum over modes has defect `0`. No numeral. -/
def modeCoupling (Φ : Finset M → ℝ) (S T : Finset M) : ℝ := Φ (S ∪ T) - Φ S - Φ T

/-- **The triples straddling two mode sets**: the triples in `S ∪ T`, not all in `S` and not all in `T`. No numeral. -/
def straddle (S T : Finset M) : Finset (M × M × M) :=
  ((S ∪ T) ×ˢ (S ∪ T) ×ˢ (S ∪ T)) \ (S ×ˢ S ×ˢ S ∪ T ×ˢ T ×ˢ T)

/-- **The additivity defect of a sum over triples is the sum over straddling triples.** No numeral. -/
theorem triple_coupling (wt : M × M × M → ℝ) {S T : Finset M} (hd : Disjoint S T) :
    modeCoupling (fun U => ∑ p ∈ U ×ˢ U ×ˢ U, wt p) S T = ∑ p ∈ straddle S T, wt p := by
  have hdis : Disjoint (S ×ˢ S ×ˢ S) (T ×ˢ T ×ˢ T) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact Finset.disjoint_left.mp hd (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1
  have hsub : S ×ˢ S ×ˢ S ∪ T ×ˢ T ×ˢ T ⊆ (S ∪ T) ×ˢ (S ∪ T) ×ˢ (S ∪ T) := by
    apply Finset.union_subset <;> intro p hp <;>
      simp only [Finset.mem_product, Finset.mem_union] at hp ⊢ <;> tauto
  have h := Finset.sum_sdiff (f := wt) hsub
  rw [Finset.sum_union hdis] at h
  simp only [modeCoupling, straddle]
  linarith

end Coupling

section Sunset

variable {d L : ℕ} [NeZero L] {R : Type*} [Ring R] [Algebra ℂ R] (τ : R →ₗ[ℂ] ℂ)
variable {M : Type*} [DecidableEq M]

/-- **The additivity defect of the torus sum is the sum over triples straddling `S` and `T`.** With `S` a high band and
`T` a low band, these are the triples of `momentum_difference`: two waves of `S` driving one of `T`. No numeral. -/
theorem sunset_coupling (k : M → Torus d L) (X : M → Fin d → R) (lam : M → ℝ) {S T : Finset M}
    (hd : Disjoint S T) :
    modeCoupling (sunset τ k X lam) S T = ∑ p ∈ straddle S T, sunsetWt τ k X lam p :=
  triple_coupling _ hd

/-- **The additivity defect of the torus sum is non-negative.** DERIVED: `0` the bound. -/
theorem sunset_coupling_nonneg (k : M → Torus d L) (X : M → Fin d → R) {lam : M → ℝ} {S T : Finset M}
    (hd : Disjoint S T) (h : ∀ m ∈ S ∪ T, 0 < lam m) : 0 ≤ modeCoupling (sunset τ k X lam) S T := by
  rw [sunset_coupling τ k X lam hd]
  refine Finset.sum_nonneg fun p hp => ?_
  have hp' := (Finset.mem_sdiff.mp hp).1
  simp only [Finset.mem_product] at hp'
  exact sunsetWt_nonneg τ k X (h _ hp'.1) (h _ hp'.2.1) (h _ hp'.2.2)

end Sunset

section Gaussian

variable {M : Type*} [DecidableEq M]

/-- **The Gaussian integral over the modes in `S`**, with stiffness `lam`. DERIVED: `½` the Gaussian action. -/
def gaussZ (lam : M → ℝ) (S : Finset M) : ℝ :=
  ∫ φ : S → ℝ, Real.exp (-∑ i : S, lam i / 2 * φ i ^ 2)

/-- **The log-partition function of the modes in `S`.** No numeral. -/
def logZ (lam : M → ℝ) (S : Finset M) : ℝ := Real.log (gaussZ lam S)

/-- **The Gaussian integral is a product over modes.** DERIVED: `2π` the Gaussian integral. -/
theorem gaussZ_eq (lam : M → ℝ) (S : Finset M) :
    gaussZ lam S = ∏ i ∈ S, √(2 * Real.pi / lam i) := by
  have h : ∀ φ : S → ℝ, Real.exp (-∑ i : S, lam i / 2 * φ i ^ 2)
      = ∏ i : S, Real.exp (-(lam i / 2) * φ i ^ 2) := by
    intro φ
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
  unfold gaussZ
  simp_rw [h]
  rw [volume_pi, integral_fintype_prod_eq_prod (fun (i : S) x => Real.exp (-(lam i / 2) * x ^ 2))]
  simp_rw [integral_gaussian]
  rw [Finset.prod_coe_sort S (fun i => √(Real.pi / (lam i / 2)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  rw [div_div_eq_mul_div]
  ring

/-- **`log Z` is a sum over modes.** DERIVED: `2π` the Gaussian integral. -/
theorem logZ_eq {lam : M → ℝ} {S : Finset M} (h : ∀ i ∈ S, 0 < lam i) :
    logZ lam S = ∑ i ∈ S, Real.log √(2 * Real.pi / lam i) := by
  rw [logZ, gaussZ_eq, Real.log_prod]
  intro i hi
  have := h i hi
  positivity

/-- **The Gaussian additivity**: a measure independent across modes has zero mode coupling. DERIVED: `0` the value. -/
theorem gaussian_additive {lam : M → ℝ} {S T : Finset M} (hd : Disjoint S T) (h : ∀ i ∈ S ∪ T, 0 < lam i) :
    modeCoupling (logZ lam) S T = 0 := by
  rw [modeCoupling, logZ_eq h, logZ_eq fun i hi => h i (Finset.mem_union_left _ hi),
    logZ_eq fun i hi => h i (Finset.mem_union_right _ hi), Finset.sum_union hd]
  ring

/-- **The doubling defect of a read with zero mode coupling is additive over modes**: `D(S ∪ T) = D(S) + D(T)` at each
side, with `PhotonStall.dbl` the doubling functional. DERIVED: `2` the doubling. -/
theorem dbl_additive (d L : ℕ) (Φ : ℕ → Finset M → ℝ) {S T : Finset M}
    (hL : modeCoupling (Φ L) S T = 0) (h2L : modeCoupling (Φ (2 * L)) S T = 0) :
    PhotonStall.dbl d (fun n => Φ n (S ∪ T)) L
      = PhotonStall.dbl d (fun n => Φ n S) L + PhotonStall.dbl d (fun n => Φ n T) L := by
  simp only [modeCoupling] at hL h2L
  simp only [PhotonStall.dbl]
  have e1 : Φ L (S ∪ T) = Φ L S + Φ L T := by linarith
  have e2 : Φ (2 * L) (S ∪ T) = Φ (2 * L) S + Φ (2 * L) T := by linarith
  rw [e1, e2]
  ring

end Gaussian

section Cumulant

variable {M : Type*} [Fintype M]

/-- **The Gaussian measure independent across modes**, variance `σ i` in mode `i`. DERIVED: `0` the mean. -/
def gaussM (σ : M → ℝ≥0) : Measure (M → ℝ) := Measure.pi fun i => gaussianReal 0 (σ i)

instance (σ : M → ℝ≥0) : IsProbabilityMeasure (gaussM σ) := by
  unfold gaussM
  infer_instance

/-- **The log moment generating function.** No numeral. -/
def logMGF (σ : M → ℝ≥0) (J : M → ℝ) : ℝ :=
  Real.log (∫ φ, Real.exp (∑ i, J i * φ i) ∂gaussM σ)

/-- **The generating function is quadratic in the source, a sum over modes.** DERIVED: `½` the Gaussian. -/
theorem logMGF_eq (σ : M → ℝ≥0) (J : M → ℝ) : logMGF σ J = ∑ i, (σ i : ℝ) * J i ^ 2 / 2 := by
  have h1 : ∀ i, ∫ x, Real.exp (J i * x) ∂gaussianReal 0 (σ i) = Real.exp ((σ i : ℝ) * J i ^ 2 / 2) := by
    intro i
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := σ i)) (J i)
    simpa [mgf] using this
  simp only [logMGF, gaussM, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (J i * x))]
  simp_rw [h1]
  rw [← Real.exp_sum, Real.log_exp]

/-- **The third connected term of a generating function**, its third mixed difference. It reads `0` on a quadratic. No
numeral beyond the difference. -/
def conn3 (Λ : (M → ℝ) → ℝ) (u v w : M → ℝ) : ℝ :=
  Λ (u + v + w) - Λ (u + v) - Λ (u + w) - Λ (v + w) + Λ u + Λ v + Λ w - Λ 0

/-- **The third-order connected term of the Gaussian is exactly `0`.** DERIVED: `0` the value. -/
theorem gaussian_connected3 (σ : M → ℝ≥0) (u v w : M → ℝ) : conn3 (logMGF σ) u v w = 0 := by
  have h : ∀ i, (σ i : ℝ) * (u i + v i + w i) ^ 2 / 2 - (σ i : ℝ) * (u i + v i) ^ 2 / 2
      - (σ i : ℝ) * (u i + w i) ^ 2 / 2 - (σ i : ℝ) * (v i + w i) ^ 2 / 2 + (σ i : ℝ) * u i ^ 2 / 2
      + (σ i : ℝ) * v i ^ 2 / 2 + (σ i : ℝ) * w i ^ 2 / 2 - (σ i : ℝ) * (0 : ℝ) ^ 2 / 2 = 0 := fun i => by ring
  have h2 := Finset.sum_eq_zero (s := Finset.univ) fun i _ => h i
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h2
  simpa only [conn3, logMGF_eq, Pi.add_apply, Pi.zero_apply] using h2

/-- **Sources on disjoint modes do not couple.** DERIVED: `0` the value. -/
theorem gaussian_source_coupling (σ : M → ℝ≥0) (u v : M → ℝ) (h : ∀ i, u i * v i = 0) :
    logMGF σ (u + v) = logMGF σ u + logMGF σ v := by
  simp only [logMGF_eq, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (σ i : ℝ) * h i

variable [DecidableEq M]

/-- The factor of mode `i` in the product of two monomials. No numeral. -/
def fac (s s' : Finset M) (i : M) (x : ℝ) : ℝ := (if i ∈ s then x else 1) * (if i ∈ s' then x else 1)

theorem prod_fac (s s' : Finset M) (φ : M → ℝ) :
    (∏ i ∈ s, φ i) * (∏ i ∈ s', φ i) = ∏ i, fac s s' i (φ i) := by
  have h : ∀ t : Finset M, ∏ i ∈ t, φ i = ∏ i, if i ∈ t then φ i else 1 := fun t => by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [h s, h s', ← Finset.prod_mul_distrib]
  rfl

/-- The second moment of a centred Gaussian. DERIVED: `2` the square. -/
theorem gauss_second (v : ℝ≥0) : ∫ x, x * x ∂gaussianReal 0 v = v := by
  have h := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 v) aemeasurable_id
    (by simpa using integral_id_gaussianReal (μ := 0) (v := v))
  rw [variance_id_gaussianReal] at h
  simpa [sq] using h.symm

theorem gauss_int_id (v : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal 1).integrable le_rfl

theorem gauss_int_sq (v : ℝ≥0) : Integrable (fun x : ℝ => x * x) (gaussianReal 0 v) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  simpa [sq] using this

theorem fac_integrable (s s' : Finset M) (i : M) (v : ℝ≥0) : Integrable (fac s s' i) (gaussianReal 0 v) := by
  by_cases h : i ∈ s <;> by_cases h' : i ∈ s'
  · have e : fac s s' i = fun x => x * x := funext fun x => by simp [fac, h, h']
    rw [e]
    exact gauss_int_sq v
  · have e : fac s s' i = fun x => x := funext fun x => by simp [fac, h, h']
    rw [e]
    exact gauss_int_id v
  · have e : fac s s' i = fun x => x := funext fun x => by simp [fac, h, h']
    rw [e]
    exact gauss_int_id v
  · have e : fac s s' i = fun _ => 1 := funext fun x => by simp [fac, h, h']
    rw [e]
    exact integrable_const _

theorem fac_integral (s s' : Finset M) (i : M) (v : ℝ≥0) :
    ∫ x, fac s s' i x ∂gaussianReal 0 v
      = if i ∈ s ∧ i ∈ s' then (v : ℝ) else if i ∈ s ∨ i ∈ s' then 0 else 1 := by
  have h0 : ∫ x, x ∂gaussianReal 0 v = 0 := integral_id_gaussianReal
  by_cases h : i ∈ s <;> by_cases h' : i ∈ s' <;> simp only [fac, h, h', if_true, if_false, one_mul, mul_one,
    true_and, and_true, or_true, true_or, or_false, false_or, false_and, and_false, not_true, not_false_eq_true]
  · exact gauss_second v
  · exact h0
  · exact h0
  · simp

/-- **The product of two monomials on sets of modes is integrable.** No numeral. -/
theorem moment_integrable (σ : M → ℝ≥0) (s s' : Finset M) :
    Integrable (fun φ : M → ℝ => (∏ i ∈ s, φ i) * (∏ i ∈ s', φ i)) (gaussM σ) := by
  simp_rw [prod_fac]
  exact Integrable.fintype_prod (fun i => fac_integrable s s' i (σ i))

/-- **Monomials on distinct sets of modes are orthogonal**: `∫ φ_s φ_{s'} dγ = δ_{s s'} Π_{i ∈ s} σᵢ`. The independence
of the modes in one line. No numeral. -/
theorem moment_pair (σ : M → ℝ≥0) (s s' : Finset M) :
    ∫ φ, (∏ i ∈ s, φ i) * (∏ i ∈ s', φ i) ∂gaussM σ = if s = s' then ∏ i ∈ s, (σ i : ℝ) else 0 := by
  simp_rw [prod_fac]
  rw [gaussM, integral_fintype_prod_eq_prod (fac s s')]
  simp_rw [fac_integral]
  split_ifs with h
  · subst h
    have : ∀ i, (if i ∈ s ∧ i ∈ s then (σ i : ℝ) else if i ∈ s ∨ i ∈ s then 0 else 1)
        = if i ∈ s then (σ i : ℝ) else 1 := fun i => by by_cases hi : i ∈ s <;> simp [hi]
    simp_rw [this]
    simp [Finset.prod_ite_mem]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ s ↔ i ∈ s') := by
      by_contra hc
      push Not at hc
      exact h (Finset.ext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases h1 : i ∈ s <;> by_cases h2 : i ∈ s' <;> simp_all

/-- **The cubic form of the model.** CHOSEN: `𝒯` the sets of distinct modes carrying a vertex, `v` its coefficients. No
numeral. -/
def cubicForm (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) (φ : M → ℝ) : ℝ := ∑ s ∈ 𝒯, v s * ∏ i ∈ s, φ i

/-- **The first-order term of the Gaussian-plus-cubic model is `0`.** DERIVED: `0` the value. -/
theorem cubicForm_mean (σ : M → ℝ≥0) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) (h0 : ∅ ∉ 𝒯) :
    ∫ φ, cubicForm 𝒯 v φ ∂gaussM σ = 0 := by
  have hi : ∀ s ∈ 𝒯, Integrable (fun φ : M → ℝ => v s * ∏ i ∈ s, φ i) (gaussM σ) := fun s _ => by
    have := (moment_integrable σ s ∅).const_mul (v s)
    simpa using this
  simp only [cubicForm]
  rw [integral_finsetSum _ hi]
  refine Finset.sum_eq_zero fun s hs => ?_
  have h := moment_pair σ s ∅
  simp only [Finset.prod_empty, mul_one] at h
  rw [integral_const_mul, h, if_neg (fun e : s = ∅ => h0 (e ▸ hs)), mul_zero]

/-- **The second moment of the cubic form is the vertex squared over the propagators.** DERIVED: `2` the square. -/
theorem cubicForm_second (σ : M → ℝ≥0) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) :
    ∫ φ, cubicForm 𝒯 v φ ^ 2 ∂gaussM σ = ∑ s ∈ 𝒯, v s ^ 2 * ∏ i ∈ s, (σ i : ℝ) := by
  have hpt : ∀ φ : M → ℝ, cubicForm 𝒯 v φ ^ 2
      = ∑ s ∈ 𝒯, ∑ s' ∈ 𝒯, v s * v s' * ((∏ i ∈ s, φ i) * (∏ i ∈ s', φ i)) := by
    intro φ
    rw [sq, cubicForm, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  simp_rw [hpt]
  have hi : ∀ s s', Integrable (fun φ : M → ℝ => v s * v s' * ((∏ i ∈ s, φ i) * (∏ i ∈ s', φ i))) (gaussM σ) :=
    fun s s' => (moment_integrable σ s s').const_mul _
  rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun s' _ => hi s s']
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [integral_finsetSum _ fun s' _ => hi s s']
  simp_rw [integral_const_mul, moment_pair]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [hs, if_true]
  ring

/-- **The second cumulant of the cubic form on the modes in `S`.** No numeral beyond the square. -/
def cum2W (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) (σ : M → ℝ≥0) (S : Finset M) : ℝ :=
  ∑ s ∈ 𝒯.filter (· ⊆ S), v s ^ 2 * ∏ i ∈ s, (σ i : ℝ)

/-- **`cum2W` is the variance of the cubic form restricted to the modes in `S`.** DERIVED: `2` the square. -/
theorem cum2W_eq_variance (σ : M → ℝ≥0) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) (S : Finset M)
    (h0 : ∅ ∉ 𝒯) :
    cum2W 𝒯 v σ S = ∫ φ, cubicForm (𝒯.filter (· ⊆ S)) v φ ^ 2 ∂gaussM σ
      - (∫ φ, cubicForm (𝒯.filter (· ⊆ S)) v φ ∂gaussM σ) ^ 2 := by
  have h0' : ∅ ∉ 𝒯.filter (· ⊆ S) := fun h => h0 (Finset.mem_filter.mp h).1
  rw [cubicForm_second, cubicForm_mean σ _ v h0', cum2W]
  ring

/-- **The additivity defect of the second cumulant is the sum over vertices straddling `S` and `T`.** DERIVED: `0` the
empty vertex excluded. -/
theorem cum2W_coupling (σ : M → ℝ≥0) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) {S T : Finset M}
    (hd : Disjoint S T) (h0 : ∅ ∉ 𝒯) :
    modeCoupling (cum2W 𝒯 v σ) S T
      = ∑ s ∈ 𝒯.filter (fun s => s ⊆ S ∪ T ∧ ¬ s ⊆ S ∧ ¬ s ⊆ T), v s ^ 2 * ∏ i ∈ s, (σ i : ℝ) := by
  simp only [modeCoupling, cum2W, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun e => h0 (e ▸ hs)
  by_cases hS : s ⊆ S
  · have hT : ¬ s ⊆ T := fun hT => by
      obtain ⟨i, hi⟩ := hne
      exact Finset.disjoint_left.mp hd (hS hi) (hT hi)
    simp [hS, hT, hS.trans Finset.subset_union_left]
  · by_cases hT : s ⊆ T
    · simp [hS, hT, hT.trans Finset.subset_union_right]
    · simp [hS, hT]

/-- **The additivity defect of the second cumulant is non-negative.** DERIVED: `0` the bound. -/
theorem cum2W_coupling_nonneg (σ : M → ℝ≥0) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) {S T : Finset M}
    (hd : Disjoint S T) (h0 : ∅ ∉ 𝒯) : 0 ≤ modeCoupling (cum2W 𝒯 v σ) S T := by
  rw [cum2W_coupling σ 𝒯 v hd h0]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ => (σ i).2)

/-- **At zero vertex the second cumulant is `0`.** DERIVED: `0` the value. -/
theorem cum2W_zero (σ : M → ℝ≥0) (𝒯 : Finset (Finset M)) (S : Finset M) : cum2W 𝒯 (fun _ => 0) σ S = 0 := by
  simp [cum2W]

/-- **The Gaussian-plus-cubic `log Z` through second order in the coupling `g`.** CHOSEN: the model of this section, a
formal expansion. DERIVED: `½` the second cumulant's coefficient in `log Z`. -/
def secondOrderLogZ (σ : M → ℝ≥0) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) (g : ℝ) (S : Finset M) : ℝ :=
  logZ (fun i => (σ i : ℝ)⁻¹) S + g ^ 2 / 2 * cum2W 𝒯 v σ S

/-- **The first non-zero mode coupling of the model is `g²/2` times the sum over straddling vertices.** DERIVED: `½`
as in `secondOrderLogZ`. -/
theorem secondOrder_coupling (σ : M → ℝ≥0) (hσ : ∀ i, 0 < σ i) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ) (g : ℝ)
    {S T : Finset M} (hd : Disjoint S T) (h0 : ∅ ∉ 𝒯) :
    modeCoupling (secondOrderLogZ σ 𝒯 v g) S T
      = g ^ 2 / 2 * ∑ s ∈ 𝒯.filter (fun s => s ⊆ S ∪ T ∧ ¬ s ⊆ S ∧ ¬ s ⊆ T), v s ^ 2 * ∏ i ∈ s, (σ i : ℝ) := by
  have h1 := gaussian_additive (lam := fun i => (σ i : ℝ)⁻¹) hd (fun i _ => inv_pos.mpr (hσ i))
  have h2 := cum2W_coupling σ 𝒯 v hd h0
  simp only [modeCoupling] at h1 h2 ⊢
  simp only [secondOrderLogZ]
  rw [← h2]
  linear_combination h1

/-- **The first non-zero mode coupling of the model is non-negative**: `log Z` is superadditive over modes at this
order. DERIVED: `0` the bound. -/
theorem secondOrder_coupling_nonneg (σ : M → ℝ≥0) (hσ : ∀ i, 0 < σ i) (𝒯 : Finset (Finset M)) (v : Finset M → ℝ)
    (g : ℝ) {S T : Finset M} (hd : Disjoint S T) (h0 : ∅ ∉ 𝒯) :
    0 ≤ modeCoupling (secondOrderLogZ σ 𝒯 v g) S T := by
  rw [secondOrder_coupling σ hσ 𝒯 v g hd h0]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun s _ => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ => (σ i).2))

end Cumulant

/-! ## 4. The single-plaquette third moment -/

section Haar

open MassGap.CompactGauge MassGap.SUN

/-- **The odd moments of `Re tr U` vanish on `SU(2)`**, from the centre element `−1`. DERIVED: `0` the value. -/
theorem haar_odd_su2 {n : ℕ} (hn : Odd n) :
    ∫ U : SU 2, (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re ^ n ∂(probHaar (SU 2)) = 0 := by
  set f : SU 2 → ℝ := fun U => (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re ^ n with hf
  have hneg : ∀ U : SU 2, f (TwistedTraceBound.negOne * U) = -f U := by
    intro U
    simp only [hf, Submonoid.coe_mul, TwistedTraceBound.coe_negOne, neg_mul, one_mul, Matrix.trace_neg,
      Complex.neg_re, hn.neg_pow]
  have h := integral_mul_left_eq_self (μ := probHaar (SU 2)) f TwistedTraceBound.negOne
  simp only [hneg, integral_neg] at h
  linarith

/-- **`∫ (Re tr U)³ dHaar = 0` on `SU(2)`.** DERIVED: `3` the order of the vertex. -/
theorem haar_cube_su2 :
    ∫ U : SU 2, (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re ^ 3 ∂(probHaar (SU 2)) = 0 :=
  haar_odd_su2 (by decide)

variable [MeasurableSpace Circle] [BorelSpace Circle]

/-- **The odd moments of `Re z` vanish on `U(1)`**, from the element `−1`. DERIVED: `0` the value. -/
theorem haar_odd_u1 {n : ℕ} (hn : Odd n) : ∫ z : Circle, ((z : ℂ).re) ^ n ∂(probHaar Circle) = 0 := by
  set f : Circle → ℝ := fun z => ((z : ℂ).re) ^ n with hf
  have hm : ((Circle.exp Real.pi : Circle) : ℂ) = -1 := by
    rw [Circle.coe_exp]
    push_cast
    exact Complex.exp_pi_mul_I
  have hneg : ∀ z : Circle, f (Circle.exp Real.pi * z) = -f z := by
    intro z
    simp only [hf, Circle.coe_mul, hm, neg_mul, one_mul, Complex.neg_re, hn.neg_pow]
  have h := integral_mul_left_eq_self (μ := probHaar Circle) f (Circle.exp Real.pi)
  simp only [hneg, integral_neg] at h
  linarith

/-- **`∫ (Re z)³ dHaar = 0` on `U(1)`.** DERIVED: `3` the order of the vertex. -/
theorem haar_cube_u1 : ∫ z : Circle, ((z : ℂ).re) ^ 3 ∂(probHaar Circle) = 0 :=
  haar_odd_u1 (by decide)

omit [MeasurableSpace Circle] [BorelSpace Circle]

/-- **The Haar mean of the `SU(2)` density is `1`**, from the centre. DERIVED: `1` the normalization. -/
theorem haarMean_two : WindowRead.haarMeanN 2 = 1 := by
  have h := haar_odd_su2 (n := 1) (by decide)
  simp only [pow_one] at h
  have hc : Integrable (fun U : SU 2 => (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re) (probHaar (SU 2)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact Complex.continuous_re.comp (Continuous.matrix_trace continuous_subtype_val)
  simp only [WindowRead.haarMeanN, WilsonAction.wilsonDensity]
  rw [integral_sub (integrable_const _) (hc.const_mul _), integral_const_mul, h]
  simp

/-- **The Haar third central moment of the `SU(2)` plaquette density is `0`.** DERIVED: `⅛ = (1/N)³` at `N = 2`. -/
theorem haarCum3_two : MixExpand.haarCum3 2 = 0 := by
  have h := haar_cube_su2
  simp only [MixExpand.haarCum3, haarMean_two, WilsonAction.wilsonDensity]
  have e : ∀ U : SU 2, (1 - (1 / ((2 : ℕ) : ℝ)) * (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re - 1) ^ 3
      = -(1 / 8) * (Matrix.trace (U : Matrix (Fin 2) (Fin 2) ℂ)).re ^ 3 := fun U => by
    push_cast
    ring
  simp_rw [e]
  rw [integral_const_mul, h, mul_zero]

/-- A primitive cube root of unity. DERIVED: `3` the order of the centre of `SU(3)`. -/
def omega3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))

theorem omega3_prim : IsPrimitiveRoot omega3 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem omega3_norm : ‖omega3‖ = 1 :=
  omega3_prim.norm'_eq_one (by norm_num)

theorem omega3_mul_star : omega3 * star omega3 = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, omega3_norm]
  simp

/-- The centre element `ω · 1` of `SU(3)`. DERIVED: `3` the matrix size. -/
def cen3 : SU 3 :=
  ⟨omega3 • (1 : Matrix (Fin 3) (Fin 3) ℂ), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, Matrix.one_mul, omega3_mul_star,
        one_smul]
    · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, omega3_prim.pow_eq_one]⟩

/-- **Triality**: `∫ χ² χ̄ dHaar = 0` on `SU(3)`. DERIVED: `0` from `ω ≠ 1`; `3` the matrix size of
`SU(3)`. -/
theorem haar_triality :
    ∫ U : SU 3, (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 2 *
        star (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ∂(probHaar (SU 3)) = 0 := by
  set f : SU 3 → ℂ := fun U => (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 2 *
    star (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) with hf
  have hrot : ∀ U : SU 3, f (cen3 * U) = omega3 * f U := by
    intro U
    have ht : Matrix.trace ((cen3 * U : SU 3) : Matrix (Fin 3) (Fin 3) ℂ)
        = omega3 * Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ) := by
      simp [cen3, Matrix.trace_smul, Matrix.smul_mul]
    simp only [hf, ht, star_mul', sq]
    linear_combination (omega3 * (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 2
      * star (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ))) * omega3_mul_star
  have h := integral_mul_left_eq_self (μ := probHaar (SU 3)) f cen3
  simp only [hrot, integral_const_mul] at h
  have hne : omega3 - 1 ≠ 0 := sub_ne_zero.mpr (omega3_prim.ne_one (by norm_num))
  have h0 : (omega3 - 1) * ∫ U, f U ∂(probHaar (SU 3)) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left hne

/-- **The `SU(3)` third moment is a quarter of the singlet read**: `∫ (Re tr U)³ dHaar = ¼ Re ∫ (tr U)³ dHaar`.
Cited: `∫ (tr U)³ dHaar = 1`, the singlet of `3 ⊗ 3 ⊗ 3`, which gives `1/4`. DERIVED: `¼` and `¾` the binomial
coefficients of `((z + z̄)/2)³`; `3` the matrix size of `SU(3)` and the power. -/
theorem haar_cube_su3 :
    ∫ U : SU 3, (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)).re ^ 3 ∂(probHaar (SU 3))
      = (1 / 4) * (∫ U : SU 3, (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 3 ∂(probHaar (SU 3))).re := by
  have hc : Continuous fun U : SU 3 => Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ) :=
    Continuous.matrix_trace continuous_subtype_val
  have hi1 : Integrable (fun U : SU 3 => (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 3) (probHaar (SU 3)) :=
    (hc.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun U : SU 3 => (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 2 *
      star (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ))) (probHaar (SU 3)) :=
    ((hc.pow 2).mul (continuous_star.comp hc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp : ∀ z : ℂ, z.re ^ 3 = (1 / 4) * (z ^ 3).re + (3 / 4) * (z ^ 2 * star z).re := by
    intro z
    simp only [Complex.star_def, pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  simp_rw [hp]
  have hr : ∀ {f : SU 3 → ℂ}, Integrable f (probHaar (SU 3)) →
      ∫ U, (f U).re ∂(probHaar (SU 3)) = (∫ U, f U ∂(probHaar (SU 3))).re :=
    fun hf => integral_re hf
  have hi1' : Integrable (fun U : SU 3 => ((Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 3).re)
      (probHaar (SU 3)) := hi1.re
  have hi2' : Integrable (fun U : SU 3 => ((Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ)) ^ 2 *
      star (Matrix.trace (U : Matrix (Fin 3) (Fin 3) ℂ))).re) (probHaar (SU 3)) := hi2.re
  rw [integral_add (hi1'.const_mul _) (hi2'.const_mul _), integral_const_mul, integral_const_mul, hr hi1, hr hi2,
    haar_triality]
  simp

end Haar

/-! ## The witness -/

section Witness

open Matrix

/-- `e(1/2) = −1`. DERIVED: `2` the extent. -/
theorem stdAddChar_two : (ZMod.stdAddChar (1 : ZMod 2)) = -1 := by
  have h := ZMod.stdAddChar_coe (N := 2) 1
  simp only [Int.cast_one] at h
  rw [h]
  have : (2 * (Real.pi : ℂ) * Complex.I * 1 / ((2 : ℕ) : ℂ)) = Real.pi * Complex.I := by
    push_cast
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- CHOSEN: the momenta `(1,0)`, `(0,1)`, `(1,1)` on `(ℤ/2)²`. They are non-zero and sum to `0`. DERIVED: `2` the least
extent with real plane waves; `3` the three legs of the vertex. -/
def wk : Fin 3 → Torus 2 2 := ![![1, 0], ![0, 1], ![1, 1]]

/-- CHOSEN: the polarizations `(e₁, 0)`, `(0, e₂)`, `(e₃, 0)`. DERIVED: `3` the three legs of the vertex;
`2` the extent and the matrix size of `su(2)`. -/
def wX : Fin 3 → Fin 2 → Mat 2 := ![![e₁, 0], ![0, e₂], ![e₃, 0]]

/-- The momenta of the witness sum to `0` on the torus. DERIVED: `2` the extent. -/
theorem wk_sum : wk 0 + wk 1 + wk 2 = 0 := by
  ext i
  fin_cases i <;> simp [wk] <;> decide

/-- **The witness**: the symmetrized form factor of the chosen modes is `−2`, so the vertex couples distinct modes.
CHOSEN: `wk`, `wX`. DERIVED: `−2` the value of the six orderings, by `su2_vertex`. -/
theorem formFactor_witness :
    symV (Matrix.traceLinearMap (Fin 2) ℂ ℂ) (modeT 0 1 (wk 0) (wX 0)) (modeT 0 1 (wk 1) (wX 1))
      (modeT 0 1 (wk 2) (wX 2)) = -2 := by
  have p00 : wave (wk 0) (ehat 0) = -1 := by simp [wave_ehat, wk, stdAddChar_two]
  have p01 : wave (wk 0) (ehat 1) = 1 := by simp [wave_ehat, wk]
  have p10 : wave (wk 1) (ehat 0) = 1 := by simp [wave_ehat, wk]
  have p11 : wave (wk 1) (ehat 1) = -1 := by simp [wave_ehat, wk, stdAddChar_two]
  have p20 : wave (wk 2) (ehat 0) = -1 := by simp [wave_ehat, wk, stdAddChar_two]
  have p21 : wave (wk 2) (ehat 1) = -1 := by simp [wave_ehat, wk, stdAddChar_two]
  simp only [symV, triV, curl, pairs, modeT, p00, p01, p10, p11, p20, p21, wX]
  simp [e₁, e₂, e₃, su2X, Matrix.trace_fin_two, Matrix.mul_fin_two, Matrix.smul_of]
  ring_nf
  simp only [Complex.I_sq, show Complex.I ^ 3 = -Complex.I from by rw [pow_succ, Complex.I_sq]; ring]
  norm_num

/-- **The torus sum couples the chosen modes**: at the witness data, with `S = {0, 1}` and `T = {2}`, the additivity
defect of `sunset` is positive. CHOSEN: `wk`, `wX`, unit propagators. DERIVED: `0` the bound. -/
theorem sunset_coupling_witness :
    0 < modeCoupling (sunset (Matrix.traceLinearMap (Fin 2) ℂ ℂ) wk wX (fun _ => (1 : ℝ))) {0, 1} {2} := by
  have hd : Disjoint ({0, 1} : Finset (Fin 3)) {2} := by decide
  rw [sunset_coupling _ _ _ _ hd]
  have hmem : ((0, 1, 2) : Fin 3 × Fin 3 × Fin 3) ∈ straddle ({0, 1} : Finset (Fin 3)) {2} := by decide
  refine Finset.sum_pos' (fun p hp => ?_) ⟨_, hmem, ?_⟩
  · exact sunsetWt_nonneg _ _ _ one_pos one_pos one_pos
  · have hv : vertexG (Matrix.traceLinearMap (Fin 2) ℂ ℂ) wk wX (0, 1, 2) = -2 := by
      have hpl : planes 2 = {(0, 1)} := by decide
      simp only [vertexG, hpl, Finset.sum_singleton]
      exact formFactor_witness
    have hk : wk 0 + wk 1 + wk 2 = 0 := wk_sum
    simp only [sunsetWt, hk, if_true, hv]
    norm_num

end Witness

end MassGap.HarmonicVertex

#print axioms MassGap.HarmonicVertex.poly_mul
#print axioms MassGap.HarmonicVertex.Jet3.mul
#print axioms MassGap.HarmonicVertex.exp_jet
#print axioms MassGap.HarmonicVertex.exp_sub_quad
#print axioms MassGap.HarmonicVertex.P2_eq
#print axioms MassGap.HarmonicVertex.tau_P2
#print axioms MassGap.HarmonicVertex.tau_P3
#print axioms MassGap.HarmonicVertex.holo_jet
#print axioms MassGap.HarmonicVertex.bch_second
#print axioms MassGap.HarmonicVertex.Jet3.map
#print axioms MassGap.HarmonicVertex.wilsonDensity_eq_wil
#print axioms MassGap.HarmonicVertex.wilson_expansion
#print axioms MassGap.HarmonicVertex.re_trace_cube_of_skew
#print axioms MassGap.HarmonicVertex.cubic_eq_commutator
#print axioms MassGap.HarmonicVertex.wilson_su_expansion
#print axioms MassGap.HarmonicVertex.cubic_comm
#print axioms MassGap.HarmonicVertex.su2_vertex
#print axioms MassGap.HarmonicVertex.cubic_su2
#print axioms MassGap.HarmonicVertex.cubic_su2_ne
#print axioms MassGap.HarmonicVertex.sum_wave
#print axioms MassGap.HarmonicVertex.sum_wave_three
#print axioms MassGap.HarmonicVertex.triV_diag
#print axioms MassGap.HarmonicVertex.momentum_selection
#print axioms MassGap.HarmonicVertex.momentum_difference
#print axioms MassGap.HarmonicVertex.momentum_double
#print axioms MassGap.HarmonicVertex.vertex_modes
#print axioms MassGap.HarmonicVertex.formFactor_comm
#print axioms MassGap.HarmonicVertex.vertex_modes_comm
#print axioms MassGap.HarmonicVertex.symV_of_commute
#print axioms MassGap.HarmonicVertex.sunset_nonneg
#print axioms MassGap.HarmonicVertex.sunset_comm
#print axioms MassGap.HarmonicVertex.triple_coupling
#print axioms MassGap.HarmonicVertex.sunset_coupling
#print axioms MassGap.HarmonicVertex.sunset_coupling_nonneg
#print axioms MassGap.HarmonicVertex.gaussZ_eq
#print axioms MassGap.HarmonicVertex.logZ_eq
#print axioms MassGap.HarmonicVertex.gaussian_additive
#print axioms MassGap.HarmonicVertex.dbl_additive
#print axioms MassGap.HarmonicVertex.logMGF_eq
#print axioms MassGap.HarmonicVertex.gaussian_connected3
#print axioms MassGap.HarmonicVertex.gaussian_source_coupling
#print axioms MassGap.HarmonicVertex.moment_pair
#print axioms MassGap.HarmonicVertex.cubicForm_mean
#print axioms MassGap.HarmonicVertex.cubicForm_second
#print axioms MassGap.HarmonicVertex.cum2W_eq_variance
#print axioms MassGap.HarmonicVertex.cum2W_coupling
#print axioms MassGap.HarmonicVertex.cum2W_coupling_nonneg
#print axioms MassGap.HarmonicVertex.cum2W_zero
#print axioms MassGap.HarmonicVertex.secondOrder_coupling
#print axioms MassGap.HarmonicVertex.secondOrder_coupling_nonneg
#print axioms MassGap.HarmonicVertex.haar_odd_su2
#print axioms MassGap.HarmonicVertex.haar_cube_su2
#print axioms MassGap.HarmonicVertex.haar_odd_u1
#print axioms MassGap.HarmonicVertex.haar_cube_u1
#print axioms MassGap.HarmonicVertex.haarMean_two
#print axioms MassGap.HarmonicVertex.haarCum3_two
#print axioms MassGap.HarmonicVertex.haar_triality
#print axioms MassGap.HarmonicVertex.haar_cube_su3
#print axioms MassGap.HarmonicVertex.formFactor_witness
#print axioms MassGap.HarmonicVertex.sunset_coupling_witness
#print axioms MassGap.HarmonicVertex.bigO_one_of_continuous
#print axioms MassGap.HarmonicVertex.tau_rot
#print axioms MassGap.HarmonicVertex.tau_br
#print axioms MassGap.HarmonicVertex.tau_comK
#print axioms MassGap.HarmonicVertex.reTr_apply
#print axioms MassGap.HarmonicVertex.reTr_comm
#print axioms MassGap.HarmonicVertex.curlF_skew
#print axioms MassGap.HarmonicVertex.br_of_commute
#print axioms MassGap.HarmonicVertex.su2X_skew
#print axioms MassGap.HarmonicVertex.su2X_trace
#print axioms MassGap.HarmonicVertex.curlF_triple
#print axioms MassGap.HarmonicVertex.wave_add_left
#print axioms MassGap.HarmonicVertex.wave_add_right
#print axioms MassGap.HarmonicVertex.wave_zero_left
#print axioms MassGap.HarmonicVertex.wave_ehat
#print axioms MassGap.HarmonicVertex.curl_smul
#print axioms MassGap.HarmonicVertex.pairs_smul
#print axioms MassGap.HarmonicVertex.triV_smul
#print axioms MassGap.HarmonicVertex.curl_sum
#print axioms MassGap.HarmonicVertex.pairs_sum_left
#print axioms MassGap.HarmonicVertex.pairs_sum_right
#print axioms MassGap.HarmonicVertex.triV_sum
#print axioms MassGap.HarmonicVertex.plaqT_waveF
#print axioms MassGap.HarmonicVertex.plaqT_sum
#print axioms MassGap.HarmonicVertex.triV_of_commute
#print axioms MassGap.HarmonicVertex.modeT_entry
#print axioms MassGap.HarmonicVertex.modeT_commute
#print axioms MassGap.HarmonicVertex.sunsetWt_nonneg
#print axioms MassGap.HarmonicVertex.prod_fac
#print axioms MassGap.HarmonicVertex.gauss_second
#print axioms MassGap.HarmonicVertex.gauss_int_id
#print axioms MassGap.HarmonicVertex.gauss_int_sq
#print axioms MassGap.HarmonicVertex.fac_integrable
#print axioms MassGap.HarmonicVertex.fac_integral
#print axioms MassGap.HarmonicVertex.moment_integrable
#print axioms MassGap.HarmonicVertex.omega3_prim
#print axioms MassGap.HarmonicVertex.omega3_norm
#print axioms MassGap.HarmonicVertex.omega3_mul_star
#print axioms MassGap.HarmonicVertex.stdAddChar_two
#print axioms MassGap.HarmonicVertex.wk_sum
