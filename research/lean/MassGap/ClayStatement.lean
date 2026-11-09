import Mathlib
import MassGap.ObserverNontrivial

/-!
# MassGap.ClayStatement — the target statement of the Clay Yang–Mills problem at `SU(N)`

Jaffe–Witten: for a compact simple gauge group `G`, a quantum Yang–Mills theory on `ℝ⁴` exists,
satisfying axiomatic properties at least as strong as the Wightman or the Osterwalder–Schrader
axioms, and it has a mass gap `Δ > 0`. `ClayStatement` is that statement for `G = SU(N)`, `N ≥ 2`,
in the Osterwalder–Schrader form, for every gauge-invariant local composite field, with the
theory built from the Wilson lattice measure and read through the flowed observer.

## The construction the statement is about

* **The lattice measure.** At step `k` the periodic infinite-volume Wilson state `stateK hN k` of
  `SU(N)` at the coupling `dyBeta k`, at spacing `dySpacing N k = aRun N (dyBeta k)`, the two-loop
  running spacing: the frozen tower. `ClayStatementDy` is the statement at the frozen tower. The
  root `MassGap.ClayStatement` (`ClayStatementG`) selects the coupling of each step by a measured
  tower (`MeasuredTower.MeasTowerG`), with the same spacing, clauses and constants.
* **The aperture.** The flowed observer `X : OSDataSLinked N D τ r`, read through a configuration
  flow `W` on a field class `D`: its Schwinger functional is the Wilson states' `schwSFM`, and its
  time semigroup has the Hamiltonian gap (`HamiltonianGap`) on all of `X.base.H`. The Hilbert
  space is the observer's own reconstruction: the closed span of vectors of the compact margin
  monomials of every local field, whose Gram matrix is the observer's flowed Schwinger functions of
  the reflected pairs, which are the observer's compact vectors on `D`, and on which the time
  translations act as the observer's time shifts (`ObsGen`). Every local field below is embedded in this one Hilbert space.
* **Classical configurations.** A smooth gauge potential `A` with Hermitian traceless values
  (`GPot.Adm`) and a coupling `g` give the lattice configuration `U_μ(x) = exp(i a g A_μ(a x))` at
  spacing `a` (`IsClassCfg`). Its field strength is `F_{ρσ} = ∂_ρA_σ − ∂_σA_ρ + i g [A_ρ, A_σ]` and
  its covariant derivative `D_μ X = ∂_μ X + i g [A_μ, X]` (`covDF`). A lattice field `L` has
  classical leading term `P` at dimension `d` (`ClassicalLead`) if
  `(L(U) − L(1))/a^d → P(A, g)` as `a → 0⁺` for every such `A`, `g`: this ties a lattice field to
  the classical expression it discretises, and excludes any field whose `a^d` coefficient differs.
  A field of higher dimension has `a^d` coefficient `0`: it cannot be the whole field, and with a
  step-independent discretisation it enters only with a fixed coefficient, where it is `O(a)`
  relative and vanishes in the limit.
* **The composites.** A classical gauge-invariant local composite is a real polynomial in the
  components of `D_{μ₁} ⋯ D_{μⱼ} F_{ρσ}` at a point, invariant under conjugation; these are spanned by
  the monomials `∏ᵢ Re/Im tr(Wᵢ)`, `Wᵢ` a word in the letters `D⋯DF` (`CMono`, `cval`), of
  dimension `∑ (2 + #derivatives)` (`cdim`). The real parts include the `C`-even fields, the
  imaginary parts the `C`-odd ones (`d^{abc} F^a F^b F^c` among them). A `Composites` family
  carries, for an index type `Ix`: the classical monomial `cl i`, a bare lattice field `bare i`
  tied to `g^{#F} cl i` at dimension `cdim (cl i)` (`Tied`), the renormalised lattice field
  `ren k i` of step `k`, and the rotation representation `rep A i`. Every non-degenerate classical
  monomial is some `cl i` (`Covers`), at every dimension. The renormalisation is triangular in the
  dimension and invertible at every level (`RenTri`): `ren k i` is a combination of `1` and the bare
  fields of dimension `≤ cdim (cl i)`, and the bare fields of dimension `≤ d` are combinations of
  `1` and the renormalised ones of dimension `≤ d`.
* **The dimension-four tensor.** Inside the composites, the rank-four tensor `T_{μνρσ}`, the field
  `tr F_{μν} F_{ρσ}`, with its lattice mixing (`RenormMix`): a finite basis `op b` of local
  gauge-invariant lattice fields and, at each step, a matrix `M k α b` from the components `α` of
  `T` to the basis. The mixing factors as `M k = Z k · Mb` (`ChannelTie`): a fixed bare
  discretisation `B_β = ∑_b Mb β b op b` whose classical leading term is `g² Re tr F_{β₀β₁}F_{β₂β₃}`
  (`ffT`), renormalised by a matrix `Z k` commuting with the hypercubic group (`IsHyp`), so each
  hypercubic sub-channel renormalises with its own factor. A field of the sector is a coefficient
  tensor `c : Idx4 → ℝ`, the field `∑_α c_α T_α`; its lattice reading is the multilinear expansion
  `latT` over the basis, each basis field entering connected, `op b − ν_k(op b)`.

## The clauses (`ClayData`)

Every clause on local fields is stated on admissible families: continuous test functions with
pairwise `d`-separated supports for some `d > 0` (`Adm`). Coincident points, where composites have
non-integrable singularities and contact terms, are never asked about. On each such family the
lattice sequence is asserted to converge along `ultra` (`SepConv`, `ConvC`), so no clause reads
the value `limUnder` assigns to a divergent sequence.

1. **Lattice Yang–Mills, through the aperture.** `X.SM = schwSFM`, `HamiltonianGap X.base`.
2. **The tensor.** Riemann-type symmetries of the mixing (`RenormMix.Riemann`), and the scalar tie
   (`ScalarTie`): the trace `∑_{μ,ν} T_{μνμν}` (`trC`) is at every step `Ztr k` times the
   observer's field `X.O = sym (plaqField q0)`, with `Ztr k · a_k⁴ → N/8`, the bare normalisation
   of `g₀² F^a_{μν} F^a_{μν}` (`= 2 g₀² tr F²` at `tr(TᵃTᵇ) = δᵃᵇ/2`).
3. **Existence of the limit** on admissible families of the tensor (`SepConv`).
4. **OS0, the kernel bound** (`OS0Sep`): one `α, γ, β, κ` with
   `|S(F)| ≤ α γⁿ (n!)^β d^{−κn} ∏ᵢ ‖cᵢ‖₁ ‖fᵢ‖_{L¹}` on `d`-separated families of continuous test
   functions, `0 < d ≤ 1`. `κ` is free: the Weyl channel has anomalous dimension
   `γ_W = +7g²N/(24π²)` and kernel `∼ r⁻⁸ (log 1/r)^{14/11}`, so no fixed power `d⁻⁴ⁿ` holds.
5. **OS1** (`OS1Sep`), every real translation.
6. **O(4) covariance** (`TensorCov`): `S((cᵢ, fᵢ ∘ A)) = S((A·cᵢ, fᵢ))`,
   `(A·c)_β = ∑_α c_α ∏ⱼ A_{βⱼαⱼ}`.
7. **OS3** (`OS3T`), as an identity of the lattice readings.
8. **The link of the tensor** (`LinkTS`): vectors `w P ∈ X.base.H` of the separated positive-time
   monomials with `⟪w P, w Q⟫ = S(ΘP ∪ Q)` (`Θ` reflects the test functions and multiplies a
   component by `(−1)^{#τ}`), the lattice sequence of `ΘP ∪ Q` converging, the dyadic shift acting
   as `X.base.time`, `w ∅ = X.base.vac`, and the cross inner product `⟪w P, X.cvec Q⟫` the
   convergent mixed reading against the observer's compact vectors.
9. **OS2** at margin `0` (`OS2T`).
10. **The spectrum on the tensor's space** (`SpectralGapOn`, `HL = HLs X w`).
11. **OS4** (`OS4T`): clustering.
12. **A non-zero vector** of `HL` orthogonal to the vacuum.
13. **Asymptotic freedom** of the trace: two-point kernel `G` (`TwoPointKernel`) with
    `r⁸ G(r) (log r)² → 12(N² − 1)/(π⁴ b₀²)`, `b₀ = 11N/(48π²)` (`AFCoefficient`), hence
    `AFShortDistance G`.
14. **Non-Gaussian**: a non-zero connected three-point function of the trace (`NonGaussianT`).
15. **Every channel non-degenerate** (`TensorNondeg`).
16. **The aperture's functional is a limit** (`ApertureConv`).
17. **Channel ties** (`ChannelTie`, `TopNorm`): `M k = Z k · Mb`, `Z k` hypercubic-equivariant,
    `B_β` with classical leading term `g² Re tr F_{β₀β₁}F_{β₂β₃}` at dimension `4`, `Mb`
    independent of the step. A field such as `(∂_μ∂_ν − δ_{μν}□/4)(g²F²)`, of dimension `6`, has
    `a⁴` coefficient `0`: it cannot be a channel, and inside `B` it carries a fixed coefficient,
    `O(a²)` relative, so no step-dependent coefficient can bring it into the limit. The pseudoscalar channel `zAct (Z k) ε = zq k ε` has `zq k · a_k⁴ → 2`: the field
    `q = (1/(64π²)) ∑ ε_{μνρσ} T_{μνρσ} = (g²/(32π²)) F^a F̃^a` carries the normalisation whose
    integral over a classical configuration is the integer instanton number, and its finite
    renormalisation tends to `1` as `g₀ → 0`.
18. **The translation Ward identity** (`WardT`): with `Θ_{μν} = R_{μν} + δ_{μν}(κ − 1)/4 · tr`
    (`stressC`, `R_{μν} = ∑_λ T_{μλνλ}`, so `Θ_{μμ} = κ · tr`, `κ` the trace-anomaly coefficient),
    for `h` equal to `1` near the supports of the fields in `I` and `0` near the others,
    `∑_μ S((Θ_{μν}, ∂_μ h), F) = −∑_{i ∈ I} S(F with fᵢ ↦ ∂_ν fᵢ)`. This fixes the normalisation of
    the traceless symmetric channel as the stress tensor's; a conserved improvement term would change
    the trace channel, which `ScalarTie` fixes.
19. **All composites** (`CompData`): `Tied`, `Covers`, `RenTri`, `RepTie` (the rotation
    representation agrees with the classical transformation of the monomials).
20. **OS0, OS1, existence, covariance and non-degeneracy on all composites** (`CompOS`): `ConvC`,
    `OS0C` (`|S(F)| ≤ α γⁿ (n!)^β ∏ᵢ Cᵢ d^{−κᵢ} ‖fᵢ‖_{L¹}`, one `Cᵢ, κᵢ` per composite), `OS1C`,
    `CovC` (`S((iⱼ, fⱼ ∘ A)) = ∑_σ ∏ⱼ rep A iⱼ σⱼ · S((σⱼ, fⱼ))`), and `CompNondeg`: every finite
    combination of composites whose top-dimension classical part is non-zero on some solution of
    the classical equations `D_μF_{μν} = 0` (`OnShell`) has a non-zero separated two-point function.
    Combinations vanishing on shell are the equation-of-motion fields, whose separated correlators
    vanish; every other composite survives the limit, so `HLC` is not the tensor's space again.
21. **OS3 on all composites** (`OS3C`).
22. **The link of all composites** (`LinkC`): vectors `wC P ∈ X.base.H` of the separated
    positive-time monomials of all composites, `⟪wC P, wC Q⟫ = sgn(P) S(ΘP ∪ Q)`
    (`sgn = (−1)^{#τ indices}`, `kernC`), the dyadic shift as `X.base.time`, `wC ∅ = X.base.vac`.
23. **OS2 on all composites** (`OS2C`). 24. **OS4 on all composites** (`OS4C`).
25. **The tensor among the composites** (`TIn`): `cl (e α)` is `Re tr F_{α₀α₁}F_{α₂α₃}`,
    `ren k (e α)` is the `α` component of the mixing, and `HLs X w ≤ HLC X wC`.
26. **The gap on the Hilbert space of all local fields** (`SpectralGapOn X.base (HLC X wC)`),
    `HLC` the closure of the span of all `wC P`: `H` self-adjoint, `HLC` invariant under every
    `e^{−tH}`, `Ω ∈ HLC`, `HΩ = 0`, `Δ‖u‖² ≤ ⟪u, Hu⟫` and `‖e^{−tH}u‖ ≤ e^{−Δt}‖u‖` on `HLC ⊖ Ω`,
    the fixed vectors on the vacuum line; so `H|_{HLC}` has spectrum in `{0} ∪ [Δ, ∞)`, `Δ > 0`,
    `0` simple.
27. **A non-zero vector** of `HLC` orthogonal to the vacuum.
28. **The observer carries the Hilbert space** (`ObsGen`): vectors `v P ∈ X.base.H` of the compact
    margin monomials of every local field with `⟪v P, v Q⟫ = S_W(θP ∪ Q)`, the observer's flowed
    Schwinger function (`contSF` of `energy0 W D hD`), equal to the observer's compact vectors
    `X.cvec` on the class `D`, carried by `X.base.time (a_m)` to the vectors of the monomials shifted
    by `a_m` in the direction `τ`, and with closed span all of `X.base.H`. So `X.base.H` is the GNS
    reconstruction of the observer's own form, with the time translations of clause 1 acting on it
    as the observer's time shifts; the vectors of clauses 8 and 22 lie in that space, and the
    cross readings of clause 8 pair them with the observer's states. A flow under which every local
    field reads a constant gives a rank-one form, a one-dimensional space, and no vector of clause 12
    (`ObserverCarries.not_clayStatementAt_flatFlow`).

## Reconstruction (a documented corollary, not formalised here)

`OS0C` bounds the kernel of `n` composites at mutual separation `≥ d` by
`α γⁿ (n!)^β ∏ Cᵢ d^{−κᵢ}` (take `fᵢ` approximating `δ`). A Schwartz function vanishing with all
derivatives on the diagonals is, by a dyadic partition around the diagonals, a sum of separated
pieces whose `L¹` norms decay faster than any power of the distance, which gives
`|S_n(f)| ≤ α′ (n!)^{β′} γ′ⁿ |f|_{κ′n}`: condition E0′ on `𝒮₀`. With covariance (`CovC`, `OS1C`),
positivity (`OS2C`, from the Gram identity), symmetry (`OS3C`) and clustering (`OS4C`), the
Osterwalder–Schrader II theorem reconstructs the Wightman theory of all composites, with the
reconstructed Hilbert space the one `HLC` spans and the energy the generator `H`; the gap of
clause 26 is then the mass gap of the joint spectrum, by Lorentz invariance.

## What the statement does not say

* The limit is along the fixed non-principal ultrafilter `ultra ≤ atTop`, a cluster point of the
  lattice sequences taken consistently for every family; independence of the choice and convergence
  along `atTop` are not claimed.
* The step from the kernel bounds to E0′ and the OS-II reconstruction are the documented corollary
  above, not formalised. The vacuum and time semigroup are given directly; the Hilbert space is
  generated by the observer (clause 28).
* The Weyl channel of `T`, and the composites beyond dimension four, carry a renormalisation that is
  a scheme choice (non-zero anomalous dimensions); they are tied to their classical expressions and
  required non-degenerate (`TensorNondeg`, `CompNondeg`), not normalised by a symmetry. The trace,
  pseudoscalar and traceless symmetric channels are normalised (clauses 2, 17, 18).
* The short-distance behaviour predicted by asymptotic freedom is stated for the trace two-point
  function (`AFCoefficient`); an operator product expansion of the composites with
  asymptotic-freedom coefficients is not stated.
* Other compact simple groups than `SU(N)` are not covered.

## What is proved here

* `clayData_of_link`, `clayStatementAt_of_link`: from the inputs, OS3 (`os3T`, `os3C`), OS2 from
  the Gram identities (`os2T_of_inner`, `os2C_of_link`), the invariance of `HL` and `HLC` under every
  `t ≥ 0` (`time_mem_HLg`), the two spectral clauses (`spectralGapOn_of_link`,
  `spectralGapOn_of_shift`), OS4 (`os4T_of_link`, `os4C_of_link` via `cluster_of_gram`),
  `AFShortDistance` from `AFCoefficient`, and the non-zero vector of `HLC` from that of `HL`
  (`nontrivial_HLC`).
* `span_single_dense`: the classes of the single monomials span a dense subspace of a GNS
  completion; `obsGen_observer` is clause 28 at `observerOSDataSLinked`, with `gvecT` and the Gram
  identity of `ContinuumFlow.flow_reconstruction`.
* Non-vacuity: `not_trace_zero`, `not_mix_zero`, `not_freeScalingForm`, `kernel_ne_freeMassless`.

The open inputs of `clayStatementAt_of_link` are listed there.

## Against `ObserverNontrivial.ClayFullT`

`ClayStatement` does not imply `ClayFullT`. `ClayFullT` asks OS0, OS1 and tensor covariance of
`contS (Renorm.connected Z)` on every family of test functions, coincident supports included, where
the value is `limUnder` of a sequence that diverges for genuine Yang–Mills; it is false for the
theory, so no statement true of the theory implies it. Its parts that are true — the functional, the
Hamiltonian gap, OS2, OS3, the gap on the reconstruction space — appear here on the corrected
objects.
-/

noncomputable section

namespace MassGap.ClayStatement

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ContinuumHypercubic MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ObserverSymField MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial Filter
open scoped Topology Matrix

variable {N : ℕ}

/-! ## 0. Classical configurations and composites -/

/-- A gauge potential: at each point and direction a matrix, written as `Fin N → Fin N → ℂ`.

DERIVED: `4` the dimension. -/
abbrev GPot (N : ℕ) : Type := (Fin 4 → ℝ) → Fin 4 → Fin N → Fin N → ℂ

/-- Smooth, with Hermitian traceless values.

DERIVED: `0` the trace. -/
def GPot.Adm (A : GPot N) : Prop :=
  (∀ n : ℕ, ContDiff ℝ n A)
    ∧ ∀ x μ, (Matrix.of (A x μ)).IsHermitian ∧ (Matrix.of (A x μ)).trace = 0

/-- The unit vector of direction `μ`. DERIVED: `1` its length; `4` the dimension. -/
def dir (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1

/-- The commutator. DERIVED: no numeral. -/
def mcomm (X Y : Fin N → Fin N → ℂ) : Fin N → Fin N → ℂ :=
  Matrix.of.symm (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X)

/-- **`D_{μ₁} ⋯ D_{μⱼ} F_{ρσ}`** for `U = exp(i a g A)`: `F_{ρσ} = ∂_ρA_σ − ∂_σA_ρ + i g [A_ρ, A_σ]`,
`D_μ X = ∂_μ X + i g [A_μ, X]`; the list is the derivatives, outermost first.

DERIVED: `4` the dimension. -/
def covDF (g : ℝ) (A : GPot N) (ρ σ : Fin 4) :
    List (Fin 4) → (Fin 4 → ℝ) → Fin N → Fin N → ℂ
  | [] => fun x => fderiv ℝ (fun y => A y σ) x (dir ρ) - fderiv ℝ (fun y => A y ρ) x (dir σ)
      + (Complex.I * (g : ℂ)) • mcomm (A x ρ) (A x σ)
  | μ :: ds => fun x => fderiv ℝ (covDF g A ρ σ ds) x (dir μ)
      + (Complex.I * (g : ℂ)) • mcomm (A x μ) (covDF g A ρ σ ds x)

/-- A letter `D_{ds} F_{ρσ}`. DERIVED: `4` the dimension. -/
abbrev Letter : Type := List (Fin 4) × Fin 4 × Fin 4

/-- A word: a product of letters. DERIVED: no numeral. -/
abbrev Word : Type := List Letter

/-- **A classical monomial** `∏ Re/Im tr(W)`: `true` the real part, `false` the imaginary part.

DERIVED: no numeral. -/
abbrev CMono : Type := List (Word × Bool)

/-- `tr W` at the origin. DERIVED: `0` the origin. -/
def wordTr (g : ℝ) (A : GPot N) (W : Word) : ℂ :=
  Matrix.trace ((W.map fun l => Matrix.of (covDF g A l.2.1 l.2.2 l.1 0)).prod)

/-- **The value of a classical monomial** at the origin. DERIVED: no numeral. -/
def cval (g : ℝ) (A : GPot N) (m : CMono) : ℝ :=
  (m.map fun p => if p.2 then (wordTr g A p.1).re else (wordTr g A p.1).im).prod

/-- The dimension of a letter: `2` for `F`, `1` per derivative. DERIVED: `2` the dimension of `F`. -/
def letDim (l : Letter) : ℕ := l.1.length + 2

/-- **The dimension of a monomial.** DERIVED: no numeral. -/
def cdim (m : CMono) : ℕ := (m.map fun p => (p.1.map letDim).sum).sum

/-- The number of field strengths, the power of `g` at leading order. DERIVED: no numeral. -/
def cnF (m : CMono) : ℕ := (m.map fun p => p.1.length).sum

/-- The number of indices equal to `τ`: the sign of the monomial under the reflection of `τ`.

DERIVED: `1`, `0` the counts; `4` the dimension. -/
def ctau (τ : Fin 4) (m : CMono) : ℕ :=
  (m.map fun p => (p.1.map fun l =>
    l.1.count τ + (if l.2.1 = τ then 1 else 0) + (if l.2.2 = τ then 1 else 0)).sum).sum

/-- **The rotated potential** `A′_μ(x) = ∑_ν R_{νμ} A_ν(R x)`.

DERIVED: `4` the dimension. -/
def rotPot (R : Matrix (Fin 4) (Fin 4) ℝ) (A : GPot N) : GPot N :=
  fun x μ => ∑ ν, R ν μ • A (R *ᵥ x) ν

/-- **The classical configuration** `U_μ(x) = exp(i a g A_μ(a x))` at spacing `a`.

DERIVED: `4` the dimension. -/
def IsClassCfg (a g : ℝ) (A : GPot N) (U : Cfg N) : Prop :=
  ∀ l, ((U l : MassGap.SUN.SU N) : Matrix (Fin N) (Fin N) ℂ)
    = NormedSpace.exp (Matrix.of ((Complex.I * ((a * g : ℝ) : ℂ)) • A (site a l.2) l.1))

/-- **The classical leading term**: `(L(U) − L(1))/a^d → P(A, g)` as `a → 0⁺` on the classical
configurations of every admissible potential.

DERIVED: `0` the point approached and the sign of the spacing; `1` the unit configuration. -/
def ClassicalLead (L : Cfg N → ℝ) (d : ℕ) (P : GPot N → ℝ → ℝ) : Prop :=
  ∀ A : GPot N, GPot.Adm A → ∀ (g : ℝ) (U : ℝ → Cfg N), (∀ a, 0 < a → IsClassCfg a g A (U a)) →
    Tendsto (fun a => (L (U a) - L (fun _ => (1 : MassGap.SUN.SU N))) / a ^ d) (𝓝[>] (0 : ℝ))
      (𝓝 (P A g))

/-- **On shell**: the classical Yang–Mills equations `∑_μ D_μ F_{μν} = 0`.

DERIVED: `0` the equations. -/
def OnShell (g : ℝ) (A : GPot N) : Prop := ∀ x ν, ∑ μ, covDF g A μ ν [μ] x = 0

/-- The `L¹` norm of a test function. DERIVED: no numeral. -/
def l1 (f : TestFn) : ℝ := ∫ x, |f.1 x|

/-! ## 1. The dimension-four sector on the lattice -/

/-- A component `(μ, ν, ρ, σ)` of a rank-four tensor.

DERIVED: `4` the rank and the dimension. -/
abbrev Idx4 : Type := Fin 4 → Fin 4

/-- **Renormalisation with mixing.** A finite basis `op b` of local gauge-invariant lattice fields
and, at each step `k`, the matrix `M k α b` giving the component `α` of `T` as `∑_b M k α b · op b`.

DERIVED: no numeral. -/
structure RenormMix (N : ℕ) where
  /-- The basis index. -/
  B : Type
  [fB : Fintype B]
  /-- The basis of lattice fields. -/
  op : B → LField (MassGap.SUN.SU N)
  /-- The mixing matrix of step `k`. -/
  M : ℕ → Idx4 → B → ℝ

attribute [instance] RenormMix.fB

/-- The transposition of the first pair. DERIVED: `0`–`3` the slots. -/
def swap01 (α : Idx4) : Idx4 := ![α 1, α 0, α 2, α 3]

/-- The transposition of the second pair. DERIVED: `0`–`3` the slots. -/
def swap23 (α : Idx4) : Idx4 := ![α 0, α 1, α 3, α 2]

/-- The exchange of the two pairs. DERIVED: `0`–`3` the slots. -/
def pairEx (α : Idx4) : Idx4 := ![α 2, α 3, α 0, α 1]

/-- **The Riemann-type symmetries of `tr F_{μν} F_{ρσ}`**, on the mixing at every step:
antisymmetry in each pair and symmetry under pair exchange.

DERIVED: no numeral. -/
def RenormMix.Riemann (ρ : RenormMix N) : Prop :=
  ∀ (k : ℕ) (α : Idx4) (b : ρ.B), ρ.M k (swap01 α) b = -ρ.M k α b
    ∧ ρ.M k (swap23 α) b = -ρ.M k α b ∧ ρ.M k (pairEx α) b = ρ.M k α b

/-- A field of the sector, `∑_α c_α T_α`, with a test function.

DERIVED: no numeral. -/
abbrev TDatum : Type := (Idx4 → ℝ) × TestFn

/-- The coefficient of the basis field `b` in `∑_α c_α T_α` at step `k`.

DERIVED: no numeral. -/
def mixC (ρ : RenormMix N) (k : ℕ) (c : Idx4 → ℝ) (b : ρ.B) : ℝ := ∑ α, c α * ρ.M k α b

/-- The connected basis field `op b − ν_k(op b)` with a test function.

DERIVED: `0` the excluded colour count. -/
def locField (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) (b : ρ.B) (f : TestFn) : SField N :=
  ((ρ.op b).sub (stateK hN k (ρ.op b).1), f)

/-- **The lattice Schwinger function of the sector at step `k`**, the multilinear expansion over the
basis: `∑_b ∏ᵢ mixC k cᵢ bᵢ · ν_k(∏ᵢ smear(op bᵢ − ν_k(op bᵢ)) fᵢ)`.

DERIVED: `0` the excluded colour count. -/
def latT (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → TDatum) : ℝ :=
  ∑ b : ι → ρ.B, (∏ i, mixC ρ k (F i).1 (b i)) * latSk hN k (fun i => locField hN ρ k (b i) (F i).2)

/-- **The continuum Schwinger function of the sector**: the limit along `ultra`. Every clause reads
it only on families where the convergence is asserted (`SepConv`).

DERIVED: `0` the excluded colour count. -/
def contT (hN : N ≠ 0) (ρ : RenormMix N) {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → TDatum) :
    ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latT hN ρ k F)

/-! ## 2. Admissible families -/

/-- The test functions of a family are pairwise `d`-separated.

DERIVED: no numeral. -/
def SepD {ι Xd : Type} (d : ℝ) (F : ι → Xd × TestFn) : Prop :=
  ∀ i j, i ≠ j → ContinuumSep.sepBy d (F i).2 (F j).2

/-- The test functions of a family are continuous.

DERIVED: no numeral. -/
def ContD {ι Xd : Type} (F : ι → Xd × TestFn) : Prop := ∀ i, Continuous (F i).2.1

/-- **Admissible**: continuous test functions, pairwise `d`-separated for some `d > 0`.

DERIVED: `0` the sign of the separation. -/
def Adm {ι Xd : Type} (F : ι → Xd × TestFn) : Prop := ContD F ∧ ∃ d : ℝ, 0 < d ∧ SepD d F

/-- The datum translated by `v`. DERIVED: `4` the dimension. -/
def translateD {Xd : Type} (v : Fin 4 → ℝ) (p : Xd × TestFn) : Xd × TestFn :=
  (p.1, p.2.translate v)

/-- The `ℓ¹` size of a coefficient tensor. DERIVED: no numeral. -/
def cnorm (c : Idx4 → ℝ) : ℝ := ∑ α, |c α|

/-- The coefficient tensor transformed by `A`: `(A·c)_β = ∑_α c_α ∏ⱼ A_{βⱼ αⱼ}`.

DERIVED: `4` the dimension. -/
def rotC (A : Matrix (Fin 4) (Fin 4) ℝ) (c : Idx4 → ℝ) : Idx4 → ℝ :=
  fun β => ∑ α, c α * tcoef A α β

/-- **The trace** `∑_{μ,ν} T_{μνμν}` as a coefficient tensor.

DERIVED: `0`–`3` the slots; `1`, `0` the coefficients. -/
def trC : Idx4 → ℝ := fun α => if α 2 = α 0 ∧ α 3 = α 1 then 1 else 0

/-- **The Ricci contraction** `R_{μν} = ∑_λ T_{μλνλ}` as a coefficient tensor.

DERIVED: `0`–`3` the slots; `1`, `0` the coefficients. -/
def ricC (μ ν : Fin 4) : Idx4 → ℝ := fun α => if α 0 = μ ∧ α 2 = ν ∧ α 3 = α 1 then 1 else 0

/-- **The stress tensor** `Θ_{μν} = R_{μν} + δ_{μν}(κ − 1)/4 · tr`: traceless part of `R` plus
`δ_{μν} κ/4 · tr`, so `Θ_{μμ} = κ · tr`.

DERIVED: `4` the dimension; `1` the trace part removed. -/
def stressC (κ : ℝ) (μ ν : Fin 4) : Idx4 → ℝ :=
  fun α => ricC μ ν α + (if μ = ν then (κ - 1) / 4 else 0) * trC α

/-- **The Levi-Civita tensor** `ε_{μνρσ}`.

DERIVED: `0` off the permutations. -/
def epsC : Idx4 → ℝ := fun α => by
  classical
  exact if h : Function.Bijective α then
    (((Equiv.Perm.sign (Equiv.ofBijective α h) : ℤˣ) : ℤ) : ℝ) else 0

/-- **The classical tensor** `Re tr F_{α₀α₁}(0) F_{α₂α₃}(0)`.

DERIVED: `0`–`3` the slots; `0` the origin. -/
def ffT (g : ℝ) (A : GPot N) : Idx4 → ℝ := fun α =>
  (Matrix.trace (Matrix.of (covDF g A (α 0) (α 1) [] 0)
    * Matrix.of (covDF g A (α 2) (α 3) [] 0))).re

/-- A hypercubic matrix: orthogonal with entries in `{−1, 0, 1}`, a signed permutation.

DERIVED: `1`, `0` the entries. -/
def IsHyp (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  A ∈ Matrix.orthogonalGroup (Fin 4) ℝ ∧ ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1

/-- The action of a channel matrix on coefficient tensors: the field `∑_α c_α ∑_β Z_{αβ} B_β` is
`∑_β (zAct Z c)_β B_β`.

DERIVED: no numeral. -/
def zAct (Z : Idx4 → Idx4 → ℝ) (c : Idx4 → ℝ) : Idx4 → ℝ := fun β => ∑ α, c α * Z α β

/-- **The channel tie.** The mixing factors through a fixed bare discretisation:
`M k α b = ∑_β Z k α β Mb β b`, `Z k` commutes with the hypercubic group, and the bare field
`B_β = ∑_b Mb β b op b` has classical leading term `g² Re tr F_{β₀β₁}F_{β₂β₃}` at dimension `4`.

DERIVED: `4` the dimension; `2` the power of the coupling. -/
def ChannelTie (ρ : RenormMix N) (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ) : Prop :=
  (∀ k α b, ρ.M k α b = ∑ β, Z k α β * Mb β b)
    ∧ (∀ k (A : Matrix (Fin 4) (Fin 4) ℝ), IsHyp A → ∀ c,
        zAct (Z k) (rotC A c) = rotC A (zAct (Z k) c))
    ∧ ∀ β, ClassicalLead (fun U => ∑ b, Mb β b * (ρ.op b).1 U) 4 (fun A g => g ^ 2 * ffT g A β)

/-- **The topological normalisation** of the pseudoscalar channel: `Z k ε = zq k ε` with
`zq k · a_k⁴ → 2`, so `q = (1/(64π²)) ∑ ε T = (g²/(32π²)) F^a F̃^a`.

DERIVED: `2 = F^aF^a/(tr FF)` at `tr(TᵃTᵇ) = δᵃᵇ/2`; `4` the dimension. -/
def TopNorm (N : ℕ) (Z : ℕ → Idx4 → Idx4 → ℝ) : Prop :=
  ∃ zq : ℕ → ℝ, (∀ k, zAct (Z k) epsC = zq k • epsC)
    ∧ Tendsto (fun k => zq k * dySpacing N k ^ 4) atTop (𝓝 2)

/-! ## 3. The clauses on the local fields -/

section Clauses

variable (hN : N ≠ 0) (ρ : RenormMix N)

/-- **Existence of the limit** on every admissible family.

DERIVED: no numeral. -/
def SepConv : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F →
    Tendsto (fun k => latT hN ρ k F) (ultra : Filter ℕ) (𝓝 (contT hN ρ F))

/-- **OS0, the kernel bound**: one `α, γ, β, κ` for the sector; on `d`-separated families of
continuous test functions, `0 < d ≤ 1`,
`|S(F)| ≤ α γⁿ (n!)^β d^{−κn} ∏ᵢ ‖cᵢ‖₁ ‖fᵢ‖_{L¹}`: the off-diagonal kernel of `n` fields at mutual
separation `≥ d` is bounded by `α γⁿ (n!)^β d^{−κn}`.

DERIVED: `1` the top of the separation, beyond which `d = 1` serves; `0` its sign. -/
def OS0Sep : Prop :=
  ∃ α γ β κ : ℝ, ∀ (n : ℕ) (F : Fin n → TDatum) (d : ℝ), 0 < d → d ≤ 1 → ContD F → SepD d F →
    |contT hN ρ F| ≤ α * γ ^ n * (n.factorial : ℝ) ^ β * (d ^ (κ * n))⁻¹
      * ∏ i, (cnorm (F i).1 * l1 (F i).2)

/-- **OS1**: the lattice sequence of every real translate of an admissible family converges to the
value of the family.

DERIVED: `4` the dimension. -/
def OS1Sep : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F → ∀ v : Fin 4 → ℝ,
    Tendsto (fun k => latT hN ρ k (fun i => translateD v (F i))) (ultra : Filter ℕ)
      (𝓝 (contT hN ρ F))

/-- **`O(4)` covariance of the sector**, on mixed families: for every orthogonal `A`, the lattice
sequence of `(cᵢ, fᵢ ∘ A)` converges to `S((A·cᵢ, fᵢ))`.

DERIVED: `4` the dimension. -/
def TensorCov : Prop :=
  ∀ A : Matrix (Fin 4) (Fin 4) ℝ, A ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → TDatum), Adm F →
      Tendsto (fun k => latT hN ρ k (fun i => ((F i).1, rotTest A (F i).2))) (ultra : Filter ℕ)
        (𝓝 (contT hN ρ (fun i => (rotC A (F i).1, (F i).2))))

/-- **OS3**, as an identity of the lattice readings at every step.

DERIVED: no numeral. -/
def OS3T : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι)
    (F : ι → TDatum) (k : ℕ), latT hN ρ k (F ∘ e) = latT hN ρ k F

/-- **The translation Ward identity.** For some trace-anomaly coefficient `κ`, every direction `ν`,
every admissible family `F` of `C¹` test functions and every `C¹` function `h` equal to `1` within
`d` of the supports of the fields in `I` and to `0` within `d` of the others:
`∑_μ S((Θ_{μν}, ∂_μ h), F) = −∑_{i ∈ I} S(F with fᵢ ↦ ∂_ν fᵢ)`. The derivatives enter as test
functions `dh μ`, `df i` equal to them pointwise.

DERIVED: `1` the differentiability order and the value of `h`; `0` its other value and the sign
of the separation. -/
def WardT : Prop :=
  ∃ κ : ℝ, ∀ (ν : Fin 4) (n : ℕ) (F : Fin n → TDatum) (I : Finset (Fin n))
      (h : (Fin 4 → ℝ) → ℝ) (dh : Fin 4 → TestFn) (df : Fin n → TestFn) (d : ℝ),
    0 < d → Adm F → ContDiff ℝ 1 h → (∀ μ x, (dh μ).1 x = fderiv ℝ h x (dir μ)) →
    (∀ i, ContDiff ℝ 1 (F i).2.1) → (∀ i x, (df i).1 x = fderiv ℝ (F i).2.1 x (dir ν)) →
    (∀ i x y, (F i).2.1 x ≠ 0 → dist x y < d → h y = if i ∈ I then 1 else 0) →
    ∑ μ, contT hN ρ (Fin.cons (α := fun _ => TDatum) (stressC κ μ ν, dh μ) F)
      = -∑ i ∈ I, contT hN ρ (Function.update F i ((F i).1, df i))

/-- The local reading of `n` insertions of the trace.

DERIVED: no numeral. -/
def contTr {n : ℕ} (u : Fin n → TestFn) : ℝ := contT hN ρ (fun i => (trC, u i))

/-- **The two-point kernel of the trace**: `G` continuous on `(0, ∞)` and, on separated continuous
test functions, `S(tr f, tr g) = ∫∫ f(x) g(y) G(|x − y|)`.

DERIVED: `0` the sign of the separation and the end of the half-line; `2` the order. -/
def TwoPointKernel (G : ℝ → ℝ) : Prop :=
  ContinuousOn G (Set.Ioi 0)
    ∧ ∀ f g : TestFn, Continuous f.1 → Continuous g.1 → (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g) →
      contTr hN ρ ![f, g] = ∫ x, ∫ y, f.1 x * g.1 y * G (ContinuumNontrivial.eDist x y)

/-- The connected three-point function of the trace.

DERIVED: `1`, `2`, `3` the orders; `2` the cumulant coefficient. -/
def cum3T (f g h : TestFn) : ℝ :=
  contTr hN ρ ![f, g, h] - contTr hN ρ ![f, g] * contTr hN ρ ![h]
    - contTr hN ρ ![f, h] * contTr hN ρ ![g] - contTr hN ρ ![g, h] * contTr hN ρ ![f]
    + 2 * contTr hN ρ ![f] * contTr hN ρ ![g] * contTr hN ρ ![h]

/-- **Non-Gaussian**: at a separated triple of continuous test functions the connected three-point
function of the trace is non-zero.

DERIVED: `0` the Gaussian value and the sign of the separation. -/
def NonGaussianT : Prop :=
  ∃ f g h : TestFn, Continuous f.1 ∧ Continuous g.1 ∧ Continuous h.1
    ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g ∧ ContinuumSep.sepBy d f h
        ∧ ContinuumSep.sepBy d g h)
    ∧ cum3T hN ρ f g h ≠ 0

/-- **The Riemann projection** of a coefficient tensor: its average over the eight-element group
generated by `swap01`, `swap23` (sign `−1`) and `pairEx` (sign `+1`). Under `RenormMix.Riemann` the
field `∑ c_α T_α` is the field of `projR c`.

DERIVED: `8` the order of the group; `1` the signs. -/
def projR (c : Idx4 → ℝ) : Idx4 → ℝ := fun α =>
  (c α - c (swap01 α) - c (swap23 α) + c (swap01 (swap23 α)) + c (pairEx α)
    - c (pairEx (swap01 α)) - c (pairEx (swap23 α)) + c (pairEx (swap01 (swap23 α)))) / 8

/-- **Every field of the sector is non-degenerate**: for every coefficient tensor with a non-zero
Riemann projection, some separated two-point function of `∑ c_α T_α` is non-zero.

DERIVED: `0` the excluded values and the sign of the separation; `2` the order. -/
def TensorNondeg : Prop :=
  ∀ c : Idx4 → ℝ, projR c ≠ 0 →
    ∃ f g : TestFn, Continuous f.1 ∧ Continuous g.1 ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f g)
      ∧ contT hN ρ ![(c, f), (c, g)] ≠ 0

end Clauses

/-- **The aperture's functional is a limit**: the flowed lattice functions are uniformly bounded
(`UniformBoundF`, so the inner limit along `ultra` exists, `tendsto_contSF`), and the outer limit in
the cut-off defining `schwSFM` converges at fields of `D`.

DERIVED: `0` the excluded colour count. -/
def ApertureConv (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) : Prop :=
  UniformBoundF hN (energy0 W D hD)
    ∧ ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)), (∀ i, O i ∈ D) →
      ∀ g : ι → Decaying,
        Tendsto (fun R : ℕ => contSF hN (energy0 W D hD) (fun i => (O i, cut (g i) R))) atTop
          (𝓝 (schwSFM hN W D hD O g))

/-- **The scalar tie.** The observer's field is `sym (plaqField q0)`, the sum over the hypercubic
group of the plaquette density; the trace channel of the mixing is at every step `Ztr k` times it,
with `Ztr k · a_k⁴ → N/8`. `sym (plaqField q0)` is `16` times the sum of the `24` plaquette densities
at the origin, each `a⁴ g² F^a_{μν} F^a_{μν}/(4N)` to leading order, so `(N/(8a⁴)) · sym (plaqField q0)`
is the bare `g₀² ∑_{μ,ν} F^a_{μν} F^a_{μν}`.

DERIVED: `8 = 16 · 4 / (2 · 4)` from the counting above; `4` the dimension of the field. -/
def ScalarTie (ρ : RenormMix N) (O : LField (MassGap.SUN.SU N)) : Prop :=
  O = sym (ObserverEnergyMoments.plaqField ObserverEnergyMoments.q0)
    ∧ ∃ Ztr : ℕ → ℝ, (∀ k, ∑ b, mixC ρ k trC b • (ρ.op b).1 = Ztr k • O.1)
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8))

/-- **`b₀` of `SU(N)`** in `μ dg/dμ = −b₀ g³ − b₁ g⁵`, the normalisation of `aRunStd`.

DERIVED: `11`, `3 · 16 = 48` the one-loop coefficient. -/
def b0 (N : ℕ) : ℝ := 11 * N / (48 * Real.pi ^ 2)

/-- The leading-log constant `12 (N² − 1)/(π⁴ b₀²)`: the tree value `48(N² − 1)/π⁴` of
`r⁸⟨g²F²(x) g²F²(0)⟩/g⁴` times `ḡ⁴(r) (log r)² → 1/(4b₀²)`.

DERIVED: `12 = 48/4`; `2` the squares; `4` the power of `π`. -/
def afConst (N : ℕ) : ℝ := 12 * ((N : ℝ) ^ 2 - 1) / (Real.pi ^ 4 * b0 N ^ 2)

/-- **The asymptotic-freedom coefficient**: `r⁸ G(r) (log r)² → 12(N² − 1)/(π⁴ b₀²)`.

DERIVED: `8`, `2` as in `AFShortDistance`; `0` the point approached. -/
def AFCoefficient (N : ℕ) (G : ℝ → ℝ) : Prop :=
  Tendsto (fun r => r ^ 8 * G r * Real.log r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (afConst N))

/-- DERIVED: `2` the least colour count; `0` the sign. -/
theorem afConst_pos (hN2 : 2 ≤ N) : 0 < afConst N := by
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hb : 0 < b0 N := div_pos (by linarith) (by positivity)
  have hn : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by nlinarith
  exact div_pos (by linarith) (by positivity)

/-- **`AFCoefficient` gives `AFShortDistance`.**

DERIVED: `2` the least colour count. -/
theorem afShortDistance_of_coefficient (hN2 : 2 ≤ N) {G : ℝ → ℝ} (h : AFCoefficient N G) :
    ShortDistanceY.AFShortDistance G :=
  ⟨afConst N, afConst_pos hN2, h⟩

#print axioms afShortDistance_of_coefficient

/-! ## 4. Monomials, reflection, the link -/

/-- The time reflection of a coefficient tensor: the component `α` by `(−1)^{#{j | αⱼ = τ}}`.

DERIVED: `1` the sign; `4` the dimension. -/
def reflC (τ : Fin 4) (c : Idx4 → ℝ) : Idx4 → ℝ :=
  fun α => (-1 : ℝ) ^ (Finset.univ.filter (fun j => α j = τ)).card * c α

/-- The time-reflected datum. DERIVED: `4` the dimension. -/
def reflD (τ : Fin 4) (p : TDatum) : TDatum := (reflC τ p.1, p.2.reflect τ)

/-- Monomials of data of type `Xd`. DERIVED: no numeral. -/
abbrev TMonoG (Xd : Type) : Type := Σ n : ℕ, (Fin n → Xd × TestFn)

/-- Monomials of the sector. DERIVED: no numeral. -/
abbrev TMono : Type := TMonoG (Idx4 → ℝ)

/-- Positive time beyond `d` and pairwise `d`-separation.

DERIVED: `4` the dimension. -/
def PosSepT {Xd : Type} (τ : Fin 4) (d : ℝ) (P : TMonoG Xd) : Prop :=
  (∀ i y, (P.2 i).2.1 y ≠ 0 → d ≤ y τ) ∧ SepD d P.2

/-- **Separated positive-time monomials** of continuous test functions, data of type `Xd`.

DERIVED: `0` the sign of the margin; `4` the dimension. -/
abbrev TSepG (Xd : Type) (τ : Fin 4) : Type :=
  {P : TMonoG Xd // ContD P.2 ∧ ∃ d : ℝ, 0 < d ∧ PosSepT τ d P}

/-- **Separated positive-time monomials** of the sector.

DERIVED: `4` the dimension. -/
abbrev TSep (τ : Fin 4) : Type := TSepG (Idx4 → ℝ) τ

/-- `ΘP ∪ Q`. DERIVED: `4` the dimension. -/
def pairT (τ : Fin 4) (P Q : TMono) : Fin P.1 ⊕ Fin Q.1 → TDatum :=
  Sum.elim (fun i => reflD τ (P.2 i)) Q.2

/-- **The reflection kernel** `S(ΘP ∪ Q)`. DERIVED: `0` the excluded colour count. -/
def kernT (hN : N ≠ 0) (ρ : RenormMix N) (τ : Fin 4) (P Q : TSep τ) : ℝ :=
  contT hN ρ (pairT τ P.1 Q.1)

/-- The empty monomial, data of type `Xd`. DERIVED: `0` its length; `1` a margin, any positive
one serves. -/
def emptyG (Xd : Type) (τ : Fin 4) : TSepG Xd τ :=
  ⟨⟨0, Fin.elim0⟩, fun i => i.elim0, 1, one_pos, fun i => i.elim0, fun i => i.elim0⟩

/-- The empty monomial of the sector. DERIVED: `4` the dimension. -/
def emptyT (τ : Fin 4) : TSep τ := emptyG (Idx4 → ℝ) τ

/-- **The forward time step** by `dySpacing N m` in direction `τ`.

DERIVED: `0` the excluded colour count; `1` one step. -/
def shiftT {Xd : Type} (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) (P : TSepG Xd τ) : TSepG Xd τ :=
  ⟨⟨P.1.1, fun i => translateD (timeVec N m τ 1) (P.1.2 i)⟩, by
    have hv : 0 ≤ timeVec N m τ 1 τ := by
      simpa using ContinuumSep.timeVec_nonneg hN m τ 1
    obtain ⟨hc, d, hd, h1, h2⟩ := P.2
    refine ⟨fun i => (hc i).comp (continuous_id.sub continuous_const), d, hd, fun i y hy => ?_,
      fun i j hij => ContinuumSep.sepBy_translate (h2 i j hij) _⟩
    have h := h1 i (y - timeVec N m τ 1) hy
    have e : (y - timeVec N m τ 1) τ = y τ - timeVec N m τ 1 τ := rfl
    rw [e] at h
    linarith⟩

/-- **The mixed lattice reading** of step `k`: `ΘP` local, `Q` flowed by `Φ`.

DERIVED: `0` the excluded colour count. -/
def mixLatT (hN : N ≠ 0) (ρ : RenormMix N) (Φ : Flow N) (τ : Fin 4) (k : ℕ) (P : TMono)
    (Q : Mono N) : ℝ :=
  ∑ b : Fin P.1 → ρ.B, (∏ i, mixC ρ k (reflC τ (P.2 i).1) (b i))
    * latSk hN k (Sum.elim (fun i => locField hN ρ k (b i) ((P.2 i).2.reflect τ))
        (fun j => Φ.field k (Q.2 j)))

/-- The mixed reading: the limit along `ultra`. DERIVED: `0` the excluded colour count. -/
def mixT (hN : N ≠ 0) (ρ : RenormMix N) (Φ : Flow N) (τ : Fin 4) (P : TMono) (Q : Mono N) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => mixLatT hN ρ Φ τ k P Q)

/-- **The closed span** of a family of vectors. DERIVED: no numeral. -/
def HLg (Y : OSDataS) {M : Type} (w : M → Y.H) : Submodule ℂ Y.H :=
  (Submodule.span ℂ (Set.range w)).topologicalClosure

section Link

variable {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}

/-- **The link of the sector to the aperture's Hilbert space**: the Gram identity with the
convergence of the lattice sequence of `ΘP ∪ Q`, the dyadic shift as `X.base.time`, the local vacuum
`w ∅ = X.base.vac`, and the convergent cross reading `⟪w P, X.cvec Q⟫`.

DERIVED: `4` the dimension. -/
def LinkTS (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (w : TSep τ → X.base.H) : Prop :=
  (∀ P Q : TSep τ, Tendsto (fun k => latT hN ρ k (pairT τ P.1 Q.1)) (ultra : Filter ℕ)
        (𝓝 (kernT hN ρ τ P Q))
      ∧ inner ℂ (w P) (w Q) = (kernT hN ρ τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSep τ), w (shiftT hN τ m P) = X.base.time (dySpacing N m) (w P))
    ∧ w (emptyT τ) = X.base.vac
    ∧ ∀ (P : TSep τ) (Q : MarginMonoD N D τ r),
        Tendsto (fun k => mixLatT hN ρ (energy0 W D hD) τ k P.1 Q.1.1) (ultra : Filter ℕ)
            (𝓝 (mixT hN ρ (energy0 W D hD) τ P.1 Q.1.1))
          ∧ inner ℂ (w P) (X.cvec Q) = (mixT hN ρ (energy0 W D hD) τ P.1 Q.1.1 : ℂ)

/-- **The reconstruction space of the sector**: the closure of the span of the vectors `w P`.

DERIVED: no numeral. -/
def HLs (X : OSDataSLinked N D τ r) (w : TSep τ → X.base.H) : Submodule ℂ X.base.H :=
  HLg X.base w

/-- **The observer carries the Hilbert space**: vectors `v P` of the compact margin monomials of
every local field that are the observer's compact vectors on the class `D` (`v Q = X.cvec Q`), with
inner products the observer's flowed Schwinger functions of the reflected pairs,
`⟪v P, v Q⟫ = S_W(θP ∪ Q)` (`contSF` of `energy0 W D hD`), on which the time translation by `a_m`
acts as the dyadic shift of the test functions by `a_m` in the direction `τ`, and whose closed span
is the whole space.

DERIVED: `1` one step. -/
def ObsGen (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (X : OSDataSLinked N D τ r) : Prop :=
  ∃ v : MarginMono N τ r → X.base.H,
    (∀ Q : MarginMonoD N D τ r, v Q.1 = X.cvec Q)
    ∧ (∀ P Q : MarginMono N τ r,
      inner ℂ (v P) (v Q) = (contSF hN (energy0 W D hD) (pairFam τ P.1 Q.1) : ℂ))
    ∧ (∀ (m : ℕ) (P Q : MarginMono N τ r),
      Q.1 = ⟨P.1.1, fun i => ((P.1.2 i).1, (P.1.2 i).2.translate (timeVec N m τ 1))⟩ →
        v Q = X.base.time (dySpacing N m) (v P))
    ∧ HLg X.base v = ⊤

/-- **The spectral clause on a closed subspace `HL`.** `H` self-adjoint; `HL` invariant under every
`e^{−tH}`, `t ≥ 0`; `Ω ∈ HL`, `HΩ = 0`; `Δ‖u‖² ≤ re⟪u, Hu⟫` and `‖e^{−tH}u‖ ≤ e^{−Δt}‖u‖` on
`HL ⊖ Ω`; the fixed vectors of `HL` on the vacuum line. With the self-adjoint contractions
`e^{−tH}`, the invariance makes `HL` reducing, and the clause says `H|_HL` is self-adjoint with
spectrum in `{0} ∪ [Δ, ∞)`, `0` simple.

DERIVED: `0` the bottom, the time origin, the zero vector and the vanishing pairing; `2` the
square of the norm. -/
def SpectralGapOn (X : OSDataS) (HL : Submodule ℂ X.H) : Prop :=
  IsSelfAdjoint (ClassHamiltonian.generator X.time)
    ∧ (∀ t : ℝ, 0 ≤ t → ∀ u ∈ HL, X.time t u ∈ HL)
    ∧ X.vac ∈ HL
    ∧ (∃ h : X.vac ∈ (ClassHamiltonian.generator X.time).domain,
        ClassHamiltonian.generator X.time ⟨X.vac, h⟩ = 0)
    ∧ (∀ u : (ClassHamiltonian.generator X.time).domain, (u : X.H) ∈ HL →
        inner ℂ X.vac (u : X.H) = 0 →
          X.gap * ‖(u : X.H)‖ ^ 2 ≤ (inner ℂ (u : X.H) (ClassHamiltonian.generator X.time u)).re)
    ∧ (∀ u ∈ HL, inner ℂ X.vac u = 0 → ∀ t : ℝ, 0 ≤ t →
        ‖X.time t u‖ ≤ Real.exp (-(X.gap * t)) * ‖u‖)
    ∧ (∀ t : ℝ, 0 < t → ∀ u ∈ HL, X.time t u = u → ∃ c : ℂ, u = c • X.vac)

/-- **OS2 at margin `0`** on separated positive-time monomials of the sector.

DERIVED: `0` the sign. -/
def OS2T (hN : N ≠ 0) (ρ : RenormMix N) (τ : Fin 4) : Prop :=
  ∀ (s : Finset (TSep τ)) (c : TSep τ → ℝ), 0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernT hN ρ τ P Q

/-- **OS4, clustering**: `S(ΘP ∪ shiftⁿ Q) → S(ΘP) S(Q)`.

DERIVED: no numeral. -/
def OS4T (hN : N ≠ 0) (ρ : RenormMix N) (τ : Fin 4) : Prop :=
  ∀ (m : ℕ) (P Q : TSep τ),
    Tendsto (fun n : ℕ => kernT hN ρ τ P ((shiftT hN τ m)^[n] Q)) atTop
      (𝓝 (kernT hN ρ τ P (emptyT τ) * kernT hN ρ τ (emptyT τ) Q))

end Link

/-! ## 5. All gauge-invariant local composites -/

/-- **A family of local composites.** For each index `i`: its classical monomial `cl i`, a bare
lattice field `bare i`, its renormalised lattice field `ren k i` at step `k`, and its rotation
representation `rep A i` (the coefficients of the rotated composite in the family).

DERIVED: `4` the dimension. -/
structure Composites (N : ℕ) where
  /-- The index type. -/
  Ix : Type
  /-- The classical monomial. -/
  cl : Ix → CMono
  /-- The bare lattice field. -/
  bare : Ix → LField (MassGap.SUN.SU N)
  /-- The renormalised lattice field of step `k`. -/
  ren : ℕ → Ix → LField (MassGap.SUN.SU N)
  /-- The rotation representation. -/
  rep : Matrix (Fin 4) (Fin 4) ℝ → Ix → (Ix →₀ ℝ)

/-- **Each bare field discretises its monomial**: classical leading term `g^{#F} cl i` at
dimension `cdim (cl i)`.

DERIVED: no numeral. -/
def Composites.Tied (C : Composites N) : Prop :=
  ∀ i, ClassicalLead (C.bare i).1 (cdim (C.cl i)) (fun A g => g ^ cnF (C.cl i) * cval g A (C.cl i))

/-- **Every composite is in the family**: every non-empty classical monomial of non-empty words, of
any dimension, real or imaginary parts, is some `cl i`.

DERIVED: no numeral. -/
def Composites.Covers (C : Composites N) : Prop :=
  ∀ m : CMono, m ≠ [] → (∀ p ∈ m, p.1 ≠ []) → ∃ i, C.cl i = m

/-- The span of `1` and the fields `F i` of dimension `≤ d`.

DERIVED: `1` the unit field. -/
def Composites.lowSpan (C : Composites N) (F : C.Ix → LField (MassGap.SUN.SU N)) (d : ℕ) :
    Submodule ℝ (ContinuousMap (Cfg N) ℝ) :=
  Submodule.span ℝ (insert 1 (Set.range fun i : {i // cdim (C.cl i) ≤ d} => (F i.1).1))

/-- **Triangular, invertible renormalisation**: `ren k i` is a combination of `1` and bare fields of
dimension `≤ cdim (cl i)`, and at every level `d` the bare fields are combinations of `1` and the
renormalised ones.

DERIVED: no numeral. -/
def Composites.RenTri (C : Composites N) : Prop :=
  (∀ k i, (C.ren k i).1 ∈ C.lowSpan C.bare (cdim (C.cl i)))
    ∧ ∀ k d, C.lowSpan C.bare d ≤ C.lowSpan (C.ren k) d

/-- **The rotation representation is the classical one**: on every admissible potential
(`GPot.Adm`, the class `Tied` and `CompNondeg` read), the monomial of the rotated potential is
`∑_j rep A i j` times the monomials `cl j`. Without the admissibility clause `Covers` excludes it
(`CompositesObserver.not_covers_and_repTieAll`).

DERIVED: `4` the dimension. -/
def Composites.RepTie (C : Composites N) : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (i : C.Ix) (A : GPot N), GPot.Adm A → ∀ g : ℝ,
      cval g (rotPot R A) (C.cl i) = ∑ j ∈ (C.rep R i).support, C.rep R i j * cval g A (C.cl j)

/-- **The composites clauses** on the family. DERIVED: no numeral. -/
def CompData (C : Composites N) : Prop := C.Tied ∧ C.Covers ∧ C.RenTri ∧ C.RepTie

/-- A composite with a test function. DERIVED: no numeral. -/
abbrev CDatum (C : Composites N) : Type := C.Ix × TestFn

/-- The connected renormalised composite `ren k i − ν_k(ren k i)` with its test function.

DERIVED: `0` the excluded colour count. -/
def cField (hN : N ≠ 0) (C : Composites N) (k : ℕ) (p : CDatum C) : SField N :=
  ((C.ren k p.1).sub (stateK hN k (C.ren k p.1).1), p.2)

/-- **The lattice Schwinger function of the composites at step `k`.**

DERIVED: `0` the excluded colour count. -/
def latC (hN : N ≠ 0) (C : Composites N) (k : ℕ) {ι : Type} [Fintype ι] (F : ι → CDatum C) : ℝ :=
  latSk hN k (fun i => cField hN C k (F i))

/-- **The continuum Schwinger function of the composites**, the limit along `ultra`.

DERIVED: `0` the excluded colour count. -/
def contC (hN : N ≠ 0) (C : Composites N) {ι : Type} [Fintype ι] (F : ι → CDatum C) : ℝ :=
  limUnder (ultra : Filter ℕ) (fun k => latC hN C k F)

section CompClauses

variable (hN : N ≠ 0) (C : Composites N)

/-- **Existence of the limit** on every admissible family of composites.

DERIVED: no numeral. -/
def ConvC : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum C), Adm F →
    Tendsto (fun k => latC hN C k F) (ultra : Filter ℕ) (𝓝 (contC hN C F))

/-- **OS0 on all composites**: `|S(F)| ≤ α γⁿ (n!)^β ∏ᵢ Cᵢ d^{−κᵢ} ‖fᵢ‖_{L¹}` on `d`-separated
families of continuous test functions, `0 < d ≤ 1`, one `Cᵢ`, `κᵢ` per composite.

DERIVED: `1` the top of the separation; `0` its sign. -/
def OS0C : Prop :=
  ∃ (α γ β : ℝ) (Cc κ : C.Ix → ℝ), ∀ (n : ℕ) (F : Fin n → CDatum C) (d : ℝ), 0 < d → d ≤ 1 →
    ContD F → SepD d F →
      |contC hN C F| ≤ α * γ ^ n * (n.factorial : ℝ) ^ β
        * ∏ i, (Cc (F i).1 * (d ^ κ (F i).1)⁻¹ * l1 (F i).2)

/-- **OS1 on all composites.** DERIVED: `4` the dimension. -/
def OS1C : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum C), Adm F → ∀ v : Fin 4 → ℝ,
    Tendsto (fun k => latC hN C k (fun i => translateD v (F i))) (ultra : Filter ℕ)
      (𝓝 (contC hN C F))

/-- **`O(4)` covariance of all composites**: the lattice sequence of `(iⱼ, fⱼ ∘ A)` converges to
`∑_σ ∏ⱼ rep A iⱼ σⱼ · S((σⱼ, fⱼ))`.

DERIVED: `4` the dimension. -/
def CovC : Prop :=
  ∀ R : Matrix (Fin 4) (Fin 4) ℝ, R ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ι → CDatum C), Adm F →
      Tendsto (fun k => latC hN C k (fun i => ((F i).1, rotTest R (F i).2))) (ultra : Filter ℕ)
        (𝓝 (∑ σ ∈ Fintype.piFinset (fun i => (C.rep R (F i).1).support),
          (∏ i, C.rep R (F i).1 (σ i)) * contC hN C (fun i => (σ i, (F i).2))))

/-- **Non-degeneracy of all composites, modulo the equations of motion.** For every finite
combination `∑ cᵢ Φᵢ` whose top-dimension classical part is non-zero on some on-shell potential
(`OnShell`), some separated two-point function of the combination is non-zero. Combinations whose
top part vanishes on shell (equation-of-motion fields, whose separated correlators vanish by the
Schwinger–Dyson equations) are not asked about. This excludes composites that vanish in the limit.

DERIVED: `0` the excluded values and the sign of the separation; `2` the order. -/
def CompNondeg : Prop :=
  ∀ c : C.Ix →₀ ℝ,
    (∃ (A : GPot N) (g : ℝ), GPot.Adm A ∧ OnShell g A
      ∧ ∑ i ∈ c.support.filter (fun i => cdim (C.cl i) = c.support.sup (fun j => cdim (C.cl j))),
          c i * g ^ cnF (C.cl i) * cval g A (C.cl i) ≠ 0) →
    ∃ f h : TestFn, Continuous f.1 ∧ Continuous h.1 ∧ (∃ d : ℝ, 0 < d ∧ ContinuumSep.sepBy d f h)
      ∧ ∑ i ∈ c.support, ∑ j ∈ c.support,
          c i * c j * contC hN C (![(i, f), (j, h)] : Fin 2 → CDatum C) ≠ 0

/-- **The analytic clauses on all composites.** DERIVED: no numeral. -/
def CompOS : Prop := ConvC hN C ∧ OS0C hN C ∧ OS1C hN C ∧ CovC hN C ∧ CompNondeg hN C

/-- **OS3 on all composites**, as an identity of the lattice readings at every step.

DERIVED: no numeral. -/
def OS3C : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι' ≃ ι) (F : ι → CDatum C) (k : ℕ),
    latC hN C k (F ∘ e) = latC hN C k F

/-- The reflection sign of a monomial of composites, `∏ᵢ (−1)^{#τ indices of cl iᵢ}`.

DERIVED: `1` the sign. -/
def sgnC (τ : Fin 4) (P : TMonoG C.Ix) : ℝ := ∏ i, (-1 : ℝ) ^ ctau τ (C.cl (P.2 i).1)

/-- `ΘP ∪ Q` for composites: the test functions of `P` reflected. DERIVED: `4` the dimension. -/
def pairC (τ : Fin 4) (P Q : TMonoG C.Ix) : Fin P.1 ⊕ Fin Q.1 → CDatum C :=
  Sum.elim (fun i => ((P.2 i).1, (P.2 i).2.reflect τ)) Q.2

/-- **The reflection kernel of the composites** `sgn(P) S(ΘP ∪ Q)`.

DERIVED: no numeral. -/
def kernC (τ : Fin 4) (P Q : TSepG C.Ix τ) : ℝ := sgnC C τ P.1 * contC hN C (pairC C τ P.1 Q.1)

/-- **OS2 on all composites.** DERIVED: `0` the sign. -/
def OS2C (τ : Fin 4) : Prop :=
  ∀ (s : Finset (TSepG C.Ix τ)) (c : TSepG C.Ix τ → ℝ),
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernC hN C τ P Q

/-- **OS4 on all composites.** DERIVED: no numeral. -/
def OS4C (τ : Fin 4) : Prop :=
  ∀ (m : ℕ) (P Q : TSepG C.Ix τ),
    Tendsto (fun n : ℕ => kernC hN C τ P ((shiftT hN τ m)^[n] Q)) atTop
      (𝓝 (kernC hN C τ P (emptyG C.Ix τ) * kernC hN C τ (emptyG C.Ix τ) Q))

end CompClauses

section LinkC

variable {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}

/-- **The link of all composites** to the aperture's Hilbert space: the Gram identity with the
convergence of the lattice sequence of `ΘP ∪ Q`, the dyadic shift as `X.base.time`, and
`wC ∅ = X.base.vac`.

DERIVED: no numeral. -/
def LinkC (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (C : Composites N)
    (wC : TSepG C.Ix τ → X.base.H) : Prop :=
  (∀ P Q : TSepG C.Ix τ,
      Tendsto (fun k => latC hN C k (pairC C τ P.1 Q.1)) (ultra : Filter ℕ)
          (𝓝 (contC hN C (pairC C τ P.1 Q.1)))
        ∧ inner ℂ (wC P) (wC Q) = (kernC hN C τ P Q : ℂ))
    ∧ (∀ (m : ℕ) (P : TSepG C.Ix τ), wC (shiftT hN τ m P) = X.base.time (dySpacing N m) (wC P))
    ∧ wC (emptyG C.Ix τ) = X.base.vac

/-- **The Hilbert space of all local fields**: the closure of the span of the vectors `wC P`.

DERIVED: no numeral. -/
def HLC (X : OSDataSLinked N D τ r) {C : Composites N} (wC : TSepG C.Ix τ → X.base.H) :
    Submodule ℂ X.base.H :=
  HLg X.base wC

/-- **The tensor among the composites**: an index `e α` with classical monomial
`Re tr F_{α₀α₁} F_{α₂α₃}` whose renormalised field is the `α` component of the mixing, and the
tensor's space inside the space of all local fields.

DERIVED: `0`–`3` the slots. -/
def TIn (ρ : RenormMix N) (C : Composites N) (X : OSDataSLinked N D τ r) (w : TSep τ → X.base.H)
    (wC : TSepG C.Ix τ → X.base.H) : Prop :=
  ∃ e : Idx4 → C.Ix, (∀ α, C.cl (e α) = [([([], α 0, α 1), ([], α 2, α 3)], true)])
    ∧ (∀ k α, (C.ren k (e α)).1 = ∑ b, ρ.M k α b • (ρ.op b).1)
    ∧ HLs X w ≤ HLC X wC

end LinkC

/-! ## 6. The statement -/

/-- DERIVED: `2` the least colour count; `0` the excluded one. -/
theorem ne_zero_of_two_le (hN2 : 2 ≤ N) : N ≠ 0 := by omega

/-- **All clauses at one witness.** See the module docstring for the list.

DERIVED: `0` the vanishing pairing and the zero vector; `4` the dimension. -/
def ClayData (hN2 : 2 ≤ N) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) (τ : Fin 4) (r : ℝ)
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (G : ℝ → ℝ) (w : TSep τ → X.base.H)
    (C : Composites N) (wC : TSepG C.Ix τ → X.base.H) : Prop :=
  (∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      X.SM O g = schwSFM (ne_zero_of_two_le hN2) W D hD O g)
    ∧ HamiltonianGap X.base
    ∧ ρ.Riemann ∧ ScalarTie ρ X.O
    ∧ SepConv (ne_zero_of_two_le hN2) ρ ∧ OS0Sep (ne_zero_of_two_le hN2) ρ
    ∧ OS1Sep (ne_zero_of_two_le hN2) ρ ∧ TensorCov (ne_zero_of_two_le hN2) ρ
    ∧ OS3T (ne_zero_of_two_le hN2) ρ
    ∧ LinkTS (ne_zero_of_two_le hN2) W D hD X ρ w ∧ OS2T (ne_zero_of_two_le hN2) ρ τ
    ∧ SpectralGapOn X.base (HLs X w) ∧ OS4T (ne_zero_of_two_le hN2) ρ τ
    ∧ (∃ u ∈ HLs X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    ∧ TwoPointKernel (ne_zero_of_two_le hN2) ρ G ∧ AFCoefficient N G
    ∧ ShortDistanceY.AFShortDistance G
    ∧ NonGaussianT (ne_zero_of_two_le hN2) ρ
    ∧ TensorNondeg (ne_zero_of_two_le hN2) ρ
    ∧ ApertureConv (ne_zero_of_two_le hN2) W D hD
    ∧ (∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTie ρ Mb Z ∧ TopNorm N Z)
    ∧ WardT (ne_zero_of_two_le hN2) ρ
    ∧ CompData C ∧ CompOS (ne_zero_of_two_le hN2) C ∧ OS3C (ne_zero_of_two_le hN2) C
    ∧ LinkC (ne_zero_of_two_le hN2) X C wC ∧ OS2C (ne_zero_of_two_le hN2) C τ
    ∧ OS4C (ne_zero_of_two_le hN2) C τ
    ∧ TIn ρ C X w wC
    ∧ SpectralGapOn X.base (HLC X wC)
    ∧ (∃ u ∈ HLC X wC, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    ∧ ObsGen (ne_zero_of_two_le hN2) W D hD X

/-- **The Clay statement at one lattice construction, with an extension point.** `Ext` is a clause
on the same witness.

DERIVED: `4` the dimension. -/
def ClayStatementAtExt (hN2 : 2 ≤ N) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (Ext : (τ : Fin 4) → (r : ℝ) → (X : OSDataSLinked N D τ r) → RenormMix N →
      (TSep τ → X.base.H) → Prop) : Prop :=
  ∃ (τ : Fin 4) (r : ℝ) (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (G : ℝ → ℝ)
    (w : TSep τ → X.base.H) (C : Composites N) (wC : TSepG C.Ix τ → X.base.H),
    ClayData hN2 W D hD τ r X ρ G w C wC ∧ Ext τ r X ρ w

/-- **The Clay statement at one lattice construction**, on all gauge-invariant local composites.

DERIVED: `4` the dimension. -/
def ClayStatementAt (hN2 : 2 ≤ N) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) : Prop :=
  ClayStatementAtExt hN2 W D hD (fun _ _ _ _ _ => True)

/-- **The Clay Yang–Mills statement for `SU(N)`, every `N ≥ 2`, at the frozen tower**, on all
gauge-invariant local composites.

DERIVED: `2` the least colour count; `4` the dimension. -/
def _root_.MassGap.ClayStatementDy : Prop :=
  ∀ N : ℕ, ∀ hN2 : 2 ≤ N, ∃ (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D),
    ClayStatementAt hN2 W D hD

/-! ## 7. What transfers -/

section Transfer

/-- **OS3 at every step**: reindexing the family reindexes the basis choices.

DERIVED: no numeral. -/
theorem os3T (hN : N ≠ 0) (ρ : RenormMix N) : OS3T hN ρ := by
  intro ι ι' _ _ _ _ e F k
  unfold latT
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl ρ.B)) _ _ (fun b => ?_)
  have hb : ∀ i', (e.arrowCongr (Equiv.refl ρ.B) b) (e i') = b i' := fun i' => by
    simp [Equiv.arrowCongr_apply]
  congr 1
  · rw [← Equiv.prod_comp e]
    exact Finset.prod_congr rfl (fun i' _ => by rw [hb]; rfl)
  · have hG : (fun i' => locField hN ρ k (b i') ((F ∘ e) i').2)
        = (fun i => locField hN ρ k ((e.arrowCongr (Equiv.refl ρ.B)) b i) (F i).2) ∘ e := by
      funext i'
      simp only [Function.comp_apply, hb]
    rw [hG]
    exact latS_comp_equiv (stateK hN k) (dySpacing N k) e _

#print axioms os3T

/-- **OS3 on all composites**, at every step.

DERIVED: no numeral. -/
theorem os3C (hN : N ≠ 0) (C : Composites N) : OS3C hN C := by
  intro ι ι' _ _ e F k
  exact latS_comp_equiv (stateK hN k) (dySpacing N k) e (fun i => cField hN C k (F i))

#print axioms os3C

/-- The lattice reading of a family over an empty type is `1`.

DERIVED: `1` the value. -/
theorem latT_of_isEmpty (hN : N ≠ 0) (ρ : RenormMix N) (k : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] [IsEmpty ι] (F : ι → TDatum) : latT hN ρ k F = 1 := by
  unfold latT
  rw [Fintype.sum_unique, Fintype.prod_empty, one_mul]
  show (stateK hN k) (∏ i, smear (dySpacing N k) _ _) = 1
  rw [Fintype.prod_empty]
  exact (stateK hN k).map_one

#print axioms latT_of_isEmpty

/-- The lattice reading of composites over an empty type is `1`.

DERIVED: `1` the value. -/
theorem latC_of_isEmpty (hN : N ≠ 0) (C : Composites N) (k : ℕ) {ι : Type} [Fintype ι]
    [IsEmpty ι] (F : ι → CDatum C) : latC hN C k F = 1 := by
  show (stateK hN k) (∏ i, smear (dySpacing N k) _ _) = 1
  rw [Fintype.prod_empty]
  exact (stateK hN k).map_one

#print axioms latC_of_isEmpty

/-- **`S(Θ∅ ∪ ∅) = 1`.** DERIVED: `1` the value. -/
theorem kernT_empty (hN : N ≠ 0) (ρ : RenormMix N) (τ : Fin 4) :
    kernT hN ρ τ (emptyT τ) (emptyT τ) = 1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  haveI : IsEmpty (Fin (emptyT τ).1.1 ⊕ Fin (emptyT τ).1.1) := by
    show IsEmpty (Fin 0 ⊕ Fin 0)
    infer_instance
  unfold kernT contT
  have e : (fun k => latT hN ρ k (pairT τ (emptyT τ).1 (emptyT τ).1)) = fun _ => (1 : ℝ) :=
    funext fun k => latT_of_isEmpty hN ρ k _
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

#print axioms kernT_empty

/-- **`sgn(∅) S(Θ∅ ∪ ∅) = 1`** for the composites. DERIVED: `1` the value. -/
theorem kernC_empty (hN : N ≠ 0) (C : Composites N) (τ : Fin 4) :
    kernC hN C τ (emptyG C.Ix τ) (emptyG C.Ix τ) = 1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  haveI : IsEmpty (Fin (emptyG C.Ix τ).1.1 ⊕ Fin (emptyG C.Ix τ).1.1) := by
    show IsEmpty (Fin 0 ⊕ Fin 0)
    infer_instance
  haveI : IsEmpty (Fin (emptyG C.Ix τ).1.1) := by
    show IsEmpty (Fin 0)
    infer_instance
  unfold kernC contC sgnC
  have e : (fun k => latC hN C k (pairC C τ (emptyG C.Ix τ).1 (emptyG C.Ix τ).1))
      = fun _ => (1 : ℝ) :=
    funext fun k => latC_of_isEmpty hN C k _
  have h1 : limUnder (ultra : Filter ℕ) (fun _ : ℕ => (1 : ℝ)) = 1 :=
    tendsto_const_nhds.limUnder_eq
  rw [e, h1, Fintype.prod_empty, one_mul]

#print axioms kernC_empty

variable {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ}

/-- **OS2 from the Gram identity**: `∑ c_P c_Q S(ΘP ∪ Q) = ‖∑ c_P w P‖²`.

DERIVED: `0` the sign. -/
theorem os2T_of_inner (hN : N ≠ 0) (ρ : RenormMix N) (X : OSDataSLinked N D τ r)
    {w : TSep τ → X.base.H}
    (hin : ∀ P Q : TSep τ, inner ℂ (w P) (w Q) = (kernT hN ρ τ P Q : ℂ)) : OS2T hN ρ τ := by
  intro s c
  set v : X.base.H := ∑ P ∈ s, (c P : ℂ) • w P with hv
  have e : inner ℂ v v = ((∑ P ∈ s, ∑ Q ∈ s, c P * c Q * kernT hN ρ τ P Q : ℝ) : ℂ) := by
    simp only [hv, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hin,
      Complex.conj_ofReal]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  have h0 := inner_self_nonneg (𝕜 := ℂ) (x := v)
  rw [e] at h0
  simpa using h0

#print axioms os2T_of_inner

/-- **Positivity from a Gram identity**, for any family of vectors.

DERIVED: `0` the sign. -/
theorem gram_nonneg (Y : OSDataS) {M : Type} (w : M → Y.H) (K : M → M → ℝ)
    (hin : ∀ P Q, inner ℂ (w P) (w Q) = (K P Q : ℂ)) (s : Finset M) (c : M → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q := by
  set v : Y.H := ∑ P ∈ s, (c P : ℂ) • w P with hv
  have e : inner ℂ v v = ((∑ P ∈ s, ∑ Q ∈ s, c P * c Q * K P Q : ℝ) : ℂ) := by
    simp only [hv, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hin,
      Complex.conj_ofReal]
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  have h0 := inner_self_nonneg (𝕜 := ℂ) (x := v)
  rw [e] at h0
  simpa using h0

#print axioms gram_nonneg

/-- **OS2 on all composites from their link.** DERIVED: no numeral. -/
theorem os2C_of_link (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (C : Composites N)
    {wC : TSepG C.Ix τ → X.base.H} (hL : LinkC hN X C wC) : OS2C hN C τ :=
  fun s c => gram_nonneg X.base wC (kernC hN C τ) (fun P Q => (hL.1 P Q).2) s c

#print axioms os2C_of_link

/-- **A time step keeps the closed span** of a family it maps into itself.

DERIVED: no numeral. -/
theorem dyadic_mem_HLg (Y : OSDataS) {M : Type} (w : M → Y.H) (a : ℝ) (sh : M → M)
    (hsh : ∀ P, w (sh P) = Y.time a (w P)) : ∀ u ∈ HLg Y w, Y.time a u ∈ HLg Y w := by
  intro u hu
  set L : Y.H →L[ℂ] Y.H := Y.time a with hL
  have hS : Submodule.span ℂ (Set.range w) ≤ (HLg Y w).comap (L : Y.H →ₗ[ℂ] Y.H) := by
    rw [Submodule.span_le]
    rintro _ ⟨P, rfl⟩
    show L (w P) ∈ HLg Y w
    rw [hL, ← hsh P]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩)
  have hC : IsClosed (((HLg Y w).comap (L : Y.H →ₗ[ℂ] Y.H) : Submodule ℂ Y.H) : Set Y.H) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  exact Submodule.topologicalClosure_minimal _ hS hC hu

#print axioms dyadic_mem_HLg

/-- **The dyadic shift keeps `HL`.**

DERIVED: no numeral. -/
theorem dyadic_mem_HLs (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (w : TSep τ → X.base.H)
    (hsh : ∀ (m : ℕ) (P : TSep τ), w (shiftT hN τ m P) = X.base.time (dySpacing N m) (w P))
    (m : ℕ) : ∀ u ∈ HLs X w, X.base.time (dySpacing N m) u ∈ HLs X w :=
  dyadic_mem_HLg X.base w _ (shiftT hN τ m) (hsh m)

#print axioms dyadic_mem_HLs

/-- **Iterating one time step** is the time `n a`.

DERIVED: `0` the sign of `a` and the base case. -/
theorem iterate_time (Y : OSDataS) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : Y.H) :
    (Y.time a)^[n] x = Y.time (n * a) x := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, Y.time_zero]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have e : ((n + 1 : ℕ) : ℝ) * a = a + n * a := by push_cast; ring
    rw [e, Y.time_add a (n * a) ha (mul_nonneg (Nat.cast_nonneg n) ha)]
    rfl

#print axioms iterate_time

/-- **The closed span is invariant under every `t ≥ 0`** when the dyadic shifts keep the family:
at `⌊t/a_k⌋ a_k` by the dyadic shifts, and at `t` by strong continuity on `[0, ∞)` and
closedness, `⌊t/a_k⌋ a_k → t`.

DERIVED: `0` the time origin and signs. -/
theorem time_mem_HLg (hN : N ≠ 0) (Y : OSDataS) {M : Type} (w : M → Y.H) (sh : ℕ → M → M)
    (hsh : ∀ (m : ℕ) (P : M), w (sh m P) = Y.time (dySpacing N m) (w P))
    (t : ℝ) (ht : 0 ≤ t) : ∀ u ∈ HLg Y w, Y.time t u ∈ HLg Y w := by
  intro u hu
  set a : ℕ → ℝ := dySpacing N with ha_def
  have ha : ∀ k, 0 < a k := fun k => dySpacing_pos (one_le_of_ne_zero hN) k
  set s : ℕ → ℝ := fun k => (⌊t / a k⌋₊ : ℝ) * a k with hs_def
  have hsle : ∀ k, s k ≤ t := fun k => by
    have h1 := Nat.floor_le (div_nonneg ht (ha k).le)
    exact (le_div_iff₀ (ha k)).mp h1
  have hsge : ∀ k, t - a k ≤ s k := fun k => by
    have h1 := Nat.lt_floor_add_one (t / a k)
    have h2 : t < ((⌊t / a k⌋₊ : ℝ) + 1) * a k := (div_lt_iff₀ (ha k)).mp h1
    show t - a k ≤ (⌊t / a k⌋₊ : ℝ) * a k
    nlinarith
  have hs0 : ∀ k, 0 ≤ s k := fun k => mul_nonneg (Nat.cast_nonneg _) (ha k).le
  have hlim : Tendsto s atTop (𝓝 t) := by
    have hlow : Tendsto (fun k => t - a k) atTop (𝓝 t) := by
      have := (tendsto_const_nhds (x := t)).sub (tendsto_dySpacing N)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hsge hsle
  have hlimW : Tendsto s atTop (𝓝[Set.Ici 0] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall hs0⟩
  have hcont : Tendsto (fun k => Y.time (s k) u) atTop (𝓝 (Y.time t u)) :=
    ((Y.time_cont u) t ht).tendsto.comp hlimW
  have hmem : ∀ k, Y.time (s k) u ∈ HLg Y w := fun k => by
    rw [hs_def, ← iterate_time Y (ha k).le]
    induction ⌊t / a k⌋₊ with
    | zero => exact hu
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact dyadic_mem_HLg Y w (a k) (sh k) (hsh k) _ ih
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hcont
    (Filter.Eventually.of_forall hmem)

#print axioms time_mem_HLg

/-- **`HL` is invariant under every `t ≥ 0`.**

DERIVED: `0` the time origin. -/
theorem time_mem_HLs (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (w : TSep τ → X.base.H)
    (hsh : ∀ (m : ℕ) (P : TSep τ), w (shiftT hN τ m P) = X.base.time (dySpacing N m) (w P))
    (t : ℝ) (ht : 0 ≤ t) : ∀ u ∈ HLs X w, X.base.time t u ∈ HLs X w :=
  time_mem_HLg hN X.base w (shiftT hN τ) hsh t ht

#print axioms time_mem_HLs

/-- **The orthogonal complement of `HL` is invariant too**, so `HL` reduces the semigroup.

DERIVED: `0` the time origin and the vanishing pairing. -/
theorem time_mem_HLs_orth (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (w : TSep τ → X.base.H)
    (hsh : ∀ (m : ℕ) (P : TSep τ), w (shiftT hN τ m P) = X.base.time (dySpacing N m) (w P))
    (t : ℝ) (ht : 0 ≤ t) : ∀ u ∈ (HLs X w)ᗮ, X.base.time t u ∈ (HLs X w)ᗮ := by
  intro u hu v hv
  have hsa := (X.base.time_selfAdjoint t ht).1
  have e : inner ℂ v (X.base.time t u) = inner ℂ (X.base.time t v) u := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hsa.adjoint_eq]
  rw [e]
  exact hu _ (time_mem_HLs hN X w hsh t ht v hv)

#print axioms time_mem_HLs_orth

/-- **The spectral clause on the closed span** of any family the dyadic shifts keep, containing the
vacuum, from the Hamiltonian gap on the whole space.

DERIVED: no numeral. -/
theorem spectralGapOn_of_shift (hN : N ≠ 0) (Y : OSDataS) {M : Type} (w : M → Y.H)
    (hH : HamiltonianGap Y) (sh : ℕ → M → M)
    (hsh : ∀ (m : ℕ) (P : M), w (sh m P) = Y.time (dySpacing N m) (w P)) (e : M)
    (hvac : w e = Y.vac) : SpectralGapOn Y (HLg Y w) :=
  ⟨hH.1, fun t ht => time_mem_HLg hN Y w sh hsh t ht,
    hvac ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_, rfl⟩),
    hH.2.2.1, fun u _ hu => hH.2.2.2.1 u hu, fun u _ hu t ht => Y.time_gap t ht u hu,
    fun t ht u _ hu => hH.2.2.2.2 t ht u hu⟩

#print axioms spectralGapOn_of_shift

/-- **The spectral clause from the link and the Hamiltonian gap.**

DERIVED: no numeral. -/
theorem spectralGapOn_of_link (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (w : TSep τ → X.base.H)
    (hH : HamiltonianGap X.base)
    (hsh : ∀ (m : ℕ) (P : TSep τ), w (shiftT hN τ m P) = X.base.time (dySpacing N m) (w P))
    (hvac : w (emptyT τ) = X.base.vac) : SpectralGapOn X.base (HLs X w) :=
  spectralGapOn_of_shift hN X.base w hH (shiftT hN τ) hsh (emptyT τ) hvac

#print axioms spectralGapOn_of_link

/-- **OS4 from the link and the gap.** With `‖Ω‖ = 1` (`kernT_empty`), `w Q = ⟪Ω, w Q⟫ Ω + u`,
`u ⊥ Ω`, the shifts fix `Ω` and contract `u` by `e^{−Δ n a}`.

DERIVED: `0` the limit of the contracted part; `1` the norm of the vacuum. -/
theorem os4T_of_link (hN : N ≠ 0) (ρ : RenormMix N) (X : OSDataSLinked N D τ r)
    (w : TSep τ → X.base.H)
    (hin : ∀ P Q : TSep τ, inner ℂ (w P) (w Q) = (kernT hN ρ τ P Q : ℂ))
    (hsh : ∀ (m : ℕ) (P : TSep τ), w (shiftT hN τ m P) = X.base.time (dySpacing N m) (w P))
    (hvac : w (emptyT τ) = X.base.vac) : OS4T hN ρ τ := by
  intro m P Q
  set Ω := X.base.vac
  set a := dySpacing N m with ha_def
  have ha : 0 < a := dySpacing_pos (one_le_of_ne_zero hN) m
  have hΩ : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [← hvac, hin, kernT_empty]
    simp
  set c : ℂ := inner ℂ Ω (w Q) with hc
  set u : X.base.H := w Q - c • Ω with hu
  have hu0 : inner ℂ Ω u = 0 := by
    rw [hu, inner_sub_right, inner_smul_right, hΩ, mul_one, hc, sub_self]
  have hiter : ∀ n : ℕ, w ((shiftT hN τ m)^[n] Q) = X.base.time (n * a) (w Q) := fun n => by
    rw [← iterate_time X.base ha.le]
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsh, ih]
  have hsplit : ∀ n : ℕ, inner ℂ (w P) (w ((shiftT hN τ m)^[n] Q))
      = c * inner ℂ (w P) Ω + inner ℂ (w P) (X.base.time (n * a) u) := fun n => by
    have hwQ : w Q = c • Ω + u := by rw [hu]; abel
    have hn : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg n) ha.le
    rw [hiter, hwQ, map_add, map_smul, X.base.time_vac _ hn, inner_add_right, inner_smul_right]
  have hdec : Tendsto (fun n : ℕ => inner ℂ (w P) (X.base.time (n * a) u)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(X.base.gap * a * n))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
      exact tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos X.base.gap_pos ha)
    have hb : Tendsto (fun n : ℕ => ‖w P‖ * (Real.exp (-(X.base.gap * a * n)) * ‖u‖)) atTop
        (𝓝 0) := by
      have := (hexp.mul_const ‖u‖).const_mul ‖w P‖
      simpa using this
    refine squeeze_zero_norm (fun n => ?_) hb
    have hn : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg n) ha.le
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have e : X.base.gap * a * n = X.base.gap * (n * a) := by ring
    rw [e]
    exact X.base.time_gap _ hn u hu0
  have hC : Tendsto (fun n : ℕ => ((kernT hN ρ τ P ((shiftT hN τ m)^[n] Q) : ℝ) : ℂ)) atTop
      (𝓝 (((kernT hN ρ τ P (emptyT τ) * kernT hN ρ τ (emptyT τ) Q : ℝ)) : ℂ)) := by
    have e1 : (fun n : ℕ => ((kernT hN ρ τ P ((shiftT hN τ m)^[n] Q) : ℝ) : ℂ))
        = fun n : ℕ => c * inner ℂ (w P) Ω + inner ℂ (w P) (X.base.time (n * a) u) :=
      funext fun n => by rw [← hin, hsplit]
    have e2 : (((kernT hN ρ τ P (emptyT τ) * kernT hN ρ τ (emptyT τ) Q : ℝ)) : ℂ)
        = c * inner ℂ (w P) Ω + 0 := by
      rw [add_zero, hc, ← hvac, hin, hin]
      push_cast
      ring
    rw [e1, e2]
    exact tendsto_const_nhds.add hdec
  have h2 := (Complex.continuous_re.tendsto _).comp hC
  rw [Complex.ofReal_re] at h2
  exact h2.congr (fun n => by simp)

#print axioms os4T_of_link

/-- **Clustering from a Gram identity and the gap**, for any family the time step `a > 0` keeps,
with `w e = Ω` and `K e e = 1`.

DERIVED: `0` the limit of the contracted part; `1` the norm of the vacuum. -/
theorem cluster_of_gram (Y : OSDataS) {M : Type} (w : M → Y.H) (K : M → M → ℝ)
    (hin : ∀ P Q, inner ℂ (w P) (w Q) = (K P Q : ℂ)) (sh : M → M) {a : ℝ} (ha : 0 < a)
    (hsh : ∀ P, w (sh P) = Y.time a (w P)) (e0 : M) (hvac : w e0 = Y.vac) (hK : K e0 e0 = 1)
    (P Q : M) : Tendsto (fun n : ℕ => K P (sh^[n] Q)) atTop (𝓝 (K P e0 * K e0 Q)) := by
  set Ω := Y.vac
  have hΩ : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [← hvac, hin, hK]
    simp
  set c : ℂ := inner ℂ Ω (w Q) with hc
  set u : Y.H := w Q - c • Ω with hu
  have hu0 : inner ℂ Ω u = 0 := by
    rw [hu, inner_sub_right, inner_smul_right, hΩ, mul_one, hc, sub_self]
  have hiter : ∀ n : ℕ, w (sh^[n] Q) = Y.time (n * a) (w Q) := fun n => by
    rw [← iterate_time Y ha.le]
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsh, ih]
  have hsplit : ∀ n : ℕ, inner ℂ (w P) (w (sh^[n] Q))
      = c * inner ℂ (w P) Ω + inner ℂ (w P) (Y.time (n * a) u) := fun n => by
    have hwQ : w Q = c • Ω + u := by rw [hu]; abel
    have hn : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg n) ha.le
    rw [hiter, hwQ, map_add, map_smul, Y.time_vac _ hn, inner_add_right, inner_smul_right]
  have hdec : Tendsto (fun n : ℕ => inner ℂ (w P) (Y.time (n * a) u)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(Y.gap * a * n))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
      exact tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos Y.gap_pos ha)
    have hb : Tendsto (fun n : ℕ => ‖w P‖ * (Real.exp (-(Y.gap * a * n)) * ‖u‖)) atTop
        (𝓝 0) := by
      have := (hexp.mul_const ‖u‖).const_mul ‖w P‖
      simpa using this
    refine squeeze_zero_norm (fun n => ?_) hb
    have hn : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg n) ha.le
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have e : Y.gap * a * n = Y.gap * (n * a) := by ring
    rw [e]
    exact Y.time_gap _ hn u hu0
  have hC : Tendsto (fun n : ℕ => ((K P (sh^[n] Q) : ℝ) : ℂ)) atTop
      (𝓝 (((K P e0 * K e0 Q : ℝ)) : ℂ)) := by
    have e1 : (fun n : ℕ => ((K P (sh^[n] Q) : ℝ) : ℂ))
        = fun n : ℕ => c * inner ℂ (w P) Ω + inner ℂ (w P) (Y.time (n * a) u) :=
      funext fun n => by rw [← hin, hsplit]
    have e2 : (((K P e0 * K e0 Q : ℝ)) : ℂ) = c * inner ℂ (w P) Ω + 0 := by
      rw [add_zero, hc, ← hvac, hin, hin]
      push_cast
      ring
    rw [e1, e2]
    exact tendsto_const_nhds.add hdec
  have h2 := (Complex.continuous_re.tendsto _).comp hC
  rw [Complex.ofReal_re] at h2
  exact h2.congr (fun n => by simp)

#print axioms cluster_of_gram

/-- **OS4 on all composites from their link and the gap.** DERIVED: no numeral. -/
theorem os4C_of_link (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (C : Composites N)
    {wC : TSepG C.Ix τ → X.base.H} (hL : LinkC hN X C wC) : OS4C hN C τ :=
  fun m P Q => cluster_of_gram X.base wC (kernC hN C τ) (fun P Q => (hL.1 P Q).2)
    (shiftT hN τ m) (dySpacing_pos (one_le_of_ne_zero hN) m) (hL.2.1 m) (emptyG C.Ix τ) hL.2.2
    (kernC_empty hN C τ) P Q

#print axioms os4C_of_link

/-- **The gap on the space of all local fields** from their link and the Hamiltonian gap.

DERIVED: no numeral. -/
theorem spectralGapOn_HLC (hN : N ≠ 0) (X : OSDataSLinked N D τ r) (C : Composites N)
    {wC : TSepG C.Ix τ → X.base.H} (hH : HamiltonianGap X.base) (hL : LinkC hN X C wC) :
    SpectralGapOn X.base (HLC X wC) :=
  spectralGapOn_of_shift hN X.base wC hH (shiftT hN τ) hL.2.1 (emptyG C.Ix τ) hL.2.2

#print axioms spectralGapOn_HLC

/-- **A non-zero vector of `HLC` orthogonal to the vacuum**, from one of `HL ≤ HLC`.

DERIVED: `0` the vanishing pairing and the zero vector. -/
theorem nontrivial_HLC (ρ : RenormMix N) (X : OSDataSLinked N D τ r) (C : Composites N)
    {w : TSep τ → X.base.H} {wC : TSepG C.Ix τ → X.base.H} (hT : TIn ρ C X w wC)
    (hnt : ∃ u ∈ HLs X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0) :
    ∃ u ∈ HLC X wC, inner ℂ X.base.vac u = 0 ∧ u ≠ 0 := by
  obtain ⟨_, _, _, hle⟩ := hT
  obtain ⟨u, hu, h0, hne⟩ := hnt
  exact ⟨u, hle hu, h0, hne⟩

#print axioms nontrivial_HLC

/-- **The single monomials span a dense subspace of a GNS completion.** For a reflection form on
finite real combinations `α →₀ ℝ`, the classes of the pairs `(single a 1, 0)` have closed complex
span the whole completion: a real combination is a sum of real multiples of single monomials, the
imaginary component is `i` times a real one, and the pre-Hilbert space is dense in its completion.

DERIVED: `1` the coefficient; `0` the imaginary component. -/
theorem span_single_dense {α : Type*} (P : Transfer.ReflForm (α →₀ ℝ)) :
    (Submodule.span ℂ (Set.range fun a : α =>
      ((GNSHilbert.Pre.ofPair P (Finsupp.single a 1) 0 : GNSHilbert.Pre P)
        : GNSHilbert.H P))).topologicalClosure = ⊤ := by
  set S := Submodule.span ℂ (Set.range fun a : α =>
      ((GNSHilbert.Pre.ofPair P (Finsupp.single a 1) 0 : GNSHilbert.Pre P) : GNSHilbert.H P))
  have hreal : ∀ x : α →₀ ℝ,
      ((GNSHilbert.Pre.ofPair P x 0 : GNSHilbert.Pre P) : GNSHilbert.H P) ∈ S := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero =>
      have e : (GNSHilbert.Pre.ofPair P (0 : α →₀ ℝ) 0 : GNSHilbert.Pre P) = 0 :=
        GNSHilbert.Pre.ext rfl rfl
      rw [e, UniformSpace.Completion.coe_zero]
      exact S.zero_mem
    | add x y hx hy =>
      have e : (GNSHilbert.Pre.ofPair P (x + y) 0 : GNSHilbert.Pre P)
          = GNSHilbert.Pre.ofPair P x 0 + GNSHilbert.Pre.ofPair P y 0 :=
        GNSHilbert.Pre.ext rfl (by simp)
      rw [e, UniformSpace.Completion.coe_add]
      exact S.add_mem hx hy
    | single a b =>
      have e : (GNSHilbert.Pre.ofPair P (Finsupp.single a b) 0 : GNSHilbert.Pre P)
          = (b : ℂ) • GNSHilbert.Pre.ofPair P (Finsupp.single a 1) 0 :=
        GNSHilbert.Pre.ext (by rw [GNSHilbert.Pre.smul_fst]; simp)
          (by rw [GNSHilbert.Pre.smul_snd]; simp)
      rw [e, UniformSpace.Completion.coe_smul]
      exact S.smul_mem _ (Submodule.subset_span ⟨a, rfl⟩)
  have hall : ∀ z : GNSHilbert.Pre P, ((z : GNSHilbert.Pre P) : GNSHilbert.H P) ∈ S := by
    intro z
    have e : z = GNSHilbert.Pre.ofPair P (z : (α →₀ ℝ) × (α →₀ ℝ)).1 0
        + Complex.I • GNSHilbert.Pre.ofPair P (z : (α →₀ ℝ) × (α →₀ ℝ)).2 0 :=
      GNSHilbert.Pre.ext (by simp) (by simp)
    rw [e, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul]
    exact S.add_mem (hreal _) (S.smul_mem _ (hreal _))
  refine eq_top_iff.mpr (fun h _ => ?_)
  have hsub : Set.range (fun z : GNSHilbert.Pre P => ((z : GNSHilbert.Pre P) : GNSHilbert.H P))
      ⊆ (S.topologicalClosure : Set (GNSHilbert.H P)) := by
    rintro _ ⟨z, rfl⟩
    exact S.le_topologicalClosure (hall z)
  have hcl := closure_minimal hsub S.isClosed_topologicalClosure
  rw [UniformSpace.Completion.denseRange_coe.closure_range] at hcl
  exact hcl (Set.mem_univ h)

#print axioms span_single_dense

/-- **The flowed reconstruction is generated by its monomials**: the vectors `gvecT P` of the
margin monomials of the energy density's flowed reconstruction have the observer's flowed Schwinger
functions of the reflected pairs as inner products (`ContinuumFlow.flow_reconstruction`), are carried
by `timeT (a_m)` to the vectors of the shifted monomials (`timeT_dyadic` at `n = 1`, `stepT_gvecT`),
and have closed span all of `FlowH` (`span_single_dense`). With `v Q = cvec Q` by definition, this
is `ObsGen` at every observer whose Hilbert space is `FlowH`.

DERIVED: `0` the reference step; `1` one step. -/
theorem obsGen_flow (hN : N ≠ 0) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
    (hpos : (energy0 W D hD).PosPreserving τ r) :
    (∀ P Q : MarginMono N τ r,
      inner ℂ (gvecT hN (energy0 W D hD) hB τ hpos P) (gvecT hN (energy0 W D hD) hB τ hpos Q)
        = (contSF hN (energy0 W D hD) (pairFam τ P.1 Q.1) : ℂ))
    ∧ (∀ (m : ℕ) (P Q : MarginMono N τ r),
      Q.1 = ⟨P.1.1, fun i => ((P.1.2 i).1, (P.1.2 i).2.translate (timeVec N m τ 1))⟩ →
        gvecT hN (energy0 W D hD) hB τ hpos Q
          = timeT hN (energy0 W D hD) hB τ hpos (dySpacing N m)
              (gvecT hN (energy0 W D hD) hB τ hpos P))
    ∧ (Submodule.span ℂ (Set.range (gvecT hN (energy0 W D hD) hB τ hpos))).topologicalClosure
      = ⊤ := by
  refine ⟨fun P Q => (flow_reconstruction hN (energy0 W D hD) hB τ hpos 0).2 P Q,
    fun m P Q hQ => ?_, span_single_dense _⟩
  have e : Q = MarginMono.shift hN τ m P := Subtype.ext hQ
  have ht := timeT_dyadic hN (energy0 W D hD) hB τ hpos m 1
  rw [Nat.cast_one, one_mul, pow_one] at ht
  rw [e, ht, stepT_gvecT]

#print axioms obsGen_flow

/-- **`ObsGen` at the observer** `observerOSDataSLinked`: `v = gvecT` (`obsGen_flow`).

DERIVED: `0` the excluded colour count and the reference step; `1` the top of `ρ`; `4` in `Fin 4`
the spacetime dimension. -/
theorem obsGen_observer (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O) {t C : ℝ}
    (ht : 0 < t) (hC0 : 0 ≤ C) (hU : ClassMoments hN W D t C)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : UnitCubeExpBound hN W O) (τ : Fin 4)
    {r : ℝ} (hphys : (energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (energy0 W D hD)
      (uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (energy0 W D hD) τ r) :
    ObsGen hN W D hD
      (observerOSDataSLinked hN W hD hpos hcube ht hC0 hU hO h τ hphys m0 hL hρ0 hρ1 hg hNT) :=
  ⟨gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ
      (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ), fun _ => rfl,
    obsGen_flow hN W D hD (uniformBoundF_energy0 hN W D hD hpos hcube) τ
      (Flow.posPreserving_of_physRange hN (energy0 W D hD) hphys τ)⟩

#print axioms obsGen_observer

/-- **What transfers, at one witness.** Proved here: OS3 (`os3T`, `os3C`), OS2 (`os2T_of_inner`,
`os2C_of_link`), the spectral clauses (`spectralGapOn_of_link`, `spectralGapOn_HLC`), OS4
(`os4T_of_link`, `os4C_of_link`), `AFShortDistance` (`afShortDistance_of_coefficient`), and the
non-zero vector of `HLC` (`nontrivial_HLC`).

The open inputs: the functional `hSM`; the Hamiltonian gap `hH`; the Riemann symmetries `hRie`;
the scalar tie `hTie`; existence of the limit `hConv`; OS0, the kernel bound `h0`; OS1 `h1`;
covariance `hCov`; the link `hL`; a non-zero vector of `HL` orthogonal to the vacuum `hnt`; the
two-point kernel `hK`; the asymptotic-freedom coefficient `hAF`; the non-zero three-point function
`hNG`; the non-degenerate channels `hND`; the convergence of the aperture's functional `hAC`; the
channel ties with the topological normalisation `hCT`; the Ward identity `hWard`; the composites
clauses `hCD` (classical ties, coverage, triangular renormalisation, rotation representation); the
analytic clauses on all composites `hCO` (existence, OS0, OS1, covariance); the link of all
composites `hLC`; the tensor among the composites `hTI`; the observer's generation of the Hilbert
space `hGen`.

DERIVED: `2` the least colour count; `0` the vanishing pairing and the zero vector. -/
theorem clayData_of_link (hN2 : 2 ≤ N) (W : ConfFlow N) (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (G : ℝ → ℝ) (w : TSep τ → X.base.H)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      X.SM O g = schwSFM (ne_zero_of_two_le hN2) W D hD O g)
    (hH : HamiltonianGap X.base) (hRie : ρ.Riemann) (hTie : ScalarTie ρ X.O)
    (hConv : SepConv (ne_zero_of_two_le hN2) ρ) (h0 : OS0Sep (ne_zero_of_two_le hN2) ρ)
    (h1 : OS1Sep (ne_zero_of_two_le hN2) ρ) (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hL : LinkTS (ne_zero_of_two_le hN2) W D hD X ρ w)
    (hnt : ∃ u ∈ HLs X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hND : TensorNondeg (ne_zero_of_two_le hN2) ρ)
    (hAC : ApertureConv (ne_zero_of_two_le hN2) W D hD)
    (C : Composites N) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTie ρ Mb Z ∧ TopNorm N Z)
    (hWard : WardT (ne_zero_of_two_le hN2) ρ) (hCD : CompData C)
    (hCO : CompOS (ne_zero_of_two_le hN2) C) (hLC : LinkC (ne_zero_of_two_le hN2) X C wC)
    (hTI : TIn ρ C X w wC) (hGen : ObsGen (ne_zero_of_two_le hN2) W D hD X) :
    ClayData hN2 W D hD τ r X ρ G w C wC :=
  have hin : ∀ P Q : TSep τ, inner ℂ (w P) (w Q) = (kernT (ne_zero_of_two_le hN2) ρ τ P Q : ℂ) :=
    fun P Q => (hL.1 P Q).2
  ⟨hSM, hH, hRie, hTie, hConv, h0, h1, hCov, os3T _ ρ, hL, os2T_of_inner _ ρ X hin,
    spectralGapOn_of_link _ X w hH hL.2.1 hL.2.2.1, os4T_of_link _ ρ X w hin hL.2.1 hL.2.2.1,
    hnt, hK, hAF, afShortDistance_of_coefficient hN2 hAF, hNG, hND, hAC, hCT, hWard, hCD, hCO,
    os3C _ C, hLC, os2C_of_link _ X C hLC, os4C_of_link _ X C hLC, hTI,
    spectralGapOn_HLC _ X C hH hLC, nontrivial_HLC ρ X C hTI hnt, hGen⟩

#print axioms clayData_of_link

/-- **`ClayStatementAt` from the inputs of `clayData_of_link`.**

DERIVED: `2` the least colour count; `0` the vanishing pairing and the zero vector. -/
theorem clayStatementAt_of_link (hN2 : 2 ≤ N) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) {τ : Fin 4} {r : ℝ}
    (X : OSDataSLinked N D τ r) (ρ : RenormMix N) (G : ℝ → ℝ) (w : TSep τ → X.base.H)
    (hSM : ∀ (ι : Type) [Fintype ι] (O : ι → LField (MassGap.SUN.SU N)) (g : ι → Decaying),
      X.SM O g = schwSFM (ne_zero_of_two_le hN2) W D hD O g)
    (hH : HamiltonianGap X.base) (hRie : ρ.Riemann) (hTie : ScalarTie ρ X.O)
    (hConv : SepConv (ne_zero_of_two_le hN2) ρ) (h0 : OS0Sep (ne_zero_of_two_le hN2) ρ)
    (h1 : OS1Sep (ne_zero_of_two_le hN2) ρ) (hCov : TensorCov (ne_zero_of_two_le hN2) ρ)
    (hL : LinkTS (ne_zero_of_two_le hN2) W D hD X ρ w)
    (hnt : ∃ u ∈ HLs X w, inner ℂ X.base.vac u = 0 ∧ u ≠ 0)
    (hK : TwoPointKernel (ne_zero_of_two_le hN2) ρ G) (hAF : AFCoefficient N G)
    (hNG : NonGaussianT (ne_zero_of_two_le hN2) ρ) (hND : TensorNondeg (ne_zero_of_two_le hN2) ρ)
    (hAC : ApertureConv (ne_zero_of_two_le hN2) W D hD)
    (C : Composites N) (wC : TSepG C.Ix τ → X.base.H)
    (hCT : ∃ (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ), ChannelTie ρ Mb Z ∧ TopNorm N Z)
    (hWard : WardT (ne_zero_of_two_le hN2) ρ) (hCD : CompData C)
    (hCO : CompOS (ne_zero_of_two_le hN2) C) (hLC : LinkC (ne_zero_of_two_le hN2) X C wC)
    (hTI : TIn ρ C X w wC) (hGen : ObsGen (ne_zero_of_two_le hN2) W D hD X) :
    ClayStatementAt hN2 W D hD :=
  ⟨τ, r, X, ρ, G, w, C, wC,
    clayData_of_link hN2 W D hD X ρ G w hSM hH hRie hTie hConv h0 h1 hCov hL hnt hK hAF hNG hND
      hAC C wC hCT hWard hCD hCO hLC hTI hGen,
    trivial⟩

#print axioms clayStatementAt_of_link

end Transfer

/-! ## 8. Sanity: the statement excludes `Z = 0` and every free theory -/

section Sanity

/-- With the trace channel of the mixing zero at every step, every non-empty trace reading is `0`.

DERIVED: `0` the value and the first index. -/
theorem contTr_eq_zero (hN : N ≠ 0) (ρ : RenormMix N) (hz : ∀ k b, mixC ρ k trC b = 0) {n : ℕ}
    (hn : 0 < n) (u : Fin n → TestFn) : contTr hN ρ u = 0 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have e : (fun k => latT hN ρ k (fun i => (trC, u i))) = fun _ => (0 : ℝ) := by
    funext k
    unfold latT
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n)) (hz k _), zero_mul]
  unfold contTr contT
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

#print axioms contTr_eq_zero

/-- **`Z = 0` on the trace is excluded**: then every connected three-point function of the trace
vanishes, against `NonGaussianT`.

DERIVED: `0` the excluded value; `1`, `2`, `3` the orders. -/
theorem not_nonGaussian_of_trace_zero (hN : N ≠ 0) (ρ : RenormMix N)
    (hz : ∀ k b, mixC ρ k trC b = 0) : ¬ NonGaussianT hN ρ := by
  rintro ⟨f, g, h, -, -, -, -, hne⟩
  apply hne
  unfold cum3T
  rw [contTr_eq_zero hN ρ hz (by norm_num), contTr_eq_zero hN ρ hz (by norm_num),
    contTr_eq_zero hN ρ hz (by norm_num), contTr_eq_zero hN ρ hz (by norm_num),
    contTr_eq_zero hN ρ hz (by norm_num), contTr_eq_zero hN ρ hz (by norm_num),
    contTr_eq_zero hN ρ hz (by norm_num)]
  ring

#print axioms not_nonGaussian_of_trace_zero

/-- **Non-vacuity: no witness has the trace channel zero at every step.**

DERIVED: `2` the least colour count. -/
theorem not_trace_zero {hN2 : 2 ≤ N} {W : ConfFlow N} {D : Set (LField (MassGap.SUN.SU N))}
    {hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D} {τ : Fin 4} {r : ℝ}
    {X : OSDataSLinked N D τ r} {ρ : RenormMix N} {G : ℝ → ℝ} {w : TSep τ → X.base.H}
    {C : Composites N} {wC : TSepG C.Ix τ → X.base.H}
    (h : ClayData hN2 W D hD τ r X ρ G w C wC) : ¬ ∀ k b, mixC ρ k trC b = 0 :=
  fun hz => not_nonGaussian_of_trace_zero _ ρ hz h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

#print axioms not_trace_zero

/-- **Non-vacuity: the zero mixing is excluded.**

DERIVED: `0` the mixing. -/
theorem not_mix_zero {hN2 : 2 ≤ N} {W : ConfFlow N} {D : Set (LField (MassGap.SUN.SU N))}
    {hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D} {τ : Fin 4} {r : ℝ}
    {X : OSDataSLinked N D τ r} {ρ : RenormMix N} {G : ℝ → ℝ} {w : TSep τ → X.base.H}
    {C : Composites N} {wC : TSepG C.Ix τ → X.base.H}
    (h : ClayData hN2 W D hD τ r X ρ G w C wC) : ¬ ∀ k α b, ρ.M k α b = 0 :=
  fun hz => not_trace_zero h (fun k b => by simp [mixC, hz])

#print axioms not_mix_zero

/-- **No free theory**: the trace two-point kernel of a witness is not that of a free composite,
massless or massive (`ShortDistanceY.FreeScalingForm`), since it is asymptotically free.

DERIVED: no numeral. -/
theorem not_freeScalingForm {hN2 : 2 ≤ N} {W : ConfFlow N} {D : Set (LField (MassGap.SUN.SU N))}
    {hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D} {τ : Fin 4} {r : ℝ}
    {X : OSDataSLinked N D τ r} {ρ : RenormMix N} {G : ℝ → ℝ} {w : TSep τ → X.base.H}
    {C : Composites N} {wC : TSepG C.Ix τ → X.base.H}
    (h : ClayData hN2 W D hD τ r X ρ G w C wC) : ¬ ShortDistanceY.FreeScalingForm G :=
  fun hF => ShortDistanceY.not_af_of_scalingForm hF h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

#print axioms not_freeScalingForm

/-- **Not the free massless field**: the kernel is not `C/r⁸`, `C ≠ 0`.

DERIVED: `0` the excluded constant. -/
theorem kernel_ne_freeMassless {hN2 : 2 ≤ N} {W : ConfFlow N}
    {D : Set (LField (MassGap.SUN.SU N))}
    {hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D} {τ : Fin 4} {r : ℝ}
    {X : OSDataSLinked N D τ r} {ρ : RenormMix N} {G : ℝ → ℝ} {w : TSep τ → X.base.H}
    {Cs : Composites N} {wC : TSepG Cs.Ix τ → X.base.H}
    (h : ClayData hN2 W D hD τ r X ρ G w Cs wC) {C : ℝ} (hC : C ≠ 0) :
    G ≠ ShortDistanceY.freeMassless C := by
  rintro rfl
  exact ShortDistanceY.not_af_freeMassless hC h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

#print axioms kernel_ne_freeMassless

end Sanity

end MassGap.ClayStatement

end
