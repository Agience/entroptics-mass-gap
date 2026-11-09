import Mathlib
import MassGap.ApertureModes

/-!
# MassGap.ApertureCount — the measured count turns one variance into every moment

The author: an observer sees only inside its aperture; the signal sets its own aperture; a fixed, finite amount
of information per aperture at every zoom; the fields settle as the aperture shrinks. `ApertureModes`
measures the count (`apDim`, the entropy-effective number of modes of the screen's Gram spectrum) but uses it
only as a factor that its own settling clause inserts, so that the count there carries no weight. This
module states the mechanism so that the count does the work: the hypotheses bound each mode relative to its
own variance and bound the reading's variance alone, and the count is what converts that one second moment
into every even moment. Declarations are in the namespace `MassGap.ApertureCount`.

## 1. The modes of a screen (proved)

For a state `ν` and a finite screen `F : ι → C(X, ℝ)`, `gram ν F` is real symmetric
(`ApertureModes.gram_isHermitian`). Its spectral decomposition (Mathlib's `eigenvectorUnitary`, columns the
`eigenvectorBasis`) gives

* `evec ν F y α` (the eigenvector matrix), `eig ν F α` (the eigenvalues), and the modes
  `mode ν F α = ∑_y evec y α • F y`;
* `state_mode_mul`: `ν(mode α · mode β) = eig α` if `α = β`, `0` otherwise (the modes are uncorrelated);
  `eig_eq`: `eig α = ν(mode α ²)`; `eig_nonneg`: the Gram matrix is positive semidefinite;
* `sum_evec_smul_mode`: every screen reading is exactly `F y = ∑_α evec y α • mode α`;
* `sum_eig`: `∑_α eig α = ∑_y ν(F y ²)` (the trace);
* `IsUnitEig G λ v`: `v` is a unit vector (`∑_y v y² = 1`) with `G v = λ v`; `evec_isUnitEig`: every column
  of the eigenvector matrix is a unit eigenvector of the Gram matrix at its eigenvalue.

When eigenvalues are degenerate (on the box, the cubic symmetry makes them so) the eigenvector matrix is
Mathlib's choice. The per-mode hypothesis (H1, §6) does not depend on that choice: it bounds the mode
`∑_y v y • F y` of every unit vector `v` in every eigenspace, and `evec_isUnitEig` specializes it to the
columns the proofs use.

## 2. Minkowski through the modes (proved)

* `state_pow_comb_le`: if every mode has `ν(e_α^{2p}) ≤ K λ_α^p`, then
  `ν((∑ c_α e_α)^{2p}) ≤ K (∑ |c_α| √λ_α)^{2p}` (pointwise Jensen with weights `|c_α|√λ_α + ε`, then
  `ε → 0⁺`).
* `state_pow_le_renyi`: if every screen reading has the moments of one observable `G₀` (translation), and
  every mode is hypercontractive relative to its own variance, `ν(mode α^{2p}) ≤ K eig α^p`, then
  `ν(G₀^{2p}) ≤ K (R · ν(G₀²))^p`, with `R = spRenyi (eig ν F) = (∑_α √p_α)²` the Rényi-½ count of the
  normalized spectrum `p_α = eig α / ∑ eig`. One site's coefficient sum is at most the mean over the screen,
  `∑_y |evec y α| ≤ √n` (Cauchy–Schwarz on a unit column), and `∑ eig = n ν(G₀²)`; so the volume `n` of the
  screen cancels and the bound is relative to the reading's own second moment.

The count that enters is the Rényi-½ count `R`, not `exp H`. `R ≥ exp H` always (Rényi entropies decrease
with the order; not used here).

## 3. Shannon to Rényi (proved)

The measured quantity stays the entroptics read: `apDim = exp H` of the normalized Gram spectrum
(`ApertureModes.spDim`). The Gram is connected (`msFlow` subtracts the state mean), so the matching read is
the centred one: `entroptics.reads.axis_spectrum` (the correlation eigenvalues of the screen after
`_centred`) read through `_fill_of` by `phi_T` / `phi_F` (`entroptics/src/entroptics/reads.py`, lines
~378–427), the fill fraction `2^H / n`; the count is `n · phi_T` (`2^H` in bits is `exp H` in nats). On a
translation-invariant screen every diagonal entry of the Gram is the same (`state_screen_pow`), so the
correlation spectrum normalized is the Gram's. `entroptics.reads.phi` (lines ~97–138) reads the raw block
uncentred and is not this read. On a spectrum with no power `_fill_of` returns NaN; `spDim` returns `1`.

* `levelCount w a i`: the number of modes with `p_α > a^{2(i+1)}`, the occupation of the spectrum above the
  `i`-th level of a geometric ladder.
* `sqrt_le_tsum_level` (layer cake): `√x ≤ ∑_i [x > a^{2(i+1)}] a^i (1 − a)` on `[0, 1]`.
* `spRenyi_le_of_levels`: if the level counts grow at most polynomially in units of the measured count,
  `levelCount w a i ≤ c · exp H · (i + 1)^r`, then `R ≤ (c · exp H · (1 − a) · ∑_i (i + 1)^r a^i)²`. The
  decay is stated in the spectrum's own units: the ladder is in `p`, the count of each rung in `exp H`.
  The free flowed spectrum meets the hypothesis (`FreeLevels.free_h3_local`): for `w_k e^{−2t μ_k}` on the
  Dirichlet lattice box (`μ_k` the lattice Laplacian levels, `FreeLevels.phat_eigen`), with the top weight
  at the lowest mode and a local weight ratio `log(w(k₀)/w(k)) ≤ κ (u_k − u_{k₀})`,
  `levelCount ≤ π^d e (1 − 2d(1 + κ) log a)^{d/2} · exp H · (i + 1)^{d/2}` and `R ≤ A_κ² e² exp H`, with
  `r = 2` in `d = 4` and no constant depending on the zoom `K`. The constants do depend on `τ`, so they
  are uniform across apertures only while the flow time relative to the aperture stays at `2t/L² ≥ τ`; a
  flow time fixed in lattice units has `2t/L² → 0` and is not covered. The massless propagator `1/μ` has
  `κ = 1/(4dτ)` at `2t/L² ≥ τ` (`FreeLevels.propagator_local`, `FreeLevels.free_h3_propagator`), while its
  ratio over all modes grows like `K²` (`FreeLevels.propagator_global_unbounded`).
  `FreeLevels.h3_of_freeScreen` gives this clause from `FreeLevels.FreeScreenSpectrum` (the screen spectrum
  is such a box spectrum); the composite channels are not of this form.
* `spRenyi_unbounded_at_bounded_spDim`: Shannon alone does not control `R`. For every `B` there is a
  spectrum with `exp H ≤ e²` and `R ≥ B` (`p₁ = 1 − ε`, `ε = 1/log m` spread over `m` modes:
  `H ≤ 1 + ε log m = 2` and `R ≥ m ε = m / log m`).
* `spRenyi_const`: `n` equal modes have `R = n`.

## 4. The load-bearing test (proved)

`cubeState m` is the uniform state on `{±1}^m`; the `2^m` Walsh characters `walsh m S` are its modes:

* `cube_walsh_mul`: they are orthonormal (`ν(χ_S χ_T) = δ_{ST}`): their Gram matrix is the identity, every
  mode uncorrelated with variance `1`;
* `cube_walsh_pow`: every mode is hypercontractive with constant `1` at every order:
  `ν(χ_S^{2p}) = ν(χ_S²)^p` — the per-mode bound of `state_pow_le_renyi` holds in the Walsh basis, uniformly
  in `m`;
* `cube_four`: the reading `∑_S χ_S` has `ν(F⁴) = 2^m ν(F²)²`;
* `no_uniform_fourth`: no `K` gives `ν(F⁴) ≤ K ν(F²)²` for every `m`.

So per-mode hypercontractivity in one basis and a variance bound do not give the higher moments uniformly;
the factor that grows is the count (`2^m` modes of equal weight, `R = 2^m`), and replacing the count by `1`
gives a false bound. In `state_pow_le_renyi` the count bound (H3) is what closes it. The spectrum here is one
eigenvalue `1` of multiplicity `2^m`, so the reading normalized, `2^{−m/2} ∑_S χ_S`, is itself a unit vector
of that eigenspace: the basis-free H1 of §6 asks the bound of it too, and its fourth moment is `2^m`, so no
one `C` meets that H1 on this test for every `m` (`cube_four`; the corollary is not stated in Lean).

The test for the basis-free H1 weights the characters so that every eigenspace is one-dimensional:

* `wt m i = exp(−2^i / 2^{m+1}) ∈ [1/2, 1]` (`wt_bounds`), `cw m S = ∏_{i ∈ S} wt m i`, the screen
  `wScreen m S = c_S χ_S` and the reading `wRead m = ∑_S c_S χ_S = ∏_i (1 + t_i xᵢ)` (`wRead_apply`);
* `wgram`: the Gram matrix is diagonal with entries `c_S²`; `cw_sq_injective`: they are distinct
  (`c_S² = exp(−∑_{i ∈ S} 2^i / 2^m)`, and the binary expansion is injective);
* `isUnitEig_diag`: a diagonal Gram matrix with distinct entries has only the unit eigenvectors `±` a
  coordinate vector; so `wcube_unitEig_pow`: every unit eigenvector's mode has `ν(e^{2p}) = λ^p`, and
  `wcube_H1`: the basis-free H1 holds with `C = 1` at every order, every Wick exponent and every `m`;
* `wcube_pow`: `ν(F^q) = 2^{−m} ∏_i ((1 − t_i)^q + (1 + t_i)^q)`; `factor_le`: on `t ∈ [1/2, 1]` each
  coordinate's fourth-moment factor is at least `¾` of its squared second-moment factor; so `wcube_four_ge`:
  `ν(F⁴) ≥ (3/2)^m ν(F²)²`;
* `no_uniform_fourth_nondeg`: no `K` gives `ν(F⁴) ≤ K ν(F²)²` for every `m`.

So the basis-free H1 and a variance bound do not give the higher moments uniformly either: without a bound
on the count, the fourth moment relative to the squared variance grows like `(3/2)^m`.

## 5. The screen and the aperture (proved, with what is not)

`screen_readsOn`: the screen reading at the box site `y` reads on the translate by `y` of the flow-range
aperture (`ApertureModes.aperture`). The screen is the observer's box `{0, …, L − 1}⁴`, `L = ⌈s/a_k⌉`, widened
by the flow's lattice range `(Wf s).range k` around the channel's support. `ConfFlow` carries no relation
between its range and `s / a_k`, so that the flow range is at most the box side is not stated; the screen's
reach is the box plus the range.

## 6. The mechanism and the derivation

**`ApertureCountAt b₀ z b Wf`**: one `u > 0` and noise exponents `γ`, `γP` with

* (H1, per mode, scale-free, basis-free) one `C ≥ 0` with, at every aperture `s ∈ (0, b]`, eventually in the
  step, for every channel, order `2p`, eigenvalue `λ` of the screen's Gram matrix and unit vector `v` in its
  eigenspace: `ν((∑_y v y • F_y)^{2p}) ≤ ((2p)!)^{wickIx j} (C λ)^p` — no noise, no scale, no choice of
  basis;
* (H2, one second moment) every channel's variance is set by the running coupling at the aperture:
  `ν(msFlow²) ≤ (σⱼ ḡ²(s)^{κⱼ} / s^{d_j})²`; at the observer's own aperture `b`, every plaquette reading has
  variance at most `σP²` and the flowed plaquette mean within `E a_k⁴`;
* (H3, the measured count along the zoom) one `D`, ladder `a ∈ (0, 1)`, `c ≥ 0`, `r` with, at every aperture,
  eventually in the step and for every channel, `apDim ≤ D` and `levelCount ≤ c · apDim · (i + 1)^r`;
* (af) the trace kernel settles onto the tree value times `ḡ²(r)²` (as in `ZoomFree`).

`apertureOneAt_of_count`: `ApertureCountAt` gives `ZoomFree.ApertureOneAt` at noise
`√(max(C R̄, 1)) σⱼ`, `R̄ = (c D (1 − a) ∑ (i + 1)^r a^i)²`: H3 bounds `R` (§3), §2 turns H1 and H2 into every
even moment. `substrateCoreCL_of_apertureCount` and the capstone `clayStatementOf_of_apertureCount` follow
through `ZoomFree`'s chain.

## 7. The band limit (argued)

With `t ∝ s²` the flowed screen's normalized spectrum is a function of `s p` alone (the aperture units), so
the fraction of the reading's power outside the first `M` modes, `ε(M) = ∑_{α > M} p_α` (the
screen-averaged relative remainder `∑_y ν((F_y − P_M F_y)²) / ∑_y ν(F_y²)`), is the same at every zoom; for
`e^{−2tp²}` in `d = 4` it falls like `exp(−κ₀ √M)` (`κ₀` a positive constant of the heat kernel, not H3's
`c`) in the number of modes and like `e^{−2(i+1)}` in the level
`i`: argued, not proved here. The remainder is relative to the reading's own second moment, never a sup norm.

## 8. What is assumed

H1–H3 and (af) are hypotheses. The Wick factor in H1 is needed: a Gaussian mode has
`ν(e^{2p}) = (2p − 1)!! λ^p`, and the double factorial outgrows every `C^p`, so no bound `C^p λ^p` holds at
`wickIx = 0`. On the compact product of two-point spins the finite-chaos bound is proved, uniformly in the
number of spins (`ModeHyper.bonami`: `ν(f^{2p}) ≤ (2p − 1)^{pq} ν(f²)^p` for degree `q`), H1's form follows
with `C = e^{2 wickIx j}` for readings of degree `q ≤ d_j / 2` (`ModeHyper.cube_H1_channel`), and the Wick
factor is needed already in degree `1` (`ModeHyper.wick_needed`).

The free field does not meet H1 as stated (argued, not proved). H1 asks one `C` for every channel of `MIx`,
and the canonical dimensions of `MIx` are unbounded (`BulkBound.cdim_mono`: `d = 4(n + 1)`). For a free
reading of chaos order `q = 2 wickIx j` (a channel with `d_j ≡ 0 mod 4` of degree `d_j / 2`) the least `C`
over all orders is about `(e/2)^q / √2` (Stirling on `(2pq − 1)!! / ((2q − 1)!!)^p` against `((2p)!)^{q/2}`),
so no single `C` covers the tower; `C_j = e^{2 wickIx j}` is what the chaos bound gives. The degree bound
`q ≤ d_j / 2` itself fails on the lattice readings of the build: a single-trace factor such as `BulkBound.p1`
carries `d = 2` but reads `N − Re tr U_p`, of degree `2` in the free field, so the tower monomial
`BulkBound.mono n` reads with chaos order `4(n + 1) = d`, beyond the Wick cover `2 wickIx = 2(n + 1)`, and no
`C` meets H1 at that channel alone. H1 for `ν_k` stays a hypothesis. ExpandStrong and the non-triviality
inputs are carried unchanged in the bundle.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the signs, the lower ends, the empty level and the point approached; `1` the
unit, the normalization, the unit norm of an eigenvector, the first level, the floor of `max(·, 1)` and the
limit of the ratio; `2` the even powers, the squares (of the Rényi-½ sum and of an eigenvector's entries) and
the two signs of a cube coordinate; `4` the spacetime dimension (the box),
the plaquette dimension and the fourth moment of the test; `8` the dimension pair; `−1` the sign of a cube
coordinate; `exp 2` the Shannon bound of the counterexample; `1/2` the lower end of the weights, `1/4` its
square, `3/4` and `3/2` the per-coordinate ratio of the weighted test, `2^i / 2^{m+1}` its binary weights;
`u`, `γ`, `γP`, `C`, `σⱼ`, `σP`, `E`, `D`, `a`, `c`, `r` existential; `b₀ = b0 N` the theory's one-loop coefficient.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ApertureCount

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.CompositeLink MassGap.JointRP
open MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ClayWiring
open MassGap.ObserverOS MassGap.ObserverOSGrowth
  MassGap.ObserverOSSchwartz MassGap.ObserverOSTempered MassGap.ObserverEnergyBox
  MassGap.ObserverOSEuclidS MassGap.ObserverOSReconstructionS MassGap.ObserverOSLinked
  MassGap.ObserverRotation MassGap.ContinuumTimeGroup
  MassGap.ClayFull MassGap.ObserverNontrivial MassGap.ContinuumHypercubic
  MassGap.ObserverSymField MassGap.ObserverEnergyMoments
  MassGap.PreObserver MassGap.CompositesBuild MassGap.ObsLead MassGap.ClayData MassGap.ReflAvg
  MassGap.MixConvRP MassGap.MultiScaleAll MassGap.CompositesRen MassGap.CompositesRenAll
  MassGap.MultiScaleOS MassGap.ApproxFromExpand MassGap.StrongExpand MassGap.CovFromFlow
  MassGap.SU2Best MassGap.NondegFromProxy MassGap.NonGaussFromScale
  MassGap.ProxyGenObserver MassGap.ProxyBoundFromScale MassGap.ScalePC MassGap.ScalePM
  MassGap.ClusterRoute MassGap.MeasuredSpacing MassGap.ZoomFree MassGap.ApertureModes

variable {N : ℕ}

/-! ## 1. The modes of a screen -/

section Modes

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
  {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → C(X, ℝ))

/-- **The eigenvector matrix of the screen's Gram matrix**: column `α` is the `α`-th eigenvector.
DERIVED: no numeral. -/
def evec (y α : ι) : ℝ := ((gram_isHermitian ν F).eigenvectorUnitary : Matrix ι ι ℝ) y α

/-- **The eigenvalues of the screen's Gram matrix**. DERIVED: no numeral. -/
def eig (α : ι) : ℝ := (gram_isHermitian ν F).eigenvalues α

/-- **The modes of the screen**: `mode α = ∑_y evec y α • F y`. DERIVED: no numeral. -/
def mode (α : ι) : C(X, ℝ) := ∑ y, evec ν F y α • F y

/-- The rows of the eigenvector matrix are orthonormal. DERIVED: `0`, `1` the identity's entries. -/
theorem evec_rows (y z : ι) : ∑ α, evec ν F y α * evec ν F z α = if y = z then 1 else 0 := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M y z)
    (Unitary.mul_star_self_of_mem ((gram_isHermitian ν F).eigenvectorUnitary).2)
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply, evec] using h

/-- The columns of the eigenvector matrix are orthonormal. DERIVED: `0`, `1` the identity's entries. -/
theorem evec_cols (α β : ι) : ∑ y, evec ν F y α * evec ν F y β = if α = β then 1 else 0 := by
  have h := congrArg (fun M : Matrix ι ι ℝ => M α β)
    (Unitary.star_mul_self_of_mem ((gram_isHermitian ν F).eigenvectorUnitary).2)
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply, evec] using h

/-- **The spectral theorem in coordinates**: `Uᵀ G U` is the diagonal of the eigenvalues.
DERIVED: `0` the off-diagonal entries. -/
theorem evec_gram_evec (α β : ι) :
    ∑ z, (∑ y, evec ν F y α * gram ν F y z) * evec ν F z β = if α = β then eig ν F α else 0 := by
  have h := (gram_isHermitian ν F).conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  have h2 := congrFun (congrFun h α) β
  simpa only [Matrix.mul_apply, Unitary.coe_star, Matrix.star_apply, star_trivial, Matrix.diagonal_apply,
    Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, evec, eig] using h2

/-- **The modes are uncorrelated, with variances the eigenvalues**. DERIVED: `0` the off-diagonal value. -/
theorem state_mode_mul (α β : ι) :
    ν (mode ν F α * mode ν F β) = if α = β then eig ν F α else 0 := by
  rw [← evec_gram_evec]
  simp only [mode, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [ν.map_sum]
  simp only [ν.map_sum, ν.map_smul, gram, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring

/-- **An eigenvalue is its mode's second moment**. DERIVED: `2` the square. -/
theorem eig_eq (α : ι) : eig ν F α = ν (mode ν F α ^ 2) := by
  rw [pow_two, state_mode_mul, if_pos rfl]

/-- **The Gram matrix is positive semidefinite**: every eigenvalue is `≥ 0`. DERIVED: `0` the sign. -/
theorem eig_nonneg (α : ι) : 0 ≤ eig ν F α := by
  rw [eig_eq]
  exact ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity

/-- **The screen is exactly its modes**: `F y = ∑_α evec y α • mode α`. DERIVED: no numeral. -/
theorem sum_evec_smul_mode (y : ι) : ∑ α, evec ν F y α • mode ν F α = F y := by
  simp only [mode, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, evec_rows, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- **The trace**: `∑_α eig α = ∑_y ν(F y ²)`. DERIVED: `2` the square. -/
theorem sum_eig : ∑ α, eig ν F α = ∑ y, ν (F y ^ 2) := by
  have h := (gram_isHermitian ν F).trace_eq_sum_eigenvalues
  simp only [Matrix.trace, Matrix.diag, gram, RCLike.ofReal_real_eq_id, id_eq] at h
  simp only [eig, pow_two]
  exact h.symm

omit [DecidableEq ι] in
/-- **A unit eigenvector**: `∑_y v y² = 1` and `G v = λ v`. DERIVED: `1` the unit norm; `2` the square. -/
def IsUnitEig (G : Matrix ι ι ℝ) (lam : ℝ) (v : ι → ℝ) : Prop :=
  ∑ y, v y ^ 2 = 1 ∧ G.mulVec v = lam • v

/-- **Every column of the eigenvector matrix is a unit eigenvector** of the Gram matrix at its eigenvalue.
DERIVED: `1` the unit norm; `2` the square. -/
theorem evec_isUnitEig (α : ι) : IsUnitEig (gram ν F) (eig ν F α) (fun y => evec ν F y α) := by
  refine ⟨?_, (gram_isHermitian ν F).mulVec_eigenvectorBasis α⟩
  have h := evec_cols ν F α α
  rw [if_pos rfl] at h
  simpa only [sq] using h

end Modes

/-! ## 2. Minkowski through the modes -/

section Minkowski

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (ν : MassGap.DLRLimit.State X)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar identity of the Minkowski step: `(c/W)^{2p} l^p = (|c| √l / W)^{2p}` for `l ≥ 0`.
DERIVED: `2` the even power. -/
theorem div_pow_sqrt (c l W : ℝ) (hl : 0 ≤ l) (p : ℕ) :
    (c / W) ^ (2 * p) * l ^ p = (|c| * Real.sqrt l / W) ^ (2 * p) := by
  rw [div_pow, div_pow, mul_pow, (even_two_mul p).pow_abs, pow_mul (Real.sqrt l), Real.sq_sqrt hl]
  ring

omit [DecidableEq ι] in
/-- **Minkowski through modes**: modes with `ν(e_α^{2p}) ≤ K λ_α^p` give
`ν((∑ c_α e_α)^{2p}) ≤ K (∑ |c_α| √λ_α)^{2p}`. DERIVED: `2` the even power; `0` the signs. -/
theorem state_pow_comb_le [Nonempty ι] (e : ι → C(X, ℝ)) (c lam : ι → ℝ) (hlam : ∀ α, 0 ≤ lam α)
    {K : ℝ} (hK : 0 ≤ K) (p : ℕ) (h : ∀ α, ν (e α ^ (2 * p)) ≤ K * lam α ^ p) :
    ν ((∑ α, c α • e α) ^ (2 * p)) ≤ K * (∑ α, |c α| * Real.sqrt (lam α)) ^ (2 * p) := by
  set S := ∑ α, |c α| * Real.sqrt (lam α) with hS
  have key : ∀ ε : ℝ, 0 < ε →
      ν ((∑ α, c α • e α) ^ (2 * p)) ≤ K * (S + Fintype.card ι * ε) ^ (2 * p) := by
    intro ε hε
    set a : ι → ℝ := fun α => |c α| * Real.sqrt (lam α) + ε with ha
    have ha0 : ∀ α, 0 < a α := fun α => by
      have : 0 ≤ |c α| * Real.sqrt (lam α) := by positivity
      simp only [ha]; linarith
    set A := ∑ α, a α with hA
    have hA0 : 0 < A := Finset.sum_pos (fun α _ => ha0 α) Finset.univ_nonempty
    have hAeq : A = S + Fintype.card ι * ε := by
      simp only [hA, ha, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hS]
    set w : ι → ℝ := fun α => a α / A with hw
    have hw0 : ∀ α, 0 < w α := fun α => div_pos (ha0 α) hA0
    have hw1 : ∑ α, w α = 1 := by
      simp only [hw]
      rw [← Finset.sum_div, div_self hA0.ne']
    have hpt : ∀ x, ((∑ α, c α • e α) ^ (2 * p)) x
        ≤ (∑ α, (w α * (c α / w α) ^ (2 * p)) • e α ^ (2 * p)) x := by
      intro x
      simp only [ContinuousMap.pow_apply, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      have e1 : ∑ α, c α * e α x = ∑ α, w α * (c α * e α x / w α) :=
        Finset.sum_congr rfl fun α _ => (mul_div_cancel₀ _ (hw0 α).ne').symm
      rw [e1]
      refine (Real.pow_arith_mean_le_arith_mean_pow_of_even Finset.univ w
        (fun α => c α * e α x / w α) (fun α _ => (hw0 α).le) hw1 (even_two_mul p)).trans_eq ?_
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [div_pow, mul_pow]
      ring
    have hterm : ∀ α, w α * (c α / w α) ^ (2 * p) * (K * lam α ^ p) ≤ K * (w α * A ^ (2 * p)) := by
      intro α
      have hcl : (c α / w α) ^ (2 * p) * lam α ^ p = (|c α| * Real.sqrt (lam α) / w α) ^ (2 * p) :=
        div_pow_sqrt (c α) (lam α) (w α) (hlam α) p
      have hle : |c α| * Real.sqrt (lam α) / w α ≤ a α / w α :=
        div_le_div_of_nonneg_right (by simp only [ha]; linarith) (hw0 α).le
      have haw : a α / w α = A := by simp only [hw]; rw [div_div_cancel₀ (ha0 α).ne']
      have hpow : (|c α| * Real.sqrt (lam α) / w α) ^ (2 * p) ≤ A ^ (2 * p) := by
        rw [← haw]; exact pow_le_pow_left₀ (by positivity) hle _
      calc w α * (c α / w α) ^ (2 * p) * (K * lam α ^ p)
          = K * (w α * ((c α / w α) ^ (2 * p) * lam α ^ p)) := by ring
        _ ≤ K * (w α * A ^ (2 * p)) := by
          rw [hcl]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (hw0 α).le) hK
    calc ν ((∑ α, c α • e α) ^ (2 * p))
        ≤ ν (∑ α, (w α * (c α / w α) ^ (2 * p)) • e α ^ (2 * p)) := ν.mono hpt
      _ = ∑ α, (w α * (c α / w α) ^ (2 * p)) * ν (e α ^ (2 * p)) := by
          rw [ν.map_sum]; simp only [ν.map_smul]
      _ ≤ ∑ α, (w α * (c α / w α) ^ (2 * p)) * (K * lam α ^ p) :=
          Finset.sum_le_sum fun α _ =>
            mul_le_mul_of_nonneg_left (h α) (mul_nonneg (hw0 α).le ((even_two_mul p).pow_nonneg _))
      _ ≤ ∑ α, K * (w α * A ^ (2 * p)) := Finset.sum_le_sum fun α _ => hterm α
      _ = K * A ^ (2 * p) := by rw [← Finset.mul_sum, ← Finset.sum_mul, hw1, one_mul]
      _ = K * (S + Fintype.card ι * ε) ^ (2 * p) := by rw [hAeq]
  have hlim : Tendsto (fun ε : ℝ => K * (S + Fintype.card ι * ε) ^ (2 * p)) (𝓝[>] 0)
      (𝓝 (K * S ^ (2 * p))) := by
    have hc : Continuous fun ε : ℝ => K * (S + Fintype.card ι * ε) ^ (2 * p) := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

variable (F : ι → C(X, ℝ))

/-- **The Rényi-½ count of a spectrum**: `(∑_α √p_α)²`, `p = w / ∑ w`. DERIVED: `2` the square. -/
def spRenyi {κ : Type*} [Fintype κ] (w : κ → ℝ) : ℝ := (∑ α, Real.sqrt (w α / ∑ β, w β)) ^ 2

/-- **The count turns one variance into every moment**: if every screen reading has the moments of `G₀` and
every mode is hypercontractive relative to its own variance, `ν(mode α^{2p}) ≤ K eig α^p`, then
`ν(G₀^{2p}) ≤ K (R ν(G₀²))^p`, `R` the Rényi-½ count of the screen's spectrum. DERIVED: `2` the even power
and the variance. -/
theorem state_pow_le_renyi [Nonempty ι] {G₀ : C(X, ℝ)} {p : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (htr : ∀ y q, ν (F y ^ q) = ν (G₀ ^ q))
    (h1 : ∀ α, ν (mode ν F α ^ (2 * p)) ≤ K * eig ν F α ^ p) :
    ν (G₀ ^ (2 * p)) ≤ K * (spRenyi (eig ν F) * ν (G₀ ^ 2)) ^ p := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set m2 := ν (G₀ ^ 2) with hm2
  have hm20 : 0 ≤ m2 := ν.nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
  set B : ι → ℝ := fun y => ∑ α, |evec ν F y α| * Real.sqrt (eig ν F α) with hB
  have hB0 : ∀ y, 0 ≤ B y := fun y => Finset.sum_nonneg fun α _ => by positivity
  have hsite : ∀ y, ν (G₀ ^ (2 * p)) ≤ K * B y ^ (2 * p) := by
    intro y
    rw [← htr y, ← sum_evec_smul_mode ν F y]
    exact state_pow_comb_le ν (mode ν F) (evec ν F y) (eig ν F) (eig_nonneg ν F) hK p h1
  -- the column sums
  have hcol : ∀ α, ∑ y, |evec ν F y α| ≤ Real.sqrt n := by
    intro α
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => |evec ν F y α|) (fun _ => (1 : ℝ))
    have h1' : ∑ y, |evec ν F y α| ^ 2 = 1 := by
      have := evec_cols ν F α α
      rw [if_pos rfl] at this
      rw [← this]
      exact Finset.sum_congr rfl fun y _ => by rw [sq_abs, sq]
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h1', one_mul] at hcs
    exact Real.le_sqrt_of_sq_le hcs
  -- the trace
  set T := ∑ α, eig ν F α with hTdef
  have hT : T = n * m2 := by
    rw [hTdef, sum_eig]
    simp only [htr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn, hm2]
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun α _ => eig_nonneg ν F α
  have hsqrt : ∑ α, Real.sqrt (eig ν F α) = Real.sqrt T * ∑ α, Real.sqrt (eig ν F α / T) := by
    rcases hT0.eq_or_lt with h0 | hpos
    · have hz : ∀ α, eig ν F α = 0 := fun α =>
        (Finset.sum_eq_zero_iff_of_nonneg fun β _ => eig_nonneg ν F β).1 h0.symm α (Finset.mem_univ α)
      simp [hz, ← h0]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Real.sqrt_div (eig_nonneg ν F α), mul_div_cancel₀ _ (Real.sqrt_pos.2 hpos).ne']
  have hSum : ∑ y, B y ≤ Real.sqrt n * ∑ α, Real.sqrt (eig ν F α) := by
    simp only [hB]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun α _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol α) (Real.sqrt_nonneg _)
  obtain ⟨y, -, hy⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (show ∑ y, B y ≤ ∑ _y : ι, (∑ y, B y) / n from le_of_eq (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn, mul_div_cancel₀ _ hn0.ne']))
  set Q := ∑ α, Real.sqrt (eig ν F α / T) with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _
  have hBy : B y ≤ Real.sqrt m2 * Q := by
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    calc B y ≤ (∑ y, B y) / n := hy
      _ ≤ Real.sqrt n * (∑ α, Real.sqrt (eig ν F α)) / n := div_le_div_of_nonneg_right hSum hn0.le
      _ = Real.sqrt n * (Real.sqrt n * Real.sqrt m2 * Q) / n := by
          rw [hsqrt, hT, Real.sqrt_mul hn0.le]
      _ = Real.sqrt m2 * Q := by
          rw [show Real.sqrt n * (Real.sqrt n * Real.sqrt m2 * Q)
              = (Real.sqrt n * Real.sqrt n) * (Real.sqrt m2 * Q) by ring, hsn,
            mul_div_cancel_left₀ _ hn0.ne']
  have hR : spRenyi (eig ν F) = Q ^ 2 := rfl
  calc ν (G₀ ^ (2 * p)) ≤ K * B y ^ (2 * p) := hsite y
    _ ≤ K * (Real.sqrt m2 * Q) ^ (2 * p) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hB0 y) hBy _) hK
    _ = K * (spRenyi (eig ν F) * m2) ^ p := by
        rw [hR, pow_mul]
        congr 2
        rw [mul_pow, Real.sq_sqrt hm20]
        ring

end Minkowski

/-! ## 3. Shannon to Rényi -/

section ShannonRenyi

/-- **The occupation of the `i`-th level**: the number of modes with `p_α > a^{2(i+1)}`.
DERIVED: `1` the first level; `2` the square of the ladder ratio. -/
def levelCount {κ : Type*} [Fintype κ] (w : κ → ℝ) (a : ℝ) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun α => a ^ (2 * (i + 1)) < w α / ∑ β, w β).card

/-- DERIVED: `0` the sign; `1`, `2` as in `levelCount`. -/
theorem level_nonneg {x a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (i : ℕ) :
    0 ≤ (if a ^ (2 * (i + 1)) < x then a ^ i * (1 - a) else 0) := by
  split_ifs
  · exact mul_nonneg (pow_nonneg ha0.le _) (by linarith)
  · exact le_rfl

/-- DERIVED: `1`, `2` as in `levelCount`; `0` the empty level. -/
theorem summable_level (x : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Summable fun i : ℕ => if a ^ (2 * (i + 1)) < x then a ^ i * (1 - a) else 0 :=
  Summable.of_nonneg_of_le (level_nonneg ha0 ha1)
    (fun i => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (pow_nonneg ha0.le _) (by linarith))
    ((summable_geometric_of_lt_one ha0.le ha1).mul_right _)

/-- **The layer cake on a geometric ladder**: `√x ≤ ∑_i [x > a^{2(i+1)}] a^i (1 − a)` for `x ∈ [0, 1]`.
DERIVED: `0`, `1` the interval; `1`, `2` as in `levelCount`. -/
theorem sqrt_le_tsum_level {x a : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ha0 : 0 < a) (ha1 : a < 1) :
    Real.sqrt x ≤ ∑' i : ℕ, if a ^ (2 * (i + 1)) < x then a ^ i * (1 - a) else 0 := by
  rcases hx0.eq_or_lt with hx | hx
  · rw [← hx, Real.sqrt_zero]; exact tsum_nonneg (level_nonneg ha0 ha1)
  have hex : ∃ i : ℕ, a ^ (2 * (i + 1)) < x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (show a ^ 2 < 1 by nlinarith)
    refine ⟨n, lt_of_le_of_lt ?_ hn⟩
    rw [pow_mul]
    exact pow_le_pow_of_le_one (by positivity) (by nlinarith) (Nat.le_succ n)
  obtain ⟨J, hJx, hmin⟩ : ∃ J : ℕ, a ^ (2 * (J + 1)) < x ∧ ∀ m < J, ¬ a ^ (2 * (m + 1)) < x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hxJ : x ≤ a ^ (2 * J) := by
    cases J with
    | zero => simpa using hx1
    | succ J' => exact not_lt.1 (hmin J' (Nat.lt_succ_self J'))
  have hsq : Real.sqrt x ≤ a ^ J := by
    rw [Real.sqrt_le_left (pow_nonneg ha0.le J), ← pow_mul, mul_comm J 2]
    exact hxJ
  have htail : ∀ i : ℕ, (if a ^ (2 * (i + J + 1)) < x then a ^ (i + J) * (1 - a) else 0)
      = a ^ J * (1 - a) * a ^ i := by
    intro i
    have hlt : a ^ (2 * (i + J + 1)) < x :=
      lt_of_le_of_lt (pow_le_pow_of_le_one ha0.le ha1.le (by omega)) hJx
    rw [if_pos hlt, pow_add]
    ring
  have h1a : (1 - a) ≠ 0 := (sub_pos.2 ha1).ne'
  have hshift : ∑' i : ℕ, (if a ^ (2 * (i + J + 1)) < x then a ^ (i + J) * (1 - a) else 0) = a ^ J := by
    rw [tsum_congr htail, tsum_mul_left, tsum_geometric_of_lt_one ha0.le ha1, mul_assoc,
      mul_inv_cancel₀ h1a, mul_one]
  calc Real.sqrt x ≤ a ^ J := hsq
    _ = ∑' i : ℕ, (if a ^ (2 * (i + J + 1)) < x then a ^ (i + J) * (1 - a) else 0) := hshift.symm
    _ ≤ (∑ i ∈ Finset.range J, (if a ^ (2 * (i + 1)) < x then a ^ i * (1 - a) else 0))
          + ∑' i : ℕ, (if a ^ (2 * (i + J + 1)) < x then a ^ (i + J) * (1 - a) else 0) :=
        le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => level_nonneg ha0 ha1 i)
    _ = _ := (summable_level x ha0 ha1).sum_add_tsum_nat_add J

/-- **The Rényi-½ sum through the level counts**. DERIVED: `0`, `1`, `2` as in `sqrt_le_tsum_level`. -/
theorem sum_sqrt_le_levels {κ : Type*} [Fintype κ] {w : κ → ℝ} (hw : ∀ α, 0 ≤ w α) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∑ α, Real.sqrt (w α / ∑ β, w β) ≤ ∑' i : ℕ, (levelCount w a i : ℝ) * (a ^ i * (1 - a)) := by
  have hT0 : 0 ≤ ∑ β, w β := Finset.sum_nonneg fun β _ => hw β
  have hp0 : ∀ α, 0 ≤ w α / ∑ β, w β := fun α => div_nonneg (hw α) hT0
  have hp1 : ∀ α, w α / ∑ β, w β ≤ 1 := fun α =>
    div_le_one_of_le₀ (Finset.single_le_sum (fun β _ => hw β) (Finset.mem_univ α)) hT0
  calc ∑ α, Real.sqrt (w α / ∑ β, w β)
      ≤ ∑ α, ∑' i : ℕ, (if a ^ (2 * (i + 1)) < w α / ∑ β, w β then a ^ i * (1 - a) else 0) :=
        Finset.sum_le_sum fun α _ => sqrt_le_tsum_level (hp0 α) (hp1 α) ha0 ha1
    _ = ∑' i : ℕ, ∑ α, (if a ^ (2 * (i + 1)) < w α / ∑ β, w β then a ^ i * (1 - a) else 0) :=
        (Summable.tsum_finsetSum fun α _ => summable_level _ ha0 ha1).symm
    _ = ∑' i : ℕ, (levelCount w a i : ℝ) * (a ^ i * (1 - a)) := by
        refine tsum_congr fun i => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rfl

/-- DERIVED: `1` the shift of the index. -/
theorem summable_shift_pow_geom (r : ℕ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Summable fun i : ℕ => ((i : ℝ) + 1) ^ r * a ^ i := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) r
    (show ‖a‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos ha0])
  have h1 := (summable_nat_add_iff 1).2 h0
  refine (h1.mul_left a⁻¹).congr fun i => ?_
  push_cast
  calc a⁻¹ * (((i : ℝ) + 1) ^ r * a ^ (i + 1)) = ((i : ℝ) + 1) ^ r * a ^ i * (a⁻¹ * a) := by ring
    _ = ((i : ℝ) + 1) ^ r * a ^ i := by rw [inv_mul_cancel₀ ha0.ne', mul_one]

/-- **Shannon to Rényi under decay in the spectrum's own units**: if the occupation of every level is at most
`c · exp H · (i + 1)^r`, then `R ≤ (c · exp H · (1 − a) · ∑_i (i + 1)^r a^i)²`. DERIVED: `0`, `1` the ladder
interval; `1`, `2` as in `levelCount`; `2` the square. -/
theorem spRenyi_le_of_levels {κ : Type*} [Fintype κ] {w : κ → ℝ} (hw : ∀ α, 0 ≤ w α) {a c : ℝ} {r : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hlev : ∀ i : ℕ, (levelCount w a i : ℝ) ≤ c * spDim w * ((i : ℝ) + 1) ^ r) :
    spRenyi w ≤ (c * spDim w * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ r * a ^ i) ^ 2 := by
  have hS := summable_shift_pow_geom r ha0 ha1
  have hlhs0 : 0 ≤ ∑ α, Real.sqrt (w α / ∑ β, w β) := Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _
  have hga : ∀ i : ℕ, 0 ≤ a ^ i * (1 - a) := fun i => mul_nonneg (pow_nonneg ha0.le i) (by linarith)
  have hbound : ∀ i : ℕ, (levelCount w a i : ℝ) * (a ^ i * (1 - a))
      ≤ c * spDim w * (1 - a) * (((i : ℝ) + 1) ^ r * a ^ i) := fun i => by
    have h := mul_le_mul_of_nonneg_right (hlev i) (hga i)
    calc _ ≤ _ := h
      _ = _ := by ring
  have hcount : Summable fun i : ℕ => (levelCount w a i : ℝ) * (a ^ i * (1 - a)) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (Nat.cast_nonneg _) (hga i)) hbound (hS.mul_left _)
  unfold spRenyi
  refine pow_le_pow_left₀ hlhs0 ?_ 2
  refine (sum_sqrt_le_levels hw ha0 ha1).trans ?_
  calc ∑' i : ℕ, (levelCount w a i : ℝ) * (a ^ i * (1 - a))
      ≤ ∑' i : ℕ, c * spDim w * (1 - a) * (((i : ℝ) + 1) ^ r * a ^ i) :=
        hcount.tsum_le_tsum hbound (hS.mul_left _)
    _ = _ := tsum_mul_left

/-- **`n` equal modes have Rényi-½ count `n`**: the count cannot be replaced by `1`. DERIVED: no numeral. -/
theorem spRenyi_const {κ : Type*} [Fintype κ] [Nonempty κ] {c : ℝ} (hc : 0 < c) :
    spRenyi (fun _ : κ => c) = Fintype.card κ := by
  have hn : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  unfold spRenyi
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e1 : c / ((Fintype.card κ : ℝ) * c) = (Fintype.card κ : ℝ)⁻¹ := by
    rw [mul_comm, ← div_div, div_self hc.ne', one_div]
  rw [e1, mul_pow, Real.sq_sqrt (inv_nonneg.2 hn.le), sq, mul_assoc, mul_inv_cancel₀ hn.ne', mul_one]

/-- **Shannon alone does not control the Rényi-½ count**: for every `B` a spectrum with `exp H ≤ e²` and
`R ≥ B` (`p₁ = 1 − ε`, `ε = 1/log m` spread evenly over `m` further modes). DERIVED: `2` the Shannon bound;
`0` the signs; `1` the first mode. -/
theorem spRenyi_unbounded_at_bounded_spDim (B : ℝ) :
    ∃ (m : ℕ) (w : Fin (m + 1) → ℝ), (∀ i, 0 ≤ w i) ∧ spDim w ≤ Real.exp 2 ∧ B ≤ spRenyi w := by
  obtain ⟨m0, hm0⟩ := exists_nat_gt (4 * B ^ 2)
  set m : ℕ := m0 + 3 with hm
  have hmR : (m : ℝ) = m0 + 3 := by rw [hm]; norm_num
  have hm0' : (0 : ℝ) < m := by rw [hmR]; positivity
  have he : Real.exp 1 < m := by
    have h := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
    rw [hmR]
    norm_num at h
    linarith
  set L := Real.log m with hL
  have hL1 : 1 < L := by rw [hL, Real.lt_log_iff_exp_lt hm0']; exact he
  set ε := 1 / L with hε
  have hε0 : 0 < ε := by rw [hε]; exact div_pos one_pos (by linarith)
  have hε1 : ε < 1 := by rw [hε, div_lt_one (by linarith)]; exact hL1
  have hεL : ε * L = 1 := by rw [hε]; exact one_div_mul_cancel (ne_of_gt (by linarith))
  set w : Fin (m + 1) → ℝ := fun i => if i = 0 then 1 - ε else ε / m with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    simp only [hw]
    split_ifs
    · linarith
    · exact div_nonneg hε0.le hm0'.le
  have hwsucc : ∀ i : Fin m, w i.succ = ε / m := fun i => by simp [hw]
  have hw00 : w 0 = 1 - ε := by simp [hw]
  have hsum : ∑ i, w i = 1 := by
    rw [Fin.sum_univ_succ, hw00]
    simp only [hwsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hm0'.ne']
    ring
  refine ⟨m, w, hw0, ?_, ?_⟩
  · unfold spDim
    rw [hsum, Real.exp_le_exp, Fin.sum_univ_succ]
    simp only [div_one, hw00, hwsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h1 : Real.negMulLog (1 - ε) ≤ ε := by
      have := Real.negMulLog_le_one_sub_self (show 0 ≤ 1 - ε by linarith)
      linarith
    have hmε : (m : ℝ) * (ε / m) = ε := mul_div_cancel₀ _ hm0'.ne'
    have h2 : (m : ℝ) * Real.negMulLog (ε / m) = Real.negMulLog ε + ε * L := by
      simp only [Real.negMulLog]
      rw [Real.log_div hε0.ne' hm0'.ne', ← hL]
      calc (m : ℝ) * (-(ε / m) * (Real.log ε - L)) = -((m : ℝ) * (ε / m)) * (Real.log ε - L) := by ring
        _ = -ε * Real.log ε + ε * L := by rw [hmε]; ring
    have h3 : Real.negMulLog ε ≤ 1 - ε := Real.negMulLog_le_one_sub_self hε0.le
    rw [h2]
    linarith
  · unfold spRenyi
    rw [hsum, Fin.sum_univ_succ]
    simp only [div_one, hw00, hwsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hq0 : 0 ≤ (m : ℝ) * Real.sqrt (ε / m) := by positivity
    have hge : (m : ℝ) * Real.sqrt (ε / m) ≤ Real.sqrt (1 - ε) + m * Real.sqrt (ε / m) :=
      le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have hsqr : ((m : ℝ) * Real.sqrt (ε / m)) ^ 2 = m * ε := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hε0.le hm0'.le), sq, mul_assoc, mul_div_cancel₀ _ hm0'.ne']
    -- `m ε = m / log m ≥ √m / 2 ≥ B`
    have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0'
    have hLle : L ≤ 2 * Real.sqrt m := by
      have hlog := Real.log_le_sub_one_of_pos hsm0
      rw [Real.log_sqrt hm0'.le, ← hL] at hlog
      linarith
    have hmε : (m : ℝ) * ε = m / L := by rw [hε]; ring
    have hhalf : Real.sqrt m / 2 ≤ m * ε := by
      rw [hmε, le_div_iff₀ (by linarith)]
      calc Real.sqrt m / 2 * L ≤ Real.sqrt m / 2 * (2 * Real.sqrt m) :=
            mul_le_mul_of_nonneg_left hLle (by positivity)
        _ = m := by rw [show Real.sqrt m / 2 * (2 * Real.sqrt m) = Real.sqrt m * Real.sqrt m by ring,
            Real.mul_self_sqrt hm0'.le]
    have hB : B ≤ Real.sqrt m / 2 := by
      rcases le_or_gt B 0 with hB0 | hB0
      · linarith
      · have : 2 * B ≤ Real.sqrt m := by
          refine Real.le_sqrt_of_sq_le ?_
          have : (m0 : ℝ) ≤ m := by rw [hmR]; linarith
          nlinarith
        linarith
    calc B ≤ Real.sqrt m / 2 := hB
      _ ≤ m * ε := hhalf
      _ = ((m : ℝ) * Real.sqrt (ε / m)) ^ 2 := hsqr.symm
      _ ≤ (Real.sqrt (1 - ε) + m * Real.sqrt (ε / m)) ^ 2 := pow_le_pow_left₀ hq0 hge 2

end ShannonRenyi

/-! ## 4. The load-bearing test -/

section Walsh

variable (m : ℕ)

/-- The sign of a cube coordinate. DERIVED: `−1`, `1` the two signs. -/
def sgnB (b : Bool) : ℝ := if b then -1 else 1

/-- DERIVED: `1` the square of a sign. -/
theorem sgnB_mul_self (b : Bool) : sgnB b * sgnB b = 1 := by cases b <;> norm_num [sgnB]

/-- **The Walsh character** `χ_S(x) = ∏_{i ∈ S} sgn(xᵢ)` on the cube `{±1}^m`. DERIVED: no numeral. -/
def walsh (S : Finset (Fin m)) : C(Fin m → Bool, ℝ) :=
  ⟨fun x => ∏ i ∈ S, sgnB (x i), continuous_of_discreteTopology⟩

/-- **The uniform state on the cube**: `ν f = 2^{−m} ∑_x f x`. DERIVED: `2` the two values of a
coordinate; `0`, `1` the state's axioms. -/
def cubeState : MassGap.DLRLimit.State (Fin m → Bool) where
  toFun f := (∑ x, f x) / 2 ^ m
  map_add' f g := by simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, add_div]
  map_smul' c f := by simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]
  nonneg' f hf := div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)
  one' := by
    rw [div_eq_one_iff_eq (by positivity)]
    simp

/-- DERIVED: `2` as in `cubeState`. -/
theorem cubeState_apply (f : C(Fin m → Bool, ℝ)) : cubeState m f = (∑ x, f x) / 2 ^ m := rfl

/-- A cube sum of a product is the product of the coordinate sums. DERIVED: no numeral. -/
theorem sum_cube_prod (g : Fin m → Bool → ℝ) :
    ∑ x : Fin m → Bool, ∏ i, g i (x i) = ∏ i, (g i true + g i false) := by
  calc ∑ x : Fin m → Bool, ∏ i, g i (x i)
      = ∑ x ∈ Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset Bool), ∏ i, g i (x i) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ i, ∑ b ∈ (Finset.univ : Finset Bool), g i b := (Finset.prod_univ_sum _ _).symm
    _ = ∏ i, (g i true + g i false) := by simp only [Fintype.sum_bool]

/-- **The Walsh characters are orthonormal**. DERIVED: `0`, `1` the entries of the identity; `2` the
coordinate sum. -/
theorem cube_walsh_mul (S T : Finset (Fin m)) :
    cubeState m (walsh m S * walsh m T) = if S = T then 1 else 0 := by
  have hfac : ∀ i : Fin m, ((if i ∈ S then sgnB true else 1) * (if i ∈ T then sgnB true else 1)
      + (if i ∈ S then sgnB false else 1) * (if i ∈ T then sgnB false else 1))
      = if (i ∈ S ↔ i ∈ T) then 2 else 0 := by
    intro i
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> norm_num [hS, hT, sgnB]
  have hx : ∀ x : Fin m → Bool, (walsh m S * walsh m T) x
      = ∏ i, (if i ∈ S then sgnB (x i) else 1) * (if i ∈ T then sgnB (x i) else 1) := by
    intro x
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Fintype.prod_ite_mem]
    rfl
  rw [cubeState_apply]
  simp_rw [hx]
  rw [sum_cube_prod m (fun i b => (if i ∈ S then sgnB b else 1) * (if i ∈ T then sgnB b else 1))]
  simp only [hfac]
  split_ifs with hST
  · subst hST
    simp only [iff_self, ↓reduceIte, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact div_self (by positivity)
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra h
      push Not at h
      exact hST (Finset.ext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), zero_div]

/-- DERIVED: `1` the unit. -/
theorem walsh_mul_self (S : Finset (Fin m)) : walsh m S * walsh m S = 1 := by
  ext x
  simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply, walsh, ContinuousMap.coe_mk,
    ← Finset.prod_mul_distrib, sgnB_mul_self, Finset.prod_const_one]

/-- **Every mode is hypercontractive with constant `1` at every order**: `ν(χ_S^{2p}) = ν(χ_S²)^p`.
DERIVED: `2` the even power and the variance. -/
theorem cube_walsh_pow (S : Finset (Fin m)) (p : ℕ) :
    cubeState m (walsh m S ^ (2 * p)) = cubeState m (walsh m S ^ 2) ^ p := by
  rw [pow_mul, sq, walsh_mul_self, one_pow, (cubeState m).map_one, one_pow]

/-- **The reading**: the sum of all `2^m` Walsh characters. DERIVED: no numeral. -/
def cubeRead : C(Fin m → Bool, ℝ) := ∑ S, walsh m S

/-- DERIVED: `1` the constant term. -/
theorem cubeRead_apply (x : Fin m → Bool) : cubeRead m x = ∏ i, (1 + sgnB (x i)) := by
  rw [Finset.prod_one_add, Finset.powerset_univ]
  simp only [cubeRead, ContinuousMap.coe_sum, Finset.sum_apply, walsh, ContinuousMap.coe_mk]

/-- DERIVED: `1`, `2` as in `cubeRead_apply`, `cubeState`. -/
theorem cube_cubeRead_pow (q : ℕ) :
    cubeState m (cubeRead m ^ q) = ((1 + sgnB true) ^ q + (1 + sgnB false) ^ q) ^ m / 2 ^ m := by
  rw [cubeState_apply]
  simp only [ContinuousMap.pow_apply, cubeRead_apply, ← Finset.prod_pow]
  rw [sum_cube_prod m (fun _ b => (1 + sgnB b) ^ q)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- DERIVED: `2` the variance; `2` the value. -/
theorem cube_two : cubeState m (cubeRead m ^ 2) = 2 ^ m := by
  rw [cube_cubeRead_pow, show (1 + sgnB true) ^ 2 + (1 + sgnB false) ^ 2 = (4 : ℝ) by norm_num [sgnB],
    ← div_pow]
  norm_num

/-- **The fourth moment grows with the count**: `ν(F⁴) = 2^m ν(F²)²`. DERIVED: `4` the fourth moment; `2`
the variance and the count's base. -/
theorem cube_four : cubeState m (cubeRead m ^ 4) = 2 ^ m * cubeState m (cubeRead m ^ 2) ^ 2 := by
  rw [cube_two, cube_cubeRead_pow,
    show (1 + sgnB true) ^ 4 + (1 + sgnB false) ^ 4 = (16 : ℝ) by norm_num [sgnB], ← div_pow,
    ← pow_mul, mul_comm m 2, pow_mul, ← mul_pow]
  norm_num

/-- **The load-bearing test**: per-mode hypercontractivity at constant `1` (`cube_walsh_pow`) and the
variance do not bound the fourth moment uniformly: no `K` has `ν(F⁴) ≤ K ν(F²)²` for every `m`. DERIVED: `4`
the fourth moment; `2` the variance. -/
theorem no_uniform_fourth :
    ¬ ∃ K : ℝ, ∀ m : ℕ, cubeState m (cubeRead m ^ 4) ≤ K * cubeState m (cubeRead m ^ 2) ^ 2 := by
  rintro ⟨K, hK⟩
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt K (one_lt_two : (1 : ℝ) < 2)
  have h := hK m
  rw [cube_four] at h
  have hX : 0 < cubeState m (cubeRead m ^ 2) ^ 2 := by rw [cube_two]; positivity
  have := le_of_mul_le_mul_right h hX
  linarith

/-- **A diagonal Gram matrix with distinct entries has one-dimensional eigenspaces**: a unit eigenvector is
`±` a coordinate vector, at that coordinate's entry. DERIVED: `0` the other coordinates; `1` the unit norm;
`2` the square. -/
theorem isUnitEig_diag {κ : Type*} [Fintype κ] [DecidableEq κ] {G : Matrix κ κ ℝ} {d : κ → ℝ}
    (hd : Function.Injective d) (hG : G = Matrix.diagonal d) {lam : ℝ} {v : κ → ℝ}
    (hv : IsUnitEig G lam v) : ∃ y, lam = d y ∧ v y ^ 2 = 1 ∧ ∀ z, z ≠ y → v z = 0 := by
  obtain ⟨h1, h2⟩ := hv
  subst hG
  have hcomp : ∀ z, d z * v z = lam * v z := fun z => by
    have := congrFun h2 z
    rwa [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  obtain ⟨y, hy⟩ : ∃ y, v y ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    simp [hcon] at h1
  have hlam : lam = d y := (mul_right_cancel₀ hy (hcomp y)).symm
  have hz : ∀ z, z ≠ y → v z = 0 := by
    intro z hzy
    have h := hcomp z
    rw [hlam] at h
    have hne : d z - d y ≠ 0 := sub_ne_zero.2 fun e => hzy (hd e)
    have h0 : (d z - d y) * v z = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.1 h0).resolve_left hne
  refine ⟨y, hlam, ?_, hz⟩
  rw [← h1, Finset.sum_eq_single y (fun z _ hzy => by rw [hz z hzy]; ring)
    (fun h => absurd (Finset.mem_univ y) h)]

/-- **The weight of a cube coordinate**: `t_i = exp(−2^i / 2^{m+1}) ∈ [1/2, 1]`. DERIVED: `2` the binary
weights and the base of the scale; `1` the shift of the scale. -/
def wt (i : Fin m) : ℝ := Real.exp (-((2 : ℝ) ^ (i : ℕ) / 2 ^ (m + 1)))

/-- **The weight of a Walsh character**: `c_S = ∏_{i ∈ S} t_i`. DERIVED: no numeral. -/
def cw (S : Finset (Fin m)) : ℝ := ∏ i ∈ S, wt m i

/-- **The weighted screen**: `F_S = c_S χ_S`. DERIVED: no numeral. -/
def wScreen (S : Finset (Fin m)) : C(Fin m → Bool, ℝ) := cw m S • walsh m S

/-- **The weighted reading**: `∑_S c_S χ_S`. DERIVED: no numeral. -/
def wRead : C(Fin m → Bool, ℝ) := ∑ S, wScreen m S

/-- DERIVED: `1/2` the lower end (`exp(−1/2) ≥ 1/2`); `1` the upper end; `2` as in `wt`. -/
theorem wt_bounds (i : Fin m) : 1 / 2 ≤ wt m i ∧ wt m i ≤ 1 := by
  have hle : (2 : ℝ) ^ (i : ℕ) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) i.isLt.le
  have hx : (2 : ℝ) ^ (i : ℕ) / 2 ^ (m + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity), pow_succ]
    linarith
  have hx0 : 0 ≤ (2 : ℝ) ^ (i : ℕ) / 2 ^ (m + 1) := by positivity
  refine ⟨?_, Real.exp_le_one_iff.2 (neg_nonpos.2 hx0)⟩
  have h := Real.add_one_le_exp (-((2 : ℝ) ^ (i : ℕ) / 2 ^ (m + 1)))
  unfold wt
  linarith

/-- **The squared weights are distinct**: `c_S² = exp(−(∑_{i ∈ S} 2^i) / 2^m)` and the binary expansion is
injective (`Finset.geomSum_injective`). DERIVED: `2` the square and the base of the expansion. -/
theorem cw_sq_injective : Function.Injective fun S : Finset (Fin m) => cw m S ^ 2 := by
  intro S T h
  have h' : cw m S ^ 2 = cw m T ^ 2 := h
  have hS : 0 ≤ cw m S := Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hT : 0 ≤ cw m T := Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have h1 := (sq_eq_sq₀ hS hT).1 h'
  unfold cw wt at h1
  rw [← Real.exp_sum, ← Real.exp_sum, Real.exp_eq_exp, Finset.sum_neg_distrib, Finset.sum_neg_distrib,
    neg_inj, ← Finset.sum_div, ← Finset.sum_div, div_left_inj' (by positivity)] at h1
  have h2 : ∑ i ∈ S.map Fin.valEmbedding, 2 ^ i = ∑ i ∈ T.map Fin.valEmbedding, 2 ^ i := by
    simp only [Finset.sum_map, Fin.valEmbedding_apply]
    exact_mod_cast h1
  exact Finset.map_injective Fin.valEmbedding (Finset.geomSum_injective (n := 2) le_rfl h2)

/-- **The weighted screen's Gram matrix is diagonal**, with entries `c_S²`. DERIVED: `2` the square; `0` the
off-diagonal entries. -/
theorem wgram : gram (cubeState m) (wScreen m) = Matrix.diagonal fun S => cw m S ^ 2 := by
  ext S T
  rw [Matrix.diagonal_apply]
  simp only [gram, wScreen, smul_mul_smul_comm, (cubeState m).map_smul, cube_walsh_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- **Every unit eigenvector's mode meets the per-mode bound with equality, at every order and every `m`**:
the eigenvalues `c_S²` are distinct, so a unit eigenvector is `±` a coordinate vector and its mode is
`± c_S χ_S`, with `ν((c_S χ_S)^{2p}) = (c_S²)^p`. DERIVED: `2` the even power. -/
theorem wcube_unitEig_pow (p : ℕ) {lam : ℝ} {v : Finset (Fin m) → ℝ}
    (hv : IsUnitEig (gram (cubeState m) (wScreen m)) lam v) :
    cubeState m ((∑ S, v S • wScreen m S) ^ (2 * p)) = lam ^ p := by
  obtain ⟨y, hlam, hy, hz⟩ := isUnitEig_diag (cw_sq_injective m) (wgram m) hv
  have hlam' : lam = cw m y ^ 2 := hlam
  rw [Finset.sum_eq_single y (fun z _ hzy => by rw [hz z hzy, zero_smul])
    (fun h => absurd (Finset.mem_univ y) h)]
  have hw : walsh m y ^ (2 * p) = 1 := by rw [pow_mul, sq, walsh_mul_self, one_pow]
  rw [wScreen, smul_smul, smul_pow, hw, (cubeState m).map_smul, (cubeState m).map_one, mul_one,
    mul_pow, pow_mul (v y), pow_mul (cw m y), hy, one_pow, one_mul, hlam']

/-- **The basis-free H1 holds on the weighted cube with `C = 1`, uniformly in `m`**, at every Wick exponent.
DERIVED: `1` the constant `C`; `2` the even power; `0` the sign. -/
theorem wcube_H1 (p w : ℕ) {lam : ℝ} {v : Finset (Fin m) → ℝ}
    (hv : IsUnitEig (gram (cubeState m) (wScreen m)) lam v) :
    cubeState m ((∑ S, v S • wScreen m S) ^ (2 * p)) ≤ ((2 * p).factorial : ℝ) ^ w * (1 * lam) ^ p := by
  have h := wcube_unitEig_pow m p hv
  have h0 : 0 ≤ lam ^ p := by
    rw [← h]
    exact (cubeState m).nonneg _ fun x => by
      simp only [ContinuousMap.pow_apply]; exact (even_two_mul p).pow_nonneg _
  rw [h, one_mul]
  exact le_mul_of_one_le_left h0 (one_le_pow₀ (by exact_mod_cast Nat.factorial_pos _))

/-- DERIVED: `1` the constant term. -/
theorem wRead_apply (x : Fin m → Bool) : wRead m x = ∏ i, (1 + wt m i * sgnB (x i)) := by
  rw [Finset.prod_one_add, Finset.powerset_univ]
  simp only [wRead, wScreen, cw, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, walsh, ContinuousMap.coe_mk, Finset.prod_mul_distrib]

/-- DERIVED: `1`, `2` as in `wRead_apply`, `cubeState`. -/
theorem wcube_pow (q : ℕ) :
    cubeState m (wRead m ^ q)
      = (∏ i, ((1 + wt m i * sgnB true) ^ q + (1 + wt m i * sgnB false) ^ q)) / 2 ^ m := by
  rw [cubeState_apply]
  simp only [ContinuousMap.pow_apply, wRead_apply, ← Finset.prod_pow]
  rw [sum_cube_prod m (fun i b => (1 + wt m i * sgnB b) ^ q)]

/-- DERIVED: `−1`, `1` the two signs. -/
theorem sgnB_true : sgnB true = -1 := by norm_num [sgnB]

/-- DERIVED: `1` the sign. -/
theorem sgnB_false : sgnB false = 1 := by norm_num [sgnB]

/-- One coordinate's factor: `(1 − t)⁴ + (1 + t)⁴ ≥ ¾ ((1 − t)² + (1 + t)²)²` for `t ∈ [1/2, 1]`.
DERIVED: `3/4` the per-coordinate ratio; `1/2`, `1` the interval; `2`, `4` the moments. -/
theorem factor_le {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t ≤ 1) :
    3 / 4 * ((1 + t * sgnB true) ^ 2 + (1 + t * sgnB false) ^ 2) ^ 2
      ≤ (1 + t * sgnB true) ^ 4 + (1 + t * sgnB false) ^ 4 := by
  rw [sgnB_true, sgnB_false]
  have hu0 : 1 / 4 ≤ t ^ 2 := by nlinarith
  have hu1 : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hu0) (sub_nonneg.2 hu1)]

/-- DERIVED: `0` the sign; `2` the variance. -/
theorem factor_pos (t : ℝ) : 0 < (1 + t * sgnB true) ^ 2 + (1 + t * sgnB false) ^ 2 := by
  rw [sgnB_true, sgnB_false]
  nlinarith [sq_nonneg t]

/-- **The fourth moment grows with the count on the non-degenerate cube**: `ν(F⁴) ≥ (3/2)^m ν(F²)²`.
DERIVED: `3/2` the per-coordinate ratio; `2`, `4` the moments. -/
theorem wcube_four_ge : (3 / 2 : ℝ) ^ m * cubeState m (wRead m ^ 2) ^ 2 ≤ cubeState m (wRead m ^ 4) := by
  rw [wcube_pow, wcube_pow, div_pow _ ((2 : ℝ) ^ m) 2, ← Finset.prod_pow]
  have hprod : ∏ i : Fin m, (3 / 4 * ((1 + wt m i * sgnB true) ^ 2 + (1 + wt m i * sgnB false) ^ 2) ^ 2)
      ≤ ∏ i : Fin m, ((1 + wt m i * sgnB true) ^ 4 + (1 + wt m i * sgnB false) ^ 4) :=
    Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => factor_le (wt_bounds m i).1 (wt_bounds m i).2)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  rw [le_div_iff₀ (by positivity)]
  have key : ∀ P : ℝ, (3 / 2 : ℝ) ^ m * (P / (2 ^ m) ^ 2) * 2 ^ m = (3 / 4) ^ m * P := by
    intro P
    have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
    rw [show (3 / 4 : ℝ) = 3 / 2 / 2 by norm_num, div_pow (3 / 2 : ℝ) 2 m]
    field_simp
  rw [key]
  exact hprod

/-- **The restored load-bearing test**: on the weighted cube the basis-free H1 holds with `C = 1` for every
`m` (`wcube_H1`) and every eigenspace is one-dimensional (`cw_sq_injective`), yet no `K` has
`ν(F⁴) ≤ K ν(F²)²` for every `m`. DERIVED: `4` the fourth moment; `2` the variance; `3/2` the ratio. -/
theorem no_uniform_fourth_nondeg :
    ¬ ∃ K : ℝ, ∀ m : ℕ, cubeState m (wRead m ^ 4) ≤ K * cubeState m (wRead m ^ 2) ^ 2 := by
  rintro ⟨K, hK⟩
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt K (by norm_num : (1 : ℝ) < 3 / 2)
  have hpos : 0 < cubeState m (wRead m ^ 2) ^ 2 := by
    have : 0 < cubeState m (wRead m ^ 2) := by
      rw [wcube_pow]
      exact div_pos (Finset.prod_pos fun i _ => factor_pos _) (by positivity)
    positivity
  have h := (wcube_four_ge m).trans (hK m)
  have := le_of_mul_le_mul_right h hpos
  linarith

end Walsh

/-! ## 5. The lattice screen -/

section Lattice

variable [NeZero N]

/-- **The eigenvalues of the observer's screen** at aperture `s` and step `k`. DERIVED: `4` the spacetime
dimension of the box. -/
def apEig (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) : (Fin 4 → Fin (apL N k s)) → ℝ :=
  eig (stateK (NeZero.ne N) k) (screen Wf k s j)

/-- **The modes of the observer's screen**. DERIVED: `4` as in `apEig`. -/
def apMode (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    (Fin 4 → Fin (apL N k s)) → C(Cfg N, ℝ) :=
  mode (stateK (NeZero.ne N) k) (screen Wf k s j)

/-- **The Rényi-½ count of the observer's screen**. DERIVED: no numeral. -/
def apRenyi (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) : ℝ := spRenyi (apEig Wf k s j)

/-- The measured count is `exp H` of the same spectrum. DERIVED: no numeral. -/
theorem apDim_eq (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) :
    apDim Wf k s j = spDim (apEig Wf k s j) := rfl

/-- DERIVED: `0` the sign. -/
theorem apEig_nonneg (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) (α : Fin 4 → Fin (apL N k s)) :
    0 ≤ apEig Wf k s j α :=
  eig_nonneg _ _ α

/-- The aperture box is nonempty. DERIVED: `0` the sign. -/
theorem apL_pos {k : ℕ} {s : ℝ} (hs : 0 < s) : 0 < apL N k s :=
  Nat.ceil_pos.2 (div_pos hs (dySpacing_pos (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)) k))

/-- **Every screen reading has the moments of the reading** (translation invariance of `ν_k`,
`ContinuumNontrivial.stateK_transObs`). DERIVED: no numeral. -/
theorem state_screen_pow (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) (y : Fin 4 → Fin (apL N k s))
    (q : ℕ) :
    stateK (NeZero.ne N) k (screen Wf k s j y ^ q) = stateK (NeZero.ne N) k (msFlow Wf k s j ^ q) := by
  simp only [screen]
  rw [← transObs_pow, MassGap.ContinuumNontrivial.stateK_transObs]

/-- **The screen reads on the translated aperture**: the reading at the box site `y` is a function of the
links of `aperture Wf k s j` moved by `y`. DERIVED: no numeral. -/
theorem screen_readsOn (Wf : ℝ → ConfFlow N) (k : ℕ) (s : ℝ) (j : MIx) (y : Fin 4 → Fin (apL N k s)) :
    ReadsOn ((fun l : ILink => (l.1, l.2 + apSite y)) '' aperture Wf k s j) (screen Wf k s j y) := by
  intro U U' h
  show msFlow Wf k s j (transConf (apSite y) U) = msFlow Wf k s j (transConf (apSite y) U')
  exact msFlow_readsOn Wf k s j _ _ fun l hl => h _ ⟨l, hl, rfl⟩

/-- **The observer's reading: every even moment from its variance and the count**: per-mode
hypercontractivity `ν_k(e_α^{2p}) ≤ K λ_α^p` gives `ν_k(msFlow^{2p}) ≤ K (R ν_k(msFlow²))^p`.
DERIVED: `2` the even power and the variance; `0` the signs. -/
theorem msFlow_moment_le_renyi {Wf : ℝ → ConfFlow N} {k : ℕ} {s : ℝ} (hs : 0 < s) (j : MIx) {p : ℕ}
    {K : ℝ} (hK : 0 ≤ K)
    (h1 : ∀ α, stateK (NeZero.ne N) k (apMode Wf k s j α ^ (2 * p)) ≤ K * apEig Wf k s j α ^ p) :
    stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
      ≤ K * (apRenyi Wf k s j * stateK (NeZero.ne N) k (msFlow Wf k s j ^ 2)) ^ p := by
  haveI : Nonempty (Fin (apL N k s)) := ⟨⟨0, apL_pos hs⟩⟩
  exact state_pow_le_renyi (stateK (NeZero.ne N) k) (screen Wf k s j) hK
    (fun y q => state_screen_pow Wf k s j y q) h1

end Lattice

/-! ## 6. The mechanism and the derivation -/

/-- **The aperture's count carries the moments** (module docstring, §6). H1 bounds the mode of every unit
eigenvector of the screen's Gram matrix, so it does not depend on the choice of eigenbasis.
DERIVED: `1` the limit of the ratio and the first level; `2` the even powers and the variances; `4` the
plaquette dimension and the spacetime dimension of the box; `8` the
dimension pair; `0` the signs and the point approached. -/
def ApertureCountAt [NeZero N] (b₀ : ℝ) (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ∃ (u : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < u ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop, ∀ (j : MIx) (p : ℕ) (lam : ℝ)
      (v : (Fin 4 → Fin (apL N k s)) → ℝ),
      IsUnitEig (gram (stateK (NeZero.ne N) k) (screen Wf k s j)) lam v →
      stateK (NeZero.ne N) k ((∑ y, v y • screen Wf k s j y) ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wickIx j * (C * lam) ^ p)
    ∧ (∀ j : MIx, ∃ σ : ℝ, 0 < σ ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop,
        stateK (NeZero.ne N) k (msFlow Wf k s j ^ 2) ≤ (σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ 2)
    ∧ (∃ σP E : ℝ, 0 < σP ∧ ∀ᶠ k in atTop, ∀ q : MassGap.GibbsSpec.IPlaq,
        |stateK (NeZero.ne N) k ((Wf b).fieldMap k (mField (Sum.inr q))).1| ≤ E * dySpacing N k ^ 4
        ∧ stateK (NeZero.ne N) k (msFlow Wf k b (Sum.inr q) ^ 2) ≤ σP ^ 2)
    ∧ (∃ (D c a : ℝ) (r : ℕ), 0 < a ∧ a < 1 ∧ 0 ≤ c ∧ ∀ s : ℝ, 0 < s → s ≤ b → ∀ᶠ k in atTop,
        ∀ j : MIx, apDim Wf k s j ≤ D
          ∧ ∀ i : ℕ, (levelCount (apEig Wf k s j) a i : ℝ) ≤ c * apDim Wf k s j * ((i : ℝ) + 1) ^ r)
    ∧ ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G
        ∧ Tendsto (fun r => r ^ 8 * G r / (trTree N * runG b₀ u r ^ 2)) (𝓝[>] 0) (𝓝 1)

set_option linter.dupNamespace false in
/-- **The aperture count** at the one-loop coefficient of `SU(N)`. DERIVED: no numeral beyond `b0`'s. -/
def ApertureCount [NeZero N] (z : Chan → ℕ → ℝ) (b : ℝ) (Wf : ℝ → ConfFlow N) : Prop :=
  ApertureCountAt (MassGap.ClayStatement.b0 N) z b Wf

/-- The scalar step: a moment bound `f C^p (R m₂)^p` with `R ≤ R̄`, `m₂ ≤ X²` is at most
`f (√(max(C R̄, 1)) X)^{2p}`. DERIVED: `1` the floor; `2` the even power and the square. -/
theorem moment_chain {F2p f C R Rb m2 X : ℝ} {p : ℕ} (hf : 0 ≤ f) (hC : 0 ≤ C) (hR0 : 0 ≤ R)
    (hm0 : 0 ≤ m2) (h : F2p ≤ f * C ^ p * (R * m2) ^ p) (hR : R ≤ Rb) (hm : m2 ≤ X ^ 2) :
    F2p ≤ f * (Real.sqrt (max (C * Rb) 1) * X) ^ (2 * p) := by
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hRb0 : 0 ≤ Rb := hR0.trans hR
  have hstep : C * (R * m2) ≤ max (C * Rb) 1 * X ^ 2 := by
    calc C * (R * m2) ≤ C * (Rb * X ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hR hm hm0 hRb0) hC
      _ = (C * Rb) * X ^ 2 := by ring
      _ ≤ max (C * Rb) 1 * X ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) hX2
  have hM : 0 ≤ max (C * Rb) 1 := le_trans zero_le_one (le_max_right _ _)
  calc F2p ≤ f * C ^ p * (R * m2) ^ p := h
    _ = f * (C * (R * m2)) ^ p := by ring
    _ ≤ f * (max (C * Rb) 1 * X ^ 2) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hstep _) hf
    _ = f * (Real.sqrt (max (C * Rb) 1) * X) ^ (2 * p) := by
        rw [pow_mul, mul_pow (Real.sqrt _) X 2, Real.sq_sqrt hM]

/-- `wickIx` of a plaquette is `1`. DERIVED: `1` the index. -/
theorem wickIx_plaq (q : MassGap.GibbsSpec.IPlaq) : wickIx (Sum.inr q : MIx) = 1 := by
  simp [wickIx, mDim]

/-- **The count's bound from H3**: `R ≤ (c D (1 − a) ∑ (i + 1)^r a^i)²`. DERIVED: `2` the square. -/
theorem apRenyi_le [NeZero N] {Wf : ℝ → ConfFlow N} {k : ℕ} {s : ℝ} {j : MIx} {D c a : ℝ} {r : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 ≤ c) (hD : apDim Wf k s j ≤ D)
    (hlev : ∀ i : ℕ, (levelCount (apEig Wf k s j) a i : ℝ) ≤ c * apDim Wf k s j * ((i : ℝ) + 1) ^ r) :
    apRenyi Wf k s j ≤ (c * D * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ r * a ^ i) ^ 2 := by
  have h := spRenyi_le_of_levels (apEig_nonneg Wf k s j) ha0 ha1 hlev
  have hS0 : 0 ≤ ∑' i : ℕ, ((i : ℝ) + 1) ^ r * a ^ i :=
    tsum_nonneg fun i => mul_nonneg (by positivity) (pow_nonneg ha0.le i)
  have h1a : 0 ≤ 1 - a := by linarith
  have hpos : 0 ≤ c * spDim (apEig Wf k s j) * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ r * a ^ i :=
    mul_nonneg (mul_nonneg (mul_nonneg hc (spDim_pos _).le) h1a) hS0
  refine h.trans (pow_le_pow_left₀ hpos ?_ 2)
  have hD' : spDim (apEig Wf k s j) ≤ D := hD
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD' hc) h1a) hS0

/-- **The count carries the moments**: `ApertureCountAt` gives `ZoomFree.ApertureOneAt` at noise
`√(max(C R̄, 1)) σⱼ` and `√(max(C R̄, 1)) σP`. DERIVED: `1` the floor; `2` the even powers; `0` the signs. -/
theorem apertureOneAt_of_count [NeZero N] {b₀ : ℝ} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (hb : 0 < b) (h : ApertureCountAt b₀ z b Wf) : ApertureOneAt b₀ z b Wf := by
  obtain ⟨u, γ, γP, hu, ⟨C, hC, h1⟩, h2, ⟨σP, E, hσP, hobs⟩, ⟨D, c, a, r, ha0, ha1, hc, h3⟩, haf⟩ := h
  set Rb := (c * D * (1 - a) * ∑' i : ℕ, ((i : ℝ) + 1) ^ r * a ^ i) ^ 2 with hRb
  set lam0 := Real.sqrt (max (C * Rb) 1) with hlam0def
  have hlam0 : 0 < lam0 := Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  -- the per-site step at an aperture `s`, a channel `j` and a step `k`
  have step : ∀ (s : ℝ) (k : ℕ) (j : MIx) (p : ℕ) (X : ℝ), 0 < s →
      (∀ α, stateK (NeZero.ne N) k (apMode Wf k s j α ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wickIx j * (C * apEig Wf k s j α) ^ p) →
      apDim Wf k s j ≤ D →
      (∀ i : ℕ, (levelCount (apEig Wf k s j) a i : ℝ) ≤ c * apDim Wf k s j * ((i : ℝ) + 1) ^ r) →
      stateK (NeZero.ne N) k (msFlow Wf k s j ^ 2) ≤ X ^ 2 →
      stateK (NeZero.ne N) k (msFlow Wf k s j ^ (2 * p))
        ≤ ((2 * p).factorial : ℝ) ^ wickIx j * (lam0 * X) ^ (2 * p) := by
    intro s k j p X hs hk1 hkD hklev hk2
    have hf : (0 : ℝ) ≤ ((2 * p).factorial : ℝ) ^ wickIx j := by positivity
    have hK : 0 ≤ ((2 * p).factorial : ℝ) ^ wickIx j * C ^ p := mul_nonneg hf (pow_nonneg hC p)
    have hmom := msFlow_moment_le_renyi (Wf := Wf) (k := k) hs j hK fun α =>
      (hk1 α).trans_eq (by rw [mul_pow, mul_assoc])
    have hm0 : 0 ≤ stateK (NeZero.ne N) k (msFlow Wf k s j ^ 2) :=
      (stateK (NeZero.ne N) k).nonneg _ fun x => by simp only [ContinuousMap.pow_apply]; positivity
    exact moment_chain hf hC (sq_nonneg _) hm0 hmom (apRenyi_le ha0 ha1 hc hkD hklev) hk2
  refine ⟨u, γ, γP, hu, fun j => ?_, ⟨lam0 * σP, E, mul_pos hlam0 hσP, ?_⟩, haf⟩
  · obtain ⟨σ, hσ, hj⟩ := h2 j
    refine ⟨lam0 * σ, mul_pos hlam0 hσ, fun s hs hsb p => ?_⟩
    filter_upwards [h1 s hs hsb, hj s hs hsb, h3 s hs hsb] with k hk1 hk2 hk3
    have := step s k j p _ hs
      (fun α => hk1 j p _ _ (evec_isUnitEig (stateK (NeZero.ne N) k) (screen Wf k s j) α))
      (hk3 j).1 (hk3 j).2 hk2
    calc _ ≤ _ := this
      _ = ((2 * p).factorial : ℝ) ^ wickIx j
            * (lam0 * σ * runG b₀ u s ^ anom γ γP j / s ^ mDim j) ^ (2 * p) := by ring
  · filter_upwards [h1 b hb le_rfl, hobs, h3 b hb le_rfl] with k hk1 hko hk3 q
    obtain ⟨hmean, hk2⟩ := hko q
    refine ⟨hmean, fun m => ?_⟩
    have := step b k (Sum.inr q) m σP hb
      (fun α => hk1 _ m _ _ (evec_isUnitEig (stateK (NeZero.ne N) k) (screen Wf k b (Sum.inr q)) α))
      (hk3 _).1 (hk3 _).2 hk2
    rwa [wickIx_plaq, pow_one] at this

/-- `ApertureCountAt` gives `ZoomFree.ApertureSettlesAt` (`apertureSettlesAt_iff_one`). DERIVED: `0` the
sign. -/
theorem apertureSettlesAt_of_count [NeZero N] {b₀ : ℝ} {z : Chan → ℕ → ℝ} {b : ℝ} {Wf : ℝ → ConfFlow N}
    (hb : 0 < b) (h : ApertureCountAt b₀ z b Wf) : ApertureSettlesAt b₀ z b Wf :=
  apertureSettlesAt_iff_one.2 (apertureOneAt_of_count hb h)

/-- **The coincident-point core from the aperture count**: `ApertureCount z b Wf`, `b > 0` and `Wf b = W`
give `SubstrateCoreCL W z b Wf`. DERIVED: `2` the least colour count; `0` the sign. -/
theorem substrateCoreCL_of_apertureCount (hN2 : 2 ≤ N) [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ}
    {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b) (htop : Wf b = W) (h : ApertureCount z b Wf) :
    SubstrateCoreCL W z b Wf :=
  substrateCoreCL_of_aperture hN2 hb htop (apertureSettlesAt_of_count hb h)

end MassGap.ApertureCount

end

/-! ### The copy over a coupling family -/

namespace MassGap.ApertureCount

set_option Elab.async false in
set_option maxHeartbeats 0 in
#along_generalize_more MassGap.ContinuumSchwinger.dyBeta from
  MassGap.ApertureCount.substrateCoreCL_of_apertureCount

-- No copy mentions the source (every copy in `MassGap.CouplingGen.Along`, the new ones included).
run_cmd do
  let env ← Lean.getEnv
  let src := ``MassGap.ContinuumSchwinger.dyBeta
  let pre := `MassGap.CouplingGen.Along
  for (c, ci) in env.constants.map₂.toList do
    if pre.isPrefixOf c then
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      if used.contains src then
        throwError "copy {c} still mentions {src}"

end MassGap.ApertureCount

/-! ## 7. The root -/

noncomputable section

namespace MassGap.ApertureCount

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ClayStatement MassGap.ClayTreeG MassGap.ClayStatementG MassGap.FlowG Filter
open scoped Topology
open MassGap.FlowAlong (cpl)
open MassGap.CouplingTower (StrongEnd CouplingTower UVConverges)
open MassGap.CompositeLink (Φ0)
open MassGap.CompositesRen (OffMix)
open MassGap.ScaleLightCone (CoreInputsAlongWSL ZoomSettlesUV clayStatementOf_of_zoomSettles)

variable {N : ℕ} [NeZero N] [Fact (2 ≤ N)]

variable (N) in
/-- **The flow-side bundle along `βs` with the aperture count**: `ZoomFree.CoreInputsAlongWAP` with the copy
of `ApertureCount z b Wf` (H1–H3 and af) in place of the copy of `ApertureSettles z b Wf`, every other field
unchanged. DERIVED: `0` the signs. -/
def CoreInputsAlongWAC (βs : ℕ → ℝ) : Prop :=
  ∃ (W : ConfFlow N) (r : ℝ) (_ : (Φ0 W).PhysRange r)
    (zri zwe : ℕ → ℝ) (_ : ∀ k, zri k ≠ 0) (_ : ∀ k, zwe k ≠ 0) (μ : OffMix) (b : ℝ)
    (Wf : ℝ → ConfFlow N) (cf : CompositesBuild.Ix0 → ℝ → (MultiScaleAll.MIx →₀ ℝ)),
    0 < b ∧ Wf b = W
      ∧ CouplingGen.Along.ApertureCount.ApertureCount (cpl βs) (ZCanon.zFix N zri zwe) b Wf
      ∧ CouplingGen.Along.StrongExpand.ExpandStrong (cpl βs) Wf cf (ZCanon.zFix N zri zwe) μ
      ∧ CouplingGen.Along.ScaleLightCone.ZoomSettles (cpl βs) Wf cf
      ∧ CouplingGen.Along.FlowCovN.FlowCovLim (cpl βs) Wf cf
      ∧ CouplingGen.Along.WardFromLattice.FlowWard (cpl βs) Wf cf
      ∧ CouplingGen.Along.NondegFromProxy.ProxyNondeg (cpl βs) Wf cf
      ∧ CouplingGen.Along.ProxyGenLimN.ProxyGenLimGerm (cpl βs) W b Wf cf r
      ∧ ∃ ℓ : ℝ, 0 < ℓ
          ∧ CouplingGen.Along.NonGaussFromScale.ThreePointAtScale (cpl βs) (NeZero.ne N) ℓ

/-- **The aperture-count bundle gives the separated-zoom bundle** (the copy of
`substrateCoreCL_of_apertureCount` at `cpl βs`). DERIVED: `2` the least colour count. -/
theorem coreWSL_of_coreWAC {βs : ℕ → ℝ} (h : CoreInputsAlongWAC N βs) : CoreInputsAlongWSL N βs := by
  obtain ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf, hb, htop, hZ, hE, F⟩ := h
  exact ⟨W, r, hphys, zri, zwe, hri, hwe, μ, b, Wf, cf,
    CouplingGen.Along.ApertureCount.substrateCoreCL_of_apertureCount (cpl βs) (Fact.out : 2 ≤ N) hb htop hZ,
    hE, F⟩

/-- **The root at `SU(N)` from the strong end, the separated zoom and the aperture count**: `StrongEnd N`,
the settling window reading and `CoreInputsAlongWAC` along the towers near `0⁺` give
`ClayStatementOf (SU N)` (`ScaleLightCone.clayStatementOf_of_zoomSettles`, `coreWSL_of_coreWAC`).
DERIVED: `0` the limit `0⁺`. -/
theorem clayStatementOf_of_apertureCount (hS : StrongEnd N)
    (hUV : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id → ZoomSettlesUV N βs)
    (hF : ∀ᶠ u₀ in 𝓝[>] (0 : ℝ), ∀ βs : ℕ → ℝ, CouplingTower N u₀ βs id →
      CoreInputsAlongWAC N βs) :
    ClayStatementOf (MassGap.SUN.SU N) :=
  clayStatementOf_of_zoomSettles hS hUV (hF.mono fun _ h βs hT => coreWSL_of_coreWAC (h βs hT))

end MassGap.ApertureCount

end

#print axioms MassGap.ApertureCount.evec_rows
#print axioms MassGap.ApertureCount.evec_cols
#print axioms MassGap.ApertureCount.evec_gram_evec
#print axioms MassGap.ApertureCount.state_mode_mul
#print axioms MassGap.ApertureCount.eig_eq
#print axioms MassGap.ApertureCount.eig_nonneg
#print axioms MassGap.ApertureCount.sum_evec_smul_mode
#print axioms MassGap.ApertureCount.sum_eig
#print axioms MassGap.ApertureCount.evec_isUnitEig
#print axioms MassGap.ApertureCount.div_pow_sqrt
#print axioms MassGap.ApertureCount.state_pow_comb_le
#print axioms MassGap.ApertureCount.state_pow_le_renyi
#print axioms MassGap.ApertureCount.level_nonneg
#print axioms MassGap.ApertureCount.summable_level
#print axioms MassGap.ApertureCount.sqrt_le_tsum_level
#print axioms MassGap.ApertureCount.sum_sqrt_le_levels
#print axioms MassGap.ApertureCount.summable_shift_pow_geom
#print axioms MassGap.ApertureCount.spRenyi_le_of_levels
#print axioms MassGap.ApertureCount.spRenyi_const
#print axioms MassGap.ApertureCount.spRenyi_unbounded_at_bounded_spDim
#print axioms MassGap.ApertureCount.sgnB_mul_self
#print axioms MassGap.ApertureCount.cubeState_apply
#print axioms MassGap.ApertureCount.sum_cube_prod
#print axioms MassGap.ApertureCount.cube_walsh_mul
#print axioms MassGap.ApertureCount.walsh_mul_self
#print axioms MassGap.ApertureCount.cube_walsh_pow
#print axioms MassGap.ApertureCount.cubeRead_apply
#print axioms MassGap.ApertureCount.cube_cubeRead_pow
#print axioms MassGap.ApertureCount.cube_two
#print axioms MassGap.ApertureCount.cube_four
#print axioms MassGap.ApertureCount.no_uniform_fourth
#print axioms MassGap.ApertureCount.isUnitEig_diag
#print axioms MassGap.ApertureCount.wt_bounds
#print axioms MassGap.ApertureCount.cw_sq_injective
#print axioms MassGap.ApertureCount.wgram
#print axioms MassGap.ApertureCount.wcube_unitEig_pow
#print axioms MassGap.ApertureCount.wcube_H1
#print axioms MassGap.ApertureCount.wRead_apply
#print axioms MassGap.ApertureCount.wcube_pow
#print axioms MassGap.ApertureCount.sgnB_true
#print axioms MassGap.ApertureCount.sgnB_false
#print axioms MassGap.ApertureCount.factor_le
#print axioms MassGap.ApertureCount.factor_pos
#print axioms MassGap.ApertureCount.wcube_four_ge
#print axioms MassGap.ApertureCount.no_uniform_fourth_nondeg
#print axioms MassGap.ApertureCount.apDim_eq
#print axioms MassGap.ApertureCount.apEig_nonneg
#print axioms MassGap.ApertureCount.apL_pos
#print axioms MassGap.ApertureCount.state_screen_pow
#print axioms MassGap.ApertureCount.screen_readsOn
#print axioms MassGap.ApertureCount.msFlow_moment_le_renyi
#print axioms MassGap.ApertureCount.moment_chain
#print axioms MassGap.ApertureCount.wickIx_plaq
#print axioms MassGap.ApertureCount.apRenyi_le
#print axioms MassGap.ApertureCount.apertureOneAt_of_count
#print axioms MassGap.ApertureCount.apertureSettlesAt_of_count
#print axioms MassGap.ApertureCount.substrateCoreCL_of_apertureCount
#print axioms MassGap.CouplingGen.Along.ApertureCount.substrateCoreCL_of_apertureCount
#print axioms MassGap.ApertureCount.coreWSL_of_coreWAC
#print axioms MassGap.ApertureCount.clayStatementOf_of_apertureCount
