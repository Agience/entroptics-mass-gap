import Mathlib
import MassGap.ApertureFixed
import MassGap.GapL2
import MassGap.GaugeInstances

/-!
# MassGap.NonAbelianForget — why the aperture forgets in Yang–Mills and not in a massless field

The author's step 2. The observer's aperture is finite and fixed in physical units and reads an infinite
substrate. It forgets the far past geometrically when a bounded fraction of information passes per
slab (`ApertureFixed.reading_cluster`, `FiniteInformation`). Compactness of the gauge group does not
give this: 4D compact `U(1)` has a massless photon phase at weak coupling (Guth 1980; Fröhlich–Spencer
1982). What separates Yang–Mills is the non-abelian self-interaction: the field binds the long waves
that would carry memory into lumps of fixed physical size, so nothing long-range is left to carry the
past. In the author's words: a photon is an edge in space, a graviton an edge in time; massless, an edge
spans until an observation. A flux edge that costs nothing per unit length (perimeter law) carries
the past across any number of slabs; a flux edge that costs `σ > 0` per unit length (string tension,
area law, closed flux loops of fixed size) is suppressed like `e^{−σ · length}`, and the aperture
forgets at the rate `e^{−σ · slab}` per slab.

This module makes that a typed ingredient, proves the abelian obstruction in conditional form (a
protected sector, where one is present, forbids geometric forgetting; no declaration here shows that a
given `U(1)` reading has one), proves the group facts, and states the remaining analytic input exactly.

## 1. The abelian obstruction: a protected long-wave sector forbids geometric forgetting

`cov Ch s n g φ ω₀` is the reading-chain covariance of `ApertureFixed.reading_cluster`.

* `exp_beats_power`: `C ρⁿ < A / (n + 1)^p` for some `n`, whenever `A > 0`, `0 ≤ ρ < 1`.
* `not_exp_of_powerFloor`: a power floor `|cov n| ≥ A / (n + 1)^p` excludes every exponential bound
  `|cov n| ≤ C ρⁿ`, `ρ < 1`, by any route.
* `no_memory_of_powerFloor`: hence no minorisation `c > 0` with memory `(η, θ)`, `θ < 1`, in the regime
  of `reading_cluster`, describes that chain.
* `spectral_floor`, `not_exp_of_spectralWeight`: the mechanism of the floor. When the connected
  reading correlator dominates a transfer-matrix spectral integral `∫ e^{−E n} dμ(E)` and the spectral
  measure has weight `μ[0, 1/(n+1)] ≥ A/(n+1)^p` at low energy (no gap: a massless mode in the reading
  channel, protected in `U(1)` by gauge invariance), the correlator has the floor `e^{−1} A/(n+1)^p`.
* `not_uniform_exp_of_eigenFloor`: the zoom version. Readings whose covariance is at least `A λ_kⁿ`
  with `sup_k λ_k = 1` (a long-wave eigenvalue of the slab transfer tending to `1`) admit no
  exponential bound uniform in `k`.
* `eigen_le_contr` (`GapL2` form): a mean-zero eigenfunction of the slab kernel with eigenvalue `λ`
  forces every `L²` rate to be at least `|λ|`; `K2_not_uniform`: the two-state flux bit flipped with
  probability `1 − a` has no rate `< 1` uniform in `a < 1`.

## 2. Edges: cost per length gives memory; zero cost does not

* `EdgeExpansion Ch w`: two pasts that agree on their last `ℓ` slabs give next-slab laws whose
  difference is carried only by flux edges reaching back across the `ℓ` agreeing slabs; edges of length
  `ℓ + j` slabs carry total weight `w (ℓ + j)`.
* `edgeRate σ h slab = e^{−(σ − h) slab}`: the per-slab factor of an edge with tension `σ` (cost per unit
  length) and entropy `h` (log of the number of edge shapes per unit length).
* `memory_of_edgeExpansion`: weights `0 ≤ w j ≤ K qʲ`, `q < 1`, give `Memory (K/(1−q)) q`: geometric
  forgetting at the rate `q` per slab. `EdgeExpansion` is `ApertureFixed.Overlap` with the profile a
  tail sum, so this step is a geometric tail bound; the reading of `w` as flux-edge weights is the
  interpretation, not a declaration. `edgeRate_lt_one`: `q < 1` exactly when `σ > h`.
* `edge_regime`: `q ≤ 1/(4(K+1))` puts `(K/(1−q), q)` in the regime of `reading_cluster`.
* `edge_mass`: an aperture whose chains all have minorisation `c` and edge weights `≤ K qʲ` (the same
  `c, K, σ, h` at every zoom) has a mass `m > 0` in physical units, uniform in the zoom.
* `perimeter_blocks_edges`: a reading with a power floor (perimeter law, a free edge) admits no such
  edge bound. `edgeRate_self`: at zero net cost `σ = h` the factor is `1`.

## 3. The group side: no abelian direction for simple `G`

* `swapElt`, `swapElt_mem`: for `p ≠ q` the signed transposition is in `SU(n, 𝕜)` (`𝕜 = ℂ` or `ℝ`).
* `phaseElt_mem`: `diag(i at p, −i at q, 1 else) ∈ SU(N)`. `signElt_mem`: `diag(−1 at p, r, 1 else)`
  is in `SO(n)`.
* `commutant_SU`: a matrix commuting with all of `SU(N)` is scalar. `commutant_SO`: the same for
  `SO(n)`, `n ≥ 3`.
* `center_SU_finite`, `center_SO_finite`: the centre is finite (it lies in the `n`-th roots of unity).
  `noAbelianSector_SU`, `noAbelianSector_SO`.
* `su_no_invariant`: a traceless matrix invariant under `Ad(SU(N))` is zero — the adjoint of `SU(N)` has
  no invariant (abelian) direction. `so_no_invariant`: an antisymmetric real matrix invariant under
  `Ad(SO(n))`, `n ≥ 3`, is zero.
* `U1`: `U(1)` as `1 × 1` unitaries. `center_U1_infinite`: its centre is all of it and infinite
  (`not_noAbelianSector_U1`); `u1_invariant`: the generator `i` of `u(1)` is nonzero and `Ad`-invariant.
* `so2_invariant`: the generator of `so(2)` is nonzero and `Ad(SO(2))`-invariant (`SO(2) ≅ U(1)`).

Compact `Sp(n)` is not treated here.

## 4. The remaining analytic input

`ConfinedEdges A`: the aperture's reading chains have, at every zoom, minorisation `c > 0` and edge
weights `w_k j ≤ K e^{−(σ−h) slab j}` with `σ > h` and the same `(c, K, σ, h)` at every zoom, in the
regime of `reading_cluster`. `NonAbelianForgetting G A := NoAbelianSector G → ConfinedEdges A`: in
The author's terms, non-abelian self-interaction leaves no long-wave sector at the aperture scale — every
flux edge costs a fixed amount per unit length — hence geometric forgetting, uniform in the zoom.

* `mass_of_confinedEdges`: `ConfinedEdges A ⇒` one physical mass `m > 0`, uniform in the zoom.
* `confinedEdges_excludes_power`, `confinedEdges_excludes_eigen`: `ConfinedEdges A` excludes a
  protected sector of either kind.
* `mass_of_nonAbelianForgetting_SU`: for `SU(N)`, `N ≥ 1`, the input gives the mass.
* `nonAbelianForgetting_U1_vacuous`: at `U(1)` the input has a false premise and asserts nothing, as it
  must, since the 4D `U(1)` photon phase has a protected sector.

`NonAbelianForgetting` is a definition, not a theorem: nothing here proves it for the Wilson measure
of any group, and `A` is not tied to the Wilson measure of `G` by any declaration in this module. Its
content at 4D weak coupling, `σ > 0` uniform in the zoom, is confinement.

DERIVED (module-wide): `1` the top of every rate and the total mass of a probability measure; `0` the
empty window; `−1` the sign that makes a transposition determinant one; `i` the unit phase that
separates two diagonal entries of `SU(N)`; `4` in `edge_regime` the margin `(1 − q)² ≥ 9/16 > 1/4`;
`e^{−1}` from `E n ≤ 1` on the low-energy window `[0, 1/(n+1)]`.
-/

noncomputable section

namespace MassGap.NonAbelianForget

open MeasureTheory Filter Topology Matrix
open MassGap.ApertureFixed
open scoped NNReal

/-! ## 1. The abelian obstruction -/

section Obstruction

/-- An exponential eventually falls below any power floor.

DERIVED: `1` the shift that keeps `n + 1 > 0`; `1/2` an arbitrary rate in `(0, 1)` dominating `ρ`. -/
theorem exp_beats_power {A C ρ : ℝ} (hA : 0 < A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (p : ℕ) :
    ∃ n : ℕ, C * ρ ^ n < A / ((n : ℝ) + 1) ^ p := by
  rcases lt_or_ge C 0 with hC | hC
  · exact ⟨0, by simp; linarith⟩
  set r := max ρ (1 / 2) with hr
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr1 : r < 1 := max_lt hρ1 (by norm_num)
  have hrabs : |r| < 1 := by rw [abs_of_pos hr0]; exact hr1
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one p hrabs
  have ht' : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ p * r ^ (n + 1)) atTop (𝓝 0) :=
    ht.comp (tendsto_add_atTop_nat 1)
  have hpos : 0 < A * r / (C + 1) := by positivity
  obtain ⟨n, hn⟩ := (ht'.eventually (gt_mem_nhds hpos)).exists
  refine ⟨n, ?_⟩
  have hn' : ((n : ℝ) + 1) ^ p * r ^ n * r < A / (C + 1) * r := by
    have e : A * r / (C + 1) = A / (C + 1) * r := by ring
    rw [← e, mul_assoc, ← pow_succ]
    simpa [Nat.cast_add, Nat.cast_one] using hn
  have h3 : ((n : ℝ) + 1) ^ p * r ^ n < A / (C + 1) := lt_of_mul_lt_mul_right hn' hr0.le
  have hP : 0 < ((n : ℝ) + 1) ^ p := by positivity
  have hX0 : 0 ≤ ((n : ℝ) + 1) ^ p * r ^ n := by positivity
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have h4 : (C + 1) * (((n : ℝ) + 1) ^ p * r ^ n) < A := by
    have h5 := mul_lt_mul_of_pos_left h3 hC1
    have e2 : (C + 1) * (A / (C + 1)) = A := by field_simp
    rwa [e2] at h5
  have h1 : C * ρ ^ n ≤ C * r ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 (le_max_left _ _) n) hC
  rw [lt_div_iff₀ hP]
  have hrn : 0 ≤ r ^ n := pow_nonneg hr0.le n
  calc C * ρ ^ n * ((n : ℝ) + 1) ^ p ≤ C * r ^ n * ((n : ℝ) + 1) ^ p :=
        mul_le_mul_of_nonneg_right h1 hP.le
    _ ≤ (C + 1) * (((n : ℝ) + 1) ^ p * r ^ n) := by nlinarith
    _ < A := h4

variable {X : Type} [MeasurableSpace X]

/-- The reading-chain covariance of `reading_cluster`: `g` read on the slabs up to `s`, `φ` on slab
`s + n`, boundary path `ω₀`.

DERIVED: `0` the first slab; `1` the slab of `g`. -/
def cov (Ch : ReadingChain X) (s n : ℕ) (g : (ℕ → X) → ℝ) (φ : X → ℝ) (ω₀ : ℕ → X) : ℝ :=
  Ch.seg 0 (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀
    - Ch.seg 0 (s + 1 + n) g ω₀ * Ch.seg 0 (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀

/-- **A power floor excludes every exponential bound.** If `|cov n| ≥ A/(n+1)^p` at every slab
distance `n`, no `C` and `0 ≤ ρ < 1` give `|cov n| ≤ C ρⁿ` for all `n`.

DERIVED: no numeral beyond `exp_beats_power`'s. -/
theorem not_exp_of_powerFloor {Ch : ReadingChain X} {s : ℕ} {g : (ℕ → X) → ℝ} {φ : X → ℝ}
    {ω₀ : ℕ → X} {A : ℝ} {p : ℕ} (hA : 0 < A)
    (hfloor : ∀ n : ℕ, A / ((n : ℝ) + 1) ^ p ≤ |cov Ch s n g φ ω₀|) :
    ¬ ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n : ℕ, |cov Ch s n g φ ω₀| ≤ C * ρ ^ n := by
  rintro ⟨C, ρ, hρ0, hρ1, hb⟩
  obtain ⟨n, hn⟩ := exp_beats_power (C := C) hA hρ0 hρ1 p
  linarith [hfloor n, hb n]

/-- **A protected sector forbids geometric forgetting.** A bounded reading pair with a power floor
admits no minorisation `c > 0` together with memory `(η, θ)`, `θ < 1`, in the regime of
`reading_cluster`.

DERIVED: `4` from `reading_cluster`. -/
theorem no_memory_of_powerFloor {Ch : ReadingChain X} {c η θ : ℝ} (hc : 0 < c) (hη : 0 ≤ η)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hsmall : η * θ < 1 - θ) (μ₀ : Measure X) {s : ℕ}
    {g : (ℕ → X) → ℝ} {φ : X → ℝ} {G B : ℝ} (hg : BM g) (hgr : ReadsBelow (s + 1) g)
    (hG : ∀ ω, |g ω| ≤ G) (hφ : Measurable φ) (hB : ∀ x, |φ x| ≤ B) (ω₀ : ℕ → X) {A : ℝ} {p : ℕ}
    (hA : 0 < A) (hfloor : ∀ n : ℕ, A / ((n : ℝ) + 1) ^ p ≤ |cov Ch s n g φ ω₀|) :
    ¬ (Ch.Doeblin c μ₀ ∧ Ch.Memory η θ) := by
  rintro ⟨hD, hM⟩
  obtain ⟨ρ, hρ0, hρ1, hcl⟩ := reading_cluster hc hη hθ0 hθ1 hsmall
  exact not_exp_of_powerFloor hA hfloor
    ⟨4 * G * B, ρ, hρ0.le, hρ1, fun n => hcl Ch μ₀ hD hM s n g φ G B hg hgr hG hφ hB ω₀⟩

/-- **Low-energy spectral weight gives the floor.** For a finite spectral measure `μ` on energies
`E ≥ 0`, `e^{−1} μ[0, 1/(n+1)] ≤ ∫ e^{−E n} dμ(E)`.

DERIVED: `e^{−1}` from `E n ≤ n/(n+1) ≤ 1` on the window. -/
theorem spectral_floor (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) :
    Real.exp (-1) * μ.real {E : ℝ≥0 | (E : ℝ) ≤ 1 / ((n : ℝ) + 1)}
      ≤ ∫ E, Real.exp (-((E : ℝ) * n)) ∂μ := by
  set S := {E : ℝ≥0 | (E : ℝ) ≤ 1 / ((n : ℝ) + 1)} with hSdef
  have hS : MeasurableSet S := measurableSet_le NNReal.continuous_coe.measurable measurable_const
  have hcont : Continuous (fun E : ℝ≥0 => Real.exp (-((E : ℝ) * n))) :=
    Real.continuous_exp.comp ((NNReal.continuous_coe.mul continuous_const).neg)
  have hint : Integrable (fun E : ℝ≥0 => Real.exp (-((E : ℝ) * n))) μ := by
    refine Integrable.of_bound hcont.measurable.aestronglyMeasurable 1
      (Eventually.of_forall fun E => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-((E : ℝ) * n)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg E.2 (Nat.cast_nonneg n)))
      _ = 1 := Real.exp_zero
  have h1 : Real.exp (-1) * μ.real S ≤ ∫ E in S, Real.exp (-((E : ℝ) * n)) ∂μ := by
    refine setIntegral_ge_of_const_le_real hS (measure_ne_top μ S) (fun E hE => ?_) hint.integrableOn
    apply Real.exp_le_exp.mpr
    have hE' : (E : ℝ) ≤ 1 / ((n : ℝ) + 1) := hE
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hk : (E : ℝ) * ((n : ℝ) + 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hE' hpos.le
      rwa [one_div, inv_mul_cancel₀ hpos.ne'] at this
    have hE0 : (0 : ℝ) ≤ E := E.2
    nlinarith
  exact h1.trans (setIntegral_le_integral hint (Eventually.of_forall fun E => (Real.exp_pos _).le))

/-- **The protected sector from its spectral weight.** If the reading correlator dominates a
spectral integral whose measure has weight at least `A/(n+1)^p` below energy `1/(n+1)`, no
exponential bound holds.

DERIVED: `e^{−1}` from `spectral_floor`. -/
theorem not_exp_of_spectralWeight {Ch : ReadingChain X} {s : ℕ} {g : (ℕ → X) → ℝ} {φ : X → ℝ}
    {ω₀ : ℕ → X} (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hrep : ∀ n : ℕ, ∫ E, Real.exp (-((E : ℝ) * n)) ∂μ ≤ |cov Ch s n g φ ω₀|) {A : ℝ} {p : ℕ}
    (hA : 0 < A)
    (hlow : ∀ n : ℕ, A / ((n : ℝ) + 1) ^ p ≤ μ.real {E : ℝ≥0 | (E : ℝ) ≤ 1 / ((n : ℝ) + 1)}) :
    ¬ ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n : ℕ, |cov Ch s n g φ ω₀| ≤ C * ρ ^ n := by
  refine not_exp_of_powerFloor (A := Real.exp (-1) * A) (p := p) (mul_pos (Real.exp_pos _) hA)
    (fun n => ?_)
  have h := mul_le_mul_of_nonneg_left (hlow n) (Real.exp_pos (-1)).le
  rw [mul_div_assoc]
  exact h.trans ((spectral_floor μ n).trans (hrep n))

/-- **The zoom version: a long-wave eigenvalue tending to one.** If `f i n ≥ A λᵢⁿ` with `λᵢ ≥ 0`
and `sup λᵢ = 1`, no `C` and `0 ≤ ρ < 1` bound every `f i n` by `C ρⁿ`.

DERIVED: `1` the top of every rate. -/
theorem not_uniform_exp_of_eigenFloor {ι : Type*} (f : ι → ℕ → ℝ) (lam : ι → ℝ) {A : ℝ}
    (hA : 0 < A) (hfloor : ∀ i n, A * lam i ^ n ≤ f i n) (hsup : ∀ r < 1, ∃ i, r < lam i) :
    ¬ ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i n, f i n ≤ C * ρ ^ n := by
  rintro ⟨C, ρ, hρ0, hρ1, hb⟩
  obtain ⟨i, hi⟩ := hsup ρ hρ1
  have hl : 0 < lam i := lt_of_le_of_lt hρ0 hi
  have hq0 : 0 ≤ ρ / lam i := div_nonneg hρ0 hl.le
  have hq1 : ρ / lam i < 1 := (div_lt_one hl).2 hi
  have hK : 0 < A / (|C| + 1) := div_pos hA (by positivity)
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually
    (gt_mem_nhds hK)).exists
  have hLn : 0 < lam i ^ n := pow_pos hl n
  have hpow : ρ ^ n = (ρ / lam i) ^ n * lam i ^ n := by
    rw [div_pow]; field_simp
  have hx0 : 0 ≤ (ρ / lam i) ^ n := pow_nonneg hq0 n
  have h1 : C * ρ ^ n ≤ |C| * ρ ^ n :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hρ0 n)
  have hC1 : (0 : ℝ) < |C| + 1 := by positivity
  have h2 : (|C| + 1) * (ρ / lam i) ^ n < A := by
    have h5 := mul_lt_mul_of_pos_left hn hC1
    have e2 : (|C| + 1) * (A / (|C| + 1)) = A := by field_simp
    rwa [e2] at h5
  have h6 := mul_lt_mul_of_pos_right h2 hLn
  have h7 : 0 ≤ (ρ / lam i) ^ n * lam i ^ n := mul_nonneg hx0 hLn.le
  have h3 : |C| * ρ ^ n < A * lam i ^ n := by
    rw [hpow]; nlinarith [abs_nonneg C]
  linarith [hfloor i n, hb i n]

/-- **A slab-kernel eigenvalue bounds the `L²` rate from below.** A mean-zero `g` with
`‖g‖ > 0` and `K g = λ g` forces `|λ| ≤ r` for every `Contr π K r`.

DERIVED: no numeral. -/
theorem eigen_le_contr {α : Type*} [Fintype α] {π : α → ℝ} {K : Matrix α α ℝ} {r lam : ℝ}
    {g : α → ℝ} (hg : GapL2.mean π g = 0) (hpos : 0 < GapL2.nsq π g) (heig : K *ᵥ g = lam • g)
    (h : GapL2.Contr π K r) : |lam| ≤ r := by
  have e : GapL2.nsq π (K *ᵥ g) = lam ^ 2 * GapL2.nsq π g := by
    rw [heig]
    unfold GapL2.nsq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h2 := h.2 g hg
  rw [e] at h2
  have h3 : lam ^ 2 ≤ r ^ 2 := le_of_mul_le_mul_right h2 hpos
  have h4 := sq_le_sq.mp h3
  rwa [abs_of_nonneg h.1] at h4

/-- The flux bit `(1, −1)`. -/
def fluxBit : Fin 2 → ℝ := ![1, -1]

theorem K2_eigen (a : ℝ) : GapL2.K2 a *ᵥ fluxBit = (2 * a - 1) • fluxBit := by
  funext i
  fin_cases i <;>
    simp [GapL2.mulVec_apply', Fin.sum_univ_two, GapL2.K2_00, GapL2.K2_01, GapL2.K2_10,
      GapL2.K2_11, fluxBit] <;> ring

/-- **A protected flux bit has no uniform rate.** The two-state cell that flips the bit with
probability `1 − a` has no `L²` rate `r < 1` valid for every `a ∈ (1/2, 1)`.

DERIVED: `3/4` and `(r + 3)/4` two stay probabilities in `(1/2, 1)`. -/
theorem K2_not_uniform :
    ¬ ∃ r : ℝ, r < 1 ∧ ∀ a : ℝ, 1 / 2 < a → a < 1 → GapL2.Contr GapL2.pi2 (GapL2.K2 a) r := by
  rintro ⟨r, hr1, h⟩
  have hm : GapL2.mean GapL2.pi2 fluxBit = 0 := by
    simp [GapL2.mean, GapL2.pi2, Fin.sum_univ_two, fluxBit]
  have hn : 0 < GapL2.nsq GapL2.pi2 fluxBit := by
    simp [GapL2.nsq, GapL2.pi2, Fin.sum_univ_two, fluxBit]
  have hr0 : 0 ≤ r := (h (3 / 4) (by norm_num) (by norm_num)).1
  have ha1 : 1 / 2 < (r + 3) / 4 := by linarith
  have ha2 : (r + 3) / 4 < 1 := by linarith
  have := eigen_le_contr hm hn (K2_eigen _) (h _ ha1 ha2)
  rw [abs_of_nonneg (by linarith)] at this
  linarith

end Obstruction

/-! ## 2. Edges -/

section Edges

variable {X : Type} [MeasurableSpace X]

/-- **The edge expansion of the memory.** Two pasts agreeing on their last `ℓ ≥ 1` slabs give
next-slab laws with a common part of mass at least `1 − Σ_j w(ℓ + j)`: their difference is carried
by flux edges reaching back across the `ℓ` agreeing slabs, edges of length `ℓ + j` slabs having
total weight `w (ℓ + j)`.

DERIVED: `1` the least window and the total mass. -/
def EdgeExpansion (Ch : ReadingChain X) (w : ℕ → ℝ) : Prop :=
  ∀ t ℓ, 1 ≤ ℓ → ∀ ω ω' : ℕ → X, Agree t ℓ ω ω' → ∃ m r r' : Measure X, IsFiniteMeasure m ∧
    IsFiniteMeasure r ∧ IsFiniteMeasure r' ∧ Ch.κ t ω = m + r ∧ Ch.κ t ω' = m + r' ∧
      1 - ∑' j, w (ℓ + j) ≤ m.real Set.univ

/-- The per-slab factor of a flux edge with tension `σ` (cost per unit length) and shape entropy `h`
per unit length, across a slab of physical thickness `slab`: `e^{−(σ − h) slab}`.

DERIVED: no numeral. -/
def edgeRate (σ h slab : ℝ) : ℝ := Real.exp (-((σ - h) * slab))

theorem edgeRate_nonneg (σ h slab : ℝ) : 0 ≤ edgeRate σ h slab := (Real.exp_pos _).le

/-- `σ > h` and `slab > 0` give `edgeRate < 1`. -/
theorem edgeRate_lt_one {σ h slab : ℝ} (hσ : h < σ) (hs : 0 < slab) : edgeRate σ h slab < 1 :=
  by
    rw [edgeRate, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos (mul_pos (sub_pos.2 hσ) hs))

/-- **A free edge carries the past.** At zero net cost per length the per-slab factor is `1`.

DERIVED: `1 = e^0`. -/
theorem edgeRate_self (σ slab : ℝ) : edgeRate σ σ slab = 1 := by
  simp [edgeRate]

/-- The tail of weights dominated by `K qʲ` is at most `K/(1 − q) · q^ℓ`.

DERIVED: `1 − q` the geometric sum. -/
theorem tail_le_geom {w : ℕ → ℝ} {K q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ j, w j ≤ K * q ^ j) (ℓ : ℕ) : ∑' j, w (ℓ + j) ≤ K / (1 - q) * q ^ ℓ := by
  have hg : Summable (fun j : ℕ => K * q ^ ℓ * q ^ j) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hle : ∀ j, w (ℓ + j) ≤ K * q ^ ℓ * q ^ j := fun j => by
    rw [mul_assoc, ← pow_add]; exact hw _
  have hs : Summable (fun j => w (ℓ + j)) := Summable.of_nonneg_of_le (fun j => hw0 _) hle hg
  calc ∑' j, w (ℓ + j) ≤ ∑' j, K * q ^ ℓ * q ^ j := Summable.tsum_le_tsum hle hs hg
    _ = K * q ^ ℓ * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    _ = K / (1 - q) * q ^ ℓ := by ring

/-- **Edge cost per length gives memory.** Edge weights `0 ≤ w j ≤ K qʲ`, `q < 1`, give
`Memory (K/(1−q)) q`: geometric forgetting at the rate `q` per slab.

DERIVED: no numeral beyond `tail_le_geom`'s. -/
theorem memory_of_edgeExpansion {Ch : ReadingChain X} {w : ℕ → ℝ} {K q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hw0 : ∀ j, 0 ≤ w j) (hw : ∀ j, w j ≤ K * q ^ j) (hE : EdgeExpansion Ch w) :
    Ch.Memory (K / (1 - q)) q := by
  intro t ℓ hℓ ω ω' hω
  obtain ⟨m, r, r', hm, hr, hr', e, e', hM⟩ := hE t ℓ hℓ ω ω' hω
  exact ⟨m, r, r', hm, hr, hr', e, e', by linarith [tail_le_geom hq0 hq1 hw0 hw ℓ]⟩

/-- **A large enough cost is in the regime.** `0 ≤ q ≤ 1/(4(K+1))`, `K ≥ 0` give
`K/(1−q) · q < 1 − q`.

DERIVED: `4` the margin `K q < 1/4 < 9/16 ≤ (1 − q)²`. -/
theorem edge_regime {K q : ℝ} (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq : q ≤ 1 / (4 * (K + 1))) :
    K / (1 - q) * q < 1 - q := by
  have hK1 : (0 : ℝ) < 4 * (K + 1) := by positivity
  have hq' : q * (4 * (K + 1)) ≤ 1 := by rwa [le_div_iff₀ hK1] at hq
  have hq4 : q ≤ 1 / 4 := by nlinarith
  have h1q : 0 < 1 - q := by linarith
  have hKq : K * q < 1 / 4 := by nlinarith
  rw [div_mul_eq_mul_div, div_lt_iff₀ h1q]
  nlinarith

/-- **Confined edges give one physical mass, uniform in the zoom.** An aperture whose zoom-`k`
chains all have minorisation `c` and edge weights `0 ≤ w_k j ≤ K qʲ`, `q = edgeRate σ h slab`,
`σ > h`, with the same `(c, K, σ, h)` at every zoom and `(K/(1−q), q)` in the regime, has a mass
`m > 0` with `|Cov_k| ≤ 4 G B e^{−m n slab}` at every zoom.

DERIVED: `4` from `aperture_cluster`. -/
theorem edge_mass (A : ApertureReading) {c K σ h : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hσ : h < σ)
    (hsmall : K / (1 - edgeRate σ h A.slab) * edgeRate σ h A.slab < 1 - edgeRate σ h A.slab)
    (μ₀ : ℕ → Measure (Fin A.K → A.Y)) (w : ℕ → ℕ → ℝ) (hw0 : ∀ k j, 0 ≤ w k j)
    (hw : ∀ k j, w k j ≤ K * edgeRate σ h A.slab ^ j) (hD : ∀ k, (A.chain k).Doeblin c (μ₀ k))
    (hE : ∀ k, EdgeExpansion (A.chain k) (w k)) :
    ∃ m : ℝ, 0 < m ∧ ∀ (k s n : ℕ) (g : (ℕ → Fin A.K → A.Y) → ℝ) (φ : (Fin A.K → A.Y) → ℝ)
      (G B : ℝ), BM g → ReadsBelow (s + 1) g → (∀ ω, |g ω| ≤ G) → Measurable φ →
      (∀ x, |φ x| ≤ B) → ∀ ω₀ : ℕ → Fin A.K → A.Y,
        |(A.chain k).seg 0 (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀
          - (A.chain k).seg 0 (s + 1 + n) g ω₀
            * (A.chain k).seg 0 (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀|
          ≤ 4 * G * B * Real.exp (-(m * (n * A.slab))) := by
  have hq0 := edgeRate_nonneg σ h A.slab
  have hq1 := edgeRate_lt_one hσ A.slab_pos
  have hη : 0 ≤ K / (1 - edgeRate σ h A.slab) := div_nonneg hK (by linarith)
  exact aperture_cluster A hc hη hq0 hq1 hsmall μ₀ hD
    (fun k => memory_of_edgeExpansion hq0 hq1 (hw0 k) (hw k) (hE k))

/-- **A free edge (perimeter law) blocks the edge bound.** A bounded reading pair with a power floor
admits no minorisation `c > 0` with edge weights `≤ K qʲ`, `q < 1`, in the regime.

DERIVED: no numeral beyond `no_memory_of_powerFloor`'s. -/
theorem perimeter_blocks_edges {Ch : ReadingChain X} {c K q : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hsmall : K / (1 - q) * q < 1 - q) (μ₀ : Measure X)
    {w : ℕ → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw : ∀ j, w j ≤ K * q ^ j) {s : ℕ} {g : (ℕ → X) → ℝ}
    {φ : X → ℝ} {G B : ℝ} (hg : BM g) (hgr : ReadsBelow (s + 1) g) (hG : ∀ ω, |g ω| ≤ G)
    (hφ : Measurable φ) (hB : ∀ x, |φ x| ≤ B) (ω₀ : ℕ → X) {A : ℝ} {p : ℕ} (hA : 0 < A)
    (hfloor : ∀ n : ℕ, A / ((n : ℝ) + 1) ^ p ≤ |cov Ch s n g φ ω₀|) :
    ¬ (Ch.Doeblin c μ₀ ∧ EdgeExpansion Ch w) := by
  rintro ⟨hD, hE⟩
  have hη : 0 ≤ K / (1 - q) := div_nonneg hK (by linarith)
  exact no_memory_of_powerFloor hc hη hq0 hq1 hsmall μ₀ hg hgr hG hφ hB ω₀ hA hfloor
    ⟨hD, memory_of_edgeExpansion hq0 hq1 hw0 hw hE⟩

end Edges

/-! ## 3. The group side -/

section Commutant

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- `M` commutes with every element of `SU(n, 𝕜)` (`SU(n)` at `𝕜 = ℂ`, `SO(n)` at `𝕜 = ℝ`):
`M` is invariant under the adjoint action. -/
def Commutes (M : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ g ∈ Matrix.specialUnitaryGroup (Fin n) 𝕜, g * M = M * g

/-- The signed transposition: the permutation matrix of `(p q)` times `diag(−1 at p, 1 else)`.

DERIVED: `−1` makes the determinant one. -/
def swapElt (p q : Fin n) : Matrix (Fin n) (Fin n) 𝕜 :=
  (Equiv.swap p q).permMatrix 𝕜 * diagonal (fun j => if j = p then -1 else 1)

theorem swapElt_mem {p q : Fin n} (hpq : p ≠ q) :
    (swapElt p q : Matrix (Fin n) (Fin n) 𝕜) ∈ Matrix.specialUnitaryGroup (Fin n) 𝕜 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  constructor
  · rw [swapElt, StarMul.star_mul,Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      conjTranspose_permMatrix, diagonal_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((Equiv.swap p q)⁻¹.permMatrix 𝕜), ← permMatrix_mul, mul_inv_cancel,
      permMatrix_one, Matrix.one_mul, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    by_cases hj : j = p <;> simp [hj]
  · rw [swapElt, det_mul, det_permutation, Equiv.Perm.sign_swap hpq, det_diagonal]
    simp [Finset.prod_ite_eq']

theorem swapElt_apply {p q : Fin n} (hpq : p ≠ q) :
    (swapElt p q : Matrix (Fin n) (Fin n) 𝕜) p q = 1 := by
  rw [swapElt, mul_diagonal]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Ne.symm hpq]

theorem diag_entry {d : Fin n → 𝕜} {M : Matrix (Fin n) (Fin n) 𝕜}
    (h : diagonal d * M = M * diagonal d) (p q : Fin n) : d p * M p q = M p q * d q := by
  have := congrFun (congrFun h p) q
  rwa [diagonal_mul, mul_diagonal] at this

/-- **Equal diagonal entries.** A commuting `M` with vanishing off-diagonal entries has equal
diagonal entries: the signed transposition exchanges them. -/
theorem diag_eq_of_commutes {M : Matrix (Fin n) (Fin n) 𝕜} (hM : Commutes M)
    (hoff : ∀ i j, i ≠ j → M i j = 0) (p q : Fin n) : M p p = M q q := by
  by_cases hpq : p = q
  · rw [hpq]
  have hD : M = diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  have h := congrFun (congrFun (hM _ (swapElt_mem (𝕜 := 𝕜) hpq)) p) q
  rw [hD, mul_diagonal, diagonal_mul, swapElt_apply hpq] at h
  simp only [one_mul, mul_one] at h
  exact h.symm

/-- **The centre is finite** when every commuting matrix is scalar: a central element is `ω · 1`
with `ωⁿ = 1`.

DERIVED: `0` the index of the read-off entry; `1` the determinant. -/
theorem center_finite_of_scalar [NeZero n]
    (hsc : ∀ M : Matrix (Fin n) (Fin n) 𝕜, Commutes M →
      (∀ i j, i ≠ j → M i j = 0) ∧ ∀ p q, M p p = M q q) :
    (Subgroup.center (Matrix.specialUnitaryGroup (Fin n) 𝕜) :
      Set (Matrix.specialUnitaryGroup (Fin n) 𝕜)).Finite := by
  have hcomm : ∀ z ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin n) 𝕜),
      Commutes (z : Matrix (Fin n) (Fin n) 𝕜) := by
    intro z hz g hg
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨g, hg⟩)
  have hdiag : ∀ z ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin n) 𝕜),
      (z : Matrix (Fin n) (Fin n) 𝕜)
        = Matrix.diagonal (fun _ => (z : Matrix (Fin n) (Fin n) 𝕜) 0 0) := by
    intro z hz
    obtain ⟨hoff, heq⟩ := hsc _ (hcomm z hz)
    ext i j
    by_cases hij : i = j
    · subst hij; rw [diagonal_apply_eq]; exact heq i 0
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine Set.Finite.of_finite_image (f := fun z => (z : Matrix (Fin n) (Fin n) 𝕜) 0 0) ?_ ?_
  · refine (Polynomial.nthRootsFinset n (1 : 𝕜)).finite_toSet.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hn]
    have hdet : (z : Matrix (Fin n) (Fin n) 𝕜).det = 1 :=
      (Matrix.mem_specialUnitaryGroup_iff.mp z.2).2
    rw [hdiag z hz, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact hdet
  · intro z hz z' hz' h
    apply Subtype.ext
    have h' : (z : Matrix (Fin n) (Fin n) 𝕜) 0 0 = (z' : Matrix (Fin n) (Fin n) 𝕜) 0 0 := h
    calc (z : Matrix (Fin n) (Fin n) 𝕜)
        = Matrix.diagonal (fun _ => (z : Matrix (Fin n) (Fin n) 𝕜) 0 0) := hdiag z hz
      _ = Matrix.diagonal (fun _ => (z' : Matrix (Fin n) (Fin n) 𝕜) 0 0) := by rw [h']
      _ = z' := (hdiag z' hz').symm

end Commutant

section SU

variable {N : ℕ}

/-- `diag(i at p, −i at q, 1 else)`.

DERIVED: `i` a unit phase with `i ≠ −i`. -/
def phaseElt (p q : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal (fun j => (if j = p then Complex.I else 1) * (if j = q then -Complex.I else 1))

theorem phaseElt_mem {p q : Fin N} (hpq : p ≠ q) :
    phaseElt p q ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  constructor
  · rw [phaseElt, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext j
    by_cases hp : j = p
    · subst hp; simp [hpq, Complex.conj_I]
    · by_cases hq : j = q
      · subst hq; simp [hp, Complex.conj_I]
      · simp [hp, hq]
  · rw [phaseElt, det_diagonal, Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq']

/-- **The commutant of `SU(N)` is the scalars.** -/
theorem commutant_SU {M : Matrix (Fin N) (Fin N) ℂ} (hM : Commutes M) :
    (∀ i j, i ≠ j → M i j = 0) ∧ ∀ p q, M p p = M q q := by
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro p q hpq
    have h := diag_entry (hM _ (phaseElt_mem hpq)) p q
    simp only [hpq, Ne.symm hpq, if_true, if_false, mul_one, one_mul] at h
    have h2 : M p q * (2 * Complex.I) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h0 | h0
    · exact h0
    · exfalso
      rcases mul_eq_zero.mp h0 with h1 | h1
      · norm_num at h1
      · exact Complex.I_ne_zero h1
  exact ⟨hoff, diag_eq_of_commutes hM hoff⟩

/-- **The centre of `SU(N)` is finite.** -/
theorem center_SU_finite [NeZero N] :
    (Subgroup.center (MassGap.SUN.SU N) : Set (MassGap.SUN.SU N)).Finite :=
  center_finite_of_scalar (fun _ hM => commutant_SU hM)

/-- **The adjoint of `SU(N)` has no invariant direction.** A traceless matrix invariant under
`Ad(SU(N))` is zero; in particular `su(N)` has no `u(1)` factor.

DERIVED: `0` the trace. -/
theorem su_no_invariant [NeZero N] {X : Matrix (Fin N) (Fin N) ℂ} (htr : X.trace = 0)
    (hX : Commutes X) : X = 0 := by
  obtain ⟨hoff, heq⟩ := commutant_SU hX
  have hsum : X.trace = (N : ℂ) * X 0 0 := by
    have e : X.trace = ∑ _i : Fin N, X 0 0 := Finset.sum_congr rfl (fun i _ => heq i 0)
    rw [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h0 : X 0 0 = 0 := by
    rw [htr] at hsum
    rcases mul_eq_zero.mp hsum.symm with h | h
    · exact absurd h hN
    · exact h
  ext i j
  by_cases hij : i = j
  · subst hij; rw [heq i 0, h0]; rfl
  · rw [hoff i j hij]; rfl

end SU

section SO

variable {n : ℕ}

theorem exists_third (hn : 3 ≤ n) (p q : Fin n) : ∃ r : Fin n, r ≠ p ∧ r ≠ q := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {p, q} := fun r _ => by
    by_cases hrp : r = p
    · simp [hrp]
    · simp [h r hrp]
  have h1 := Finset.card_le_card hsub
  have h2 : ({p, q} : Finset (Fin n)).card ≤ 2 :=
    (Finset.card_insert_le p {q}).trans (by simp)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- `diag(−1 at p, −1 at r, 1 else)`, `p ≠ r`.

DERIVED: two `−1`s make the determinant one. -/
def signElt (p r : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun j => (if j = p then -1 else 1) * (if j = r then -1 else 1))

theorem signElt_mem {p r : Fin n} (hpr : p ≠ r) :
    signElt p r ∈ Matrix.specialUnitaryGroup (Fin n) ℝ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  constructor
  · rw [signElt, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext j
    by_cases hp : j = p
    · subst hp; simp [hpr]
    · by_cases hr : j = r
      · subst hr; simp [hp]
      · simp [hp, hr]
  · rw [signElt, det_diagonal, Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq']

/-- **The commutant of `SO(n)`, `n ≥ 3`, is the scalars.** -/
theorem commutant_SO (hn : 3 ≤ n) {M : Matrix (Fin n) (Fin n) ℝ} (hM : Commutes M) :
    (∀ i j, i ≠ j → M i j = 0) ∧ ∀ p q, M p p = M q q := by
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro p q hpq
    obtain ⟨r, hrp, hrq⟩ := exists_third hn p q
    have h := diag_entry (hM _ (signElt_mem (Ne.symm hrp))) p q
    simp only [Ne.symm hpq, Ne.symm hrp, Ne.symm hrq, if_true, if_false, mul_one] at h
    linarith
  exact ⟨hoff, diag_eq_of_commutes hM hoff⟩

/-- **The centre of `SO(n)`, `n ≥ 3`, is finite.** -/
theorem center_SO_finite (hn : 3 ≤ n) :
    (Subgroup.center (GaugeInstances.SO n) : Set (GaugeInstances.SO n)).Finite := by
  haveI : NeZero n := ⟨by omega⟩
  exact center_finite_of_scalar (fun _ hM => commutant_SO hn hM)

/-- **The adjoint of `SO(n)`, `n ≥ 3`, has no invariant direction**: an antisymmetric real matrix
invariant under `Ad(SO(n))` is zero. -/
theorem so_no_invariant (hn : 3 ≤ n) {X : Matrix (Fin n) (Fin n) ℝ} (hanti : Xᵀ = -X)
    (hX : Commutes X) : X = 0 := by
  obtain ⟨hoff, _⟩ := commutant_SO hn hX
  ext i j
  by_cases hij : i = j
  · subst hij
    have h : X i i = -X i i := congrFun (congrFun hanti i) i
    show X i i = 0
    linarith
  · rw [hoff i j hij]; rfl

/-- The generator of `so(2)`. -/
def J2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- **`SO(2)` is abelian: its generator is a nonzero `Ad`-invariant direction.** -/
theorem so2_invariant : J2 ≠ 0 ∧ J2ᵀ = -J2 ∧ Commutes J2 := by
  refine ⟨fun h => by simpa [J2] using congrFun (congrFun h 1) 0, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [J2]
  · intro g hg
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff'] at hg
    obtain ⟨hu, hdet⟩ := hg
    have e00 := congrFun (congrFun hu 0) 0
    have e01 := congrFun (congrFun hu 0) 1
    have e11 := congrFun (congrFun hu 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose] at e00 e01 e11
    rw [Matrix.det_fin_two] at hdet
    have hd : g 1 1 = g 0 0 ∧ g 0 1 = -g 1 0 := by
      have key : (g 1 1 - g 0 0) ^ 2 + (g 0 1 + g 1 0) ^ 2 = 0 := by nlinarith
      have h1 : (g 1 1 - g 0 0) ^ 2 = 0 := by nlinarith [sq_nonneg (g 1 1 - g 0 0), sq_nonneg (g 0 1 + g 1 0)]
      have h2 : (g 0 1 + g 1 0) ^ 2 = 0 := by nlinarith [sq_nonneg (g 1 1 - g 0 0), sq_nonneg (g 0 1 + g 1 0)]
      constructor
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1; linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2; linarith
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith [hd.1, hd.2]

end SO

section U1

/-- `U(1)` as the `1 × 1` unitaries. -/
abbrev U1 : Type := Matrix.unitaryGroup (Fin 1) ℂ

/-- The point `t + i √(1 − t²)` of the circle, `t ∈ [−1, 1]`, as a `1 × 1` unitary. -/
theorem circle_mem {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    diagonal (fun _ : Fin 1 => (⟨t, Real.sqrt (1 - t ^ 2)⟩ : ℂ)) ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext _
  have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hs := Real.mul_self_sqrt h0
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

/-- **The centre of `U(1)` is all of `U(1)` and is infinite.** -/
theorem center_U1_infinite : (Subgroup.center U1 : Set U1).Infinite := by
  let f : Set.Icc (-1 : ℝ) 1 → U1 := fun t => ⟨_, circle_mem t.2⟩
  haveI : Infinite (Set.Icc (-1 : ℝ) 1) := (Set.Icc_infinite (by norm_num)).to_subtype
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ ?_
  · intro t t' h
    have := congrArg (fun z : U1 => ((z : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re) h
    simp [f] at this
    exact Subtype.ext this
  · intro t
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Matrix (Fin 1) (Fin 1) ℂ) * (f t : Matrix (Fin 1) (Fin 1) ℂ)
      = (f t : Matrix (Fin 1) (Fin 1) ℂ) * (g : Matrix (Fin 1) (Fin 1) ℂ)
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]

/-- **`u(1)` is an invariant abelian direction**: the generator `i` is nonzero, anti-hermitian, and
commutes with every element of `U(1)`. -/
theorem u1_invariant :
    let X : Matrix (Fin 1) (Fin 1) ℂ := diagonal (fun _ => Complex.I)
    X ≠ 0 ∧ Xᴴ = -X ∧ ∀ g ∈ Matrix.unitaryGroup (Fin 1) ℂ, g * X = X * g := by
  intro X
  refine ⟨fun h => Complex.I_ne_zero (by simpa [X] using congrFun (congrFun h 0) 0), ?_, ?_⟩
  · rw [diagonal_conjTranspose]
    ext i j; fin_cases i; fin_cases j; simp [X, Complex.conj_I]
  · intro g _
    ext i j; fin_cases i; fin_cases j
    simp [X, Matrix.mul_apply, mul_comm]

end U1

/-! ## 4. The remaining analytic input -/

/-- **No abelian sector**: the centre of `G` is finite. Holds at `SU(N)` and `SO(n)`, `n ≥ 3`;
fails at `U(1)`. DERIVED: no numeral in the definition; `n ≥ 3` the hypothesis of
`center_SO_finite` (`SO(2)` is abelian). -/
def NoAbelianSector (G : Type) [Group G] : Prop := (Subgroup.center G : Set G).Finite

theorem noAbelianSector_SU (N : ℕ) [NeZero N] : NoAbelianSector (MassGap.SUN.SU N) :=
  center_SU_finite

theorem noAbelianSector_SO {n : ℕ} (hn : 3 ≤ n) : NoAbelianSector (GaugeInstances.SO n) :=
  center_SO_finite hn

theorem not_noAbelianSector_U1 : ¬ NoAbelianSector U1 := center_U1_infinite

/-- **Confined edges at the aperture**: one minorisation `c > 0` and one edge bound
`w_k j ≤ K · edgeRate σ h slab ^ j`, `σ > h`, at every zoom, in the regime of `reading_cluster`.

DERIVED: `0`, `1` the positivity and the regime of `reading_cluster`. -/
def ConfinedEdges (A : ApertureReading) : Prop :=
  ∃ (c K σ h : ℝ) (μ₀ : ℕ → Measure (Fin A.K → A.Y)) (w : ℕ → ℕ → ℝ), 0 < c ∧ 0 ≤ K ∧ h < σ ∧
    K / (1 - edgeRate σ h A.slab) * edgeRate σ h A.slab < 1 - edgeRate σ h A.slab ∧
    (∀ k j, 0 ≤ w k j) ∧ (∀ k j, w k j ≤ K * edgeRate σ h A.slab ^ j) ∧
    ∀ k, (A.chain k).Doeblin c (μ₀ k) ∧ EdgeExpansion (A.chain k) (w k)

/-- **The remaining analytic input, in the author's terms**: non-abelian self-interaction (no abelian
sector) leaves no long-wave sector at the aperture scale — every flux edge costs a fixed amount per
unit length, uniformly in the zoom. As a definition `A` is an arbitrary `ApertureReading` and is not
tied to `G`; the intended instance is the aperture reading of the `G` Wilson measure, which no
declaration constructs. For a group with finite centre it is equivalent to `ConfinedEdges A`. Not
proved here for any `G`; at 4D weak coupling its content is confinement. -/
def NonAbelianForgetting (G : Type) [Group G] (A : ApertureReading) : Prop :=
  NoAbelianSector G → ConfinedEdges A

/-- The uniform constants of a confined aperture. -/
theorem uniform_of_confinedEdges {A : ApertureReading} (hA : ConfinedEdges A) :
    ∃ (c η θ : ℝ) (μ₀ : ℕ → Measure (Fin A.K → A.Y)), 0 < c ∧ 0 ≤ η ∧ 0 ≤ θ ∧ θ < 1 ∧
      η * θ < 1 - θ ∧ ∀ k, (A.chain k).Doeblin c (μ₀ k) ∧ (A.chain k).Memory η θ := by
  obtain ⟨c, K, σ, h, μ₀, w, hc, hK, hσ, hsmall, hw0, hw, hk⟩ := hA
  have hq0 := edgeRate_nonneg σ h A.slab
  have hq1 := edgeRate_lt_one hσ A.slab_pos
  exact ⟨c, K / (1 - edgeRate σ h A.slab), edgeRate σ h A.slab, μ₀, hc,
    div_nonneg hK (by linarith), hq0, hq1, hsmall,
    fun k => ⟨(hk k).1, memory_of_edgeExpansion hq0 hq1 (hw0 k) (hw k) (hk k).2⟩⟩

/-- **Confined edges give one physical mass, uniform in the zoom.**

DERIVED: `4` from `aperture_cluster`. -/
theorem mass_of_confinedEdges {A : ApertureReading} (hA : ConfinedEdges A) :
    ∃ m : ℝ, 0 < m ∧ ∀ (k s n : ℕ) (g : (ℕ → Fin A.K → A.Y) → ℝ) (φ : (Fin A.K → A.Y) → ℝ)
      (G B : ℝ), BM g → ReadsBelow (s + 1) g → (∀ ω, |g ω| ≤ G) → Measurable φ →
      (∀ x, |φ x| ≤ B) → ∀ ω₀ : ℕ → Fin A.K → A.Y,
        |(A.chain k).seg 0 (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀
          - (A.chain k).seg 0 (s + 1 + n) g ω₀
            * (A.chain k).seg 0 (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀|
          ≤ 4 * G * B * Real.exp (-(m * (n * A.slab))) := by
  obtain ⟨c, η, θ, μ₀, hc, hη, hθ0, hθ1, hsmall, hk⟩ := uniform_of_confinedEdges hA
  exact aperture_cluster A hc hη hθ0 hθ1 hsmall μ₀ (fun k => (hk k).1) (fun k => (hk k).2)

/-- **A protected power sector at some zoom**: a bounded reading pair whose covariance has a power
floor `A₀/(n+1)^p` at every slab distance. -/
def PowerSector (A : ApertureReading) : Prop :=
  ∃ (k s : ℕ) (g : (ℕ → Fin A.K → A.Y) → ℝ) (φ : (Fin A.K → A.Y) → ℝ) (G B : ℝ)
    (ω₀ : ℕ → Fin A.K → A.Y) (A₀ : ℝ) (p : ℕ), BM g ∧ ReadsBelow (s + 1) g ∧ (∀ ω, |g ω| ≤ G) ∧
    Measurable φ ∧ (∀ x, |φ x| ≤ B) ∧ 0 < A₀ ∧
    ∀ n : ℕ, A₀ / ((n : ℝ) + 1) ^ p ≤ |cov (A.chain k) s n g φ ω₀|

/-- **A protected long-wave sector across zooms**: bounded reading pairs `(g_k, φ_k)` with uniform
bounds whose covariance at zoom `k` is at least `A₀ λ_kⁿ`, with `sup λ_k = 1`. -/
def EigenSector (A : ApertureReading) : Prop :=
  ∃ (s : ℕ) (g : ℕ → (ℕ → Fin A.K → A.Y) → ℝ) (φ : ℕ → (Fin A.K → A.Y) → ℝ) (G B : ℝ)
    (ω₀ : ℕ → ℕ → Fin A.K → A.Y) (A₀ : ℝ) (lam : ℕ → ℝ), (∀ k, BM (g k)) ∧
    (∀ k, ReadsBelow (s + 1) (g k)) ∧ (∀ k ω, |g k ω| ≤ G) ∧ (∀ k, Measurable (φ k)) ∧
    (∀ k x, |φ k x| ≤ B) ∧ 0 < A₀ ∧ (∀ r < 1, ∃ k, r < lam k) ∧
    ∀ k n, A₀ * lam k ^ n ≤ |cov (A.chain k) s n (g k) (φ k) (ω₀ k)|

/-- **Confined edges exclude a protected power sector.** -/
theorem confinedEdges_excludes_power {A : ApertureReading} (hA : ConfinedEdges A) :
    ¬ PowerSector A := by
  rintro ⟨k, s, g, φ, G, B, ω₀, A₀, p, hg, hgr, hG, hφ, hB, hA₀, hfloor⟩
  obtain ⟨c, η, θ, μ₀, hc, hη, hθ0, hθ1, hsmall, hk⟩ := uniform_of_confinedEdges hA
  exact no_memory_of_powerFloor hc hη hθ0 hθ1 hsmall (μ₀ k) hg hgr hG hφ hB ω₀ hA₀ hfloor (hk k)

/-- **Confined edges exclude a protected long-wave sector across zooms.** -/
theorem confinedEdges_excludes_eigen {A : ApertureReading} (hA : ConfinedEdges A) :
    ¬ EigenSector A := by
  rintro ⟨s, g, φ, G, B, ω₀, A₀, lam, hg, hgr, hG, hφ, hB, hA₀, hsup, hfloor⟩
  obtain ⟨c, η, θ, μ₀, hc, hη, hθ0, hθ1, hsmall, hk⟩ := uniform_of_confinedEdges hA
  obtain ⟨ρ, hρ0, hρ1, hcl⟩ := reading_cluster hc hη hθ0 hθ1 hsmall
  exact not_uniform_exp_of_eigenFloor (fun k n => |cov (A.chain k) s n (g k) (φ k) (ω₀ k)|) lam
    hA₀ hfloor hsup ⟨4 * G * B, ρ, hρ0.le, hρ1, fun k n =>
      hcl (A.chain k) (μ₀ k) (hk k).1 (hk k).2 s n (g k) (φ k) G B (hg k) (hgr k) (hG k)
        (hφ k) (hB k) (ω₀ k)⟩

/-- **The input gives the mass at `SU(N)`.** -/
theorem mass_of_nonAbelianForgetting_SU (N : ℕ) [NeZero N] {A : ApertureReading}
    (hA : NonAbelianForgetting (MassGap.SUN.SU N) A) :
    ∃ m : ℝ, 0 < m ∧ ∀ (k s n : ℕ) (g : (ℕ → Fin A.K → A.Y) → ℝ) (φ : (Fin A.K → A.Y) → ℝ)
      (G B : ℝ), BM g → ReadsBelow (s + 1) g → (∀ ω, |g ω| ≤ G) → Measurable φ →
      (∀ x, |φ x| ≤ B) → ∀ ω₀ : ℕ → Fin A.K → A.Y,
        |(A.chain k).seg 0 (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀
          - (A.chain k).seg 0 (s + 1 + n) g ω₀
            * (A.chain k).seg 0 (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀|
          ≤ 4 * G * B * Real.exp (-(m * (n * A.slab))) :=
  mass_of_confinedEdges (hA (noAbelianSector_SU N))

/-- **At `SU(N)` the input excludes every protected sector.** -/
theorem nonAbelianForgetting_SU_no_sector (N : ℕ) [NeZero N] {A : ApertureReading}
    (hA : NonAbelianForgetting (MassGap.SUN.SU N) A) : ¬ PowerSector A ∧ ¬ EigenSector A :=
  ⟨confinedEdges_excludes_power (hA (noAbelianSector_SU N)),
    confinedEdges_excludes_eigen (hA (noAbelianSector_SU N))⟩

/-- **At `U(1)` the input asserts nothing**: its premise is false, so it holds for every aperture,
including one with a protected photon sector. -/
theorem nonAbelianForgetting_U1_vacuous (A : ApertureReading) : NonAbelianForgetting U1 A :=
  fun h => absurd h not_noAbelianSector_U1

#print axioms exp_beats_power
#print axioms no_memory_of_powerFloor
#print axioms not_exp_of_spectralWeight
#print axioms not_uniform_exp_of_eigenFloor
#print axioms K2_not_uniform
#print axioms memory_of_edgeExpansion
#print axioms edge_regime
#print axioms edge_mass
#print axioms perimeter_blocks_edges
#print axioms center_SU_finite
#print axioms su_no_invariant
#print axioms center_SO_finite
#print axioms so_no_invariant
#print axioms so2_invariant
#print axioms center_U1_infinite
#print axioms u1_invariant
#print axioms mass_of_confinedEdges
#print axioms confinedEdges_excludes_power
#print axioms confinedEdges_excludes_eigen
#print axioms mass_of_nonAbelianForgetting_SU
#print axioms nonAbelianForgetting_SU_no_sector
#print axioms nonAbelianForgetting_U1_vacuous

end MassGap.NonAbelianForget
