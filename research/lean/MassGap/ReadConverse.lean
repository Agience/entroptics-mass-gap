import Mathlib
import MassGap.SpectralGap

/-!
# A converse of the read chain: a fast enough contraction on the vacuum complement clears every read

`SpectralGap.gap_of_reads` turns `ReadsClear a Ω k` into a contraction of the vacuum complement at
`ρ = cap^{1/(k+1)}`, `cap = 12(1 − 3^{−1/4})/8`. This module proves a converse at a faster rate.
Let `a` be self-adjoint with spectrum in `[0, 1]`, `a Ω = Ω`, `0 ≤ r`, and `‖a u‖ ≤ r ‖u‖` for every
`u` orthogonal to `Ω`. If the single-mode read at `r` clears the floor,

    3^{−1/4} < modeCosAvg k r = (∑_d r^{c_d} cos(2π c_d / n)) / (∑_d r^{c_d}),
    c_d = circLag d,   n = 2(k + 1),

then `ReadsClear a Ω k` (`readsClear_of_contraction`). The literal converse at `ρ` is false: a
contraction whose complement is the single eigenvalue `ρ` has a read with cosine average
`modeCosAvg k ρ`, which is `0.470, 0.250, 0.214, 0.203` at `k = 0, 1, 3, 255` (computed, not proved
here), below `3^{−1/4} ≈ 0.760`.

How.

* Support (`ae_le_of_contraction`). For `v ⊥ Ω` with spectral measure `w`, the vector `u = φ(a) v`,
  `φ(t) = max 0 (t − r)`, is orthogonal to `Ω` (`SpectralRep.cfc_apply_of_fixed`), and
  `‖a u‖² − r² ‖u‖² = ∫ φ(t)² (t² − r²) dw` is at most `0` while its integrand is nonnegative and
  positive above `r`. So `w` puts no mass above `r`.
* Mixture. A read of `v` has correlation `ρ(d) = ∫ t^{c_d} dw`, so `∑ ρ = ∫ modeMass k t dw` and
  `∑ ρ(d) cos θ_d = ∫ modeCos k t dw`.
* Chebyshev (`cheb_sum`, `modeCos_mul_modeMass_le`, `modeCosAvg_antitone`). For `0 ≤ t ≤ s`,
  `modeCos k s · modeMass k t ≤ modeCos k t · modeMass k s`: twice the difference is
  `∑_{d,e} (t^{c_d} s^{c_e} − s^{c_d} t^{c_e})(cos θ_d − cos θ_e)`, and each term is nonnegative
  because `cos(2π c / n)` falls on `c ∈ [0, n/2]` (`cos_circ_antitone`). Integrated over the support
  `[0, r]`, the cosine average of `v` is at least `modeCosAvg k r`.

Explicit sufficient conditions. `cos x ≥ 1 − x²/2`, `(1 − r)³ ∑_j r^j j² ≤ r(1 + r)` for
`0 ≤ r ≤ 1` (the closed form `one_sub_cube_mul_sum_sq_pow`, in `modeSq_le`) and
`(1 − r) · modeMass k r ≥ 1 − r^{k+1}` give (`modeCosAvg_gt_of_bound`)

    4π² r(1 + r) < (1 − 3^{−1/4}) · n² · (1 − r)² · (1 − r^{k+1})   ⟹   3^{−1/4} < modeCosAvg k r.

With `r ≤ e^{−X/n}`, the bound `x ≤ sinh x` gives `X² r ≤ n² (1 − r)²`, and `r^{k+1} ≤ e^{−X/2}`;
the condition then follows from the aperture-free `8π² < (1 − 3^{−1/4}) X² (1 − e^{−X/2})`
(`cond_of_rate`), which `X = 20` satisfies (`twenty_clears`). At a window of physical extent
`L = n · sp`, a contraction of the vacuum complement at physical rate `−log r / sp ≥ 20/L` gives
`ReadsClear` (`readsClear_of_physical_rate` at `X = 20`, `twenty_clears`).

A bracket at one window (`readsClear_brackets_physical_gap`), with
`κ* = −2·log(12(1 − 3^{−1/4})/8) ≈ 2.042` (`SpectralGap.physical_gap_of_reads`): a physical gap of
at least `20/L` gives the reads, and the reads give a physical gap of at least `κ*/L`: the two
thresholds are a factor `20/κ* ≈ 9.8` apart, and between them the reads are not decided.

The `20` is not sharp. The aperture-free condition holds exactly for `X` above `18.1328…`, the root
of `8π² = (1 − 3^{−1/4}) X² (1 − e^{−X/2})`. The single-mode criterion itself,
`3^{−1/4} < modeCosAvg k (e^{−X/n})`, holds from `X = 9.94, 10.69, 10.97, 10.9885` at
`n = 8, 16, 64, 512`, rising to `10.98875`; those values are computed by direct summation, not
proved here.
-/

namespace MassGap.ReadConverse

open MeasureTheory MassGap.SpectralRep MassGap.SpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## The single mode at aperture `2k + 1` -/

/-- The single-mode normalisation at aperture `2k + 1`: `∑_d t^{circLag d}` over the `2(k + 1)`
lags.

DERIVED: `2` and the first `1` spell the aperture `2k + 1`; the second `1` is the `+ 1` of the lag
index type `Fin (N + 1)`. -/
noncomputable def modeMass (k : ℕ) (t : ℝ) : ℝ :=
  ∑ d : Fin (2 * k + 1 + 1), t ^ Moment.circLag d

/-- The single-mode cosine sum at aperture `2k + 1`:
`∑_d t^{circLag d} · cos(2π · circLag d / ((2k + 1) + 1))`. The cosine is the read's own
`cos (R.θ d)` (`Moment.Read.cos_theta_circ`).

DERIVED: `2 * π` is the full turn; `2` and the first `1` spell the aperture `2k + 1`; each remaining
`1` is the lag arity's `+ 1`. -/
noncomputable def modeCos (k : ℕ) (t : ℝ) : ℝ :=
  ∑ d : Fin (2 * k + 1 + 1),
    t ^ Moment.circLag d
      * Real.cos (2 * Real.pi * (Moment.circLag d : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1))

/-- The single-mode circle second moment at aperture `2k + 1`: `∑_d t^{circLag d} · (circLag d)²`.

DERIVED: `2` and the first `1` spell the aperture `2k + 1`, the second `1` is the lag arity's `+ 1`;
the exponent `2` is the second moment's. -/
noncomputable def modeSq (k : ℕ) (t : ℝ) : ℝ :=
  ∑ d : Fin (2 * k + 1 + 1), t ^ Moment.circLag d * (Moment.circLag d : ℝ) ^ 2

/-- The single-mode cosine average `modeCos k t / modeMass k t`: the cosine average of the read at
aperture `2k + 1` whose correlation is `t^{circLag d}` (`cosAvg_eq_modeCosAvg`).

DERIVED: no numeral occurs. -/
noncomputable def modeCosAvg (k : ℕ) (t : ℝ) : ℝ := modeCos k t / modeMass k t

/-- `modeMass k` is continuous.

DERIVED: no numeral occurs in the statement. -/
theorem continuous_modeMass (k : ℕ) : Continuous (modeMass k) := by
  show Continuous (fun t : ℝ => ∑ d : Fin (2 * k + 1 + 1), t ^ Moment.circLag d)
  exact continuous_finsetSum _ (fun d _ => continuous_pow (Moment.circLag d))

/-- `modeCos k` is continuous.

DERIVED: no numeral occurs in the statement. -/
theorem continuous_modeCos (k : ℕ) : Continuous (modeCos k) := by
  show Continuous (fun t : ℝ => ∑ d : Fin (2 * k + 1 + 1), t ^ Moment.circLag d
      * Real.cos (2 * Real.pi * (Moment.circLag d : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1)))
  exact continuous_finsetSum _
    (fun d _ => (continuous_pow (Moment.circLag d)).mul continuous_const)

/-- For `0 ≤ t`, `1 ≤ modeMass k t`: the lag `0` has `circLag 0 = 0` and contributes `t⁰ = 1`, and
every other term is nonnegative.

DERIVED: `1` is `t⁰`, the zero lag's term; `0` is the sign of `t`. -/
theorem one_le_modeMass (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ modeMass k t := by
  have hlag0 : Moment.circLag (0 : Fin (2 * k + 1 + 1)) = 0 := by simp [Moment.circLag]
  have h : t ^ Moment.circLag (0 : Fin (2 * k + 1 + 1))
      ≤ ∑ d : Fin (2 * k + 1 + 1), t ^ Moment.circLag d :=
    Finset.single_le_sum (f := fun d : Fin (2 * k + 1 + 1) => t ^ Moment.circLag d)
      (fun d _ => pow_nonneg ht _) (Finset.mem_univ _)
  rw [hlag0, pow_zero] at h
  exact h

/-- For `0 ≤ t`, `0 < modeMass k t` (`one_le_modeMass`).

DERIVED: `0` is the sign of `t` and the strict lower bound asserted. -/
theorem modeMass_pos (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < modeMass k t :=
  lt_of_lt_of_le one_pos (one_le_modeMass k ht)

#print axioms modeMass_pos

/-- **`modeCosAvg` is the single-mode read's cosine average.** For a read `R` at aperture `2k + 1`
whose correlation is `R.ρ d = t^{circLag d}`, `∑_d R.p d · cos (R.θ d) = modeCosAvg k t`.

DERIVED: `2` and `1` spell the aperture `2k + 1`. -/
theorem cosAvg_eq_modeCosAvg (k : ℕ) (t : ℝ) (R : Moment.Read (2 * k + 1))
    (hρ : ∀ d, R.ρ d = t ^ Moment.circLag d) :
    ∑ d, R.p d * Real.cos (R.θ d) = modeCosAvg k t := by
  have hsum : ∑ e, R.ρ e = ∑ e : Fin (2 * k + 1 + 1), t ^ Moment.circLag e :=
    Finset.sum_congr rfl (fun e _ => hρ e)
  unfold modeCosAvg modeCos modeMass
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  unfold Moment.Read.p
  rw [R.cos_theta_circ d, hρ d, hsum]
  ring

#print axioms cosAvg_eq_modeCosAvg

/-! ## Chebyshev: the single-mode cosine average falls with the mode -/

/-- **Chebyshev's sum inequality for a one-parameter family of weights.** Over a finite index set,
with `c : ι → ℕ` and `g : ι → ℝ` such that `c i ≤ c j` gives `g j ≤ g i`, and `0 ≤ t ≤ s`:

    (∑_i s^{c i} g i) · (∑_j t^{c j})  ≤  (∑_i t^{c i} g i) · (∑_j s^{c j}).

Twice the difference is `∑_{i,j} (t^{c i} s^{c j} − s^{c i} t^{c j})(g i − g j)`, and both factors
of each term have the same sign: for `c i ≤ c j`, `t^{c i} s^{c j} − s^{c i} t^{c j} =
(ts)^{c i}(s^{c j − c i} − t^{c j − c i}) ≥ 0` and `g i ≥ g j`.

DERIVED: `0` is the lower end of `t`. -/
theorem cheb_sum {ι : Type*} [Fintype ι] (c : ι → ℕ) (g : ι → ℝ)
    (hg : ∀ i j, c i ≤ c j → g j ≤ g i) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    (∑ i, s ^ c i * g i) * ∑ j, t ^ c j ≤ (∑ i, t ^ c i * g i) * ∑ j, s ^ c j := by
  have hs : 0 ≤ s := ht.trans hts
  -- one pair `(i, j)` against its mirror `(j, i)`
  have hpair : ∀ i j, 0 ≤ (t ^ c i * s ^ c j - s ^ c i * t ^ c j) * (g i - g j) := by
    intro i j
    rcases le_total (c i) (c j) with h | h
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
      have hx : s ^ c i * t ^ c j ≤ t ^ c i * s ^ c j := by
        rw [hm, pow_add t (c i) m, pow_add s (c i) m]
        have h1 : t ^ m ≤ s ^ m := pow_le_pow_left₀ ht hts m
        have h2 : 0 ≤ s ^ c i * t ^ c i := mul_nonneg (pow_nonneg hs _) (pow_nonneg ht _)
        calc s ^ c i * (t ^ c i * t ^ m) = (s ^ c i * t ^ c i) * t ^ m := by ring
          _ ≤ (s ^ c i * t ^ c i) * s ^ m := mul_le_mul_of_nonneg_left h1 h2
          _ = t ^ c i * (s ^ c i * s ^ m) := by ring
      exact mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr (hg i j h))
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
      have hx : t ^ c i * s ^ c j ≤ s ^ c i * t ^ c j := by
        rw [hm, pow_add t (c j) m, pow_add s (c j) m]
        have h1 : t ^ m ≤ s ^ m := pow_le_pow_left₀ ht hts m
        have h2 : 0 ≤ t ^ c j * s ^ c j := mul_nonneg (pow_nonneg ht _) (pow_nonneg hs _)
        calc t ^ c j * t ^ m * s ^ c j = (t ^ c j * s ^ c j) * t ^ m := by ring
          _ ≤ (t ^ c j * s ^ c j) * s ^ m := mul_le_mul_of_nonneg_left h1 h2
          _ = s ^ c j * s ^ m * t ^ c j := by ring
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx) (sub_nonpos.mpr (hg j i h))
  -- the difference of the two products is one double sum
  have hX : (∑ i, t ^ c i * g i) * ∑ j, s ^ c j - (∑ i, s ^ c i * g i) * ∑ j, t ^ c j
      = ∑ i, ∑ j, (t ^ c i * g i * s ^ c j - s ^ c i * g i * t ^ c j) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- the mirrored double sum is the same sum
  have hXX : ∑ i, ∑ j, (t ^ c j * g j * s ^ c i - s ^ c j * g j * t ^ c i)
      = ∑ i, ∑ j, (t ^ c i * g i * s ^ c j - s ^ c i * g i * t ^ c j) :=
    Finset.sum_comm
  -- the symmetrised terms are the pair products
  have hsplit : ∑ i, ∑ j, (t ^ c i * s ^ c j - s ^ c i * t ^ c j) * (g i - g j)
      = ∑ i, ∑ j, (t ^ c i * g i * s ^ c j - s ^ c i * g i * t ^ c j)
        + ∑ i, ∑ j, (t ^ c j * g j * s ^ c i - s ^ c j * g j * t ^ c i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have htot : 0 ≤ ∑ i, ∑ j, (t ^ c i * s ^ c j - s ^ c i * t ^ c j) * (g i - g j) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hpair i j))
  rw [hsplit, hXX, ← hX] at htot
  linarith

#print axioms cheb_sum

/-- The circle cosine falls with the circle distance: for lags `i`, `j` at aperture `2k + 1` with
`circLag i ≤ circLag j`, `cos(2π · circLag j / n) ≤ cos(2π · circLag i / n)`, `n = (2k + 1) + 1`.
Both angles lie in `[0, π]` because `2 · circLag ≤ n`, and cosine is antitone there
(`Real.cos_le_cos_of_nonneg_of_le_pi`).

DERIVED: `2 * π` is the full turn; `2` and `1` spell the aperture `2k + 1`, and the other `1` is the
lag arity's `+ 1`. -/
theorem cos_circ_antitone (k : ℕ) (i j : Fin (2 * k + 1 + 1))
    (h : Moment.circLag i ≤ Moment.circLag j) :
    Real.cos (2 * Real.pi * (Moment.circLag j : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1))
      ≤ Real.cos (2 * Real.pi * (Moment.circLag i : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1)) := by
  have hN : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) + 1 := by positivity
  have hhalf : 2 * Moment.circLag j ≤ 2 * k + 1 + 1 := by
    have := j.isLt
    unfold Moment.circLag
    omega
  have hhalfR : 2 * (Moment.circLag j : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhalf
  have hij : (Moment.circLag i : ℝ) ≤ (Moment.circLag j : ℝ) := by exact_mod_cast h
  have hpi := Real.pi_pos
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ hN]
    linarith [mul_le_mul_of_nonneg_left hhalfR hpi.le]
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hij (by positivity)) hN.le

/-- **The cross-multiplied single-mode comparison.** For `0 ≤ t ≤ s`,
`modeCos k s · modeMass k t ≤ modeCos k t · modeMass k s` (`cheb_sum` with `c = circLag` and
`g = cos(2π · circLag / n)`, antitone by `cos_circ_antitone`).

DERIVED: `0` is the lower end of `t`. -/
theorem modeCos_mul_modeMass_le (k : ℕ) {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    modeCos k s * modeMass k t ≤ modeCos k t * modeMass k s :=
  cheb_sum (Moment.circLag : Fin (2 * k + 1 + 1) → ℕ)
    (fun d => Real.cos (2 * Real.pi * (Moment.circLag d : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1)))
    (fun i j hij => cos_circ_antitone k i j hij) ht hts

#print axioms modeCos_mul_modeMass_le

/-- **The single-mode cosine average is antitone on `[0, ∞)`.** For `0 ≤ t ≤ s`,
`modeCosAvg k s ≤ modeCosAvg k t`: `modeCos_mul_modeMass_le` divided by the two positive
normalisations.

DERIVED: `0` is the lower end of the interval. -/
theorem modeCosAvg_antitone (k : ℕ) : AntitoneOn (modeCosAvg k) (Set.Ici 0) := by
  intro t ht s hs hts
  have ht0 : 0 ≤ t := ht
  have hs0 : 0 ≤ s := hs
  unfold modeCosAvg
  rw [div_le_div_iff₀ (modeMass_pos k hs0) (modeMass_pos k ht0)]
  exact modeCos_mul_modeMass_le k ht0 hts

#print axioms modeCosAvg_antitone

/-! ## A contraction on the vacuum complement confines every spectral measure -/

/-- The excess of `t` over `r`: `max 0 (t − r)`.

DERIVED: `0` is the floor of the excess. -/
noncomputable def excess (r t : ℝ) : ℝ := max 0 (t - r)

/-- `excess r` is continuous.

DERIVED: no numeral occurs in the statement. -/
theorem continuous_excess (r : ℝ) : Continuous (excess r) :=
  continuous_const.max (continuous_id.sub continuous_const)

/-- DERIVED: `0` is the floor of the excess. -/
theorem excess_eq_zero {r t : ℝ} (h : t ≤ r) : excess r t = 0 := by
  unfold excess
  exact max_eq_left (by linarith)

/-- DERIVED: no numeral occurs in the statement. -/
theorem excess_eq_sub {r t : ℝ} (h : r ≤ t) : excess r t = t - r := by
  unfold excess
  exact max_eq_right (by linarith)

/-- **A contraction on the vacuum complement confines every spectral measure below the rate.** For
`a` self-adjoint with spectrum in `[0, 1]`, `a Ω = Ω`, `0 ≤ r`, and `‖a u‖ ≤ r ‖u‖` for every `u`
orthogonal to `Ω`: every `v` orthogonal to `Ω`, with a finite measure `w` on `[0, 1]` representing
the functional calculus at `v`, has `t ≤ r` for `w`-almost every `t`.

DERIVED: `0` and `1` are the interval's ends; `0` is also the orthogonality and the lower end of
`r`. -/
theorem ae_le_of_contraction (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (r : ℝ) (hr0 : 0 ≤ r)
    (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖) (v : E) (hv : inner ℂ Ω v = 0)
    (w : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure w]
    (hw : ∀ h : ℝ → ℝ, Continuous h → RCLike.re (inner ℂ v (cfc h a v)) = ∫ t, h (t : ℝ) ∂w) :
    ∀ᵐ t : Set.Icc (0 : ℝ) 1 ∂w, (t : ℝ) ≤ r := by
  have hec := continuous_excess r
  -- the excess vector `u = φ(a) v` is orthogonal to `Ω`
  have hu : inner ℂ Ω (cfc (excess r) a v) = 0 := by
    have hsa : IsSelfAdjoint (cfc (excess r) a) := cfc_predicate _ a
    have hsym : inner ℂ (cfc (excess r) a Ω) v = inner ℂ Ω (cfc (excess r) a v) :=
      hsa.isSymmetric Ω v
    rw [← hsym, cfc_apply_of_fixed a ha hspec Ω hΩ _ hec,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, hv, mul_zero]
  -- `a u` is the functional calculus of `t · φ(t)`
  have hau : a (cfc (excess r) a v) = cfc (fun t : ℝ => t * excess r t) a v := by
    rw [cfc_mul (fun t : ℝ => t) (excess r) a continuous_id.continuousOn hec.continuousOn,
      cfc_id' ℝ a ha, ContinuousLinearMap.mul_apply]
  have hA : ‖a (cfc (excess r) a v)‖ ^ 2
      = ∫ t, ((t : ℝ) * excess r t) * ((t : ℝ) * excess r t) ∂w := by
    rw [hau, norm_sq_cfc a ha (fun t : ℝ => t * excess r t) (continuous_id.mul hec) v]
    exact hw (fun t : ℝ => (t * excess r t) * (t * excess r t))
      ((continuous_id.mul hec).mul (continuous_id.mul hec))
  have hB : ‖cfc (excess r) a v‖ ^ 2 = ∫ t, excess r t * excess r t ∂w := by
    rw [norm_sq_cfc a ha (excess r) hec v]
    exact hw (fun t : ℝ => excess r t * excess r t) (hec.mul hec)
  -- the contraction, squared
  have hsq : ‖a (cfc (excess r) a v)‖ ^ 2 ≤ r ^ 2 * ‖cfc (excess r) a v‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (hcon _ hu) 2
    rw [mul_pow] at h
    exact h
  rw [hA, hB] at hsq
  have hi1 : Integrable (fun t : Set.Icc (0 : ℝ) 1 =>
      ((t : ℝ) * excess r t) * ((t : ℝ) * excess r t)) w :=
    integrable_of_continuous w
      ((continuous_subtype_val.mul (hec.comp continuous_subtype_val)).mul
        (continuous_subtype_val.mul (hec.comp continuous_subtype_val)))
  have hi2 : Integrable (fun t : Set.Icc (0 : ℝ) 1 => excess r t * excess r t) w :=
    integrable_of_continuous w
      ((hec.comp continuous_subtype_val).mul (hec.comp continuous_subtype_val))
  have hFi : Integrable (fun t : Set.Icc (0 : ℝ) 1 =>
      ((t : ℝ) * excess r t) * ((t : ℝ) * excess r t) - r ^ 2 * (excess r t * excess r t)) w :=
    hi1.sub (hi2.const_mul (r ^ 2))
  -- the integrand `φ² (t² − r²)` is nonnegative
  have hF0 : ∀ t : Set.Icc (0 : ℝ) 1,
      0 ≤ ((t : ℝ) * excess r t) * ((t : ℝ) * excess r t) - r ^ 2 * (excess r t * excess r t) := by
    intro t
    rcases le_or_gt (t : ℝ) r with htr | htr
    · rw [excess_eq_zero htr]
      simp
    · rw [excess_eq_sub htr.le]
      have h1 : 0 < (t : ℝ) - r := sub_pos.mpr htr
      have h2 : 0 < (t : ℝ) + r := by linarith
      linarith [mul_pos (mul_pos h1 h1) (mul_pos h1 h2)]
  -- and its integral is at most `0`, so it vanishes almost everywhere
  have hint : ∫ t, (((t : ℝ) * excess r t) * ((t : ℝ) * excess r t)
      - r ^ 2 * (excess r t * excess r t)) ∂w = 0 := by
    apply le_antisymm
    · rw [integral_sub hi1 (hi2.const_mul (r ^ 2)), integral_const_mul]
      linarith
    · exact integral_nonneg hF0
  have hae := (integral_eq_zero_iff_of_nonneg (f := fun t : Set.Icc (0 : ℝ) 1 =>
      ((t : ℝ) * excess r t) * ((t : ℝ) * excess r t) - r ^ 2 * (excess r t * excess r t))
      hF0 hFi).mp hint
  filter_upwards [hae] with t ht
  have ht' : ((t : ℝ) * excess r t) * ((t : ℝ) * excess r t)
      - r ^ 2 * (excess r t * excess r t) = 0 := ht
  by_contra htr
  push_neg at htr
  rw [excess_eq_sub htr.le] at ht'
  have h1 : 0 < (t : ℝ) - r := sub_pos.mpr htr
  have h2 : 0 < (t : ℝ) + r := by linarith
  linarith [mul_pos (mul_pos h1 h1) (mul_pos h1 h2)]

#print axioms ae_le_of_contraction

/-! ## A converse at a faster rate -/

/-- **A fast enough contraction on the vacuum complement clears every read.** For `a` self-adjoint
with spectrum in `[0, 1]`, `a Ω = Ω`, `0 ≤ r`, `‖a u‖ ≤ r ‖u‖` for every `u` orthogonal to `Ω`, and
`3^{−1/4} < modeCosAvg k r` (the single-mode read at `r` clears the floor,
`cosAvg_eq_modeCosAvg`): `ReadsClear a Ω k`.

For `v` orthogonal to `Ω` with spectral measure `w`, `ae_le_of_contraction` puts `w` on `[0, r]`; a
read of `v` has `∑ ρ = ∫ modeMass k t dw` and `∑ ρ(d) cos θ_d = ∫ modeCos k t dw`, and
`modeCos_mul_modeMass_le` integrated over `[0, r]` puts the read's cosine average at or above
`modeCosAvg k r`.

DERIVED: `3`, `1` and `4` spell the floor's `3^{−1/4} = e^{−κ₀}`; `0` and `1` are the interval's
ends; `0` is also the orthogonality and the lower end of `r`. -/
theorem readsClear_of_contraction (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (r : ℝ) (hr0 : 0 ≤ r)
    (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖)
    (hmode : (3 : ℝ) ^ (-(1 : ℝ) / 4) < modeCosAvg k r) :
    ReadsClear a Ω k := by
  intro v hv R hR
  obtain ⟨w, hwfin, hw⟩ := exists_spectral_measure a ha hspec v
  have hsupp := ae_le_of_contraction a ha hspec Ω hΩ r hr0 hcon v hv w hw
  -- the correlation is the moment sequence of `w`
  have hmom : ∀ c : ℕ, RCLike.re (inner ℂ v ((a ^ c) v)) = ∫ t, (t : ℝ) ^ c ∂w := by
    intro c
    have h : RCLike.re (inner ℂ v (cfc (fun x : ℝ => x ^ c) a v)) = ∫ t, (t : ℝ) ^ c ∂w :=
      hw (fun x : ℝ => x ^ c) (continuous_pow c)
    rw [cfc_pow_id (R := ℝ) a c ha] at h
    exact h
  have hρ : ∀ d, R.ρ d = ∫ t, (t : ℝ) ^ Moment.circLag d ∂w := fun d => (hR d).trans (hmom _)
  have hD : ∑ d, R.ρ d = ∫ t, modeMass k (t : ℝ) ∂w := by
    unfold modeMass
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun d _ => hρ d)
    · intro d _
      exact integrable_of_continuous w (continuous_subtype_val.pow _)
  have hN : ∑ d, R.ρ d * Real.cos (R.θ d) = ∫ t, modeCos k (t : ℝ) ∂w := by
    unfold modeCos
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [hρ d, R.cos_theta_circ d, integral_mul_const]
    · intro d _
      exact (integrable_of_continuous w (continuous_subtype_val.pow _)).mul_const _
  have hS : 0 < ∑ d, R.ρ d := R.hpos
  have hDr : 0 < modeMass k r := modeMass_pos k hr0
  have hmode' : (3 : ℝ) ^ (-(1 : ℝ) / 4) * modeMass k r < modeCos k r := by
    have h := hmode
    unfold modeCosAvg at h
    rwa [lt_div_iff₀ hDr] at h
  -- the Chebyshev comparison, integrated over the support `[0, r]`
  have hcmp : modeCos k r * ∑ d, R.ρ d ≤ modeMass k r * ∑ d, R.ρ d * Real.cos (R.θ d) := by
    rw [hD, hN, ← integral_const_mul, ← integral_const_mul]
    refine integral_mono_ae ?_ ?_ ?_
    · exact (integrable_of_continuous w
        ((continuous_modeMass k).comp continuous_subtype_val)).const_mul _
    · exact (integrable_of_continuous w
        ((continuous_modeCos k).comp continuous_subtype_val)).const_mul _
    · filter_upwards [hsupp] with t ht
      have h := modeCos_mul_modeMass_le k t.2.1 ht
      linarith
  have hkey : (3 : ℝ) ^ (-(1 : ℝ) / 4) * ∑ d, R.ρ d < ∑ d, R.ρ d * Real.cos (R.θ d) := by
    by_contra hneg
    push_neg at hneg
    have h3 : modeMass k r * ∑ d, R.ρ d * Real.cos (R.θ d)
        ≤ modeMass k r * ((3 : ℝ) ^ (-(1 : ℝ) / 4) * ∑ d, R.ρ d) :=
      mul_le_mul_of_nonneg_left hneg hDr.le
    have h4 : (3 : ℝ) ^ (-(1 : ℝ) / 4) * modeMass k r * ∑ d, R.ρ d
        < modeCos k r * ∑ d, R.ρ d := mul_lt_mul_of_pos_right hmode' hS
    linarith
  have havg : ∑ d, R.p d * Real.cos (R.θ d)
      = (∑ d, R.ρ d * Real.cos (R.θ d)) / ∑ d, R.ρ d := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold Moment.Read.p
    ring
  have hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < ∑ d, R.p d * Real.cos (R.θ d) := by
    rw [havg, lt_div_iff₀ hS]
    exact hkey
  exact ⟨lt_trans (Real.rpow_pos_of_pos (by norm_num) _) hc, R.tension_lt_floor_of_cosAvg hc⟩

#print axioms readsClear_of_contraction

/-! ## An explicit lattice condition for the single mode -/

/-- `(1 − r) · ∑_{j < K} r^j = 1 − r^K`, by induction on `K`.

DERIVED: `1` is the geometric series' leading term. -/
theorem one_sub_mul_sum_pow (r : ℝ) (K : ℕ) :
    (1 - r) * ∑ j ∈ Finset.range K, r ^ j = 1 - r ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    linear_combination ih

/-- The weighted sum of squares in closed form:

    (1 − r)³ · ∑_{j < K} r^j j²  =  r(1 + r) − r^K ((1 − r)² K² + 2r(1 − r) K + r(1 + r)),

by induction on `K`; the step is `r · Q_{K+1} = Q_K − (1 − r)³ K²` for the bracket `Q_K`.

DERIVED: `3` is the cube `(1 − r)³` clearing the denominator of `∑ j² r^j = r(1 + r)/(1 − r)³`; `2`
is the square on `j`, on `K` and on `1 − r`, and the `2` of `2r(1 − r)K`; `1` is the unit in `1 − r`
and `1 + r`. All are the closed form's own. -/
theorem one_sub_cube_mul_sum_sq_pow (r : ℝ) (K : ℕ) :
    (1 - r) ^ 3 * ∑ j ∈ Finset.range K, r ^ j * (j : ℝ) ^ 2
      = r * (1 + r)
        - r ^ K * ((1 - r) ^ 2 * (K : ℝ) ^ 2 + 2 * r * (1 - r) * (K : ℝ) + r * (1 + r)) := by
  induction K with
  | zero =>
    simp only [Finset.sum_range_zero, mul_zero, pow_zero, Nat.cast_zero, one_mul]
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

#print axioms one_sub_cube_mul_sum_sq_pow

/-- For `0 ≤ t`, `∑_{j ≤ k} t^j ≤ modeMass k t`: the lags `0, …, k` have circle distance equal to
the lag, and every other term is nonnegative.

DERIVED: `1` is the `+ 1` of `range (k + 1)`, the lags below the antipode; `0` is the sign of
`t`. -/
theorem sum_pow_le_modeMass (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ j ∈ Finset.range (k + 1), t ^ j ≤ modeMass k t := by
  have h : modeMass k t
      = ∑ d ∈ Finset.range (2 * k + 1 + 1), t ^ ZeroMode.clag (2 * k + 1 + 1) d :=
    ZeroMode.sum_circLag_eq_range (N := 2 * k + 1) (fun c => t ^ c)
  rw [h]
  have hsub : Finset.range (k + 1) ⊆ Finset.range (2 * k + 1 + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  calc ∑ j ∈ Finset.range (k + 1), t ^ j
      = ∑ j ∈ Finset.range (k + 1), t ^ ZeroMode.clag (2 * k + 1 + 1) j := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        have hc : ZeroMode.clag (2 * k + 1 + 1) j = j := by
          unfold ZeroMode.clag
          omega
        rw [hc]
    _ ≤ ∑ d ∈ Finset.range (2 * k + 1 + 1), t ^ ZeroMode.clag (2 * k + 1 + 1) d :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg ht _)

/-- For `0 ≤ r ≤ 1`, `1 − r^{k+1} ≤ (1 − r) · modeMass k r` (`sum_pow_le_modeMass` and the geometric
sum `one_sub_mul_sum_pow`).

DERIVED: `1` is the geometric series' leading term, the upper end of `r`, and the `+ 1` of the
antipodal exponent `k + 1`; `0` is the lower end of `r`. -/
theorem one_sub_pow_le_modeMass (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    1 - r ^ (k + 1) ≤ (1 - r) * modeMass k r := by
  rw [← one_sub_mul_sum_pow r (k + 1)]
  exact mul_le_mul_of_nonneg_left (sum_pow_le_modeMass k hr0) (by linarith)

/-- For `0 ≤ r ≤ 1`, `(1 − r)³ · modeSq k r ≤ 2 r (1 + r)`: each circle distance occurs at most
twice (`Moment.sum_circLag_le_two_mul`), and `(1 − r)³ ∑_j r^j j² ≤ r(1 + r)`
(`one_sub_cube_mul_sum_sq_pow`, the remainder being nonnegative).

DERIVED: `3` is `one_sub_cube_mul_sum_sq_pow`'s cube; `2` is the multiplicity of a circle distance;
`1` is the unit in `1 − r` and `1 + r` and the upper end of `r`; `0` its lower end. -/
theorem modeSq_le (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - r) ^ 3 * modeSq k r ≤ 2 * (r * (1 + r)) := by
  have h2 : modeSq k r ≤ 2 * ∑ j ∈ Finset.range (2 * k + 1 + 2), r ^ j * (j : ℝ) ^ 2 :=
    Moment.sum_circLag_le_two_mul (N := 2 * k + 1) (fun j => r ^ j * (j : ℝ) ^ 2)
      (fun j => mul_nonneg (pow_nonneg hr0 j) (sq_nonneg _))
  have hid := one_sub_cube_mul_sum_sq_pow r (2 * k + 1 + 2)
  have h1r : 0 ≤ 1 - r := by linarith
  have hK0 : (0 : ℝ) ≤ ((2 * k + 1 + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQ0 : 0 ≤ (1 - r) ^ 2 * ((2 * k + 1 + 2 : ℕ) : ℝ) ^ 2
      + 2 * r * (1 - r) * ((2 * k + 1 + 2 : ℕ) : ℝ) + r * (1 + r) := by
    have e1 := mul_nonneg (pow_nonneg h1r 2) (sq_nonneg ((2 * k + 1 + 2 : ℕ) : ℝ))
    have e2 := mul_nonneg (mul_nonneg (mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) hr0) h1r) hK0
    have e3 := mul_nonneg hr0 (by linarith : (0 : ℝ) ≤ 1 + r)
    linarith
  have hQ := mul_nonneg (pow_nonneg hr0 (2 * k + 1 + 2)) hQ0
  have h13 : 0 ≤ (1 - r) ^ 3 := pow_nonneg h1r 3
  calc (1 - r) ^ 3 * modeSq k r
      ≤ (1 - r) ^ 3 * (2 * ∑ j ∈ Finset.range (2 * k + 1 + 2), r ^ j * (j : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 h13
    _ = 2 * ((1 - r) ^ 3 * ∑ j ∈ Finset.range (2 * k + 1 + 2), r ^ j * (j : ℝ) ^ 2) := by ring
    _ ≤ 2 * (r * (1 + r)) := by
        rw [hid]
        linarith

/-- The quadratic cosine bound on the single mode: for `0 ≤ r`,
`modeMass k r − (2π/n)²/2 · modeSq k r ≤ modeCos k r`, `n = (2k + 1) + 1`, from
`1 − x²/2 ≤ cos x` termwise.

DERIVED: `2 * π` is the full turn; the exponent `2` and the divisor `2` are those of `1 − x²/2`; `2`
and `1` spell the aperture, the other `1` is the lag arity's `+ 1`; `0` is the sign of `r`. -/
theorem modeCos_ge (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    modeMass k r - (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2 * modeSq k r
      ≤ modeCos k r := by
  unfold modeMass modeSq modeCos
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun d _ => ?_)
  have hc := Real.one_sub_sq_div_two_le_cos
    (x := 2 * Real.pi * (Moment.circLag d : ℝ) / (((2 * k + 1 : ℕ) : ℝ) + 1))
  have hp : 0 ≤ r ^ Moment.circLag d := pow_nonneg hr0 _
  have h := mul_le_mul_of_nonneg_left hc hp
  have he : r ^ Moment.circLag d - (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2
        * (r ^ Moment.circLag d * (Moment.circLag d : ℝ) ^ 2)
      = r ^ Moment.circLag d * (1 - (2 * Real.pi * (Moment.circLag d : ℝ)
        / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2) := by ring
  rw [he]
  exact h

/-- **An explicit lattice condition for the single mode.** For `0 ≤ r` with

    4π² r (1 + r)  <  (1 − 3^{−1/4}) · (2(k + 1))² · (1 − r)² · (1 − r^{k+1}),

`3^{−1/4} < modeCosAvg k r`. The condition forces `r < 1`. `modeCos_ge` puts `modeCos k r` above
`modeMass k r − (2π/n)²/2 · modeSq k r`; `modeSq_le` bounds `(1 − r)³ modeSq k r` by `2r(1 + r)` and
`one_sub_pow_le_modeMass` bounds `(1 − r) modeMass k r` below by `1 − r^{k+1}`.

DERIVED: `4π² = (2π)²` is the squared full turn and the `2` of `modeSq_le` against the divisor `2`
of `1 − x²/2`; `2(k + 1)` is the number of lags of the aperture `2k + 1`; `3`, `1` and `4` spell the
floor's `3^{−1/4}`; the exponent `2` on `1 − r` is `modeSq_le`'s cube less the `1 − r` of
`one_sub_pow_le_modeMass`; `1` is the unit in `1 ± r` and the `+ 1` of `k + 1`; `0` is the sign of
`r`. -/
theorem modeCosAvg_gt_of_bound (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hcond : 4 * Real.pi ^ 2 * (r * (1 + r))
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2
        * (1 - r ^ (k + 1))) :
    (3 : ℝ) ^ (-(1 : ℝ) / 4) < modeCosAvg k r := by
  have hc1 : 0 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := Moment.floor_rhs_pos
  have hn : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have hA : 0 ≤ (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2 :=
    mul_nonneg (mul_nonneg hc1.le (sq_nonneg _)) (sq_nonneg _)
  -- the condition forces `r < 1`
  have hr1 : r < 1 := by
    by_contra h
    push_neg at h
    have hp : 1 ≤ r ^ (k + 1) := one_le_pow₀ h
    have hB := mul_le_mul_of_nonneg_left (show 1 - r ^ (k + 1) ≤ 0 by linarith) hA
    rw [mul_zero] at hB
    have hr : 0 < r * (1 + r) := mul_pos (by linarith) (by linarith)
    have hC : 0 < 4 * Real.pi ^ 2 * (r * (1 + r)) :=
      mul_pos (mul_pos (by norm_num) (pow_pos Real.pi_pos 2)) hr
    linarith
  have h1r : 0 < 1 - r := by linarith
  have hDr : 0 < modeMass k r := modeMass_pos k hr0
  have hcos := modeCos_ge k hr0
  have hsq := modeSq_le k hr0 hr1.le
  have hD := one_sub_pow_le_modeMass k hr0 hr1.le
  have hnn : ((2 * k + 1 : ℕ) : ℝ) + 1 = 2 * ((k : ℝ) + 1) := by push_cast; ring
  have hK : (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2 * (2 * ((k : ℝ) + 1)) ^ 2
      = 2 * Real.pi ^ 2 := by
    rw [hnn]
    have hm : (2 * ((k : ℝ) + 1)) ≠ 0 := hn.ne'
    calc (2 * Real.pi / (2 * ((k : ℝ) + 1))) ^ 2 / 2 * (2 * ((k : ℝ) + 1)) ^ 2
        = (2 * Real.pi / (2 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1))) ^ 2 / 2 := by ring
      _ = (2 * Real.pi) ^ 2 / 2 := by rw [div_mul_cancel₀ _ hm]
      _ = 2 * Real.pi ^ 2 := by ring
  have hP : 0 < (1 - r) ^ 3 * (2 * ((k : ℝ) + 1)) ^ 2 := mul_pos (pow_pos h1r 3) (pow_pos hn 2)
  have hlt : (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2 * modeSq k r
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * modeMass k r := by
    refine lt_of_mul_lt_mul_right ?_ hP.le
    calc (2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2 * modeSq k r
          * ((1 - r) ^ 3 * (2 * ((k : ℝ) + 1)) ^ 2)
        = ((2 * Real.pi / (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 2 / 2 * (2 * ((k : ℝ) + 1)) ^ 2)
            * ((1 - r) ^ 3 * modeSq k r) := by ring
      _ = 2 * Real.pi ^ 2 * ((1 - r) ^ 3 * modeSq k r) := by rw [hK]
      _ ≤ 2 * Real.pi ^ 2 * (2 * (r * (1 + r))) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * Real.pi ^ 2 * (r * (1 + r)) := by ring
      _ < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2
            * (1 - r ^ (k + 1)) := hcond
      _ ≤ (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2
            * ((1 - r) * modeMass k r) := mul_le_mul_of_nonneg_left hD hA
      _ = (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * modeMass k r
            * ((1 - r) ^ 3 * (2 * ((k : ℝ) + 1)) ^ 2) := by ring
  have hmain : (3 : ℝ) ^ (-(1 : ℝ) / 4) * modeMass k r < modeCos k r := by linarith
  unfold modeCosAvg
  rw [lt_div_iff₀ hDr]
  exact hmain

#print axioms modeCosAvg_gt_of_bound

/-- The lattice condition holds at `r = 0`, so `3^{−1/4} < modeCosAvg k 0` at every aperture: the
hypothesis of `readsClear_of_contraction` is satisfiable.

DERIVED: `3`, `1` and `4` spell the floor's `3^{−1/4}`; `0` is the rate. -/
theorem modeCosAvg_gt_at_zero (k : ℕ) : (3 : ℝ) ^ (-(1 : ℝ) / 4) < modeCosAvg k 0 := by
  apply modeCosAvg_gt_of_bound k le_rfl
  have hc1 : 0 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := Moment.floor_rhs_pos
  have hn : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have hz : (0 : ℝ) ^ (k + 1) = 0 := zero_pow (Nat.succ_ne_zero k)
  rw [hz]
  linarith [mul_pos hc1 (pow_pos hn 2)]

/-- **A converse under the explicit lattice condition.** For `a` self-adjoint with spectrum in
`[0, 1]`, `a Ω = Ω`, `0 ≤ r`, `‖a u‖ ≤ r ‖u‖` for every `u` orthogonal to `Ω`, and
`4π² r(1 + r) < (1 − 3^{−1/4}) (2(k + 1))² (1 − r)² (1 − r^{k+1})`: `ReadsClear a Ω k`
(`modeCosAvg_gt_of_bound`, then `readsClear_of_contraction`).

DERIVED: the numerals are `modeCosAvg_gt_of_bound`'s: `4π² = (2π)²`, `2(k + 1)` the lag count,
`3^{−1/4}` the floor, `2` the exponents; `0` and `1` are the interval's ends and `0` the
orthogonality and the lower end of `r`. -/
theorem readsClear_of_contraction_bound (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (r : ℝ) (hr0 : 0 ≤ r)
    (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖)
    (hcond : 4 * Real.pi ^ 2 * (r * (1 + r))
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2
        * (1 - r ^ (k + 1))) :
    ReadsClear a Ω k :=
  readsClear_of_contraction a ha hspec Ω hΩ k r hr0 hcon (modeCosAvg_gt_of_bound k hr0 hcond)

#print axioms readsClear_of_contraction_bound

/-! ## A rate in units of the window -/

/-- **A rate in units of the window meets the lattice condition.** For `0 < X`, `0 ≤ r`,
`r ≤ e^{−X/(2(k + 1))}` and the aperture-free

    8π² < (1 − 3^{−1/4}) · X² · (1 − e^{−X/2}),

the lattice condition of `modeCosAvg_gt_of_bound` holds. With `u = X/(2(k + 1))` and `E = e^{−u/2}`:
`u ≤ 2 sinh(u/2)` (`Real.self_le_sinh_iff`) gives `u E ≤ 1 − E² ≤ 1 − r`, so `X² r ≤ (2(k + 1))²
(1 − r)²`; `r^{k+1} ≤ e^{−u(k+1)} = e^{−X/2}`; and `r(1 + r) ≤ 2r`.

DERIVED: `2(k + 1)` is the lag count; `8π² = 2 · 4π²` is the lattice condition's `4π²` with
`r(1 + r) ≤ 2r`; `X/2 = (k + 1) · X/(2(k + 1))` is the antipodal exponent in units of the window;
`3`, `1` and `4` spell the floor; `2` in `X²` is the square of `n(1 − r)`; `0` is the sign of `X`
and `r`. -/
theorem cond_of_rate (k : ℕ) {X r : ℝ} (hX0 : 0 < X) (hr0 : 0 ≤ r)
    (hrate : r ≤ Real.exp (-(X / (2 * ((k : ℝ) + 1)))))
    (hX : 8 * Real.pi ^ 2 < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * X ^ 2 * (1 - Real.exp (-(X / 2)))) :
    4 * Real.pi ^ 2 * (r * (1 + r))
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2
        * (1 - r ^ (k + 1)) := by
  have hc1 : 0 < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 4) := Moment.floor_rhs_pos
  have hn : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = X / (2 * ((k : ℝ) + 1)) := ⟨_, rfl⟩
  rw [← hu_def] at hrate
  have hu : 0 < u := by rw [hu_def]; exact div_pos hX0 hn
  have hXu : X = u * (2 * ((k : ℝ) + 1)) := by rw [hu_def, div_mul_cancel₀ X hn.ne']
  -- `E = e^{−u/2}`: `E² = e^{−u}` and `u E ≤ 1 − E²`, which is `u ≤ 2 sinh(u/2)`
  have hEpos : 0 < Real.exp (-(u / 2)) := Real.exp_pos _
  have hEE : Real.exp (-(u / 2)) * Real.exp (-(u / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsinh : u * Real.exp (-(u / 2)) ≤ 1 - Real.exp (-(u / 2)) * Real.exp (-(u / 2)) := by
    have hs : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_eq] at hs
    have hprod : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : u ≤ Real.exp (u / 2) - Real.exp (-(u / 2)) := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hEpos.le
    linarith
  have hrE : r ≤ Real.exp (-(u / 2)) * Real.exp (-(u / 2)) := by rw [hEE]; exact hrate
  have h1r : u * Real.exp (-(u / 2)) ≤ 1 - r := by linarith
  have huE : 0 ≤ u * Real.exp (-(u / 2)) := mul_nonneg hu.le hEpos.le
  have hr1 : r ≤ 1 := by linarith
  -- `X² r ≤ n² (1 − r)²`
  have hur : u ^ 2 * r ≤ (1 - r) ^ 2 := by
    have hsq : (u * Real.exp (-(u / 2))) ^ 2 ≤ (1 - r) ^ 2 := pow_le_pow_left₀ huE h1r 2
    have hm : u ^ 2 * r ≤ u ^ 2 * (Real.exp (-(u / 2)) * Real.exp (-(u / 2))) :=
      mul_le_mul_of_nonneg_left hrE (sq_nonneg u)
    linarith
  have hXr : X ^ 2 * r ≤ (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hur (sq_nonneg (2 * ((k : ℝ) + 1)))
    rw [hXu]
    linarith
  -- `r^{k+1} ≤ e^{−X/2}`
  have hpow : r ^ (k + 1) ≤ Real.exp (-(X / 2)) := by
    calc r ^ (k + 1) ≤ (Real.exp (-u)) ^ (k + 1) := pow_le_pow_left₀ hr0 hrate (k + 1)
      _ = Real.exp (((k + 1 : ℕ) : ℝ) * (-u)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(X / 2)) := by
          congr 1
          rw [hXu]
          push_cast
          ring
  have hβ : 0 < 1 - Real.exp (-(X / 2)) := by
    have h := Real.exp_lt_exp.mpr (show -(X / 2) < 0 by linarith)
    rw [Real.exp_zero] at h
    linarith
  rcases hr0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have hz : (0 : ℝ) ^ (k + 1) = 0 := zero_pow (Nat.succ_ne_zero k)
    rw [hz]
    linarith [mul_pos hc1 (pow_pos hn 2)]
  · have hA : 8 * Real.pi ^ 2 * r
        < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * X ^ 2 * (1 - Real.exp (-(X / 2))) * r :=
      mul_lt_mul_of_pos_right hX hpos
    have hB : 0 ≤ Real.pi ^ 2 * (r * (1 - r)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg hr0 (by linarith))
    have hC : (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (1 - Real.exp (-(X / 2))) * (X ^ 2 * r)
        ≤ (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (1 - Real.exp (-(X / 2)))
          * ((2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2) :=
      mul_le_mul_of_nonneg_left hXr (mul_nonneg hc1.le hβ.le)
    have hD : (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2
          * (1 - Real.exp (-(X / 2)))
        ≤ (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * ((k : ℝ) + 1)) ^ 2 * (1 - r) ^ 2
          * (1 - r ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg hc1.le (sq_nonneg _)) (sq_nonneg _))
    linarith

#print axioms cond_of_rate

/-- **`X = 20` meets the aperture-free condition**: `8π² < (1 − 3^{−1/4}) · 20² · (1 − e^{−20/2})`.
In the proof: `π < 3.15` (`Real.pi_lt_d2`), `3^{−1/4} < 0.77` (as `0.77⁴ > 1/3`), and
`e^{−10} ≤ 1/11` (as `e^{10} ≥ 11`), so the right side exceeds `0.23 · 400 · 10/11 = 83.6` and the
left is below `8 · 3.15² = 79.4`.

CHOSEN: `20`. The condition holds exactly for `X` above `18.1328…` (computed, not proved here);
`20` is a round value above it. DERIVED: `8`, `3`, `1`, `4`, the exponent `2` on `π` and on `20`,
and the `2` of `20/2` are `cond_of_rate`'s. -/
theorem twenty_clears :
    8 * Real.pi ^ 2
      < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (20 : ℝ) ^ 2 * (1 - Real.exp (-((20 : ℝ) / 2))) := by
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  have hπ2 : Real.pi ^ 2 < 9.9225 := by nlinarith [Real.pi_pos]
  have h4 : ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 4 = 1 / 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have he : (-(1 : ℝ) / 4) * ((4 : ℕ) : ℝ) = -1 := by norm_num
    rw [he, Real.rpow_neg_one]
    norm_num
  have hc : (3 : ℝ) ^ (-(1 : ℝ) / 4) < 0.77 := by
    by_contra h
    push_neg at h
    have h' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.77) h 4
    rw [h4] at h'
    norm_num at h'
  have he : Real.exp (-((20 : ℝ) / 2)) ≤ 1 / 11 := by
    have h10 : -((20 : ℝ) / 2) = -10 := by norm_num
    rw [h10]
    have h1 : (10 : ℝ) + 1 ≤ Real.exp 10 := Real.add_one_le_exp 10
    have h2 : Real.exp (-10) * Real.exp 10 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : 0 < Real.exp (-10) := Real.exp_pos _
    linarith [mul_le_mul_of_nonneg_left h1 h3.le]
  have hprod : (0.23 : ℝ) * (10 / 11)
      ≤ (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * (1 - Real.exp (-((20 : ℝ) / 2))) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  linarith

#print axioms twenty_clears

/-- **A converse at a rate in units of the window.** For `a` self-adjoint with spectrum in
`[0, 1]`, `a Ω = Ω`, `0 < X` meeting `8π² < (1 − 3^{−1/4}) X² (1 − e^{−X/2})`, `0 ≤ r` with
`r ≤ e^{−X/(2(k + 1))}`, and `‖a u‖ ≤ r ‖u‖` for every `u` orthogonal to `Ω`: `ReadsClear a Ω k`
(`cond_of_rate`, then `readsClear_of_contraction_bound`).

DERIVED: `8π² = 2 · (2π)²`: `(2π)²` is the squared full turn of `modeCosAvg_gt_of_bound`'s `4π²`
(`modeSq_le`'s multiplicity `2` against the divisor `2` of `1 − x²/2`), and the leading `2` is
`1 + r ≤ 2` (`cond_of_rate`); `3`, `1` and `4` spell the floor `3^{−1/4}`; `2(k + 1)` is the number
of sites of the aperture `2k + 1`; `X/2 = (k + 1) · X/(2(k + 1))` is the antipodal exponent; the
exponent `2` on `X` is the square of `n(1 − r)`, on `π` the square of the full turn; the `1` of
`1 − 3^{−1/4}` is that of `1 − x²/2`, and the `1` of `1 − e^{−X/2}` the geometric series' leading
term (`one_sub_pow_le_modeMass`); `0` and `1` are the interval's ends, and `0` the sign of `X` and
`r` and the orthogonality. -/
theorem readsClear_of_rate (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (X r : ℝ)
    (hX0 : 0 < X) (hr0 : 0 ≤ r) (hrate : r ≤ Real.exp (-(X / (2 * ((k : ℝ) + 1)))))
    (hX : 8 * Real.pi ^ 2 < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * X ^ 2 * (1 - Real.exp (-(X / 2))))
    (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖) :
    ReadsClear a Ω k :=
  readsClear_of_contraction_bound a ha hspec Ω hΩ k r hr0 hcon (cond_of_rate k hX0 hr0 hrate hX)

#print axioms readsClear_of_rate

/-- **A converse at a lattice rate.** As `readsClear_of_rate`, with the rate stated as
`X/(2(k + 1)) ≤ −log r` for `0 < r`.

DERIVED: `8π² = 2 · (2π)²`: `(2π)²` is the squared full turn of `modeCosAvg_gt_of_bound`'s `4π²`
(`modeSq_le`'s multiplicity `2` against the divisor `2` of `1 − x²/2`), and the leading `2` is
`1 + r ≤ 2` (`cond_of_rate`); `3`, `1` and `4` spell the floor `3^{−1/4}`; `2(k + 1)` is the number
of sites of the aperture `2k + 1`; `X/2 = (k + 1) · X/(2(k + 1))` is the antipodal exponent; the
exponent `2` on `X` is the square of `n(1 − r)`, on `π` the square of the full turn; the `1` of
`1 − 3^{−1/4}` is that of `1 − x²/2`, and the `1` of `1 − e^{−X/2}` the geometric series' leading
term (`one_sub_pow_le_modeMass`); `0` is the sign of `X` and `r`, the lower end of the interval and
the orthogonality; `1` is the upper end of the interval. -/
theorem readsClear_of_log_rate (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (X r : ℝ)
    (hX0 : 0 < X) (hr : 0 < r) (hrate : X / (2 * ((k : ℝ) + 1)) ≤ -Real.log r)
    (hX : 8 * Real.pi ^ 2 < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * X ^ 2 * (1 - Real.exp (-(X / 2))))
    (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖) :
    ReadsClear a Ω k := by
  have hle : r ≤ Real.exp (-(X / (2 * ((k : ℝ) + 1)))) := by
    calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ ≤ Real.exp (-(X / (2 * ((k : ℝ) + 1)))) := Real.exp_le_exp.mpr (by linarith)
  exact readsClear_of_rate a ha hspec Ω hΩ k X r hX0 hr.le hle hX hcon

#print axioms readsClear_of_log_rate

/-- **A converse at a physical rate.** With spacing `sp > 0` and the aperture `2k + 1` spanning
the physical extent `L = 2(k + 1) · sp`: for `0 < X` meeting
`8π² < (1 − 3^{−1/4}) X² (1 − e^{−X/2})`, `0 < r`, a physical rate `−log r / sp ≥ X/L`, and
`‖a u‖ ≤ r ‖u‖` for every `u` orthogonal to `Ω`: `ReadsClear a Ω k`. The spacing cancels:
`−log r / sp ≥ X/L` is `−log r ≥ X/(2(k + 1))`.

DERIVED: `8π² = 2 · (2π)²`: `(2π)²` is the squared full turn of `modeCosAvg_gt_of_bound`'s `4π²`
(`modeSq_le`'s multiplicity `2` against the divisor `2` of `1 − x²/2`), and the leading `2` is
`1 + r ≤ 2` (`cond_of_rate`); `3`, `1` and `4` spell the floor `3^{−1/4}`; `2(k + 1)` is the number
of sites of the aperture `2k + 1`; `X/2 = (k + 1) · X/(2(k + 1))` is the antipodal exponent; the
exponent `2` on `X` is the square of `n(1 − r)`, on `π` the square of the full turn; the `1` of
`1 − 3^{−1/4}` is that of `1 − x²/2`, and the `1` of `1 − e^{−X/2}` the geometric series' leading
term (`one_sub_pow_le_modeMass`); `0` is the sign of `X`, `r` and `sp`, the lower end of the
interval and the orthogonality; `1` is the upper end of the interval. -/
theorem readsClear_of_physical_rate (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (X r sp L : ℝ)
    (hX0 : 0 < X) (hr : 0 < r) (hsp : 0 < sp) (hL : (2 * ((k : ℝ) + 1)) * sp = L)
    (hrate : X / L ≤ -Real.log r / sp)
    (hX : 8 * Real.pi ^ 2 < (1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) * X ^ 2 * (1 - Real.exp (-(X / 2))))
    (hcon : ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖) :
    ReadsClear a Ω k := by
  have hn : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have hL0 : 0 < L := by rw [← hL]; exact mul_pos hn hsp
  have hlat : X / (2 * ((k : ℝ) + 1)) ≤ -Real.log r := by
    rw [div_le_div_iff₀ hL0 hsp] at hrate
    rw [← hL] at hrate
    rw [div_le_iff₀ hn]
    have h2 : X * sp ≤ (-Real.log r * (2 * ((k : ℝ) + 1))) * sp := by linarith
    exact le_of_mul_le_mul_right h2 hsp
  exact readsClear_of_log_rate a ha hspec Ω hΩ k X r hX0 hr hlat hX hcon

#print axioms readsClear_of_physical_rate

/-- **`ReadsClear` at a fixed window brackets the physical gap.** With spacing `sp > 0` and the
aperture `2k + 1` spanning `L = 2(k + 1) · sp`:

* `ReadsClear a Ω k` gives a `ρ ∈ (0, 1)` with `‖a u‖ ≤ ρ ‖u‖` for every `u` orthogonal to `Ω`, at
  physical rate `−log ρ / sp = −2·log(12(1 − 3^{−1/4})/8)/L = κ*/L`, `κ* ≈ 2.042`
  (`SpectralGap.physical_gap_of_reads` at one step);
* every `r ∈ (0, ∞)` with physical rate `−log r / sp ≥ 20/L` and `‖a u‖ ≤ r ‖u‖` for every `u`
  orthogonal to `Ω` gives `ReadsClear a Ω k` (`readsClear_of_physical_rate`, `twenty_clears`).

This is a bracket, not an equivalence: a physical gap of at least `20/L` gives the reads, and the
reads give a physical gap of at least `κ*/L`; the two thresholds are a factor `20/κ* ≈ 9.8` apart,
and for a physical gap between them the reads are not decided.

DERIVED: `2(k + 1)` is the number of sites of the aperture; `2` in `κ* = −2·log cap` is that
doubling; `12`, `8`, `3`, `1` and `4` spell the cap `12(1 − 3^{−1/4})/8`; `0` and `1` bracket `ρ`
and are the interval's ends; `0` is the sign of `sp` and `r` and the orthogonality.
CHOSEN: `20`, as in `twenty_clears`. -/
theorem readsClear_brackets_physical_gap (a : E →L[ℂ] E) (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) (Ω : E) (hΩ : a Ω = Ω) (k : ℕ) (sp L : ℝ)
    (hsp : 0 < sp) (hL : (2 * ((k : ℝ) + 1)) * sp = L) :
    (ReadsClear a Ω k →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        -Real.log ρ / sp = -2 * Real.log (12 * ((1 - (3 : ℝ) ^ (-(1 : ℝ) / 4)) / 8)) / L ∧
        ∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ ρ * ‖u‖) ∧
    (∀ r : ℝ, 0 < r → 20 / L ≤ -Real.log r / sp →
      (∀ u : E, inner ℂ Ω u = 0 → ‖a u‖ ≤ r * ‖u‖) → ReadsClear a Ω k) := by
  refine ⟨fun hread => ?_, fun r hr hrate hcon => ?_⟩
  · obtain ⟨ρ, hρ0, hρ1, heq, _, hdec⟩ :=
      physical_gap_of_reads a ha hspec Ω hΩ k hread sp L hsp hL
    refine ⟨ρ, hρ0, hρ1, heq, fun u hu => ?_⟩
    simpa only [pow_one] using hdec u hu 1
  · exact readsClear_of_physical_rate a ha hspec Ω hΩ k 20 r sp L (by norm_num) hr hsp hL hrate
      twenty_clears hcon

#print axioms readsClear_brackets_physical_gap

end MassGap.ReadConverse
