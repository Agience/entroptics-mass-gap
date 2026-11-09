import MassGap.FreqRead

/-!
# MassGap.BandShell — the band read on the mass shell, for a spectral measure

`FreqRead` proves, at the free field on a periodic box, the band identity `(A ω₁)² = (A ω₀)² + cL²`: the
in-aperture read and the mass read differ by a number of the box. This module proves the same identity for
any spectral measure, the Källén–Lehmann form of a two-point function, at the level the tree supports: the
rate read of a momentum sector. It uses proven templates only: the Källén–Lehmann representation of the
momentum-`p` sector of a Euclidean two-point function as `∫ e^{−τ √(s + |p|²)} dρ(s)` (a Lorentz-invariant
spectral measure `ρ` on the mass squared `s`), and the edge asymptotics of a Laplace transform (the slowest
rate of the transform is the bottom of the support). Declarations are in the namespace `MassGap.BandShell`.

## 1. The read of a momentum sector (proved)

* `shell s p2 = √(s + p2)`: the energy of mass squared `s` at momentum squared `p2`.
* `bandProfile ρ p2 τ = ∫ e^{−τ shell s p2} dρ(s)`: the momentum-`p` sector of the two-point function in
  Källén–Lehmann form. The free propagator density `1/(2 shell)` is folded into `ρ`; it is positive and
  does not move the bottom of the support.
* `SpecBottom ρ M2`: `M2` is the bottom of the support of `ρ` (`ρ(−∞, M2) = 0`, every `[M2, M2 + ε)` has
  positive mass). Nothing is chosen: `M2` is the measure's own edge.
* `shell_rate`: for a finite `ρ` with bottom `M2` and `M2 + p2 ≥ 0`,
  `−log(bandProfile ρ p2 τ)/τ → √(M2 + p2)` as `τ → ∞`. The continuous form of `FreqRead.profile_rate`.
* `mass_of_band_read`: if the read of the `p` sector tends to `r`, then `M2 = r² − p2`. The mass is read
  exactly from any one momentum sector.
* `gap_iff_band_excess`: with `p2 ≥ 0`, `0 < M2 ↔ √p2 < r`. A positive bottom of the mass spectrum is
  the same statement as the sector read exceeding the momentum.
* `rest_is_bottom`: `shell M2 0 = √M2 ≤ shell M2 p2`; the bottom over all sectors is the rest sector.
* `aperture_shell`: at the in-aperture momentum `c/A`, `A · shell M2 (c/A)² = FreqRead.cross (√M2) c A`.
  With `c = 2π` (the continuum value, which bounds `FreqRead.cL` by `FreqRead.cL_le_two_pi`; the limit
  `cL L → 2π` is not proved here) this gives the band identity of `FreqRead` §5 for a measure `ρ` once
  the continuum two-point function is known to have one; no such measure is constructed in this module.

## 2. Load tests (proved)

* `specBottom_dirac`: a single mass `δ_{M2}` has bottom `M2` (the hypotheses of §1 are met).
* `free_rate_agrees`: at `ρ = δ_{m²}` and the box momentum `p̂²₁`, `shell_rate` reads `FreqRead.omega m a L 1`,
  the in-aperture fundamental of `FreqRead.kept_rate`.
* `band_identity_of_shell`: `mass_of_band_read` at `δ_{m²}` gives back `FreqRead.band_identity`
  `(A ω₁)² = (A m)² + cL²`.
* `massive_excess`: `m > 0` gives band excess; `massless_no_excess`: `δ_0` gives none.
* `specBottom_zero_add` and `zero_mass_no_excess`: a measure with mass at `0` and a massive part, `δ_0 + δ_M`,
  has bottom `0`, no gap, and no band excess. Both sides of `gap_iff_band_excess` are realised; no clause
  is vacuous.

## 3. The bridge question, plainly (argued, not proved here)

What the tree has. The Clay statement (`ClayStatementG.ClayStatementOf`, clauses `HamiltonianGap` and
`SpectralGapOn`) carries an `OSDataS`: a Hilbert space, a vacuum, a time semigroup `e^{−tH}` and a number
`gap > 0` with `gap ‖u‖² ≤ ⟪u, Hu⟫` and `‖e^{−tH} u‖ ≤ e^{−gap t}‖u‖` on the vacuum complement. The mass gap is
the bottom of `H` above the vacuum. There are no spatial translations, no momentum operator and no joint
spectrum of `(H, P)` on `OSDataS`; only the Euclidean test-function space (`WightmanData.TestFn`) of the Wightman setting is in the tree; it contains no Wightman axioms, Lorentz boosts, BHW extension or joint spectrum. The OS-II
reconstruction is a documented corollary in `ClayStatement`'s docstring, not formalised. The covariance
the tree has is Euclidean: `FlowCovN.FlowCovLim ↔ CovC` (`O(4)` covariance of the continuum composite
Schwinger functions, under `ExpandR` and `ConvC`).

(a) Does the continuum limit carry a Lorentz-invariant Källén–Lehmann measure from the bundle? Plainly,
not in Lean. `CovC` (from `FlowCovLim`), `OS2` and the `OS0` growth bound are the inputs of the
Osterwalder–Schrader II theorem; its output with the Källén–Lehmann theorem is a Lorentz-invariant
measure `ρ_O` for each scalar composite `O`, bottom at least the gap. Neither step is formalised, and the
measure exists only for the limit, whose existence is what the bundle's inputs are for. `mass_of_band_read`
applies to the limit once that corollary is formalised; it does not apply along the zoom, where the
periodic lattice box is not Lorentz-invariant and the identity holds only at the free field
(`FreqRead.band_identity`).

(b) Does it reduce any of the 8 inputs of `ProxBound.CoreInputsAlongWPB` (`ApertureBridge`, `ExpandMatch`,
`ProxBound`, `ZoomSettling`, `FlowCovLim`, `FlowWard`, `ProxyNondeg`, `ProxyGenLimGerm`; with
`ThreePointAtScale`)? No. None of them states the mass: they are moment, matching, settling, covariance,
Ward and non-degeneracy statements on the flowed reads. The hard core:

* first non-zero read: `gap_iff_band_excess` makes `M2 > 0` equivalent to band excess in one sector. This
  is a restatement of the gap, not a discharge of it.
* no-stall crossover: with `aperture_shell`, the continuum in-aperture read is `cross (√M2) 2π A`, strictly
  increasing in `A` exactly when `M2 > 0` (`FreqRead.cross_strictMonoOn`, `FreqRead.cross_massless`). No
  stall is again the gap itself.
* the fine view: as `A → 0` the excess `cross (√M2) 2π A − 2π` tends to `0`
  (`FreqRead.cross_tendsto_fine`), and by `√(x² + c²) − c ≤ x²/(2c)` (argued here, not formalised) it is
  at most `M2 A²/(4π)`, so the fine view alone cannot certify `M2 > 0` without a quantitative lower bound on
  that excess, and that bound is the gap.

Count: 8 inputs before, 8 after. No input is replaced, so no capstone is built here.

(c) The single bridge statement this points to. The coarse and fine reads are one function
`A ↦ A · rate(p = 2π/A) = cross m 2π A` of the aperture, exactly, once the limit has a Lorentz-invariant
Källén–Lehmann measure. The bridge is then: "the continuum limit of one scalar composite with a non-zero
two-point function has a Källén–Lehmann measure invariant under the Lorentz group (OS-II from `CovC`,
`OS2`, `OS0`), and its in-aperture read exceeds `2π` at one aperture". The first half is a proven
template not yet formalised; the second half is the gap, read in the in-aperture sector instead of the
rest sector. Plainly, the second half is not supplied by anything in this module.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.BandShell

open Real Filter Topology MeasureTheory Set

noncomputable section

/-! ## 1. The read of a momentum sector -/

/-- **The shell energy** `√(s + p²)` of mass squared `s` at momentum squared `p2`. DERIVED: no numeral. -/
def shell (s p2 : ℝ) : ℝ := Real.sqrt (s + p2)

/-- **The momentum-`p` sector** of a two-point function in Källén–Lehmann form,
`∫ e^{−τ √(s + p²)} dρ(s)`. DERIVED: no numeral. -/
def bandProfile (ρ : Measure ℝ) (p2 τ : ℝ) : ℝ := ∫ s, Real.exp (-(τ * shell s p2)) ∂ρ

/-- **The bottom of the support** of `ρ` is `M2`: nothing below, positive mass in every `[M2, M2 + ε)`.
DERIVED: `0` the empty measure and the sign. -/
def SpecBottom (ρ : Measure ℝ) (M2 : ℝ) : Prop :=
  ρ (Iio M2) = 0 ∧ ∀ ε : ℝ, 0 < ε → 0 < ρ (Ico M2 (M2 + ε))

/-- DERIVED: no numeral. -/
theorem shell_mono {s t : ℝ} (p2 : ℝ) (h : s ≤ t) : shell s p2 ≤ shell t p2 :=
  Real.sqrt_le_sqrt (by linarith)

/-- DERIVED: `0` the sign. -/
theorem shell_nonneg (s p2 : ℝ) : 0 ≤ shell s p2 := Real.sqrt_nonneg _

/-- **The shell moves by at most `√ε`.** DERIVED: `0` the signs; `2` the square. -/
theorem shell_add_le {s p2 ε : ℝ} (hs : 0 ≤ s + p2) (hε : 0 ≤ ε) :
    shell (s + ε) p2 ≤ shell s p2 + Real.sqrt ε := by
  have h1 := Real.sq_sqrt hs
  have h2 := Real.sq_sqrt hε
  have h0 : 0 ≤ Real.sqrt (s + p2) + Real.sqrt ε := by positivity
  unfold shell
  calc Real.sqrt (s + ε + p2) ≤ Real.sqrt ((Real.sqrt (s + p2) + Real.sqrt ε) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (Real.sqrt_nonneg (s + p2)) (Real.sqrt_nonneg ε)])
    _ = Real.sqrt (s + p2) + Real.sqrt ε := Real.sqrt_sq h0

/-- DERIVED: `0` the sign; `1` the bound. -/
theorem integrable_band (ρ : Measure ℝ) [IsFiniteMeasure ρ] (p2 : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun s => Real.exp (-(τ * shell s p2))) ρ := by
  have hc : Continuous (fun s : ℝ => Real.exp (-(τ * shell s p2))) := by
    unfold shell
    exact Real.continuous_exp.comp ((continuous_const.mul
      (Real.continuous_sqrt.comp (continuous_id.add continuous_const))).neg)
  refine (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [shell_nonneg s p2])

/-- **Upper bound**: nothing below `M2`, so the sector decays at least at `shell M2`.
DERIVED: `0` the sign. -/
theorem bandProfile_le {ρ : Measure ℝ} [IsFiniteMeasure ρ] {M2 : ℝ} (h0 : ρ (Iio M2) = 0) (p2 : ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    bandProfile ρ p2 τ ≤ ρ.real univ * Real.exp (-(τ * shell M2 p2)) := by
  have hae : ∀ᵐ s ∂ρ, M2 ≤ s := by
    rw [ae_iff]
    have : {s : ℝ | ¬ M2 ≤ s} = Iio M2 := by ext s; simp [not_le]
    rw [this]; exact h0
  unfold bandProfile
  calc ∫ s, Real.exp (-(τ * shell s p2)) ∂ρ ≤ ∫ _s, Real.exp (-(τ * shell M2 p2)) ∂ρ := by
        apply integral_mono_ae (integrable_band ρ p2 hτ) (integrable_const _)
        filter_upwards [hae] with s hs
        exact Real.exp_le_exp.mpr (by nlinarith [shell_mono p2 hs])
    _ = ρ.real univ * Real.exp (-(τ * shell M2 p2)) := by rw [integral_const, smul_eq_mul]

/-- **Lower bound**: the mass in `[M2, M2 + ε)` decays no faster than `shell (M2 + ε)`.
DERIVED: `0` the sign. -/
theorem le_bandProfile (ρ : Measure ℝ) [IsFiniteMeasure ρ] (M2 ε p2 : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.exp (-(τ * shell (M2 + ε) p2)) * ρ.real (Ico M2 (M2 + ε)) ≤ bandProfile ρ p2 τ := by
  have hint := integrable_band ρ p2 hτ
  unfold bandProfile
  calc Real.exp (-(τ * shell (M2 + ε) p2)) * ρ.real (Ico M2 (M2 + ε))
        ≤ ∫ s in Ico M2 (M2 + ε), Real.exp (-(τ * shell s p2)) ∂ρ := by
        apply setIntegral_ge_of_const_le_real measurableSet_Ico (measure_ne_top _ _) _ hint.integrableOn
        intro s hs
        exact Real.exp_le_exp.mpr (by nlinarith [shell_mono p2 hs.2.le])
    _ ≤ ∫ s, Real.exp (-(τ * shell s p2)) ∂ρ :=
        setIntegral_le_integral hint (ae_of_all _ fun s => (Real.exp_pos _).le)

/-- DERIVED: `0` the sign. -/
theorem real_pos_of_pos {ρ : Measure ℝ} [IsFiniteMeasure ρ] {S : Set ℝ} (h : 0 < ρ S) :
    0 < ρ.real S :=
  ENNReal.toReal_pos h.ne' (measure_ne_top _ _)

/-- **The slowest rate of a momentum sector is the shell of the bottom of the spectrum**:
`−log(∫ e^{−τ √(s + p²)} dρ)/τ → √(M2 + p²)`. DERIVED: `0` the signs and the vanishing `c/τ`; `1` a width
(any positive width gives the positivity of the profile); `2` the halving of the gap to the target. -/
theorem shell_rate {ρ : Measure ℝ} [IsFiniteMeasure ρ] {M2 p2 : ℝ} (hb : SpecBottom ρ M2)
    (hM : 0 ≤ M2 + p2) :
    Tendsto (fun τ => -Real.log (bandProfile ρ p2 τ) / τ) atTop (𝓝 (shell M2 p2)) := by
  set E := shell M2 p2 with hE
  have hW : 0 < ρ.real univ :=
    real_pos_of_pos (lt_of_lt_of_le (hb.2 1 one_pos) (measure_mono (subset_univ _)))
  have hpos : ∀ τ, 0 ≤ τ → 0 < bandProfile ρ p2 τ := fun τ hτ =>
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) (real_pos_of_pos (hb.2 1 one_pos)))
      (le_bandProfile ρ M2 1 p2 hτ)
  have hlim : ∀ r c : ℝ, Tendsto (fun τ : ℝ => r - c / τ) atTop (𝓝 r) := by
    intro r c
    simpa using (tendsto_const_nhds (x := r)).sub
      ((tendsto_const_nhds (x := c)).div_atTop tendsto_id)
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [(hlim E (Real.log (ρ.real univ))).eventually (lt_mem_nhds ha),
      eventually_gt_atTop 0] with τ h1 hτ
    have hC := hpos τ hτ.le
    have hlog : Real.log (bandProfile ρ p2 τ) ≤ Real.log (ρ.real univ) - τ * E := by
      have := Real.log_le_log hC (bandProfile_le hb.1 p2 hτ.le)
      rwa [Real.log_mul hW.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
    have : E - Real.log (ρ.real univ) / τ ≤ -Real.log (bandProfile ρ p2 τ) / τ := by
      rw [le_div_iff₀ hτ, sub_mul, div_mul_cancel₀ _ hτ.ne']
      nlinarith
    linarith
  · intro b hb'
    set ε := ((b - E) / 2) ^ 2 with hεdef
    have hε : 0 < ε := by positivity
    have hsε : Real.sqrt ε = (b - E) / 2 := Real.sqrt_sq (by linarith)
    have hE' : shell (M2 + ε) p2 < b := by
      have := shell_add_le hM hε.le
      rw [hsε] at this
      linarith
    have hw : 0 < ρ.real (Ico M2 (M2 + ε)) := real_pos_of_pos (hb.2 ε hε)
    filter_upwards [(hlim (shell (M2 + ε) p2) (Real.log (ρ.real (Ico M2 (M2 + ε))))).eventually
      (gt_mem_nhds hE'), eventually_gt_atTop 0] with τ h1 hτ
    have hlo := le_bandProfile ρ M2 ε p2 hτ.le
    have hC0 : 0 < Real.exp (-(τ * shell (M2 + ε) p2)) * ρ.real (Ico M2 (M2 + ε)) :=
      mul_pos (Real.exp_pos _) hw
    have hlog : Real.log (ρ.real (Ico M2 (M2 + ε))) - τ * shell (M2 + ε) p2
        ≤ Real.log (bandProfile ρ p2 τ) := by
      have := Real.log_le_log hC0 hlo
      rw [Real.log_mul (Real.exp_pos _).ne' hw.ne', Real.log_exp] at this
      linarith
    have : -Real.log (bandProfile ρ p2 τ) / τ
        ≤ shell (M2 + ε) p2 - Real.log (ρ.real (Ico M2 (M2 + ε))) / τ := by
      rw [div_le_iff₀ hτ, sub_mul, div_mul_cancel₀ _ hτ.ne']
      nlinarith
    linarith

/-- **The mass from one momentum sector**: if the sector read tends to `r`, then `M2 = r² − p²`.
DERIVED: `2` the square. -/
theorem mass_of_band_read {ρ : Measure ℝ} [IsFiniteMeasure ρ] {M2 p2 r : ℝ} (hb : SpecBottom ρ M2)
    (hM : 0 ≤ M2 + p2) (hr : Tendsto (fun τ => -Real.log (bandProfile ρ p2 τ) / τ) atTop (𝓝 r)) :
    M2 = r ^ 2 - p2 := by
  have := tendsto_nhds_unique hr (shell_rate hb hM)
  rw [this, shell, Real.sq_sqrt hM]
  ring

/-- **Gap iff band excess**: the bottom of the mass spectrum is positive exactly when the sector read
exceeds the momentum `√p²`. DERIVED: `0` the signs. -/
theorem gap_iff_band_excess {ρ : Measure ℝ} [IsFiniteMeasure ρ] {M2 p2 r : ℝ} (hb : SpecBottom ρ M2)
    (hp : 0 ≤ p2) (hM : 0 ≤ M2 + p2)
    (hr : Tendsto (fun τ => -Real.log (bandProfile ρ p2 τ) / τ) atTop (𝓝 r)) :
    0 < M2 ↔ Real.sqrt p2 < r := by
  rw [tendsto_nhds_unique hr (shell_rate hb hM), shell, Real.sqrt_lt_sqrt_iff hp]
  constructor <;> intro h <;> linarith

/-- **The rest sector is the bottom over all sectors**: `shell M2 0 = √M2 ≤ shell M2 p2`.
DERIVED: `0` the rest momentum and the sign. -/
theorem rest_is_bottom (M2 : ℝ) {p2 : ℝ} (hp : 0 ≤ p2) :
    shell M2 0 = Real.sqrt M2 ∧ shell M2 0 ≤ shell M2 p2 :=
  ⟨by simp [shell], Real.sqrt_le_sqrt (by linarith)⟩

/-- **The in-aperture sector in aperture units is the crossover**:
`A · shell M2 (c/A)² = cross (√M2) c A`. DERIVED: `2` the squares. -/
theorem aperture_shell {M2 A : ℝ} (hM : 0 ≤ M2) (hA : 0 < A) (c : ℝ) :
    A * shell M2 ((c / A) ^ 2) = MassGap.FreqRead.cross (Real.sqrt M2) c A := by
  unfold shell MassGap.FreqRead.cross
  rw [show A * Real.sqrt (M2 + (c / A) ^ 2) = Real.sqrt (A ^ 2 * (M2 + (c / A) ^ 2)) by
    rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]]
  congr 1
  rw [mul_pow, Real.sq_sqrt hM]
  field_simp

/-! ## 2. Load tests -/

/-- **A single mass has bottom at that mass.** DERIVED: `1` the unit mass; `0` the sign. -/
theorem specBottom_dirac (M2 : ℝ) : SpecBottom (Measure.dirac M2) M2 := by
  refine ⟨?_, fun ε hε => ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp
  · rw [Measure.dirac_apply_of_mem (show M2 ∈ Ico M2 (M2 + ε) from ⟨le_refl _, by linarith⟩)]
    exact one_pos

/-- **The free field agrees with `FreqRead`**: at `δ_{m²}` and the box fundamental `p̂²₁`, the read is
`FreqRead.omega m a L 1`. DERIVED: `1` the first kept mode; `2` the square. -/
theorem free_rate_agrees (m a : ℝ) (L : ℕ) :
    Tendsto (fun τ => -Real.log (bandProfile (Measure.dirac (m ^ 2))
      (MassGap.FreqRead.phat2 a L 1) τ) / τ) atTop (𝓝 (MassGap.FreqRead.omega m a L 1)) :=
  shell_rate (specBottom_dirac _)
    (add_nonneg (sq_nonneg m) (MassGap.FreqRead.phat2_nonneg a L 1))

/-- **`FreqRead.band_identity` from the shell**: `mass_of_band_read` at `δ_{m²}` gives
`(A ω₁)² = (A m)² + cL²`. DERIVED: `1` the first kept mode; `2` the squares. -/
theorem band_identity_of_shell (m : ℝ) {a : ℝ} (ha : a ≠ 0) (L : ℕ) :
    (MassGap.FreqRead.aperture a L * MassGap.FreqRead.omega m a L 1) ^ 2
      = (MassGap.FreqRead.aperture a L * m) ^ 2 + MassGap.FreqRead.cL L ^ 2 := by
  have h := mass_of_band_read (specBottom_dirac (m ^ 2))
    (add_nonneg (sq_nonneg m) (MassGap.FreqRead.phat2_nonneg a L 1)) (free_rate_agrees m a L)
  have hc := MassGap.FreqRead.aperture_sq_phat2_fund ha L
  linear_combination (-(MassGap.FreqRead.aperture a L ^ 2)) * h + hc

/-- **A massive free field has band excess.** DERIVED: `0` the signs; `2` the square. -/
theorem massive_excess {m p2 : ℝ} (hm : 0 < m) (hp : 0 ≤ p2) :
    Real.sqrt p2 < shell (m ^ 2) p2 :=
  (gap_iff_band_excess (specBottom_dirac (m ^ 2)) hp (by positivity)
    (shell_rate (specBottom_dirac _) (by positivity))).mp (by positivity)

/-- **A massless free field has no band excess.** DERIVED: `0` the mass and the signs. -/
theorem massless_no_excess {p2 : ℝ} (hp : 0 ≤ p2) : ¬ Real.sqrt p2 < shell 0 p2 := fun h =>
  lt_irrefl (0 : ℝ) ((gap_iff_band_excess (specBottom_dirac 0) hp (by linarith)
    (shell_rate (specBottom_dirac 0) (by linarith))).mpr h)

/-- **Mass at `0` plus a massive part has bottom `0`.** DERIVED: `0` the bottom and the sign; `1` the
unit mass. -/
theorem specBottom_zero_add {M : ℝ} (hM : 0 ≤ M) :
    SpecBottom (Measure.dirac 0 + Measure.dirac M) 0 := by
  refine ⟨?_, fun ε hε => ?_⟩
  · rw [Measure.add_apply, Measure.dirac_apply' _ measurableSet_Iio,
      Measure.dirac_apply' _ measurableSet_Iio]
    simp [not_lt.mpr hM]
  · rw [Measure.add_apply, Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Ico 0 (0 + ε) from ⟨le_refl _, by linarith⟩)]
    exact lt_of_lt_of_le one_pos le_self_add

/-- **No gap, no band excess**: at `δ_0 + δ_M` the sector read is exactly `√p²`.
DERIVED: `0` the bottom and the signs. -/
theorem zero_mass_no_excess {M p2 r : ℝ} (hM : 0 ≤ M) (hp : 0 ≤ p2)
    (hr : Tendsto (fun τ => -Real.log (bandProfile (Measure.dirac 0 + Measure.dirac M) p2 τ) / τ)
      atTop (𝓝 r)) :
    ¬ Real.sqrt p2 < r ∧ r = Real.sqrt p2 := by
  have hb := specBottom_zero_add hM
  refine ⟨fun h => lt_irrefl (0 : ℝ) ((gap_iff_band_excess hb hp (by linarith) hr).mpr h), ?_⟩
  rw [tendsto_nhds_unique hr (shell_rate hb (by linarith)), shell, zero_add]

end

end MassGap.BandShell

#print axioms MassGap.BandShell.shell_add_le
#print axioms MassGap.BandShell.bandProfile_le
#print axioms MassGap.BandShell.le_bandProfile
#print axioms MassGap.BandShell.shell_rate
#print axioms MassGap.BandShell.mass_of_band_read
#print axioms MassGap.BandShell.gap_iff_band_excess
#print axioms MassGap.BandShell.rest_is_bottom
#print axioms MassGap.BandShell.aperture_shell
#print axioms MassGap.BandShell.specBottom_dirac
#print axioms MassGap.BandShell.free_rate_agrees
#print axioms MassGap.BandShell.band_identity_of_shell
#print axioms MassGap.BandShell.massive_excess
#print axioms MassGap.BandShell.massless_no_excess
#print axioms MassGap.BandShell.specBottom_zero_add
#print axioms MassGap.BandShell.zero_mass_no_excess
