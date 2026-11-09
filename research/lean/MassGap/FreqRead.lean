import Mathlib

/-!
# MassGap.FreqRead — the in-aperture frequency read, in closed form at the free field

Every route input reads either the coarse view (first zoom step) or the fine view (late steps). This
module adds the read neither view carries: the frequency of the signal inside the aperture. It is built at
the free field, where everything is explicit, from proven templates only: the free lattice dispersion
`p̂² = (2/a)² sin²(π j / L)`, the Abbe cut (a wavelength longer than twice the aperture leaves the
picture), equipartition of the free propagator, and the Källén–Lehmann form of a correlator as a sum of
decaying exponentials. The kept band is the cut's: a mode whose wavelength exceeds twice the aperture leaves
the picture. On a periodic box every non-zero mode has wavelength at most `A`, so the cut removes exactly the
zero mode for any factor of at least `1`; the factor `2` is the Abbe convention and does not affect the
result. No frequency or mode count is chosen: the frequencies are the spectrum's own, and the read is the
decay rate of the measured profile.
Declarations are in the namespace `MassGap.FreqRead`.

## 1. The box, the dispersion and the cut (proved)

A periodic box of `L` cells of spacing `a` has aperture `A = L a` (`aperture`) and modes `j < L` with
`p̂²_j = (2/a)² sin²(π j/L)` (`phat2`) and `ω²_j = m² + p̂²_j` (`omega2`, `omega`). Mode `j` has wavelength
`A / j`; the Abbe cut keeps it when that wavelength is at most `2A` (`Kept`). `kept_iff`: for `a, L > 0` the
cut removes exactly the zero mode, so the diffracted low band is `{0}` and its frequency is
`omega_zero_mode : ω₀ = m`. The kept set is `keptSet L = (range L).erase 0` (`mem_keptSet`).

## 2. The read (proved)

* The library read `entroptics.reads.diffraction_limit` returns an entropy width of the decay power
  `C(τ)²`, which is proportional to the decay rate on a single exponential and a blend of the modes on a
  sum. `effective_rates` reads the lag-local rate `log(c_t / c_{t+1})`, which falls to the slowest mode. The
  Lean read is that rate: `profile s w r τ = ∑_{j∈s} w_j e^{−r_j τ}`, and `profile_rate`: if `j₀ ∈ s` has
  the least rate and every weight is positive, `−log(profile τ)/τ → r_{j₀}`. It corresponds to
  `effective_rates` and agrees with `diffraction_limit` only on a single exponential, up to a constant. The
  rate is measured from the profile; nothing is fitted.
* `kept_rate`: on the kept band of the free field (weights `1/(2ω_j)`, the free propagator), the read is the
  in-aperture fundamental `ω₁` (`phat2_fund_le`: `p̂²_1 ≤ p̂²_j` on the kept band).
* `full_rate`: on the whole box, diffracted band included, the read is `ω₀ = m` (massive field).
* `energyMean_eq_flat` (equipartition): the energy weight `ω² · (1/ω²)` of each kept mode is `1`, so the
  energy-weighted mean of `ω²` over the kept band is the flat mean `meanSqKept`.
* `diffraction_raises_mean`: removing the diffracted band raises the mean squared frequency per mode,
  `meanSqAll ≤ meanSqKept`.

## 3. Two refinement maps (proved)

Magnify `(a, L) ↦ (a/2, L)`: same cells, each covers less. Refine `(a, L) ↦ (a/2, 2L)`: same aperture,
twice the cells.

* `magnify_cell_units`: under magnify the spectrum in cell units `a² p̂²_j` is unchanged mode by mode.
* `magnify_massless`: the massless read in aperture units `A ω₁` is unchanged by magnify.
* `cL_refine_lt`, `refine_raises`: under refine `A ω₁` strictly rises (`cL L < cL (2L)`); its constant is
  bounded, `cL L ≤ 2π` (`cL_le_two_pi`). At `L = 1` the box has no kept mode and `cL 1 = 0`, so the read is
  a kept mode only for `L ≥ 2`.

The tree's zoom step `k ↦ k+1` (`dySpacing` halves, the window `2^k` doubles in cells, the physical window
`aRun 1 / 2` is fixed) is a refine. Along the step coupling `βs = dyBeta`,
`ScaleLightCone.windowReading = 2^k m′(β_k)` is read as `A ω₀`, the slowest decay rate of the periodic state
times the aperture, with `m′` in cell units; this identification is by the definitions, not a theorem here.
The two maps are not conflated in the step: the step is a refine and the read is the full-box read
(`full_rate`).

## 4. The crossover (proved)

`cross m c A = √((mA)² + c²)`. `freqAp_eq`: `A ω₁ = cross m (cL L) A`, `cL L = 2L sin(π/L)`;
`freqApMean_eq`: `A √meanSqKept = cross m (√dL L) A`. For the crossover:

* `cross_tendsto_fine`: `cross m c A → |c|` as `A → 0` (massless behaviour: a pure number of the box);
* `cross_tendsto_coarse`: `cross m c A − m A → 0` as `A → ∞`, `m > 0` (grows like `m A`);
* `cross_strictMonoOn`: strictly increasing on `A ≥ 0` for `m ≠ 0` (no stall);
* `cross_massless`: `cross 0 c A = |c|` at every `A` (no mass, no crossover).
* `band_identity`: `(A ω₁)² = (A ω₀)² + cL²` — the coarse band read is the in-aperture read with the
  diffraction constant removed, exactly, at every aperture.

## 5. The interacting version (argued, not proved here)

In the tree's terms the statement would be: the in-aperture read `F_k = 2^k ω₁(β_k)` (the slowest
non-zero-momentum decay rate in window units) and the band read `windowReading k = 2^k m′(β_k)` obey
`F_k² − windowReading_k² → c_∞²` along the zoom with `c_∞` the free constant (bounded by `2π` per axis,
`cL_le_two_pi`), and
`windowReading` is non-decreasing in the aperture. What would follow, plainly:

* `ZoomSettling` / `ZoomSettlesUV`: follows from the interacting identity only if `F_k` settles; `F_k`
  settling at a rate is the UV statement (that `F_k → c_∞`, the free limit, is the content of the Bałaban
  side and is not proved here), so this would replace the settling input by a free-limit comparison; it
  does not follow from the free-field identity alone.
* StrongEnd no-stall: the free crossover is strictly monotone; the interacting monotonicity of
  `windowReading` in the aperture is exactly the no-stall input. It is not implied; it is restated in
  frequency form.
* ExpandMatch's coarse/fine identification: `band_identity` is an exact free identification of the coarse
  band read with the fine read minus `cL²`. The interacting version would supply the identification if the
  correction stays `cL² + o(1)`; that is a new hypothesis, not a discharge.
* ProxyNondeg first non-zero read: `full_rate` gives `m > 0` as the first non-zero band read whenever the
  mass is positive; it does not prove the mass positive.

Nothing in §5 is proved. No route input (`ZoomSettlesUV`, `ZoomSettles`, StrongEnd no-stall, ExpandMatch,
ProxyNondeg) is discharged by this module; each interacting statement above is a new hypothesis, and §§1–4
prove only the free-field identities.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.FreqRead

open Real Filter Topology Finset

noncomputable section

/-! ## 1. The box, the dispersion and the cut -/

/-- **The aperture**: `L` cells of spacing `a`. DERIVED: no numeral. -/
def aperture (a : ℝ) (L : ℕ) : ℝ := (L : ℝ) * a

/-- **The free lattice momentum squared** of mode `j` on the periodic box: `(2/a)² sin²(π j/L)`.
DERIVED: `2` the lattice Laplacian `4 sin²(p/2) = (2 sin(p/2))²`. -/
def phat2 (a : ℝ) (L j : ℕ) : ℝ := (2 / a) ^ 2 * Real.sin (π * j / L) ^ 2

/-- **The free frequency squared** `ω² = m² + p̂²`. DERIVED: `2` the square. -/
def omega2 (m a : ℝ) (L j : ℕ) : ℝ := m ^ 2 + phat2 a L j

/-- **The free frequency** `ω = √(m² + p̂²)`. DERIVED: no numeral. -/
def omega (m a : ℝ) (L j : ℕ) : ℝ := Real.sqrt (omega2 m a L j)

/-- **The Abbe cut**: mode `j` (wavelength `A/j`) stays in the picture when its wavelength is at most twice
the aperture, `A ≤ 2 A j`. DERIVED: `2` the Abbe factor (stated, not selecting: any factor `≥ 1` keeps the same modes). -/
def Kept (a : ℝ) (L j : ℕ) : Prop := aperture a L ≤ 2 * aperture a L * j

/-- DERIVED: `0` the sign. -/
theorem aperture_pos {a : ℝ} {L : ℕ} (ha : 0 < a) (hL : 0 < L) : 0 < aperture a L := by
  have : (0 : ℝ) < L := by exact_mod_cast hL
  unfold aperture; positivity

/-- **The cut removes exactly the zero mode.** DERIVED: `0` the zero mode and the signs; `1` the first
kept mode; `2` the Abbe factor and `1/2` its threshold. -/
theorem kept_iff {a : ℝ} {L j : ℕ} (ha : 0 < a) (hL : 0 < L) : Kept a L j ↔ j ≠ 0 := by
  have hA := aperture_pos ha hL
  unfold Kept
  constructor
  · rintro h rfl
    simp only [Nat.cast_zero, mul_zero] at h
    linarith
  · intro hj
    have h1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    nlinarith

/-- **The kept set**: the box's modes with the diffracted band removed. DERIVED: `0` the zero mode. -/
def keptSet (L : ℕ) : Finset ℕ := (range L).erase 0

/-- DERIVED: `0` the zero mode and the sign. -/
theorem mem_keptSet {a : ℝ} {L j : ℕ} (ha : 0 < a) (hL : 0 < L) :
    j ∈ keptSet L ↔ j < L ∧ Kept a L j := by
  rw [kept_iff ha hL]
  simp [keptSet, mem_erase, and_comm]

/-- DERIVED: `0` the zero mode. -/
theorem phat2_zero (a : ℝ) (L : ℕ) : phat2 a L 0 = 0 := by simp [phat2]

/-- **The diffracted band carries the mass**: `ω₀ = m`. DERIVED: `0` the zero mode and the sign. -/
theorem omega_zero_mode {m : ℝ} (hm : 0 ≤ m) (a : ℝ) (L : ℕ) : omega m a L 0 = m := by
  simp [omega, omega2, phat2_zero, Real.sqrt_sq hm]

/-- DERIVED: `0` the sign; `2` the square. -/
theorem phat2_nonneg (a : ℝ) (L j : ℕ) : 0 ≤ phat2 a L j := by unfold phat2; positivity

/-- **The fundamental is the least kept sine.** DERIVED: `1` the first kept mode; `2` the half-turn
`π/2`. -/
theorem sin_fund_le {L j : ℕ} (hj1 : 1 ≤ j) (hjL : j + 1 ≤ L) :
    Real.sin (π * 1 / L) ≤ Real.sin (π * j / L) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjL' : (j : ℝ) + 1 ≤ L := by exact_mod_cast hjL
  have h0 : 0 ≤ π * 1 / L := by positivity
  have hx0 : π * 1 / L ≤ π * j / L :=
    div_le_div_of_nonneg_right (by nlinarith [pi_pos]) hL.le
  have hsum : π * 1 / L + π * j / L ≤ π := by
    have : π * 1 / L + π * j / L = π * (1 + j) / L := by ring
    rw [this, div_le_iff₀ hL]; nlinarith [pi_pos]
  by_cases hx : π * j / L ≤ π / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hx hx0
  · rw [← Real.sin_pi_sub (π * j / L)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) (by linarith)

/-- DERIVED: `0` the sign; `1` the first kept mode. -/
theorem sin_fund_nonneg {L : ℕ} (hL : 1 ≤ L) : 0 ≤ Real.sin (π * 1 / L) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
  rw [div_le_iff₀ (by linarith)]; nlinarith [pi_pos]

/-- **The in-aperture fundamental is the least kept momentum**: `p̂²_1 ≤ p̂²_j` for `1 ≤ j < L`.
DERIVED: `1` the first kept mode. -/
theorem phat2_fund_le {a : ℝ} {L j : ℕ} (hj1 : 1 ≤ j) (hjL : j + 1 ≤ L) :
    phat2 a L 1 ≤ phat2 a L j := by
  have hs := sin_fund_le hj1 hjL
  have h0 := sin_fund_nonneg (L := L) (by omega)
  simp only [phat2, Nat.cast_one]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith [mul_le_mul hs hs h0 (h0.trans hs)]

/-- **The fundamental is positive on a box of at least two cells.** DERIVED: `0` the sign; `1` the first
kept mode; `2` the least box with a kept mode. -/
theorem phat2_fund_pos {a : ℝ} (ha : a ≠ 0) {L : ℕ} (hL : 2 ≤ L) : 0 < phat2 a L 1 := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hs : 0 < Real.sin (π * 1 / L) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by linarith)]; nlinarith [pi_pos]
  simp only [phat2, Nat.cast_one]
  have h2 : (0 : ℝ) < (2 / a) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (div_ne_zero two_ne_zero ha)))
  exact mul_pos h2 (pow_pos hs 2)

/-- **Every kept mode has positive frequency squared** (massless included). DERIVED: `0` the sign; `1` the
first kept mode; `2` the least box with a kept mode. -/
theorem omega2_kept_pos {m a : ℝ} (ha : a ≠ 0) {L j : ℕ} (hL : 2 ≤ L) (hj : j ∈ keptSet L) :
    0 < omega2 m a L j := by
  simp only [keptSet, mem_erase, mem_range] at hj
  have := phat2_fund_le (a := a) (L := L) (j := j) (by omega) (by omega)
  have := phat2_fund_pos ha hL
  unfold omega2; nlinarith [sq_nonneg m]

/-! ## 2. The read -/

/-- **The decay profile** (Källén–Lehmann form): `∑_{j∈s} w_j e^{−r_j τ}`. DERIVED: no numeral. -/
def profile (s : Finset ℕ) (w r : ℕ → ℝ) (τ : ℝ) : ℝ := ∑ j ∈ s, w j * Real.exp (-(r j * τ))

/-- **The rate read of a profile is its slowest mode**: with positive weights and `j₀` of least rate,
`−log(profile τ)/τ → r_{j₀}`. This is the asymptote of `entroptics.reads.effective_rates`. DERIVED: `0` the signs and the vanishing `c/τ`. -/
theorem profile_rate {s : Finset ℕ} {w r : ℕ → ℝ} {j₀ : ℕ} (hj₀ : j₀ ∈ s)
    (hw : ∀ j ∈ s, 0 < w j) (hr : ∀ j ∈ s, r j₀ ≤ r j) :
    Tendsto (fun τ => -Real.log (profile s w r τ) / τ) atTop (𝓝 (r j₀)) := by
  set W := ∑ j ∈ s, w j with hWdef
  have hw0 := hw j₀ hj₀
  have hW : 0 < W := lt_of_lt_of_le hw0
    (Finset.single_le_sum (fun j hj => (hw j hj).le) hj₀)
  have hlo : ∀ τ, w j₀ * Real.exp (-(r j₀ * τ)) ≤ profile s w r τ := fun τ =>
    Finset.single_le_sum (f := fun j => w j * Real.exp (-(r j * τ)))
      (fun j hj => (mul_pos (hw j hj) (Real.exp_pos _)).le) hj₀
  have hhi : ∀ τ, 0 ≤ τ → profile s w r τ ≤ W * Real.exp (-(r j₀ * τ)) := by
    intro τ hτ
    unfold profile
    rw [hWdef, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (hw j hj).le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hr j hj) hτ]
  have hlim : ∀ c : ℝ, Tendsto (fun τ : ℝ => r j₀ - c / τ) atTop (𝓝 (r j₀)) := by
    intro c
    simpa using (tendsto_const_nhds (x := r j₀)).sub
      ((tendsto_const_nhds (x := c)).div_atTop tendsto_id)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (Real.log W)) (hlim (Real.log (w j₀)))
  · filter_upwards [eventually_gt_atTop 0] with τ hτ
    have hC : 0 < profile s w r τ := lt_of_lt_of_le (mul_pos hw0 (Real.exp_pos _)) (hlo τ)
    have hlog : Real.log (profile s w r τ) ≤ Real.log W - r j₀ * τ := by
      have := Real.log_le_log hC (hhi τ hτ.le)
      rwa [Real.log_mul hW.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
    rw [le_div_iff₀ hτ, sub_mul, div_mul_cancel₀ _ hτ.ne']
    linarith
  · filter_upwards [eventually_gt_atTop 0] with τ hτ
    have hC : 0 < w j₀ * Real.exp (-(r j₀ * τ)) := mul_pos hw0 (Real.exp_pos _)
    have hlog : Real.log (w j₀) - r j₀ * τ ≤ Real.log (profile s w r τ) := by
      have := Real.log_le_log hC (hlo τ)
      rwa [Real.log_mul hw0.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
    rw [div_le_iff₀ hτ, sub_mul, div_mul_cancel₀ _ hτ.ne']
    linarith

/-- **The free propagator weight** of mode `j` in the time profile: `1/(2ω_j)`. DERIVED: `2` the
free propagator `e^{−ω τ}/(2ω)`. -/
def propW (m a : ℝ) (L : ℕ) (j : ℕ) : ℝ := 1 / (2 * omega m a L j)

/-- **The in-aperture read is the fundamental**: on the kept band of the free field the rate read is `ω₁`.
DERIVED: `1` the first kept mode; `2` the least box with a kept mode. -/
theorem kept_rate {m a : ℝ} (ha : a ≠ 0) {L : ℕ} (hL : 2 ≤ L) :
    Tendsto (fun τ => -Real.log (profile (keptSet L) (propW m a L) (omega m a L) τ) / τ) atTop
      (𝓝 (omega m a L 1)) := by
  have h1 : 1 ∈ keptSet L := by
    simp only [keptSet, mem_erase, mem_range]; exact ⟨one_ne_zero, by omega⟩
  apply profile_rate h1
  · intro j hj
    have := omega2_kept_pos (m := m) ha hL hj
    unfold propW omega
    have : 0 < Real.sqrt (omega2 m a L j) := Real.sqrt_pos.mpr this
    exact div_pos one_pos (mul_pos two_pos this)
  · intro j hj
    simp only [keptSet, mem_erase, mem_range] at hj
    unfold omega omega2
    exact Real.sqrt_le_sqrt (by linarith [phat2_fund_le (a := a) (L := L) (j := j) (by omega) (by omega)])

/-- **The full-box read is the mass**: with the diffracted band in, the rate read is `ω₀ = m` (`m > 0`).
DERIVED: `0` the zero mode and the sign. -/
theorem full_rate {m a : ℝ} (hm : 0 < m) {L : ℕ} (hL : 0 < L) :
    Tendsto (fun τ => -Real.log (profile (range L) (propW m a L) (omega m a L) τ) / τ) atTop (𝓝 m) := by
  have h0 : 0 ∈ range L := mem_range.mpr hL
  have := profile_rate (w := propW m a L) (r := omega m a L) h0 ?_ ?_
  · rwa [omega_zero_mode hm.le] at this
  · intro j _
    have : 0 < omega2 m a L j := by unfold omega2; nlinarith [phat2_nonneg a L j]
    unfold propW omega
    have : 0 < Real.sqrt (omega2 m a L j) := Real.sqrt_pos.mpr this
    exact div_pos one_pos (mul_pos two_pos this)
  · intro j _
    unfold omega omega2
    exact Real.sqrt_le_sqrt (by linarith [phat2_nonneg a L j, phat2_zero a L])

/-- **The free power** of mode `j`, `1/ω²`. DERIVED: no numeral. -/
def power (m a : ℝ) (L j : ℕ) : ℝ := (omega2 m a L j)⁻¹

/-- **The energy weight** of mode `j`, `ω² · power`. DERIVED: no numeral. -/
def energyWeight (m a : ℝ) (L j : ℕ) : ℝ := omega2 m a L j * power m a L j

/-- **The energy-weighted mean of `ω²`** over a set of modes. DERIVED: no numeral. -/
def energyMean (m a : ℝ) (L : ℕ) (s : Finset ℕ) : ℝ :=
  (∑ j ∈ s, energyWeight m a L j * omega2 m a L j) / ∑ j ∈ s, energyWeight m a L j

/-- **Equipartition**: where no mode has zero frequency, the energy-weighted mean is the flat mean.
DERIVED: `1` the unit energy per mode. -/
theorem energyMean_eq_flat {m a : ℝ} {L : ℕ} {s : Finset ℕ} (hs : ∀ j ∈ s, omega2 m a L j ≠ 0) :
    energyMean m a L s = (∑ j ∈ s, omega2 m a L j) / s.card := by
  have he : ∀ j ∈ s, energyWeight m a L j = 1 := fun j hj => mul_inv_cancel₀ (hs j hj)
  have h1 : ∑ j ∈ s, energyWeight m a L j * omega2 m a L j = ∑ j ∈ s, omega2 m a L j :=
    Finset.sum_congr rfl (fun j hj => by rw [he j hj, one_mul])
  have h2 : ∑ j ∈ s, energyWeight m a L j = ∑ _j ∈ s, (1 : ℝ) := Finset.sum_congr rfl he
  unfold energyMean
  rw [h1, h2]
  simp

/-- **The mean squared frequency over the kept band.** DERIVED: `1` the removed zero mode. -/
def meanSqKept (m a : ℝ) (L : ℕ) : ℝ := (∑ j ∈ keptSet L, omega2 m a L j) / ((L : ℝ) - 1)

/-- **The mean squared frequency over the whole box.** DERIVED: no numeral. -/
def meanSqAll (m a : ℝ) (L : ℕ) : ℝ := (∑ j ∈ range L, omega2 m a L j) / L

/-- DERIVED: `0` the zero mode; `1` the removed mode. -/
theorem card_keptSet {L : ℕ} (hL : 1 ≤ L) : ((keptSet L).card : ℝ) = (L : ℝ) - 1 := by
  rw [keptSet, Finset.card_erase_of_mem (mem_range.mpr (by omega)), Finset.card_range,
    Nat.cast_sub hL, Nat.cast_one]

/-- **The kept read is the energy-weighted read.** DERIVED: `2` the least box with a kept mode. -/
theorem energyMean_kept {m a : ℝ} (ha : a ≠ 0) {L : ℕ} (hL : 2 ≤ L) :
    energyMean m a L (keptSet L) = meanSqKept m a L := by
  rw [energyMean_eq_flat (fun j hj => (omega2_kept_pos ha hL hj).ne'), card_keptSet (by omega)]
  rfl

/-- **Removing the diffracted band raises the mean squared frequency per mode.** DERIVED: `0` the zero
mode; `1` the removed mode; `2` the least box with a kept mode. -/
theorem diffraction_raises_mean (m a : ℝ) {L : ℕ} (hL : 2 ≤ L) :
    meanSqAll m a L ≤ meanSqKept m a L := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hsplit := Finset.add_sum_erase (range L) (omega2 m a L) (mem_range.mpr (by omega : 0 < L))
  have hK : ((L : ℝ) - 1) * m ^ 2 ≤ ∑ j ∈ keptSet L, omega2 m a L j := by
    rw [← card_keptSet (by omega), ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j _ => by unfold omega2; linarith [phat2_nonneg a L j]
  have h0 : omega2 m a L 0 = m ^ 2 := by simp [omega2, phat2_zero]
  unfold meanSqAll meanSqKept
  rw [← hsplit, h0, div_le_div_iff₀ (by linarith) (by linarith)]
  change (m ^ 2 + ∑ j ∈ keptSet L, omega2 m a L j) * ((L : ℝ) - 1) ≤ _
  nlinarith

/-! ## 3. Two refinement maps -/

/-- **The massless in-aperture constant** `cL L = 2L sin(π/L)`: `A p̂₁` on `L` cells.
DERIVED: `2` the lattice Laplacian. -/
def cL (L : ℕ) : ℝ := 2 * L * Real.sin (π / L)

/-- **`A² p̂²₁ = cL²`**: the fundamental in aperture units depends on the cell count only.
DERIVED: `2` the square. -/
theorem aperture_sq_phat2_fund {a : ℝ} (ha : a ≠ 0) (L : ℕ) :
    aperture a L ^ 2 * phat2 a L 1 = cL L ^ 2 := by
  simp only [aperture, phat2, cL, Nat.cast_one, mul_one]
  have h2 : a * (2 / a) = 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ ha]
  calc ((L : ℝ) * a) ^ 2 * ((2 / a) ^ 2 * Real.sin (π / L) ^ 2)
      = ((L : ℝ) * (a * (2 / a))) ^ 2 * Real.sin (π / L) ^ 2 := by ring
    _ = (2 * L * Real.sin (π / L)) ^ 2 := by rw [h2]; ring

/-- **Magnify keeps the cell-unit spectrum**: `(a/2)² p̂²_j(a/2) = a² p̂²_j(a)`. DERIVED: `2` the halving
and the square. -/
theorem magnify_cell_units {a : ℝ} (ha : a ≠ 0) (L j : ℕ) :
    (a / 2) ^ 2 * phat2 (a / 2) L j = a ^ 2 * phat2 a L j := by
  unfold phat2
  generalize Real.sin (π * j / L) ^ 2 = s
  have ha2 : a / 2 ≠ 0 := div_ne_zero ha two_ne_zero
  have h1 : a / 2 * (2 / (a / 2)) = 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ ha2]
  have h2 : a * (2 / a) = 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ ha]
  calc (a / 2) ^ 2 * ((2 / (a / 2)) ^ 2 * s) = (a / 2 * (2 / (a / 2))) ^ 2 * s := by ring
    _ = (a * (2 / a)) ^ 2 * s := by rw [h1, h2]
    _ = a ^ 2 * ((2 / a) ^ 2 * s) := by ring

/-- **The massless constant is bounded by the continuum value** `2π`. DERIVED: `2` the lattice
Laplacian; `π` the half-turn bound (`sin x ≤ x`); `0` the sign. -/
theorem cL_le_two_pi (L : ℕ) : cL L ≤ 2 * π := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp only [cL, Nat.cast_zero, mul_zero, zero_mul]; positivity
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hs := Real.sin_le (by positivity : (0 : ℝ) ≤ π / L)
  have : (L : ℝ) * (π / L) = π := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hL'.ne']
  unfold cL
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * L)]

/-- DERIVED: `0` the sign; `1` the least box. -/
theorem cL_nonneg {L : ℕ} (hL : 1 ≤ L) : 0 ≤ cL L := by
  have := sin_fund_nonneg hL
  simp only [mul_one] at this
  unfold cL; exact mul_nonneg (by positivity) this

/-- **Refine strictly raises the massless constant**: `cL L < cL (2L)`. DERIVED: `2` the doubling;
`1` the least box; `0` the signs. -/
theorem cL_refine_lt {L : ℕ} (hL : 1 ≤ L) : cL L < cL (2 * L) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hx0 : 0 < π / (2 * (L : ℝ)) := by positivity
  have hxpi : π / (2 * (L : ℝ)) < π := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hs : 0 < Real.sin (π / (2 * (L : ℝ))) := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hc : Real.cos (π / (2 * (L : ℝ))) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hxpi.le hx0
    simpa using this
  have h2 : π / (L : ℝ) = 2 * (π / (2 * (L : ℝ))) := by ring
  unfold cL
  push_cast
  rw [h2, Real.sin_two_mul]
  nlinarith [mul_pos (mul_pos hLpos hs) (sub_pos.mpr hc)]

/-! ## 4. The crossover -/

/-- **The crossover**: `√((mA)² + c²)`. DERIVED: `2` the squares. -/
def cross (m c A : ℝ) : ℝ := Real.sqrt ((m * A) ^ 2 + c ^ 2)

/-- **The in-aperture read in aperture units**: `A ω₁`. DERIVED: `1` the first kept mode. -/
def freqAp (m a : ℝ) (L : ℕ) : ℝ := aperture a L * omega m a L 1

/-- **`A ω₁` is the crossover with the massless constant.** DERIVED: `2` the square. -/
theorem freqAp_eq {m a : ℝ} (ha : 0 < a) (L : ℕ) :
    freqAp m a L = cross m (cL L) (aperture a L) := by
  have hA : 0 ≤ aperture a L := by unfold aperture; positivity
  unfold freqAp omega omega2 cross
  conv_lhs => rw [show aperture a L = Real.sqrt (aperture a L ^ 2) from (Real.sqrt_sq hA).symm]
  rw [← Real.sqrt_mul (sq_nonneg (aperture a L))]
  congr 1
  rw [mul_add, aperture_sq_phat2_fund ha.ne']
  ring

/-- **The band identity**: `(A ω₁)² = (A ω₀)² + cL²` — the coarse band read is the in-aperture read with
the diffraction constant removed. DERIVED: `2` the squares; `0` the zero mode; `1` the first kept mode. -/
theorem band_identity {m a : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (L : ℕ) :
    freqAp m a L ^ 2 = (aperture a L * omega m a L 0) ^ 2 + cL L ^ 2 := by
  rw [freqAp_eq ha, omega_zero_mode hm, cross, Real.sq_sqrt (by positivity)]
  ring

/-- **Fine end**: `cross m c A → |c|` as `A → 0`. DERIVED: `0` the limit point; `2` the squares in `cross`. -/
theorem cross_tendsto_fine (m c : ℝ) : Tendsto (cross m c) (𝓝 0) (𝓝 |c|) := by
  have hcont : Continuous (fun A => cross m c A) := by
    show Continuous (fun A => Real.sqrt ((m * A) ^ 2 + c ^ 2))
    exact Real.continuous_sqrt.comp (by fun_prop : Continuous fun A : ℝ => (m * A) ^ 2 + c ^ 2)
  rw [show |c| = cross m c 0 by simp [cross, Real.sqrt_sq_eq_abs]]
  exact hcont.tendsto 0

/-- DERIVED: `0` the sign; `2` the squares. -/
theorem cross_sub_le {m c A : ℝ} (hm : 0 < m) (hA : 0 < A) :
    0 ≤ cross m c A - m * A ∧ cross m c A - m * A ≤ c ^ 2 / (m * A) := by
  have hmA : 0 < m * A := mul_pos hm hA
  have hsq : cross m c A ^ 2 = (m * A) ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hge : m * A ≤ cross m c A := by
    unfold cross
    calc m * A = Real.sqrt ((m * A) ^ 2) := (Real.sqrt_sq hmA.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg c])
  refine ⟨by linarith, ?_⟩
  rw [le_div_iff₀ hmA]
  nlinarith [mul_nonneg (sub_nonneg.mpr hge) (hmA.le.trans hge)]

/-- **Coarse end**: `cross m c A − m A → 0` as `A → ∞` (`m > 0`): the read grows like `m A`.
DERIVED: `0` the limit and the signs. -/
theorem cross_tendsto_coarse {m : ℝ} (hm : 0 < m) (c : ℝ) :
    Tendsto (fun A => cross m c A - m * A) atTop (𝓝 0) := by
  have hden : Tendsto (fun A : ℝ => m * A) atTop atTop := Tendsto.const_mul_atTop hm tendsto_id
  have hup : Tendsto (fun A : ℝ => c ^ 2 / (m * A)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_gt_atTop 0] with A hA using (cross_sub_le hm hA).1
  · filter_upwards [eventually_gt_atTop 0] with A hA using (cross_sub_le hm hA).2

/-- **No stall**: for `m ≠ 0` the crossover strictly increases on `A ≥ 0`. DERIVED: `0` the sign; `2` the squares in `cross`. -/
theorem cross_strictMonoOn {m : ℝ} (hm : m ≠ 0) (c : ℝ) : StrictMonoOn (cross m c) (Set.Ici 0) := by
  intro A hA B _ hAB
  simp only [Set.mem_Ici] at hA
  unfold cross
  apply Real.sqrt_lt_sqrt (by positivity)
  have hm2 : 0 < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  nlinarith [mul_lt_mul_of_pos_left (mul_self_lt_mul_self hA hAB) hm2]

/-- **No mass, no crossover**: `cross 0 c A = |c|` at every aperture. DERIVED: `0` the mass; `2` the squares in `cross`. -/
theorem cross_massless (c A : ℝ) : cross 0 c A = |c| := by
  simp [cross, Real.sqrt_sq_eq_abs]

/-- **Magnify leaves the massless read fixed.** DERIVED: `2` the halving; `0` the mass. -/
theorem magnify_massless {a : ℝ} (ha : 0 < a) (L : ℕ) : freqAp 0 (a / 2) L = freqAp 0 a L := by
  rw [freqAp_eq ha, freqAp_eq (a := a / 2) (by positivity), cross_massless, cross_massless]

/-- **Magnify slides along the crossover**: the aperture halves, the constant stays. DERIVED: `2` the
halving. -/
theorem magnify_slides {m a : ℝ} (ha : 0 < a) (L : ℕ) :
    freqAp m (a / 2) L = cross m (cL L) (aperture a L / 2) := by
  rw [freqAp_eq (a := a / 2) (by positivity)]
  congr 1
  unfold aperture; ring

/-- **Refine raises the read at fixed aperture**, massive or massless. DERIVED: `2` the halving and the
doubling; `1` the least box. -/
theorem refine_raises {m a : ℝ} (ha : 0 < a) {L : ℕ} (hL : 1 ≤ L) :
    freqAp m a L < freqAp m (a / 2) (2 * L) := by
  have hAeq : aperture (a / 2) (2 * L) = aperture a L := by unfold aperture; push_cast; ring
  rw [freqAp_eq ha, freqAp_eq (a := a / 2) (by positivity), hAeq]
  unfold cross
  apply Real.sqrt_lt_sqrt (by positivity)
  have h0 := cL_nonneg hL
  have h1 := cL_refine_lt hL
  nlinarith [mul_self_lt_mul_self h0 h1]

/-- **The kept mean in aperture units**: `A² · meanSqKept = (mA)² + dL L`, with `dL` a number of the box.
DERIVED: `4` the lattice Laplacian `(2 sin)²`; `1` the removed mode. -/
def dL (L : ℕ) : ℝ := 4 * (L : ℝ) ^ 2 * (∑ j ∈ keptSet L, Real.sin (π * j / L) ^ 2) / ((L : ℝ) - 1)

/-- DERIVED: `2` the squares and the least box with a kept mode. -/
theorem aperture_sq_meanSqKept {m a : ℝ} (ha : a ≠ 0) {L : ℕ} (hL : 2 ≤ L) :
    aperture a L ^ 2 * meanSqKept m a L = (m * aperture a L) ^ 2 + dL L := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hL1 : (L : ℝ) - 1 ≠ 0 := by linarith
  have hsum : ∑ j ∈ keptSet L, omega2 m a L j
      = ((L : ℝ) - 1) * m ^ 2 + (2 / a) ^ 2 * ∑ j ∈ keptSet L, Real.sin (π * j / L) ^ 2 := by
    simp only [omega2, phat2]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_keptSet (by omega),
      ← Finset.mul_sum]
  unfold meanSqKept dL aperture
  rw [hsum]
  field_simp
  ring

/-- DERIVED: `0` the sign; `2` the least box with a kept mode; `4` the positive constant. -/
theorem dL_nonneg {L : ℕ} (hL : 2 ≤ L) : 0 ≤ dL L := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  unfold dL
  apply div_nonneg ?_ (by linarith)
  have := Finset.sum_nonneg (s := keptSet L) (fun j _ => sq_nonneg (Real.sin (π * j / L)))
  positivity

/-- **The mean read in aperture units** `A √meanSqKept`. DERIVED: no numeral. -/
def freqApMean (m a : ℝ) (L : ℕ) : ℝ := aperture a L * Real.sqrt (meanSqKept m a L)

/-- **The mean read is the crossover with constant `√dL`.** DERIVED: `2` the squares and the least box
with a kept mode. -/
theorem freqApMean_eq {m a : ℝ} (ha : 0 < a) {L : ℕ} (hL : 2 ≤ L) :
    freqApMean m a L = cross m (Real.sqrt (dL L)) (aperture a L) := by
  have hA : 0 ≤ aperture a L := by unfold aperture; positivity
  unfold freqApMean cross
  conv_lhs => rw [show aperture a L = Real.sqrt (aperture a L ^ 2) from (Real.sqrt_sq hA).symm]
  rw [← Real.sqrt_mul (sq_nonneg _), aperture_sq_meanSqKept ha.ne' hL, Real.sq_sqrt (dL_nonneg hL)]

end

end MassGap.FreqRead

#print axioms MassGap.FreqRead.kept_iff
#print axioms MassGap.FreqRead.mem_keptSet
#print axioms MassGap.FreqRead.omega_zero_mode
#print axioms MassGap.FreqRead.phat2_fund_le
#print axioms MassGap.FreqRead.phat2_fund_pos
#print axioms MassGap.FreqRead.omega2_kept_pos
#print axioms MassGap.FreqRead.profile_rate
#print axioms MassGap.FreqRead.kept_rate
#print axioms MassGap.FreqRead.full_rate
#print axioms MassGap.FreqRead.energyMean_eq_flat
#print axioms MassGap.FreqRead.energyMean_kept
#print axioms MassGap.FreqRead.diffraction_raises_mean
#print axioms MassGap.FreqRead.magnify_cell_units
#print axioms MassGap.FreqRead.magnify_massless
#print axioms MassGap.FreqRead.magnify_slides
#print axioms MassGap.FreqRead.cL_le_two_pi
#print axioms MassGap.FreqRead.cL_refine_lt
#print axioms MassGap.FreqRead.refine_raises
#print axioms MassGap.FreqRead.freqAp_eq
#print axioms MassGap.FreqRead.band_identity
#print axioms MassGap.FreqRead.freqApMean_eq
#print axioms MassGap.FreqRead.aperture_sq_meanSqKept
#print axioms MassGap.FreqRead.cross_tendsto_fine
#print axioms MassGap.FreqRead.cross_tendsto_coarse
#print axioms MassGap.FreqRead.cross_strictMonoOn
#print axioms MassGap.FreqRead.cross_massless
