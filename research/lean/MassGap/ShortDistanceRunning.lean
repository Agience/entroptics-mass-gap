import Mathlib
import MassGap.PointReadingRatio
import MassGap.WDeltaRun

noncomputable section

/-!
# MassGap.ShortDistanceRunning — ultraviolet control of the Wilson family, and what it carries

`UVControl hN O` is one statement about the Wilson `SU(N)` lattice family alone, at the tree's field `O`.
It has two clauses, both at fixed physical scales below one `s₀ < 1` and uniform in the spacing:

* **(D) `DefectBounded N s₀`, the free energy at fixed physical size.** For every window `[c, C]` of physical
  sizes, `0 < c`, `C ≤ s₀`, the doubling defect `defectW N β n = 16 log ZR(n⁴) − log ZR((2n)⁴)` on power-of-two tori
  with `n · aRun N β ∈ [c, C]` is bounded by one `S`, eventually in `β`. The defect cancels the bulk free
  energy exactly, so this is the finite-volume ultraviolet stability of the torus at fixed physical size.
* **(R) `RunningBelow hN O s₀ K δ`, the running of the canonical two-point reading.** Below a scale
  `s₀ < 1`, for every pair `s < s' ≤ s₀`, eventually in the step, the unit-strength reflected cube-pair
  readings `x = refReading hN O s s k` (cube of side `s` at margin `s`) and `x'` at `s'` are positive and
  `|log(x (log s)²) − log(x' (log s')²)| ≤ K ((−log s')^{−δ} − (−log s)^{−δ})` (`RunBound`). At `s' = 2s`
  this is `x/x' = (1 − log 2/log(1/s))² · (1 + O(log(1/s)^{−1−δ}))`: the asymptotically free ratio of the
  readings at `s` and `2s`, with a summable correction. `runningBelow_of_octave`: the bound on pairs at most
  one octave apart (`RunningOctave`) gives it on every pair, because the errors telescope
  (`runBound_trans`).

No clause names one of the capstone's hypotheses, and the definitions use only `ZR`, `aRun` and the unit-strength
lattice readings.

What it carries, proved here:

* `exists_tendsto_of_modulus`: a function with a vanishing modulus at `0⁺` has a limit there.
* `refPos_of_running`: (R) gives the reference positivity `0 < refReading hN O s₀ s₀ k`, eventually.
* `runSeed_of_defect`: (D) with the infrared input `DefectDescent N s₀` gives `WDeltaRun.RunSeed N`.
* `pointRatio_of_running`: (R) with the scale-local input `PointCubeLocal hN O s₀` gives
  `PointReadingRatio.PointRatio hN O s₀ s₀`, hence E. (R) carries the running from the point's scale `d`
  to the reference scale `s₀`, which is where the drifting-exponent control fails.
* `splitThreePoint_of_running`: (R) with `SplitCubic hN O s₀ s₀` gives `SplitThreePoint`. (R) supplies the
  positivity conjunct only.

Controls, proved here: `not_running_of_ratio_unbounded` (the generalised free field with drifting Källén–Lehmann weight `μ^{γ_k}`:
the ratio of the readings at two fixed scales grows without bound in the step) and
`not_running_of_vanishing` (`β = 0`: connected readings of disjoint supports vanish).

DERIVED (module-wide): `0` the reflection plane, signs and the point approached; `1` where `log` changes
sign; `2` the square of the logarithm (two insertions, each `ḡ²`), the doubling of the side, and the
halving `s₀/2`; `3` the window `[C₁, 3C₁]`, which contains `nP · a ∈ [C₁, 2C₁ + 2a]` once `a ≤ C₁/4`
(`DoublingClay2.nP_bounds` at `ℓ₀ = C₁/2`); `4` that `a ≤ ℓ₀/2`; `8` the canonical dimension count of the
point readings; `16` and `1/1000` the seed's.
-/

namespace MassGap.ShortDistanceRunning

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ExistenceReduce MassGap.NonTrivialCanonical MassGap.ExistencePoint Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The statement -/

/-- The error of the running bound between scales `s < s'`: `K ((−log s')^{−δ} − (−log s)^{−δ})`. -/
def runErr (K δ s s' : ℝ) : ℝ := K * ((-Real.log s') ^ (-δ) - (-Real.log s) ^ (-δ))

/-- **The running bound** between two readings `x` at scale `s` and `x'` at scale `s'`. -/
def RunBound (K δ s s' x x' : ℝ) : Prop :=
  0 < x ∧ 0 < x' ∧
    |Real.log (x * Real.log s ^ 2) - Real.log (x' * Real.log s' ^ 2)| ≤ runErr K δ s s'

/-- **(R) The running of the canonical two-point reading below `s₀`.** For every pair of scales
`s < s' ≤ s₀`, eventually in the step, the unit-strength reflected cube-pair readings at `s` and `s'` satisfy
the running bound. -/
def RunningBelowAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ K δ : ℝ) : Prop :=
  ∀ s s' : ℝ, 0 < s → s < s' → s' ≤ s₀ → ∀ᶠ k in atTop,
    RunBound K δ s s' (refReadingAlong hN βs O s s k) (refReadingAlong hN βs O s' s' k)

/-- `RunningBelow` at the couplings `dyBeta`: `RunningBelowAlong` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
def RunningBelow (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (s₀ K δ : ℝ) : Prop :=
  RunningBelowAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀ K δ


/-- **(D) The doubling defect at fixed physical size below `s₀` is bounded.** For every window `[c, C]` of
physical sizes with `0 < c` and `C ≤ s₀`, one `S` bounds the defect on every power-of-two torus whose physical
side lies in the window, eventually in `β`. -/
def DefectBounded (N : ℕ) (s₀ : ℝ) : Prop :=
  ∀ c C : ℝ, 0 < c → C ≤ s₀ → ∃ S : ℝ, ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n →
    c ≤ (n : ℝ) * AsymptoticScaling.aRun N β → (n : ℝ) * AsymptoticScaling.aRun N β ≤ C →
      ZoomSelfScale.defectW N β n ≤ S

/-- **Ultraviolet control below `s₀`.** -/
def UVControlBelow (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  s₀ < 1 ∧ DefectBounded N s₀ ∧ ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ RunningBelow hN O s₀ K δ

/-- **Ultraviolet control of the Wilson `SU(N)` family at the field `O`.** -/
def UVControl (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) : Prop :=
  ∃ s₀ : ℝ, 0 < s₀ ∧ UVControlBelow hN O s₀

/-- **(R) in one octave.** The running bound for pairs `s < s' ≤ min(2s, s₀)` only: the ratio of the readings
at `s` and at a scale at most twice `s`. -/
def RunningOctaveAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ K δ : ℝ) : Prop :=
  ∀ s s' : ℝ, 0 < s → s < s' → s' ≤ 2 * s → s' ≤ s₀ → ∀ᶠ k in atTop,
    RunBound K δ s s' (refReadingAlong hN βs O s s k) (refReadingAlong hN βs O s' s' k)

/-- `RunningOctave` at the couplings `dyBeta`: `RunningOctaveAlong` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
def RunningOctave (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (s₀ K δ : ℝ) : Prop :=
  RunningOctaveAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀ K δ


/-- **The running bound composes**: the errors telescope. -/
theorem runBound_trans {K δ s m s' x y z : ℝ} (h1 : RunBound K δ s m x y) (h2 : RunBound K δ m s' y z) :
    RunBound K δ s s' x z := by
  obtain ⟨hx, hy, hb1⟩ := h1
  obtain ⟨-, hz, hb2⟩ := h2
  refine ⟨hx, hz, ?_⟩
  have e : runErr K δ s s' = runErr K δ s m + runErr K δ m s' := by unfold runErr; ring
  rw [e]
  calc _ = |(Real.log (x * Real.log s ^ 2) - Real.log (y * Real.log m ^ 2))
          + (Real.log (y * Real.log m ^ 2) - Real.log (z * Real.log s' ^ 2))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hb1 hb2)

/-- **(R) is its one-octave form.** The running bound on every pair below `s₀` follows from the bound on
pairs at most one octave apart. -/
theorem runningBelow_of_octave_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ}
    (h : RunningOctaveAlong hN βs O s₀ K δ) : RunningBelowAlong hN βs O s₀ K δ := by
  have key : ∀ j : ℕ, ∀ s s' : ℝ, 0 < s → s < s' → s' ≤ s₀ → s' ≤ 2 ^ j * s → ∀ᶠ k in atTop,
      RunBound K δ s s' (refReadingAlong hN βs O s s k) (refReadingAlong hN βs O s' s' k) := by
    intro j
    induction j with
    | zero =>
      intro s s' _ hss' _ hj
      simp only [pow_zero, one_mul] at hj
      exact absurd hj (not_le.mpr hss')
    | succ j ih =>
      intro s s' hs hss' hs' hj
      by_cases h2 : s' ≤ 2 * s
      · exact h s s' hs hss' h2 hs'
      · rw [not_le] at h2
        have hm : s < 2 * s := by linarith
        have hm' : 2 * s ≤ s₀ := (le_of_lt h2).trans hs'
        have hj' : s' ≤ 2 ^ j * (2 * s) := by
          calc s' ≤ 2 ^ (j + 1) * s := hj
            _ = 2 ^ j * (2 * s) := by ring
        filter_upwards [h s (2 * s) hs hm le_rfl hm', ih (2 * s) s' (by linarith) h2 hs' hj']
          with k h1 h2'
        exact runBound_trans h1 h2'
  intro s s' hs hss' hs'
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (s' / s) (by norm_num : (1 : ℝ) < 2)
  exact key j s s' hs hss' hs' (by
    have := (div_lt_iff₀ hs).mp hj
    linarith)

/-- `runningBelow_of_octave` at the couplings `dyBeta`: `runningBelow_of_octave_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem runningBelow_of_octave (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ}
    (h : RunningOctave hN O s₀ K δ) : RunningBelow hN O s₀ K δ :=
  runningBelow_of_octave_along hN (dyBeta (one_le_of_ne_zero hN)) O h


/-! ## 2. The running bound as a two-sided ratio -/

/-- On `(0, 1)` the square of the logarithm is positive. -/
theorem log_sq_pos {s : ℝ} (hs : 0 < s) (hs1 : s < 1) : 0 < Real.log s ^ 2 :=
  sq_pos_of_neg (Real.log_neg hs hs1)

/-- **The running bound is a two-sided bound on the ratio**:
`e^{∓E} (log s')²/(log s)²` brackets `x/x'`. -/
theorem ratio_bounds {K δ s s' x x' : ℝ} (hs : 0 < s) (hs1 : s < 1) (hs' : 0 < s') (hs'1 : s' < 1)
    (h : RunBound K δ s s' x x') :
    x / x' ≤ Real.exp (runErr K δ s s') * (Real.log s' ^ 2 / Real.log s ^ 2) ∧
      Real.exp (-runErr K δ s s') * (Real.log s' ^ 2 / Real.log s ^ 2) ≤ x / x' := by
  obtain ⟨hx, hx', hb⟩ := h
  have hA := log_sq_pos hs hs1
  have hA' := log_sq_pos hs' hs'1
  set A := Real.log s ^ 2
  set A' := Real.log s' ^ 2
  set u := x / x' * (A / A') with hu_def
  have hu : 0 < u := by positivity
  have hlog : Real.log (x * A) - Real.log (x' * A') = Real.log u := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    rw [hu_def]
    field_simp
  rw [hlog] at hb
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  have h1 : u ≤ Real.exp (runErr K δ s s') := (Real.log_le_iff_le_exp hu).mp hhi
  have h2 : Real.exp (-runErr K δ s s') ≤ u := (Real.le_log_iff_exp_le hu).mp hlo
  have hxx : x / x' = u * (A' / A) := by
    rw [hu_def]
    field_simp
  have hAA : 0 ≤ A' / A := by positivity
  rw [hxx]
  exact ⟨mul_le_mul_of_nonneg_right h1 hAA, mul_le_mul_of_nonneg_right h2 hAA⟩

/-- **The reference reading is eventually positive.** -/
theorem refPos_of_running_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ} (hs₀ : 0 < s₀)
    (hR : RunningBelowAlong hN βs O s₀ K δ) : ∀ᶠ k in atTop, 0 < refReadingAlong hN βs O s₀ s₀ k :=
  (hR (s₀ / 2) s₀ (by positivity) (by linarith) le_rfl).mono fun _ h => h.2.1

/-- `refPos_of_running` at the couplings `dyBeta`: `refPos_of_running_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem refPos_of_running (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ} (hs₀ : 0 < s₀)
    (hR : RunningBelow hN O s₀ K δ) : ∀ᶠ k in atTop, 0 < refReading hN O s₀ s₀ k :=
  refPos_of_running_along hN (dyBeta (one_le_of_ne_zero hN)) O hs₀ hR


/-! ## 3. Asymptotic freedom of the canonical reading -/

/-- **A function with a vanishing modulus at `0⁺` has a limit there.** If `|f s − f s'| ≤ ε s'` for
`0 < s < s' ≤ s₁` and `ε s' → 0` as `s' → 0⁺`, then `f` converges as `s → 0⁺`. -/
theorem exists_tendsto_of_modulus {f ε : ℝ → ℝ} {s₁ : ℝ} (hs₁ : 0 < s₁)
    (hε0 : ∀ s, 0 < s → s ≤ s₁ → 0 ≤ ε s) (hε : Tendsto ε (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h : ∀ s s', 0 < s → s < s' → s' ≤ s₁ → |f s - f s'| ≤ ε s') :
    ∃ F : ℝ, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 F) := by
  let u : ℕ → ℝ := fun n => s₁ * (1 / ((n : ℝ) + 1))
  have hu_pos : ∀ n, 0 < u n := fun n => by positivity
  have hu_le : ∀ n, u n ≤ s₁ := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc u n ≤ s₁ * 1 := mul_le_mul_of_nonneg_left this hs₁.le
      _ = s₁ := mul_one _
  have hu_lt : ∀ n m, n < m → u m < u n := fun n m hnm => by
    have hc : ((n : ℝ) + 1) < (m : ℝ) + 1 := by
      have : (n : ℝ) < m := by exact_mod_cast hnm
      linarith
    have : 1 / ((m : ℝ) + 1) < 1 / ((n : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) hc
    exact mul_lt_mul_of_pos_left this hs₁
  have hu_t : Tendsto u atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall hu_pos⟩
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul s₁
    rw [mul_zero] at h
    exact h
  have hc : CauchySeq (fun n => f (u n)) := by
    refine cauchySeq_of_le_tendsto_0' (fun n => ε (u n)) (fun n m hnm => ?_) (hε.comp hu_t)
    rcases eq_or_lt_of_le hnm with h' | h'
    · subst h'
      simp only [dist_self]
      exact hε0 _ (hu_pos n) (hu_le n)
    · rw [Real.dist_eq, abs_sub_comm]
      exact h (u m) (u n) (hu_pos m) (hu_lt n m h') (hu_le n)
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hc
  have key : ∀ s, 0 < s → s ≤ s₁ → |f s - F| ≤ ε s := by
    intro s hs hs1
    have ht : Tendsto (fun n => |f (u n) - f s|) atTop (𝓝 |F - f s|) := (hF.sub_const _).abs
    have hev : ∀ᶠ n in atTop, u n < s :=
      (hu_t.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds hs)
    have := le_of_tendsto ht (hev.mono fun n hn => h (u n) s (hu_pos n) hn hs1)
    rwa [abs_sub_comm] at this
  refine ⟨F, tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' ?_ ?_ hε)⟩
  · exact Filter.Eventually.of_forall fun _ => dist_nonneg
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hs₁)] with s hs hs1
    rw [Real.dist_eq]
    exact key s hs hs1

/-! ## 4. The gap seed: (D) and the infrared descent -/

/-- **The infrared descent of the defect (named input).** There is a physical size `C₁ > 0` with
`3C₁ ≤ s₀` such that for every bound `S` some number `m` of doublings carries every power-of-two torus whose
physical side lies in `[C₁, 3C₁]` and whose defect is at most `S` to the sharp seed, eventually in `β`.

DERIVED: `3` the window `[C₁, 3C₁]`, which contains `nP · a ∈ [C₁, 2C₁ + 2a]` once `a ≤ C₁/4`
(`DoublingClay2.nP_bounds`); `1/1000` the sharp seed of `DoublingSharp`; `2` the doubling and the least side. -/
def DefectDescent (N : ℕ) (s₀ : ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ 3 * C₁ ≤ s₀ ∧ ∀ S : ℝ, ∃ m : ℕ, ∀ᶠ β in atTop, ∀ n : ℕ, PeriodicState.IsPow2 n → 2 ≤ n →
    C₁ ≤ (n : ℝ) * AsymptoticScaling.aRun N β → (n : ℝ) * AsymptoticScaling.aRun N β ≤ 3 * C₁ →
      ZoomSelfScale.defectW N β n ≤ S → ZoomSelfScale.defectW N β (2 ^ m * n) ≤ 1 / 1000

/-- **The gap seed from (D) and the infrared descent.** -/
theorem runSeed_of_defect (hN : N ≠ 0) {s₀ : ℝ} (hD : DefectBounded N s₀) (hI : DefectDescent N s₀) :
    WDeltaRun.RunSeed N := by
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  obtain ⟨C₁, hC₁, h3C₁, hdesc⟩ := hI
  obtain ⟨S, hS⟩ := hD C₁ (3 * C₁) hC₁ h3C₁
  obtain ⟨m, hm⟩ := hdesc S
  refine ⟨2 ^ m * (3 * C₁), by positivity, ?_⟩
  filter_upwards [hS, hm, eventually_gt_atTop (0 : ℝ),
    WeakCouplingWindow.eventually_aRun_le hN1 (b := C₁ / 4) (by positivity)] with β hβS hβm hβ0 haLe
  set a := AsymptoticScaling.aRun N β with ha_def
  have ha : 0 < a := AsymptoticScaling.aRun_pos hN1 hβ0
  have hℓ : (0 : ℝ) < C₁ / 2 := by positivity
  obtain ⟨h2, hna⟩ := DoublingClay2.nP_bounds hℓ ha (by linarith)
  set n := DoublingClay2.nP N (C₁ / 2) β with hn_def
  have hn2 : 2 ≤ n := h2
  have hup : (n : ℝ) * a ≤ 3 * C₁ := by
    have : ((n : ℕ) : ℝ) * a ≤ 4 * (C₁ / 2) + 2 * a := hna
    linarith
  have hlow : C₁ ≤ (n : ℝ) * a := by
    have h1 : C₁ / a ≤ (⌈2 * (C₁ / 2) / a⌉₊ : ℝ) := by
      have : 2 * (C₁ / 2) / a = C₁ / a := by ring
      rw [← this]
      exact Nat.le_ceil _
    have h2' : ⌈2 * (C₁ / 2) / a⌉₊ ≤ n := Nat.le_pow_clog (by norm_num) _
    have h3 : C₁ / a ≤ (n : ℝ) := h1.trans (by exact_mod_cast h2')
    rwa [div_le_iff₀ ha] at h3
  have hpow : PeriodicState.IsPow2 n := DoublingClay2.nP_isPow2 (C₁ / 2) β
  have hseed := hβm n hpow hn2 hlow hup (hβS n hpow hlow hup)
  obtain ⟨b, hb⟩ := hpow
  refine ⟨2 ^ m * n, ⟨m + b, by rw [hb, pow_add]⟩, ?_, ?_, hseed⟩
  · have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    nlinarith
  · push_cast
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    calc (2 : ℝ) ^ m * (n : ℝ) * a = 2 ^ m * ((n : ℝ) * a) := by ring
      _ ≤ 2 ^ m * (3 * C₁) := mul_le_mul_of_nonneg_left hup h2m.le

/-! ## 5. E: the running from the point's scale to the reference -/

/-- **Point readings against the cube at their own scale (named input).** For every list of fields and
every margin `d < s₀`, the unit-strength reflected point readings of configurations `d` above the plane and
pairwise `d`-separated are at most `C · a_k^{8n}` times the `n`-th power of the cube-pair reading at the
same scale `d`. The two scales compared are equal, so no running enters.

DERIVED: `8` in `8 * n` the canonical dimension count of the point readings, `a⁸ = a⁴ · a⁴` per reflected
pair as in `ApertureNearAll.NearAll`. -/
def PointCubeLocalAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  ∀ (n : ℕ) (L : Fin n → LField (MassGap.SUN.SU N)) (d : ℝ), 0 < d → d < s₀ → ∃ C : ℝ,
    ∀ᶠ k in atTop, ∀ p : Fin n → ISite,
      ContinuumSep.sepPos 0 d (ptMono L (fun i => site (dySpacing N k) (p i))) →
      latSkRAlong hN βs (rho1Along hN βs) k
          (pairFam 0 (ptMono L (fun i => site (dySpacing N k) (p i)))
            (ptMono L (fun i => site (dySpacing N k) (p i))))
        ≤ C * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d d k ^ n

/-- `PointCubeLocal` at the couplings `dyBeta`: `PointCubeLocalAlong` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
def PointCubeLocal (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (s₀ : ℝ) : Prop :=
  PointCubeLocalAlong hN (dyBeta (one_le_of_ne_zero hN)) O s₀


/-- **E from (R) and the scale-local input.** -/
theorem pointRatio_of_running_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ}
    (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1) (hR : RunningBelowAlong hN βs O s₀ K δ) (hL : PointCubeLocalAlong hN βs O s₀) :
    PointReadingRatio.PointRatioAlong hN βs O s₀ s₀ := by
  intro n L d hd
  set d' := min d (s₀ / 2) with hd'_def
  have hd' : 0 < d' := lt_min hd (by positivity)
  have hd's : d' < s₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hd'1 : d' < 1 := hd's.trans hs₀1
  obtain ⟨C, hC⟩ := hL n L d' hd' hd's
  set M := Real.exp (runErr K δ d' s₀) * (Real.log s₀ ^ 2 / Real.log d' ^ 2)
  refine ⟨max C 0 * M ^ n, ?_⟩
  filter_upwards [hC, hR d' s₀ hd' hd's le_rfl] with k hk hrb p hp
  have hp' := ContinuumSep.sepPos_mono hp (min_le_left d (s₀ / 2))
  have hu := hk p hp'
  have hx := hrb.1
  have hx' := hrb.2.1
  have hratio := (ratio_bounds hd' hd'1 hs₀ hs₀1 hrb).1
  have hxle : refReadingAlong hN βs O d' d' k ≤ M * refReadingAlong hN βs O s₀ s₀ k := by
    rwa [div_le_iff₀ hx'] at hratio
  have ha : 0 ≤ dySpacing N k ^ (8 * n) :=
    pow_nonneg (dySpacing_pos (one_le_of_ne_zero hN) k).le _
  have hpow : refReadingAlong hN βs O d' d' k ^ n ≤ (M * refReadingAlong hN βs O s₀ s₀ k) ^ n :=
    pow_le_pow_left₀ hx.le hxle n
  show _ ≤ max C 0 * M ^ n * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O s₀ s₀ k ^ n
  calc _ ≤ C * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d' d' k ^ n := hu
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d' d' k ^ n := by
        have : 0 ≤ dySpacing N k ^ (8 * n) * refReadingAlong hN βs O d' d' k ^ n :=
          mul_nonneg ha (pow_nonneg hx.le n)
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
    _ ≤ max C 0 * dySpacing N k ^ (8 * n) * (M * refReadingAlong hN βs O s₀ s₀ k) ^ n :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) ha)
    _ = max C 0 * M ^ n * dySpacing N k ^ (8 * n) * refReadingAlong hN βs O s₀ s₀ k ^ n := by
        rw [mul_pow]
        ring

/-- `pointRatio_of_running` at the couplings `dyBeta`: `pointRatio_of_running_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem pointRatio_of_running (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ}
    (hs₀ : 0 < s₀) (hs₀1 : s₀ < 1) (hR : RunningBelow hN O s₀ K δ) (hL : PointCubeLocal hN O s₀) :
    PointReadingRatio.PointRatio hN O s₀ s₀ :=
  pointRatio_of_running_along hN (dyBeta (one_le_of_ne_zero hN)) O hs₀ hs₀1 hR hL


/-! ## 6. The three-point bound: the cubic ratio -/

/-- **The cubic ratio of a split three-point reading (named input).** `SplitRatio` without its positivity
conjunct: one split of three insertions of `O` and one `c > 0` with `c · refReading³ ≤ κ²` eventually.

DERIVED: `3` the insertions of a three-point reading, one reference reading per insertion; `2` the
square of the reading. -/
def SplitCubicAlong (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  ∃ (P Q : ContinuumSep.SepMono N 0), P.1.1 + Q.1.1 = 3 ∧
    (∀ x, (pairFam 0 P.1 Q.1 x).1 = O) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      c * refReadingAlong hN βs O t ℓ k ^ 3 ≤ (latSkRAlong hN βs (rho1Along hN βs) k (pairFam 0 P.1 Q.1)) ^ 2

/-- `SplitCubic` at the couplings `dyBeta`: `SplitCubicAlong` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
def SplitCubic (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) (t ℓ : ℝ) : Prop :=
  SplitCubicAlong hN (dyBeta (one_le_of_ne_zero hN)) O t ℓ


/-- **`SplitThreePoint` from (R) and the cubic ratio.** -/
theorem splitThreePoint_of_running_along (hN : N ≠ 0) (βs : ℕ → ℝ) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ}
    (hs₀ : 0 < s₀) (hR : RunningBelowAlong hN βs O s₀ K δ) (h3 : SplitCubicAlong hN βs O s₀ s₀) :
    ClaySplitThreePoint.SplitThreePointAlong hN βs O s₀ s₀ := by
  obtain ⟨P, Q, hcard, hO, c, hc, hev⟩ := h3
  exact (splitThreePoint_iff_splitRatio_along hN βs O s₀ s₀).mpr
    ⟨P, Q, hcard, hO, c, hc, (hev.and (refPos_of_running_along hN βs O hs₀ hR)).mono fun _ h => ⟨h.2, h.1⟩⟩

/-- `splitThreePoint_of_running` at the couplings `dyBeta`: `splitThreePoint_of_running_along` at `βs = dyBeta`.

DERIVED: no numeral beyond those of the statement. -/
theorem splitThreePoint_of_running (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ K δ : ℝ}
    (hs₀ : 0 < s₀) (hR : RunningBelow hN O s₀ K δ) (h3 : SplitCubic hN O s₀ s₀) :
    ClaySplitThreePoint.SplitThreePoint hN O s₀ s₀ :=
  splitThreePoint_of_running_along hN (dyBeta (one_le_of_ne_zero hN)) O hs₀ hR h3


/-! ## 7. The capstone -/

/-! ## 8. Controls -/

/-- **A ratio that grows without bound in the step fails (R)**: the generalised free field with drifting
Källén–Lehmann weight `μ^{γ_k}`, whose reading at `s` exceeds the one at `s'` by a factor of order
`(s'/s)^{2γ_k}`. -/
theorem not_running_of_ratio_unbounded (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ K δ s s' : ℝ}
    (hs₀1 : s₀ < 1) (hs : 0 < s) (hss' : s < s') (hs's₀ : s' ≤ s₀)
    (hun : ∀ M : ℝ, ∃ᶠ k in atTop, M * refReading hN O s' s' k < refReading hN O s s k) :
    ¬ RunningBelow hN O s₀ K δ := by
  intro hR
  have hs' : 0 < s' := hs.trans hss'
  have hs'1 : s' < 1 := lt_of_le_of_lt hs's₀ hs₀1
  set M := Real.exp (runErr K δ s s') * (Real.log s' ^ 2 / Real.log s ^ 2)
  obtain ⟨k, hk, hrb⟩ := ((hun M).and_eventually (hR s s' hs hss' hs's₀)).exists
  replace hrb : RunBound K δ s s' (refReading hN O s s k) (refReading hN O s' s' k) := hrb
  have hr := (ratio_bounds hs (hss'.trans hs'1) hs' hs'1 hrb).1
  rw [div_le_iff₀ hrb.2.1] at hr
  linarith

/-- **Vanishing readings fail (R)**: the `β = 0` family, whose connected readings of disjoint supports are `0`. -/
theorem not_running_of_vanishing (hN : N ≠ 0) (O : LField (MassGap.SUN.SU N)) {s₀ K δ s : ℝ}
    (hs : 0 < s) (hss₀ : s < s₀) (hv : ∃ᶠ k in atTop, refReading hN O s s k ≤ 0) :
    ¬ RunningBelow hN O s₀ K δ := by
  intro hR
  obtain ⟨k, hk, hrb⟩ := (hv.and_eventually (hR s s₀ hs hss₀ le_rfl)).exists
  replace hrb : RunBound K δ s s₀ (refReading hN O s s k) (refReading hN O s₀ s₀ k) := hrb
  linarith [hrb.1]

end MassGap.ShortDistanceRunning

#print axioms MassGap.ShortDistanceRunning.runningBelow_of_octave
#print axioms MassGap.ShortDistanceRunning.ratio_bounds
#print axioms MassGap.ShortDistanceRunning.exists_tendsto_of_modulus
#print axioms MassGap.ShortDistanceRunning.runSeed_of_defect
#print axioms MassGap.ShortDistanceRunning.pointRatio_of_running
#print axioms MassGap.ShortDistanceRunning.splitThreePoint_of_running
#print axioms MassGap.ShortDistanceRunning.not_running_of_ratio_unbounded
#print axioms MassGap.ShortDistanceRunning.not_running_of_vanishing
