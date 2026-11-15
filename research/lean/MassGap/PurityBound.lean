import Mathlib
import MassGap.DefectBound
import MassGap.DoublingWilsonG

/-!
# MassGap.PurityBound — the sharp conversion from thermal purity to the excited weight

Sections 2–4 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford and
S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`),
formalized on the four trace facts `DoublingPower.PowerFacts`.

With `a m = Tr Kᵐ`, top eigenvalue `λ` and relative excited weight `s` (`a m = λᵐ (1 + s)`), the
thermal purity is `P = a (2m) / a m ² = exp (−defect a m)`, and the top occupation is
`q = 1 / (1 + s)`. `PowerFacts` gives `P ≤ q` and `P ≤ q² + (1 − q)²`; these two facts carry the
sharp bound.

* `excited_le_d`, `excited_le_sharp`: `P > 1/2 ⇒ s ≤ d P` with
  `d p = (1 − √(2p − 1)) / (1 + √(2p − 1))` (paper, Lemma 2.1 and Theorem 2.2, (2.2)).
  `purity_two_level`: the two-level spectrum `(1, d p)` has purity `p`, so the bound is attained.
  `d_antitoneOn`, `excited_le_of_purity_ge`: a certified bound `P ≥ p > 1/2` gives `s ≤ d p`.
* `twoLevel u = −log (e^{−2u} + (1 − e^{−u})²)`, the defect of the two-level spectrum with
  `log (1 + s) = u`; on `[0, log 2]` it is the inverse of the paper's `F`.
  `twoLevel_le_defect`: `twoLevel (log (1 + s)) ≤ defect a m`.
* `twoLevel_strictMonoOn`, `twoLevel_concaveOn`, `twoLevel_chord` on `[0, log 2]`
  (paper, Lemma 2.4: `F` increasing and convex, with the chord bound).
* `purity_mem_of_intervals`, `defect_le_of_approx`: certified intervals (paper, Proposition 3.3).
* `pressure_le`: paper, Theorem 4.1, with `u_m = F (ε_m)`. `inv161_le_twoLevel`: `1/161 ≤ twoLevel (1/320)`.
  `window_datum`: paper, Corollary 4.2.
* `wilson_facts`, `wilson_excited_le_sharp`, `wilson_window_datum`: the same for the `L²` operator
  `K = wilsonK` of the transverse transfer kernel of the Wilson model of every gauge group, on every
  transverse torus, at every even time `2j`, with `Tr K^{2j} = ‖K‖^{2j} (1 + s)`. There `defect` is
  the paper's pressure defect `ψ = 2 log Z(T) − log Z(2T)` at fixed spatial torus.

DERIVED (module-wide): `1/2` the purity threshold of a simple top level; `2` the doubling;
`161` and `320` the coefficients of the paper's Corollary 4.2, with `2 · (1/320) · 2³ = 1/20` the
ascent parameter of its first paper.
-/

namespace MassGap.PurityBound

open Real Set MassGap.DoublingPower

/-- `d p = (1 − √(2p − 1)) / (1 + √(2p − 1))`. -/
noncomputable def d (p : ℝ) : ℝ := (1 - Real.sqrt (2 * p - 1)) / (1 + Real.sqrt (2 * p - 1))

/-- **Lemma 2.1 / Theorem 2.2 on two scalar facts.** A purity `P > 1/2` with `P ≤ q` and
`P ≤ q² + (1 − q)²`, `q = 1/(1 + s)`, gives `s ≤ d P`. DERIVED: `1/2`, `2`. -/
theorem excited_le_d {s P : ℝ} (hs : 0 ≤ s) (htop : P ≤ 1 / (1 + s))
    (hpur : P ≤ (1 + s ^ 2) / (1 + s) ^ 2) (hP : 1 / 2 < P) : s ≤ d P := by
  have h1s : 0 < 1 + s := by linarith
  have htop' : P * (1 + s) ≤ 1 := by rwa [le_div_iff₀ h1s] at htop
  have hpur' : P * (1 + s) ^ 2 ≤ 1 + s ^ 2 := by rwa [le_div_iff₀ (by positivity)] at hpur
  have hs1 : s < 1 := by nlinarith [mul_pos (by linarith : (0:ℝ) < P - 1 / 2) h1s]
  unfold d
  set r := Real.sqrt (2 * P - 1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * P - 1 := Real.sq_sqrt (by linarith)
  have key : (r * (1 + s)) ^ 2 ≤ (1 - s) ^ 2 := by
    rw [mul_pow, hr2]; nlinarith
  have hle : r * (1 + s) ≤ 1 - s := by
    by_contra hc
    have := mul_self_lt_mul_self (by linarith : (0:ℝ) ≤ 1 - s) (not_le.mp hc)
    nlinarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **The bound is attained**: the two-level spectrum `(1, d p)` has purity `p`. -/
theorem purity_two_level {p : ℝ} (hp : 1 / 2 ≤ p) : (1 + d p ^ 2) / (1 + d p) ^ 2 = p := by
  unfold d
  set r := Real.sqrt (2 * p - 1) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * p - 1 := Real.sq_sqrt (by linarith)
  have h1r : (1:ℝ) + r ≠ 0 := by linarith
  have e1 : 1 + (1 - r) / (1 + r) = 2 / (1 + r) := by field_simp; ring
  have e2 : 1 + ((1 - r) / (1 + r)) ^ 2 = (2 + 2 * r ^ 2) / (1 + r) ^ 2 := by field_simp; ring
  rw [e1, e2, div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 h1r), hr2]
  ring

/-- `d` is antitone on `[1/2, ∞)`. -/
theorem d_antitoneOn : AntitoneOn d (Set.Ici (1 / 2)) := by
  intro p hp p' hp' hpp'
  have hp0 : (0:ℝ) ≤ 2 * p - 1 := by have := Set.mem_Ici.mp hp; linarith
  have hr : Real.sqrt (2 * p - 1) ≤ Real.sqrt (2 * p' - 1) := Real.sqrt_le_sqrt (by linarith)
  have h0 := Real.sqrt_nonneg (2 * p - 1)
  unfold d
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

section Facts

variable {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}

/-- The thermal purity: `exp (−defect) = a (2m) / a m ²`. -/
theorem exp_neg_defect (h : PowerFacts a lam s m) : exp (-defect a m) = a (2 * m) / a m ^ 2 := by
  have hA := h.a_pos
  have hB := h.a2_pos
  unfold defect
  rw [neg_sub, exp_sub, exp_log hB,
    show (2:ℝ) * log (a m) = log (a m) + log (a m) by ring, exp_add, exp_log hA]
  ring

/-- `P ≤ q`: the purity is at most the top occupation. -/
theorem purity_le_top (h : PowerFacts a lam s m) : a (2 * m) / a m ^ 2 ≤ 1 / (1 + s) := by
  have hA := h.a_pos
  have h1s : 0 < 1 + s := by linarith [h.s_nonneg]
  rw [div_le_div_iff₀ (by positivity) h1s, one_mul]
  calc a (2 * m) * (1 + s) ≤ lam ^ m * a m * (1 + s) :=
        mul_le_mul_of_nonneg_right h.dbl_le h1s.le
    _ = a m ^ 2 := by rw [h.base]; ring

/-- `P ≤ q² + (1 − q)²`: the excited levels carry at most the square of their weight. -/
theorem purity_le_two_level (h : PowerFacts a lam s m) :
    a (2 * m) / a m ^ 2 ≤ (1 + s ^ 2) / (1 + s) ^ 2 := by
  have hl := h.lam_pow_pos (2 * m)
  have h1s : 0 < 1 + s := by linarith [h.s_nonneg]
  have hsq : a m ^ 2 = lam ^ (2 * m) * (1 + s) ^ 2 := by rw [h.base]; ring
  rw [hsq, div_le_div_iff₀ (by positivity) (by positivity)]
  calc a (2 * m) * (1 + s) ^ 2 ≤ lam ^ (2 * m) * (1 + s ^ 2) * (1 + s) ^ 2 :=
        mul_le_mul_of_nonneg_right h.dbl_le_sq (by positivity)
    _ = (1 + s ^ 2) * (lam ^ (2 * m) * (1 + s) ^ 2) := by ring

theorem half_lt_purity (h : PowerFacts a lam s m) (hd : defect a m < log 2) :
    1 / 2 < a (2 * m) / a m ^ 2 := by
  rw [← exp_neg_defect h]
  have e : exp (-log 2) = 1 / 2 := by rw [exp_neg, exp_log two_pos]; norm_num
  rw [← e]
  exact exp_lt_exp.mpr (by linarith)

/-- **Theorem 2.2, (2.2).** A defect below `log 2` gives `s ≤ d (exp (−defect))`. -/
theorem excited_le_sharp (h : PowerFacts a lam s m) (hd : defect a m < log 2) :
    s ≤ d (exp (-defect a m)) := by
  rw [exp_neg_defect h]
  exact excited_le_d h.s_nonneg (purity_le_top h) (purity_le_two_level h) (half_lt_purity h hd)

/-- **Theorem 2.2 from a certified purity bound**: `exp (−defect) ≥ p > 1/2` gives `s ≤ d p`. With
`purity_mem_of_intervals` this takes interval data to the excited weight. -/
theorem excited_le_of_purity_ge (h : PowerFacts a lam s m) {p : ℝ} (hp : 1 / 2 < p)
    (hP : p ≤ exp (-defect a m)) : s ≤ d p := by
  have hd : defect a m < log 2 := by
    have : exp (-log 2) < exp (-defect a m) := by
      rw [exp_neg, exp_log two_pos]; linarith
    linarith [exp_lt_exp.mp this]
  exact (excited_le_sharp h hd).trans
    (d_antitoneOn (Set.mem_Ici.mpr hp.le) (Set.mem_Ici.mpr (by linarith)) hP)

end Facts

/-- `pur u = e^{−2u} + (1 − e^{−u})²`, the purity of the two-level spectrum with top occupation
`e^{−u}`. -/
noncomputable def pur (u : ℝ) : ℝ := exp (-u) ^ 2 + (1 - exp (-u)) ^ 2

/-- `twoLevel u = −log (pur u)`. -/
noncomputable def twoLevel (u : ℝ) : ℝ := -log (pur u)

theorem pur_pos (u : ℝ) : 0 < pur u := by
  unfold pur; nlinarith [sq_nonneg (2 * exp (-u) - 1)]

theorem pur_log {s : ℝ} (hs : 0 ≤ s) : pur (log (1 + s)) = (1 + s ^ 2) / (1 + s) ^ 2 := by
  have h1s : (1:ℝ) + s ≠ 0 := by linarith
  unfold pur
  rw [exp_neg, exp_log (by linarith)]
  field_simp
  ring

theorem twoLevel_le_defect {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ} (h : PowerFacts a lam s m) :
    twoLevel (log (1 + s)) ≤ defect a m := by
  unfold twoLevel
  rw [pur_log h.s_nonneg]
  have hP := purity_le_two_level h
  rw [← exp_neg_defect h] at hP
  have := log_le_log (exp_pos _) hP
  rw [log_exp] at this
  linarith

theorem twoLevel_zero : twoLevel 0 = 0 := by
  unfold twoLevel pur; simp

theorem twoLevel_log_two : twoLevel (log 2) = log 2 := by
  unfold twoLevel pur
  rw [exp_neg, exp_log two_pos]
  have e : (2:ℝ)⁻¹ ^ 2 + (1 - 2⁻¹) ^ 2 = 2⁻¹ := by norm_num
  rw [e, Real.log_inv, neg_neg]

theorem exp_neg_mem {u : ℝ} (hu : u ∈ Icc 0 (log 2)) : exp (-u) ∈ Icc (1 / 2 : ℝ) 1 := by
  constructor
  · have : exp (-log 2) ≤ exp (-u) := exp_le_exp.mpr (by linarith [hu.2])
    rwa [exp_neg, exp_log two_pos, ← one_div] at this
  · exact exp_le_one_iff.mpr (by linarith [hu.1])

theorem twoLevel_strictMonoOn : StrictMonoOn twoLevel (Icc 0 (log 2)) := by
  intro u hu v hv huv
  have hwu := exp_neg_mem hu
  have hwv := exp_neg_mem hv
  have hlt : exp (-v) < exp (-u) := exp_lt_exp.mpr (by linarith)
  have hp : pur v < pur u := by
    unfold pur
    nlinarith [mul_pos (sub_pos.mpr hlt)
      (by linarith [hwu.1, hwv.1] : (0:ℝ) < exp (-u) + exp (-v) - 1)]
  unfold twoLevel
  have := log_lt_log (pur_pos v) hp
  linarith

theorem hasDerivAt_twoLevel (u : ℝ) :
    HasDerivAt twoLevel (2 * exp (-u) * (2 * exp (-u) - 1) / pur u) u := by
  have he : HasDerivAt (fun x => exp (-x)) (exp (-u) * -1) u := (hasDerivAt_id' u).neg.exp
  have hp : HasDerivAt pur (2 * exp (-u) * (1 - 2 * exp (-u))) u := by
    have h := (he.pow 2).add (((hasDerivAt_const u (1:ℝ)).sub he).pow 2)
    have hf : pur = fun x => exp (-x) ^ 2 + (1 - exp (-x)) ^ 2 := rfl
    rw [hf]
    exact h.congr_deriv (by norm_num <;> ring)
  have h := (hp.log (pur_pos u).ne').neg
  have hf : twoLevel = fun y => -log (pur y) := rfl
  rw [hf]
  exact h.congr_deriv (by ring)

theorem deriv_twoLevel (u : ℝ) :
    deriv twoLevel u = 2 * exp (-u) * (2 * exp (-u) - 1) / pur u :=
  (hasDerivAt_twoLevel u).deriv

/-- The slope `2w(2w − 1)/(w² + (1 − w)²)` is monotone in `w` on `[1/2, 1]`. -/
theorem slope_mono {x y : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 1) (hy : y ∈ Icc (1 / 2 : ℝ) 1)
    (hxy : y ≤ x) :
    2 * y * (2 * y - 1) / (y ^ 2 + (1 - y) ^ 2) ≤ 2 * x * (2 * x - 1) / (x ^ 2 + (1 - x) ^ 2) := by
  have hDx : 0 < x ^ 2 + (1 - x) ^ 2 := by nlinarith [sq_nonneg (2 * x - 1)]
  have hDy : 0 < y ^ 2 + (1 - y) ^ 2 := by nlinarith [sq_nonneg (2 * y - 1)]
  rw [div_le_div_iff₀ hDy hDx]
  have hc : 0 ≤ 4 * x * (1 - y) + 4 * y - 2 := by
    nlinarith [mul_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) (by linarith [hy.2] : (0:ℝ) ≤ 1 - y),
      hy.1]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - y) hc]

/-- **Lemma 2.4 (convexity of `F`), as concavity of its inverse.** -/
theorem twoLevel_concaveOn : ConcaveOn ℝ (Icc 0 (log 2)) twoLevel := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
  · exact fun u _ => (hasDerivAt_twoLevel u).continuousAt.continuousWithinAt
  · exact fun u _ => (hasDerivAt_twoLevel u).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro u hu v hv huv
    rw [deriv_twoLevel, deriv_twoLevel]
    unfold pur
    exact slope_mono (exp_neg_mem (Ioo_subset_Icc_self hu)) (exp_neg_mem (Ioo_subset_Icc_self hv))
      (exp_le_exp.mpr (by linarith))

/-- **The chord bound** (paper, (2.6)): `θ · twoLevel u ≤ twoLevel (θ u)` for `θ ∈ [0, 1]`. -/
theorem twoLevel_chord {θ u : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc 0 (log 2)) :
    θ * twoLevel u ≤ twoLevel (θ * u) := by
  have h0 : (0:ℝ) ∈ Icc 0 (log 2) := ⟨le_rfl, (log_pos one_lt_two).le⟩
  have := twoLevel_concaveOn.2 h0 hu (by linarith [hθ.2] : 0 ≤ 1 - θ) hθ.1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, twoLevel_zero] at this
  exact this

/-- **Proposition 3.3 (purity).** Certified intervals for the two partition functions bound the
purity. -/
theorem purity_mem_of_intervals {Z₁ Z₂ l₁ u₁ l₂ u₂ : ℝ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (h₁ : Z₁ ∈ Icc l₁ u₁) (h₂ : Z₂ ∈ Icc l₂ u₂) :
    l₂ / u₁ ^ 2 ≤ Z₂ / Z₁ ^ 2 ∧ Z₂ / Z₁ ^ 2 ≤ u₂ / l₁ ^ 2 := by
  have hZ₁ : 0 < Z₁ := lt_of_lt_of_le hl₁ h₁.1
  have hu₁ : 0 < u₁ := lt_of_lt_of_le hZ₁ h₁.2
  have hZ₂ : 0 < Z₂ := lt_of_lt_of_le hl₂ h₂.1
  constructor
  · rw [div_le_div_iff₀ (pow_pos hu₁ 2) (pow_pos hZ₁ 2)]
    exact mul_le_mul h₂.1 (pow_le_pow_left₀ hZ₁.le h₁.2 2) (sq_nonneg _) hZ₂.le
  · rw [div_le_div_iff₀ (pow_pos hZ₁ 2) (pow_pos hl₁ 2)]
    exact mul_le_mul h₂.2 (pow_le_pow_left₀ hl₁.le h₁.1 2) (sq_nonneg _)
      (hZ₂.le.trans h₂.2)

/-- **Proposition 3.3 (defect), (3.3).** Approximate logarithms bound the defect. -/
theorem defect_le_of_approx {a : ℕ → ℝ} {m : ℕ} {z₁ z₂ η₁ η₂ : ℝ}
    (h₁ : |log (a m) - z₁| ≤ η₁) (h₂ : |log (a (2 * m)) - z₂| ≤ η₂) :
    defect a m ≤ 2 * z₁ - z₂ + 2 * η₁ + η₂ := by
  unfold defect
  obtain ⟨-, h₁'⟩ := abs_le.mp h₁
  obtain ⟨h₂', -⟩ := abs_le.mp h₂
  linarith

section Pressure

variable {a : ℕ → ℝ} {lam s : ℝ} {m : ℕ}

/-- **Theorem 4.1.** With `u_m ∈ [0, log 2]` (the paper's `F (ε_m)`, so `ε_m = twoLevel u_m`) and
`θ ∈ [0, 1]` (the volume ratio `V(s)/(48T₀)³`), `defect ≤ θ · twoLevel u_m` gives
`log (1 + s) ≤ θ u_m`. -/
theorem pressure_le (h : PowerFacts a lam s m) {um θ : ℝ} (hum : um ∈ Icc 0 (log 2))
    (hθ : θ ∈ Icc (0:ℝ) 1) (hd : defect a m ≤ θ * twoLevel um) : log (1 + s) ≤ θ * um := by
  have hs := h.s_nonneg
  have hl2 : (0:ℝ) ≤ log 2 := (log_pos one_lt_two).le
  have hmono := twoLevel_strictMonoOn
  have h0 : (0:ℝ) ∈ Icc 0 (log 2) := ⟨le_rfl, hl2⟩
  have hl2m : log 2 ∈ Icc 0 (log 2) := ⟨hl2, le_rfl⟩
  have hG0 : 0 ≤ twoLevel um := by
    have := hmono.monotoneOn h0 hum hum.1; rwa [twoLevel_zero] at this
  have hG2 : twoLevel um ≤ log 2 := by
    have := hmono.monotoneOn hum hl2m hum.2; rwa [twoLevel_log_two] at this
  have hθG : θ * twoLevel um ≤ log 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hθ.2 hG0]
  have hmem : log (1 + s) ∈ Icc 0 (log 2) :=
    ⟨log_nonneg (by linarith), by linarith [DefectBound.log_one_add_le_defect h]⟩
  have hθu : θ * um ∈ Icc 0 (log 2) :=
    ⟨mul_nonneg hθ.1 hum.1, by nlinarith [mul_le_mul_of_nonneg_right hθ.2 hum.1, hum.2]⟩
  have hG : twoLevel (log (1 + s)) ≤ twoLevel (θ * um) :=
    (twoLevel_le_defect h).trans (hd.trans (twoLevel_chord hθ hum))
  exact (hmono.le_iff_le hmem hθu).mp hG

/-- **The exact margin of (4.5).** `1/161 ≤ twoLevel (1/320)`, i.e. `1/161 ≤ ε*`. DERIVED: `161`,
`320`. -/
theorem inv161_le_twoLevel : 1 / 161 ≤ twoLevel (1 / 320) := by
  have hx : (0:ℝ) ≤ 1 / 320 := by norm_num
  have hl2 : (1:ℝ) / 320 ≤ log 2 := by have := Real.log_two_gt_d9; linarith
  have hmem := exp_neg_mem ⟨hx, hl2⟩
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hwU : exp (-(1 / 320 : ℝ)) ≤ 1 / (1 + 1 / 320 + (1 / 320) ^ 2 / 2) := by
    rw [exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hq
  have hwU2 : (1:ℝ) / 2 ≤ 1 / (1 + 1 / 320 + (1 / 320) ^ 2 / 2) := by norm_num
  have hnum : (1 / (1 + 1 / 320 + (1 / 320) ^ 2 / 2) : ℝ) ^ 2
      + (1 - 1 / (1 + 1 / 320 + (1 / 320) ^ 2 / 2)) ^ 2 ≤ 160 / 161 := by norm_num
  have hpw : pur (1 / 320) ≤ 160 / 161 := by
    unfold pur
    nlinarith [mul_nonneg (sub_nonneg.mpr hwU)
      (by linarith [hmem.1] : (0:ℝ) ≤ 1 / (1 + 1 / 320 + (1 / 320) ^ 2 / 2) + exp (-(1 / 320)) - 1)]
  have he : (160:ℝ) / 161 ≤ exp (-(1 / 161)) := by
    have := add_one_le_exp (-(1 / 161 : ℝ)); linarith
  have hlog := log_le_log (pur_pos _) (hpw.trans he)
  rw [log_exp] at hlog
  unfold twoLevel
  linarith

/-- **Corollary 4.2.** `defect ≤ V / (161 W)` with `0 ≤ V ≤ W` gives `log (1 + s) ≤ V / (320 W)`.
At `W = (48T₀)³` this is the first paper's datum `log Z ≤ γ V` with `2γ (96T₀)³ = 1/20`. -/
theorem window_datum (h : PowerFacts a lam s m) {V W : ℝ} (hV : 0 ≤ V) (hVW : V ≤ W) (hW : 0 < W)
    (hd : defect a m ≤ V / (161 * W)) : log (1 + s) ≤ V / (320 * W) := by
  have hθ : V / W ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hV hW.le, (div_le_one hW).mpr hVW⟩
  have hum : (1:ℝ) / 320 ∈ Icc 0 (log 2) :=
    ⟨by norm_num, by have := Real.log_two_gt_d9; linarith⟩
  have hd' : defect a m ≤ V / W * twoLevel (1 / 320) :=
    calc defect a m ≤ V / (161 * W) := hd
      _ = V / W * (1 / 161) := by ring
      _ ≤ V / W * twoLevel (1 / 320) := mul_le_mul_of_nonneg_left inv161_le_twoLevel hθ.1
  calc log (1 + s) ≤ V / W * (1 / 320) := pressure_le h hum hθ hd'
    _ = V / (320 * W) := by ring

end Pressure

section Wilson

open MeasureTheory MassGap.DoublingWilsonG MassGap.GaugeGroup MassGap.RectTransferG
  MassGap.SlabKernelOperator MassGap.KernelPower

variable (𝒢 : Type) [Group 𝒢] [TopologicalSpace 𝒢] [MeasurableSpace 𝒢] [GaugeGroup 𝒢]

/-- The `L²` operator `K` of the transverse transfer kernel of the Wilson model of `𝒢`. -/
noncomputable def wilsonK {β : ℝ} (hβ : 0 ≤ β) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ) :=
  kernelCLM (kTG 𝒢 μ T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (hSG 𝒢 μ T) (hSG 𝒢 μ T)

variable {𝒢}

/-- The trace facts at the operator norm: `Tr K^{2j} = ‖K‖^{2j} (1 + s)`, with `‖K‖` the top
eigenvalue in absolute value. -/
theorem wilson_facts {β : ℝ} (hβ : 0 ≤ β) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : ∃ s : ℝ, PowerFacts (FG 𝒢 β μ T) ‖wilsonK 𝒢 hβ μ T‖ s (2 * j) := by
  obtain ⟨φ, hφm, ⟨B, hφb⟩, hφ1, c, hc, heig⟩ :=
    KernelEigen.exists_eigen (μ := hSG 𝒢 μ T) (continuous_kTG β) zero_le_one (abs_kTG_le hβ)
      (kTG_symm β) (K_posG hβ μ T)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith [K_posG (G := 𝒢) hβ μ T]
  have hpf := powerFacts (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (kTG_symm β) hφm hφb hφ1 heig hc hc0 j hj
  rw [hc] at hpf
  exact ⟨_, hpf⟩

/-- **Theorem 2.2 for the Wilson transfer operator.** For every gauge group, every transverse torus
`T` and every even time `2j ≥ 2`, write `Tr K^{2j} = ‖K‖^{2j} (1 + s)`. A pressure defect
`ψ = 2 log Tr K^{2j} − log Tr K^{4j}` below `log 2` gives `s ≤ d (exp (−ψ))`. -/
theorem wilson_excited_le_sharp {β : ℝ} (hβ : 0 ≤ β) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ s : ℝ, PowerFacts (FG 𝒢 β μ T) ‖wilsonK 𝒢 hβ μ T‖ s (2 * j) ∧
      (defect (FG 𝒢 β μ T) (2 * j) < log 2 → s ≤ d (exp (-defect (FG 𝒢 β μ T) (2 * j)))) := by
  obtain ⟨s, h⟩ := wilson_facts (𝒢 := 𝒢) hβ μ T j hj
  exact ⟨s, h, excited_le_sharp h⟩

/-- **Corollary 4.2 for the Wilson transfer operator.** On every transverse torus, at every even time
`2j ≥ 2` and every gauge group, with `Tr K^{2j} = ‖K‖^{2j} (1 + s)`: `ψ ≤ V / (161 W)` with
`0 ≤ V ≤ W` gives `log (1 + s) ≤ V / (320 W)`. -/
theorem wilson_window_datum {β : ℝ} (hβ : 0 ≤ β) (μ : Fin 4) (T : {j : Fin 4 // j ≠ μ} → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ s : ℝ, PowerFacts (FG 𝒢 β μ T) ‖wilsonK 𝒢 hβ μ T‖ s (2 * j) ∧
      ∀ V W : ℝ, 0 ≤ V → V ≤ W → 0 < W → defect (FG 𝒢 β μ T) (2 * j) ≤ V / (161 * W) →
        log (1 + s) ≤ V / (320 * W) := by
  obtain ⟨s, h⟩ := wilson_facts (𝒢 := 𝒢) hβ μ T j hj
  exact ⟨s, h, fun V W hV hVW hW hd => window_datum h hV hVW hW hd⟩

end Wilson

end MassGap.PurityBound

#print axioms MassGap.PurityBound.excited_le_d
#print axioms MassGap.PurityBound.d_antitoneOn
#print axioms MassGap.PurityBound.excited_le_of_purity_ge
#print axioms MassGap.PurityBound.wilson_facts
#print axioms MassGap.PurityBound.purity_two_level
#print axioms MassGap.PurityBound.exp_neg_defect
#print axioms MassGap.PurityBound.purity_le_top
#print axioms MassGap.PurityBound.purity_le_two_level
#print axioms MassGap.PurityBound.half_lt_purity
#print axioms MassGap.PurityBound.excited_le_sharp
#print axioms MassGap.PurityBound.pur_pos
#print axioms MassGap.PurityBound.pur_log
#print axioms MassGap.PurityBound.twoLevel_le_defect
#print axioms MassGap.PurityBound.twoLevel_zero
#print axioms MassGap.PurityBound.twoLevel_log_two
#print axioms MassGap.PurityBound.exp_neg_mem
#print axioms MassGap.PurityBound.twoLevel_strictMonoOn
#print axioms MassGap.PurityBound.hasDerivAt_twoLevel
#print axioms MassGap.PurityBound.deriv_twoLevel
#print axioms MassGap.PurityBound.slope_mono
#print axioms MassGap.PurityBound.twoLevel_concaveOn
#print axioms MassGap.PurityBound.twoLevel_chord
#print axioms MassGap.PurityBound.purity_mem_of_intervals
#print axioms MassGap.PurityBound.defect_le_of_approx
#print axioms MassGap.PurityBound.pressure_le
#print axioms MassGap.PurityBound.inv161_le_twoLevel
#print axioms MassGap.PurityBound.window_datum
#print axioms MassGap.PurityBound.wilson_excited_le_sharp
#print axioms MassGap.PurityBound.wilson_window_datum
