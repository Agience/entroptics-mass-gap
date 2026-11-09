import Mathlib
import MassGap.SectorDefect

/-!
# MassGap.TwistedTransferDoubling — doubling a side transverse to a twist is the twisted transfer's own defect

Let `(X, μ)` be a probability space and `a`, `b` two bounded kernels with positive traces. `a` is the
transfer over half the extent of a direction `μ` of the untwisted torus, `b` the same for the torus
twisted in a plane `(i, ν)` not containing `μ`: the twist then sits on spatial plaquettes of every
`μ`-slice, so it is a different kernel on the same slice, not an insertion. `hs a = Z`, `hs b = Z_tw`,
and `hs (a ∗ a)`, `hs (b ∗ b)` are the same partition functions with `L_μ` doubled. Write
`z = hs b / hs a` and `z₂ = hs (b ∗ b) / hs (a ∗ a)` for the twisted ratio before and after.

**The identity** (`log_ratio_conv`, `ratio_conv_eq`):

    z₂ = z² · exp(dd a − dd b).

So the transverse doubling squares the twisted ratio up to the difference of the two doubling defects.

**Transverse non-spreading is a defect comparison at the scale of the twist deficit.** With
`ε = 1 − z`:
* `one_sub_ratio_conv_le`: `dd b − dd a ≤ c ε` gives `1 − z₂ ≤ (2 + c) ε`;
* `dd_sub_le_of_one_sub_ratio_conv`: `1 − z₂ ≤ C ε` with `C ε ≤ 1/2` gives `dd b − dd a ≤ 2 C ε`.

So a bounded factor on the deficit across one transverse doubling holds exactly when the twisted
transfer's defect exceeds the untwisted one's by at most a multiple of `ε`. The admissible excess is
of the size of the deficit itself, not of order one: an excess `d` of order one gives
`z₂ = z² e^{−d}`, a deficit of order one.

**The defect difference splits over the electric-flux sectors of the slice** (`dd_ge_evL`,
`dd_sub_le_sectors`). For `a` and `b` each admissible for a list of commuting flips (`SectorDefect.Adm`),
with `e_a = evL a l`, `e_b = evL b l'` their trivial sectors,

    dd b − dd a ≤ (dd e_b − dd e_a) + 2 log(hs b / hs e_b) + log(1 + (hs a − hs e_a)² / hs(e_a ∗ e_a)).

The three terms are the difference of the two trivial-sector defects, the log inverse trivial share of
the twisted kernel, and the squared flux odds of the untwisted kernel weighted by its trivial sector's
doubling. `one_sub_ratio_conv_le_of_sectors` composes this with the first bound.

Scope. Nothing here mentions a lattice. On the Wilson lattice `b` is the transfer of the twisted
spatial action; that kernel, its flip invariance, and the identification of `hs b / hs a` with
`FluxShareSquaring.twistRatio` (the same twisted partition function read along the twisted plane's
own direction `i`) are not constructed in this module.

DERIVED (module-wide): `2` is the square of the trace (one doubling); `2` in `2 C ε` is
`x/(1 − x) ≤ 2x` for `x ≤ 1/2`.
-/

noncomputable section

namespace MassGap.TwistedTransferDoubling

open MeasureTheory MassGap.KernelPower MassGap.FluxSectorBound MassGap.SectorDefect

/-! ## 1. Real-number steps -/

/-- `(1 − ε)² (1 − c ε) ≥ 1 − (2 + c) ε` for `ε ∈ [0, 1]`, `c ≥ 0`: the difference is
`ε² (1 + c + c (1 − ε))`. -/
theorem one_sub_sq_mul_ge {ε c : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hc : 0 ≤ c) :
    1 - (2 + c) * ε ≤ (1 - ε) ^ 2 * (1 - c * ε) := by
  have h1 : 0 ≤ ε * ε := mul_nonneg hε0 hε0
  have h2 : 0 ≤ c * (ε * ε) := mul_nonneg hc h1
  have h3 : 0 ≤ c * (ε * ε) * (1 - ε) := mul_nonneg h2 (by linarith)
  nlinarith [h1, h2, h3]

/-- `−log(1 − x) ≤ 2x` for `x ∈ [0, 1/2]`. -/
theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith
  linarith

/-! ## 2. The identity -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **The transverse doubling of the twisted ratio**:
`log z₂ = 2 log z + dd a − dd b`. -/
theorem log_ratio_conv {a b : X → X → ℝ} (ha : 0 < hs μ a) (hb : 0 < hs μ b)
    (ha2 : 0 < hs μ (conv μ a a)) (hb2 : 0 < hs μ (conv μ b b)) :
    Real.log (hs μ (conv μ b b) / hs μ (conv μ a a))
      = 2 * Real.log (hs μ b / hs μ a) + dd μ a - dd μ b := by
  rw [Real.log_div hb2.ne' ha2.ne', Real.log_div hb.ne' ha.ne']
  unfold dd
  ring

/-- **The transverse doubling of the twisted ratio**: `z₂ = z² · exp(dd a − dd b)`. -/
theorem ratio_conv_eq {a b : X → X → ℝ} (ha : 0 < hs μ a) (hb : 0 < hs μ b)
    (ha2 : 0 < hs μ (conv μ a a)) (hb2 : 0 < hs μ (conv μ b b)) :
    hs μ (conv μ b b) / hs μ (conv μ a a)
      = (hs μ b / hs μ a) ^ 2 * Real.exp (dd μ a - dd μ b) := by
  have hz : 0 < hs μ b / hs μ a := div_pos hb ha
  have h2 : 0 < hs μ (conv μ b b) / hs μ (conv μ a a) := div_pos hb2 ha2
  rw [← Real.exp_log h2, log_ratio_conv ha hb ha2 hb2,
    show 2 * Real.log (hs μ b / hs μ a) + dd μ a - dd μ b
      = Real.log ((hs μ b / hs μ a) ^ 2) + (dd μ a - dd μ b) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_add, Real.exp_log (pow_pos hz 2)]

/-! ## 3. Non-spreading as a defect comparison -/

/-- **Sufficiency.** If the twisted defect exceeds the untwisted one by at most `c ε`, `ε = 1 − z`,
the deficit grows by at most the factor `2 + c` across the transverse doubling. -/
theorem one_sub_ratio_conv_le {a b : X → X → ℝ} (ha : 0 < hs μ a) (hb : 0 < hs μ b)
    (ha2 : 0 < hs μ (conv μ a a)) (hb2 : 0 < hs μ (conv μ b b)) (hz1 : hs μ b / hs μ a ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (hd : dd μ b - dd μ a ≤ c * (1 - hs μ b / hs μ a)) :
    1 - hs μ (conv μ b b) / hs μ (conv μ a a) ≤ (2 + c) * (1 - hs μ b / hs μ a) := by
  rw [ratio_conv_eq ha hb ha2 hb2]
  set z := hs μ b / hs μ a with hzdef
  have hz : 0 < z := div_pos hb ha
  have hexp : 1 - c * (1 - z) ≤ Real.exp (dd μ a - dd μ b) := by
    have h1 := Real.add_one_le_exp (-(c * (1 - z)))
    have h2 : Real.exp (-(c * (1 - z))) ≤ Real.exp (dd μ a - dd μ b) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hlow := one_sub_sq_mul_ge (ε := 1 - z) (by linarith) (by linarith) hc
  have hsq : (1 - (1 - z)) ^ 2 = z ^ 2 := by ring
  rw [hsq] at hlow
  have : z ^ 2 * (1 - c * (1 - z)) ≤ z ^ 2 * Real.exp (dd μ a - dd μ b) :=
    mul_le_mul_of_nonneg_left hexp (sq_nonneg z)
  linarith

/-- **Necessity.** If the deficit grows by at most the factor `C` across the transverse doubling,
with `C ε ≤ 1/2`, the twisted defect exceeds the untwisted one by at most `2 C ε`. -/
theorem dd_sub_le_of_one_sub_ratio_conv {a b : X → X → ℝ} (ha : 0 < hs μ a) (hb : 0 < hs μ b)
    (ha2 : 0 < hs μ (conv μ a a)) (hb2 : 0 < hs μ (conv μ b b)) (hz1 : hs μ b / hs μ a ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hhalf : C * (1 - hs μ b / hs μ a) ≤ 1 / 2)
    (hN : 1 - hs μ (conv μ b b) / hs μ (conv μ a a) ≤ C * (1 - hs μ b / hs μ a)) :
    dd μ b - dd μ a ≤ 2 * C * (1 - hs μ b / hs μ a) := by
  set z := hs μ b / hs μ a with hzdef
  set z₂ := hs μ (conv μ b b) / hs μ (conv μ a a) with hz₂def
  have hz : 0 < z := div_pos hb ha
  have hlogz : Real.log z ≤ 0 := Real.log_nonpos hz.le hz1
  have hid : dd μ b - dd μ a = 2 * Real.log z - Real.log z₂ := by
    have := log_ratio_conv ha hb ha2 hb2
    rw [← hzdef, ← hz₂def] at this
    linarith
  have hx0 : 0 ≤ C * (1 - z) := mul_nonneg hC (by linarith)
  have hpos : 0 < 1 - C * (1 - z) := by linarith
  have hmono : Real.log (1 - C * (1 - z)) ≤ Real.log z₂ :=
    Real.log_le_log hpos (by linarith)
  have hneg := neg_log_one_sub_le hx0 hhalf
  rw [hid]
  linarith

/-! ## 4. The defect difference over the electric-flux sectors -/

variable [IsProbabilityMeasure μ]

theorem hs_pos_of_adm {l : List (X → X)} {c : ℝ} {k : X → X → ℝ} (hc : 0 < c) (hk : Adm l c k) :
    0 < hs μ k := by
  have := sq_le_hs (μ := μ) hk.bdd hc.le hk.low
  have : 0 < c ^ 2 := by positivity
  linarith

theorem hs_conv_pos_of_adm {l : List (X → X)} {c : ℝ} {k : X → X → ℝ} (hc : 0 < c)
    (hk : Adm l c k) : 0 < hs μ (conv μ k k) := by
  have := sq_le_hs (μ := μ) (hk.bdd.conv (μ := μ) hk.bdd) (mul_nonneg hc.le hc.le)
    (conv_low (μ := μ) hk.bdd hc.le hk.low)
  have : 0 < (c * c) ^ 2 := by positivity
  linarith

/-- **The defect from below through the trivial sector**:
`dd a ≥ dd e + 2 log(hs a / hs e) − log(1 + (hs a − hs e)² / hs(e ∗ e))`, `e = evL a l`. -/
theorem dd_ge_evL {c : ℝ} (hc : 0 < c) (l : List (X → X)) (a : X → X → ℝ) (hl : Flips μ l)
    (ha : Adm l c a) :
    dd μ (evL a l) + 2 * (Real.log (hs μ a) - Real.log (hs μ (evL a l)))
      - Real.log (1 + (hs μ a - hs μ (evL a l)) ^ 2 / hs μ (conv μ (evL a l) (evL a l)))
      ≤ dd μ a := by
  have he := adm_evL l a hl ha
  have hA2 : 0 < hs μ (conv μ a a) := hs_conv_pos_of_adm hc ha
  have hE2 : 0 < hs μ (conv μ (evL a l) (evL a l)) := hs_conv_pos_of_adm hc he
  set E2 := hs μ (conv μ (evL a l) (evL a l)) with hE2def
  set D := hs μ a - hs μ (evL a l) with hDdef
  have hconv : hs μ (conv μ a a) ≤ E2 + D ^ 2 := hs_conv_le_evL l a hl ha
  have hfac : E2 + D ^ 2 = E2 * (1 + D ^ 2 / E2) := by
    have hne : E2 ≠ 0 := hE2.ne'
    rw [mul_add, mul_one, mul_div_cancel₀ (D ^ 2) hne]
  have h1 : 0 < 1 + D ^ 2 / E2 := by positivity
  have hlog : Real.log (hs μ (conv μ a a)) ≤ Real.log E2 + Real.log (1 + D ^ 2 / E2) := by
    rw [← Real.log_mul hE2.ne' h1.ne', ← hfac]
    exact Real.log_le_log hA2 hconv
  unfold dd
  linarith

/-- **The defect difference over the sectors.** For `a` admissible for `l` and `b` admissible for
`l'`, with trivial sectors `e_a = evL a l`, `e_b = evL b l'`:
`dd b − dd a ≤ (dd e_b − dd e_a) + 2 log(hs b / hs e_b) + log(1 + (hs a − hs e_a)² / hs(e_a ∗ e_a))`. -/
theorem dd_sub_le_sectors {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (l l' : List (X → X))
    (a b : X → X → ℝ) (hl : Flips μ l) (hl' : Flips μ l') (ha : Adm l c a) (hb : Adm l' c' b) :
    dd μ b - dd μ a
      ≤ (dd μ (evL b l') - dd μ (evL a l))
        + 2 * (Real.log (hs μ b) - Real.log (hs μ (evL b l')))
        + Real.log (1 + (hs μ a - hs μ (evL a l)) ^ 2 / hs μ (conv μ (evL a l) (evL a l))) := by
  have hup := dd_le_evL hc' l' b hl' hb
  have hdown := dd_ge_evL hc l a hl ha
  have he := adm_evL l a hl ha
  have hE : 0 < hs μ (evL a l) := hs_pos_of_adm hc he
  have hEA : Real.log (hs μ (evL a l)) ≤ Real.log (hs μ a) :=
    Real.log_le_log hE (hs_evL_le l a hl ha)
  linarith

/-- **Non-spreading from the sector comparison.** If the sector bound on `dd b − dd a` is at most
`c₀ ε`, `ε = 1 − hs b / hs a`, the deficit grows by at most the factor `2 + c₀` across the transverse
doubling. -/
theorem one_sub_ratio_conv_le_of_sectors {c c' c₀ : ℝ} (hc : 0 < c) (hc' : 0 < c') (hc₀ : 0 ≤ c₀)
    (l l' : List (X → X)) (a b : X → X → ℝ) (hl : Flips μ l) (hl' : Flips μ l') (ha : Adm l c a)
    (hb : Adm l' c' b) (hz1 : hs μ b / hs μ a ≤ 1)
    (hsec : (dd μ (evL b l') - dd μ (evL a l))
        + 2 * (Real.log (hs μ b) - Real.log (hs μ (evL b l')))
        + Real.log (1 + (hs μ a - hs μ (evL a l)) ^ 2 / hs μ (conv μ (evL a l) (evL a l)))
      ≤ c₀ * (1 - hs μ b / hs μ a)) :
    1 - hs μ (conv μ b b) / hs μ (conv μ a a) ≤ (2 + c₀) * (1 - hs μ b / hs μ a) :=
  one_sub_ratio_conv_le (hs_pos_of_adm hc ha) (hs_pos_of_adm hc' hb) (hs_conv_pos_of_adm hc ha)
    (hs_conv_pos_of_adm hc' hb) hz1 hc₀
    ((dd_sub_le_sectors hc hc' l l' a b hl hl' ha hb).trans hsec)

end MassGap.TwistedTransferDoubling

end

#print axioms MassGap.TwistedTransferDoubling.ratio_conv_eq
#print axioms MassGap.TwistedTransferDoubling.one_sub_ratio_conv_le
#print axioms MassGap.TwistedTransferDoubling.dd_sub_le_of_one_sub_ratio_conv
#print axioms MassGap.TwistedTransferDoubling.dd_ge_evL
#print axioms MassGap.TwistedTransferDoubling.dd_sub_le_sectors
#print axioms MassGap.TwistedTransferDoubling.one_sub_ratio_conv_le_of_sectors
