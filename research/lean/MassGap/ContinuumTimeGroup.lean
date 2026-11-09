import Mathlib
import MassGap.ObserverEnergyReductionsN

noncomputable section

/-!
# MassGap.ContinuumTimeGroup — the continuous time translations of the flowed reconstruction

`ContinuumFlow.flow_reconstruction` reconstructs, at every dyadic step `m`, a Hilbert space, a unit
vacuum and a positive self-adjoint transfer `T_m` of norm at most one, the time translation by the
spacing `a_m = dySpacing N m`. This module puts the steps on one space and extends the dyadic times to
every real time `t ≥ 0`.

## One space for every step

`flowTransfer hN Φ hB τ hpos m` is `gTransfer` with the same kernel, the same reflection form and the
same vacuum at every `m`; only the step `MarginMono.shift hN τ m` changes. So the reconstructed Hilbert
spaces at all steps are one type, `FlowH`, and the vacuum is one vector, `vacT`. On it the steps are
the operators `stepT m`, with `stepT (m + 1) * stepT (m + 1) = stepT m` (`stepT_sq`, from
`ContinuumFlow.gT_half`).

## The time group

A positive square root is unique (`CFC.sqrt_unique`), so `stepT m = A ^ (1/2)^m` with `A = stepT 0`,
the real power taken in the continuous functional calculus (`stepT_eq_powT`). The time translation at
`t ≥ 0` is `timeT t = A ^ (t / a_0)`. It agrees with the dyadic steps, `timeT (n a_m) = stepT m ^ n`
(`timeT_dyadic`); it is a semigroup of positive self-adjoint contractions (`timeT_add`, `timeT_zero`,
`timeT_nonneg`, `norm_timeT_le_one`); it is norm continuous on `t > 0` (`norm_powT_sub_le`) and strongly
continuous on `t ≥ 0` (`continuousOn_timeT`). Strong continuity at `t = 0` is `ker A = 0`
(`stepT_zero_injective`): every margin monomial is one step forward of another margin monomial once
the step is smaller than its margin, so a vector killed by `A` is killed by every `stepT m` and is
orthogonal to every reconstructed monomial, which are dense.

## The gap in continuous time

The dyadic gaps `GappedAt (flowTransfer m) (e^{-μ a_m})`, `μ` independent of `m` (what
`FlowCapstone.flow_clay` and `ObserverEnergyReductionsN.flowN_clay_of_gap` conclude), give at every
`t ≥ 0`: `timeT t Ω = Ω`, `‖timeT t u‖ ≤ e^{-μ t} ‖u‖` on the vacuum complement, and
`spectrum ℝ (timeT t) ⊆ {1} ∪ [0, e^{-μ t}]` (`flow_time_group`). The two norm statements pass from
the dense dyadic times to every time through the norm continuity; the spectral one is the spectral
mapping of `x ↦ x ^ (t / a_0)` on the step-zero spectrum.

## The Hamiltonian

`-log A` is an element of the operator algebra only when `0` is outside the spectrum of `A`; in
general the generator `H = -(1/a_0) log A` is unbounded and the statement above is the semigroup form
of `spec H ⊆ {0} ∪ [μ, ∞)`. No Hamiltonian is constructed in this module.
-/

namespace MassGap.ContinuumTimeGroup

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger MassGap.ContinuumReconstruction
  MassGap.ContinuumFlow Filter
open scoped Topology

/-! ## 1. Real powers on `[0, 1]` -/

section Real

/-- A real lemma used to pass from `∀ ε > 0, a ≤ b + ε` to `a ≤ b`.

DERIVED: `0` is the sign of `ε`; `2` halves the excess. -/
theorem le_of_forall_pos_le_add' {a b : ℝ} (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have := h ((a - b) / 2) (by linarith)
  linarith

#print axioms le_of_forall_pos_le_add'

/-- **The real power is Lipschitz in the exponent away from zero, uniformly on `[0, 1]`**:
`0 ≤ x ^ s − x ^ (s + h) ≤ h / s` for `0 ≤ x ≤ 1`, `s > 0`, `h ≥ 0`. With `L = log x ≤ 0`,
`x ^ s − x ^ (s+h) = e^{sL}(1 − e^{hL}) ≤ e^{sL}(−hL) = (h/s)(−sL)e^{sL} ≤ h/s`, by `1 + u ≤ e^u`
twice.

DERIVED: `0` and `1` bound the base; `0` is the sign of `s` and `h`. -/
theorem rpow_sub_rpow_le {x s h : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hs : 0 < s) (hh : 0 ≤ h) :
    0 ≤ x ^ s - x ^ (s + h) ∧ x ^ s - x ^ (s + h) ≤ h / s := by
  refine ⟨sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hs.le (by linarith)), ?_⟩
  rcases hx0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hs.ne', Real.zero_rpow (by linarith : s + h ≠ 0), sub_zero]
    exact div_nonneg hh hs.le
  · have hL0 : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
    rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hpos]
    have hsplit : Real.exp (Real.log x * (s + h))
        = Real.exp (Real.log x * s) * Real.exp (Real.log x * h) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsplit]
    have hE0 : 0 < Real.exp (Real.log x * s) := Real.exp_pos _
    have h1 : 1 - Real.exp (Real.log x * h) ≤ -(Real.log x * h) := by
      linarith [Real.add_one_le_exp (Real.log x * h)]
    have h4 : Real.exp (-(Real.log x * s)) * Real.exp (Real.log x * s) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h2 : (-(Real.log x * s)) * Real.exp (Real.log x * s) ≤ 1 := by
      have h3 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(Real.log x * s))) hE0.le
      nlinarith [h3, h4, hE0]
    rw [le_div_iff₀ hs]
    have h5 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hE0.le hs.le)
    have h6 := mul_le_mul_of_nonneg_left h2 hh
    have e1 : (Real.exp (Real.log x * s) - Real.exp (Real.log x * s) * Real.exp (Real.log x * h)) * s
        = Real.exp (Real.log x * s) * s * (1 - Real.exp (Real.log x * h)) := by ring
    have e2 : Real.exp (Real.log x * s) * s * (-(Real.log x * h))
        = h * ((-(Real.log x * s)) * Real.exp (Real.log x * s)) := by ring
    rw [e1]
    linarith [h5, h6, e2]

#print axioms rpow_sub_rpow_le

end Real

/-! ## 2. Real powers of a positive contraction -/

section Powers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The real power** `a ^ s = cfc (x ↦ x ^ s) a` in the continuous functional calculus.

DERIVED: no numeral. -/
def powT (a : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E := cfc (fun x : ℝ => x ^ s) a

variable {a : E →L[ℂ] E}

/-- DERIVED: `0` is the power; `1` the identity. -/
theorem powT_zero (ha : IsSelfAdjoint a) : powT a 0 = 1 := by
  simp only [powT, Real.rpow_zero]
  exact cfc_const_one ℝ a ha

#print axioms powT_zero

/-- DERIVED: `1` is the power. -/
theorem powT_one (ha : IsSelfAdjoint a) : powT a 1 = a := by
  simp only [powT, Real.rpow_one]
  exact cfc_id' ℝ a ha

#print axioms powT_one

/-- **The semigroup law** for nonnegative exponents, on a spectrum in `[0, 1]`.

DERIVED: `0` is the sign of the exponents and the bottom of the spectrum; `1` its top. -/
theorem powT_add (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    powT a (s + t) = powT a s * powT a t := by
  unfold powT
  rw [← cfc_mul (fun x : ℝ => x ^ s) (fun x : ℝ => x ^ t) a
    (Real.continuous_rpow_const hs).continuousOn (Real.continuous_rpow_const ht).continuousOn]
  refine cfc_congr (fun x hx => ?_)
  have hx0 : 0 ≤ x := (hsp hx).1
  rcases (add_nonneg hs ht).eq_or_lt with h0 | h0
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    rw [hs0, ht0, add_zero, Real.rpow_zero, one_mul]
  · exact Real.rpow_add' hx0 h0.ne'

#print axioms powT_add

/-- **Dyadic powers**: `a ^ (n q) = (a ^ q) ^ n` for `q ≥ 0`.

DERIVED: `0` is the sign of `q`; `1` the successor step. -/
theorem powT_nat_mul (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {q : ℝ}
    (hq : 0 ≤ q) (n : ℕ) : powT a (n * q) = powT a q ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero, powT_zero ha]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, powT_add hsp (mul_nonneg (Nat.cast_nonneg n) hq) hq, ih,
      pow_succ]

#print axioms powT_nat_mul

/-- DERIVED: no numeral. -/
theorem isSelfAdjoint_powT (s : ℝ) : IsSelfAdjoint (powT a s) := cfc_predicate _ _

#print axioms isSelfAdjoint_powT

/-- **The power is positive.**

DERIVED: `0` is the order's bottom and the bottom of the spectrum; `1` its top. -/
theorem powT_nonneg (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) (s : ℝ) : 0 ≤ powT a s :=
  cfc_nonneg (fun x hx => Real.rpow_nonneg (hsp hx).1 s)

#print axioms powT_nonneg

/-- **The power is a contraction.**

DERIVED: `0` and `1` bound the spectrum and the exponent; `1` is the norm bound. -/
theorem norm_powT_le_one (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {s : ℝ} (hs : 0 ≤ s) :
    ‖powT a s‖ ≤ 1 :=
  norm_cfc_le zero_le_one (fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hsp hx).1 s)]
    exact Real.rpow_le_one (hsp hx).1 (hsp hx).2 hs)

#print axioms norm_powT_le_one

/-- **Norm continuity in the exponent**: `‖a ^ s − a ^ (s + h)‖ ≤ h / s` for `s > 0`, `h ≥ 0`
(`rpow_sub_rpow_le` on the spectrum, `norm_cfc_le`).

DERIVED: `0` and `1` bound the spectrum; `0` is the sign of `s` and `h`. -/
theorem norm_powT_sub_le (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {s h : ℝ} (hs : 0 < s)
    (hh : 0 ≤ h) : ‖powT a s - powT a (s + h)‖ ≤ h / s := by
  unfold powT
  rw [← cfc_sub (fun x : ℝ => x ^ s) (fun x : ℝ => x ^ (s + h)) a
    (Real.continuous_rpow_const hs.le).continuousOn
    (Real.continuous_rpow_const (by linarith)).continuousOn]
  refine norm_cfc_le (div_nonneg hh hs.le) (fun x hx => ?_)
  obtain ⟨h1, h2⟩ := rpow_sub_rpow_le (hsp hx).1 (hsp hx).2 hs hh
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

#print axioms norm_powT_sub_le

/-- The symmetric form: `‖a ^ s − a ^ t‖ ≤ |s − t| / min s t` for `s, t > 0`.

DERIVED: `0` is the sign of the exponents. -/
theorem norm_powT_sub_le' (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) : ‖powT a s - powT a t‖ ≤ |s - t| / min s t := by
  rcases le_total s t with hst | hts
  · have h := norm_powT_sub_le hsp hs (sub_nonneg.mpr hst)
    rw [add_sub_cancel] at h
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst), min_eq_left hst]
    exact h
  · have h := norm_powT_sub_le hsp ht (sub_nonneg.mpr hts)
    rw [add_sub_cancel] at h
    rw [norm_sub_rev, abs_of_nonneg (sub_nonneg.mpr hts), min_eq_right hts]
    exact h

#print axioms norm_powT_sub_le'

/-- **Norm continuity on `s > 0`.**

DERIVED: `0` is the open end; `2` halves the base point. -/
theorem continuousAt_powT (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ContinuousAt (powT a) s₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min (s₀ / 2) (ε * s₀ / 4), lt_min (by linarith) (by positivity), fun s hs => ?_⟩
  rw [Real.dist_eq] at hs
  have hs1 : |s - s₀| < s₀ / 2 := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : |s - s₀| < ε * s₀ / 4 := lt_of_lt_of_le hs (min_le_right _ _)
  have hspos : s₀ / 2 < s := by linarith [(abs_lt.mp hs1).1]
  have hmin : s₀ / 2 ≤ min s s₀ := le_min hspos.le (by linarith)
  rw [dist_eq_norm]
  calc ‖powT a s - powT a s₀‖ ≤ |s - s₀| / min s s₀ :=
        norm_powT_sub_le' hsp (by linarith) hs₀
    _ ≤ |s - s₀| / (s₀ / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hmin
    _ < (ε * s₀ / 4) / (s₀ / 2) := div_lt_div_of_pos_right hs2 (by linarith)
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

#print axioms continuousAt_powT

/-- **Dense range from a trivial kernel** for a self-adjoint operator: `(range a)ᗮ = ker a`.

DERIVED: `0` is the zero vector. -/
theorem dense_range_of_injective (ha : IsSelfAdjoint a) (hker : ∀ x, a x = 0 → x = 0) :
    Dense (Set.range a) := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha
  have hperp : (LinearMap.range (a : E →ₗ[ℂ] E))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have h1 : inner ℂ (a (a v)) v = 0 :=
      (Submodule.mem_orthogonal _ _).mp hv (a (a v)) ⟨a v, rfl⟩
    have h2 : inner ℂ (a v) (a v) = 0 := by
      have := hsym (a v) v
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [← this]
      exact h1
    exact hker v (inner_self_eq_zero.mp h2)
  have hcl : (LinearMap.range (a : E →ₗ[ℂ] E)).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr hperp
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr hcl
  have hset : ((LinearMap.range (a : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) = Set.range a := by
    ext y
    simp
  rwa [hset] at hd

#print axioms dense_range_of_injective

/-- **Strong continuity at time zero** from a trivial kernel: `a ^ s y → y` as `s → 0⁺`. On the
range, `a ^ s (a z) − a z = (a ^ (1+s) − a ^ 1) z` has norm at most `s ‖z‖`; the range is dense
and every power is a contraction.

DERIVED: `0` is the time and the zero vector; `1` the power of `a`; `3` splits `ε`. -/
theorem tendsto_powT_zero (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (y : E) :
    Tendsto (fun s => powT a s y) (𝓝[Set.Ici 0] 0) (𝓝 y) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨w, hw, z, rfl⟩ :=
    Metric.dense_iff.mp (dense_range_of_injective ha hker) y (ε / 3) (by positivity)
  rw [Metric.mem_ball] at hw
  refine ⟨ε / (3 * (‖z‖ + 1)), by positivity, fun s hs hsd => ?_⟩
  have hs0 : 0 ≤ s := hs
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0] at hsd
  have hz1 : 0 < ‖z‖ + 1 := by positivity
  have hpow : powT a s (a z) = powT a (1 + s) z := by
    rw [add_comm, powT_add hsp hs0 zero_le_one, powT_one ha, ContinuousLinearMap.mul_apply]
  have hA : ‖powT a s (y - a z)‖ ≤ ‖y - a z‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_powT_le_one hsp hs0))
  have hB : ‖a z - powT a (1 + s) z‖ ≤ s * ‖z‖ := by
    have h := norm_powT_sub_le hsp (a := a) one_pos hs0
    rw [powT_one ha, div_one] at h
    calc ‖a z - powT a (1 + s) z‖ = ‖(a - powT a (1 + s)) z‖ := by
          rw [ContinuousLinearMap.sub_apply]
      _ ≤ ‖a - powT a (1 + s)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ s * ‖z‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have hC : s * ‖z‖ ≤ ε / 3 := by
    have h1 : s * ‖z‖ ≤ ε / (3 * (‖z‖ + 1)) * (‖z‖ + 1) :=
      mul_le_mul hsd.le (by linarith) (norm_nonneg _) (by positivity)
    have h2 : ε / (3 * (‖z‖ + 1)) * (‖z‖ + 1) = ε / 3 := by field_simp
    linarith
  have hD : ‖y - a z‖ < ε / 3 := by rw [← dist_eq_norm, dist_comm]; exact hw
  rw [dist_eq_norm]
  have hsplit : powT a s y - y
      = powT a s (y - a z) - (a z - powT a (1 + s) z) + (a z - y) := by
    rw [map_sub, hpow]
    abel
  rw [hsplit]
  have hE : ‖a z - y‖ = ‖y - a z‖ := norm_sub_rev _ _
  calc ‖powT a s (y - a z) - (a z - powT a (1 + s) z) + (a z - y)‖
      ≤ ‖powT a s (y - a z)‖ + ‖a z - powT a (1 + s) z‖ + ‖a z - y‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ < ε := by linarith

#print axioms tendsto_powT_zero

/-- **Strong continuity on `[0, ∞)`**: norm continuity on `s > 0`, and `tendsto_powT_zero` at `0`.

DERIVED: `0` is the time origin. -/
theorem continuousOn_powT_apply (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hker : ∀ x, a x = 0 → x = 0) (y : E) :
    ContinuousOn (fun s => powT a s y) (Set.Ici 0) := by
  intro s₀ hs₀
  rcases (Set.mem_Ici.mp hs₀).eq_or_lt with h0 | h0
  · rw [← h0]
    show Tendsto (fun s => powT a s y) (𝓝[Set.Ici 0] 0) (𝓝 (powT a 0 y))
    rw [powT_zero ha, ContinuousLinearMap.one_apply]
    exact tendsto_powT_zero ha hsp hker y
  · exact ((continuousAt_powT hsp h0).clm_apply continuousAt_const).continuousWithinAt

#print axioms continuousOn_powT_apply

/-- **Dyadic approximation from above**: for `s > 0` and `ε > 0` there is a dyadic `d = n (1/2)^m ≥ s`
with `‖a ^ s − a ^ d‖ ≤ ε`.

DERIVED: `0` is the sign of `s`, `ε`; `1/2` is the dyadic ratio; `1` the ceiling's excess. -/
theorem exists_dyadic_near (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {s ε : ℝ} (hs : 0 < s)
    (hε : 0 < ε) : ∃ m n : ℕ, s ≤ n * (1 / 2 : ℝ) ^ m
      ∧ ‖powT a s - powT a (n * (1 / 2 : ℝ) ^ m)‖ ≤ ε := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (mul_pos hε hs) (by norm_num : (1 / 2 : ℝ) < 1)
  set q : ℝ := (1 / 2 : ℝ) ^ m with hq
  have hq0 : 0 < q := by positivity
  refine ⟨m, ⌈s / q⌉₊, ?_, ?_⟩
  · have h := Nat.le_ceil (s / q)
    rw [div_le_iff₀ hq0] at h
    exact h
  · have hup : (⌈s / q⌉₊ : ℝ) < s / q + 1 := Nat.ceil_lt_add_one (by positivity)
    have hlo : s ≤ (⌈s / q⌉₊ : ℝ) * q := by
      have h := Nat.le_ceil (s / q)
      rwa [div_le_iff₀ hq0] at h
    have hlt : (⌈s / q⌉₊ : ℝ) * q - s < q := by
      have := mul_lt_mul_of_pos_right hup hq0
      rw [add_mul, div_mul_cancel₀ s hq0.ne', one_mul] at this
      linarith
    have h := norm_powT_sub_le hsp (a := a) hs (sub_nonneg.mpr hlo)
    rw [add_sub_cancel] at h
    refine h.trans ?_
    rw [div_le_iff₀ hs]
    linarith

#print axioms exists_dyadic_near

/-- **A vector fixed at the dyadic times is fixed at every time.**

DERIVED: `0` is the time origin and the sign of `ε`; `1/2` the dyadic ratio; `1` keeps the divisor
positive. -/
theorem powT_apply_fixed (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {Ω : E}
    (hfix : ∀ m n : ℕ, powT a (n * (1 / 2 : ℝ) ^ m) Ω = Ω) {s : ℝ} (hs : 0 ≤ s) :
    powT a s Ω = Ω := by
  rcases hs.eq_or_lt with h0 | h0
  · rw [← h0, powT_zero ha, ContinuousLinearMap.one_apply]
  · refine eq_of_forall_dist_le (fun ε hε => ?_)
    obtain ⟨m, n, -, hmn⟩ := exists_dyadic_near hsp h0 (by positivity : 0 < ε / (‖Ω‖ + 1))
    rw [dist_eq_norm]
    have h1 : powT a s Ω - Ω = (powT a s - powT a (n * (1 / 2 : ℝ) ^ m)) Ω := by
      rw [ContinuousLinearMap.sub_apply, hfix m n]
    rw [h1]
    calc ‖(powT a s - powT a (n * (1 / 2 : ℝ) ^ m)) Ω‖
        ≤ ‖powT a s - powT a (n * (1 / 2 : ℝ) ^ m)‖ * ‖Ω‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε / (‖Ω‖ + 1) * ‖Ω‖ := mul_le_mul_of_nonneg_right hmn (norm_nonneg _)
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg Ω]

#print axioms powT_apply_fixed

/-- **A dyadic exponential bound extends to every time**: if
`‖a ^ (n (1/2)^m) u‖ ≤ e^{-ν n (1/2)^m} ‖u‖` at every dyadic time, `ν ≥ 0`, then
`‖a ^ s u‖ ≤ e^{-ν s} ‖u‖` at every `s ≥ 0`.

DERIVED: `0` is the time origin, the sign of `ν` and of `ε`; `1/2` the dyadic ratio; `1` keeps the
divisor positive. -/
theorem norm_powT_apply_le (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {ν : ℝ}
    (hν : 0 ≤ ν) {u : E}
    (hd : ∀ m n : ℕ, ‖powT a (n * (1 / 2 : ℝ) ^ m) u‖
      ≤ Real.exp (-(ν * (n * (1 / 2 : ℝ) ^ m))) * ‖u‖) {s : ℝ} (hs : 0 ≤ s) :
    ‖powT a s u‖ ≤ Real.exp (-(ν * s)) * ‖u‖ := by
  rcases hs.eq_or_lt with h0 | h0
  · rw [← h0, powT_zero ha, ContinuousLinearMap.one_apply, mul_zero, neg_zero, Real.exp_zero,
      one_mul]
  · refine le_of_forall_pos_le_add' (fun ε hε => ?_)
    obtain ⟨m, n, hsd, hmn⟩ := exists_dyadic_near hsp h0 (by positivity : 0 < ε / (‖u‖ + 1))
    have h1 : powT a s u = (powT a s - powT a (n * (1 / 2 : ℝ) ^ m)) u
        + powT a (n * (1 / 2 : ℝ) ^ m) u := by
      rw [ContinuousLinearMap.sub_apply]
      abel
    have h2 : ‖(powT a s - powT a (n * (1 / 2 : ℝ) ^ m)) u‖ ≤ ε := by
      calc ‖(powT a s - powT a (n * (1 / 2 : ℝ) ^ m)) u‖
          ≤ ‖powT a s - powT a (n * (1 / 2 : ℝ) ^ m)‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ε / (‖u‖ + 1) * ‖u‖ := mul_le_mul_of_nonneg_right hmn (norm_nonneg _)
        _ ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg u]
    have h3 : Real.exp (-(ν * (n * (1 / 2 : ℝ) ^ m))) ≤ Real.exp (-(ν * s)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h4 := mul_le_mul_of_nonneg_right h3 (norm_nonneg u)
    rw [h1]
    calc ‖(powT a s - powT a (n * (1 / 2 : ℝ) ^ m)) u + powT a (n * (1 / 2 : ℝ) ^ m) u‖
        ≤ ‖(powT a s - powT a (n * (1 / 2 : ℝ) ^ m)) u‖ + ‖powT a (n * (1 / 2 : ℝ) ^ m) u‖ :=
          norm_add_le _ _
      _ ≤ ε + Real.exp (-(ν * s)) * ‖u‖ := add_le_add h2 ((hd m n).trans h4)
      _ = Real.exp (-(ν * s)) * ‖u‖ + ε := add_comm _ _

#print axioms norm_powT_apply_le

/-- **The spectral gap passes to every power**: `spectrum a ⊆ {1} ∪ [0, ρ]` gives
`spectrum (a ^ s) ⊆ {1} ∪ [0, ρ ^ s]` for `s ≥ 0` (`cfc_map_spectrum`).

DERIVED: `0` and `1` bound the spectrum; `1` is the vacuum eigenvalue; `0` the sign of `s` and `ρ`. -/
theorem spectrum_powT_subset (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1) {ρ : ℝ}
    (hgap : spectrum ℝ a ⊆ {1} ∪ Set.Icc 0 ρ) {s : ℝ} (hs : 0 ≤ s) :
    spectrum ℝ (powT a s) ⊆ {1} ∪ Set.Icc 0 (ρ ^ s) := by
  unfold powT
  rw [cfc_map_spectrum (fun x : ℝ => x ^ s) a ha (Real.continuous_rpow_const hs).continuousOn]
  rintro _ ⟨x, hx, rfl⟩
  rcases hgap hx with h1 | h2
  · left
    rw [Set.mem_singleton_iff] at h1 ⊢
    rw [h1]
    exact Real.one_rpow s
  · right
    exact ⟨Real.rpow_nonneg h2.1 s, Real.rpow_le_rpow h2.1 h2.2 hs⟩

#print axioms spectrum_powT_subset

/-- **Uniqueness of the dyadic roots**: a sequence of positive operators `b m` with `b 0 = a` and
`b (m+1) * b (m+1) = b m` is `b m = a ^ (1/2)^m` (`CFC.sqrt_unique` at each step).

DERIVED: `1/2` the dyadic ratio; `0` the first step and the order's bottom; `1` the successor. -/
theorem eq_powT_of_sq (ha : IsSelfAdjoint a) (hsp : spectrum ℝ a ⊆ Set.Icc 0 1)
    (b : ℕ → E →L[ℂ] E) (h0 : b 0 = a) (hpos : ∀ m, 0 ≤ b m)
    (hsq : ∀ m, b (m + 1) * b (m + 1) = b m) (m : ℕ) :
    b m = powT a ((1 / 2 : ℝ) ^ m) := by
  induction m with
  | zero => rw [pow_zero, powT_one ha, h0]
  | succ m ih =>
    have hq : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
    have hhalf : powT a ((1 / 2 : ℝ) ^ (m + 1)) * powT a ((1 / 2 : ℝ) ^ (m + 1))
        = powT a ((1 / 2 : ℝ) ^ m) := by
      rw [← powT_add hsp hq hq]
      congr 1
      rw [pow_succ]
      ring
    have e1 : CFC.sqrt (powT a ((1 / 2 : ℝ) ^ m)) = b (m + 1) :=
      CFC.sqrt_unique (by rw [hsq m, ih]) (hpos (m + 1))
    have e2 : CFC.sqrt (powT a ((1 / 2 : ℝ) ^ m)) = powT a ((1 / 2 : ℝ) ^ (m + 1)) :=
      CFC.sqrt_unique hhalf (powT_nonneg hsp _)
    rw [← e1, e2]

#print axioms eq_powT_of_sq

end Powers

/-! ## 3. The flowed reconstruction on one space -/

section Flow

variable {N : ℕ}

/-- **The one reconstructed Hilbert space** of the flowed transfers: every step has the reflection
form of step `0` (`flowTransfer` changes only the step).

DERIVED: `0` is the step whose form names the space; `4` in `Fin 4` is the spacetime dimension. -/
abbrev FlowH (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving τ r) : Type :=
  GNSHilbert.H (flowTransfer hN Φ hB τ hpos 0).toReflForm

/-- The reflection form is the same at every step.

DERIVED: `0` is the reference step; `4` in `Fin 4` is the spacetime dimension. -/
theorem toReflForm_flowTransfer (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hpos : Φ.PosPreserving τ r) (m : ℕ) :
    (flowTransfer hN Φ hB τ hpos m).toReflForm = (flowTransfer hN Φ hB τ hpos 0).toReflForm := rfl

#print axioms toReflForm_flowTransfer

/-- **The step-`m` transfer on the one space**: the time translation by `dySpacing N m`.

DERIVED: no numeral of its own; `4` in `Fin 4` is the spacetime dimension. -/
def stepT (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving τ r) (m : ℕ) :
    FlowH hN Φ hB τ hpos →L[ℂ] FlowH hN Φ hB τ hpos :=
  GNSHilbert.opT (flowTransfer hN Φ hB τ hpos m)

/-- **The one vacuum**: the vacuum of every step.

DERIVED: `0` is the reference step; `4` in `Fin 4` is the spacetime dimension. -/
def vacT (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpos : Φ.PosPreserving τ r) : FlowH hN Φ hB τ hpos :=
  GNSHilbert.Omega (flowTransfer hN Φ hB τ hpos 0).toReflForm (flowTransfer hN Φ hB τ hpos 0).vac

variable (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
  (hpos : Φ.PosPreserving τ r)

/-- `stepT` on a pre-Hilbert vector: the step applied to both components.

DERIVED: `0` is the reference step; `4` in `Fin 4` is the spacetime dimension. -/
theorem stepT_coe (m : ℕ) (z : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm) :
    stepT hN Φ hB τ hpos m (z : FlowH hN Φ hB τ hpos)
      = ((GNSHilbert.Pre.ofPair (flowTransfer hN Φ hB τ hpos 0).toReflForm
          ((flowTransfer hN Φ hB τ hpos m).T (z : _ × _).1)
          ((flowTransfer hN Φ hB τ hpos m).T (z : _ × _).2)
          : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm) : FlowH hN Φ hB τ hpos) :=
  GNSHilbert.opT_coe (flowTransfer hN Φ hB τ hpos m) z

#print axioms stepT_coe

/-- **Two half steps are one step** on the one space: `stepT (m+1)² = stepT m` (`gT_half` on the
pre-Hilbert space, then density).

DERIVED: `1` is the half-step offset; `4` in `Fin 4` is the spacetime dimension. -/
theorem stepT_sq (m : ℕ) :
    stepT hN Φ hB τ hpos (m + 1) * stepT hN Φ hB τ hpos (m + 1) = stepT hN Φ hB τ hpos m := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (stepT hN Φ hB τ hpos (m + 1) * stepT hN Φ hB τ hpos (m + 1)).continuous
      (stepT hN Φ hB τ hpos m).continuous) (fun z => ?_)
  rw [ContinuousLinearMap.mul_apply, stepT_coe, stepT_coe, stepT_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show (flowTransfer hN Φ hB τ hpos (m + 1)).T ((flowTransfer hN Φ hB τ hpos (m + 1)).T _)
      = (flowTransfer hN Φ hB τ hpos m).T _
    exact (gT_half _ _ (fun P => MarginMono.shift_half hN τ m P) _).symm
  · show (flowTransfer hN Φ hB τ hpos (m + 1)).T ((flowTransfer hN Φ hB τ hpos (m + 1)).T _)
      = (flowTransfer hN Φ hB τ hpos m).T _
    exact (gT_half _ _ (fun P => MarginMono.shift_half hN τ m P) _).symm

#print axioms stepT_sq

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem isSelfAdjoint_stepT (m : ℕ) : IsSelfAdjoint (stepT hN Φ hB τ hpos m) :=
  GNSHilbert.isSelfAdjoint_opT _

#print axioms isSelfAdjoint_stepT

/-- **Every step is positive** (`flowTransfer_positive`).

DERIVED: `0` is the order's bottom; `4` in `Fin 4` is the spacetime dimension. -/
theorem stepT_nonneg (m : ℕ) : 0 ≤ stepT hN Φ hB τ hpos m :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (GNSHilbert.isPositive_opT _ (flowTransfer_positive hN Φ hB τ hpos m))

#print axioms stepT_nonneg

/-- DERIVED: `0` and `1` bound the spectrum (`flow_reconstruction`); `4` in `Fin 4` is the spacetime
dimension. -/
theorem spectrum_stepT (m : ℕ) : spectrum ℝ (stepT hN Φ hB τ hpos m) ⊆ Set.Icc 0 1 :=
  (flow_reconstruction hN Φ hB τ hpos m).1.2.2.2.2

#print axioms spectrum_stepT

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem stepT_vacT (m : ℕ) : stepT hN Φ hB τ hpos m (vacT hN Φ hB τ hpos) = vacT hN Φ hB τ hpos :=
  GNSHilbert.opT_Omega (flowTransfer hN Φ hB τ hpos m)

#print axioms stepT_vacT

/-- **The steps are the dyadic roots of step `0`**: `stepT m = (stepT 0) ^ (1/2)^m`.

DERIVED: `1/2` is the dyadic ratio; `0` the reference step; `4` in `Fin 4` is the spacetime
dimension. -/
theorem stepT_eq_powT (m : ℕ) :
    stepT hN Φ hB τ hpos m = powT (stepT hN Φ hB τ hpos 0) ((1 / 2 : ℝ) ^ m) :=
  eq_powT_of_sq (isSelfAdjoint_stepT hN Φ hB τ hpos 0) (spectrum_stepT hN Φ hB τ hpos 0)
    (stepT hN Φ hB τ hpos) rfl (stepT_nonneg hN Φ hB τ hpos) (stepT_sq hN Φ hB τ hpos) m

#print axioms stepT_eq_powT

/-- **The steps commute.**

DERIVED: `1/2` the dyadic ratio; `4` in `Fin 4` is the spacetime dimension. -/
theorem stepT_commute (m m' : ℕ) :
    Commute (stepT hN Φ hB τ hpos m) (stepT hN Φ hB τ hpos m') := by
  rw [stepT_eq_powT hN Φ hB τ hpos m, stepT_eq_powT hN Φ hB τ hpos m']
  unfold powT
  exact cfc_commute_cfc (R := ℝ) (fun x : ℝ => x ^ ((1 / 2 : ℝ) ^ m))
    (fun x : ℝ => x ^ ((1 / 2 : ℝ) ^ m')) (stepT hN Φ hB τ hpos 0)

#print axioms stepT_commute

/-! ### The kernel of step `0` is trivial -/

/-- The reconstructed vector of a margin monomial.

DERIVED: `1` is the coefficient; `0` the imaginary part and the reference step; `4` in `Fin 4` is the
spacetime dimension. -/
def gvecT (Q : MarginMono N τ r) : FlowH hN Φ hB τ hpos :=
  ((GNSHilbert.Pre.ofPair (flowTransfer hN Φ hB τ hpos 0).toReflForm (Finsupp.single Q 1) 0
    : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm) : FlowH hN Φ hB τ hpos)

/-- **The step moves a monomial forward**: `stepT m (gvec Q) = gvec (shift_m Q)`.

DERIVED: `1` is the coefficient; `0` the imaginary part; `4` in `Fin 4` is the spacetime
dimension. -/
theorem stepT_gvecT (m : ℕ) (Q : MarginMono N τ r) :
    stepT hN Φ hB τ hpos m (gvecT hN Φ hB τ hpos Q)
      = gvecT hN Φ hB τ hpos (MarginMono.shift hN τ m Q) := by
  unfold gvecT
  rw [stepT_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · show Finsupp.mapDomain (MarginMono.shift hN τ m) (Finsupp.single Q 1)
      = Finsupp.single (MarginMono.shift hN τ m Q) 1
    exact Finsupp.mapDomain_single
  · show (flowTransfer hN Φ hB τ hpos m).T 0 = 0
    exact map_zero _

#print axioms stepT_gvecT

/-- **Every margin monomial is one step forward of a margin monomial**, at a step finer than its
margin: if every factor vanishes below `d > max r 0`, take `a_m < min d (d − r)` and the monomial
shifted back by `a_m`.

DERIVED: `0` is the sign of the margin; `1` is the unit step and its inverse `-1`; `4` in `Fin 4` is
the spacetime dimension. -/
theorem exists_shift_preimage (Q : MarginMono N τ r) :
    ∃ (m : ℕ) (Q' : MarginMono N τ r), MarginMono.shift hN τ m Q' = Q := by
  obtain ⟨P1, d, hd, hrd, hP⟩ := Q
  obtain ⟨m, hm⟩ := ((tendsto_dySpacing N).eventually
    (gt_mem_nhds (lt_min hd (sub_pos.mpr hrd)))).exists
  have hm1 : dySpacing N m < d := lt_of_lt_of_le hm (min_le_left _ _)
  have hm2 : dySpacing N m < d - r := lt_of_lt_of_le hm (min_le_right _ _)
  refine ⟨m, ⟨Mono.shift (timeVec N m τ (-1)) P1, d - dySpacing N m, by linarith, by linarith,
    fun i y hy => ?_⟩, ?_⟩
  · have h1 := hP i (y - timeVec N m τ (-1)) hy
    have h2 : (y - timeVec N m τ (-1)) τ = y τ - timeVec N m τ (-1) τ := rfl
    rw [h2, timeVec_self] at h1
    push_cast at h1
    linarith
  · apply Subtype.ext
    show Mono.shift (timeVec N m τ 1) (Mono.shift (timeVec N m τ (-1)) P1) = P1
    rw [Mono.shift_shift, timeVec_add, neg_add_cancel, timeVec_zero, Mono.shift_zero]

#print axioms exists_shift_preimage

/-- A vector killed by step `m` is killed by step `m + 1`: `‖T x‖² = ⟪x, T² x⟫`.

DERIVED: `0` is the zero vector; `1` the half-step offset; `4` in `Fin 4` is the spacetime
dimension. -/
theorem stepT_succ_eq_zero {m : ℕ} {x : FlowH hN Φ hB τ hpos}
    (hx : stepT hN Φ hB τ hpos m x = 0) : stepT hN Φ hB τ hpos (m + 1) x = 0 := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_stepT hN Φ hB τ hpos (m + 1))
  have h1 : stepT hN Φ hB τ hpos (m + 1) (stepT hN Φ hB τ hpos (m + 1) x) = 0 := by
    rw [← ContinuousLinearMap.mul_apply, stepT_sq, hx]
  have h2 : inner ℂ (stepT hN Φ hB τ hpos (m + 1) x) (stepT hN Φ hB τ hpos (m + 1) x) = 0 := by
    have := hsym x (stepT hN Φ hB τ hpos (m + 1) x)
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h2

#print axioms stepT_succ_eq_zero

/-- **Orthogonal to the monomials is orthogonal to the pre-Hilbert space**: a vector orthogonal to
every `gvecT Q` is orthogonal to the class of every pair of finite combinations.

DERIVED: `0` is the zero combination and the imaginary part; `1` the coefficient; `4` in `Fin 4` is
the spacetime dimension. -/
theorem inner_pre_eq_zero (x : FlowH hN Φ hB τ hpos)
    (horth : ∀ Q : MarginMono N τ r, inner ℂ x (gvecT hN Φ hB τ hpos Q) = 0)
    (z : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm) :
    inner ℂ x (z : FlowH hN Φ hB τ hpos) = 0 := by
  have hlin : ∀ c : MarginMono N τ r →₀ ℝ,
      inner ℂ x ((GNSHilbert.Pre.ofPair (flowTransfer hN Φ hB τ hpos 0).toReflForm c 0
        : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm) : FlowH hN Φ hB τ hpos) = 0 := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero =>
      have h0 : (GNSHilbert.Pre.ofPair (flowTransfer hN Φ hB τ hpos 0).toReflForm
          (0 : MarginMono N τ r →₀ ℝ) 0
          : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm) = 0 :=
        GNSHilbert.Pre.ext rfl rfl
      rw [h0, UniformSpace.Completion.coe_zero, inner_zero_right]
    | add f g hf hg =>
      have h0 : (GNSHilbert.Pre.ofPair (flowTransfer hN Φ hB τ hpos 0).toReflForm (f + g) 0
          : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm)
          = GNSHilbert.Pre.ofPair _ f 0 + GNSHilbert.Pre.ofPair _ g 0 :=
        GNSHilbert.Pre.ext rfl
          (show (0 : MarginMono N τ r →₀ ℝ) = 0 + 0 from (add_zero 0).symm)
      rw [h0, UniformSpace.Completion.coe_add, inner_add_right, hf, hg, add_zero]
    | single Q b =>
      have h0 : (GNSHilbert.Pre.ofPair (flowTransfer hN Φ hB τ hpos 0).toReflForm
          (Finsupp.single Q b) 0 : GNSHilbert.Pre (flowTransfer hN Φ hB τ hpos 0).toReflForm)
          = (b : ℂ) • GNSHilbert.Pre.ofPair _ (Finsupp.single Q 1) 0 := by
        refine GNSHilbert.Pre.ext ?_ ?_
        · show Finsupp.single Q b
            = (b : ℂ).re • Finsupp.single Q (1 : ℝ) + (-(b : ℂ).im) • (0 : MarginMono N τ r →₀ ℝ)
          simp only [Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_smul, add_zero,
            Finsupp.smul_single, smul_eq_mul, mul_one]
        · show (0 : MarginMono N τ r →₀ ℝ)
            = (b : ℂ).re • (0 : MarginMono N τ r →₀ ℝ) + (b : ℂ).im • Finsupp.single Q (1 : ℝ)
          simp only [Complex.ofReal_im, zero_smul, smul_zero, add_zero]
      rw [h0, UniformSpace.Completion.coe_smul, inner_smul_right]
      exact mul_eq_zero_of_right _ (horth Q)
  have hz : z = GNSHilbert.Pre.ofPair _ (z : _ × _).1 0
      + Complex.I • GNSHilbert.Pre.ofPair _ (z : _ × _).2 0 := by
    refine GNSHilbert.Pre.ext ?_ ?_
    · show (z : _ × _).1 = (z : _ × _).1 + (Complex.I.re • (z : _ × _).2
        + (-Complex.I.im) • (0 : MarginMono N τ r →₀ ℝ))
      simp only [Complex.I_re, Complex.I_im, zero_smul, smul_zero, add_zero]
    · show (z : _ × _).2 = (0 : MarginMono N τ r →₀ ℝ) + (Complex.I.re • (0 : MarginMono N τ r →₀ ℝ)
        + Complex.I.im • (z : _ × _).2)
      simp only [Complex.I_re, Complex.I_im, zero_smul, smul_zero, one_smul, zero_add]
  rw [hz, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul, inner_add_right,
    inner_smul_right, hlin, hlin, mul_zero, add_zero]

#print axioms inner_pre_eq_zero

/-- **Step `0` has trivial kernel.** A vector killed by step `0` is killed by every step
(`stepT_succ_eq_zero`), hence orthogonal to every reconstructed monomial (`exists_shift_preimage`,
`stepT_gvecT`), hence to every pre-Hilbert vector (`inner_pre_eq_zero`), which are dense.

DERIVED: `0` is the reference step and the zero vector; `4` in `Fin 4` is the spacetime dimension. -/
theorem stepT_zero_injective (x : FlowH hN Φ hB τ hpos) (hx : stepT hN Φ hB τ hpos 0 x = 0) :
    x = 0 := by
  have hall : ∀ m, stepT hN Φ hB τ hpos m x = 0 := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih => exact stepT_succ_eq_zero hN Φ hB τ hpos ih
  have horth : ∀ Q : MarginMono N τ r, inner ℂ x (gvecT hN Φ hB τ hpos Q) = 0 := by
    intro Q
    obtain ⟨m, Q', hQ'⟩ := exists_shift_preimage hN τ Q
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_stepT hN Φ hB τ hpos m)
    rw [← hQ', ← stepT_gvecT]
    have := hsym x (gvecT hN Φ hB τ hpos Q')
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hall m, inner_zero_left]
  have hall' : ∀ y : FlowH hN Φ hB τ hpos, inner ℂ x y = 0 := fun y =>
    UniformSpace.Completion.induction_on y
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
      (inner_pre_eq_zero hN Φ hB τ hpos x horth)
  exact inner_self_eq_zero.mp (hall' x)

#print axioms stepT_zero_injective

/-! ### The time translations -/

/-- **The time translation by `t`**: `(stepT 0) ^ (t / a_0)`, `a_0 = dySpacing N 0`.

DERIVED: `0` is the reference step; `4` in `Fin 4` is the spacetime dimension. -/
def timeT (t : ℝ) : FlowH hN Φ hB τ hpos →L[ℂ] FlowH hN Φ hB τ hpos :=
  powT (stepT hN Φ hB τ hpos 0) (t / dySpacing N 0)

/-- `a_m = a_0 (1/2)^m`.

DERIVED: `0` is the reference step; `1/2` the dyadic ratio; `2` the refinement factor. -/
theorem dySpacing_eq_mul (N m : ℕ) : dySpacing N m = dySpacing N 0 * (1 / 2 : ℝ) ^ m := by
  have h := dySpacing_mul_pow N (Nat.zero_le m)
  rw [Nat.sub_zero] at h
  rw [← h, mul_assoc, ← mul_pow]
  norm_num

#print axioms dySpacing_eq_mul

/-- **The time translations agree with the dyadic steps**: `timeT (n a_m) = stepT m ^ n`.

DERIVED: `0` is the reference step; `1/2` the dyadic ratio; `4` in `Fin 4` is the spacetime
dimension. -/
theorem timeT_dyadic (m n : ℕ) :
    timeT hN Φ hB τ hpos (n * dySpacing N m) = stepT hN Φ hB τ hpos m ^ n := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  unfold timeT
  rw [dySpacing_eq_mul N m, stepT_eq_powT hN Φ hB τ hpos m,
    ← powT_nat_mul (isSelfAdjoint_stepT hN Φ hB τ hpos 0) (spectrum_stepT hN Φ hB τ hpos 0)
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m) n]
  congr 1
  field_simp

#print axioms timeT_dyadic

/-- DERIVED: `0` is the time origin; `1` the identity. -/
theorem timeT_zero : timeT hN Φ hB τ hpos 0 = 1 := by
  unfold timeT
  rw [zero_div, powT_zero (isSelfAdjoint_stepT hN Φ hB τ hpos 0)]

#print axioms timeT_zero

/-- **The semigroup law** `T(s + t) = T(s) T(t)`, `s, t ≥ 0`.

DERIVED: `0` is the sign of the times and the reference step. -/
theorem timeT_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    timeT hN Φ hB τ hpos (s + t) = timeT hN Φ hB τ hpos s * timeT hN Φ hB τ hpos t := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  unfold timeT
  rw [add_div, powT_add (spectrum_stepT hN Φ hB τ hpos 0) (div_nonneg hs ha0.le)
    (div_nonneg ht ha0.le)]

#print axioms timeT_add

/-- **Positive self-adjoint contractions.**

DERIVED: `0` is the order's bottom and the sign of `t`; `1` the norm bound. -/
theorem timeT_nonneg_norm (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ timeT hN Φ hB τ hpos t ∧ IsSelfAdjoint (timeT hN Φ hB τ hpos t)
      ∧ ‖timeT hN Φ hB τ hpos t‖ ≤ 1 :=
  ⟨powT_nonneg (spectrum_stepT hN Φ hB τ hpos 0) _, isSelfAdjoint_powT _,
    norm_powT_le_one (spectrum_stepT hN Φ hB τ hpos 0)
      (div_nonneg ht (dySpacing_pos (one_le_of_ne_zero hN) 0).le)⟩

#print axioms timeT_nonneg_norm

/-- **Strong continuity on `[0, ∞)`** (`continuousOn_powT_apply` with `stepT_zero_injective`).

DERIVED: `0` is the time origin and the reference step. -/
theorem continuousOn_timeT (y : FlowH hN Φ hB τ hpos) :
    ContinuousOn (fun t => timeT hN Φ hB τ hpos t y) (Set.Ici 0) := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  have hc := continuousOn_powT_apply (isSelfAdjoint_stepT hN Φ hB τ hpos 0)
    (spectrum_stepT hN Φ hB τ hpos 0) (stepT_zero_injective hN Φ hB τ hpos) y
  have hd : ContinuousOn (fun t : ℝ => t / dySpacing N 0) (Set.Ici 0) :=
    (continuous_id.div_const _).continuousOn
  exact hc.comp hd (fun t ht => div_nonneg ht ha0.le)

#print axioms continuousOn_timeT

/-- **The vacuum is invariant at every time.**

DERIVED: `0` is the sign of `t` and the reference step; `1/2` the dyadic ratio. -/
theorem timeT_vacT {t : ℝ} (ht : 0 ≤ t) :
    timeT hN Φ hB τ hpos t (vacT hN Φ hB τ hpos) = vacT hN Φ hB τ hpos := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  refine powT_apply_fixed (isSelfAdjoint_stepT hN Φ hB τ hpos 0)
    (spectrum_stepT hN Φ hB τ hpos 0) (fun m n => ?_) (div_nonneg ht ha0.le)
  rw [powT_nat_mul (isSelfAdjoint_stepT hN Φ hB τ hpos 0) (spectrum_stepT hN Φ hB τ hpos 0)
    (by positivity) n, ← stepT_eq_powT]
  induction n with
  | zero => rw [pow_zero, ContinuousLinearMap.one_apply]
  | succ n ih => rw [pow_succ, ContinuousLinearMap.mul_apply, stepT_vacT, ih]

#print axioms timeT_vacT

/-- **The dyadic gaps give the gap at every time.** If at every step the reconstructed transfer is
`GappedAt` the rate `e^{−μ a_m}`, `μ ≥ 0` independent of `m`, then at every `t ≥ 0` the time
translation contracts the vacuum complement by `e^{−μ t}` and its spectrum lies in
`{1} ∪ [0, e^{−μ t}]`.

DERIVED: `0` is the sign of `μ` and `t`, the vanishing vacuum pairing and the reference step; `1` is
the vacuum eigenvalue; `1/2` the dyadic ratio; `4` in `Fin 4` is the spacetime dimension. -/
theorem timeT_gap {μ : ℝ} (hμ : 0 ≤ μ)
    (hgap : ∀ m : ℕ, ContinuumClay.GappedAt (flowTransfer hN Φ hB τ hpos m)
      (Real.exp (-μ * dySpacing N m))) {t : ℝ} (ht : 0 ≤ t) :
    (∀ u : FlowH hN Φ hB τ hpos, inner ℂ (vacT hN Φ hB τ hpos) u = 0 →
        ‖timeT hN Φ hB τ hpos t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
      ∧ spectrum ℝ (timeT hN Φ hB τ hpos t) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(μ * t))) := by
  have ha0 := dySpacing_pos (one_le_of_ne_zero hN) 0
  have hsa := isSelfAdjoint_stepT hN Φ hB τ hpos 0
  have hsp := spectrum_stepT hN Φ hB τ hpos 0
  have htime : μ * dySpacing N 0 * (t / dySpacing N 0) = μ * t := by field_simp
  refine ⟨fun u hu => ?_, ?_⟩
  · -- the dyadic bound
    have hd : ∀ m n : ℕ, ‖powT (stepT hN Φ hB τ hpos 0) (n * (1 / 2 : ℝ) ^ m) u‖
        ≤ Real.exp (-(μ * dySpacing N 0 * (n * (1 / 2 : ℝ) ^ m))) * ‖u‖ := by
      intro m n
      rw [powT_nat_mul hsa hsp (by positivity) n, ← stepT_eq_powT]
      have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (isSelfAdjoint_stepT hN Φ hB τ hpos m)
      have hstep : ∀ v : FlowH hN Φ hB τ hpos, inner ℂ (vacT hN Φ hB τ hpos) v = 0 →
          ‖stepT hN Φ hB τ hpos m v‖ ≤ Real.exp (-μ * dySpacing N m) * ‖v‖ :=
        fun v hv => (hgap m).2.2.2.1 v hv
      have hinv : ∀ v : FlowH hN Φ hB τ hpos, inner ℂ (vacT hN Φ hB τ hpos) v = 0 →
          inner ℂ (vacT hN Φ hB τ hpos) (stepT hN Φ hB τ hpos m v) = 0 := by
        intro v hv
        have := hsym (vacT hN Φ hB τ hpos) v
        simp only [ContinuousLinearMap.coe_coe] at this
        rw [← this, stepT_vacT, hv]
      have hpow : ∀ k : ℕ, inner ℂ (vacT hN Φ hB τ hpos) ((stepT hN Φ hB τ hpos m ^ k) u) = 0
          ∧ ‖(stepT hN Φ hB τ hpos m ^ k) u‖ ≤ Real.exp (-μ * dySpacing N m) ^ k * ‖u‖ := by
        intro k
        induction k with
        | zero =>
          rw [pow_zero, ContinuousLinearMap.one_apply, pow_zero, one_mul]
          exact ⟨hu, le_rfl⟩
        | succ k ih =>
          rw [pow_succ', ContinuousLinearMap.mul_apply]
          refine ⟨hinv _ ih.1, (hstep _ ih.1).trans ?_⟩
          rw [pow_succ', mul_assoc]
          exact mul_le_mul_of_nonneg_left ih.2 (Real.exp_pos _).le
      refine (hpow n).2.trans (le_of_eq ?_)
      rw [← Real.exp_nat_mul, dySpacing_eq_mul N m]
      congr 2
      ring
    have h := norm_powT_apply_le hsa hsp (mul_nonneg hμ ha0.le) hd (div_nonneg ht ha0.le)
    rw [htime] at h
    exact h
  · have hgap0 : spectrum ℝ (stepT hN Φ hB τ hpos 0)
        ⊆ {1} ∪ Set.Icc 0 (Real.exp (-μ * dySpacing N 0)) := (hgap 0).2.2.2.2.1
    have h := spectrum_powT_subset hsa hsp hgap0 (div_nonneg ht ha0.le)
    rw [← Real.exp_mul] at h
    have e : -μ * dySpacing N 0 * (t / dySpacing N 0) = -(μ * t) := by field_simp
    rw [e] at h
    exact h

#print axioms timeT_gap

/-- **The continuous-time picture at rate `μ`** on the one reconstructed space: the time translations
`timeT t`, `t ≥ 0`, form a strongly continuous semigroup of positive self-adjoint contractions,
`timeT 0 = 1`, agreeing with the dyadic steps, fixing the vacuum, contracting its complement by
`e^{−μ t}`, with spectrum in `{1} ∪ [0, e^{−μ t}]`.

DERIVED: `0` the time origin, the sign of `t`, `s`, the vanishing pairing; `1` the identity, the
vacuum eigenvalue and the norm bound; `4` in `Fin 4` is the spacetime dimension. -/
def TimeGroupAt (μ : ℝ) : Prop :=
  timeT hN Φ hB τ hpos 0 = 1
    ∧ (∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        timeT hN Φ hB τ hpos (s + t) = timeT hN Φ hB τ hpos s * timeT hN Φ hB τ hpos t)
    ∧ (∀ m n : ℕ, timeT hN Φ hB τ hpos (n * dySpacing N m) = stepT hN Φ hB τ hpos m ^ n)
    ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ timeT hN Φ hB τ hpos t ∧ IsSelfAdjoint (timeT hN Φ hB τ hpos t)
        ∧ ‖timeT hN Φ hB τ hpos t‖ ≤ 1)
    ∧ (∀ y : FlowH hN Φ hB τ hpos, ContinuousOn (fun t => timeT hN Φ hB τ hpos t y) (Set.Ici 0))
    ∧ (∀ t : ℝ, 0 ≤ t → timeT hN Φ hB τ hpos t (vacT hN Φ hB τ hpos) = vacT hN Φ hB τ hpos)
    ∧ (∀ t : ℝ, 0 ≤ t → ∀ u : FlowH hN Φ hB τ hpos, inner ℂ (vacT hN Φ hB τ hpos) u = 0 →
        ‖timeT hN Φ hB τ hpos t u‖ ≤ Real.exp (-(μ * t)) * ‖u‖)
    ∧ (∀ t : ℝ, 0 ≤ t →
        spectrum ℝ (timeT hN Φ hB τ hpos t) ⊆ {1} ∪ Set.Icc 0 (Real.exp (-(μ * t))))

/-- **The continuous-time picture of the flowed reconstruction.** Under the dyadic gaps at a rate
`μ ≥ 0` independent of the step: on the one reconstructed Hilbert space, the time translations
`timeT t`, `t ≥ 0`, form a strongly continuous semigroup of positive self-adjoint contractions,
`timeT 0 = 1`, agreeing with the dyadic steps, fixing the vacuum, contracting its complement by
`e^{−μ t}`, with spectrum in `{1} ∪ [0, e^{−μ t}]`.

DERIVED: `0` the time origin, the sign of `μ`, `t`, `s`, the vanishing pairing; `1` the identity, the
vacuum eigenvalue and the norm bound; `4` in `Fin 4` is the spacetime dimension. -/
theorem flow_time_group {μ : ℝ} (hμ : 0 ≤ μ)
    (hgap : ∀ m : ℕ, ContinuumClay.GappedAt (flowTransfer hN Φ hB τ hpos m)
      (Real.exp (-μ * dySpacing N m))) : TimeGroupAt hN Φ hB τ hpos μ :=
  ⟨timeT_zero hN Φ hB τ hpos, fun _ _ hs ht => timeT_add hN Φ hB τ hpos hs ht,
    timeT_dyadic hN Φ hB τ hpos, timeT_nonneg_norm hN Φ hB τ hpos,
    continuousOn_timeT hN Φ hB τ hpos, fun _ ht => timeT_vacT hN Φ hB τ hpos ht,
    fun _ ht => (timeT_gap hN Φ hB τ hpos hμ hgap ht).1,
    fun _ ht => (timeT_gap hN Φ hB τ hpos hμ hgap ht).2⟩

#print axioms flow_time_group

end Flow

/-! ## 4. The observer's energy-density transfer -/

section Observer

variable {N : ℕ}

/-- **The continuous-time capstone for any flow**: `ObserverEnergyReductionsN.flowN_clay_of_gap`'s
inputs (the uniform bound, a physical range bound, the transfer at one step gapped, the pairing N)
give a rate `μ > 0` and the continuous-time picture of `flow_time_group` at that rate on the one
reconstructed space, together with a non-zero vector orthogonal to the vacuum.

DERIVED: `0` is the sign of `μ`, `L`, `ρ` and the reference step; `1` the top of `ρ`; `4` in `Fin 4`
is the spacetime dimension. -/
theorem flowN_time_group_of_gap (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r : ℝ} (hphys : Φ.PhysRange r) (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN Φ τ r) :
    ∃ μ : ℝ, 0 < μ
      ∧ TimeGroupAt hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hphys τ) μ
      ∧ ContinuumClay.NontrivialVacuum
          (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys 0) := by
  obtain ⟨c', hc', h⟩ :=
    ObserverEnergyReductionsN.flowN_clay_of_gap hN Φ hB τ hphys m0 hL hρ0 hρ1 hg hNT
  refine ⟨c' / L, div_pos hc' hL, ?_⟩
  have hgap : ∀ m : ℕ, ContinuumClay.GappedAt
      (flowTransfer hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hphys τ) m)
      (Real.exp (-(c' / L) * dySpacing N m)) := fun m => (h m).1
  exact ⟨flow_time_group hN Φ hB τ (Flow.posPreserving_of_physRange hN Φ hphys τ)
    (div_pos hc' hL).le hgap, (h 0).2⟩

#print axioms flowN_time_group_of_gap

/-- **The energy density's continuous-time capstone**: `ObserverEnergyReductionsN.energyN_clay_of_gap`'s
inputs (E: smeared moments on `D`; a physical range bound; M: the transfer at one step gapped; N: the
pairing), for every `N ≠ 0` and every `W : ConfFlow N`, give a rate `μ > 0` and the continuous-time
picture `TimeGroupAt` for the class-scaled energy density, with a non-zero vector orthogonal to the
vacuum.

DERIVED: `2` makes the power even; `0` the sign of `μ`, `L`, `ρ` and the reference step; `1` the top of
`ρ`; `4` in `Fin 4` is the spacetime dimension. -/
theorem energyN_time_group_of_gap (hN : N ≠ 0) (W : ConfFlow N)
    (D : Set (LField (MassGap.SUN.SU N)))
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (s : ℕ → LField (MassGap.SUN.SU N) → ℝ)
    (hs : ∀ (k : ℕ) (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), s k (O.refl τ) = s k O)
    (hM : ∀ O ∈ D, ∀ (f : TestFn) (p : ℕ), ∃ C : ℝ, ∀ᶠ k in atTop,
      stateK hN k (smear (dySpacing N k)
        ((ObserverEnergyMoments.energyOn W D hD s hs).map k O).1 f ^ (2 * p)) ≤ C)
    (τ : Fin 4) {r : ℝ} (hphys : (ObserverEnergyMoments.energyOn W D hD s hs).PhysRange r)
    (m0 : ℕ) {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt
      (ObserverEnergyReductionsN.transferN hN (ObserverEnergyMoments.energyOn W D hD s hs)
        (ObserverEnergyReductionsN.energyBoundN hN W D hD s hs hM) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (ObserverEnergyMoments.energyOn W D hD s hs) τ r) :
    ∃ μ : ℝ, 0 < μ
      ∧ TimeGroupAt hN (ObserverEnergyMoments.energyOn W D hD s hs)
          (ObserverEnergyReductionsN.energyBoundN hN W D hD s hs hM) τ
          (Flow.posPreserving_of_physRange hN _ hphys τ) μ
      ∧ ContinuumClay.NontrivialVacuum
          (ObserverEnergyReductionsN.transferN hN (ObserverEnergyMoments.energyOn W D hD s hs)
            (ObserverEnergyReductionsN.energyBoundN hN W D hD s hs hM) τ hphys 0) :=
  flowN_time_group_of_gap hN _ (ObserverEnergyReductionsN.energyBoundN hN W D hD s hs hM) τ hphys m0
    hL hρ0 hρ1 hg hNT

#print axioms energyN_time_group_of_gap

end Observer

end MassGap.ContinuumTimeGroup
