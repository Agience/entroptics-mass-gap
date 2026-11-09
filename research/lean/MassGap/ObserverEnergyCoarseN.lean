import Mathlib
import MassGap.ObserverEnergyBox

noncomputable section

/-!
# MassGap.ObserverEnergyCoarseN — E and N for the energy density through the coarse view

This module treats E for the energy density through the observer's coarse view, at the fine spacing
`a_k`.

1. **State calculus** (`state_mul_sq_le`, `state_sq_le`): Cauchy–Schwarz for a state, and the bound
   `ν(F²) ≤ B²` from a pointwise bound `|F| ≤ B`.
2. **E through the coarse view and per-step control** (`sum_abs_pow_le`, `state_pow_sum_le`,
   `cubeMomentBound_of_coarseSteps`): if the cube energy at step `k` is a bounded reading `G_c ∘ χ_k`
   of the coarse view plus a sum of per-step increments `Δ_{k,j}` (the steps between the coarse scale
   and `a_k`) whose `2q+2`-th moments are `≤ D w_j^{2q+2}` with `Σ w < ∞`, uniformly in `k`, then
   `CubeMomentBound` holds. The coarse part is bounded outright; Dobrushin's condition is not used.
3. **The coarse pairing** (`coarsePair`): the connected pairing of the coarse readings `G`, `Gθ`
   along the coarse maps `χ_k` at step `k`.

## Scope

E is reduced to a statement about the part of the fine-spacing energy that the coarse view does not
carry (`Δ`): it is small in moments, uniformly in the spacing. That part is not a function of the
coarse view.
-/

namespace MassGap.ObserverEnergyCoarseN

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.FlowCapstone MassGap.ObserverFlow MassGap.ObserverClay
    MassGap.ObserverEnergyBox
   Filter
open scoped Topology

/-! ## 1. State calculus -/

section StateCalc

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

/-- **Cauchy–Schwarz for a state**: `ν(f g)² ≤ ν(f²) ν(g²)`, from `ν((f − s g)²) ≥ 0` for every `s`.

DERIVED: `2` the square and the cross term; `1` the step `s = (A + 1)/(2B)` in the degenerate case;
`0` the signs. -/
theorem state_mul_sq_le (ν : MassGap.DLRLimit.State X) (f g : C(X, ℝ)) :
    ν (f * g) ^ 2 ≤ ν (f * f) * ν (g * g) := by
  have hq : ∀ s : ℝ, 0 ≤ ν (f * f) - 2 * s * ν (f * g) + s ^ 2 * ν (g * g) := by
    intro s
    have h0 := ν.nonneg ((f - s • g) * (f - s • g)) (fun x => mul_self_nonneg _)
    have e : (f - s • g) * (f - s • g) = f * f - (2 * s) • (f * g) + (s ^ 2) • (g * g) := by
      ext x
      simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.add_apply, smul_eq_mul]
      ring
    rw [e, ν.map_add, ν.map_sub, ν.map_smul, ν.map_smul] at h0
    linarith
  set A := ν (f * f)
  set B := ν (f * g)
  set D := ν (g * g)
  have hD : 0 ≤ D := ν.nonneg _ (fun x => mul_self_nonneg _)
  rcases hD.eq_or_lt with h0 | hpos
  · have hB : B = 0 := by
      by_contra hB
      have h1 := hq ((A + 1) / (2 * B))
      have e : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by field_simp
      rw [e, ← h0, mul_zero, add_zero] at h1
      linarith
    rw [hB, ← h0]
    simp
  · have h1 := hq (B / D)
    have e1 : 2 * (B / D) * B = 2 * (B ^ 2 / D) := by ring
    have e2 : (B / D) ^ 2 * D = B ^ 2 / D := by field_simp
    rw [e1, e2] at h1
    have h2 : B ^ 2 / D ≤ A := by linarith
    rw [div_le_iff₀ hpos] at h2
    linarith

#print axioms state_mul_sq_le

/-- A pointwise bound on an observable bounds the value of its square.

DERIVED: `2` the square; `1` the unit observable; `0` the sign. -/
theorem state_sq_le (ν : MassGap.DLRLimit.State X) {F : C(X, ℝ)} {B : ℝ} (h : ∀ x, |F x| ≤ B) :
    ν (F * F) ≤ B ^ 2 := by
  have h1 : ν (F * F) ≤ ν (B ^ 2 • (1 : C(X, ℝ))) := ν.mono fun x => by
    simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
    have := pow_le_pow_left₀ (abs_nonneg (F x)) (h x) 2
    rw [sq_abs] at this
    nlinarith [this]
  rwa [ν.map_smul, ν.map_one, mul_one] at h1

#print axioms state_sq_le

end StateCalc

/-! ## 2. E through the coarse view and per-step control -/

section E

/-- **A weighted power-mean bound**: for weights `w > 0` on `s`,
`(Σ |x_i|)^{n+1} ≤ (Σ w)^n · Σ |x_i|^{n+1} / w_i^n` (Jensen for `t ↦ t^{n+1}` at the weights
`w_i/Σ w` and the points `|x_i| Σ w / w_i`).

DERIVED: `1` the exponent shift; `0` the signs. -/
theorem sum_abs_pow_le {ι : Type*} (s : Finset ι) (x w : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (n : ℕ) :
    (∑ i ∈ s, |x i|) ^ (n + 1) ≤ (∑ i ∈ s, w i) ^ n * ∑ i ∈ s, |x i| ^ (n + 1) / w i ^ n := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  set W := ∑ i ∈ s, w i with hWdef
  have hW : 0 < W := Finset.sum_pos hw hne
  have hsum1 : ∑ i ∈ s, w i / W = 1 := by
    rw [← Finset.sum_div, div_self hW.ne']
  have key := Real.pow_arith_mean_le_arith_mean_pow s (fun i => w i / W)
    (fun i => |x i| * W / w i) (fun i hi => div_nonneg (hw i hi).le hW.le) hsum1
    (fun i hi => div_nonneg (mul_nonneg (abs_nonneg _) hW.le) (hw i hi).le) (n + 1)
  have e1 : ∑ i ∈ s, w i / W * (|x i| * W / w i) = ∑ i ∈ s, |x i| :=
    Finset.sum_congr rfl fun i hi => by
      have := (hw i hi).ne'
      field_simp
  have e2 : ∑ i ∈ s, w i / W * (|x i| * W / w i) ^ (n + 1)
      = W ^ n * ∑ i ∈ s, |x i| ^ (n + 1) / w i ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by
      have h1 := (hw i hi).ne'
      have h2 := hW.ne'
      have h3 : w i ^ n ≠ 0 := pow_ne_zero _ h1
      rw [div_pow, mul_pow, pow_succ W n, pow_succ (w i) n]
      field_simp
  rw [e1, e2] at key
  exact key

#print axioms sum_abs_pow_le

/-- **Moments of a sum of per-step increments.** If `ν(Δ_i^{2q+2}) ≤ D w_i^{2q+2}` with `w > 0` on
`s`, then `ν((Σ Δ_i)^{2q+2}) ≤ D (Σ w)^{2q+2}` (Minkowski's inequality in `L^{2q+2}` through
`sum_abs_pow_le`).

DERIVED: `2` makes the power even; `1` the exponent shift; `0` the signs. -/
theorem state_pow_sum_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ν : MassGap.DLRLimit.State X) {ι : Type*} (s : Finset ι) (Δ : ι → C(X, ℝ)) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (q : ℕ) {D : ℝ}
    (hD : ∀ i ∈ s, ν (Δ i ^ (2 * q + 2)) ≤ D * w i ^ (2 * q + 2)) :
    ν ((∑ i ∈ s, Δ i) ^ (2 * q + 2)) ≤ D * (∑ i ∈ s, w i) ^ (2 * q + 2) := by
  set W := ∑ i ∈ s, w i with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i hi => (hw i hi).le
  set c : ι → ℝ := fun i => W ^ (2 * q + 1) / w i ^ (2 * q + 1) with hc
  have hc0 : ∀ i ∈ s, 0 ≤ c i := fun i hi => div_nonneg (pow_nonneg hW0 _) (pow_pos (hw i hi) _).le
  have hev : Even (2 * q + 2) := ⟨q + 1, by ring⟩
  have hmono : ν ((∑ i ∈ s, Δ i) ^ (2 * q + 2))
      ≤ ν (∑ i ∈ s, c i • Δ i ^ (2 * q + 2)) := ν.mono fun x => by
    simp only [ContinuousMap.pow_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    have h1 := sum_abs_pow_le s (fun i => Δ i x) w hw (2 * q + 1)
    calc (∑ i ∈ s, Δ i x) ^ (2 * q + 2) = |∑ i ∈ s, Δ i x| ^ (2 * q + 2) := (hev.pow_abs _).symm
      _ ≤ (∑ i ∈ s, |Δ i x|) ^ (2 * q + 2) :=
          pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) _
      _ ≤ W ^ (2 * q + 1) * ∑ i ∈ s, |Δ i x| ^ (2 * q + 1 + 1) / w i ^ (2 * q + 1) := h1
      _ = ∑ i ∈ s, c i * Δ i x ^ (2 * q + 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by
            rw [show 2 * q + 1 + 1 = 2 * q + 2 by ring, hev.pow_abs, hc]
            ring
  rw [ν.map_sum] at hmono
  refine hmono.trans ?_
  calc ∑ i ∈ s, ν (c i • Δ i ^ (2 * q + 2))
      = ∑ i ∈ s, c i * ν (Δ i ^ (2 * q + 2)) := Finset.sum_congr rfl fun i _ => ν.map_smul _ _
    _ ≤ ∑ i ∈ s, c i * (D * w i ^ (2 * q + 2)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hD i hi) (hc0 i hi)
    _ = D * W ^ (2 * q + 1) * ∑ i ∈ s, w i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => by
          have := (hw i hi).ne'
          rw [hc]
          field_simp
          ring
    _ = D * W ^ (2 * q + 2) := by rw [← hWdef]; ring

#print axioms state_pow_sum_le

variable {N : ℕ}

/-- **E at the fine spacing from the coarse view and per-step control.** Suppose that for every cube
`[-R, R]⁴` the cube energy at step `k` is, eventually in `k`, a bounded reading `G_c ∘ χ_k` of a coarse
view plus `Σ_{j < m_k} Δ_{k,j}`, and that for every `q` the increments have
`ν_k(Δ_{k,j}^{2q+2}) ≤ D w_j^{2q+2}` for all `j < m_k`, eventually in `k`, with `w > 0` summable.
Then `CubeMomentBound` holds (`state_pow_le_of_abs_le`, `state_pow_sum_le`).

The index `j` counts the steps from the coarse scale down: the hypothesis asks that the step `j`
below the coarse scale contribute at most `w_j` in `L^{2q+2}`, uniformly in the fine step `k`.

DERIVED: `0` the zeroth moment and the signs; `1` the unit observable, the coefficient of the
remainder and the zeroth-moment bound; `2` makes the power even. -/
theorem cubeMomentBound_of_coarseSteps (hN : N ≠ 0) (W : ConfFlow N) (O : LField (MassGap.SUN.SU N))
    (χ : ℕ → C(Cfg N, Cfg N))
    (h : ∀ R : ℝ, 0 ≤ R → ∃ (Gc : C(Cfg N, ℝ)) (Bc : ℝ) (m : ℕ → ℕ)
      (Δ : ℕ → ℕ → C(Cfg N, ℝ)), (∀ U, |Gc U| ≤ Bc) ∧
      (∀ᶠ k in atTop, cubeSum (dySpacing N k) R (W.fieldMap k O).1
        = Gc.comp (χ k) + ∑ j ∈ Finset.range (m k), Δ k j) ∧
      ∀ q : ℕ, ∃ (D : ℝ) (w : ℕ → ℝ), (∀ j, 0 < w j) ∧ Summable w ∧
        ∀ᶠ k in atTop, ∀ j < m k,
          stateK hN k (Δ k j ^ (2 * q + 2)) ≤ D * w j ^ (2 * q + 2)) :
    CubeMomentBound hN W O := by
  intro R hR p
  obtain ⟨Gc, Bc, m, Δ, hGc, hsplit, hstep⟩ := h R hR
  rcases p with _ | q
  · refine ⟨1, Filter.Eventually.of_forall fun k => ?_⟩
    rw [Nat.mul_zero, pow_zero, (stateK hN k).map_one]
  obtain ⟨D, w, hw, hws, hk⟩ := hstep q
  have hw0 : ∀ j, 0 ≤ w j := fun j => (hw j).le
  set Bc' := max Bc 0
  set D' := max D 0
  refine ⟨2 ^ (2 * (q + 1)) * (1 ^ (2 * (q + 1)) * (D' * (∑' j, w j) ^ (2 * q + 2))
    + Bc' ^ (2 * (q + 1))), ?_⟩
  filter_upwards [hsplit, hk] with k hks hkk
  have hle := state_pow_le_of_abs_le (stateK hN k) (cubeSum (dySpacing N k) R (W.fieldMap k O).1)
    (∑ j ∈ Finset.range (m k), Δ k j) (K := 1) (c := Bc') zero_le_one (le_max_right _ _)
    (fun U => by
      rw [hks]
      simp only [ContinuousMap.add_apply, ContinuousMap.comp_apply, one_mul]
      calc |Gc (χ k U) + (∑ j ∈ Finset.range (m k), Δ k j) U|
          ≤ |Gc (χ k U)| + |(∑ j ∈ Finset.range (m k), Δ k j) U| := abs_add_le _ _
        _ ≤ Bc' + |(∑ j ∈ Finset.range (m k), Δ k j) U| := by
            linarith [hGc (χ k U), le_max_left Bc 0]
        _ = |(∑ j ∈ Finset.range (m k), Δ k j) U| + Bc' := add_comm _ _) (q + 1)
  have hZ := state_pow_sum_le (stateK hN k) (Finset.range (m k)) (Δ k) w (fun j _ => hw j) q
    (D := D') (fun j hj => (hkk j (Finset.mem_range.mp hj)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hw0 j) _)))
  have hsum : (∑ j ∈ Finset.range (m k), w j) ^ (2 * q + 2) ≤ (∑' j, w j) ^ (2 * q + 2) :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => hw0 j)
      (hws.sum_le_tsum _ fun j _ => hw0 j) _
  have hZ' : stateK hN k ((∑ j ∈ Finset.range (m k), Δ k j) ^ (2 * (q + 1)))
      ≤ D' * (∑' j, w j) ^ (2 * q + 2) := by
    rw [show 2 * (q + 1) = 2 * q + 2 by ring]
    exact hZ.trans (mul_le_mul_of_nonneg_left hsum (le_max_right _ _))
  refine hle.trans ?_
  have h2 : (0 : ℝ) ≤ 2 ^ (2 * (q + 1)) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h2
  rw [one_pow, one_mul, one_mul]
  linarith

#print axioms cubeMomentBound_of_coarseSteps

end E

/-! ## 3. The coarse pairing -/

section Tower

/-- **The coarse reflected pairing** at fine step `k`: `ν_k((G_θ G) ∘ χ_k) − ν_k(G ∘ χ_k)²`.

DERIVED: `2` the rank and the square. -/
def coarsePair (χ : ℕ → C(Cfg 2, Cfg 2)) (G Gθ : C(Cfg 2, ℝ)) (k : ℕ) : ℝ :=
  stateK two_ne k ((Gθ * G).comp (χ k)) - stateK two_ne k (G.comp (χ k)) ^ 2

end Tower

section N

end N

end MassGap.ObserverEnergyCoarseN
