import Mathlib
import MassGap.ZCanon
import MassGap.LinkReduce

/-!
# MassGap.TraceNorm — the normalisation of the trace channel in `ClayStatement`

`ShortDistance` (§4, `shortDist2_const`) takes the trace at `ScalarTie`'s normalisation, and the limit
of its clause `ShortDist2` is `afConst N`. This module shows where that normalisation comes from: the
trace read by the target carries factor `2/a_k⁴`, the same factor on which `ChannelTie`, `ScalarTie`
and `TopNorm` agree.

## The trace field of the target

`trField ρ k U = ∑_b mixC ρ k trC b · op_b(U)` is the lattice field of `trC = ∑_{μν} T_{μνμν}` at
step `k`; `TwoPointKernel` reads it.

* `classicalLead_trField`: under `ScalarTie ρ O` there is `Ztr` with `Ztr k · a_k⁴ → N/8` and, at
  every step, `trField ρ k` has classical lead `Ztr k · (16/N) · g² ⟨trC, ffT g A⟩` at dimension `4`
  (from `ObsLead.classicalLead_obs`).
* `tendsto_trace_factor`: `Ztr k · a_k⁴ · (16/N) → 2`. So the trace read by the target has, per
  `a_k⁴`, classical lead tending to `2 · g² ∑_{μν} Re tr F_{μν}F_{μν}`, not `1 ·` that.
* `trField_eq_channel`: under `ChannelTie ρ Mb Z`, `trField ρ k = ∑_β (zAct (Z k) trC)_β B_β`, with
  `B_β = ∑_b Mb β b op_b` the bare discretisation.
* `trace_channel_factor`: under both ties, on every classical configuration family,
  `g² ⟨zAct (Z k) trC, ffT g A⟩ = Ztr k · (16/N) · g² ⟨trC, ffT g A⟩`. `ChannelTie` leaves the trace
  factor of `Z k` free; `ScalarTie` fixes it, at `2/a_k⁴` asymptotically (`trace_factor_of_ties`),
  the same value `TopNorm` fixes on the pseudoscalar channel.
* `ties_jointly`: `ScalarTie`, `ChannelTie` and `TopNorm` hold together at the data
  `ClayData.rhoD (ObsLead.fT N) (ZCanon.zFix N 1 1)`. The normalisation clauses are jointly
  satisfiable; there is no inconsistency among them.

## The constant of `AFCoefficient`

* `afConst_eq_sq_two_mul`: `afConst N = 2² · (12(N² − 1)/π⁴)/(4 b₀²)`. `12(N² − 1)/π⁴` is the
  tree value (ARGUED) of the field `g² ⟨trC, ffT⟩` with factor `1/a_k⁴`. The trace of the target
  carries factor `2/a_k⁴` (`tendsto_trace_factor`). A two-point function is quadratic in the field, so
  its tree value is `2² · 12 = 48`, which is `ShortDistance.treeTwoTr_unit` and the value `afConst` is
  built on.
* `not_afCoefficient_and_quarter`: no `G` has both `AFCoefficient N G` and
  `r⁸ G(r) (log r)² → afConst N / 4` (`2 ≤ N`). So the trace at factor `1/a_k⁴`
  instead of `2/a_k⁴` contradicts the target. `ShortDistance` takes it at `2/a_k⁴`, and
  `shortDist2_const` gives `afConst N`.

ARGUED (the Gaussian measure and Wick contraction are not formalised; colour algebra
`tr(TᵃTᵇ) = δᵃᵇ/2`): `g² ∑_{μν} Re tr F_{μν}F_{μν} = (g²/2) F^aF^a`, whose free two-point value is
`12(N² − 1) g⁴/(π⁴ r⁸)`; twice it is `g² F^aF^a`, value `48(N² − 1) g⁴/(π⁴ r⁸)`; times
`ḡ⁴(r) (log r)² → 1/(4b₀²)` this is `afConst N`.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `4` the dimension and `4 = 2²`; `16`, `8` as in `ScalarTie` and
`ObsLead.classicalLead_obs`; `2 = (N/8)(16/N)` the trace factor; `12`, `48 = 4 · 12` the tree
values; `1` the factors `zri`, `zwe` of the witness; `0` the plane.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.TraceNorm

open MassGap MassGap.ClayStatement MassGap.ClassicalLimit MassGap.ContinuumSchwinger
  MassGap.ContinuumField MassGap.InfiniteLattice Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. The trace field under `ScalarTie` -/

/-- **The lattice trace field** of step `k`: `∑_b mixC ρ k trC b · op_b(U)`.
DERIVED: no numeral. -/
def trField (ρ : RenormMix N) (k : ℕ) (U : Cfg N) : ℝ := ∑ b, mixC ρ k trC b * (ρ.op b).1 U

/-- **The classical lead of the trace under `ScalarTie`**: `Ztr k · (16/N) g² ⟨trC, ffT g A⟩` at
dimension `4`, with `Ztr k · a_k⁴ → N/8`.

DERIVED: `4` the dimension; `16` as in `classicalLead_obs`; `8` as in `ScalarTie`. -/
theorem classicalLead_trField (ρ : RenormMix N) (O : LField (MassGap.SUN.SU N))
    (hT : ScalarTie ρ O) :
    ∃ Ztr : ℕ → ℝ,
      (∀ k, ClassicalLead (trField ρ k) 4
        (fun A g => Ztr k * ((16 / (N : ℝ)) * (g ^ 2 * (trC ⬝ᵥ ffT g A)))))
      ∧ Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8)) := by
  obtain ⟨hO, Ztr, hZ, hlim⟩ := hT
  refine ⟨Ztr, fun k => ?_, hlim⟩
  subst hO
  have he : trField ρ k = fun U => Ztr k * (ClayData.obs N).1 U := by
    funext U
    have h := DFunLike.congr_fun (hZ k) U
    rw [ClayData.obs_def]
    simpa [trField, ContinuousMap.sum_apply] using h
  rw [he]
  intro A hA g U hU
  have h := (ObsLead.classicalLead_obs (N := N) A hA g U hU).const_mul (Ztr k)
  refine h.congr fun a => ?_
  try beta_reduce
  ring

/-- **The trace factor tends to `2`**: `Ztr k · a_k⁴ · (16/N) → 2`.

DERIVED: `2 = (N/8)(16/N)`; `4` the dimension. -/
theorem tendsto_trace_factor (hN : N ≠ 0) {Ztr : ℕ → ℝ}
    (h : Tendsto (fun k => Ztr k * dySpacing N k ^ 4) atTop (𝓝 ((N : ℝ) / 8))) :
    Tendsto (fun k => Ztr k * dySpacing N k ^ 4 * (16 / (N : ℝ))) atTop (𝓝 2) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h2 := h.mul_const (16 / (N : ℝ))
  have e : (N : ℝ) / 8 * (16 / N) = 2 := by
    calc (N : ℝ) / 8 * (16 / N) = 2 * ((N : ℝ) * (N : ℝ)⁻¹) := by ring
      _ = 2 := by rw [mul_inv_cancel₀ hN', mul_one]
  rwa [e] at h2

/-! ## 2. The trace field under `ChannelTie` -/

/-- **The trace through the bare discretisation**: under `ChannelTie`,
`trField ρ k U = ∑_β (zAct (Z k) trC)_β B_β(U)`, `B_β = ∑_b Mb β b op_b`.

DERIVED: no numeral. -/
theorem trField_eq_channel (ρ : RenormMix N) (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ)
    (hCT : ChannelTie ρ Mb Z) (k : ℕ) (U : Cfg N) :
    trField ρ k U = ∑ β, zAct (Z k) trC β * ∑ b, Mb β b * (ρ.op b).1 U := by
  have h1 : ∀ b, mixC ρ k trC b * (ρ.op b).1 U
      = ∑ β, ∑ α, trC α * Z k α β * (Mb β b * (ρ.op b).1 U) := by
    intro b
    simp only [mixC, hCT.1 k, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by ring
  unfold trField
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [zAct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]

/-- **The trace factor of `Z k` read by `ScalarTie`**: under `ChannelTie` and the classical lead of
`classicalLead_trField`, on every classical configuration family of an admissible potential,
`g² ⟨zAct (Z k) trC, ffT g A⟩ = Ztr k · (16/N) · g² ⟨trC, ffT g A⟩`.

DERIVED: `4` the dimension; `16` as in `classicalLead_obs`; `2` the power of the coupling. -/
theorem trace_channel_factor (ρ : RenormMix N) (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ)
    (hCT : ChannelTie ρ Mb Z) (Ztr : ℕ → ℝ)
    (hL : ∀ k, ClassicalLead (trField ρ k) 4
      (fun A g => Ztr k * ((16 / (N : ℝ)) * (g ^ 2 * (trC ⬝ᵥ ffT g A)))))
    (k : ℕ) (A : GPot N) (hA : GPot.Adm A) (g : ℝ) (U : ℝ → Cfg N)
    (hU : ∀ a, 0 < a → IsClassCfg a g A (U a)) :
    g ^ 2 * (zAct (Z k) trC ⬝ᵥ ffT g A)
      = Ztr k * ((16 / (N : ℝ)) * (g ^ 2 * (trC ⬝ᵥ ffT g A))) := by
  have hB : ClassicalLead (fun U => ∑ β ∈ Finset.univ, zAct (Z k) trC β
        * (fun β (V : Cfg N) => ∑ b, Mb β b * (ρ.op b).1 V) β U) 4
      (fun A g => ∑ β ∈ Finset.univ, zAct (Z k) trC β
        * (fun β (A : GPot N) (g : ℝ) => g ^ 2 * ffT g A β) β A g) :=
    classicalLead_sum Finset.univ (zAct (Z k) trC)
      (fun β (V : Cfg N) => ∑ b, Mb β b * (ρ.op b).1 V)
      (fun β (A : GPot N) (g : ℝ) => g ^ 2 * ffT g A β) 4 fun β _ => hCT.2.2 β
  have e : trField ρ k = fun V => ∑ β ∈ Finset.univ, zAct (Z k) trC β
      * (fun β (V : Cfg N) => ∑ b, Mb β b * (ρ.op b).1 V) β V :=
    funext fun V => trField_eq_channel ρ Mb Z hCT k V
  have h1 := hL k A hA g U hU
  have h2 := hB A hA g U hU
  rw [e] at h1
  have hu : ∑ β, zAct (Z k) trC β * (g ^ 2 * ffT g A β)
      = Ztr k * ((16 / (N : ℝ)) * (g ^ 2 * (trC ⬝ᵥ ffT g A))) := tendsto_nhds_unique h2 h1
  rw [← hu]
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun β _ => by ring

/-- **Under both ties the trace factor of `Z k` is `c k` with `c k · a_k⁴ → 2`**: there is `c` with
`c k · a_k⁴ → 2` and, on every classical configuration family,
`g² ⟨zAct (Z k) trC, ffT g A⟩ = c k · g² ⟨trC, ffT g A⟩`.

DERIVED: `2` as in `tendsto_trace_factor`; `4` the dimension. -/
theorem trace_factor_of_ties (hN : N ≠ 0) (ρ : RenormMix N) (O : LField (MassGap.SUN.SU N))
    (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ)
    (hT : ScalarTie ρ O) (hCT : ChannelTie ρ Mb Z) :
    ∃ c : ℕ → ℝ, Tendsto (fun k => c k * dySpacing N k ^ 4) atTop (𝓝 2)
      ∧ ∀ k (A : GPot N), GPot.Adm A → ∀ (g : ℝ) (U : ℝ → Cfg N),
        (∀ a, 0 < a → IsClassCfg a g A (U a)) →
          g ^ 2 * (zAct (Z k) trC ⬝ᵥ ffT g A) = c k * (g ^ 2 * (trC ⬝ᵥ ffT g A)) := by
  obtain ⟨Ztr, hL, hlim⟩ := classicalLead_trField ρ O hT
  refine ⟨fun k => Ztr k * (16 / (N : ℝ)), ?_, fun k A hA g U hU => ?_⟩
  · exact (tendsto_trace_factor hN hlim).congr fun k => by
      try beta_reduce
      ring
  · rw [trace_channel_factor ρ Mb Z hCT Ztr hL k A hA g U hU]
    try beta_reduce
    ring

/-! ## 3. The ties hold together -/

/-- **`ScalarTie`, `ChannelTie` and `TopNorm` hold together** at
`ClayData.rhoD (ObsLead.fT N) (ZCanon.zFix N 1 1)`.

DERIVED: `2` the least colour count; `1` the free factors. -/
theorem ties_jointly (hN2 : 2 ≤ N) :
    ∃ (ρ : RenormMix N) (Mb : Idx4 → ρ.B → ℝ) (Z : ℕ → Idx4 → Idx4 → ℝ),
      ScalarTie ρ (MassGap.ObserverSymField.sym
          (MassGap.ObserverEnergyMoments.plaqField MassGap.ObserverEnergyMoments.q0))
        ∧ ChannelTie ρ Mb Z ∧ TopNorm N Z := by
  have hN : N ≠ 0 := ne_zero_of_two_le hN2
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Mb, Zc, hCT, hlim⟩ := ClayData.channelTie_D (ObsLead.fT N) (ObsLead.bT N)
    (ZCanon.zFix N 1 1) (ZCanon.tendsto_zFix_ps hN1 1 1) (ObsLead.tiedB_obs hN)
  exact ⟨_, Mb, Zc, ClayData.scalarTie_D hN (ObsLead.fT N) (ZCanon.zFix N 1 1)
    (ZCanon.tendsto_zFix_sc hN1 1 1), hCT, LinkReduce.topNorm_of_channelTie _ Mb Zc hCT hlim⟩

/-! ## 4. The constant of `AFCoefficient` -/

/-- **`afConst` is `2²` times the tree value at factor `1/a_k⁴`**:
`afConst N = 2² · (12(N² − 1)/π⁴)/(4 b₀²)`.

DERIVED: `2` the trace factor; `12` the tree value; `4` the running-coupling limit and the power
of `π`. -/
theorem afConst_eq_sq_two_mul (N : ℕ) :
    afConst N = 2 ^ 2 * (12 * ((N : ℝ) ^ 2 - 1) / Real.pi ^ 4 / (4 * b0 N ^ 2)) := by
  unfold afConst
  ring

/-- **`AFCoefficient` excludes the limit `afConst N / 4`**: no `G` has both.

DERIVED: `2` the least colour count; `4` the ratio; `8`, `2` as in `AFCoefficient`; `0` the
point approached. -/
theorem not_afCoefficient_and_quarter (hN2 : 2 ≤ N) (G : ℝ → ℝ) :
    ¬ (AFCoefficient N G ∧ Tendsto (fun r => r ^ 8 * G r * Real.log r ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (afConst N / 4))) := by
  rintro ⟨h1, h2⟩
  have hu := tendsto_nhds_unique h1 h2
  have hp := afConst_pos hN2
  linarith

end MassGap.TraceNorm

#print axioms MassGap.TraceNorm.classicalLead_trField
#print axioms MassGap.TraceNorm.tendsto_trace_factor
#print axioms MassGap.TraceNorm.trField_eq_channel
#print axioms MassGap.TraceNorm.trace_channel_factor
#print axioms MassGap.TraceNorm.trace_factor_of_ties
#print axioms MassGap.TraceNorm.ties_jointly
#print axioms MassGap.TraceNorm.afConst_eq_sq_two_mul
#print axioms MassGap.TraceNorm.not_afCoefficient_and_quarter
