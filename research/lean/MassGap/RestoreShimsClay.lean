import Mathlib
import MassGap.ClayRoutes
import MassGap.UVIRSplit
import MassGap.HeatBathLocal
import MassGap.BoxPatch

noncomputable section

/-!
# MassGap.RestoreShimsClay — the finite-size route to `ClayRoutes.ClayContinuum`

Its declarations keep the namespace `ClayRoutes`; they sit in this module because they import `UVIRSplit`,
`HeatBathLocal` and `BoxPatch`, which `ClayRoutes` does not.

`UVBelowIR` names the UV step below an IR rate; `clay_continuum_of_irGap` takes an IR gap
(`UVIRSplit.IRGapAt`) and the UV step below it, with E, N and Y, to `ClayRoutes.ClayContinuum`;
`clay_continuum_of_boxPatchGap` takes one box (`BoxPatch.BoxPatchGap`) through
`HeatBathLocal.irGapAt_boxRate` to the same conclusion.
-/

namespace MassGap.ClayRoutes

variable {N : ℕ}

/-! ## 2. The finite-size route -/

section FiniteSize

open MassGap

/-- **The UV step below the rate `M₀`.** Some non-negative loss function `ε` and budget `E` have
`UVIRSplit.LossBudget ε (aRun N β₀) E`, `E < M₀` and the step clipped at `M₀`,
`UVIRSplit.UVLossStepBelow τ p hN βUV ε M₀`: the losses of the dyadic tower from `β₀` sum below `M₀`, and
the rates up to `M₀` are carried from `βUV` on. The step is asked only at rates `M ≤ M₀`, which is all the
composition consumes (`UVIRSplit.gapAt_eventually_of_uv_ir_below`); asked at every rate it would have to
cover every fall of the true rate between two couplings. The losses are non-negative: a negative loss would assert a gap
outright, and with `0 ≤ ε` the step holds on gapless families (`UVIRSplit.lossStep_of_no_gap`), so it
carries no IR content. `UVIRSplit.fixedWindowDecay_of_uv_ir_below` consumes it at the IR rate `M₀`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the sign of the losses. -/
def UVBelowIR (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) (β₀ βUV M₀ : ℝ) : Prop :=
  ∃ (ε : ℝ → ℝ) (E : ℝ), (∀ s, 0 ≤ ε s) ∧
    UVIRSplit.LossBudget ε (MassGap.AsymptoticScaling.aRun N β₀) E ∧
    E < M₀ ∧ UVIRSplit.UVLossStepBelow τ p hN βUV ε M₀

/-- **A UV step at zero budget is below every positive rate.** A non-negative loss function `ε`,
`UVIRSplit.UVLossStep τ p hN βUV ε` and `UVIRSplit.LossBudget ε (aRun N β₀) E` with `E ≤ 0` give
`UVBelowIR τ p hN β₀ βUV M₀` at every `M₀ > 0`. `LossBudget` at no terms gives `0 ≤ E`, so `E = 0`: the
degenerate, loss-free case.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank, the bound on `E` and the sign of
`M₀`. -/
theorem uvBelowIR_of_nonpos_budget (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β₀ βUV E M₀ : ℝ}
    {ε : ℝ → ℝ} (hε : ∀ s, 0 ≤ ε s) (hstep : UVIRSplit.UVLossStep τ p hN βUV ε)
    (hbud : UVIRSplit.LossBudget ε (MassGap.AsymptoticScaling.aRun N β₀) E) (hE : E ≤ 0)
    (hM₀ : 0 < M₀) :
    UVBelowIR τ p hN β₀ βUV M₀ :=
  ⟨ε, E, hε, hbud, lt_of_le_of_lt hE hM₀, UVIRSplit.uvLossStepBelow_of_uvLossStep τ p hN hstep M₀⟩

#print axioms uvBelowIR_of_nonpos_budget

/-- **The UV input from a uniform gap at the rate.** If the periodic data has the gap at rate
`e^{−M₀·aRun N β}` at every `β ≥ βUV`, `0 < βUV` and `0 < M₀`, then `UVBelowIR τ p hN β₀ βUV M₀` with zero
losses: every rate `M ≤ M₀` is carried from any coupling to any other by `GapStep.gapAt_mono`. With the
clipped step, the UV input at `M₀` asks no more than the lattice gap at the fixed physical rate `M₀` from
`βUV` on.

DERIVED: `4` is the spacetime dimension; `1` is the least colour count; `0` is the excluded rank, the
sign of `βUV` and `M₀`, and the zero loss. -/
theorem uvBelowIR_of_uniform_gap (τ : Fin 4) (p : ℤ) (hN1 : 1 ≤ N) (hN : N ≠ 0) {β₀ βUV M₀ : ℝ}
    (hUV : 0 < βUV) (hM₀ : 0 < M₀)
    (hgap : ∀ β : ℝ, βUV ≤ β → UVIRSplit.IRGapAt τ p hN β M₀) :
    UVBelowIR τ p hN β₀ βUV M₀ := by
  refine ⟨fun _ => 0, 0, fun _ => le_rfl, fun n => by simp, hM₀, ?_⟩
  intro β β' _ hβ' _ _ M hM _
  have ha : 0 < MassGap.AsymptoticScaling.aRun N β' :=
    MassGap.AsymptoticScaling.aRun_pos hN1 (lt_of_lt_of_le hUV hβ')
  have h := hgap β' hβ'
  unfold UVIRSplit.IRGapAt at h
  refine GapStep.gapAt_mono _ (Real.exp_pos _).le ?_ h
  simp only [sub_zero, Real.exp_le_exp]
  linarith [mul_le_mul_of_nonneg_right hM ha.le]

#print axioms uvBelowIR_of_uniform_gap

end FiniteSize

section FiniteSizeCapstone

open MassGap MassGap.ContinuumField MassGap.ContinuumSchwinger

/-- **The continuum Clay statement from an IR gap and the UV step below it.** At `2 ≤ N`, `0 < L`,
`0 < β₀`, `βUV ≤ β₀`, the IR gap `UVIRSplit.IRGapAt τ 0 hN β₀ M₀` at a rate `M₀`, the UV step below it
(`UVBelowIR τ 0 hN β₀ βUV M₀`), and E, N, Y: `ClayContinuum hN Z τ hZ hB L`
(`UVIRSplit.fixedWindowDecay_of_uv_ir_below`, `clay_continuum_of_fixedWindowDecay`).

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension. -/
theorem clay_continuum_of_irGap (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV M₀ : ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀) (hir : UVIRSplit.IRGapAt τ 0 hN β₀ M₀)
    (huv : UVBelowIR τ 0 hN β₀ βUV M₀)
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuum hN Z τ hZ hB L := by
  obtain ⟨ε, E, hε, hbud, hEM, hstep⟩ := huv
  exact clay_continuum_of_fixedWindowDecay hN2 hN Z τ hZ hB hL
    (UVIRSplit.fixedWindowDecay_of_uv_ir_below τ 0 hN2 hN hL hβ₀ hUVβ₀ hbud hEM hε hstep hir) O G hconv hY

#print axioms clay_continuum_of_irGap

/-- **The continuum Clay statement from one box.** At `2 ≤ N`, `0 < L`, `0 < β₀`, `βUV ≤ β₀`,
`BoxPatch.BoxPatchGap hN β₀ n γ` (M-middle), the UV step below the box's rate
`HeatBathLocal.boxRate N β₀ n γ = min(boxKnabe n γ, 1)/(508 · aRun N β₀)` (`HeatBathLocal.boxRate_eq`)
from `βUV` on, the budget along the dyadic tower from `β₀` (`UVBelowIR`, M-UV), with `βUV` past the peak
`17N²/(88π²)` of `aRun N`, and E, N, Y: `ClayContinuum hN Z τ hZ hB L`. The box gives the IR gap
at that rate (`HeatBathLocal.irGapAt_boxRate`), and `clay_continuum_of_irGap` concludes.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` in `Fin 4` is the spacetime dimension; `1` in
the proof is the least colour count; `17N²/(88π²)` is the peak of `aRun N` (`AsymptoticScaling.aRun`, the peak `17N²/(44π²)` of `aRunStd` at
`β_std = 2β`). CHOSEN: the scope restriction `_hpeak`, not used by the proof, keeps every coupling of the UV step where `aRun N` decreases, so each step of the tower refines the spacing. The peak lies deep in strong coupling (about `0.078` at `N = 2`); the physical crossover (Lean `β ≈ 1.1` at `N = 2`, `≈ 2.85` at `N = 3`) lies at larger `β`, inside the UV step unless `β₀` is past it. -/
theorem clay_continuum_of_boxPatchGap (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ : ℝ} {n : ℕ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (_hpeak : 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2) ≤ βUV)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ)
    (huv : UVBelowIR τ 0 hN β₀ βUV (HeatBathLocal.boxRate N β₀ n γ))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayContinuum hN Z τ hZ hB L :=
  clay_continuum_of_irGap hN2 hN Z τ hZ hB hL hβ₀ hUVβ₀
    (HeatBathLocal.irGapAt_boxRate τ 0 (by omega) hN hβ₀ hbox).2 huv O G hconv hY

#print axioms clay_continuum_of_boxPatchGap

end FiniteSizeCapstone

end MassGap.ClayRoutes
