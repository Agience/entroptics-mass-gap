import Mathlib
import MassGap.PurityResponse
import MassGap.PurityResponseWilson

/-!
# MassGap.PurityResponseSmooth — smoothness of the thermal response, Proposition 6.4 of the purity paper

Proposition 6.4 of D. Bhattacharjee, U. Bhattacharya, J. M. Lockwood, T. Romanov, I. J. Sessford
and S. Singha Roy, *Thermal Purity Bounds for Yang–Mills Theory at Weak Coupling* (research draft,
15 November 2026, <https://github.com/anaxia-research/4Y-M>, commit 8e01510, `Paper-2/Paper-2.pdf`)
states that `ψ` is smooth in `b`. For a finite measure `ν` and a bounded measurable action `S`,
`d/db mom ν g S = −mom ν (g S) S` (`PurityResponse.hasDerivAt_mom`) with `g S` again bounded and
measurable, so induction on the order gives every derivative.

* `contDiff_mom`, `contDiff_mom_infty`: `b ↦ ∫ g e^{−bS} dν` is `Cⁿ` for every `n`, hence `C^∞`.
* `contDiff_log_Z`, `contDiff_gibbs`, `contDiff_eT`: `log Z_b`, `⟨S⟩_b` and `e(b)` are `C^∞`
  (`Z_b > 0`, `PurityResponse.Z_pos`).
* `contDiff_psi`: `ψ(b) = 2 log Z_b(T) − log Z_b(2T)` is `C^∞`.
* `wilson_contDiff_ZRG`, `wilson_contDiff_psi`: for the Wilson model `RectWilsonG.sysRG` of any
  compact gauge group on any rectangular 4-torus, `β ↦ ZRG G L β` and
  `b ↦ 2 log ZRG G L (b/2) − log ZRG G L' (b/2)` are `C^∞`, with no condition on `L, L'`.
-/

namespace MassGap.PurityResponseSmooth

open Real MeasureTheory MassGap MassGap.LatticeGauge MassGap.WilsonLattice MassGap.CompactGauge
  MassGap.RectWilson MassGap.RectWilsonG MassGap.GaugeGroup MassGap.GaugeWilson
  MassGap.PurityResponse MassGap.PurityResponseWilson

open scoped ContDiff

variable {X : Type*} [MeasurableSpace X]

/-- `b ↦ ∫ g e^{−bS} dν` is `Cⁿ` for every `n` and every bounded measurable `g`. -/
theorem contDiff_mom {ν : Measure X} [IsFiniteMeasure ν] {S : X → ℝ} {M : ℝ} (hS : Measurable S)
    (hM : ∀ x, |S x| ≤ M) :
    ∀ n : ℕ, ∀ (g : X → ℝ) (K : ℝ), Measurable g → (∀ x, |g x| ≤ K) →
      ContDiff ℝ n (mom ν g S)
  | 0, g, K, hg, hgK => by
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun b =>
      (hasDerivAt_mom hg hS hgK hM b).continuousAt
  | n + 1, g, K, hg, hgK => by
    have hgS : ∀ x, |g x * S x| ≤ K * M := fun x => by
      rw [abs_mul]
      exact mul_le_mul (hgK x) (hM x) (abs_nonneg _) ((abs_nonneg _).trans (hgK x))
    have hd : deriv (mom ν g S) = fun b => -mom ν (fun x => g x * S x) S b :=
      funext fun b => (hasDerivAt_mom hg hS hgK hM b).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun b => (hasDerivAt_mom hg hS hgK hM b).differentiableAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [hd]
      exact (contDiff_mom hS hM n (fun x => g x * S x) (K * M) (hg.mul hS) hgS).neg

/-- `b ↦ ∫ g e^{−bS} dν` is `C^∞`. -/
theorem contDiff_mom_infty {ν : Measure X} [IsFiniteMeasure ν] {g S : X → ℝ} {K M : ℝ}
    (hg : Measurable g) (hS : Measurable S) (hgK : ∀ x, |g x| ≤ K) (hM : ∀ x, |S x| ≤ M) :
    ContDiff ℝ ∞ (mom ν g S) :=
  contDiff_infty.2 fun n => contDiff_mom hS hM n g K hg hgK

/-- The partition function `b ↦ Z_b = ∫ e^{−bS} dν` is `C^∞`. -/
theorem contDiff_Z {ν : Measure X} [IsFiniteMeasure ν] {S : X → ℝ} {M : ℝ} (hS : Measurable S)
    (hM : ∀ x, |S x| ≤ M) : ContDiff ℝ ∞ (mom ν (fun _ => 1) S) :=
  contDiff_mom_infty measurable_const hS (fun _ => le_of_eq (abs_one)) hM

/-- `b ↦ log Z_b` is `C^∞`. -/
theorem contDiff_log_Z {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {M : ℝ}
    (hS : Measurable S) (hM : ∀ x, |S x| ≤ M) :
    ContDiff ℝ ∞ (fun b => log (mom ν (fun _ => 1) S b)) :=
  (contDiff_Z hS hM).log fun b => (Z_pos hS hM b).ne'

/-- The Gibbs mean `b ↦ ⟨S⟩_b` is `C^∞`. -/
theorem contDiff_gibbs {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {M : ℝ}
    (hS : Measurable S) (hM : ∀ x, |S x| ≤ M) : ContDiff ℝ ∞ (gibbs ν S) := by
  exact (contDiff_mom_infty (ν := ν) hS hS hM hM).div (contDiff_Z (ν := ν) hS hM)
    fun b => (Z_pos hS hM b).ne'

/-- The energy density `b ↦ e(b) = ⟨S⟩_b / N` is `C^∞`. -/
theorem contDiff_eT {ν : Measure X} [IsProbabilityMeasure ν] {S : X → ℝ} {M : ℝ} (N : ℝ)
    (hS : Measurable S) (hM : ∀ x, |S x| ≤ M) : ContDiff ℝ ∞ (eT N ν S) :=
  (contDiff_gibbs hS hM).div_const N

variable {Y : Type*} [MeasurableSpace Y]

/-- Proposition 6.4: `ψ(b) = 2 log Z_b(T) − log Z_b(2T)` is `C^∞` in `b`. -/
theorem contDiff_psi {ν₁ : Measure X} [IsProbabilityMeasure ν₁] {ν₂ : Measure Y}
    [IsProbabilityMeasure ν₂] {S₁ : X → ℝ} {S₂ : Y → ℝ} {M₁ M₂ : ℝ} (hS₁ : Measurable S₁)
    (hS₂ : Measurable S₂) (hM₁ : ∀ x, |S₁ x| ≤ M₁) (hM₂ : ∀ y, |S₂ y| ≤ M₂) :
    ContDiff ℝ ∞ (psi ν₁ ν₂ S₁ S₂) :=
  (contDiff_const.mul (contDiff_log_Z hS₁ hM₁)).sub (contDiff_log_Z hS₂ hM₂)

section Wilson

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- `|SW| ≤ 2 (6 ∏ L i)`, from `SW_nonneg` and `SW_le`. -/
theorem abs_SW_le (L : Fin 4 → ℕ) (U : (sysRG G L).Config) :
    |SW G L U| ≤ 2 * (6 * ∏ i, (L i : ℝ)) := by
  rw [abs_of_nonneg (SW_nonneg U)]
  exact SW_le U

/-- The Wilson partition function `β ↦ ZRG G L β` is `C^∞`. -/
theorem wilson_contDiff_ZRG (L : Fin 4 → ℕ) : ContDiff ℝ ∞ (fun β => ZRG G L β) := by
  have h := (contDiff_Z (ν := nu G L) measurable_SW (abs_SW_le L)).comp
    (contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun β : ℝ => 2 * β)
  convert h using 1
  funext β
  simp only [Function.comp_apply]
  rw [mom_eq]
  congr 1
  ring

/-- Proposition 6.4 for the Wilson model: `b ↦ 2 log ZRG G L (b/2) − log ZRG G L' (b/2)` is
`C^∞`, for all `L, L'`. -/
theorem wilson_contDiff_psi (L L' : Fin 4 → ℕ) :
    ContDiff ℝ ∞ (fun b => 2 * log (ZRG G L (b / 2)) - log (ZRG G L' (b / 2))) := by
  convert contDiff_psi (ν₁ := nu G L) (ν₂ := nu G L') measurable_SW measurable_SW
    (abs_SW_le L) (abs_SW_le L') using 1
  funext b
  rw [psi_eq]

end Wilson

end MassGap.PurityResponseSmooth

#print axioms MassGap.PurityResponseSmooth.contDiff_mom
#print axioms MassGap.PurityResponseSmooth.contDiff_mom_infty
#print axioms MassGap.PurityResponseSmooth.contDiff_Z
#print axioms MassGap.PurityResponseSmooth.contDiff_log_Z
#print axioms MassGap.PurityResponseSmooth.contDiff_gibbs
#print axioms MassGap.PurityResponseSmooth.contDiff_eT
#print axioms MassGap.PurityResponseSmooth.contDiff_psi
#print axioms MassGap.PurityResponseSmooth.abs_SW_le
#print axioms MassGap.PurityResponseSmooth.wilson_contDiff_ZRG
#print axioms MassGap.PurityResponseSmooth.wilson_contDiff_psi
