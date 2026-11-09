import Mathlib
import MassGap.NoTransition

/-!
# MassGap.FineEnd — the fine end from one block step at a time

The open statement is `NoTransition.NoFadeAtFineEnd gLat rLat`: with the observer held constant, the
aperture's reading of the substrate keeps a positive gap as the substrate refines without limit
(a positive floor on `ratio gLat rLat k = gLat k / rLat k` from some zoom on). This module states a
local form of it, one block step at a time, and proves that the local form gives it.

## 1. The step statement

The zoom `k` grows toward the fine end; one block step maps zoom `k + 1` (finer) to zoom `k`
(coarser). `f = ratio gLat rLat` is the gap in the observer's units.

* `StepLoss f ε K`: from zoom `K` on, one block step loses at most the fraction `ε k` of the reading:
  `(1 − ε k) f k ≤ f (k + 1)`. Gains are free; only the losses are budgeted.
* `StepBudget ε`: `0 ≤ ε k < 1` at every step, and the total loss `Σ ε k` is finite.
* `FineEndStep gLat rLat`: some budget, some zoom `K` with a positive reading (in the owner's chain,
  `K` is the zoom at the fixed physical length, where the substrate reads coarse), and `StepLoss`
  from `K` on.

`noFadeAtFineEnd_of_fineEndStep`: `FineEndStep ⇒ NoFadeAtFineEnd`, with the explicit floor
`f K' · e^{−2 Σ_{k ≥ K'} ε k}` from the zoom `K'` where the step losses fall below `1/2`
(`exp_neg_two_mul_le`: `e^{−2x} ≤ 1 − x` on `[0, 1/2]`; `tail_lower`). With link 3,
`ratioInvariant_of_fineEndStep` and `physical_gap_of_fineEndStep` carry it to `RatioInvariant` and to
a uniform positive physical gap on the observer's line. `fineEndStep_of_oneScale`: under link 3 the
positive reading at `K` is automatic, so the step statement is the budget alone.
`noFade_of_stepMono`: the case `ε ≡ 0` (the reading does not decrease under refinement).

## 2. Its relation to `NoFadeAtFineEnd`

The step inequality is local (each consecutive pair of zooms is checked on its own), the budget
`Summable ε` is a condition on the whole line, and the statement is a sufficient condition, not an
equivalent one. `osc_noFade`, `osc_not_fineEndStep`: a reading
alternating between `2` and `1` has a floor and admits no summable step budget. What the step
statement adds is that the losses along the line have a finite total.

## 3. How large the step loss may be

* `stepBudget_geom`: losses `ε k ≤ D qᵏ`, `q < 1`, are a budget.
* `stepBudget_resolution`: on the zoom line `a k = a₀ / sᵏ`, `s > 1`, losses
  `ε k ≤ D (a k / L)ᵖ`, `p ≥ 1` (the resolution of the substrate relative to the fixed length `L`,
  the size of a lattice artefact of order `p`) are a budget (`resolution_geom`).
* `stepBudget_twoLoop`: losses `ε k ≤ D / (α + β k)²` are a budget: on the one-loop line the inverse
  coupling at the cutoff is `α + β k` (`invCoup_geometric`), so this is a loss of the size of the
  square of the coupling, `g⁴` (the name refers to that order; the running used is one-loop).
* `perturbative_budget_admits_fade`, `oneLoop_budget_admits_fade`: losses of the size of the coupling
  itself, `ε k ≤ C g²(a k)`, do not suffice. `fade k = 1/(k+1)` loses exactly `1/(k+2)` per step,
  that loss is at most `C` times the one-loop `g²` at the cutoff on every geometric line with
  `b₀ > 0`, `s > 1` and `1/g²(a₀) > 0` (for the constant `C = 1/g²(a₀) + 2 b₀ log s`), it is not
  summable, and `fade` has no floor.

So the step loss of the gap ratio must be below the one-loop order of the running: one order of `g²`
smaller (`g⁴`) or of the size of a power of the resolution `a/L` suffices; the size `g²` does not.

## 4. Controls

* `fineEndStep_fails_of_gap_zero`: a gap reading that vanishes at every fine zoom (the `U(1)`
  Coulomb-phase photon, Guth 1980, Fröhlich–Spencer 1982; cited, not proved here) fails the step
  statement.
* `fineEndStep_fails_of_observer_zero`: so does an observer reading that vanishes at every fine zoom
  (zero string tension: the deconfined phase of 4D `Z_N`, Creutz–Jacobs–Rebbi 1979, and the `U(1)`
  Coulomb phase; cited, not proved here). In Lean `x / 0 = 0`, so the ratio is `0` there; the
  physical statement is that link 3 (`OneScale`) fails there.
* `fineEndStep_fails_fade`: the `fade` line fails it.
* `jump_fineEndStep`: a finite downward jump (the model of a first-order bulk transition of the
  lattice action, as for the large-`N` Wilson action; cited, not proved here) satisfies it: the
  statement is about the physical ratio, not about analyticity of the bare action.

## 5. What remains

`FineEndStep gLat rLat` for the 4D `SU(N)` Wilson line: one block step at a time from the zoom of the
fixed physical length to the continuum, the gap in the observer's units loses at most a summable
fraction, i.e. a loss below the order `g²` of the running at every step. No declaration here proves
it or ties `gLat`, `rLat` to the Wilson measure.

DERIVED (module-wide): `1/2` the threshold below which `e^{−2x} ≤ 1 − x`; `2` in `e^{−2x}` from
`(1 − x)(1 + 2x) ≥ 1` on `[0, 1/2]`; `2` in `1/(k+2)` the step loss of `fade`; `2` in `(α + β k)²` the
square of the coupling; `2` and `1` the two values of `osc`; `1/2` the step loss of the jump; `0` the
first zoom and the sign of every bound.
-/

noncomputable section

namespace MassGap.FineEnd

open Filter Topology
open MassGap.ApertureInvariance MassGap.EdgeCost MassGap.NoTransition

variable {gLat rLat : ℕ → ℝ}

/-! ## 1. The step statement -/

/-- **One block step loses at most the fraction `ε k`**: from zoom `K` on,
`(1 − ε k) f k ≤ f (k + 1)`. -/
def StepLoss (f ε : ℕ → ℝ) (K : ℕ) : Prop := ∀ k, K ≤ k → (1 - ε k) * f k ≤ f (k + 1)

/-- **A step budget**: each step loss in `[0, 1)`, and the total loss finite. -/
def StepBudget (ε : ℕ → ℝ) : Prop := (∀ k, 0 ≤ ε k ∧ ε k < 1) ∧ Summable ε

/-- **The fine end one block step at a time**: a step budget, a zoom `K` with a positive gap ratio,
and the step loss of the gap ratio within the budget from `K` on. -/
def FineEndStep (gLat rLat : ℕ → ℝ) : Prop :=
  ∃ (ε : ℕ → ℝ) (K : ℕ), StepBudget ε ∧ 0 < ratio gLat rLat K ∧ StepLoss (ratio gLat rLat) ε K

/-- `e^{−2x} ≤ 1 − x` for `0 ≤ x ≤ 1/2`.

DERIVED: `2` and `1/2` from `(1 − x)(1 + 2x) ≥ 1` on `[0, 1/2]`. -/
theorem exp_neg_two_mul_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-(2 * x)) ≤ 1 - x := by
  have hpos : 0 < 2 * x + 1 := by linarith
  have he := Real.add_one_le_exp (2 * x)
  rw [Real.exp_neg]
  calc (Real.exp (2 * x))⁻¹ ≤ (2 * x + 1)⁻¹ := inv_anti₀ hpos he
    _ ≤ 1 - x := by
        rw [← one_div, div_le_iff₀ hpos]
        nlinarith

/-- **A positive reading stays positive** under steps losing less than everything. -/
theorem pos_of_stepLoss {f ε : ℕ → ℝ} {K : ℕ} (hpos : 0 < f K) (hlt : ∀ k, ε k < 1)
    (hstep : StepLoss f ε K) (n : ℕ) : 0 < f (n + K) := by
  induction n with
  | zero => simpa using hpos
  | succ n ih =>
    have hs := hstep (n + K) (by omega)
    rw [show n + 1 + K = n + K + 1 by omega]
    exact lt_of_lt_of_le (mul_pos (by linarith [hlt (n + K)]) ih) hs

/-- **The reading after `n` steps is at least `f K · e^{−2 Σ losses}`** when every loss is at most
`1/2`.

DERIVED: `2` and `1/2` from `exp_neg_two_mul_le`. -/
theorem tail_lower {f ε : ℕ → ℝ} {K : ℕ} (hpos : 0 < f K) (he0 : ∀ k, 0 ≤ ε k)
    (hhalf : ∀ k, K ≤ k → ε k ≤ 1 / 2) (hstep : StepLoss f ε K) (n : ℕ) :
    f K * Real.exp (-(2 * ∑ i ∈ Finset.range n, ε (i + K))) ≤ f (n + K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := hstep (n + K) (by omega)
    have hh := hhalf (n + K) (by omega)
    have he := exp_neg_two_mul_le (he0 (n + K)) hh
    rw [show n + 1 + K = n + K + 1 by omega]
    calc f K * Real.exp (-(2 * ∑ i ∈ Finset.range (n + 1), ε (i + K)))
        = Real.exp (-(2 * ε (n + K)))
            * (f K * Real.exp (-(2 * ∑ i ∈ Finset.range n, ε (i + K)))) := by
          rw [Finset.sum_range_succ, mul_add, neg_add, Real.exp_add]; ring
      _ ≤ (1 - ε (n + K)) * f (n + K) :=
          mul_le_mul he ih (mul_pos hpos (Real.exp_pos _)).le (by linarith)
      _ ≤ f (n + K + 1) := hs

/-- **A summable step budget from a positive zoom gives a floor on a tail.** -/
theorem noFade_of_stepLoss {f ε : ℕ → ℝ} {K : ℕ} (hb : StepBudget ε) (hpos : 0 < f K)
    (hstep : StepLoss f ε K) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, c ≤ f k := by
  obtain ⟨hε, hsum⟩ := hb
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨K', hK'⟩ : ∃ K', K' = K₁ + K := ⟨_, rfl⟩
  have hposK' : 0 < f K' := by rw [hK']; exact pos_of_stepLoss hpos (fun k => (hε k).2) hstep K₁
  have hstep' : StepLoss f ε K' := fun k hk => hstep k (by omega)
  have hhalf : ∀ k, K' ≤ k → ε k ≤ 1 / 2 := fun k hk => (hK₁ k (by omega)).le
  have hs' : Summable (fun i => ε (i + K')) := (summable_nat_add_iff K').mpr hsum
  refine ⟨f K' * Real.exp (-(2 * ∑' i, ε (i + K'))), mul_pos hposK' (Real.exp_pos _),
    eventually_atTop.mpr ⟨K', fun k hk => ?_⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + K' := ⟨k - K', by omega⟩
  have hle : ∑ i ∈ Finset.range n, ε (i + K') ≤ ∑' i, ε (i + K') :=
    hs'.sum_le_tsum _ (fun i _ => (hε _).1)
  calc f K' * Real.exp (-(2 * ∑' i, ε (i + K')))
      ≤ f K' * Real.exp (-(2 * ∑ i ∈ Finset.range n, ε (i + K'))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hposK'.le
    _ ≤ f (n + K') := tail_lower hposK' (fun k => (hε k).1) hhalf hstep' n

/-- **The step statement gives `NoFadeAtFineEnd`.** -/
theorem noFadeAtFineEnd_of_fineEndStep (h : FineEndStep gLat rLat) : NoFadeAtFineEnd gLat rLat := by
  obtain ⟨ε, K, hb, hpos, hs⟩ := h
  exact noFade_of_stepLoss hb hpos hs

/-- **With link 3, the step statement gives `RatioInvariant`.** -/
theorem ratioInvariant_of_fineEndStep (h3 : OneScale gLat rLat) (h : FineEndStep gLat rLat) :
    ∃ q C : ℝ, 0 < q ∧ RatioInvariant gLat rLat q C :=
  (ratioInvariant_iff_links h3).2 (noFadeAtFineEnd_of_fineEndStep h)

/-- **With link 3, the step statement gives a uniform positive physical gap on the observer's
line.** -/
theorem physical_gap_of_fineEndStep {a : ℕ → ℝ} {r₀ : ℝ} (hr0 : 0 < r₀) (h3 : OneScale gLat rLat)
    (h : FineEndStep gLat rLat) (ha : ∀ k, a k ≠ 0) (hline : ∀ k, rLat k / a k = r₀) :
    ∃ m : ℝ, 0 < m ∧ ∀ k, m ≤ gLat k / a k :=
  physical_gap_of_links hr0 h3 (noFadeAtFineEnd_of_fineEndStep h) ha hline

/-- **Under link 3 the step statement is the budget alone.** -/
theorem fineEndStep_of_oneScale (h3 : OneScale gLat rLat) {ε : ℕ → ℝ} {K : ℕ} (hb : StepBudget ε)
    (hs : StepLoss (ratio gLat rLat) ε K) : FineEndStep gLat rLat :=
  ⟨ε, K, hb, oneScale_ratio_pos h3 K, hs⟩

/-- **No loss at any step**: a positive reading that does not decrease under refinement from `K` on
has a floor on a tail. -/
theorem noFade_of_stepMono {K : ℕ} (hpos : 0 < ratio gLat rLat K)
    (hmono : ∀ k, K ≤ k → ratio gLat rLat k ≤ ratio gLat rLat (k + 1)) :
    NoFadeAtFineEnd gLat rLat :=
  noFadeAtFineEnd_of_fineEndStep ⟨fun _ => 0, K, ⟨fun _ => ⟨le_rfl, one_pos⟩, summable_zero⟩, hpos,
    fun k hk => by simpa using hmono k hk⟩

/-! ## 2. Local, and sufficient only -/

/-- A reading alternating between `2` (even zooms) and `1` (odd zooms).

DERIVED: `2` and `1` the two values. -/
def osc (k : ℕ) : ℝ := if Even k then 2 else 1

/-- **The alternating reading has a floor.** -/
theorem osc_noFade : NoFadeAtFineEnd osc (fun _ => 1) :=
  ⟨1, one_pos, Eventually.of_forall fun k => by
    simp only [ratio, div_one]; unfold osc; split_ifs <;> norm_num⟩

/-- **The alternating reading admits no step budget**: its loss at every even zoom is `1/2`.

DERIVED: `1/2` the loss from `2` to `1`. -/
theorem osc_not_fineEndStep : ¬ FineEndStep osc (fun _ => 1) := by
  rintro ⟨ε, K, ⟨hε, hsum⟩, -, hs⟩
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have h := hs (2 * (K + K₁)) (by omega)
  have hlt := hK₁ (2 * (K + K₁)) (by omega)
  have he : Even (2 * (K + K₁)) := even_two_mul _
  have ho : ¬ Even (2 * (K + K₁) + 1) := by rw [Nat.even_add_one]; exact not_not.2 he
  simp only [ratio, div_one, osc, he, ho, if_true, if_false] at h
  linarith

/-! ## 3. How large the step loss may be -/

/-- **Geometric losses are a budget.** -/
theorem stepBudget_geom {ε : ℕ → ℝ} {D q : ℝ} (hε : ∀ k, 0 ≤ ε k ∧ ε k < 1) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hD : ∀ k, ε k ≤ D * q ^ k) : StepBudget ε :=
  ⟨hε, Summable.of_nonneg_of_le (fun k => (hε k).1) hD
    ((summable_geometric_of_lt_one hq0 hq1).mul_left D)⟩

/-- **The resolution on a geometric zoom line is geometric**:
`(a₀/sᵏ / L)ᵖ = (a₀/L)ᵖ ((sᵖ)⁻¹)ᵏ`. -/
theorem resolution_geom (a0 L s : ℝ) (p k : ℕ) :
    (a0 / s ^ k / L) ^ p = (a0 / L) ^ p * ((s ^ p)⁻¹) ^ k := by
  rw [show a0 / s ^ k / L = a0 / L * (s⁻¹) ^ k by rw [inv_pow]; ring, mul_pow, ← pow_mul,
    mul_comm k p, pow_mul, inv_pow]

/-- **Losses of the size of a power of the resolution are a budget**: on the zoom line
`a k = a₀ / sᵏ`, `s > 1`, `ε k ≤ D (a k / L)ᵖ` with `p ≥ 1`. -/
theorem stepBudget_resolution {ε : ℕ → ℝ} {D a0 L s : ℝ} {p : ℕ} (hε : ∀ k, 0 ≤ ε k ∧ ε k < 1)
    (hs : 1 < s) (hp : p ≠ 0) (hD : ∀ k, ε k ≤ D * (a0 / s ^ k / L) ^ p) : StepBudget ε := by
  refine stepBudget_geom (D := D * (a0 / L) ^ p) (q := (s ^ p)⁻¹) hε
    (inv_nonneg.2 (pow_pos (by linarith) p).le) (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hs hp))
    (fun k => ?_)
  rw [mul_assoc, ← resolution_geom]
  exact hD k

/-- **Losses of the size of the squared coupling are a budget**: `ε k ≤ D / (α + β k)²`,
`α, β > 0`.

DERIVED: `2` the square of the coupling; `1` the shift of the `p`-series. -/
theorem stepBudget_twoLoop {ε : ℕ → ℝ} {D α β : ℝ} (hε : ∀ k, 0 ≤ ε k ∧ ε k < 1) (hα : 0 < α)
    (hβ : 0 < β) (hD : ∀ k : ℕ, ε k ≤ D * ((α + β * k) ^ 2)⁻¹) : StepBudget ε := by
  refine ⟨hε, ?_⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = min α β := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; exact lt_min hα hβ
  have hmα : m ≤ α := by rw [hm_def]; exact min_le_left α β
  have hmβ : m ≤ β := by rw [hm_def]; exact min_le_right α β
  have h2 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_nonneg_of_le (fun k => (hε k).1) (fun k => ?_)
    (h2.mul_left (|D| * (m ^ 2)⁻¹))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk : m * ((k : ℝ) + 1) ≤ α + β * k := by nlinarith
  have hpos : 0 < m * ((k : ℝ) + 1) := mul_pos hm (by linarith)
  have hinv : ((α + β * k) ^ 2)⁻¹ ≤ (m ^ 2)⁻¹ * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hk 2)
  calc ε k ≤ D * ((α + β * k) ^ 2)⁻¹ := hD k
    _ ≤ |D| * ((α + β * k) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity)
    _ ≤ |D| * ((m ^ 2)⁻¹ * (((k : ℝ) + 1) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hinv (abs_nonneg D)
    _ = |D| * (m ^ 2)⁻¹ * (((k : ℝ) + 1) ^ 2)⁻¹ := by ring

/-- **On a geometric zoom line the one-loop inverse coupling at the cutoff is affine in the zoom**:
`1/g²(a₀/sᵏ) = (us − 2b₀ log(a₀/L)) + 2b₀ log s · k`, from `1/g²(L) = us`.

DERIVED: `2b₀` the one-loop normalisation of `invCoup`. -/
theorem invCoup_geometric (b₀ a0 L us s : ℝ) (ha0 : 0 < a0) (hL : 0 < L) (hs : 0 < s) (k : ℕ) :
    invCoup b₀ L us (a0 / s ^ k) = (us - 2 * b₀ * Real.log (a0 / L)) + 2 * b₀ * Real.log s * k := by
  simp only [invCoup]
  rw [show a0 / s ^ k / L = (a0 / L) / s ^ k by ring,
    Real.log_div (div_pos ha0 hL).ne' (pow_pos hs k).ne', Real.log_pow]
  ring

/-- The step loss of `fade`: `1/(k+2)`.

DERIVED: `2` from `fade (k+1) = 1/(k+2)`. -/
def fadeLoss (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

theorem fadeLoss_mem (k : ℕ) : 0 ≤ fadeLoss k ∧ fadeLoss k < 1 := by
  unfold fadeLoss
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

/-- **`fade` loses exactly `fadeLoss k` per step.** -/
theorem fade_stepLoss : StepLoss fade fadeLoss 0 := fun k _ => by
  unfold fade fadeLoss
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [Nat.cast_succ]
  apply le_of_eq
  field_simp
  try ring

/-- **`fadeLoss` is at most `α + β` times `1/(α + β k)`.** -/
theorem fadeLoss_le_coupling {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    fadeLoss k ≤ (α + β) * (α + β * k)⁻¹ := by
  unfold fadeLoss
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 0 < α + β * k := by nlinarith
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by linarith) h1]
  nlinarith [mul_nonneg hα.le hk]

/-- **A loss of the size of the coupling per step does not give the floor.** `fade` loses
`fadeLoss k` per step, each loss in `[0, 1)` and at most `(α + β) / (α + β k)`, the losses are not
summable, and `fade` has no floor on any tail. -/
theorem perturbative_budget_admits_fade {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    StepLoss (ratio fade (fun _ => 1)) fadeLoss 0 ∧ (∀ k, 0 ≤ fadeLoss k ∧ fadeLoss k < 1) ∧
      (∀ k : ℕ, fadeLoss k ≤ (α + β) * (α + β * k)⁻¹) ∧ ¬ Summable fadeLoss ∧
      ¬ NoFadeAtFineEnd fade (fun _ => 1) := by
  have hno := links_not_sufficient.2.2
  refine ⟨by rw [ratio_fade_one]; exact fade_stepLoss, fadeLoss_mem, fadeLoss_le_coupling hα hβ,
    fun hs => hno ?_, hno⟩
  exact noFade_of_stepLoss (K := 0) ⟨fadeLoss_mem, hs⟩ (by rw [ratio_fade_one]; exact fade_pos 0)
    (by rw [ratio_fade_one]; exact fade_stepLoss)

/-- **A loss of the size of the one-loop `g²` at the cutoff does not give the floor.** On the zoom
line `a k = a₀/sᵏ`, `s > 1`, with `b₀ > 0` and `1/g²(a₀) > 0` (from `1/g²(L) = us`), the loss of
`fade` is at most `C · g²(a k)` with `C = 1/g²(a₀) + 2b₀ log s`. -/
theorem oneLoop_budget_admits_fade {b₀ a0 L us s : ℝ} (hb : 0 < b₀) (ha0 : 0 < a0) (hL : 0 < L)
    (hs : 1 < s) (hα : 0 < us - 2 * b₀ * Real.log (a0 / L)) :
    (∀ k : ℕ, fadeLoss k ≤ ((us - 2 * b₀ * Real.log (a0 / L)) + 2 * b₀ * Real.log s)
        * (invCoup b₀ L us (a0 / s ^ k))⁻¹) ∧ ¬ Summable fadeLoss ∧
      ¬ NoFadeAtFineEnd fade (fun _ => 1) := by
  have hβ : 0 < 2 * b₀ * Real.log s := mul_pos (by linarith) (Real.log_pos hs)
  obtain ⟨-, -, -, hns, hno⟩ := perturbative_budget_admits_fade hα hβ
  refine ⟨fun k => ?_, hns, hno⟩
  rw [invCoup_geometric b₀ a0 L us s ha0 hL (by linarith) k]
  exact fadeLoss_le_coupling hα hβ k

/-! ## 4. Controls -/

/-- Without the floor, no step statement. -/
theorem not_fineEndStep_of_not_noFade (h : ¬ NoFadeAtFineEnd gLat rLat) : ¬ FineEndStep gLat rLat :=
  fun hs => h (noFadeAtFineEnd_of_fineEndStep hs)

/-- **A gap reading that vanishes at every fine zoom fails the step statement** (the `U(1)`
Coulomb-phase photon is cited, not proved here, as an instance; there the observer's string tension
vanishes too, so the physical ratio is `0/0` and the Lean value `0` uses `x / 0 = 0`). -/
theorem fineEndStep_fails_of_gap_zero (hz : ∀ᶠ k in atTop, gLat k = 0) : ¬ FineEndStep gLat rLat := by
  refine not_fineEndStep_of_not_noFade ?_
  rintro ⟨c, hc, ht⟩
  obtain ⟨k, hk1, hk2⟩ := (ht.and hz).exists
  simp only [ratio, hk2, zero_div] at hk1
  linarith

/-- **An observer reading that vanishes at every fine zoom fails the step statement** (with Lean's
`x / 0 = 0`; zero string tension in the 4D `Z_N` deconfined phase and the `U(1)` Coulomb phase is
cited, not proved here, as an instance). Physically, link 3 (`OneScale`) fails there. -/
theorem fineEndStep_fails_of_observer_zero (hz : ∀ᶠ k in atTop, rLat k = 0) :
    ¬ FineEndStep gLat rLat := by
  refine not_fineEndStep_of_not_noFade ?_
  rintro ⟨c, hc, ht⟩
  obtain ⟨k, hk1, hk2⟩ := (ht.and hz).exists
  simp only [ratio, hk2, div_zero] at hk1
  linarith

/-- **The `fade` line fails the step statement.** -/
theorem fineEndStep_fails_fade : ¬ FineEndStep fade (fun _ => 1) :=
  not_fineEndStep_of_not_noFade links_not_sufficient.2.2

/-- The step loss of the jump: `1/2` before zoom `k₁`, `0` after.

DERIVED: `1/2` the loss from `2` to `1`. -/
def jumpLoss (k₁ k : ℕ) : ℝ := if k < k₁ then 1 / 2 else 0

/-- **A finite downward jump satisfies the step statement** (the model of a first-order bulk
transition; such transitions are cited, not proved here). -/
theorem jump_fineEndStep (k₁ : ℕ) : FineEndStep (stepProfile k₁ 2 1) (fun _ => 1) := by
  have hr : ratio (stepProfile k₁ 2 1) (fun _ => 1) = stepProfile k₁ 2 1 := by
    funext k; simp [ratio]
  refine ⟨jumpLoss k₁, 0, ⟨fun k => ?_, ?_⟩, ?_, ?_⟩
  · unfold jumpLoss; split_ifs <;> norm_num
  · exact summable_of_ne_finset_zero (s := Finset.range k₁) (fun b hb => by
      simp only [Finset.mem_range] at hb; simp [jumpLoss, hb])
  · rw [hr]; unfold stepProfile; split_ifs <;> norm_num
  · rw [hr]; intro k _; unfold jumpLoss stepProfile; split_ifs <;> norm_num

#print axioms exp_neg_two_mul_le
#print axioms pos_of_stepLoss
#print axioms tail_lower
#print axioms noFade_of_stepLoss
#print axioms noFadeAtFineEnd_of_fineEndStep
#print axioms ratioInvariant_of_fineEndStep
#print axioms physical_gap_of_fineEndStep
#print axioms fineEndStep_of_oneScale
#print axioms noFade_of_stepMono
#print axioms osc_noFade
#print axioms osc_not_fineEndStep
#print axioms stepBudget_geom
#print axioms resolution_geom
#print axioms stepBudget_resolution
#print axioms stepBudget_twoLoop
#print axioms invCoup_geometric
#print axioms fade_stepLoss
#print axioms fadeLoss_le_coupling
#print axioms perturbative_budget_admits_fade
#print axioms oneLoop_budget_admits_fade
#print axioms fineEndStep_fails_of_gap_zero
#print axioms fineEndStep_fails_of_observer_zero
#print axioms fineEndStep_fails_fade
#print axioms jump_fineEndStep

end MassGap.FineEnd
