import Mathlib
import MassGap.GaugeRunning
import MassGap.FluxSplitCasimir

/-!
# MassGap.RunningCrossover — what the running coupling supplies to the strong end, and what it cannot

What separates `SU(N)` from `U(1)` and `Z₂` is asymptotic freedom (`b₀ > 0`: the coupling at the scale of a window
grows with the window) and the absence of a bulk transition. This module states both on the tree's objects and
proves what each carries toward `CouplingTower.StrongEnd`, `CasimirStep.NoCasimirAt` and
`FluxSplitCasimir.FluxConfinedAt`. Declarations are in the namespace `MassGap.RunningCrossover`.

## 1. The perturbative running (proved)

At the Lean coupling the two-loop spacing of `GaugeRunning` is `aRunG G β = (k β)^{51/121} e^{−kβ/2}` with
`k = kG G = 96π² T(ρ)/(11 h^∨ d)` (`aRunG_eq`). The one-loop step of the bare coupling per doubling of the length
is `runStepG G = 2 log 2 / k = (d/T) b₀ log 2` (`runStepG_eq`), positive because `b₀ > 0` (`runStepG_pos`). At
`SU(2)` it is `(11/(6π²)) log 2`, the `b log 2` of `ToronDecrement`.

* `aOneG_sub_step`, `aOneG_sub_nsmul`: the one-loop spacing `aOneG G β = e^{−kβ/2}` doubles exactly when `β`
  drops by one step: the one-loop running coupling at the length `2^n a(β)` is `β − n · runStepG G`.
* `oneLoop_crossing`: from every `β` above a level `β*`, the one-loop running reaches `β*` at a window `W` with
  `2^W aOneG β ∈ [aOneG β*, 2 aOneG β*)`. The crossing sits at one physical length, the same at every `β`;
  only the number of doublings grows with `β`.
* `twoLoop_step_le`: on the decreasing branch, a two-loop doubling (`aRunG β' = 2 aRunG β`, `0 < β' ≤ β`)
  lowers the coupling by at least the one-loop step (`b₁ > 0`: no two-loop fixed point).
  `twoLoop_run_le`, `twoLoop_doublings_lt`: along any chain of two-loop doublings `β n ≤ β 0 − n · runStepG G`,
  so fewer than `(β 0 − β*)/runStepG G` doublings stay above any level `β*`, uniformly.
* `aRunG_bounded`, `twoLoop_exits`: the two-loop spacing is bounded on `β ≥ 0`, so at every `β > 0` the length
  `2^w aRunG β` exceeds every value of the spacing past finitely many doublings: the perturbative running leaves
  its own domain at a finite window.
* `exits_iff`, `exits_oneLoop_iff`: a one-loop flow `β ↦ β − c` reaches every level from every start exactly when
  `c > 0`; for the coefficient `oneLoopStep h d T` of a group with dual Coxeter number `h`, exactly when `h > 0`.
  `abelian_no_exit`: at `h = 0` (pure `U(1)`, `b₀ = 0`) it never leaves. With charged matter (`b₀ < 0`) the failure
  is `exits_oneLoop_iff` at `h < 0`.

## 2. The step-scaling input on the window coupling (defined; consequences proved)

For a window reading `g` (the tree's is `windowCoupling N β w = defectW N β (2^w)`):

* `StepDropOn g a b`: some `δ > 0` such that at every `β ≥ 0` and window `w ≥ 1` with `g β w ∈ [a, b]`, one
  doubling lowers the reading by at least `δ`.
* `NoStepFixedPoint g`: `StepDropOn g a b` on every compact band `0 < a ≤ b`. The lattice step-scaling map of the
  reading has no fixed point in `(0, ∞)`, uniformly on compact bands. No map, no threshold, no start window.
* `WilsonNoStepFixedPoint N := NoStepFixedPoint (windowCoupling N)`: the named open input.

Proved:

* `stepDropOn_mono`, `stepDropOn_union`, `stepDrop_above_of_bands`: bands glue.
* `basin_stepDrop`: below the basin edge every band is a theorem (`DoublingSharp`, `basin_contracts`).
  `wilsonNoStep_iff`: so `WilsonNoStepFixedPoint N` is equivalent to its part above one basin edge `a₀ > 0`.
* `exists_lt_of_stepDropOn`, `vanishing_of_wilsonNoStep`: the input makes the window coupling vanish at every
  `β ≥ 0`. `noCasimir_of_wilsonNoStep`, `strongEnd_of_wilsonNoStep`, `sectors_of_wilsonNoStep` (flux confinement
  and neutral binding at every `β ≥ 0`), `windowGap_of_wilsonNoStep` (the periodic Clay gap at every `β ≥ 0`).
* `noStepFixedPoint_of_selfSimilar`: `SelfSimilarStep.SelfSimilar` gives it when the first-window readings are
  unbounded in `β` (compactness of each band). The converse (a continuous map from band-wise drops) is not built.

## 3. What the running supplies to the input, and what it cannot

* `stepDropOn_of_covariantOn` (supplies): where the reading is a continuous strictly increasing function `H` of
  the running coupling at the window's scale (`g β w = H(β − w c)`, and one-sided at the next window), with
  `c > 0`, every band of that region is a band of `StepDropOn`. The drop is `H t − H(t − c) > 0`, minimized on
  the band. This is how asymptotic freedom would supply the weak band (the reading above some `G`), argued from
  the covariance hypothesis of this theorem together with the running term `−(45/2) b log 2/β`;
  `ToronDecrement.ToronLaplace`'s own step bound, of order `α 4^{−w}`, gives no uniform drop. It is not proved on
  `windowCoupling`.
* `not_exactCovariant` (cannot): no injective `H` and no `c ≠ 0` make `windowCoupling N β w = H(β − w c)` at
  every `β ≥ 0` and `w ≥ 1`, because the reading is `0` at `β = 0` at every window. The reading is not a function
  of the running coupling through the strong-coupling end; with §1, the perturbative running leaves its domain at
  a fixed physical length and says nothing past it.
* The band between the basin edge and the weak band, reached at that fixed physical length, is the crossover.
  Nothing in this module or in the tree supplies its drop: it is the intermediate-coupling renormalization-group
  problem (Bałaban type), here in one parameter-free form.

## 4. Tests

* Abelian and `Z₂`. `not_noStepFixedPoint_of_rise`: a positive reading that does not fall at one doubling fails the
  input. `not_noStepFixedPoint_of_limit`, `not_noStepFixedPoint_of_const`: a reading with a positive limit along
  the windows at one `β ≥ 0` fails it (a Coulomb line for `U(1)`; the deconfined phase of `Z₂`, where the
  topological flux sectors keep a positive limit: argued, the tree does not compute either reading). On the
  running side, the one-loop flow at `b₀ = 0` (`abelian_no_exit`) or `b₀ < 0` (`exits_oneLoop_iff` at `h < 0`)
  never leaves weak coupling (proved); `Z₂` has no Lie algebra and no
  continuous running, and its weak-coupling phase is separated from the confined one by a first-order transition
  (cited, Creutz–Jacobs–Rebbi 1979), so no band-wise drop connects the two: argued.
* Degenerate. `noStepFixedPoint_const_zero`: the ultralocal reading `g ≡ 0` satisfies the input vacuously; at
  `β = 0` the Wilson reading is `0` (`CouplingTower.windowCoupling_zero`) and every band is empty there.
* Strength. The input implies the periodic Clay gap at every `β ≥ 0`, and it implies `StrongEnd`; no converse is
  proved. It is a sufficient condition, at least as strong as `NoCasimir N`.

DERIVED (module-wide): `0` the trivial reading, the signs and the abelian dual Coxeter number; `1` the least window
index and the step; `2` the doubling (and `2 log 2 = k · runStepG`); `51/121` the two-loop exponent
`b₁/(2b₀²)` (`GaugeRunning.exponent_eq`); `96 = 2 · 48`, with `48π²` and `11` from `b0G` and `2` the plane
orderings of the Lean coupling. Proof-internal constants: `1/1000` and `3/4` (the basin seed and the drop `1 − 1/4`
of `basin_contracts`), the bound `2` on the two-loop spacing, the width `min (L/2) (δ/2)` and the drop `1` of the
vacuous case; none is in a statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.RunningCrossover

open Filter Topology Real
open MassGap.GaugeRunning
open MassGap.CouplingTower (windowCoupling StrongEnd tendsto_zero_of_seed)
open MassGap.SelfSimilarStep (SelfSimilar)

/-! ## 1. The perturbative running -/

section Running

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G] [GaugeSimple G]

/-- **The scale factor of the two-loop spacing** at the Lean coupling, `k = 96π² T(ρ)/(11 h^∨ d)`.
DERIVED: `96 = 2 · 48`, `48π²` and `11` from `b0G`, `2` the plane orderings. -/
def kG : ℝ := 96 * π ^ 2 * TG G / (11 * hG G * dG G)

theorem kG_pos : 0 < kG G := by
  unfold kG
  have := hG_pos (G := G)
  have := TG_pos (G := G)
  have := dG_pos (G := G)
  positivity

/-- **The two-loop spacing in the scale variable**: `aRunG G β = (k β)^{51/121} e^{−kβ/2}`.
DERIVED: `51/121` the two-loop exponent; `2` the `1/(2 b₀ g²)` of the exponential. -/
theorem aRunG_eq (β : ℝ) : aRunG G β = (kG G * β) ^ (51 / 121 : ℝ) * Real.exp (-(kG G * β / 2)) := by
  rw [aRunG, aRunStdG_eq]
  have e1 : 48 * π ^ 2 * TG G * (2 * β) / (11 * hG G * dG G) = kG G * β := by unfold kG; ring
  have e2 : 24 * π ^ 2 * TG G * (2 * β) / (11 * hG G * dG G) = kG G * β / 2 := by unfold kG; ring
  rw [e1, e2]

/-- **The one-loop step of the bare coupling per doubling**, `2 log 2 / k`. DERIVED: the factor `2` is the
`1/(2 b₀ g²)` of the one-loop spacing; the `2` inside `log 2` the doubling. -/
def runStepG : ℝ := 2 * Real.log 2 / kG G

/-- DERIVED: the factor `2` is the `1/(2 b₀ g²)` of the one-loop spacing; the `2` inside `log 2` the doubling. -/
theorem kG_mul_runStep : kG G * runStepG G = 2 * Real.log 2 := by
  have := (kG_pos G).ne'
  unfold runStepG
  field_simp

/-- **The step is `(d/T) b₀ log 2`.** DERIVED: `2` the doubling. -/
theorem runStepG_eq : runStepG G = dG G / TG G * b0G G * Real.log 2 := by
  have hh := (hG_pos (G := G)).ne'
  have hT := (TG_pos (G := G)).ne'
  have hd := (dG_pos (G := G)).ne'
  have hp : π ≠ 0 := Real.pi_ne_zero
  unfold runStepG kG b0G
  first | (field_simp; done) | (field_simp; ring)

/-- **Asymptotic freedom: the step is positive.** DERIVED: `0` the sign. -/
theorem runStepG_pos : 0 < runStepG G := by
  have := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
  exact div_pos (by linarith) (kG_pos G)

/-- **The one-loop spacing** `e^{−kβ/2}`. DERIVED: `2` the `1/(2 b₀ g²)`. -/
def aOneG (β : ℝ) : ℝ := Real.exp (-(kG G * β / 2))

/-- **One step down in the coupling doubles the one-loop spacing.** DERIVED: `2` the doubling. -/
theorem aOneG_sub_step (β : ℝ) : aOneG G (β - runStepG G) = 2 * aOneG G β := by
  have hk := kG_mul_runStep G
  unfold aOneG
  have e : -(kG G * (β - runStepG G) / 2) = Real.log 2 + -(kG G * β / 2) := by
    have h' : kG G * (β - runStepG G) = kG G * β - 2 * Real.log 2 := by rw [mul_sub, hk]
    rw [h']
    ring
  rw [e, Real.exp_add, Real.exp_log two_pos]

/-- **`n` steps down multiply the one-loop spacing by `2^n`.** DERIVED: `2` the doubling. -/
theorem aOneG_sub_nsmul (β : ℝ) (n : ℕ) : aOneG G (β - n * runStepG G) = 2 ^ n * aOneG G β := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : β - ((n + 1 : ℕ) : ℝ) * runStepG G = (β - n * runStepG G) - runStepG G := by push_cast; ring
    rw [e, aOneG_sub_step, ih, pow_succ]
    ring

theorem aOneG_strictAnti : StrictAnti (aOneG G) := by
  intro x y hxy
  have := mul_lt_mul_of_pos_left hxy (kG_pos G)
  exact Real.exp_lt_exp.mpr (by linarith)

/-- **The one-loop running crosses every level at one physical length.** From `β ≥ β*`, the running coupling
`β − W · runStepG G` reaches `β*` within one step at a window `W` with `2^W aOneG β ∈ [aOneG β*, 2 aOneG β*)`.
DERIVED: `2` the doubling. -/
theorem oneLoop_crossing {β βs : ℝ} (h : βs ≤ β) : ∃ W : ℕ,
    β - W * runStepG G ≤ βs ∧ βs < β - W * runStepG G + runStepG G ∧
    aOneG G βs ≤ 2 ^ W * aOneG G β ∧ 2 ^ W * aOneG G β < 2 * aOneG G βs := by
  have hc := runStepG_pos G
  have hq : 0 ≤ (β - βs) / runStepG G := div_nonneg (by linarith) hc.le
  have h1 : (β - βs) / runStepG G ≤ (⌈(β - βs) / runStepG G⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈(β - βs) / runStepG G⌉₊ : ℝ) < (β - βs) / runStepG G + 1 := Nat.ceil_lt_add_one hq
  have hqc : (β - βs) / runStepG G * runStepG G = β - βs := div_mul_cancel₀ _ hc.ne'
  have m1 := mul_le_mul_of_nonneg_right h1 hc.le
  have m2 := mul_lt_mul_of_pos_right h2 hc
  have hlo : β - (⌈(β - βs) / runStepG G⌉₊ : ℝ) * runStepG G ≤ βs := by nlinarith
  have hhi : βs < β - (⌈(β - βs) / runStepG G⌉₊ : ℝ) * runStepG G + runStepG G := by nlinarith
  refine ⟨⌈(β - βs) / runStepG G⌉₊, hlo, hhi, ?_, ?_⟩
  · rw [← aOneG_sub_nsmul]
    exact (aOneG_strictAnti G).antitone hlo
  · rw [← aOneG_sub_nsmul, ← aOneG_sub_step]
    exact aOneG_strictAnti G (by linarith)

/-- **A two-loop doubling lowers the coupling by at least the one-loop step** (on the decreasing branch).
DERIVED: `0` the sign; `2` the doubling. -/
theorem twoLoop_step_le {β β' : ℝ} (h0 : 0 < β') (hle : β' ≤ β) (h : aRunG G β' = 2 * aRunG G β) :
    β' ≤ β - runStepG G := by
  have hk := kG_pos G
  rw [aRunG_eq, aRunG_eq] at h
  have hy' : 0 < kG G * β' := mul_pos hk h0
  have hyy : kG G * β' ≤ kG G * β := mul_le_mul_of_nonneg_left hle hk.le
  have hy : 0 < kG G * β := lt_of_lt_of_le hy' hyy
  have hp : (kG G * β') ^ (51 / 121 : ℝ) ≤ (kG G * β) ^ (51 / 121 : ℝ) :=
    Real.rpow_le_rpow hy'.le hyy (by norm_num)
  have hP : 0 < (kG G * β) ^ (51 / 121 : ℝ) := Real.rpow_pos_of_pos hy _
  have he' : 0 < Real.exp (-(kG G * β' / 2)) := Real.exp_pos _
  have h2 : 2 * Real.exp (-(kG G * β / 2)) ≤ Real.exp (-(kG G * β' / 2)) := by
    have hm : (kG G * β) ^ (51 / 121 : ℝ) * (2 * Real.exp (-(kG G * β / 2)))
        ≤ (kG G * β) ^ (51 / 121 : ℝ) * Real.exp (-(kG G * β' / 2)) := by
      calc _ = 2 * ((kG G * β) ^ (51 / 121 : ℝ) * Real.exp (-(kG G * β / 2))) := by ring
        _ = (kG G * β') ^ (51 / 121 : ℝ) * Real.exp (-(kG G * β' / 2)) := h.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hp he'.le
    exact le_of_mul_le_mul_left hm hP
  have h3 : Real.exp (Real.log 2 + -(kG G * β / 2)) ≤ Real.exp (-(kG G * β' / 2)) := by
    rw [Real.exp_add, Real.exp_log two_pos]
    exact h2
  have h4 := Real.exp_le_exp.mp h3
  have h5 : kG G * β' ≤ kG G * (β - runStepG G) := by
    rw [mul_sub, kG_mul_runStep]
    linarith
  exact le_of_mul_le_mul_left h5 hk

/-- **Along a chain of two-loop doublings the coupling falls at least linearly**: `β n ≤ β 0 − n · runStepG G`.
DERIVED: `0` the sign; `1` the step; `2` the doubling. -/
theorem twoLoop_run_le {β : ℕ → ℝ} {n : ℕ}
    (h : ∀ k < n, 0 < β (k + 1) ∧ β (k + 1) ≤ β k ∧ aRunG G (β (k + 1)) = 2 * aRunG G (β k)) :
    β n ≤ β 0 - n * runStepG G := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => h k (by omega))
    obtain ⟨h0, hle, hr⟩ := h n (by omega)
    have := twoLoop_step_le G h0 hle hr
    push_cast
    linarith

/-- **Fewer than `(β 0 − β*)/runStepG G` two-loop doublings stay above a level `β*`.**
DERIVED: `0` the sign; `1` the step; `2` the doubling. -/
theorem twoLoop_doublings_lt {β : ℕ → ℝ} {n : ℕ}
    (h : ∀ k < n, 0 < β (k + 1) ∧ β (k + 1) ≤ β k ∧ aRunG G (β (k + 1)) = 2 * aRunG G (β k))
    {βs : ℝ} (hs : βs < β n) : (n : ℝ) * runStepG G < β 0 - βs := by
  have := twoLoop_run_le G h
  linarith

theorem aRunG_pos {β : ℝ} (hβ : 0 < β) : 0 < aRunG G β := by
  rw [aRunG_eq]
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos (kG_pos G) hβ) _) (Real.exp_pos _)

private theorem rpow_mul_exp_le {y : ℝ} (hy : 0 ≤ y) :
    y ^ (51 / 121 : ℝ) * Real.exp (-(y / 2)) ≤ 2 := by
  have h1 : y ^ (51 / 121 : ℝ) ≤ 1 + y := by
    rcases le_total y 1 with hy1 | hy1
    · have := Real.rpow_le_one hy hy1 (by norm_num : (0 : ℝ) ≤ 51 / 121)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num : (51 / 121 : ℝ) ≤ 1)
      rw [Real.rpow_one] at this
      linarith
  have h2 : 1 + y ≤ 2 * Real.exp (y / 2) := by
    have := Real.add_one_le_exp (y / 2)
    linarith
  have he : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos : 0 < Real.exp (-(y / 2)) := Real.exp_pos _
  calc y ^ (51 / 121 : ℝ) * Real.exp (-(y / 2)) ≤ (1 + y) * Real.exp (-(y / 2)) :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ ≤ 2 * Real.exp (y / 2) * Real.exp (-(y / 2)) := mul_le_mul_of_nonneg_right h2 hpos.le
    _ = 2 := by rw [mul_assoc, he, mul_one]

/-- **The two-loop spacing is bounded on `β ≥ 0`.** DERIVED: `0` the sign. Proof-internal: the bound `2`. -/
theorem aRunG_bounded : ∃ M : ℝ, ∀ β : ℝ, 0 ≤ β → aRunG G β ≤ M :=
  ⟨2, fun β hβ => by
    rw [aRunG_eq]
    exact rpow_mul_exp_le (mul_nonneg (kG_pos G).le hβ)⟩

/-- **The two-loop running leaves its domain after finitely many doublings**: at every `β > 0`, past some window
`W` the length `2^w aRunG β` exceeds every value of the spacing. DERIVED: `0` the signs; `2` the doubling. -/
theorem twoLoop_exits {β : ℝ} (hβ : 0 < β) : ∃ W : ℕ, ∀ w : ℕ, W ≤ w → ∀ β' : ℝ, 0 ≤ β' →
    aRunG G β' < 2 ^ w * aRunG G β := by
  obtain ⟨M, hM⟩ := aRunG_bounded G
  have ha := aRunG_pos G hβ
  obtain ⟨W, hW⟩ := pow_unbounded_of_one_lt (M / aRunG G β) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨W, fun w hw β' hβ' => ?_⟩
  have h1 : (2 : ℝ) ^ W ≤ 2 ^ w := pow_le_pow_right₀ one_le_two hw
  have h2 : M < 2 ^ w * aRunG G β := (div_lt_iff₀ ha).mp (lt_of_lt_of_le hW h1)
  exact lt_of_le_of_lt (hM β' hβ') h2

end Running

/-- **A one-loop flow `β ↦ β − c` reaches every level from every start exactly when `c > 0`.**
DERIVED: `0` the sign. -/
theorem exits_iff (c : ℝ) : (∀ β βs : ℝ, ∃ w : ℕ, β - w * c < βs) ↔ 0 < c := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := h 0 0
    by_contra hc
    have : (w : ℝ) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg w) (not_lt.mp hc)
    linarith
  · intro hc β βs
    obtain ⟨w, hw⟩ := exists_nat_gt ((β - βs) / c)
    refine ⟨w, ?_⟩
    have := (div_lt_iff₀ hc).mp hw
    linarith

/-- **The one-loop step of a group with dual Coxeter number `h`**, representation dimension `d` and Dynkin index
`T`: `(d/T) (11h/(48π²)) log 2`. DERIVED: `11`, `48π²` the one-loop coefficient; `2` the doubling. -/
def oneLoopStep (h d T : ℝ) : ℝ := d / T * (11 * h / (48 * π ^ 2)) * Real.log 2

theorem runStepG_eq_oneLoopStep (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    [GaugeSimple G] : runStepG G = oneLoopStep (hG G) (dG G) (TG G) := by
  rw [runStepG_eq]
  rfl

/-- **The one-loop flow leaves weak coupling exactly when `h > 0`.** DERIVED: `0` the signs. -/
theorem exits_oneLoop_iff {h d T : ℝ} (hd : 0 < d) (hT : 0 < T) :
    (∀ β βs : ℝ, ∃ w : ℕ, β - w * oneLoopStep h d T < βs) ↔ 0 < h := by
  rw [exits_iff]
  have hK : 0 < d / T * (11 / (48 * π ^ 2)) * Real.log 2 := by
    have := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
    positivity
  have e : oneLoopStep h d T = d / T * (11 / (48 * π ^ 2)) * Real.log 2 * h := by unfold oneLoopStep; ring
  rw [e]
  exact ⟨fun hp => by
    by_contra hh
    have := mul_nonpos_of_nonneg_of_nonpos hK.le (not_lt.mp hh)
    linarith, fun hh => mul_pos hK hh⟩

/-- **Abelian test: at `h = 0` the one-loop flow never leaves weak coupling.** DERIVED: `0` the abelian dual
Coxeter number and the signs of `d` and `T`. -/
theorem abelian_no_exit {d T : ℝ} (hd : 0 < d) (hT : 0 < T) :
    ¬ ∀ β βs : ℝ, ∃ w : ℕ, β - w * oneLoopStep 0 d T < βs := by
  rw [exits_oneLoop_iff hd hT]
  exact lt_irrefl 0

/-! ## 2. The step-scaling input -/

section Step

variable {g : ℝ → ℕ → ℝ}

/-- **One doubling lowers every reading of the band `[a, b]` by at least some `δ > 0`**, at every `β ≥ 0` and
window `w ≥ 1`. DERIVED: `0` the signs; `1` the least window index and the step. -/
def StepDropOn (g : ℝ → ℕ → ℝ) (a b : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → a ≤ g β w → g β w ≤ b →
    g β (w + 1) + δ ≤ g β w

/-- **The step-scaling map has no fixed point in `(0, ∞)`**, uniformly on every compact band.
DERIVED: `0` the trivial reading. -/
def NoStepFixedPoint (g : ℝ → ℕ → ℝ) : Prop := ∀ a b : ℝ, 0 < a → a ≤ b → StepDropOn g a b

theorem stepDropOn_mono {a b a' b' : ℝ} (h : StepDropOn g a b) (ha : a ≤ a') (hb : b' ≤ b) :
    StepDropOn g a' b' := by
  obtain ⟨δ, hδ, hd⟩ := h
  exact ⟨δ, hδ, fun β hβ w hw h1 h2 => hd β hβ w hw (ha.trans h1) (h2.trans hb)⟩

theorem stepDropOn_union {a m b : ℝ} (h1 : StepDropOn g a m) (h2 : StepDropOn g m b) : StepDropOn g a b := by
  obtain ⟨δ₁, hδ₁, hd₁⟩ := h1
  obtain ⟨δ₂, hδ₂, hd₂⟩ := h2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun β hβ w hw ha hb => ?_⟩
  rcases le_total (g β w) m with hm | hm
  · have := hd₁ β hβ w hw ha hm
    linarith [min_le_left δ₁ δ₂]
  · have := hd₂ β hβ w hw hm hb
    linarith [min_le_right δ₁ δ₂]

/-- **A crossover band and a weak band give every band above the basin edge.** No numerals. -/
theorem stepDrop_above_of_bands {a₀ G : ℝ} (hcross : StepDropOn g a₀ G)
    (hweak : ∀ b : ℝ, G ≤ b → StepDropOn g G b) : ∀ b : ℝ, a₀ ≤ b → StepDropOn g a₀ b := by
  intro b _
  rcases le_total b G with h | h
  · exact stepDropOn_mono hcross le_rfl h
  · exact stepDropOn_union hcross (hweak b h)

/-- **A band below the first-window reading is left in finitely many doublings.**
DERIVED: `0` the sign; `1` the first window. -/
theorem exists_lt_of_stepDropOn {a b β : ℝ} (hβ : 0 ≤ β) (h : StepDropOn g a b) (hb : g β 1 ≤ b) :
    ∃ w : ℕ, 1 ≤ w ∧ g β w < a := by
  obtain ⟨δ, hδ, hd⟩ := h
  by_contra hne
  have hall : ∀ w : ℕ, 1 ≤ w → a ≤ g β w := fun w hw => by
    by_contra hlt
    exact hne ⟨w, hw, not_le.mp hlt⟩
  have key : ∀ k : ℕ, g β (k + 1) ≤ g β 1 - k * δ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ.le
      have hs := hd β hβ (k + 1) (by omega) (hall (k + 1) (by omega)) (by linarith)
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((g β 1 - a) / δ)
  have h1 := key k
  have h2 := hall (k + 1) (by omega)
  have h3 := (div_lt_iff₀ hδ).mp hk
  linarith

/-- **`SelfSimilar` gives the input** when the first-window readings are unbounded in `β`.
DERIVED: `0` the signs; `1` the first window. -/
theorem noStepFixedPoint_of_selfSimilar (h : SelfSimilar g)
    (hub : ∀ x : ℝ, ∃ β : ℝ, 0 ≤ β ∧ x ≤ g β 1) : NoStepFixedPoint g := by
  obtain ⟨Φ, hΦ, hmap, -, hfix⟩ := h
  intro a b ha hab
  have hcont : Continuous fun x => x - Φ x := continuous_id.sub hΦ
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_isMinOn
    (Set.nonempty_Icc.mpr hab) hcont.continuousOn
  obtain ⟨β₀, hβ₀, hb⟩ := hub b
  have hpos : 0 < x₀ - Φ x₀ := by
    have := hfix β₀ hβ₀ x₀ (lt_of_lt_of_le ha hx₀.1) (hx₀.2.trans hb)
    linarith
  refine ⟨x₀ - Φ x₀, hpos, fun β hβ w hw h1 h2 => ?_⟩
  have hm : x₀ - Φ x₀ ≤ g β w - Φ (g β w) := isMinOn_iff.mp hmin _ ⟨h1, h2⟩
  have hs := hmap β hβ w hw
  linarith

/-- **Where the reading is a function of the running coupling, the running supplies the drop.** If on the band
`[H t₁, H t₂]` the reading is `H(β − w c)` with `H` continuous and strictly increasing, `c > 0`, and the next
window is at most `H(β − (w+1) c)`, then `StepDropOn g (H t₁) (H t₂)`.
DERIVED: `0` the signs; `1` the least window index and the step. -/
theorem stepDropOn_of_covariantOn {H : ℝ → ℝ} (hHc : Continuous H) (hHm : StrictMono H)
    {c : ℝ} (hc : 0 < c) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂)
    (hcov : ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → H t₁ ≤ g β w → g β w ≤ H t₂ →
      g β w = H (β - w * c) ∧ g β (w + 1) ≤ H (β - ((w + 1 : ℕ) : ℝ) * c)) :
    StepDropOn g (H t₁) (H t₂) := by
  have hcont : Continuous fun t => H t - H (t - c) :=
    hHc.sub (hHc.comp (continuous_id.sub continuous_const))
  obtain ⟨s₀, -, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc t₁ t₂)).exists_isMinOn
    (Set.nonempty_Icc.mpr ht) hcont.continuousOn
  have hpos : 0 < H s₀ - H (s₀ - c) := sub_pos.mpr (hHm (by linarith))
  refine ⟨H s₀ - H (s₀ - c), hpos, fun β hβ w hw h1 h2 => ?_⟩
  obtain ⟨he, hs⟩ := hcov β hβ w hw h1 h2
  have h1' : H t₁ ≤ H (β - w * c) := by rw [← he]; exact h1
  have h2' : H (β - w * c) ≤ H t₂ := by rw [← he]; exact h2
  have hm : H s₀ - H (s₀ - c) ≤ H (β - w * c) - H (β - w * c - c) :=
    isMinOn_iff.mp hmin _ ⟨hHm.le_iff_le.mp h1', hHm.le_iff_le.mp h2'⟩
  have e : β - ((w + 1 : ℕ) : ℝ) * c = β - w * c - c := by push_cast; ring
  rw [e] at hs
  rw [he]
  linarith

/-- **A positive reading that does not fall at one doubling fails the input.** DERIVED: `0` the signs; `1` the
least window index and the step. -/
theorem not_noStepFixedPoint_of_rise {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (hpos : 0 < g β w)
    (hrise : g β w ≤ g β (w + 1)) : ¬ NoStepFixedPoint g := by
  intro h
  obtain ⟨δ, hδ, hd⟩ := h (g β w) (g β w) hpos le_rfl
  have := hd β hβ w hw le_rfl le_rfl
  linarith

/-- **A reading with a positive limit along the windows fails the input** (a Coulomb line; a deconfined phase).
DERIVED: `0` the signs. -/
theorem not_noStepFixedPoint_of_limit {β : ℝ} (hβ : 0 ≤ β) {L : ℝ} (hL : 0 < L)
    (hlim : Tendsto (g β) atTop (𝓝 L)) : ¬ NoStepFixedPoint g := by
  intro h
  obtain ⟨δ, hδ, hd⟩ := h (L / 2) (2 * L) (by positivity) (by linarith)
  have hε : 0 < min (L / 2) (δ / 2) := lt_min (by positivity) (by positivity)
  obtain ⟨W, hW⟩ := eventually_atTop.mp (hlim.eventually (Metric.ball_mem_nhds L hε))
  have h0 := hW (max W 1) (le_max_left _ _)
  have h1 := hW (max W 1 + 1) ((le_max_left W 1).trans (Nat.le_succ _))
  rw [Real.dist_eq] at h0 h1
  have a0 := abs_lt.mp h0
  have a1 := abs_lt.mp h1
  have hm1 := min_le_left (L / 2) (δ / 2)
  have hm2 := min_le_right (L / 2) (δ / 2)
  have := hd β hβ (max W 1) (le_max_right _ _) (by linarith [a0.1]) (by linarith [a0.2])
  linarith [a0.1, a0.2, a1.1, a1.2]

/-- **A positive line of fixed points fails the input** (a model of the Coulomb line of `U(1)`; argued).
DERIVED: `0` the signs. -/
theorem not_noStepFixedPoint_of_const {c : ℝ → ℝ} (hc : ∀ β w, g β w = c β) {β : ℝ} (hβ : 0 ≤ β)
    (hpos : 0 < c β) : ¬ NoStepFixedPoint g := by
  have e : g β = fun _ => c β := funext (hc β)
  exact not_noStepFixedPoint_of_limit hβ hpos (by rw [e]; exact tendsto_const_nhds)

end Step

/-- **The ultralocal reading satisfies the input vacuously.** DERIVED: `0` the trivial reading. Proof-internal:
the drop `1`. -/
theorem noStepFixedPoint_const_zero : NoStepFixedPoint fun _ _ => 0 :=
  fun _ _ ha _ => ⟨1, one_pos, fun _ _ _ _ h1 _ => absurd h1 (not_le.mpr ha)⟩

/-! ## 3. The Wilson window coupling -/

section Wilson

variable {N : ℕ}

/-- **The step-scaling input of the Wilson window coupling** (the named open input). -/
def WilsonNoStepFixedPoint (N : ℕ) : Prop := NoStepFixedPoint (windowCoupling N)

/-- **Below the basin edge every band is a theorem.** DERIVED: `0` the signs. Proof-internal: the seed
`1/1000` and the drop `3a/4` from `basin_contracts`. -/
theorem basin_stepDrop (hN : N ≠ 0) : ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ a b : ℝ, 0 < a → b ≤ a₀ → StepDropOn (windowCoupling N) a b := by
  refine ⟨1 / 1000, by norm_num, fun a b ha hb => ⟨3 * a / 4, by positivity, fun β hβ w hw h1 h2 => ?_⟩⟩
  have hc := CouplingTower.basin_contracts hN hβ hw (h2.trans hb)
  linarith

/-- **The input is its part above one basin edge.** DERIVED: `0` the signs. -/
theorem wilsonNoStep_iff (hN : N ≠ 0) : ∃ a₀ : ℝ, 0 < a₀ ∧
    (WilsonNoStepFixedPoint N ↔ ∀ b : ℝ, a₀ ≤ b → StepDropOn (windowCoupling N) a₀ b) := by
  obtain ⟨a₀, ha₀, hbas⟩ := basin_stepDrop hN
  refine ⟨a₀, ha₀, fun h b hb => h a₀ b ha₀ hb, fun h a b ha hab => ?_⟩
  rcases le_total b a₀ with hb | hb
  · exact hbas a b ha hb
  rcases le_total a₀ a with ha' | ha'
  · exact stepDropOn_mono (h b hb) ha' le_rfl
  · exact stepDropOn_union (hbas a a₀ ha le_rfl) (h b hb)

/-- **The input makes the window coupling vanish at every `β ≥ 0`.** DERIVED: `0` the limit and the signs.
Proof-internal: the seed `1/1000`. -/
theorem vanishing_of_wilsonNoStep (hN : N ≠ 0) (h : WilsonNoStepFixedPoint N) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (windowCoupling N β) atTop (𝓝 0) := by
  obtain ⟨w, hw, hlt⟩ := exists_lt_of_stepDropOn hβ
    (h (1 / 1000) (max (1 / 1000) (windowCoupling N β 1)) (by norm_num) (le_max_left _ _))
    (le_max_right _ _)
  exact tendsto_zero_of_seed hN hβ hw hlt.le

/-- **The input gives no Casimir term at every `β ≥ 0`.** DERIVED: `0` the excluded rank. -/
theorem noCasimir_of_wilsonNoStep (hN : N ≠ 0) (h : WilsonNoStepFixedPoint N) : CasimirStep.NoCasimir N :=
  fun _ hβ => (CasimirStep.vanishing_iff_noCasimirAt N _).mp (vanishing_of_wilsonNoStep hN h hβ)

/-- **The input gives the strong end.** DERIVED: `0` the excluded rank. -/
theorem strongEnd_of_wilsonNoStep (hN : N ≠ 0) (h : WilsonNoStepFixedPoint N) : StrongEnd N :=
  (StrongEndVanishing.strongEnd_iff_vanishing hN).mpr
    ((eventually_ge_atTop 0).mono fun _ hβ => vanishing_of_wilsonNoStep hN h hβ).frequently

/-- **The input gives flux confinement and neutral binding at every `β ≥ 0`.** DERIVED: `0` the sign of `β`. -/
theorem sectors_of_wilsonNoStep [NeZero N] (h : WilsonNoStepFixedPoint N) {β : ℝ} (hβ : 0 ≤ β) :
    FluxSplitCasimir.FluxConfinedAt N β ∧ FluxSplitCasimir.NeutralBindingAt N β := by
  have hc := (CasimirStep.vanishing_iff_noCasimirAt N β).mp (vanishing_of_wilsonNoStep (NeZero.ne N) h hβ)
  obtain ⟨hF, hZ⟩ := FluxSplitCasimir.sectors_of_noCasimirAt hβ hc
  exact ⟨hF, FluxSplitCasimir.binding_of_zeroFluxVanishing hZ⟩

/-- **The input gives the periodic Clay gap at every `β ≥ 0`.** DERIVED: `2` the least rank; `0` the plane, the
time axis and the signs; `1` the upper end of the rate interval. -/
theorem windowGap_of_wilsonNoStep (hN2 : 2 ≤ N) (hN : N ≠ 0) (h : WilsonNoStepFixedPoint N) {β : ℝ}
    (hβ : 0 ≤ β) : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ PeriodicContent.PeriodicClayGapAt 0 0 hN β r :=
  StrongEndVanishing.windowGap_of_vanishing hN2 hN hβ (vanishing_of_wilsonNoStep hN h hβ)

/-- **The reading is not a function of the running coupling through the strong end**: no injective `H` and no
`c ≠ 0` give `windowCoupling N β w = H(β − w c)` at every `β ≥ 0` and `w ≥ 1`.
DERIVED: `0` the ultralocal coupling and the signs; `1` the least window index. Proof-internal: `1`, `2` the two
windows read at `β = 0`. -/
theorem not_exactCovariant {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ H : ℝ → ℝ, Function.Injective H ∧
      ∀ β : ℝ, 0 ≤ β → ∀ w : ℕ, 1 ≤ w → windowCoupling N β w = H (β - w * c) := by
  rintro ⟨H, hH, hcov⟩
  have h1 := hcov 0 le_rfl 1 le_rfl
  have h2 := hcov 0 le_rfl 2 (by norm_num)
  rw [CouplingTower.windowCoupling_zero] at h1 h2
  have := hH (h1.symm.trans h2)
  push_cast at this
  apply hc
  linarith

end Wilson

end MassGap.RunningCrossover

#print axioms MassGap.RunningCrossover.kG_pos
#print axioms MassGap.RunningCrossover.aRunG_eq
#print axioms MassGap.RunningCrossover.kG_mul_runStep
#print axioms MassGap.RunningCrossover.runStepG_eq
#print axioms MassGap.RunningCrossover.runStepG_pos
#print axioms MassGap.RunningCrossover.aOneG_sub_step
#print axioms MassGap.RunningCrossover.aOneG_sub_nsmul
#print axioms MassGap.RunningCrossover.aOneG_strictAnti
#print axioms MassGap.RunningCrossover.oneLoop_crossing
#print axioms MassGap.RunningCrossover.twoLoop_step_le
#print axioms MassGap.RunningCrossover.twoLoop_run_le
#print axioms MassGap.RunningCrossover.twoLoop_doublings_lt
#print axioms MassGap.RunningCrossover.aRunG_pos
#print axioms MassGap.RunningCrossover.aRunG_bounded
#print axioms MassGap.RunningCrossover.twoLoop_exits
#print axioms MassGap.RunningCrossover.exits_iff
#print axioms MassGap.RunningCrossover.runStepG_eq_oneLoopStep
#print axioms MassGap.RunningCrossover.exits_oneLoop_iff
#print axioms MassGap.RunningCrossover.abelian_no_exit
#print axioms MassGap.RunningCrossover.stepDropOn_mono
#print axioms MassGap.RunningCrossover.stepDropOn_union
#print axioms MassGap.RunningCrossover.stepDrop_above_of_bands
#print axioms MassGap.RunningCrossover.exists_lt_of_stepDropOn
#print axioms MassGap.RunningCrossover.noStepFixedPoint_of_selfSimilar
#print axioms MassGap.RunningCrossover.stepDropOn_of_covariantOn
#print axioms MassGap.RunningCrossover.not_noStepFixedPoint_of_rise
#print axioms MassGap.RunningCrossover.not_noStepFixedPoint_of_limit
#print axioms MassGap.RunningCrossover.not_noStepFixedPoint_of_const
#print axioms MassGap.RunningCrossover.noStepFixedPoint_const_zero
#print axioms MassGap.RunningCrossover.basin_stepDrop
#print axioms MassGap.RunningCrossover.wilsonNoStep_iff
#print axioms MassGap.RunningCrossover.vanishing_of_wilsonNoStep
#print axioms MassGap.RunningCrossover.noCasimir_of_wilsonNoStep
#print axioms MassGap.RunningCrossover.strongEnd_of_wilsonNoStep
#print axioms MassGap.RunningCrossover.sectors_of_wilsonNoStep
#print axioms MassGap.RunningCrossover.windowGap_of_wilsonNoStep
#print axioms MassGap.RunningCrossover.not_exactCovariant
