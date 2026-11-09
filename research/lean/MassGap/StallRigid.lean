import Mathlib
import MassGap.DoublingWilsonG
import MassGap.JentzschKT
import MassGap.KernelGap
import MassGap.StrongTransferGap
import MassGap.FlatCap
import MassGap.EffectiveCoupling
import MassGap.CoverCompact

/-!
# MassGap.StallRigid — what a stall has to be: the fork of the doubling defect at the window scale

The doubling defect is a Rényi-2 entropy of the transfer spectrum at the window's own time. This module classifies
what a defect that does not vanish has to be, for the Wilson measure of every compact group (`GaugeGroup G`: `SU(N)`,
`SO(n)`, `USp(n)`, the exceptional groups, `A₅`, and `U(1)`, whose instance is built here).
Declarations are in the namespace `MassGap.StallRigid`.

`D(w)` is the defect at side `2^w` (`Dw`). `y_i(w) = (λ₁/λ₀)^{2^w}` on the slice of step `i` of the window
(`winRead`, `sliceT`), with sides `2^{w+1}` and `2^{w+2}`, and `Y(w)` is the largest of the four (`Yw`).

## 1. The Rényi read of a finite spectrum (proved)

`log(1+e) ≤ d ≤ 2 log(1+e)` (`defect_le_two_log`, `excited_ge`). `d(2m) ≤ 2 y (exp d(m) − 1)` for `y` bounding the
levels at time `m`, the fork (`defect_double_le_level`), and `d(2m) ≤ 2 d(m)` (`defect_double_le_two`). `level_count`: the
levels with `y_i ≥ c` number at most `(exp d − 1)/c`, whatever the window. `exists_level`: a bounded stall has a level in
the window. `defect_const`: `M` equal levels have defect `log M`.

## 2. The corners (proved)

`pred_le`: with `p ≥ 0` and the raising identity alone, the defect one time step before each step of the window is at
most `8 D(w) + 2 D(w+1)`. `exists_step`: one step carries `1/15` of `D(w+1)`.

## 3. The kernels (proved)

`IsTop.level_step` is the fork with no eigenvalue list, from `hs(k^{∗j}) = c^{2j} + hs(r^{∗j})` and
`hs(r^{∗2j}) ≤ ‖R‖^{2j} hs(r^{∗j})`. `IsTop.ratio_le_excited` is the converse, at dyadic time.

## 4. Perron–Frobenius with an explicit gap (proved)

`schur_gap`: a symmetric kernel `k ≥ a > 0` with unit top `0 < φ ≤ B` has `‖k − c φ⊗φ‖ ≤ c − a/B²`, by the Schur test
with weight `φ`. `exists_topG`: on every slice of every compact group at every `β ≥ 0`, `ρ ≤ c − a c²`, `a = kTmin`. So
the top is simple, and `Yw_lt_one`: (T) is never exact degeneracy.

## 5. The fork of a window (proved, the main results)

* `fork_quant`: `D(w+1) ≤ 30 Y(w) (exp(8 D(w) + 2 D(w+1)) − 1)`, every `β ≥ 0`, `w ≥ 1`, every compact group.
* `level_floor`: a bounded stall has `c₀ ≤ Y(w)` eventually.
* `stall_dichotomy`: a bounded stall has `c₀ ≤ Y(w) < 1` eventually, and either (T) `Y` comes frequently within every `δ`
  of `1`, or (M) `Y ≤ 1 − δ` eventually. With `D` unbounded, the third alternative (H), the fork forces nothing near the top.
* `vanishes_iff_read`, `vanishes_iff_read_SU`, `strongEnd_iff_read`: `D → 0` exactly when `D` is bounded and `Y → 0`.
  `vanishes_of_read` is `WindowFreq.GapGivesVanishing` on the step slices with its missing clause named.
* `massive_stall_grows`: with `Y(w) ≤ e^{−m 2^w}` a stall has `8 D(w) + 2 D(w+1) ≥ m 2^w + log(s/30)`.

## 6. `SU(N)` (proved)

`exists_gap_kT`, `top_centre_neutral`: the Jentzsch top is a `TransferGapAt` with `ρ < λ` at every coupling, it is invariant
under `Z_N³`, and the flux trace lies in the remainder, with no gap assumed. `large_stall_zero_flux`: a stall above
`90 log N` is zero-flux.

## 7. Tests (proved models; the phases named are cited or argued)

* `biased_stall` (`A₅` shape). Two points of weights `1/3`, `2/3` have no non-trivial measure-preserving map, and
  strictly positive kernels with a simple top stall at `log 2` in one sector. So PF, positivity and trivial symmetry
  exclude no bounded-multiplicity stall.
* `isolated_topological` (tangency shape). `1 + r^{vol}`, `r = e^{−|β−1|}`: a top cluster at one coupling alone. Its per-volume limit is `f_∞ ≡ 0`, so it is a tangency, not a crossing of sector free energies, and leaves no kink in `f_∞` (`GapPersist.tangency_flat`).
* `rotor_read` (`U(1)` flux shape). Levels `k²/(2bL)` read `e^{−1/(2b)}` at time `L`, free of `L`.
* `read_tests`: `vanishes_iff_read` at `U(1)` (`instGaugeGroupCircle`), `A₅`, `G₂`, by the one proof.
* `Yw_zero_coupling`: `Y = 0` at `β = 0`.

## 8. Rigidity and the Ward statement (proved)

`exists_cut`, `cut_limit`: limits of the defect at two couplings fix the limit of the cut energy at intermediate couplings.
`no_plaquette_charge`: no conserved plaquette charge at `SU(N)`, one at `U(1)`.

DERIVED (module-wide): `2` the square in the purity, the `L²` exponent and the doubling; `15 = 8 + 4 + 2 + 1` the path
weights; `8` the three raisings, `2 ≥ 3/2` the raising weights; `30 = 2 · 15`; `10 = 8 + 2`; `16 = 2⁴` the copies; `4` the
dimension; `0`, `1` limits, signs, the least window. CHOSEN: the weights `1/3`, `2/3` of `νW` (any unequal pair has no
symmetry); `β = 1` in `isolated_topological` (any coupling); the three levels `0, ±1` of `rotorSpec`.

## What does not follow

No stall is excluded at any coupling outside the anchors. (H), (T), (M) are all open for `SU(N)` at large `β`. A lower bound on `gap · L` (ZP) and the exclusion of a zero-flux level at gap of order `1/L` (ZM) are named, not proved. Boundedness of
`D` along the windows is proved at no large `β`. `stall_dichotomy` is exhaustive by logic: its content is `level_floor`. The
slices of `Y` have aspect up to `4`; no theorem here reads the cubic slice of the periodic gap. The kernels carry no
eigenvalue list, so the level count is at the finite-spectrum level only. `biased_stall`, `isolated_topological` and
`rotor_read` are models, not Wilson kernels. The phase of each group at large `β` is cited or argued, not proved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.StallRigid

open MeasureTheory Filter Topology MassGap.KernelPower MassGap.SlabKernelOperator

/-! ## 1. The Rényi read of a finite spectrum -/

section Spectrum

open Finset MassGap.DoublingRecursion

variable {ι : Type} [DecidableEq ι] {s : Finset ι} {w : ι → ℝ} {i₀ : ι}

/-- **The defect is at most twice `log(1 + e)`.** With `excited_le`: `log(1+e) ≤ d ≤ 2 log(1+e)`.
DERIVED: `2` the square in the purity. -/
theorem defect_le_two_log (h : Top s w i₀) (m : ℕ) :
    defect s w m ≤ 2 * Real.log (1 + excited s w i₀ m) := by
  have ha := top_pow_pos h m
  have he := excited_nonneg h m
  have hP := powSum_pos h m
  have hQ := powSum_pos h (2 * m)
  have e1 : powSum s w m = w i₀ ^ m * (1 + excited s w i₀ m) := by
    rw [one_add_excited h m]; field_simp
  have hge : (w i₀ ^ m) ^ 2 ≤ powSum s w (2 * m) := by
    have e2 : (w i₀ ^ m) ^ 2 = w i₀ ^ (2 * m) := by rw [← pow_mul]; ring_nf
    rw [e2]
    exact Finset.single_le_sum (f := fun i => w i ^ (2 * m))
      (fun j hj => pow_nonneg (h.nonneg j hj) _) h.mem
  have hl := Real.log_le_log (by positivity) hge
  rw [Real.log_pow] at hl
  unfold defect
  rw [e1, Real.log_mul ha.ne' (by positivity : (1 + excited s w i₀ m) ≠ 0)]
  push_cast at hl
  linarith

/-- **The excited weight, from below.** DERIVED: `2` the square in the purity. -/
theorem excited_ge (h : Top s w i₀) (m : ℕ) :
    Real.exp (defect s w m / 2) - 1 ≤ excited s w i₀ m := by
  have he := excited_nonneg h m
  have hd := defect_le_two_log h m
  have h1 : defect s w m / 2 ≤ Real.log (1 + excited s w i₀ m) := by linarith
  have h2 := Real.exp_le_exp.mpr h1
  rw [Real.exp_log (by positivity)] at h2
  linarith

theorem excited_eq_sum (h : Top s w i₀) (m : ℕ) :
    excited s w i₀ m = ∑ i ∈ s.erase i₀, (w i / w i₀) ^ m := by
  simp only [DoublingRecursion.excited, div_pow, Finset.sum_div]

/-- **The doubled excited weight is at most the top level times the excited weight.** -/
theorem excited_double_le (h : Top s w i₀) (m : ℕ) {y : ℝ}
    (hy : ∀ i ∈ s.erase i₀, (w i / w i₀) ^ m ≤ y) :
    excited s w i₀ (2 * m) ≤ y * excited s w i₀ m := by
  rw [excited_eq_sum h, excited_eq_sum h, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h0 : 0 ≤ (w i / w i₀) ^ m :=
    pow_nonneg (div_nonneg (h.nonneg i (Finset.mem_of_mem_erase hi)) h.pos.le) m
  rw [two_mul, pow_add]
  exact mul_le_mul_of_nonneg_right (hy i hi) h0

theorem ratio_pow_le_one (h : Top s w i₀) (m : ℕ) {i : ι} (hi : i ∈ s) :
    (w i / w i₀) ^ m ≤ 1 := by
  refine pow_le_one₀ (div_nonneg (h.nonneg i hi) h.pos.le) ?_
  rw [div_le_one h.pos]
  exact h.le_top i hi

theorem one_add_excited_le (h : Top s w i₀) (m : ℕ) :
    1 + excited s w i₀ m ≤ Real.exp (defect s w m) := by
  linarith [DoublingRecursion.excited_le h m]

/-- **The fork.** A defect at time `2m` needs a level at time `m` or an exponentially large weight:
`d(2m) ≤ 2 y (exp d(m) − 1)` for every bound `y` of the excited levels at time `m`.
DERIVED: `2` the square in the purity. -/
theorem defect_double_le_level (h : Top s w i₀) (m : ℕ) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : ∀ i ∈ s.erase i₀, (w i / w i₀) ^ m ≤ y) :
    defect s w (2 * m) ≤ 2 * y * (Real.exp (defect s w m) - 1) := by
  have h1 := defect_le_two_log h (2 * m)
  have h2 := excited_double_le h m hy
  have h3 := excited_nonneg h (2 * m)
  have h4 := DoublingRecursion.excited_le h m
  have h5 : Real.log (1 + excited s w i₀ (2 * m)) ≤ excited s w i₀ (2 * m) := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + excited s w i₀ (2 * m))
    linarith
  have h6 : y * excited s w i₀ m ≤ y * (Real.exp (defect s w m) - 1) :=
    mul_le_mul_of_nonneg_left h4 hy0
  linarith

/-- **The defect can at most double with the time.** DERIVED: `2` the square in the purity. -/
theorem defect_double_le_two (h : Top s w i₀) (m : ℕ) : defect s w (2 * m) ≤ 2 * defect s w m := by
  have h1 := defect_le_two_log h (2 * m)
  have h2 : excited s w i₀ (2 * m) ≤ 1 * excited s w i₀ m :=
    excited_double_le h m fun i hi => ratio_pow_le_one h m (Finset.mem_of_mem_erase hi)
  have h3 := excited_nonneg h (2 * m)
  have h4 := one_add_excited_le h m
  have h5 : Real.log (1 + excited s w i₀ (2 * m)) ≤ defect s w m := by
    have := Real.log_le_log (by positivity) ((by linarith : 1 + excited s w i₀ (2 * m)
      ≤ Real.exp (defect s w m)))
    rwa [Real.log_exp] at this
  linarith

/-- **The window count.** The levels with `y_i ≥ c` number at most `(exp d − 1)/c`, whatever the
window. A bounded defect has bounded multiplicity at every aperture. -/
theorem level_count (h : Top s w i₀) (m : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    c * (((s.erase i₀).filter fun i => c ≤ (w i / w i₀) ^ m).card : ℝ)
      ≤ Real.exp (defect s w m) - 1 := by
  have h1 : c * (((s.erase i₀).filter fun i => c ≤ (w i / w i₀) ^ m).card : ℝ)
      ≤ ∑ i ∈ (s.erase i₀).filter (fun i => c ≤ (w i / w i₀) ^ m), (w i / w i₀) ^ m := by
    rw [mul_comm, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun i hi => (Finset.mem_filter.mp hi).2
  have h2 : ∑ i ∈ (s.erase i₀).filter (fun i => c ≤ (w i / w i₀) ^ m), (w i / w i₀) ^ m
      ≤ ∑ i ∈ s.erase i₀, (w i / w i₀) ^ m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i hi _ =>
      pow_nonneg (div_nonneg (h.nonneg i (Finset.mem_of_mem_erase hi)) h.pos.le) m
  rw [← excited_eq_sum h] at h2
  linarith [DoublingRecursion.excited_le h m]

/-- **A bounded stall has a level in the window**, at the finite-spectrum level: a defect at least `t > 0`
at time `2m`, and at most `A` at time `m`, give an excited level with
`(λ_i/λ₀)^m ≥ t / (2 (exp A − 1))`. DERIVED: `2` the square in the purity. -/
theorem exists_level (h : Top s w i₀) (m : ℕ) {t A : ℝ} (ht : 0 < t)
    (hd : t ≤ defect s w (2 * m)) (hA : defect s w m ≤ A) :
    ∃ i ∈ s.erase i₀, t / (2 * (Real.exp A - 1)) ≤ (w i / w i₀) ^ m := by
  have hne : (s.erase i₀).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : excited s w i₀ (2 * m) = 0 := by rw [excited_eq_sum h, hemp, Finset.sum_empty]
    have := defect_le_two_log h (2 * m)
    rw [h0] at this
    simp at this
    linarith
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ (fun i => (w i / w i₀) ^ m) hne
  refine ⟨i, hi, ?_⟩
  have hy0 : 0 ≤ (w i / w i₀) ^ m :=
    pow_nonneg (div_nonneg (h.nonneg i (Finset.mem_of_mem_erase hi)) h.pos.le) m
  have h1 := defect_double_le_level h m hy0 hmax
  have h2 : Real.exp (defect s w m) ≤ Real.exp A := Real.exp_le_exp.mpr hA
  have h3 : 2 * (w i / w i₀) ^ m * (Real.exp (defect s w m) - 1)
      ≤ 2 * (w i / w i₀) ^ m * (Real.exp A - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hApos : 0 < Real.exp A - 1 := by
    by_contra hc
    have hle : Real.exp A - 1 ≤ 0 := not_lt.mp hc
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Exact degeneracy.** `M` equal levels have defect `log M` at every time: the top cluster reading of a
stall. -/
theorem defect_const {a : ℝ} (ha : 0 < a) (hs : s.Nonempty) (hw : ∀ i ∈ s, w i = a) (m : ℕ) :
    defect s w m = Real.log s.card := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have e : ∀ k : ℕ, powSum s w k = s.card * a ^ k := fun k => by
    unfold powSum
    have e0 : ∑ i ∈ s, w i ^ k = ∑ _i ∈ s, a ^ k := Finset.sum_congr rfl fun i hi => by rw [hw i hi]
    rw [e0, Finset.sum_const, nsmul_eq_mul]
  have hpa : a ^ m ≠ 0 := (pow_pos ha m).ne'
  have e2 : Real.log (a ^ (2 * m)) = 2 * Real.log (a ^ m) := by
    rw [Real.log_pow, Real.log_pow]; push_cast; ring
  unfold defect
  rw [e, e, Real.log_mul hc.ne' hpa, Real.log_mul hc.ne' (pow_pos ha _).ne', e2]
  ring

end Spectrum

/-! ## 2. The corners: the predecessor bound -/

section Corners

open MassGap.DoublingRecursion

/-- The base corners of the four steps of the window at `corner 1`, one time step early. -/
def uP : Fin 4 → Pt := ![![0, 1, 1, 1], ![2, 0, 1, 1], ![2, 2, 0, 1], ![2, 2, 2, 0]]

theorem uP_self (i : Fin 4) : uP i i = 0 := by fin_cases i <;> rfl

variable {x : Pt → ℝ}

theorem p_eq (μ : Fin 4) {a v u : Pt} (h1 : a = v) (h2 : a + E μ = u) :
    p x μ a = 2 * x v - x u := by
  rw [p, h2, h1]

/-- **The predecessor bound.** With only `p ≥ 0` and the raising identity,
`p_i(uP i) ≤ 8 Δ(0) + 2 Δ(𝟙)` at each of the four steps. DERIVED: `8 = 2³` the three raisings of the last
step; `2` is above `3/2 = 4/8 + 2/4 + 1/2`, the weights of the raising terms in `Δ(𝟙)`. -/
theorem pred_le (hx : Positive x) (i : Fin 4) :
    p x i (uP i) ≤ 8 * Δ x (corner 0) + 2 * Δ x (corner 1) := by
  have e00 : (corner 0 : Pt) = ![0, 0, 0, 0] := by decide
  have e11 : (corner 1 : Pt) = ![1, 1, 1, 1] := by decide
  have e001 : (![0, 0, 0, 0] : Pt) + one = ![1, 1, 1, 1] := by decide
  have e111 : (![1, 1, 1, 1] : Pt) + one = ![2, 2, 2, 2] := by decide
  have a1 := nn hx 1 ![0, 0, 0, 0] ![0, 1, 0, 0] (by decide)
  have a2 := nn hx 2 ![0, 1, 0, 0] ![0, 1, 1, 0] (by decide)
  have a3 := nn hx 3 ![0, 1, 1, 0] ![0, 1, 1, 1] (by decide)
  have a4 := nn hx 0 ![0, 1, 1, 1] ![1, 1, 1, 1] (by decide)
  have b1 := nn hx 0 ![0, 0, 0, 0] ![1, 0, 0, 0] (by decide)
  have b2 := nn hx 2 ![1, 0, 0, 0] ![1, 0, 1, 0] (by decide)
  have b3 := nn hx 3 ![1, 0, 1, 0] ![1, 0, 1, 1] (by decide)
  have b4 := nn hx 1 ![1, 0, 1, 1] ![1, 1, 1, 1] (by decide)
  have c2 := nn hx 1 ![1, 0, 0, 0] ![1, 1, 0, 0] (by decide)
  have c3 := nn hx 3 ![1, 1, 0, 0] ![1, 1, 0, 1] (by decide)
  have c4 := nn hx 2 ![1, 1, 0, 1] ![1, 1, 1, 1] (by decide)
  have d3 := nn hx 2 ![1, 1, 0, 0] ![1, 1, 1, 0] (by decide)
  have d4 := nn hx 3 ![1, 1, 1, 0] ![1, 1, 1, 1] (by decide)
  have n1 := nn hx 0 ![1, 1, 1, 1] ![2, 1, 1, 1] (by decide)
  have n2 := nn hx 1 ![2, 1, 1, 1] ![2, 2, 1, 1] (by decide)
  have n3 := nn hx 2 ![2, 2, 1, 1] ![2, 2, 2, 1] (by decide)
  have n4 := nn hx 3 ![2, 2, 2, 1] ![2, 2, 2, 2] (by decide)
  have r1 := nn hx 0 ![1, 0, 1, 1] ![2, 0, 1, 1] (by decide)
  have r2 := nn hx 0 ![1, 1, 0, 1] ![2, 1, 0, 1] (by decide)
  have r3 := nn hx 1 ![2, 1, 0, 1] ![2, 2, 0, 1] (by decide)
  have r4 := nn hx 0 ![1, 1, 1, 0] ![2, 1, 1, 0] (by decide)
  have r5 := nn hx 1 ![2, 1, 1, 0] ![2, 2, 1, 0] (by decide)
  have r6 := nn hx 2 ![2, 2, 1, 0] ![2, 2, 2, 0] (by decide)
  have hd : 8 * Δ x (corner 0) + 2 * Δ x (corner 1) =
      8 * (16 * x ![0, 0, 0, 0] - x ![1, 1, 1, 1]) + 2 * (16 * x ![1, 1, 1, 1] - x ![2, 2, 2, 2]) := by
    simp only [Δ, e00, e11, e001, e111]
  rw [hd]
  fin_cases i
  · have e : p x 0 (uP 0) = 2 * x ![0, 1, 1, 1] - x ![1, 1, 1, 1] :=
      p_eq 0 (by decide) (by decide)
    show p x 0 (uP 0) ≤ _
    rw [e]; linarith
  · have e : p x 1 (uP 1) = 2 * x ![2, 0, 1, 1] - x ![2, 1, 1, 1] :=
      p_eq 1 (by decide) (by decide)
    show p x 1 (uP 1) ≤ _
    rw [e]; linarith
  · have e : p x 2 (uP 2) = 2 * x ![2, 2, 0, 1] - x ![2, 2, 1, 1] :=
      p_eq 2 (by decide) (by decide)
    show p x 2 (uP 2) ≤ _
    rw [e]; linarith
  · have e : p x 3 (uP 3) = 2 * x ![2, 2, 2, 0] - x ![2, 2, 2, 1] :=
      p_eq 3 (by decide) (by decide)
    show p x 3 (uP 3) ≤ _
    rw [e]; linarith

/-- **One of the four steps carries at least `1/15` of the window.** DERIVED: `15 = 8 + 4 + 2 + 1`. -/
theorem exists_step (hx : Positive x) : ∃ i, Δ x (corner 1) / 15 ≤ p x i (uP i + E i) := by
  have e11 : (corner 1 : Pt) = ![1, 1, 1, 1] := by decide
  have e111 : (![1, 1, 1, 1] : Pt) + one = ![2, 2, 2, 2] := by decide
  have e0 : p x 0 (uP 0 + E 0) = 2 * x ![1, 1, 1, 1] - x ![2, 1, 1, 1] :=
    p_eq 0 (by decide) (by decide)
  have e1 : p x 1 (uP 1 + E 1) = 2 * x ![2, 1, 1, 1] - x ![2, 2, 1, 1] :=
    p_eq 1 (by decide) (by decide)
  have e2 : p x 2 (uP 2 + E 2) = 2 * x ![2, 2, 1, 1] - x ![2, 2, 2, 1] :=
    p_eq 2 (by decide) (by decide)
  have e3 : p x 3 (uP 3 + E 3) = 2 * x ![2, 2, 2, 1] - x ![2, 2, 2, 2] :=
    p_eq 3 (by decide) (by decide)
  have hd : Δ x (corner 1) = 16 * x ![1, 1, 1, 1] - x ![2, 2, 2, 2] := by
    simp only [Δ, e11, e111]
  by_contra hc
  push_neg at hc
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [hd] at h0 h1 h2 h3
  linarith

/-- **The defect at a corner is nonnegative.** DERIVED: `8, 4, 2, 1` the path weights. -/
theorem Δ_corner_nonneg (hx : Positive x) : 0 ≤ Δ x (corner 0) := by
  have e00 : (corner 0 : Pt) = ![0, 0, 0, 0] := by decide
  have e001 : (![0, 0, 0, 0] : Pt) + one = ![1, 1, 1, 1] := by decide
  have a1 := nn hx 1 ![0, 0, 0, 0] ![0, 1, 0, 0] (by decide)
  have a2 := nn hx 2 ![0, 1, 0, 0] ![0, 1, 1, 0] (by decide)
  have a3 := nn hx 3 ![0, 1, 1, 0] ![0, 1, 1, 1] (by decide)
  have a4 := nn hx 0 ![0, 1, 1, 1] ![1, 1, 1, 1] (by decide)
  simp only [Δ, e00, e001]
  linarith

end Corners

/-! ## 3. The kernels: the fork with no eigenvalue list -/

section Kernels

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- `(c, φ)` is a top eigenpair of the kernel `k` and `ρ` is exactly the norm of the remainder. -/
structure IsTop (ν : Measure X) [IsProbabilityMeasure ν] (k : X → X → ℝ) (C : ℝ)
    (hkm : Measurable (Function.uncurry k)) (hC0 : 0 ≤ C) (hkb : ∀ x y, |k x y| ≤ C)
    (c : ℝ) (φ : X → ℝ) (ρ : ℝ) : Prop where
  meas : Measurable φ
  bdd : ∃ B, ∀ x, |φ x| ≤ B
  norm1 : ∫ x, φ x ^ 2 ∂ν = 1
  ne : c ≠ 0
  eig : ∀ z, ∫ y, k z y * φ y ∂ν = c * φ z
  top : |c| = ‖kernelCLM k C hkm hC0 hkb ν ν‖
  rem : ∃ (C' : ℝ) (hm : Measurable (Function.uncurry (rem k c φ))) (hC0' : 0 ≤ C')
    (hb : ∀ x y, |KernelPower.rem k c φ x y| ≤ C'),
      ‖kernelCLM (KernelPower.rem k c φ) C' hm hC0' hb ν ν‖ = ρ

open DoublingPower in
/-- **The fork at the trace level.** Facts at `m` and at `2m` and `s' ≤ y s` give
`defect(2m) ≤ 2 y (exp defect(m) − 1)`. DERIVED: `2` the square in the purity. -/
theorem defect_double_of_facts {a : ℕ → ℝ} {lam s s' y : ℝ} {m : ℕ}
    (h : PowerFacts a lam s m) (h' : PowerFacts a lam s' (2 * m)) (hy0 : 0 ≤ y) (hy : s' ≤ y * s) :
    defect a (2 * m) ≤ 2 * y * (Real.exp (defect a m) - 1) := by
  have hl := h'.lam_pow_pos (2 * m)
  have hb := h'.base
  have hA := h'.a_pos
  have hB := h'.a2_pos
  have h1s : 0 < 1 + s' := by linarith [h'.s_nonneg]
  have hge := h'.dbl_ge
  have e2 : lam ^ (2 * (2 * m)) = (lam ^ (2 * m)) ^ 2 := by rw [← pow_mul]; ring_nf
  have hlog := Real.log_le_log (by rw [e2]; positivity) hge
  rw [e2, Real.log_pow] at hlog
  have h2 : defect a (2 * m) ≤ 2 * Real.log (1 + s') := by
    unfold defect
    rw [hb, Real.log_mul hl.ne' h1s.ne']
    push_cast at hlog
    linarith
  have h3 : Real.log (1 + s') ≤ s' := by
    have := Real.log_le_sub_one_of_pos h1s
    linarith
  have h4 := DoublingPower.excited_le h
  have h5 : y * s ≤ y * (Real.exp (defect a m) - 1) := mul_le_mul_of_nonneg_left h4 hy0
  linarith

variable {k : X → X → ℝ} {C : ℝ} {hkm : Measurable (Function.uncurry k)} {hC0 : 0 ≤ C}
  {hkb : ∀ x y, |k x y| ≤ C} {c : ℝ} {φ : X → ℝ} {ρ : ℝ}

theorem IsTop.rho_nonneg (h : IsTop ν k C hkm hC0 hkb c φ ρ) : 0 ≤ ρ := by
  obtain ⟨C', hm, h0, hb, e⟩ := h.rem
  rw [← e]; exact norm_nonneg _

theorem IsTop.powerFacts (h : IsTop ν k C hkm hC0 hkb c φ ρ) (hsym : ∀ x y, k x y = k y x)
    (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.PowerFacts (traceSeq ν k) |c| (KernelPower.excited ν k c φ j) (2 * j) := by
  obtain ⟨B, hφb⟩ := h.bdd
  exact KernelPower.powerFacts hkm hC0 hkb hsym h.meas hφb h.norm1 h.eig h.top h.ne j hj

/-- **The excited weight doubles down by the second level**: `e(4j) ≤ (ρ/|c|)^{2j} e(2j)`.
DERIVED: `2` the square in `hs`. -/
theorem IsTop.excited_double_le (h : IsTop ν k C hkm hC0 hkb c φ ρ) (j : ℕ) (hj : 1 ≤ j) :
    KernelPower.excited ν k c φ (2 * j)
      ≤ (ρ / |c|) ^ (2 * j) * KernelPower.excited ν k c φ j := by
  obtain ⟨C', hm, h0, hb, e⟩ := h.rem
  have hl : 0 < |c| := abs_pos.mpr h.ne
  have hρ : 0 ≤ ρ := h.rho_nonneg
  have h1 := hs_iter_le (μ := ν) hm h0 hb (j - 1) j
  rw [e] at h1
  have e1 : 2 * j - 1 = (j - 1) + j := by omega
  have e2 : 2 * (2 * j) = 2 * j + 2 * j := by ring
  unfold KernelPower.excited
  rw [e1, e2, pow_add, div_pow, div_mul_div_comm]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact h1

/-- **The fork on a kernel.** `p(4j) ≤ 2 (ρ/|c|)^{2j} (exp p(2j) − 1)`, `p` the defect of the trace sequence:
a defect at time `4j` forces the second eigenvalue at time `2j`, or a large defect at time `2j`.
DERIVED: `2` the square in the purity. -/
theorem IsTop.level_step (h : IsTop ν k C hkm hC0 hkb c φ ρ) (hsym : ∀ x y, k x y = k y x)
    (j : ℕ) (hj : 1 ≤ j) :
    DoublingPower.defect (traceSeq ν k) (2 * (2 * j))
      ≤ 2 * (ρ / |c|) ^ (2 * j) * (Real.exp (DoublingPower.defect (traceSeq ν k) (2 * j)) - 1) := by
  have hl : 0 < |c| := abs_pos.mpr h.ne
  exact defect_double_of_facts (h.powerFacts hsym j hj) (h.powerFacts hsym (2 * j) (by omega))
    (pow_nonneg (div_nonneg h.rho_nonneg hl.le) _) (h.excited_double_le j hj)

end Kernels

/-! ## 4. Perron–Frobenius with an explicit gap: the Schur test -/

section Schur

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- **The Schur test with weight `φ`.** A nonnegative bounded symmetric kernel `s` with a positive bounded
eigenfunction `φ`, `S φ = μ' φ`, has `‖S g‖² ≤ μ'² ‖g‖²`. DERIVED: `2` the `L²` exponent. -/
theorem schur_sq {s : X → X → ℝ} (hsm : Measurable (Function.uncurry s)) {Cs : ℝ}
    (hsb : ∀ x y, |s x y| ≤ Cs) (hs0 : ∀ x y, 0 ≤ s x y) (hsym : ∀ x y, s x y = s y x)
    {φ : X → ℝ} (hφm : Measurable φ) {c₁ B : ℝ} (hc₁ : 0 < c₁) (hlow : ∀ x, c₁ ≤ φ x)
    (hB : ∀ x, φ x ≤ B) {μ' : ℝ} (heig : ∀ z, ∫ y, s z y * φ y ∂ν = μ' * φ z)
    {g : X → ℝ} (hg : MemLp g 2 ν) :
    ∫ x, (∫ y, s x y * g y ∂ν) ^ 2 ∂ν ≤ μ' ^ 2 * ∫ y, g y ^ 2 ∂ν := by
  have hφpos : ∀ x, 0 < φ x := fun x => lt_of_lt_of_le hc₁ (hlow x)
  have hg2 : Integrable (fun y => g y ^ 2) ν := hg.integrable_sq
  have hg1 : Integrable g ν := hg.integrable one_le_two
  have hinvm : Measurable fun y => (φ y)⁻¹ := hφm.inv
  have hinvb : ∀ y, ‖(φ y)⁻¹‖ ≤ c₁⁻¹ := fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hφpos y))]
    exact inv_anti₀ hc₁ (hlow y)
  set t : X → ℝ := fun y => g y ^ 2 * (φ y)⁻¹ with ht
  have htI : Integrable t ν := hg2.mul_bdd hinvm.aestronglyMeasurable
    (Eventually.of_forall hinvb)
  have hφb : ∀ x, |φ x| ≤ B := fun x => by
    rw [abs_of_pos (hφpos x)]; exact hB x
  -- the product integrand
  have hF : Integrable (Function.uncurry fun x y => φ x * s x y * t y) (ν.prod ν) := by
    have h1 : Integrable (fun p : X × X => t p.2) (ν.prod ν) := htI.comp_snd ν
    have hm : Measurable fun p : X × X => φ p.1 * s p.1 p.2 :=
      (hφm.comp measurable_fst).mul hsm
    have h2 := h1.bdd_mul (c := B * Cs) hm.aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hφb _) (hsb _ _) (abs_nonneg _) ((abs_nonneg _).trans (hφb p.1)))
    exact h2
  -- the pointwise Cauchy–Schwarz
  have hpt : ∀ x, (∫ y, s x y * g y ∂ν) ^ 2 ≤ μ' * ∫ y, φ x * s x y * t y ∂ν := by
    intro x
    set f1 : X → ℝ := fun y => Real.sqrt (s x y * φ y) with hf1
    set f2 : X → ℝ := fun y => Real.sqrt (s x y * (φ y)⁻¹) * g y with hf2
    have e1 : (fun y => f1 y ^ 2) = fun y => s x y * φ y := by
      funext y
      exact Real.sq_sqrt (mul_nonneg (hs0 x y) (hφpos y).le)
    have e2 : (fun y => f2 y ^ 2) = fun y => s x y * t y := by
      funext y
      simp only [hf2, ht, mul_pow]
      rw [Real.sq_sqrt (mul_nonneg (hs0 x y) (inv_nonneg.mpr (hφpos y).le))]
      ring
    have e3 : (fun y => f1 y * f2 y) = fun y => s x y * g y := by
      funext y
      simp only [hf1, hf2]
      rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg (hs0 x y) (hφpos y).le)]
      have : s x y * φ y * (s x y * (φ y)⁻¹) = s x y ^ 2 := by
        field_simp [(hφpos y).ne']
      rw [this, Real.sqrt_sq (hs0 x y)]
    have i1 : Integrable (fun y => s x y * φ y) ν :=
      integrable_row_mul hsm hsb (integrable_of_bdd hφm hφb) x
    have i2 : Integrable (fun y => s x y * t y) ν := integrable_row_mul hsm hsb htI x
    have i3 : Integrable (fun y => s x y * g y) ν := integrable_row_mul hsm hsb hg1 x
    have h := sq_integral_mul_le (ν := ν) (f := f1) (g := f2) (by rw [e1]; exact i1)
      (by rw [e2]; exact i2) (by rw [e3]; exact i3)
    rw [e1, e2, e3, heig x] at h
    have e4 : ∫ y, φ x * s x y * t y ∂ν = φ x * ∫ y, s x y * t y ∂ν := by
      rw [← integral_const_mul]; congr 1; funext y; ring
    rw [e4]
    calc _ ≤ _ := h
      _ = _ := by ring
  have hR : Integrable (fun x => μ' * ∫ y, φ x * s x y * t y ∂ν) ν :=
    (hF.integral_prod_left).const_mul μ'
  have h1 : ∫ x, (∫ y, s x y * g y ∂ν) ^ 2 ∂ν ≤ ∫ x, μ' * ∫ y, φ x * s x y * t y ∂ν ∂ν :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hR
      (Eventually.of_forall hpt)
  rw [integral_const_mul, integral_integral_swap hF] at h1
  have e5 : ∀ y, ∫ x, φ x * s x y * t y ∂ν = μ' * g y ^ 2 := by
    intro y
    have : ∀ x, φ x * s x y * t y = t y * (s y x * φ x) := fun x => by rw [hsym x y]; ring
    simp_rw [this]
    rw [integral_const_mul, heig y]
    simp only [ht]
    field_simp [(hφpos y).ne']
  simp_rw [e5] at h1
  rw [integral_const_mul] at h1
  calc _ ≤ _ := h1
    _ = _ := by ring

/-- **Perron–Frobenius with an explicit gap.** A symmetric kernel `k ≥ a > 0` with a unit eigenfunction
`0 < c₁ ≤ φ ≤ B`, eigenvalue `c`, has `‖k − c φ⊗φ‖ ≤ c − a/B²`. The kernel `s = k − (a/B²) φ⊗φ` is
nonnegative with eigenvalue `c − a/B²`, the Schur test bounds it, and on `f` the remainder is `S (f − ⟨f,φ⟩φ)`.
DERIVED: `2` the `L²` exponent. -/
theorem schur_gap {k : X → X → ℝ} (hk : Bdd k) (hsym : ∀ x y, k x y = k y x) {a : ℝ} (ha : 0 < a)
    (hlo : ∀ x y, a ≤ k x y) {φ : X → ℝ} (hφm : Measurable φ) {c₁ B : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ x, c₁ ≤ φ x) (hB : ∀ x, φ x ≤ B) (hφ1 : ∫ x, φ x ^ 2 ∂ν = 1) {c : ℝ}
    (heig : ∀ z, ∫ y, k z y * φ y ∂ν = c * φ z) {C' : ℝ}
    (hm : Measurable (Function.uncurry (KernelPower.rem k c φ))) (h0 : 0 ≤ C')
    (hb : ∀ x y, |KernelPower.rem k c φ x y| ≤ C') :
    ‖kernelCLM (KernelPower.rem k c φ) C' hm h0 hb ν ν‖ ≤ c - a / B ^ 2 := by
  classical
  have hφpos : ∀ x, 0 < φ x := fun x => lt_of_lt_of_le hc₁ (hlow x)
  have hφb : ∀ x, |φ x| ≤ B := fun x => by rw [abs_of_pos (hφpos x)]; exact hB x
  have hne : Nonempty X := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h0' : ν = 0 := Measure.eq_zero_of_isEmpty ν
    have : ν Set.univ = 1 := measure_univ
    rw [h0'] at this
    simp at this
  obtain ⟨x₀⟩ := hne
  have hBpos : 0 < B := lt_of_lt_of_le (hφpos x₀) (hB x₀)
  set κ := a / B ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set s : X → X → ℝ := fun x y => k x y - κ * φ x * φ y with hs
  set μ' := c - κ with hμ'
  have hrs : ∀ x y, KernelPower.rem k c φ x y = s x y - μ' * φ x * φ y := fun x y => by
    simp only [KernelPower.rem, hs, hμ']; ring
  have hs0 : ∀ x y, 0 ≤ s x y := fun x y => by
    have h1 : φ x * φ y ≤ B ^ 2 := by
      have := mul_le_mul (hB x) (hB y) (hφpos y).le hBpos.le
      nlinarith
    have h2 : κ * (φ x * φ y) ≤ κ * B ^ 2 := mul_le_mul_of_nonneg_left h1 hκ0
    have h3 : κ * B ^ 2 = a := by rw [hκ]; field_simp
    have := hlo x y
    simp only [hs]
    nlinarith
  have hsr : Bdd s := Bdd.rem hk hφm hφb (c := κ)
  obtain ⟨Cs, hCs⟩ := hsr.bdd
  obtain ⟨Ck, hCk⟩ := hk.bdd
  have hssym : ∀ x y, s x y = s y x := fun x y => by simp only [hs]; rw [hsym x y]; ring
  have hφ2 : Integrable (fun y => φ y ^ 2) ν := integrable_of_bdd (hφm.pow_const 2) (C := B ^ 2)
    (fun y => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hφb y) 2)
  have heigs : ∀ z, ∫ y, s z y * φ y ∂ν = μ' * φ z := fun z => by
    have e : (fun y => s z y * φ y) = fun y => k z y * φ y - κ * φ z * φ y ^ 2 := by
      funext y; simp only [hs]; ring
    have i1 : Integrable (fun y => k z y * φ y) ν :=
      integrable_mul_of_bdd (hk.row z) hφm (fun y => hCk z y) hφb
    rw [e, integral_sub i1 (hφ2.const_mul _), integral_const_mul, heig z, hφ1, hμ']
    ring
  have hμ0 : 0 ≤ μ' := by
    have h1 : 0 ≤ ∫ y, s x₀ y * φ y ∂ν :=
      integral_nonneg fun y => mul_nonneg (hs0 x₀ y) (hφpos y).le
    rw [heigs x₀] at h1
    exact nonneg_of_mul_nonneg_left h1 (hφpos x₀)
  refine ContinuousLinearMap.opNorm_le_bound _ hμ0 fun f => ?_
  have hφL : MemLp φ 2 ν := MemLp.of_bound hφm.aestronglyMeasurable B
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hφb y)
  have hfL : MemLp (f : X → ℝ) 2 ν := Lp.memLp f
  have hf1 : Integrable (f : X → ℝ) ν := hfL.integrable one_le_two
  set A := ∫ y, (f : X → ℝ) y * φ y ∂ν with hA
  set g : X → ℝ := fun y => (f : X → ℝ) y - A * φ y with hg
  have hgL : MemLp g 2 ν := hfL.sub (hφL.const_mul A)
  have hS := schur_sq (ν := ν) hsr.meas hCs hs0 hssym hφm hc₁ hlow hB heigs hgL
  have hfφ : Integrable (fun y => (f : X → ℝ) y * φ y) ν := hf1.mul_bdd hφm.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hφb y)
  -- the remainder acts as `S` on `g`
  have hact : ∀ x, kernelFun (KernelPower.rem k c φ) ν (f : X → ℝ) x = ∫ y, s x y * g y ∂ν := by
    intro x
    have i1 : Integrable (fun y => s x y * (f : X → ℝ) y) ν := integrable_row_mul hsr.meas hCs hf1 x
    have i2 : Integrable (fun y => s x y * φ y) ν :=
      integrable_row_mul hsr.meas hCs (integrable_of_bdd hφm hφb) x
    have e1 : (fun y => KernelPower.rem k c φ x y * (f : X → ℝ) y)
        = fun y => s x y * (f : X → ℝ) y - (μ' * φ x) * ((f : X → ℝ) y * φ y) := by
      funext y; rw [hrs]; ring
    have e2 : (fun y => s x y * g y)
        = fun y => s x y * (f : X → ℝ) y - A * (s x y * φ y) := by
      funext y; simp only [hg]; ring
    unfold kernelFun
    rw [e1, e2, integral_sub i1 (hfφ.const_mul _), integral_sub i1 (i2.const_mul _),
      integral_const_mul, integral_const_mul, heigs x]
    ring
  have hnorm : ‖kernelCLM (KernelPower.rem k c φ) C' hm h0 hb ν ν f‖ ^ 2
      = ∫ x, (∫ y, s x y * g y ∂ν) ^ 2 ∂ν := by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_kernelCLM (KernelPower.rem k c φ) C' hm h0 hb ν ν f] with x hx
    rw [hx, hact x]
  have hg2 : ∫ y, g y ^ 2 ∂ν ≤ ‖f‖ ^ 2 := by
    rw [norm_sq_eq_integral]
    have e : (fun y => g y ^ 2) = fun y => (f : X → ℝ) y ^ 2
        - (2 * A) * ((f : X → ℝ) y * φ y) + A ^ 2 * φ y ^ 2 := by
      funext y; simp only [hg]; ring
    have i1 : Integrable (fun y => (f : X → ℝ) y ^ 2) ν := hfL.integrable_sq
    have j1 : Integrable (fun y => (f : X → ℝ) y ^ 2 - (2 * A) * ((f : X → ℝ) y * φ y)) ν :=
      i1.sub (hfφ.const_mul _)
    have j2 : Integrable (fun y => A ^ 2 * φ y ^ 2) ν := hφ2.const_mul _
    rw [e, integral_add j1 j2, integral_sub i1 (hfφ.const_mul _), integral_const_mul,
      integral_const_mul, hφ1, ← hA]
    nlinarith [sq_nonneg A]
  have hfin : ‖kernelCLM (KernelPower.rem k c φ) C' hm h0 hb ν ν f‖ ^ 2 ≤ (μ' * ‖f‖) ^ 2 := by
    rw [hnorm, mul_pow]
    exact hS.trans (mul_le_mul_of_nonneg_left hg2 (sq_nonneg _))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hμ0 (norm_nonneg _)) (by norm_num)).mp hfin

end Schur

/-! ## 5. The window read: the second eigenvalue is bounded by the excited weight -/

section Read

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
  {k : X → X → ℝ} {C : ℝ} {hkm : Measurable (Function.uncurry k)} {hC0 : 0 ≤ C}
  {hkb : ∀ x y, |k x y| ≤ C} {c : ℝ} {φ : X → ℝ} {ρ : ℝ}

/-- **The second eigenvalue is read by the excited weight**: at a dyadic time,
`(ρ/|c|)^{2j} ≤ e(2j)`. A self-adjoint remainder has `‖R^{2^a}‖ = ‖R‖^{2^a}`, and `‖R^j‖² ≤ hs(r^{∗j})`.
DERIVED: `2` the `L²` exponent and the dyadic time. -/
theorem IsTop.ratio_le_excited (h : IsTop ν k C hkm hC0 hkb c φ ρ) (hsym : ∀ x y, k x y = k y x)
    (a : ℕ) : (ρ / |c|) ^ (2 * 2 ^ a) ≤ KernelPower.excited ν k c φ (2 ^ a) := by
  obtain ⟨C', hm, h0, hb, e⟩ := h.rem
  obtain ⟨B, hφb⟩ := h.bdd
  have hk : Bdd k := ⟨hkm, C, hkb⟩
  have hr := Bdd.rem hk h.meas hφb (c := c)
  have hl : 0 < |c| := abs_pos.mpr h.ne
  set R := kernelCLM (KernelPower.rem k c φ) C' hm h0 hb ν ν with hR
  have hrsym : ∀ x y, KernelPower.rem k c φ x y = KernelPower.rem k c φ y x := fun x y => by
    simp only [KernelPower.rem]; rw [hsym x y]; ring
  have hsa : IsSelfAdjoint R :=
    MassGap.SlabTransferAdjoint.isSelfAdjoint_kernelCLM_of_symm _ _ _ _ _ _ hrsym
  have hpow : ‖R ^ 2 ^ a‖ = ρ ^ 2 ^ a := by rw [← e]; exact hsa.norm_pow_two_pow a
  set H := hs ν (iter ν (KernelPower.rem k c φ) (2 ^ a - 1)) with hH
  have hH0 : 0 ≤ H := hs_nonneg _
  have hj : 2 ^ a - 1 + 1 = 2 ^ a := Nat.sub_add_cancel Nat.one_le_two_pow
  have hle : ‖R ^ 2 ^ a‖ ≤ Real.sqrt H := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun f => ?_
    have h2 : ‖(R ^ 2 ^ a) f‖ ^ 2 ≤ H * ‖f‖ ^ 2 := by
      rw [norm_sq_eq_integral]
      have hae := KernelGap.opPow_coe hm h0 hb f (2 ^ a - 1)
      rw [hj] at hae
      have e2 : ∫ x, (((R ^ 2 ^ a) f : Lp ℝ 2 ν) : X → ℝ) x ^ 2 ∂ν
          = ∫ x, kernelFun (iter ν (KernelPower.rem k c φ) (2 ^ a - 1)) ν (f : X → ℝ) x ^ 2 ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx]
      rw [e2]
      exact KernelGap.integral_kernelFun_sq_le (hr.iter _) f
    have h3 : (Real.sqrt H * ‖f‖) ^ 2 = H * ‖f‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hH0]
    rw [← h3] at h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h2
  have hsq : (ρ ^ 2 ^ a) ^ 2 ≤ H := by
    rw [← hpow]
    calc ‖R ^ 2 ^ a‖ ^ 2 ≤ Real.sqrt H ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = H := Real.sq_sqrt hH0
  unfold KernelPower.excited
  rw [div_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc ρ ^ (2 * 2 ^ a) = (ρ ^ 2 ^ a) ^ 2 := by rw [← pow_mul]; ring_nf
    _ ≤ H := hsq

end Read

/-! ## 6. The fork on the Wilson torus of a compact group -/

section Group

open MassGap.DoublingRecursion MassGap.DoublingWilson MassGap.DoublingWilsonG
  MassGap.RectWilson MassGap.RectWilsonG MassGap.RectTransferG MassGap.GaugeGroup

variable (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]

/-- The slice of step `i` at time `m`: the sides transverse to `i` at the corner `uP i`. -/
abbrev sliceT (m : ℕ) (i : Fin 4) : {j : Fin 4 // j ≠ i} → ℕ := tr (ext m (uP i)) i

/-- `(c, φ)` is a top pair of the Wilson slice transfer of `G`, and `ρ` the norm of its remainder. -/
def TopG {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) (c : ℝ)
    (φ : (SpT i T → G) → ℝ) (ρ : ℝ) : Prop :=
  IsTop (hSG G i T) (kTG G i T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ) c φ ρ

/-- The doubling defect at side `2^w`. -/
def Dw (β : ℝ) (w : ℕ) : ℝ := TorusDoubling.defectWG G 4 (wilsonDensityG G) β (2 ^ w)

variable {G} {β : ℝ}

/-- **Perron–Frobenius on the Wilson slice, for every compact group, at every coupling**: the top pair has
a strictly positive eigenfunction, and the second eigenvalue is at most `c − a c²`,
`a = kTmin = e^{−β M}`. So the top is simple at every finite slice, with a gap of volume order.
DERIVED: `2` the `L²` exponent, from `B = 1/c`. -/
theorem exists_topG (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) :
    ∃ (c : ℝ) (φ : (SpT i T → G) → ℝ) (ρ : ℝ), TopG G hβ i T c φ ρ ∧ 0 < c ∧
      ρ ≤ c - RectTransfer.kTmin i T β * c ^ 2 ∧ ∀ x, 0 < φ x := by
  obtain ⟨hK, φ, hφm, hφb, ⟨c₀, hc₀, hlow⟩, hφ1, heig⟩ :=
    JentzschKT.exists_pos_eigen (μ := hSG G i T) (continuous_kTG (μ := i) (T := T) β) zero_le_one
      (abs_kTG_le hβ) (kTG_symm β) (RectTransfer.kTmin_pos (μ := i) (T := T) β) (kTG_lower hβ)
  set c := ‖kernelCLM (kTG G i T β) 1 (continuous_kTG β).measurable zero_le_one (abs_kTG_le hβ)
    (hSG G i T) (hSG G i T)‖ with hcdef
  have hk : Bdd (kTG G i T β) := bdd_kTG hβ
  have hr := Bdd.rem hk hφm hφb (c := c)
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hb : ∀ x y, |KernelPower.rem (kTG G i T β) c φ x y| ≤ max Cr 0 :=
    fun x y => (hCr x y).trans (le_max_left _ _)
  have hS := schur_gap (ν := hSG G i T) hk (kTG_symm β) (RectTransfer.kTmin_pos (μ := i) (T := T) β)
    (kTG_lower hβ) hφm hc₀ hlow (B := 1 / c) (fun x => (le_abs_self _).trans (hφb x)) hφ1 heig
    hr.meas (le_max_right _ _) hb
  refine ⟨c, φ, _, ⟨hφm, ⟨_, hφb⟩, hφ1, hK.ne', heig, abs_of_pos hK, _, hr.meas,
    le_max_right _ _, hb, rfl⟩, hK,
    ?_, fun x => lt_of_lt_of_le hc₀ (hlow x)⟩
  have e : RectTransfer.kTmin i T β / (1 / c) ^ 2 = RectTransfer.kTmin i T β * c ^ 2 := by
    field_simp
  rw [← e]
  exact hS

theorem exists_ratio (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ ∃ (c : ℝ) (φ : (SpT i T → G) → ℝ) (ρ : ℝ),
      TopG G hβ i T c φ ρ ∧ y = ρ / |c| := by
  obtain ⟨c, φ, ρ, hT, hc, hρ, -⟩ := exists_topG (G := G) hβ i T
  have ha : 0 < RectTransfer.kTmin i T β * c ^ 2 := mul_pos (RectTransfer.kTmin_pos β) (by positivity)
  refine ⟨ρ / |c|, div_nonneg (IsTop.rho_nonneg hT) (abs_nonneg _), ?_, c, φ, ρ, hT, rfl⟩
  rw [abs_of_pos hc, div_lt_one hc]
  linarith

variable (G) in
/-- `λ₁/λ₀` of the Wilson slice transfer. -/
def topRatio {β : ℝ} (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) : ℝ :=
  Classical.choose (exists_ratio (G := G) hβ i T)

theorem topRatio_spec (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) :
    0 ≤ topRatio G hβ i T ∧ topRatio G hβ i T < 1 ∧ ∃ (c : ℝ) (φ : (SpT i T → G) → ℝ) (ρ : ℝ),
      TopG G hβ i T c φ ρ ∧ topRatio G hβ i T = ρ / |c| :=
  Classical.choose_spec (exists_ratio (G := G) hβ i T)

variable (G) in
/-- The window read of step `i`: `(λ₁/λ₀)^{2^w}` on the slice of that step. -/
def winRead {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) : ℝ :=
  topRatio G hβ i (sliceT (2 ^ w) i) ^ 2 ^ w

variable (G) in
/-- The window read: the largest of the four steps. -/
def Yw {β : ℝ} (hβ : 0 ≤ β) (w : ℕ) : ℝ := Finset.univ.sup' Finset.univ_nonempty (winRead G hβ w)

theorem winRead_nonneg (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) : 0 ≤ winRead G hβ w i :=
  pow_nonneg (topRatio_spec hβ i _).1 _

theorem winRead_le_Yw (hβ : 0 ≤ β) (w : ℕ) (i : Fin 4) : winRead G hβ w i ≤ Yw G hβ w :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem Yw_nonneg (hβ : 0 ≤ β) (w : ℕ) : 0 ≤ Yw G hβ w :=
  (winRead_nonneg hβ w 0).trans (winRead_le_Yw hβ w 0)

/-- **The window read stays below `1`.** Every slice is gapped: `T` is never exact degeneracy. -/
theorem Yw_lt_one (hβ : 0 ≤ β) (w : ℕ) : Yw G hβ w < 1 := by
  rw [Yw, Finset.sup'_lt_iff]
  intro i _
  have h := topRatio_spec (G := G) hβ i (sliceT (2 ^ w) i)
  exact pow_lt_one₀ h.1 h.2.1 (by positivity)

/-- **The fork at one step of the torus.** `m = 2j`: the defect on the slice of step `i` at time `2m` is at
most `2 (ρ/|c|)^m (exp p − 1)`, `p` the defect at time `m`. -/
theorem fork_step (hβ : 0 ≤ β) {j m : ℕ} (hj : 1 ≤ j) (hm : m = 2 * j) (i : Fin 4) {c : ℝ}
    {φ : (SpT i (sliceT m i) → G) → ℝ} {ρ : ℝ} (h : TopG G hβ i (sliceT m i) c φ ρ) :
    p (xWG G m β) i (uP i + E i)
      ≤ 2 * (ρ / |c|) ^ m * (Real.exp (p (xWG G m β) i (uP i)) - 1) := by
  subst hm
  have hn : 2 ≤ 2 * j := by omega
  have he : Even (2 * j) := even_two_mul j
  have hs := IsTop.level_step h (kTG_symm β) j hj
  have e1 : ext (2 * j) (uP i) i = 2 * j := by simp [ext, uP_self]
  have x1 := xWG_eq (G := G) hβ hn he (uP i) i
  have x2 := xWG_eq (G := G) hβ hn he (uP i + E i) i
  have x3 := xWG_eq (G := G) hβ hn he (uP i + E i + E i) i
  rw [e1] at x1
  rw [tr_ext_add, ext_add_self, e1] at x2
  rw [tr_ext_add, tr_ext_add, ext_add_self, ext_add_self, e1] at x3
  have p1 : p (xWG G (2 * j) β) i (uP i)
      = DoublingPower.defect (traceSeq (hSG G i (sliceT (2 * j) i)) (kTG G i (sliceT (2 * j) i) β))
        (2 * j) := by
    rw [p, x1, x2]; rfl
  have p2 : p (xWG G (2 * j) β) i (uP i + E i)
      = DoublingPower.defect (traceSeq (hSG G i (sliceT (2 * j) i)) (kTG G i (sliceT (2 * j) i) β))
        (2 * (2 * j)) := by
    rw [p, x2, x3]; rfl
  rw [p1, p2]
  exact hs

theorem Dw_corner0 (β : ℝ) (w : ℕ) : Δ (xWG G (2 ^ w) β) (corner 0) = Dw G β w :=
  Δ_corner0G G _ β

theorem Dw_corner1 (β : ℝ) (w : ℕ) : Δ (xWG G (2 ^ w) β) (corner 1) = Dw G β (w + 1) := by
  rw [Δ_cornerG G (2 ^ w) 1 β, Dw]
  congr 1
  ring

theorem window_data {w : ℕ} (hw : 1 ≤ w) :
    ∃ j, 1 ≤ j ∧ 2 ^ w = 2 * j ∧ j = 2 ^ (w - 1) ∧ 2 ≤ 2 ^ w ∧ Even (2 ^ w) := by
  obtain ⟨u, rfl⟩ : ∃ u, w = u + 1 := ⟨w - 1, by omega⟩
  refine ⟨2 ^ u, Nat.one_le_two_pow, by ring, by simp, ?_, ?_⟩
  · have : 1 ≤ 2 ^ u := Nat.one_le_two_pow
    rw [pow_succ]; omega
  · exact ⟨2 ^ u, by ring⟩

theorem Dw_nonneg (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) : 0 ≤ Dw G β w := by
  obtain ⟨j, -, -, -, hn, he⟩ := window_data hw
  rw [← Dw_corner0]
  exact Δ_corner_nonneg (positiveG hβ hn he)

/-- **The exact fork of a window.** At every `β ≥ 0`, window `w ≥ 1`, every compact group:
`D(w+1) ≤ 30 Y(w) (exp(8 D(w) + 2 D(w+1)) − 1)`. A defect forces the transfer's second eigenvalue on a step
slice at the window's own time, or an exponentially larger defect. DERIVED: `30 = 2 · 15`, the square in the
purity and the sum of the path weights; `8`, `2` from `pred_le`. -/
theorem fork_quant (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    Dw G β (w + 1) ≤ 30 * Yw G hβ w * (Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) - 1) := by
  obtain ⟨j, hj, hm, -, hn, he⟩ := window_data hw
  have hx := positiveG (G := G) hβ hn he
  obtain ⟨i, hi⟩ := exists_step hx
  obtain ⟨-, -, c, φ, ρ, hT, hy⟩ := topRatio_spec (G := G) hβ i (sliceT (2 ^ w) i)
  have hf := fork_step hβ hj hm i hT
  have hp := pred_le hx i
  rw [Dw_corner0, Dw_corner1] at hp
  rw [Dw_corner1] at hi
  rw [← hy] at hf
  have hu0 : 0 ≤ p (xWG G (2 ^ w) β) i (uP i) := hx.nonneg i (uP i)
  have h1 : Real.exp (p (xWG G (2 ^ w) β) i (uP i)) - 1
      ≤ Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) - 1 := by
    have := Real.exp_le_exp.mpr hp
    linarith
  have h2 : 0 ≤ Real.exp (p (xWG G (2 ^ w) β) i (uP i)) - 1 := by
    have := Real.one_le_exp hu0
    linarith
  have h3 : topRatio G hβ i (sliceT (2 ^ w) i) ^ 2 ^ w ≤ Yw G hβ w := winRead_le_Yw hβ w i
  have h4 : 0 ≤ topRatio G hβ i (sliceT (2 ^ w) i) ^ 2 ^ w := winRead_nonneg hβ w i
  have h5 := mul_le_mul h3 h1 h2 (Yw_nonneg (G := G) hβ w)
  nlinarith

/-- **The read is at most the defect.** `y_i(w) ≤ exp(8 D(w) + 2 D(w+1)) − 1`, the converse of the fork.
DERIVED: `8`, `2` from `pred_le`. -/
theorem winRead_le (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) (i : Fin 4) :
    winRead G hβ w i ≤ Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) - 1 := by
  obtain ⟨j, hj, hm, hjp, hn, he⟩ := window_data hw
  have hx := positiveG (G := G) hβ hn he
  obtain ⟨-, -, c, φ, ρ, hT, hy⟩ := topRatio_spec (G := G) hβ i (sliceT (2 ^ w) i)
  have hp := pred_le hx i
  rw [Dw_corner0, Dw_corner1] at hp
  have h1 := IsTop.ratio_le_excited hT (kTG_symm β) (w - 1)
  have hfacts := IsTop.powerFacts hT (kTG_symm β) j hj
  have h2 := DoublingPower.excited_le hfacts
  have e1 : ext (2 ^ w) (uP i) i = 2 * j := by simp [ext, uP_self, hm]
  have x1 := xWG_eq (G := G) hβ hn he (uP i) i
  have x2 := xWG_eq (G := G) hβ hn he (uP i + E i) i
  rw [e1] at x1
  rw [tr_ext_add, ext_add_self, e1] at x2
  have p1 : p (xWG G (2 ^ w) β) i (uP i)
      = DoublingPower.defect (traceSeq (hSG G i (sliceT (2 ^ w) i)) (kTG G i (sliceT (2 ^ w) i) β))
        (2 * j) := by
    rw [p, x1, x2]; rfl
  rw [← p1] at h2
  have e2 : 2 * 2 ^ (w - 1) = 2 ^ w := by rw [← hjp, ← hm]
  rw [e2, ← hjp] at h1
  have h3 : winRead G hβ w i = (ρ / |c|) ^ 2 ^ w := by rw [winRead, hy]
  have := Real.exp_le_exp.mpr hp
  rw [h3]
  linarith

theorem Yw_le (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    Yw G hβ w ≤ Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) - 1 :=
  Finset.sup'_le _ _ fun i _ => winRead_le hβ hw i

/-- **A bounded stall** at `β`: eventually `s ≤ D(w) ≤ A`. -/
def BoundedStall (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] [GaugeGroup G]
    (β s A : ℝ) : Prop := ∀ᶠ w in atTop, s ≤ Dw G β w ∧ Dw G β w ≤ A

/-- **A bounded stall has a level in the window.** Eventually `c₀ ≤ Y(w)`, `c₀ = s/(30 (e^{10A} − 1))`. So the
second eigenvalue of a step slice stays within `log(1/c₀)/2^w` of the top. DERIVED: `10 = 8 + 2`; `30` from
`fork_quant`. -/
theorem level_floor (hβ : 0 ≤ β) {s A : ℝ} (hs : 0 < s) (h : BoundedStall G β s A) :
    0 < s / (30 * (Real.exp (10 * A) - 1)) ∧
      ∀ᶠ w in atTop, s / (30 * (Real.exp (10 * A) - 1)) ≤ Yw G hβ w := by
  obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp h
  have hA : 0 < A := lt_of_lt_of_le hs ((hw₀ w₀ le_rfl).1.trans (hw₀ w₀ le_rfl).2)
  have hE : 0 < Real.exp (10 * A) - 1 := by
    have : 1 < Real.exp (10 * A) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  refine ⟨by positivity, eventually_atTop.mpr ⟨max w₀ 1, fun w hw => ?_⟩⟩
  have h1 : w₀ ≤ w := (le_max_left _ _).trans hw
  have h2 : 1 ≤ w := (le_max_right _ _).trans hw
  have hf := fork_quant (G := G) hβ h2
  have b1 := hw₀ w h1
  have b2 := hw₀ (w + 1) (by omega)
  have hle : Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) ≤ Real.exp (10 * A) :=
    Real.exp_le_exp.mpr (by linarith [b1.2, b2.2])
  have hY := Yw_nonneg (G := G) hβ w
  have h3 : 30 * Yw G hβ w * (Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) - 1)
      ≤ 30 * Yw G hβ w * (Real.exp (10 * A) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [b2.1]

/-- **The dichotomy.** A bounded stall has `c₀ ≤ Y(w) < 1` eventually, and either (T) `Y` comes frequently
within every `δ` of `1`: a level with `gap · 2^w` along a subsequence tending to `0`, or (M) `Y ≤ 1 − δ` eventually: the lowest level sits at
`gap ≍ 2^{−w}`, between `δ` and `log(1/c₀)`. The content is the floor; the split is exhaustive. -/
theorem stall_dichotomy (hβ : 0 ≤ β) {s A : ℝ} (hs : 0 < s) (h : BoundedStall G β s A) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ (∀ᶠ w in atTop, c₀ ≤ Yw G hβ w ∧ Yw G hβ w < 1) ∧
      ((∀ δ : ℝ, 0 < δ → ∃ᶠ w in atTop, 1 - δ < Yw G hβ w) ∨
        (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w in atTop, Yw G hβ w ≤ 1 - δ)) := by
  obtain ⟨h0, hfl⟩ := level_floor hβ hs h
  refine ⟨_, h0, hfl.mono fun w hw => ⟨hw, Yw_lt_one hβ w⟩, ?_⟩
  by_cases hT : ∀ δ : ℝ, 0 < δ → ∃ᶠ w in atTop, 1 - δ < Yw G hβ w
  · exact Or.inl hT
  · right
    push_neg at hT
    obtain ⟨δ, hδ, hn⟩ := hT
    exact ⟨δ, hδ, hn⟩

/-- **A vanishing read with a bounded defect makes the defect vanish.** This is
`WindowFreq.GapGivesVanishing` on the step slices, with its missing clause named: the bound on `D`. -/
theorem vanishes_of_read (hβ : 0 ≤ β) {A : ℝ} (hA : ∀ᶠ w in atTop, Dw G β w ≤ A)
    (hY : Tendsto (Yw G hβ) atTop (𝓝 0)) : Tendsto (Dw G β) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  obtain ⟨w₀, hw₀⟩ := eventually_atTop.mp hA
  have hlim : Tendsto (fun w => 30 * Yw G hβ w * (Real.exp (10 * |A|) - 1)) atTop (𝓝 0) := by
    have := (hY.const_mul 30).mul_const (Real.exp (10 * |A|) - 1)
    simpa using this
  refine squeeze_zero' (eventually_atTop.mpr ⟨1, fun w hw => Dw_nonneg hβ (by omega)⟩) ?_ hlim
  refine eventually_atTop.mpr ⟨max w₀ 1, fun w hw => ?_⟩
  have h1 : w₀ ≤ w := (le_max_left _ _).trans hw
  have h2 : 1 ≤ w := (le_max_right _ _).trans hw
  have hf := fork_quant (G := G) hβ h2
  have b1 := hw₀ w h1
  have b2 := hw₀ (w + 1) (by omega)
  have hle : Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) ≤ Real.exp (10 * |A|) :=
    Real.exp_le_exp.mpr (by linarith [le_abs_self A])
  have hY0 := Yw_nonneg (G := G) hβ w
  have h3 : 30 * Yw G hβ w * (Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) - 1)
      ≤ 30 * Yw G hβ w * (Real.exp (10 * |A|) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **A vanishing defect makes the read vanish.** -/
theorem read_of_vanishes (hβ : 0 ≤ β) (hD : Tendsto (Dw G β) atTop (𝓝 0)) :
    Tendsto (Yw G hβ) atTop (𝓝 0) := by
  have hD1 : Tendsto (fun w => Dw G β (w + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hD
  have hsum : Tendsto (fun w => 8 * Dw G β w + 2 * Dw G β (w + 1)) atTop (𝓝 0) := by
    simpa using (hD.const_mul 8).add (hD1.const_mul 2)
  have hexp : Tendsto (fun w => Real.exp (8 * Dw G β w + 2 * Dw G β (w + 1)) - 1) atTop (𝓝 0) := by
    have := (Real.continuous_exp.tendsto 0).comp hsum
    simpa [Function.comp_def] using this.sub_const 1
  exact squeeze_zero' (Eventually.of_forall fun w => Yw_nonneg hβ w)
    (eventually_atTop.mpr ⟨1, fun w hw => Yw_le hβ hw⟩) hexp

/-- **The defect vanishes exactly when it is bounded and the read vanishes**, at every `β ≥ 0`, for every
compact group. The bound on `D` is the third alternative: its failure is the Hagedorn branch. -/
theorem vanishes_iff_read (hβ : 0 ≤ β) :
    Tendsto (Dw G β) atTop (𝓝 0) ↔
      (∃ A : ℝ, ∀ᶠ w in atTop, Dw G β w ≤ A) ∧ Tendsto (Yw G hβ) atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨⟨1, (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono fun _ hw => hw.le⟩,
      read_of_vanishes hβ h⟩
  · rintro ⟨⟨A, hA⟩, hY⟩
    exact vanishes_of_read hβ hA hY

/-- **A positive lattice mass cannot carry a bounded stall.** If `Y(w) ≤ e^{−m 2^w}` and `D(w) ≥ s > 0`
eventually, then eventually `m 2^w + log(s/30) ≤ 8 D(w) + 2 D(w+1)`: the defect grows at least linearly in the
side. DERIVED: `30`, `8`, `2` from `fork_quant`. -/
theorem massive_stall_grows (hβ : 0 ≤ β) {m s : ℝ} (hs : 0 < s)
    (hm : ∀ᶠ w : ℕ in atTop, Yw G hβ w ≤ Real.exp (-(m * 2 ^ w)))
    (hD : ∀ᶠ w in atTop, s ≤ Dw G β w) :
    ∀ᶠ w : ℕ in atTop, m * 2 ^ w + Real.log (s / 30) ≤ 8 * Dw G β w + 2 * Dw G β (w + 1) := by
  obtain ⟨w₁, h1⟩ := eventually_atTop.mp hm
  obtain ⟨w₂, h2⟩ := eventually_atTop.mp hD
  refine eventually_atTop.mpr ⟨max (max w₁ w₂) 1, fun w hw => ?_⟩
  have a1 : w₁ ≤ w := ((le_max_left _ _).trans (le_max_left _ _)).trans hw
  have a2 : w₂ ≤ w := ((le_max_right _ _).trans (le_max_left _ _)).trans hw
  have a3 : 1 ≤ w := (le_max_right _ _).trans hw
  set X := 8 * Dw G β w + 2 * Dw G β (w + 1) with hX
  have hf := fork_quant (G := G) hβ a3
  have hb := h2 (w + 1) (by omega)
  have hy := h1 w a1
  have hY0 := Yw_nonneg (G := G) hβ w
  have hE0 : 0 ≤ Real.exp X - 1 := by
    have hX0 : 0 ≤ X := by
      have := Dw_nonneg (G := G) hβ a3
      have := Dw_nonneg (G := G) hβ (w := w + 1) (by omega)
      positivity
    have := Real.one_le_exp hX0
    linarith
  have h3 : Yw G hβ w * (Real.exp X - 1) ≤ Real.exp (-(m * 2 ^ w)) * Real.exp X := by
    refine mul_le_mul hy (by linarith) hE0 (Real.exp_pos _).le
  have h4 : s / 30 ≤ Real.exp (-(m * 2 ^ w) + X) := by
    rw [Real.exp_add]
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have h5 := Real.log_le_log (by positivity) h4
  rw [Real.log_exp] at h5
  linarith

end Group

/-! ## 7. `SU(N)`: the window coupling, and the neutral top -/

section SU

open MassGap.RectTransfer MassGap.RectWilson MassGap.CouplingTower

variable {N : ℕ} [NeZero N] {β : ℝ}

theorem Dw_SU (β : ℝ) (w : ℕ) : Dw (MassGap.SUN.SU N) β w = windowCoupling N β w := by
  unfold Dw windowCoupling
  rw [GaugeInstances.wilsonDensityG_SU]
  exact TorusDoubling.defectWG_four_eq N β _

/-- **The vanishing read of `SU(N)` is a bounded defect with a vanishing window read.** -/
theorem vanishes_iff_read_SU (hβ : 0 ≤ β) :
    StrongAnchor.Vanishes N β ↔ (∃ A : ℝ, ∀ᶠ w in atTop, windowCoupling N β w ≤ A) ∧
      Tendsto (Yw (MassGap.SUN.SU N) hβ) atTop (𝓝 0) := by
  have e : Dw (MassGap.SUN.SU N) β = windowCoupling N β := funext (Dw_SU β)
  have h := vanishes_iff_read (G := MassGap.SUN.SU N) hβ
  rw [e] at h
  exact h

/-- **The strong end is a bounded defect with a vanishing window read, frequently at large `β`.** -/
theorem strongEnd_iff_read :
    StrongEnd N ↔ ∃ᶠ β in atTop, ∃ hβ : (0 : ℝ) ≤ β,
      (∃ A : ℝ, ∀ᶠ w in atTop, windowCoupling N β w ≤ A) ∧
        Tendsto (Yw (MassGap.SUN.SU N) hβ) atTop (𝓝 0) := by
  rw [StrongAnchor.strongEnd_iff_frequently_vanishes]
  constructor
  · intro h
    exact (h.and_eventually (eventually_ge_atTop 0)).mono fun β hb =>
      ⟨hb.2, (vanishes_iff_read_SU hb.2).mp hb.1⟩
  · intro h
    exact h.mono fun β ⟨hβ, hb⟩ => (vanishes_iff_read_SU hβ).mpr hb

/-- **The fork of `SU(N)`.** -/
theorem fork_SU (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    windowCoupling N β (w + 1) ≤ 30 * Yw (MassGap.SUN.SU N) hβ w *
      (Real.exp (8 * windowCoupling N β w + 2 * windowCoupling N β (w + 1)) - 1) := by
  have h := fork_quant (G := MassGap.SUN.SU N) hβ hw
  rwa [Dw_SU, Dw_SU] at h

/-- **Perron–Frobenius on the `SU(N)` slice, with the tree's gap datum.** At every `β ≥ 0` and every slice the
Jentzsch top is a `TransferGapAt` with `ρ < λ = ‖K‖`, with no restriction on the coupling. -/
theorem exists_gap_kT (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) :
    ∃ (lam : ℝ) (φ : (SpT i T → MassGap.SUN.SU N) → ℝ) (ρ : ℝ),
      SliceTransferGap.TransferGapAt N i T β lam φ ρ ∧ 0 ≤ ρ ∧ ρ < lam ∧ ∀ x, 0 < φ x := by
  have hN := NeZero.ne N
  obtain ⟨hK, φ, hφm, hφb, ⟨c₀, hc₀, hlow⟩, hφ1, heig⟩ :=
    JentzschKT.exists_pos_eigen_kT (μ := i) (T := T) (N := N) hN hβ
  set c := ‖kernelCLM (kT i T N β) 1 (continuous_kT β).measurable zero_le_one (abs_kT_le hN hβ)
    (hS i T N) (hS i T N)‖ with hcdef
  have hk : Bdd (kT i T N β) := bdd_kT hN hβ
  have hr := Bdd.rem hk hφm hφb (c := c)
  obtain ⟨Cr, hCr⟩ := hr.bdd
  have hb : ∀ x y, |KernelPower.rem (kT i T N β) c φ x y| ≤ max Cr 0 :=
    fun x y => (hCr x y).trans (le_max_left _ _)
  have hS' := schur_gap (ν := hS i T N) hk (kT_symm β) (kTmin_pos (μ := i) (T := T) β)
    (kT_lower hN hβ) hφm hc₀ hlow (B := 1 / c) (fun x => (le_abs_self _).trans (hφb x)) hφ1 heig
    hr.meas (le_max_right _ _) hb
  have e : kTmin i T β / (1 / c) ^ 2 = kTmin i T β * c ^ 2 := by field_simp
  rw [e] at hS'
  have ha : 0 < kTmin i T β * c ^ 2 := mul_pos (kTmin_pos β) (by positivity)
  exact ⟨c, φ, _, ⟨hφm, ⟨_, hφb⟩, hφ1, hK.ne', heig, max Cr 0, hr.meas, le_max_right _ _, hb, le_rfl⟩,
    norm_nonneg _, by linarith, fun x => lt_of_lt_of_le hc₀ (hlow x)⟩

/-- **The vacuum of the slice is neutral at every coupling.** The top eigenfunction of every `SU(N)` slice is
invariant under the centre `Z_N³`, and the flux trace lies wholly in the remainder, at every `β ≥ 0`. In
`SliceTransferGap` both were conditional on a gap; the gap is now proved at each finite slice. So a flux state
is always excited: a top cluster carried by the flux is never exact. -/
theorem top_centre_neutral (hβ : 0 ≤ β) (i : Fin 4) (T : {j : Fin 4 // j ≠ i} → ℕ) :
    ∃ (lam : ℝ) (φ : (SpT i T → MassGap.SUN.SU N) → ℝ) (ρ : ℝ),
      SliceTransferGap.TransferGapAt N i T β lam φ ρ ∧ ρ < lam ∧
      (∀ (g : SliceCentreAction.Cen i N) (x : SpT i T → MassGap.SUN.SU N),
        φ (SliceCentreAction.act g x) = φ x) ∧
      ∀ j : ℕ, TorusContraction.fluxTrace N i T β j
        = hs (hS i T N) (RelayChain.fk (iter (hS i T N) (KernelPower.rem (kT i T N β) lam φ) j)
          (SliceCentreAction.act (μ := i) (T := T) (N := N))) := by
  obtain ⟨lam, φ, ρ, h, hρ0, hρ, -⟩ := exists_gap_kT (N := N) hβ i T
  have hsq : ρ ^ 2 < lam ^ 2 := pow_lt_pow_left₀ hρ hρ0 (by norm_num)
  exact ⟨lam, φ, ρ, h, hρ, SliceTransferGap.phi_act_kT hβ h hsq,
    SliceTransferGap.fluxTrace_eq_rem hβ h hsq⟩

/-- **A stall above the flux cap is zero-flux**: `D − 90 log N ≤ restW`. The flux half is capped at every `β`. -/
theorem large_stall_zero_flux (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w) :
    windowCoupling N β w - 90 * Real.log N ≤ FlatCap.restW N β w := by
  have := FlatCap.windowCoupling_le_rest_add_cap (N := N) hβ hw
  linarith

/-- **`β = 0`.** The window read vanishes at the ultralocal point. -/
theorem Yw_zero_coupling {w : ℕ} (hw : 1 ≤ w) : Yw (MassGap.SUN.SU N) (le_refl (0 : ℝ)) w = 0 := by
  refine le_antisymm ?_ (Yw_nonneg _ w)
  have h := Yw_le (G := MassGap.SUN.SU N) (le_refl (0 : ℝ)) hw
  rw [Dw_SU, Dw_SU, windowCoupling_zero, windowCoupling_zero] at h
  simpa using h

end SU

/-! ## 8. Perron–Frobenius excludes nothing uniform: a stall with no symmetry -/

section Biased

open scoped ENNReal

/-- Two points of weights `1/3`, `2/3`.

CHOSEN: the weights `1/3`, `2/3` (`3` their denominator): any unequal pair has no symmetry; choosing them costs
nothing, the example only needs a biased two-point measure. -/
def νW : Measure Bool := ((3 : ℝ≥0∞)⁻¹) • Measure.dirac true + (2 * (3 : ℝ≥0∞)⁻¹) • Measure.dirac false

theorem integral_νW (f : Bool → ℝ) : ∫ x, f x ∂νW = f true / 3 + 2 * f false / 3 := by
  have i1 : Integrable f (((3 : ℝ≥0∞)⁻¹) • Measure.dirac true : Measure Bool) := by
    refine Integrable.smul_measure ?_ (by simp)
    exact integrable_dirac (by simp)
  have i2 : Integrable f ((2 * (3 : ℝ≥0∞)⁻¹) • Measure.dirac false : Measure Bool) := by
    refine Integrable.smul_measure ?_ (by simp [ENNReal.mul_eq_top])
    exact integrable_dirac (by simp)
  rw [νW, integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, smul_eq_mul]
  norm_num
  ring

/-- `νW` has total mass one.

CHOSEN: `3` the denominator of `νW`'s weights `1/3`, `2/3` (any unequal pair serves). -/
instance : IsProbabilityMeasure νW := by
  constructor
  simp only [νW, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [show (3 : ℝ≥0∞)⁻¹ + 2 * 3⁻¹ = (1 + 2) * 3⁻¹ by ring]
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- `1 + r g⊗g`, `g = (√2, −1/√2)`: the mean-zero unit vector of `νW`. -/
def kW (r : ℝ) (x y : Bool) : ℝ :=
  match x, y with
  | true, true => 1 + 2 * r
  | true, false => 1 - r
  | false, true => 1 - r
  | false, false => 1 + r / 2

theorem conv_kW (r q : ℝ) : conv νW (kW r) (kW q) = kW (r * q) := by
  funext x z
  unfold conv
  rw [integral_νW]
  cases x <;> cases z <;> simp only [kW] <;> ring

theorem iter_kW (r : ℝ) : ∀ i : ℕ, iter νW (kW r) i = kW (r ^ (i + 1))
  | 0 => by simp [iter]
  | i + 1 => by
    change conv νW (kW r) (iter νW (kW r) i) = _
    rw [iter_kW r i, conv_kW]
    congr 1
    ring

theorem hs_kW (r : ℝ) : hs νW (kW r) = 1 + r ^ 2 := by
  unfold hs
  simp_rw [integral_νW]
  simp only [kW]
  ring

theorem dd_kW (r : ℝ) :
    SectorDefect.dd νW (kW r) = 2 * Real.log (1 + r ^ 2) - Real.log (1 + r ^ 4) := by
  unfold SectorDefect.dd
  rw [conv_kW, hs_kW, hs_kW]
  congr 3
  ring

/-- **A stall in one sector, with no symmetry at all.** Every measure-preserving self-map of `νW` is the
identity. The kernels `kW r`, `0 ≤ r < 1`, are symmetric, strictly positive with floor `1 − r`, have the
constant as a unit top with value `1` and excited trace `r²`. Along any `t_w → 1` the defect tends to `log 2`.
So strict positivity, a simple top at every window and the absence of every symmetry exclude no bounded-
multiplicity stall. This is the shape of the `A₅` phase; it is a model, not a Wilson kernel. -/
theorem biased_stall :
    (∀ σ : Bool → Bool, (∀ f : Bool → ℝ, ∫ x, f (σ x) ∂νW = ∫ x, f x ∂νW) → σ = id) ∧
    (∀ r x y, kW r x y = kW r y x) ∧
    (∀ r : ℝ, 0 ≤ r → ∀ x y, 1 - r ≤ kW r x y) ∧
    (∀ r z, ∫ y, kW r z y * (1 : ℝ) ∂νW = 1 * 1) ∧
    (∀ r : ℝ, hs νW (KernelPower.rem (kW r) 1 fun _ => 1) = r ^ 2) ∧
    ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 1) →
      Tendsto (fun w => SectorDefect.dd νW (kW (t w))) atTop (𝓝 (Real.log 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ h
    have h1 := h fun b => if b then 1 else 0
    simp only [integral_νW] at h1
    funext b
    cases ht : σ true <;> cases hf : σ false <;> simp only [ht, hf] at h1 <;> cases b <;>
      simp_all <;> norm_num at h1
  · intro r x y
    cases x <;> cases y <;> rfl
  · intro r hr x y
    cases x <;> cases y <;> simp only [kW] <;> linarith
  · intro r z
    rw [integral_νW]
    cases z <;> simp only [kW] <;> ring
  · intro r
    unfold hs KernelPower.rem
    simp_rw [integral_νW]
    simp only [kW]
    ring
  · intro t ht
    simp_rw [dd_kW]
    have h2 : Tendsto (fun w => 2 * Real.log (1 + t w ^ 2) - Real.log (1 + t w ^ 4)) atTop
        (𝓝 (2 * Real.log (1 + 1 ^ 2) - Real.log (1 + 1 ^ 4))) := by
      refine Tendsto.sub (Tendsto.const_mul _ ?_) ?_
      · exact (Real.continuousAt_log (by norm_num)).tendsto.comp
          (tendsto_const_nhds.add (ht.pow 2))
      · exact (Real.continuousAt_log (by norm_num)).tendsto.comp
          (tendsto_const_nhds.add (ht.pow 4))
    have e : 2 * Real.log (1 + 1 ^ 2) - Real.log (1 + 1 ^ 4) = Real.log 2 := by
      norm_num
      ring
    rwa [e] at h2

end Biased

/-! ## 9. A top cluster at one coupling: a tangency at one coupling -/

section Isolated

open MassGap.DoublingRecursion MassGap.EffectiveCoupling

theorem sum_corner (k : ℕ) : ∑ i, corner k i = 4 * k := by
  simp [corner]

/-- **Two bulk phases at one coupling.** A family of corner functions with trace facts at every coupling,
continuous in the coupling, with `Δ = 15 log 2` at every corner at `β = 1` and `Δ → 0` along the corners at
every other `β`. It is `1 + r^{vol}` with `r = e^{−|β − 1|}`: two sectors touching at one coupling, with `f_∞ ≡ 0`.
So a top cluster at an isolated coupling needs no symmetry and no disconnectedness, and a rigidity argument can
exclude (T) only on open sets of couplings. A model, not a Wilson torus. -/
theorem isolated_topological :
    ∃ X : ℝ → Pt → ℝ, (∀ β, DoublingPower.FactRep (X β)) ∧ (∀ v, Continuous fun β => X β v) ∧
      (∀ k, Δ (X 1) (corner k) = 15 * Real.log 2) ∧
      ∀ β : ℝ, β ≠ 1 → Tendsto (fun k => Δ (X β) (corner k)) atTop (𝓝 0) := by
  refine ⟨fun β => twoLevel (Real.exp (-|β - 1|)), fun β => ?_, fun v => ?_, fun k => ?_,
    fun β hβ => ?_⟩
  · exact factRep_twoLevel (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by simp))
  · refine Continuous.log (by fun_prop) fun β => ?_
    have := Real.exp_pos (-|β - 1|)
    positivity
  · have e : Real.exp (-|(1 : ℝ) - 1|) = 1 := by simp
    simp only [Δ, e, twoLevel_one]
    ring
  · set r := Real.exp (-|β - 1|) with hr
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by
      rw [hr, Real.exp_lt_one_iff]
      have : 0 < |β - 1| := abs_pos.mpr (sub_ne_zero.mpr hβ)
      linarith
    have hp : Tendsto (fun k : ℕ => r ^ (2 ^ (4 * k))) atTop (𝓝 0) := by
      refine (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp ?_
      refine tendsto_atTop_mono (fun k => ?_) tendsto_id
      have : k < 2 ^ k := Nat.lt_two_pow_self
      have h2 : 2 ^ k ≤ 2 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [id]
      omega
    have hp1 : Tendsto (fun k : ℕ => r ^ (2 ^ (4 * (k + 1)))) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr hp
    have hlog : ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 0) →
        Tendsto (fun k => Real.log (1 + u k)) atTop (𝓝 0) := by
      intro u hu
      have h1 : Tendsto (fun k => 1 + u k) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hu
      have h2 := (Real.continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp h1
      rw [add_zero, Real.log_one] at h2
      exact h2
    have hmain := ((hlog hp).const_mul 16).sub (hlog hp1)
    have e : ∀ k, Δ (twoLevel r) (corner k)
        = 16 * Real.log (1 + r ^ (2 ^ (4 * k))) - Real.log (1 + r ^ (2 ^ (4 * (k + 1)))) := by
      intro k
      simp only [Δ, twoLevel, ← corner_succ, sum_corner]
    show Tendsto (fun k => Δ (twoLevel r) (corner k)) atTop (𝓝 0)
    rw [tendsto_congr e]
    have h0 : (16 : ℝ) * 0 - 0 = 0 := by norm_num
    rw [h0] at hmain
    exact hmain

end Isolated

/-! ## 10. The rotor: a scale-free flux level -/

section Rotor

open MassGap.DoublingRecursion

/-- Three electric-flux levels `k = 0, ±1` of energy `k²/(2 b L)`, the rotor of a `U(1)` slice of side `L` at
coupling `b`. A model of the flux spectrum, not the compact `U(1)` measure.

CHOSEN: the three levels `k = 0, ±1` (`3`), the lowest flux levels; keeping only them costs the higher levels,
which the model does not claim. DERIVED: `2` in `2 b L` the `k²/2` of the rotor energy. -/
def rotorSpec (b : ℝ) (L : ℕ) : Fin 3 → ℝ :=
  ![1, Real.exp (-(1 / (2 * b * L))), Real.exp (-(1 / (2 * b * L)))]

theorem rotor_pow {b : ℝ} {L : ℕ} (hb : 0 < b) (hL : 0 < L) :
    Real.exp (-(1 / (2 * b * L))) ^ L = Real.exp (-(1 / (2 * b))) := by
  rw [← Real.exp_nat_mul]
  congr 1
  have : (L : ℝ) ≠ 0 := by positivity
  field_simp

theorem rotor_top {b : ℝ} {L : ℕ} (hb : 0 < b) (hL : 0 < L) :
    Top Finset.univ (rotorSpec b L) 0 := by
  have h1 : Real.exp (-(1 / (2 * b * L))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 < 1 / (2 * b * (L : ℝ)) := by positivity
    linarith
  have h0 := Real.exp_pos (-(1 / (2 * b * L)))
  refine ⟨Finset.mem_univ _, by simp [rotorSpec], fun i _ => ?_, fun i _ => ?_⟩
  · fin_cases i
    · change (0 : ℝ) ≤ 1
      norm_num
    · exact h0.le
    · exact h0.le
  · fin_cases i
    · exact le_rfl
    · exact h1
    · exact h1

/-- **The rotor level is scale-free.** At time `L` on a slice of side `L` the level reads `e^{−1/(2b)}` and the
defect is `2 log(1 + 2q) − log(1 + 2q²)`, at every `L`. It lands in (M) at every `b`: `0 < q < 1`, `q` free of
`L`. And `q → 1` as `b → ∞`: the top cluster is the strong end of a line of scale levels. -/
theorem rotor_read {b : ℝ} {L : ℕ} (hb : 0 < b) (hL : 0 < L) :
    (rotorSpec b L 1 / rotorSpec b L 0) ^ L = Real.exp (-(1 / (2 * b))) ∧
      0 < Real.exp (-(1 / (2 * b))) ∧ Real.exp (-(1 / (2 * b))) < 1 ∧
      defect Finset.univ (rotorSpec b L) L
        = 2 * Real.log (1 + 2 * Real.exp (-(1 / (2 * b))))
          - Real.log (1 + 2 * Real.exp (-(1 / (2 * b))) ^ 2) := by
  have hq := rotor_pow hb hL
  refine ⟨by simpa [rotorSpec] using hq, Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    have : 0 < 1 / (2 * b) := by positivity
    linarith
  · unfold defect powSum
    simp only [Fin.sum_univ_three, rotorSpec, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, one_pow]
    have e2 : Real.exp (-(1 / (2 * b * L))) ^ (2 * L) = Real.exp (-(1 / (2 * b))) ^ 2 := by
      rw [mul_comm 2 L, pow_mul, hq]
    rw [hq, e2]
    congr 2 <;> ring_nf

end Rotor

/-! ## 11. β-rigidity and the Ward statement -/

section Rigidity

open MassGap.EffectiveCoupling MassGap.ZoomSelfScale

variable {N : ℕ}

/-- The cut energy at side `n`: the β-derivative of the defect.

DERIVED: `16 = 2⁴` the copies of the side-`n` torus in the side-`2n` torus; `2` the doubling. -/
def cutE (N n : ℕ) (β : ℝ) : ℝ :=
  meanAction N (fun _ => 2 * n) β - 16 * meanAction N (fun _ => n) β

/-- **The mean value form of the rigidity.** The change of the defect between two couplings is the cut energy
at an intermediate coupling. -/
theorem exists_cut (hN : N ≠ 0) (n : ℕ) {β₁ β₂ : ℝ} (h : β₁ < β₂) :
    ∃ η ∈ Set.Ioo β₁ β₂, defectW N β₂ n - defectW N β₁ n = (β₂ - β₁) * cutE N n η := by
  have hd := fun x => hasDerivAt_defectW hN n x
  have hc : ContinuousOn (fun x => defectW N x n) (Set.Icc β₁ β₂) :=
    fun x _ => (hd x).continuousAt.continuousWithinAt
  obtain ⟨η, hη, he⟩ := exists_hasDerivAt_eq_slope (fun x => defectW N x n) (fun x => cutE N n x) h hc
    (fun x _ => hd x)
  refine ⟨η, hη, ?_⟩
  have hne : β₂ - β₁ ≠ 0 := (sub_pos.mpr h).ne'
  rw [he]
  field_simp

/-- **The limit of the cut energy.** If the window defects converge at two couplings `β₁ < β₂`, some `η_w ∈ (β₁, β₂)`
have cut energy tending to the slope of the limit. Equal limits (a top cluster on an interval, or an attractive
scale-invariant limit) give a vanishing cut; unequal limits (a line of fixed points) keep an `L⁻⁴` term in the mean
action, with a coupling-dependent coefficient. -/
theorem cut_limit (hN : N ≠ 0) {β₁ β₂ L₁ L₂ : ℝ} (h : β₁ < β₂)
    (h1 : Tendsto (CouplingTower.windowCoupling N β₁) atTop (𝓝 L₁))
    (h2 : Tendsto (CouplingTower.windowCoupling N β₂) atTop (𝓝 L₂)) :
    ∃ η : ℕ → ℝ, (∀ w, η w ∈ Set.Ioo β₁ β₂) ∧
      Tendsto (fun w => cutE N (2 ^ w) (η w)) atTop (𝓝 ((L₂ - L₁) / (β₂ - β₁))) := by
  choose η hη he using fun w => exists_cut hN (2 ^ w) h
  refine ⟨η, hη, ?_⟩
  have hne : β₂ - β₁ ≠ 0 := (sub_pos.mpr h).ne'
  have e : (fun w => cutE N (2 ^ w) (η w))
      = fun w => (CouplingTower.windowCoupling N β₂ w - CouplingTower.windowCoupling N β₁ w)
        / (β₂ - β₁) := by
    funext w
    have := he w
    unfold CouplingTower.windowCoupling
    rw [this]
    field_simp
  rw [e]
  exact (h2.sub h1).div_const _

/-- **No conserved plaquette charge at `SU(N)`, and one at `U(1)`.** The lattice absence of the current whose
breaking is a photon: `CoverCompact.conserved_iff_affine` at a perfect group, against the identity of the
circle. -/
theorem no_plaquette_charge {d L : ℕ} (hL : 2 ≤ L) {i j k : Fin d} (hij : i ≠ j) (hjk : j ≠ k)
    (hki : k ≠ i) (x : TorusDoubling.TSite d L) :
    (∀ {N : ℕ} [NeZero N] {A : Type} [AddCommGroup A] (Q : MassGap.SUN.SU N → A),
      (∀ U : TorusDoubling.TLink d L → MassGap.SUN.SU N,
        CoverCompact.cubeSum (fun q => Q (HolderBondMoving.thol q U)) i j k x = 0) →
      ∀ g, Q g = Q 1) ∧
    (∀ U : TorusDoubling.TLink d L → Circle,
      CoverCompact.cubeSum (fun q => Additive.ofMul (HolderBondMoving.thol q U)) i j k x = 0) := by
  refine ⟨fun Q h g => CoverCompact.conserved_const_of_perfect Q hL hij hjk hki x h g, ?_⟩
  refine (CoverCompact.conserved_iff_affine (fun g : Circle => Additive.ofMul g) hL hij hjk hki x).mpr ?_
  intro g h
  simp [ofMul_mul]

end Rigidity

/-! ## 12. The tests on the groups -/

section Tests

open MassGap.GaugeGroup

instance instMeasurableCircle : MeasurableSpace Circle := borel Circle

instance instBorelCircle : BorelSpace Circle := ⟨rfl⟩

instance instSecondCountableCircle : SecondCountableTopology Circle :=
  inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))

/-- The circle as a unitary `1 × 1` representation. -/
def circleRep : Circle →* Matrix.unitaryGroup (Fin 1) ℂ where
  toFun z := ⟨Matrix.scalar (Fin 1) (z : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Matrix.scalar_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp

/-- **`U(1)` is a lattice gauge group of the tree.** So every theorem of §6 reads the compact `U(1)` Wilson
measure itself.

DERIVED: `1` the dimension of the representation `circleRep`; `6` the section number of "The fork on the Wilson
torus of a compact group". -/
instance instGaugeGroupCircle : GaugeGroup Circle where
  isTopologicalGroup := inferInstance
  compactSpace := inferInstance
  borelSpace := inferInstance
  secondCountable := inferInstance
  nonempty := inferInstance
  repDim := 1
  repDim_pos := by norm_num
  rep := circleRep
  continuous_rep := by
    refine continuous_matrix fun i j => ?_
    fin_cases i
    fin_cases j
    have hc : Continuous fun z : Circle => (z : ℂ) :=
      (continuous_subtype_val : Continuous fun z : Metric.sphere (0 : ℂ) 1 => (z : ℂ))
    simpa [circleRep, Matrix.scalar_apply] using hc
  rep_injective := by
    intro a b h
    have h1 : (Matrix.scalar (Fin 1) (a : ℂ)) = Matrix.scalar (Fin 1) (b : ℂ) :=
      congrArg Subtype.val h
    have h2 := congrFun (congrFun h1 0) 0
    simp at h2
    exact h2

/-- **The exact statements at `U(1)`, `A₅`, `G₂`.** The fork and the vanishing criterion hold at every compact
group, by one proof. So neither excludes anything by itself; the groups differ in which alternative is met. -/
theorem read_tests {β : ℝ} (hβ : 0 ≤ β) :
    (Tendsto (Dw Circle β) atTop (𝓝 0) ↔
      (∃ A : ℝ, ∀ᶠ w in atTop, Dw Circle β w ≤ A) ∧ Tendsto (Yw Circle hβ) atTop (𝓝 0)) ∧
    (Tendsto (Dw CoverCompact.A5 β) atTop (𝓝 0) ↔
      (∃ A : ℝ, ∀ᶠ w in atTop, Dw CoverCompact.A5 β w ≤ A) ∧
        Tendsto (Yw CoverCompact.A5 hβ) atTop (𝓝 0)) ∧
    (Tendsto (Dw GaugeG2.G2 β) atTop (𝓝 0) ↔
      (∃ A : ℝ, ∀ᶠ w in atTop, Dw GaugeG2.G2 β w ≤ A) ∧ Tendsto (Yw GaugeG2.G2 hβ) atTop (𝓝 0)) :=
  ⟨vanishes_iff_read hβ, vanishes_iff_read hβ, vanishes_iff_read hβ⟩

end Tests

end MassGap.StallRigid

#print axioms MassGap.StallRigid.defect_le_two_log
#print axioms MassGap.StallRigid.excited_ge
#print axioms MassGap.StallRigid.excited_eq_sum
#print axioms MassGap.StallRigid.excited_double_le
#print axioms MassGap.StallRigid.ratio_pow_le_one
#print axioms MassGap.StallRigid.one_add_excited_le
#print axioms MassGap.StallRigid.defect_double_le_level
#print axioms MassGap.StallRigid.defect_double_le_two
#print axioms MassGap.StallRigid.level_count
#print axioms MassGap.StallRigid.exists_level
#print axioms MassGap.StallRigid.defect_const
#print axioms MassGap.StallRigid.uP_self
#print axioms MassGap.StallRigid.p_eq
#print axioms MassGap.StallRigid.pred_le
#print axioms MassGap.StallRigid.exists_step
#print axioms MassGap.StallRigid.Δ_corner_nonneg
#print axioms MassGap.StallRigid.defect_double_of_facts
#print axioms MassGap.StallRigid.IsTop.rho_nonneg
#print axioms MassGap.StallRigid.IsTop.powerFacts
#print axioms MassGap.StallRigid.IsTop.excited_double_le
#print axioms MassGap.StallRigid.IsTop.level_step
#print axioms MassGap.StallRigid.schur_sq
#print axioms MassGap.StallRigid.schur_gap
#print axioms MassGap.StallRigid.IsTop.ratio_le_excited
#print axioms MassGap.StallRigid.exists_topG
#print axioms MassGap.StallRigid.exists_ratio
#print axioms MassGap.StallRigid.topRatio_spec
#print axioms MassGap.StallRigid.winRead_nonneg
#print axioms MassGap.StallRigid.winRead_le_Yw
#print axioms MassGap.StallRigid.Yw_nonneg
#print axioms MassGap.StallRigid.Yw_lt_one
#print axioms MassGap.StallRigid.fork_step
#print axioms MassGap.StallRigid.Dw_corner0
#print axioms MassGap.StallRigid.Dw_corner1
#print axioms MassGap.StallRigid.window_data
#print axioms MassGap.StallRigid.Dw_nonneg
#print axioms MassGap.StallRigid.fork_quant
#print axioms MassGap.StallRigid.winRead_le
#print axioms MassGap.StallRigid.Yw_le
#print axioms MassGap.StallRigid.level_floor
#print axioms MassGap.StallRigid.stall_dichotomy
#print axioms MassGap.StallRigid.vanishes_of_read
#print axioms MassGap.StallRigid.read_of_vanishes
#print axioms MassGap.StallRigid.vanishes_iff_read
#print axioms MassGap.StallRigid.massive_stall_grows
#print axioms MassGap.StallRigid.Dw_SU
#print axioms MassGap.StallRigid.vanishes_iff_read_SU
#print axioms MassGap.StallRigid.strongEnd_iff_read
#print axioms MassGap.StallRigid.fork_SU
#print axioms MassGap.StallRigid.exists_gap_kT
#print axioms MassGap.StallRigid.top_centre_neutral
#print axioms MassGap.StallRigid.large_stall_zero_flux
#print axioms MassGap.StallRigid.Yw_zero_coupling
#print axioms MassGap.StallRigid.integral_νW
#print axioms MassGap.StallRigid.conv_kW
#print axioms MassGap.StallRigid.iter_kW
#print axioms MassGap.StallRigid.hs_kW
#print axioms MassGap.StallRigid.dd_kW
#print axioms MassGap.StallRigid.biased_stall
#print axioms MassGap.StallRigid.sum_corner
#print axioms MassGap.StallRigid.isolated_topological
#print axioms MassGap.StallRigid.rotor_pow
#print axioms MassGap.StallRigid.rotor_top
#print axioms MassGap.StallRigid.rotor_read
#print axioms MassGap.StallRigid.exists_cut
#print axioms MassGap.StallRigid.cut_limit
#print axioms MassGap.StallRigid.no_plaquette_charge
#print axioms MassGap.StallRigid.read_tests
