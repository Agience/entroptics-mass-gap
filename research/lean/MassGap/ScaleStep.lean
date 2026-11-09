import Mathlib
import MassGap.ObserverGapSplit
import MassGap.ChessboardRead
import MassGap.ClayRoutes
import MassGap.ZoomStep

noncomputable section

/-!
# MassGap.ScaleStep — "zoom only coarsens" as a theorem, its direction, and the UV step on the view

The UV step of the finite-box route is `UVIRSplit.LossStep` (clipped: `LossStepBelow`, consumed by
`RestoreShimsClay.UVBelowIR`): under one dyadic refinement, the attenuation `GapAt` at physical rate `M`
survives at rate `M − ε(a)`. The thesis "zoom only coarsens" reads it as a monotonicity of the
attenuation under refinement beneath an observer of fixed physical resolution. This module proves the
thesis in the direction it holds, shows that direction is the converse of what the induction needs,
and moves the UV step from the whole lattice-scale class onto the observer's view.

## What it gives

1. **Rates carry no constants.** `sqProfile D x n = ⟨Tⁿx, Tⁿx⟩` is log-convex for every transfer
   (`sqProfile_log_convex`: symmetry and Cauchy–Schwarz, no positivity of `T`). So a per-vector bound
   `⟨Tⁿx, Tⁿx⟩ ≤ K r²ⁿ` with ANY constant `K` gives the one-step contraction
   `⟨Tx, Tx⟩ ≤ r² ⟨x, x⟩` of that vector (`step_le_of_rate`), with no orthogonality to the vacuum
   asked. `RateVec D r x` is that per-vector bound; the rate vectors form a submodule
   (`rateSubmodule`): constants add. A comparison of correlation functions that costs a factor
   `K e^{δ n}` therefore costs exactly the rate `δ` and nothing for `K`.
2. **The view decides the gap when it is dense.** `ViewDense D S`: every vacuum-orthogonal vector is
   a form-limit of finite combinations of `S`. `ViewRate D S r`: every element of `S` is a rate
   vector. `gapAt_of_viewRate_dense`: density and the view's rate give `GapAt D r`.
   `gapAt_iff_viewRate_of_dense`: with `S` vacuum-orthogonal and dense, `GapAt D r` holds exactly when
   the view's per-vector rates do, each vector with its own constant.
3. **The aperture changes weights, never rates.** `rateVec_map`: a form-bounded map commuting with
   `T` (a smoothing commutes with time translation) sends rate vectors to rate vectors.
   `gapAt_iff_smoothed`: if it keeps the vacuum complement and has dense range there, `GapAt D r` is
   the rate of the smoothed vectors. Smoothing reweights the spectral measure of each vector and
   cannot move its top: a view hides a slow mode only through a dark fringe (non-dense range).
4. **"Zoom only coarsens", proved, in its true direction.** `gapAt_coarse_of_compression`: a coarse
   transfer `D_c` whose correlation functions are dominated, up to a constant per vector, by the fine
   transfer's at doubled lag through a form-isometric block map `B` with `B Ω_c = Ω_f` (the exact
   blocked theory is the case of equality) inherits the fine gap at the same physical rate:
   `GapAt D_f r → GapAt D_c r²`, i.e. `GapAt D_f e^{−M a/2} → GapAt D_c e^{−M a}`
   (`gapAt_coarse_of_compression_phys`). A coarse observer cannot read a slower mode than the fine
   theory has. That is the data-processing direction, and it is the converse of the UV step.
5. **The converse needs density, and nothing in the structure supplies it.**
   `viewRate_without_density_no_gap`: a positive transfer, a vacuum-orthogonal view with rate `1/2`,
   and no gap at any rate below one (from `ObserverGapSplit.coarse_gap_does_not_lift`). The escape of
   this no-go is the density hypothesis of item 2.
6. **The UV step on the view.** `ViewLossStep D S a βUV ε` (clipped: `ViewLossStepBelow … M₀`): for
   two couplings one block step apart, the view's per-vector rate at physical rate `M` at `β` gives
   the view's per-vector rate at `M − ε(a β)` at `β'`, constants free.
   `lossStep_of_viewLossStep`, `viewLossStep_of_lossStep`, `lossStep_iff_viewLossStep` (and the
   clipped forms): under density and vacuum-orthogonality of the view at every coupling from `βUV`,
   the view step IS `UVIRSplit.LossStep`. `uvBelowIR_of_view`, `clay_continuum_of_boxPatchGap_view`:
   the Clay capstone of the finite-box route with its UV input on the view.

## What is open, and where the gap sits

The view step is equivalent to `LossStep` under density; it is a restatement on a smaller class, not
a discharge. What it changes: the lattice-scale class enters only through `ViewDense`, which carries
no rate, and the rate is asked only of the observer's vectors with constants free, so a comparison of
the view's correlation functions at two spacings that is multiplicative (constant times `e^{δ t}`)
carries the step with loss `δ`, while an additive one (total variation, `χ²`) carries no rate at all.
The gap is carried by the base (`IRGapAt` at one coupling): the free field, massive or massless, meets
the view step with zero loss (its view rate `(2/a) asinh(ma/2)` rises to `m` under refinement), and
only the base separates them.

## Scope

`ViewDense`, `ViewRate`, `ViewLossStep` and the compression hypotheses are hypotheses of every theorem
that takes them. Density of the observer's view on the Wilson half-space algebra is not proved here.
The block factor is `2`, as in `UVIRSplit`.

DERIVED (module-wide): `2` is the form's degree in `r²`, the doubling `2n` of a separation and the
block factor of `UVIRSplit.LossStep`; `0` is the sign of rates and constants and the vacuum pairing;
`1` is the one-step index; `3` in `Fin 3` is the dimension of `ObserverGapSplit`'s witness and `1/2`
its coarse rate; `4` in `Fin 4` is the spacetime dimension.
-/

namespace MassGap.ScaleStep

open MassGap

section Abstract

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-! ## 1. Rates carry no constants -/

/-- **The squared-norm profile** `n ↦ ⟨Tⁿx, Tⁿx⟩`, the reflected pairing of `x` with itself at
separation `2n` (`TransferGap.form_pow_diag`).

DERIVED: no numeral. -/
def sqProfile (D : Transfer.TransferData A) (x : A) (n : ℕ) : ℝ :=
  D.form ((D.T ^ n) x) ((D.T ^ n) x)

/-- DERIVED: `0` is the sign. -/
theorem sqProfile_nonneg (D : Transfer.TransferData A) (x : A) (n : ℕ) : 0 ≤ sqProfile D x n :=
  D.form_nonneg _

#print axioms sqProfile_nonneg

/-- **The squared-norm profile is log-convex**, for every transfer: `⟨Tⁿ⁺¹x, Tⁿ⁺¹x⟩ = ⟨Tⁿx, Tⁿ⁺²x⟩`
by symmetry, and Cauchy–Schwarz of the reflection form bounds its square. No positivity of `T`.

DERIVED: `1` and `2` are the one- and two-step shifts; `2` is also the square of Cauchy–Schwarz. -/
theorem sqProfile_log_convex (D : Transfer.TransferData A) (x : A) (n : ℕ) :
    sqProfile D x (n + 1) ^ 2 ≤ sqProfile D x n * sqProfile D x (n + 2) := by
  have h1 : sqProfile D x (n + 1) = D.form ((D.T ^ n) x) ((D.T ^ (n + 2)) x) := by
    unfold sqProfile
    have e1 : (D.T ^ (n + 1)) x = D.T ((D.T ^ n) x) := by rw [pow_succ', Module.End.mul_apply]
    have e2 : (D.T ^ (n + 2)) x = D.T ((D.T ^ (n + 1)) x) := by
      rw [show n + 2 = (n + 1) + 1 by ring, pow_succ', Module.End.mul_apply]
    rw [e2, e1, D.T_symm]
  rw [h1]
  exact Transfer.ReflForm.cauchy_schwarz D.toReflForm _ _

#print axioms sqProfile_log_convex

/-- **A sequence dominated by a geometric one with any constant is dominated term by term.** From
`uᵐ ≤ C vᵐ` at every `m`, with `0 ≤ u` and `0 ≤ v`: `u ≤ v`. If `u > v > 0`, `(u/v)ᵐ` passes `C`.

DERIVED: `0` is the sign; `1` is the exponent read at `v = 0` and the threshold of `u/v`. -/
theorem le_of_pow_le_mul_pow {u v C : ℝ} (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : ∀ m : ℕ, u ^ m ≤ C * v ^ m) : u ≤ v := by
  by_contra hnot
  have hlt : v < u := lt_of_not_ge hnot
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · have h1 := h 1
    rw [← hv0] at h1
    simp at h1
    linarith
  · have ht : 1 < u / v := by rw [one_lt_div hvpos]; exact hlt
    have hten := tendsto_pow_atTop_atTop_of_one_lt ht
    obtain ⟨m, hm⟩ := (hten.eventually (Filter.eventually_gt_atTop C)).exists
    have hm' := h m
    have hvm : 0 < v ^ m := pow_pos hvpos m
    have hq : (u / v) ^ m * v ^ m = u ^ m := by
      rw [div_pow, div_mul_cancel₀]
      exact hvm.ne'
    linarith [mul_lt_mul_of_pos_right hm hvm]

#print axioms le_of_pow_le_mul_pow

/-- **A per-vector rate with any constant gives the one-step contraction of that vector.** If
`⟨Tⁿx, Tⁿx⟩ ≤ K r²ⁿ` at every `n`, then `⟨Tx, Tx⟩ ≤ r² ⟨x, x⟩`. Log-convexity gives
`b₁ᵐ b₀ ≤ b₀ᵐ bₘ ≤ b₀ᵐ K r²ᵐ` (`ChessboardRead.pow_mul_le_of_log_convex`), and the constant drops out
in the limit (`le_of_pow_le_mul_pow`). At `⟨x, x⟩ = 0` the contraction field closes it. No
orthogonality to the vacuum is asked: at `r < 1` the bound itself excludes a vacuum component.

DERIVED: `0` is the sign of `r`; `2` is the form's degree and the doubled separation; `1` is the
one-step index. -/
theorem step_le_of_rate (D : Transfer.TransferData A) {r K : ℝ} (_hr : 0 ≤ r) {x : A}
    (hK : ∀ n : ℕ, sqProfile D x n ≤ K * r ^ (2 * n)) :
    D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x := by
  have hb0 : sqProfile D x 0 = D.form x x := by simp [sqProfile]
  have hb1 : sqProfile D x 1 = D.form (D.T x) (D.T x) := by simp [sqProfile]
  rcases eq_or_lt_of_le (D.form_nonneg x) with h0 | hpos
  · have hle : D.form (D.T x) (D.T x) ≤ D.form x x := D.T_contract x
    rw [← h0] at hle ⊢
    simpa using hle
  · have hlc := ChessboardRead.pow_mul_le_of_log_convex (b := sqProfile D x)
      (fun n => sqProfile_nonneg D x n) (fun n => sqProfile_log_convex D x n)
    have key : ∀ m : ℕ, D.form (D.T x) (D.T x) ^ m
        ≤ (K / D.form x x) * (r ^ 2 * D.form x x) ^ m := by
      intro m
      have h1 := hlc m
      rw [hb0, hb1] at h1
      have hpm : 0 ≤ D.form x x ^ m := pow_nonneg hpos.le m
      have h3 : D.form (D.T x) (D.T x) ^ m * D.form x x ≤ D.form x x ^ m * (K * r ^ (2 * m)) :=
        le_trans h1 (mul_le_mul_of_nonneg_left (hK m) hpm)
      have hrw : (K / D.form x x) * (r ^ 2 * D.form x x) ^ m
          = (D.form x x ^ m * (K * r ^ (2 * m))) / D.form x x := by
        rw [mul_pow, ← pow_mul]
        ring
      rw [hrw, le_div_iff₀ hpos]
      exact h3
    exact le_of_pow_le_mul_pow (D.form_nonneg _) (by positivity) key

#print axioms step_le_of_rate

/-- **A rate vector**: `⟨Tⁿx, Tⁿx⟩ ≤ K r²ⁿ` at every `n`, for some constant `K` chosen after `x`.

DERIVED: `2` is the form's degree. -/
def RateVec (D : Transfer.TransferData A) (r : ℝ) (x : A) : Prop :=
  ∃ K : ℝ, ∀ n : ℕ, sqProfile D x n ≤ K * r ^ (2 * n)

/-- `step_le_of_rate` on a rate vector.

DERIVED: `0` is the sign of `r`; `2` is the form's degree. -/
theorem step_le_of_rateVec (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) {x : A}
    (h : RateVec D r x) : D.form (D.T x) (D.T x) ≤ r ^ 2 * D.form x x := by
  obtain ⟨K, hK⟩ := h
  exact step_le_of_rate D hr hK

#print axioms step_le_of_rateVec

/-- `⟨u + v, u + v⟩ ≤ 2⟨u, u⟩ + 2⟨v, v⟩`: the quadratic of `PreForm.form_quad` at `t = −1` is
non-negative.

DERIVED: `2` is the parallelogram's factor; `−1` is the reflected sign. -/
theorem form_add_le (D : Transfer.TransferData A) (u v : A) :
    D.form (u + v) (u + v) ≤ 2 * D.form u u + 2 * D.form v v := by
  have h1 := Transfer.PreForm.form_add_self D.toReflForm.toPreForm u v
  have h2 := Transfer.PreForm.form_quad D.toReflForm.toPreForm u v (-1)
  have h3 := D.form_nonneg ((-1 : ℝ) • u + v)
  have e1 : D.form (u + v) (u + v) = D.toReflForm.toPreForm.form (u + v) (u + v) := rfl
  have e2 : D.form ((-1 : ℝ) • u + v) ((-1 : ℝ) • u + v)
      = D.toReflForm.toPreForm.form ((-1 : ℝ) • u + v) ((-1 : ℝ) • u + v) := rfl
  have e3 : D.form u u = D.toReflForm.toPreForm.form u u := rfl
  have e4 : D.form v v = D.toReflForm.toPreForm.form v v := rfl
  rw [e1, e3, e4]
  rw [e2] at h3
  rw [h2] at h3
  rw [h1]
  nlinarith [h3]

#print axioms form_add_le

/-- `⟨c u, c u⟩ = c² ⟨u, u⟩`.

DERIVED: `2` is the form's degree. -/
theorem form_smul_smul (D : Transfer.TransferData A) (c : ℝ) (u : A) :
    D.form (c • u) (c • u) = c ^ 2 * D.form u u := by
  have h1 := D.form_smul_left c u (c • u)
  have h2 := Transfer.PreForm.form_smul_right D.toReflForm.toPreForm c u u
  have e : D.form u (c • u) = D.toReflForm.toPreForm.form u (c • u) := rfl
  rw [h1, e, h2]
  show c * (c * D.form u u) = c ^ 2 * D.form u u
  ring

#print axioms form_smul_smul

/-- **The rate vectors form a submodule**: constants add (`form_add_le`) and scale
(`form_smul_smul`).

DERIVED: `0` is the zero vector's constant; `2` is the parallelogram's factor and the form's
degree. -/
def rateSubmodule (D : Transfer.TransferData A) (r : ℝ) : Submodule ℝ A where
  carrier := {x | RateVec D r x}
  zero_mem' := by
    refine ⟨0, fun n => ?_⟩
    simp only [sqProfile, map_zero, zero_mul]
    exact le_of_eq (Transfer.PreForm.form_zero_left D.toReflForm.toPreForm 0)
  add_mem' := by
    rintro x y ⟨Kx, hx⟩ ⟨Ky, hy⟩
    refine ⟨2 * Kx + 2 * Ky, fun n => ?_⟩
    have h := form_add_le D ((D.T ^ n) x) ((D.T ^ n) y)
    have hxn := hx n
    have hyn := hy n
    simp only [sqProfile, map_add] at h hxn hyn ⊢
    nlinarith [h, hxn, hyn]
  smul_mem' := by
    rintro c x ⟨K, hx⟩
    refine ⟨c ^ 2 * K, fun n => ?_⟩
    have hxn := hx n
    simp only [sqProfile, map_smul] at hxn ⊢
    rw [form_smul_smul]
    have hc : 0 ≤ c ^ 2 := sq_nonneg c
    calc c ^ 2 * D.form ((D.T ^ n) x) ((D.T ^ n) x) ≤ c ^ 2 * (K * r ^ (2 * n)) :=
          mul_le_mul_of_nonneg_left hxn hc
      _ = c ^ 2 * K * r ^ (2 * n) := by ring

/-! ## 2. The view decides the gap when it is dense -/

/-- `⟨−z, −z⟩ = ⟨z, z⟩` in the form `⟨y − x, y − x⟩ = ⟨x − y, x − y⟩`.

DERIVED: `−1` is the sign of the reflection `y − x = −(x − y)`; `2` is the form's degree. -/
theorem form_sub_comm (D : Transfer.TransferData A) (x y : A) :
    D.form (y - x) (y - x) = D.form (x - y) (x - y) := by
  have e : y - x = (-1 : ℝ) • (x - y) := by rw [neg_one_smul, neg_sub]
  rw [e, form_smul_smul]
  ring

#print axioms form_sub_comm

/-- **The form seminorm is subadditive**: `√⟨u+v, u+v⟩ ≤ √⟨u, u⟩ + √⟨v, v⟩` (Cauchy–Schwarz).

DERIVED: `2` is the square and the cross-term count. -/
theorem sqrt_form_add_le (D : Transfer.TransferData A) (u v : A) :
    Real.sqrt (D.form (u + v) (u + v)) ≤ Real.sqrt (D.form u u) + Real.sqrt (D.form v v) := by
  have hu := D.form_nonneg u
  have hv := D.form_nonneg v
  have hcs := Transfer.ReflForm.cauchy_schwarz D.toReflForm u v
  have hsu := Real.sq_sqrt hu
  have hsv := Real.sq_sqrt hv
  have hnu := Real.sqrt_nonneg (D.form u u)
  have hnv := Real.sqrt_nonneg (D.form v v)
  have hsq : D.form u v ^ 2 ≤ (Real.sqrt (D.form u u) * Real.sqrt (D.form v v)) ^ 2 := by
    rw [mul_pow, hsu, hsv]
    exact hcs
  have hcross : D.form u v ≤ Real.sqrt (D.form u u) * Real.sqrt (D.form v v) := by
    nlinarith [hsq, mul_nonneg hnu hnv]
  have hexp := Transfer.PreForm.form_add_self D.toReflForm.toPreForm u v
  have e1 : D.form (u + v) (u + v) = D.toReflForm.toPreForm.form (u + v) (u + v) := rfl
  have e2 : D.form u v = D.toReflForm.toPreForm.form u v := rfl
  have e3 : D.form u u = D.toReflForm.toPreForm.form u u := rfl
  have e4 : D.form v v = D.toReflForm.toPreForm.form v v := rfl
  have hle : D.form (u + v) (u + v) ≤ (Real.sqrt (D.form u u) + Real.sqrt (D.form v v)) ^ 2 := by
    rw [e1, hexp, ← e2, ← e3, ← e4]
    nlinarith [hcross, hsu, hsv]
  calc Real.sqrt (D.form (u + v) (u + v))
      ≤ Real.sqrt ((Real.sqrt (D.form u u) + Real.sqrt (D.form v v)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (D.form u u) + Real.sqrt (D.form v v) := Real.sqrt_sq (add_nonneg hnu hnv)

#print axioms sqrt_form_add_le

/-- **A dense view**: every vacuum-orthogonal vector is, within any `ε > 0` in the form, a finite
combination of the view's vectors.

DERIVED: `0` is the vacuum pairing and the sign of `ε`. -/
def ViewDense (D : Transfer.TransferData A) (S : Set A) : Prop :=
  ∀ x : A, D.form x D.vac = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ y ∈ Submodule.span ℝ S, D.form (x - y) (x - y) ≤ ε

/-- **The view's rate**: every vector of the view is a rate vector at `r`, each with its own
constant.

DERIVED: no numeral. -/
def ViewRate (D : Transfer.TransferData A) (S : Set A) (r : ℝ) : Prop :=
  ∀ s ∈ S, RateVec D r s

/-- **A dense view with a rate gives the gap.** The span of the view consists of rate vectors
(`rateSubmodule`), each contracted by `r` in one step (`step_le_of_rateVec`); the contraction passes
to form-limits through the seminorm (`sqrt_form_add_le`, `T_contract`).

DERIVED: `0` is the sign of `r` and the vacuum pairing; `1` in `1 + r` is the coefficient of the
approximation error; `2` is the form's degree. -/
theorem gapAt_of_viewRate_dense (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) {S : Set A}
    (hrate : ViewRate D S r) (hdense : ViewDense D S) : TransferGap.GapAt D r := by
  intro x hx
  have hspan : ∀ y ∈ Submodule.span ℝ S, RateVec D r y := by
    intro y hy
    have hle : Submodule.span ℝ S ≤ rateSubmodule D r :=
      Submodule.span_le.mpr (fun s hs => hrate s hs)
    exact hle hy
  have hmain : Real.sqrt (D.form (D.T x) (D.T x)) ≤ r * Real.sqrt (D.form x x) := by
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have hδ : 0 < η / (1 + r) := div_pos hη h1r
    obtain ⟨y, hy, hxy⟩ := hdense x hx ((η / (1 + r)) ^ 2) (by positivity)
    have hNxy : Real.sqrt (D.form (x - y) (x - y)) ≤ η / (1 + r) := by
      calc Real.sqrt (D.form (x - y) (x - y)) ≤ Real.sqrt ((η / (1 + r)) ^ 2) :=
            Real.sqrt_le_sqrt hxy
        _ = η / (1 + r) := Real.sqrt_sq hδ.le
    have hTy : Real.sqrt (D.form (D.T y) (D.T y)) ≤ r * Real.sqrt (D.form y y) := by
      have h := step_le_of_rateVec D hr (hspan y hy)
      calc Real.sqrt (D.form (D.T y) (D.T y)) ≤ Real.sqrt (r ^ 2 * D.form y y) :=
            Real.sqrt_le_sqrt h
        _ = r * Real.sqrt (D.form y y) := by
            rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
    have hsplitT : D.T x = D.T y + D.T (x - y) := by rw [map_sub]; abel
    have h1 : Real.sqrt (D.form (D.T x) (D.T x)) ≤ Real.sqrt (D.form (D.T y) (D.T y))
        + Real.sqrt (D.form (D.T (x - y)) (D.T (x - y))) := by
      rw [hsplitT]
      exact sqrt_form_add_le D _ _
    have h2 : Real.sqrt (D.form (D.T (x - y)) (D.T (x - y)))
        ≤ Real.sqrt (D.form (x - y) (x - y)) := Real.sqrt_le_sqrt (D.T_contract _)
    have hysplit : x + (y - x) = y := by abel
    have h3 : Real.sqrt (D.form y y)
        ≤ Real.sqrt (D.form x x) + Real.sqrt (D.form (x - y) (x - y)) := by
      have h := sqrt_form_add_le D x (y - x)
      rw [hysplit, form_sub_comm D x y] at h
      exact h
    have hδeq : r * (η / (1 + r)) + η / (1 + r) = η := by
      field_simp
      ring
    have hm3 := mul_le_mul_of_nonneg_left h3 hr
    have hm4 := mul_le_mul_of_nonneg_left hNxy hr
    nlinarith [h1, h2, hTy, hNxy, hm3, hm4, hδeq]
  have hNT := Real.sqrt_nonneg (D.form (D.T x) (D.T x))
  have hsq := pow_le_pow_left₀ hNT hmain 2
  rw [Real.sq_sqrt (D.form_nonneg _), mul_pow, Real.sq_sqrt (D.form_nonneg _)] at hsq
  exact hsq

#print axioms gapAt_of_viewRate_dense

/-- **The gap gives the view's rate**, at constant `⟨s, s⟩` (`TransferGap.gap_pow`), for any
vacuum-orthogonal view.

DERIVED: `0` is the sign of `r` and the vacuum pairing. -/
theorem viewRate_of_gapAt (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r) {S : Set A}
    (horth : ∀ s ∈ S, D.form s D.vac = 0) (hg : TransferGap.GapAt D r) : ViewRate D S r := by
  intro s hs
  refine ⟨D.form s s, fun n => ?_⟩
  have h := TransferGap.gap_pow D hr hg n s (horth s hs)
  unfold sqProfile
  rw [mul_comm]
  exact h

#print axioms viewRate_of_gapAt

/-- **Under density the gap is the view's rate**, with constants free.

DERIVED: `0` is the sign of `r` and the vacuum pairing. -/
theorem gapAt_iff_viewRate_of_dense (D : Transfer.TransferData A) {r : ℝ} (hr : 0 ≤ r)
    {S : Set A} (horth : ∀ s ∈ S, D.form s D.vac = 0) (hdense : ViewDense D S) :
    TransferGap.GapAt D r ↔ ViewRate D S r :=
  ⟨viewRate_of_gapAt D hr horth, fun h => gapAt_of_viewRate_dense D hr h hdense⟩

#print axioms gapAt_iff_viewRate_of_dense

/-! ## 3. The aperture changes weights, never rates -/

/-- A map commuting with `T` commutes with every power of `T`.

DERIVED: no numeral. -/
theorem pow_comm_of_comm (D : Transfer.TransferData A) (O : A →ₗ[ℝ] A)
    (hcomm : ∀ x, O (D.T x) = D.T (O x)) : ∀ (n : ℕ) (x : A), O ((D.T ^ n) x) = (D.T ^ n) (O x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hcomm, ih]

#print axioms pow_comm_of_comm

/-- **Smoothing keeps every rate.** A map `O` commuting with `T` and bounded in the form,
`⟨Ox, Ox⟩ ≤ c ⟨x, x⟩`, sends rate vectors to rate vectors at the same rate.

DERIVED: `0` is the floor taken on `c`. -/
theorem rateVec_map (D : Transfer.TransferData A) (O : A →ₗ[ℝ] A)
    (hcomm : ∀ x, O (D.T x) = D.T (O x)) {c : ℝ} (hbd : ∀ x, D.form (O x) (O x) ≤ c * D.form x x)
    {r : ℝ} {x : A} (h : RateVec D r x) : RateVec D r (O x) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨max c 0 * K, fun n => ?_⟩
  have hc : 0 ≤ max c 0 := le_max_right c 0
  have hnn := sqProfile_nonneg D x n
  have h1 : sqProfile D (O x) n ≤ c * sqProfile D x n := by
    unfold sqProfile
    rw [← pow_comm_of_comm D O hcomm n x]
    exact hbd _
  have h2 : c * sqProfile D x n ≤ max c 0 * sqProfile D x n :=
    mul_le_mul_of_nonneg_right (le_max_left c 0) hnn
  calc sqProfile D (O x) n ≤ max c 0 * sqProfile D x n := le_trans h1 h2
    _ ≤ max c 0 * (K * r ^ (2 * n)) := mul_le_mul_of_nonneg_left (hK n) hc
    _ = max c 0 * K * r ^ (2 * n) := by ring

#print axioms rateVec_map

/-- **A smoothing with dense range reads the gap exactly.** For `O` commuting with `T`, keeping the
vacuum complement, and with dense range on it: `GapAt D r` holds exactly when every smoothed
vacuum-orthogonal vector is a rate vector. The smoothing chooses the weights each vector puts on the
spectrum; the rates are the transfer's.

DERIVED: `0` is the sign of `r` and the vacuum pairing. -/
theorem gapAt_iff_smoothed (D : Transfer.TransferData A) (O : A →ₗ[ℝ] A) {r : ℝ} (hr : 0 ≤ r)
    (hOvac : ∀ x, D.form x D.vac = 0 → D.form (O x) D.vac = 0)
    (hdense : ViewDense D (O '' {x | D.form x D.vac = 0})) :
    TransferGap.GapAt D r ↔ ∀ x, D.form x D.vac = 0 → RateVec D r (O x) := by
  have horth : ∀ s ∈ O '' {x | D.form x D.vac = 0}, D.form s D.vac = 0 := by
    rintro s ⟨x, hx, rfl⟩
    exact hOvac x hx
  rw [gapAt_iff_viewRate_of_dense D hr horth hdense]
  constructor
  · intro h x hx
    exact h (O x) ⟨x, hx, rfl⟩
  · rintro h s ⟨x, hx, rfl⟩
    exact h x hx

#print axioms gapAt_iff_smoothed

/-! ## 4. "Zoom only coarsens": the coarse view inherits the fine gap -/

/-- **Zoom only coarsens.** A coarse transfer `Dc`, a form-isometric block map `B` into the fine
transfer `Df` sending vacuum to vacuum, and a domination of each coarse correlation function by the
fine one at doubled lag up to a constant per vector (equality with `K = 1` is the exact blocked
theory): the fine gap at `r` gives the coarse gap at `r²`, the same physical rate one block step
coarser. The coarse view reads no slower mode than the fine theory has.

DERIVED: `2` is the block factor (`2n` fine steps per coarse step) and, in `r²`, the rate at the
doubled time; `0` is the sign of `r` and the vacuum pairing. -/
theorem gapAt_coarse_of_compression {Ac Af : Type*} [AddCommGroup Ac] [Module ℝ Ac]
    [AddCommGroup Af] [Module ℝ Af] (Dc : Transfer.TransferData Ac) (Df : Transfer.TransferData Af)
    (B : Ac →ₗ[ℝ] Af) (hform : ∀ x y, Df.form (B x) (B y) = Dc.form x y)
    (hvac : B Dc.vac = Df.vac)
    (hmom : ∀ x : Ac, ∃ K : ℝ, ∀ n : ℕ,
      sqProfile Dc x n ≤ K * sqProfile Df (B x) (2 * n))
    {r : ℝ} (hr : 0 ≤ r) (hg : TransferGap.GapAt Df r) : TransferGap.GapAt Dc (r ^ 2) := by
  intro x hx
  have hBx : Df.form (B x) Df.vac = 0 := by rw [← hvac, hform]; exact hx
  obtain ⟨K, hK⟩ := hmom x
  have hrate : RateVec Dc (r ^ 2) x := by
    refine ⟨max K 0 * Dc.form x x, fun n => ?_⟩
    have hf := TransferGap.gap_pow Df hr hg (2 * n) (B x) hBx
    rw [hform] at hf
    have hk0 : 0 ≤ max K 0 := le_max_right K 0
    have hnn := sqProfile_nonneg Df (B x) (2 * n)
    calc sqProfile Dc x n ≤ K * sqProfile Df (B x) (2 * n) := hK n
      _ ≤ max K 0 * sqProfile Df (B x) (2 * n) := mul_le_mul_of_nonneg_right (le_max_left K 0) hnn
      _ ≤ max K 0 * (r ^ (2 * (2 * n)) * Dc.form x x) := mul_le_mul_of_nonneg_left hf hk0
      _ = max K 0 * Dc.form x x * (r ^ 2) ^ (2 * n) := by rw [← pow_mul]; ring
  have h := step_le_of_rateVec Dc (sq_nonneg r) hrate
  exact h

#print axioms gapAt_coarse_of_compression

/-- **The same in physical units.** Fine gap at `e^{−M a/2}` (spacing `a/2`) gives coarse gap at
`e^{−M a}` (spacing `a`): the coarse view's physical rate is at least the fine one.

DERIVED: `2` is the block factor. -/
theorem gapAt_coarse_of_compression_phys {Ac Af : Type*} [AddCommGroup Ac] [Module ℝ Ac]
    [AddCommGroup Af] [Module ℝ Af] (Dc : Transfer.TransferData Ac) (Df : Transfer.TransferData Af)
    (B : Ac →ₗ[ℝ] Af) (hform : ∀ x y, Df.form (B x) (B y) = Dc.form x y)
    (hvac : B Dc.vac = Df.vac)
    (hmom : ∀ x : Ac, ∃ K : ℝ, ∀ n : ℕ,
      sqProfile Dc x n ≤ K * sqProfile Df (B x) (2 * n))
    (M a : ℝ) (hg : TransferGap.GapAt Df (Real.exp (-(M * (a / 2))))) :
    TransferGap.GapAt Dc (Real.exp (-(M * a))) := by
  have h := gapAt_coarse_of_compression Dc Df B hform hvac hmom (Real.exp_pos _).le hg
  rw [exp_half_sq] at h
  exact h

#print axioms gapAt_coarse_of_compression_phys

/-! ## 5. The converse needs density -/

/-- **A view with a rate and no gap.** A positive transfer on `ℝ³`, a vacuum-orthogonal view whose
every vector is a rate vector at `1/2`, and no gap at any rate below one: the view is the invariant
coarse span of `ObserverGapSplit.coarse_gap_does_not_lift`, which is not dense. The escape of this
no-go is `ViewDense`.

DERIVED: `3` is the dimension of the witness; `1/2` its coarse rate; `1` the threshold on `ρ²`. -/
theorem viewRate_without_density_no_gap :
    ∃ (D : Transfer.TransferData (Fin 3 → ℝ)) (S : Set (Fin 3 → ℝ)),
      GNSHilbert.PositiveTransfer D ∧ (∀ s ∈ S, D.form s D.vac = 0) ∧ ViewRate D S (1 / 2) ∧
        ∀ ρ : ℝ, ρ ^ 2 < 1 → ¬ TransferGap.GapAt D ρ := by
  obtain ⟨D, C, hP, _, hTC, _, hcoarse, hno⟩ := ObserverGapSplit.coarse_gap_does_not_lift
  refine ⟨D, {c | c ∈ C ∧ D.form c D.vac = 0}, hP, fun s hs => hs.2, ?_, hno⟩
  intro s hs
  refine ⟨D.form s s, fun n => ?_⟩
  have hmem : ∀ k : ℕ, (D.T ^ k) s ∈ C := by
    intro k
    induction k with
    | zero => simpa using hs.1
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hTC _ ih
  have hrec : ∀ k : ℕ, sqProfile D s k ≤ (1 / 2 : ℝ) ^ (2 * k) * D.form s s := by
    intro k
    induction k with
    | zero => simp [sqProfile]
    | succ k ih =>
        have hstep := hcoarse _ (hmem k) (ObserverGapSplit.form_pow_orth D k hs.2)
        have he : (D.T ^ (k + 1)) s = D.T ((D.T ^ k) s) := by
          rw [pow_succ', Module.End.mul_apply]
        unfold sqProfile at ih ⊢
        rw [he]
        calc D.form (D.T ((D.T ^ k) s)) (D.T ((D.T ^ k) s))
            ≤ (1 / 2 : ℝ) ^ 2 * D.form ((D.T ^ k) s) ((D.T ^ k) s) := hstep
          _ ≤ (1 / 2 : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ (2 * k) * D.form s s) := by gcongr
          _ = (1 / 2 : ℝ) ^ (2 * (k + 1)) * D.form s s := by ring
  calc sqProfile D s n ≤ (1 / 2 : ℝ) ^ (2 * n) * D.form s s := hrec n
    _ = D.form s s * (1 / 2 : ℝ) ^ (2 * n) := mul_comm _ _

#print axioms viewRate_without_density_no_gap

/-! ## 6. The UV step on the view -/

/-- **The UV step on the view.** For two couplings `β, β' ≥ βUV` one block step apart (the
admissibility of `UVIRSplit.LossStep`) and every `M`: the view's per-vector rate at `e^{−M a β}` at
`β` gives the view's per-vector rate at `e^{−(M − ε(a β)) a β'}` at `β'`, constants free.

DERIVED: `2` is the block factor. -/
def ViewLossStep (D : ℝ → Transfer.TransferData A) (S : ℝ → Set A) (a : ℝ → ℝ) (βUV : ℝ)
    (ε : ℝ → ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → a β / 2 ≤ a β' → a β' ≤ a β →
    ∀ M : ℝ, ViewRate (D β) (S β) (Real.exp (-(M * a β))) →
      ViewRate (D β') (S β') (Real.exp (-((M - ε (a β)) * a β')))

/-- **The view step clipped at `M₀`**, the form `RestoreShimsClay.UVBelowIR` consumes.

DERIVED: `2` is the block factor. -/
def ViewLossStepBelow (D : ℝ → Transfer.TransferData A) (S : ℝ → Set A) (a : ℝ → ℝ) (βUV : ℝ)
    (ε : ℝ → ℝ) (M₀ : ℝ) : Prop :=
  ∀ β β' : ℝ, βUV ≤ β → βUV ≤ β' → a β / 2 ≤ a β' → a β' ≤ a β →
    ∀ M : ℝ, M ≤ M₀ → ViewRate (D β) (S β) (Real.exp (-(M * a β))) →
      ViewRate (D β') (S β') (Real.exp (-((M - ε (a β)) * a β')))

/-- **The view step gives the lattice step** under density and vacuum-orthogonality of the view.

DERIVED: no numeral beyond the step's. -/
theorem lossStep_of_viewLossStep (D : ℝ → Transfer.TransferData A) (S : ℝ → Set A) (a : ℝ → ℝ)
    (βUV : ℝ) (ε : ℝ → ℝ) (horth : ∀ β, βUV ≤ β → ∀ s ∈ S β, (D β).form s (D β).vac = 0)
    (hdense : ∀ β, βUV ≤ β → ViewDense (D β) (S β)) (h : ViewLossStep D S a βUV ε) :
    UVIRSplit.LossStep D a βUV ε := by
  intro β β' hβ hβ' h1 h2 M hg
  have hv := viewRate_of_gapAt (D β) (Real.exp_pos _).le (horth β hβ) hg
  exact gapAt_of_viewRate_dense (D β') (Real.exp_pos _).le (h β β' hβ hβ' h1 h2 M hv)
    (hdense β' hβ')

#print axioms lossStep_of_viewLossStep

/-- **The lattice step gives the view step** under the same hypotheses.

DERIVED: no numeral beyond the step's. -/
theorem viewLossStep_of_lossStep (D : ℝ → Transfer.TransferData A) (S : ℝ → Set A) (a : ℝ → ℝ)
    (βUV : ℝ) (ε : ℝ → ℝ) (horth : ∀ β, βUV ≤ β → ∀ s ∈ S β, (D β).form s (D β).vac = 0)
    (hdense : ∀ β, βUV ≤ β → ViewDense (D β) (S β)) (h : UVIRSplit.LossStep D a βUV ε) :
    ViewLossStep D S a βUV ε := by
  intro β β' hβ hβ' h1 h2 M hv
  have hg := gapAt_of_viewRate_dense (D β) (Real.exp_pos _).le hv (hdense β hβ)
  exact viewRate_of_gapAt (D β') (Real.exp_pos _).le (horth β' hβ') (h β β' hβ hβ' h1 h2 M hg)

#print axioms viewLossStep_of_lossStep

/-- **Under density the UV step is the view step.**

DERIVED: no numeral beyond the step's. -/
theorem lossStep_iff_viewLossStep (D : ℝ → Transfer.TransferData A) (S : ℝ → Set A) (a : ℝ → ℝ)
    (βUV : ℝ) (ε : ℝ → ℝ) (horth : ∀ β, βUV ≤ β → ∀ s ∈ S β, (D β).form s (D β).vac = 0)
    (hdense : ∀ β, βUV ≤ β → ViewDense (D β) (S β)) :
    UVIRSplit.LossStep D a βUV ε ↔ ViewLossStep D S a βUV ε :=
  ⟨viewLossStep_of_lossStep D S a βUV ε horth hdense,
    lossStep_of_viewLossStep D S a βUV ε horth hdense⟩

#print axioms lossStep_iff_viewLossStep

/-- **The clipped view step gives the clipped lattice step.**

DERIVED: no numeral beyond the step's. -/
theorem lossStepBelow_of_viewLossStepBelow (D : ℝ → Transfer.TransferData A) (S : ℝ → Set A)
    (a : ℝ → ℝ) (βUV : ℝ) (ε : ℝ → ℝ) (M₀ : ℝ)
    (horth : ∀ β, βUV ≤ β → ∀ s ∈ S β, (D β).form s (D β).vac = 0)
    (hdense : ∀ β, βUV ≤ β → ViewDense (D β) (S β)) (h : ViewLossStepBelow D S a βUV ε M₀) :
    UVIRSplit.LossStepBelow D a βUV ε M₀ := by
  intro β β' hβ hβ' h1 h2 M hM hg
  have hv := viewRate_of_gapAt (D β) (Real.exp_pos _).le (horth β hβ) hg
  exact gapAt_of_viewRate_dense (D β') (Real.exp_pos _).le (h β β' hβ hβ' h1 h2 M hM hv)
    (hdense β' hβ')

#print axioms lossStepBelow_of_viewLossStepBelow

/-- **The clipped lattice step gives the clipped view step.**

DERIVED: no numeral beyond the step's. -/
theorem viewLossStepBelow_of_lossStepBelow (D : ℝ → Transfer.TransferData A) (S : ℝ → Set A)
    (a : ℝ → ℝ) (βUV : ℝ) (ε : ℝ → ℝ) (M₀ : ℝ)
    (horth : ∀ β, βUV ≤ β → ∀ s ∈ S β, (D β).form s (D β).vac = 0)
    (hdense : ∀ β, βUV ≤ β → ViewDense (D β) (S β)) (h : UVIRSplit.LossStepBelow D a βUV ε M₀) :
    ViewLossStepBelow D S a βUV ε M₀ := by
  intro β β' hβ hβ' h1 h2 M hM hv
  have hg := gapAt_of_viewRate_dense (D β) (Real.exp_pos _).le hv (hdense β hβ)
  exact viewRate_of_gapAt (D β') (Real.exp_pos _).le (horth β' hβ')
    (h β β' hβ hβ' h1 h2 M hM hg)

#print axioms viewLossStepBelow_of_lossStepBelow

end Abstract

/-! ## 7. At the periodic Wilson data -/

section Periodic

variable {N : ℕ}

/-- **The UV input of the finite-box route from the view.** A view `S β` of the periodic
gauge-invariant half-space algebra, vacuum-orthogonal and dense at every coupling from `βUV`, the
clipped view step at `M₀` with non-negative losses and a budget `E < M₀` along the dyadic tower below
`aRun N β₀`: `RestoreShimsClay.UVBelowIR τ p hN β₀ βUV M₀`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank and the sign of the losses. -/
theorem uvBelowIR_of_view (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {β₀ βUV M₀ E : ℝ} {ε : ℝ → ℝ}
    (S : ℝ → Set ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ p))
    (horth : ∀ β, βUV ≤ β → ∀ s ∈ S β,
      (PeriodicState.periodicGaugeInvData τ p hN β).form s
        (PeriodicState.periodicGaugeInvData τ p hN β).vac = 0)
    (hdense : ∀ β, βUV ≤ β → ViewDense (PeriodicState.periodicGaugeInvData τ p hN β) (S β))
    (hε : ∀ s, 0 ≤ ε s) (hbud : UVIRSplit.LossBudget ε (AsymptoticScaling.aRun N β₀) E)
    (hE : E < M₀)
    (hview : ViewLossStepBelow (fun β => PeriodicState.periodicGaugeInvData τ p hN β) S
      (AsymptoticScaling.aRun N) βUV ε M₀) :
    ClayRoutes.UVBelowIR τ p hN β₀ βUV M₀ :=
  ⟨ε, E, hε, hbud, hE,
    lossStepBelow_of_viewLossStepBelow _ S _ βUV ε M₀ horth hdense hview⟩

#print axioms uvBelowIR_of_view

open MassGap.ContinuumField MassGap.ContinuumSchwinger in
/-- **The continuum Clay statement from one box and the UV step on the view.**
`RestoreShimsClay.clay_continuum_of_boxPatchGap` with its UV input `UVBelowIR` supplied by
`uvBelowIR_of_view`.

DERIVED: `2` is the least rank with a non-zero Haar variance; `0` is the excluded colour count, the
reflection plane and the lower end of `L` and `β₀`; `4` is the spacetime dimension;
`17N²/(88π²)` is the peak of `aRun N`, carried as `RestoreShimsClay.clay_continuum_of_boxPatchGap`
carries it. -/
theorem clay_continuum_of_boxPatchGap_view (hN2 : 2 ≤ N) (hN : N ≠ 0)
    (Z : ℕ → LField (MassGap.SUN.SU N) → ℝ) (τ : Fin 4) (hZ : ∀ k O, Z k (O.refl τ) = Z k O)
    (hB : ContinuumSep.UniformBoundSep hN (Renorm.connected hN Z)) {L : ℝ} (hL : 0 < L)
    {β₀ βUV γ E : ℝ} {n : ℕ} {ε : ℝ → ℝ} (hβ₀ : 0 < β₀) (hUVβ₀ : βUV ≤ β₀)
    (hpeak : 17 * (N : ℝ) ^ 2 / (88 * Real.pi ^ 2) ≤ βUV)
    (hbox : BoxPatch.BoxPatchGap hN β₀ n γ)
    (S : ℝ → Set ↥(MassGap.GaugeInvariantAlgebra.gaugeInvHalfSpaceAlg (G := MassGap.SUN.SU N) τ 0))
    (horth : ∀ β, βUV ≤ β → ∀ s ∈ S β,
      (PeriodicState.periodicGaugeInvData τ 0 hN β).form s
        (PeriodicState.periodicGaugeInvData τ 0 hN β).vac = 0)
    (hdense : ∀ β, βUV ≤ β → ViewDense (PeriodicState.periodicGaugeInvData τ 0 hN β) (S β))
    (hε : ∀ s, 0 ≤ ε s) (hbud : UVIRSplit.LossBudget ε (AsymptoticScaling.aRun N β₀) E)
    (hE : E < HeatBathLocal.boxRate N β₀ n γ)
    (hview : ViewLossStepBelow (fun β => PeriodicState.periodicGaugeInvData τ 0 hN β) S
      (AsymptoticScaling.aRun N) βUV ε (HeatBathLocal.boxRate N β₀ n γ))
    (O : LField (MassGap.SUN.SU N)) (G : ℝ → ℝ)
    (hconv : ContinuumNontrivial.KernelConvergesSep hN (Renorm.connected hN Z) τ O
      (fun p q => G (ContinuumNontrivial.eDist p q)))
    (hY : ShortDistanceY.AFShortDistance G) :
    ClayRoutes.ClayContinuum hN Z τ hZ hB L :=
  ClayRoutes.clay_continuum_of_boxPatchGap hN2 hN Z τ hZ hB hL hβ₀ hUVβ₀ hpeak hbox
    (uvBelowIR_of_view τ 0 hN S horth hdense hε hbud hE hview) O G hconv hY

#print axioms clay_continuum_of_boxPatchGap_view

end Periodic

end MassGap.ScaleStep
