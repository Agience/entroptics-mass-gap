import Mathlib
import MassGap.CondGap
import MassGap.WilsonSlab

/-!
# MassGap.FineLinks — the three links of the fine end (A), stated on the tree's objects

`RelativeGap`, `LayerRate` and `CondGap` reduce (A), the floor on the box gap at fixed aperture as the
zoom refines, to a layer rate for the new modes of each fixed cell (the conditional UV gap) and a
summable error on the intertwining defect `η_k` and the relative cross term `δ_k`. Asked why the new
short-distance modes inside one fixed cell forget quickly however fine the zoom, the owner gave three
links: (1) zoomed in, the reading is near-free (asymptotic freedom; short modes have mass `~ 1/a`);
(2) the aperture is fixed relative to the observer, so refining inside it does not change what the
observer reads; (3) read relative to the reading, a finer layer adds by `max` and cannot lower the
floor. This module states each link on the tree's objects, proves what follows from it, and names
what each leaves open. It does not prove (A) or the gap.

## 1. Link (1): near-free gives the conditional rate (finite form)

A two-slice law is a weight `J` on `α × α` with both marginals `π` (`Joint`); `jc J f g = Σ J f g`;
`CorrW π J W r`: mean-zero readings `f, g ∈ W` have `(Σ J f g)² ≤ r² ‖f‖² ‖g‖²` in `L²(π)`.
`Joint.of_markov`, `jc_kernel`: a Markov pair `(π, Q)` gives the law `π(x) Q(x,y)`, and
`jc = ⟨f, Q g⟩_π`.

* `NearFree π₀ J₀ J L W δ ε`: `|J − J₀| ≤ δ J₀ + L` pointwise, with `L ≥ 0` a large-field excess
  whose weight relative to every reading of `W` is at most `ε` (`Σ L f(x)² ≤ ε ‖f‖²_{π₀}`, both
  slices) and whose mass is at most `ε`. Every bound is relative to the readings' own norms.
* `corrW_of_nearFree` (**the perturbation lemma**): `CorrW π₀ J₀ W r₀`, `W` closed under adding
  constants, `NearFree`, `κ = δ + ε`, `κ + κ² < 1` give `CorrW π J W ((r₀ + κ + κ²)/(1 − κ − κ²))`.
  The steps: `nearFree_jc` (cross term `≤ (r₀ + κ)`), `nearFree_mean` (the shift of the mean
  `≤ κ`), `nearFree_nsq` (the norm `≥ 1 − κ`), all relative to the reference norms.
* `nearFreeRate_zero`; `nearFreeRate_le`: the rate is `≤ r₀ + 4κ` at `r₀ ≤ 1`, `0 ≤ κ ≤ 1/4`;
  `freeNearRate_lt_one`: at the free value `r₀ = e^{−arccosh 2} = 2 − √3` (`CondGap` section 4) it is
  `< 1` once `4κ < √3 − 1`.
* `large_of_sup₀`, `large_of_sup₁`: `ε ≤ M P` with `M = sup_x f(x)² / ‖f‖²_{π₀}` over `W` and `P` the
  excess mass. A large-field probability `P ~ e^{−cβ}` bounds the relative weight only through the
  sup ratio `M` of the readings.
* `contrOn_of_nearFree`: the per-step contraction of an invariant layer, the `hstep` of
  `CondGap.hW_of_condGap` on one fibre. `stepCorr_of_corrW`: on a fibre measure realised by a finite
  transfer (`CondGap.Realises`), a rate of its two-slice law is `CondGap.StepCorr`, the clause of
  `WilsonCondUVGap` — through a finite realisation only; no measure-level `NearFree` lemma is here,
  and the `NontrivialLayer` clause is not supplied.

**Residual of (1).** `NearFree` for the fibre Gibbs measure of one physical cell of the 4D `SU(N)`
Wilson measure given the block field, against its Gaussian (free, axially gauge-fixed) law, on the
gauge-invariant new-mode layer, with `4 κ_k < √3 − 1` uniformly in the zoom `k` and the block field.
That is a Bałaban-type statement: `δ_k` is the small-field density comparison, `ε_k` the large-field
weight relative to the readings. It gives the conditional UV gap (input (i)) with
`c = −log nearFreeRate > 0`; it concerns one cell at `β_k → ∞` and not the aperture size. For an
`L²` layer `M = ∞`, so `large_of_sup` does not close `ε` from `P(large field)`; the relative weight is
part of the input. On gauge-variant new modes the free reference rate itself tends to `1`
(`CondGap` part A), and the lemma gives nothing there.

## 2. Link (2): the aperture is fixed relative to the observer

The observer reads a fixed finite coarse variable: `c : β → O` with the same `O` at every zoom, its
readings `f ∘ c`. `obsPush π c` is the law of `c` under `π`.

* `sum_obsPush`, `mean_comp`, `nsq_comp`, `ip_comp`: the readings of `c` are `L²(obsPush π c)`.
  `obs_isometry`: with the same observer marginal at two zooms, `f ∘ c ↔ f ∘ c'` preserves the mean,
  the norm and the inner product. `obs_of_e`, `obsPush_eq_of_e`: conversely, an inner-product-preserving
  `e` that carries `f ∘ c` to `f ∘ c'` (the exact part `e` of the split restricted to the observer's
  readings) forces the same observer marginal.
* `ObsCorr π K c r`, the observer's rate; `obsCorr_iff_corrOn`: it is `RelativeGap.CorrOn` on
  `readings c`; `obsCorr_maxCorr`: it is at most the fine `maxCorr`.
* `obs_law_diff`: with `‖K' (e u) − e (K u)‖² ≤ η² ‖u‖²` on the mean-zero readings, the observer's
  two-slice form moves by `≤ η ‖f∘c‖ ‖g∘c‖`. `obsCorr_step`, `obsCorr_step_back`: the observer's rate at
  zoom `k+1` is `≤` its rate at `k` plus `η`, and conversely. `drift`, `obsCorr_along_zoom`: at zoom `k`
  it is `≤` its rate at `K₀` plus `Σ_{K₀ ≤ j < k} η_j`.
* `obsLaw_eq_of_exact`: at `η = 0` the observer's connected two-slice form is the same at both zooms.
  `eta_pos_of_flow`: if that form moves, every admissible `η` is positive. So `η_k` is bounded below by
  the change of the observer's coarse two-slice law under refinement (the block-spin defect). For the
  Wilson measure that law is the two-time law of the block field at zoom `k`, whose effective action
  changes with `k` (the renormalisation flow).

**What (2) carries.** It bounds the observer's rate along the zoom. `RelFloorM` bounds the fine
maximal correlation, and `RelativeGap.hidden_coarse`, `hidden_maxCorr` give a reading of correlation
`0` beside a hidden mode of correlation `1`: (2) alone gives no fine floor. **Residual of (2).** The
defect `η_k` of the Wilson block map, summable in `k`; it is at least the change of the observer's
coarse law, so its summability contains the convergence of the coarse law along the zoom. The
lemmas of this section assume an inner-product-preserving `e` on the observer's readings, which by
`obsPush_eq_of_e` forces the observer's marginal to be the same at both zooms; a moving marginal
needs an approximate-isometry version of them, not given here.

## 3. Link (3): a finer layer adds by `max`

* `link3_exact`: `LayerRate.refine_step_sq` at `η = δ = 0`, `ρ_{k+1}² ≤ max(ρ_k², r_W²)` — the
  squared `RelativeGap.refine_step`; `le_max_of_sq` takes the square root.
* `error_zero_iff`: the step error `η (2 + η) + δ` vanishes iff `η = δ = 0`. `fixedObs_of_noBudget`:
  a vanishing step error forces the observer's two-slice form to be the same at the two zooms.

(3) adds nothing beyond `RelativeGap.refine_step` and `LayerRate.refine_step_sq`. It removes the
summable budget of `LayerRate` section 2 only under exact intertwining, which needs the observer's
coarse law to be independent of the zoom: a fixed point of the refinement, the aperture invariance
itself. Otherwise the budget `Σ (η_k (2 + η_k) + δ_k)` stays.

## 4. The measure form on the Wilson box

* `refine_step_H`: the approximate step on inner product spaces (`ι` a linear isometry, defect `η`,
  layer rate `r_W`, cross term `δ`): `ρ(P')² ≤ max((ρ(P) + η)², r_W²) + δ`. `SplitM`, `refine_step_M`:
  the same on `SlabM`.
* `boxSlab`: the Doob slab of `m 2ᵏ` steps of the slice transfer of `WilsonSlab`'s box (`boxL`,
  `boxT`); `boxSlab_rho_le_one`.
* `relFloorM_box_of_splits`: at every aperture `m > 0`, a start `ρ_{K m}² ≤ ρb_m²`, `SplitM` data at every
  step `k ≥ K m` with `r_W² ≤ ρb_m²`, and summed errors `≤ E m` with `ρb_m² + E m < 1` give `RelFloorM`
  on the box slabs. `fixedApertureFloor_box_of_splits`: with `WilsonSlab.fixedApertureFloor_wilson_box`,
  `FixedApertureFloor` for the box gap `−log ratio / a_k`.

No declaration here constructs `SplitM` for the Wilson box; `ι`, the layer, `η`, `δ` and `r_W` are its
inputs, and the finite-form links of sections 1 and 2 are not tied to its `L²` objects.

## 5. Numerics

`research/code/fine_links_checks.py` (under 10 s, no Monte Carlo).

* Link (1), a compact two-slice law on the circle `∝ exp(β[(1 + √3)(cos θ + cos θ') + cos(θ − θ')])`
  against its Gaussian law (correlation `2 − √3`), readings the cubic polynomials of `√β θ`:
  at `β = 16, 64, 256, 1024`, `κ = 6.8·10⁻², 1.6·10⁻², 4.1·10⁻³, 1.0·10⁻³` (`κ β ≈ 1.0 … 1.1`),
  bound `0.3676, 0.2894, 0.2731, 0.2692` against the rate on `W` `0.26711, 0.26774, 0.26790,
  0.26794`, reference `0.267949 = 2 − √3`; `ε ≤ M P` at every `β`. The cut minimising `κ` is the core
  `|√β θ| ≤ 0.5`: the comparison is pointwise relative, and `L` absorbs the rest.
* Link (2), 4D free field (each photon polarisation as a massless scalar, spatial zero mode removed),
  `τ = L = 1`, the observer reading the `2³` physical cell averages: at `N = 4, 8, 16, 32` the
  observer rate is `5.15·10⁻³, 2.39·10⁻³, 1.92·10⁻³, 1.81·10⁻³` (fine rate `5.15·10⁻³ … 1.91·10⁻³`);
  per step the observer's marginal moves by `4.8·10⁻², 9.9·10⁻³, 2.3·10⁻³` and its relative cross form
  by `2.8·10⁻³, 4.7·10⁻⁴, 1.1·10⁻⁴` (ratios `≈ 0.2`, summable). The cross-form change is a lower
  bound for `η_k` given an admissible `e` (`obs_law_diff`); the moving marginal means the exact
  hypotheses of section 2 do not hold here (no inner-product-preserving `e` exists). At `τ = 1`,
  `a = 1/8`, `L = 1, 2, 4`: `0.0024, 0.043, 0.199` (beside `e^{−2π/L}`), tending to `1`. Links (1)
  and (2) hold at the fine end for the free field, link (3) is checked on 2D `SU(2)` below; what fails
  for the free field is (B).
* Link (3), 2D `SU(2)`, the observer reading holonomy class functions: heat-kernel action, the
  observer's law is the same at every zoom (`η = 0`, semigroup defect `1.1·10⁻¹⁶`); Wilson action at
  `β_k` fixing the fundamental slab value: `η_k = 2.2·10⁻², 2.5·10⁻³, 1.3·10⁻⁴, 8.0·10⁻⁶, …`, ratios
  `→ 0.062 ≈ 1/16`, sum `2.5·10⁻²`, the `j = 1` entry tending to the heat-kernel value `e^{−8/3}`. The
  2D gauge-invariant new-mode layer is `{constants}` (`CondGap` part A), so there `r_W = δ = 0`.

## 6. What remains for (A)

In the owner's terms: **zoomed in, every fixed cell is near-free uniformly in the zoom, and the
observer's reading converges along it.** Formally, for the 4D `SU(N)` Wilson box at `β_k → ∞`: at
every step `k → k+1` the `SplitM` data of `relFloorM_box_of_splits`, with `r_W` supplied by `NearFree`
of the conditional cell law on the gauge-invariant new modes (`4 κ_k < √3 − 1` uniformly), and
`Σ_k (η_k (2 + η_k) + δ_k)` below `1 − ρb²`. Both clauses are short-distance statements about one
cell and the steps of the zoom; neither bounds anything uniformly in the aperture, which is (B).

DERIVED (module-wide): `0` the mean that selects the readings orthogonal to the vacuum and the sign of
every bound; `1` the mass of each two-slice law, the bound `ρ ≤ 1` and the bound `RelFloorM` asks
below; `2` the `L²` exponent, the cross term counted twice and the `2` of `η (2 + η)`; `2 − √3` the
free per-step factor `e^{−arccosh 2}` of `CondGap`; `4` and `1/4` the slope and window of
`nearFreeRate_le` (`(r₀ + κ + κ²) ≤ (r₀ + 4κ)(1 − κ − κ²)` there, from `3κ + 2κ² ≤ 1`); `2ᵏ` the
doubling of the box.
-/

noncomputable section

namespace MassGap.FineLinks

open Filter Topology Matrix GapL2 MeasureTheory
open MassGap.RelativeGap MassGap.LayerRate MassGap.CondGap
open MassGap.SlabMeasure MassGap.SlabKernelOperator MassGap.WilsonSlab MassGap.FixedAperture

/-! ## 1. Link (1): near-free at the fine end -/

section NearFree

variable {α : Type*} [Fintype α]

/-- **The uncentred two-slice correlation** `Σ_{x,y} J(x,y) f(x) g(y)` of a joint weight `J`. -/
def jc (J : α → α → ℝ) (f g : α → ℝ) : ℝ := ∑ x, ∑ y, J x y * f x * g y

/-- **A two-slice law with both marginals `π`**: `J ≥ 0`, row and column sums `π`, total mass `1`. -/
structure Joint (π : α → ℝ) (J : α → α → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ J x y
  left : ∀ x, ∑ y, J x y = π x
  right : ∀ y, ∑ x, J x y = π y
  pi_sum : ∑ x, π x = 1

/-- **The rate of a two-slice law on a set `W` of readings**: mean-zero `f, g ∈ W` have
`(Σ J f g)² ≤ r² ‖f‖² ‖g‖²` in `L²(π)`. -/
def CorrW (π : α → ℝ) (J : α → α → ℝ) (W : Set (α → ℝ)) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ f ∈ W, ∀ g ∈ W, mean π f = 0 → mean π g = 0 →
    jc J f g ^ 2 ≤ r ^ 2 * nsq π f * nsq π g

theorem Joint.pi_nonneg {π : α → ℝ} {J : α → α → ℝ} (h : Joint π J) (x : α) : 0 ≤ π x := by
  rw [← h.left x]; exact Finset.sum_nonneg fun y _ => h.nonneg x y

/-- **A Markov pair gives a two-slice law** `π(x) Q(x,y)`. -/
theorem Joint.of_markov {π : α → ℝ} {Q : Matrix α α ℝ} (M : Markov π Q) :
    Joint π (fun x y => π x * Q x y) where
  nonneg x y := mul_nonneg (M.pi_nonneg x) (M.nonneg x y)
  left x := by
    show ∑ y, π x * Q x y = π x
    rw [← Finset.mul_sum, M.row x, mul_one]
  right y := by
    show ∑ x, π x * Q x y = π y
    exact M.stat y
  pi_sum := M.pi_sum

/-- **The two-slice correlation of a kernel**: `Σ π(x) Q(x,y) f(x) g(y) = ⟨f, Q g⟩_π`. -/
theorem jc_kernel (π : α → ℝ) (Q : Matrix α α ℝ) (f g : α → ℝ) :
    jc (fun x y => π x * Q x y) f g = ip π f (Q *ᵥ g) := by
  simp only [jc, ip, mulVec_apply', Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem Joint.mean_eq {π : α → ℝ} {J : α → α → ℝ} (h : Joint π J) (u : α → ℝ) :
    mean π u = ∑ x, ∑ y, J x y * u x := by
  unfold mean
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← h.left x, Finset.sum_mul]

theorem Joint.mean_eq₁ {π : α → ℝ} {J : α → α → ℝ} (h : Joint π J) (v : α → ℝ) :
    mean π v = ∑ x, ∑ y, J x y * v y := by
  rw [Finset.sum_comm]
  unfold mean
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← h.right y, Finset.sum_mul]

theorem Joint.nsq_eq₀ {π : α → ℝ} {J : α → α → ℝ} (h : Joint π J) (u : α → ℝ) :
    nsq π u = ∑ x, ∑ y, J x y * u x ^ 2 := by
  unfold nsq
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← h.left x, Finset.sum_mul]

theorem Joint.nsq_eq₁ {π : α → ℝ} {J : α → α → ℝ} (h : Joint π J) (v : α → ℝ) :
    nsq π v = ∑ x, ∑ y, J x y * v y ^ 2 := by
  rw [Finset.sum_comm]
  unfold nsq
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← h.right y, Finset.sum_mul]

theorem Joint.total {π : α → ℝ} {J : α → α → ℝ} (h : Joint π J) : ∑ x, ∑ y, J x y = 1 := by
  rw [← h.pi_sum]; exact Finset.sum_congr rfl fun x _ => h.left x

/-- **Shifting the readings by constants**:
`Σ J (F − s)(G − t) = Σ J F G − t ⟨F⟩ − s ⟨G⟩ + s t`. -/
theorem Joint.jc_shift {π : α → ℝ} {J : α → α → ℝ} (h : Joint π J) (F G : α → ℝ) (s t : ℝ) :
    jc J (fun x => F x - s) (fun y => G y - t)
      = jc J F G - t * mean π F - s * mean π G + s * t := by
  rw [h.mean_eq F, h.mean_eq₁ G]
  have e3 := h.total
  have e : ∀ x y, J x y * (F x - s) * (G y - t) = J x y * F x * G y - t * (J x y * F x)
      - s * (J x y * G y) + s * t * J x y := fun x y => by ring
  simp only [jc, e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e3]
  ring

/-- `S² ≤ c² A B` with `c, A, B ≥ 0` gives `|S| ≤ c √A √B`. -/
theorem abs_le_of_sq_le_mul {S c A B : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : S ^ 2 ≤ c ^ 2 * A * B) : |S| ≤ c * (Real.sqrt A * Real.sqrt B) := by
  have hx : 0 ≤ c * (Real.sqrt A * Real.sqrt B) := by positivity
  refine abs_le_of_sq_le_sq ?_ hx
  rw [mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, ← mul_assoc]
  exact h

/-- **Cauchy–Schwarz for a nonnegative two-slice weight.** -/
theorem dsum_cs {w : α → α → ℝ} (hw : ∀ x y, 0 ≤ w x y) (u v : α → ℝ) :
    (∑ x, ∑ y, w x y * |u x| * |v y|) ^ 2
      ≤ (∑ x, ∑ y, w x y * u x ^ 2) * ∑ x, ∑ y, w x y * v y ^ 2 := by
  have h := ip_sq_le (π := fun p : α × α => w p.1 p.2) (fun p => hw p.1 p.2)
    (fun p => |u p.1|) (fun p => |v p.2|)
  simp only [ip, nsq, Fintype.sum_prod_type, sq_abs] at h
  exact h

/-- **A weighted cross sum bounded by the readings' own weights**: `Σ w u² ≤ c A`, `Σ w v² ≤ c B`
give `Σ w |u| |v| ≤ c √A √B`. -/
theorem dsum_bound {w : α → α → ℝ} (hw : ∀ x y, 0 ≤ w x y) {u v : α → ℝ} {c A B : ℝ}
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∑ x, ∑ y, w x y * u x ^ 2 ≤ c * A) (hv : ∑ x, ∑ y, w x y * v y ^ 2 ≤ c * B) :
    ∑ x, ∑ y, w x y * |u x| * |v y| ≤ c * (Real.sqrt A * Real.sqrt B) := by
  have hv0 : 0 ≤ ∑ x, ∑ y, w x y * v y ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hw x y) (sq_nonneg _)
  have h2 : (∑ x, ∑ y, w x y * |u x| * |v y|) ^ 2 ≤ c ^ 2 * A * B := by
    calc _ ≤ _ := dsum_cs hw u v
      _ ≤ (c * A) * (c * B) := mul_le_mul hu hv hv0 (mul_nonneg hc hA)
      _ = c ^ 2 * A * B := by ring
  exact (le_abs_self _).trans (abs_le_of_sq_le_mul hc hA hB h2)

/-- **The one-reading form**: `Σ w u² ≤ c A` and `Σ w ≤ c` give `Σ w |u| ≤ c √A`. -/
theorem dsum_bound₁ {w : α → α → ℝ} (hw : ∀ x y, 0 ≤ w x y) {u : α → ℝ} {c A : ℝ}
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hu : ∑ x, ∑ y, w x y * u x ^ 2 ≤ c * A)
    (hm : ∑ x, ∑ y, w x y ≤ c) : ∑ x, ∑ y, w x y * |u x| ≤ c * Real.sqrt A := by
  have h := ip_sq_le (π := fun p : α × α => w p.1 p.2) (fun p => hw p.1 p.2)
    (fun p => |u p.1|) (fun _ => 1)
  simp only [ip, nsq, Fintype.sum_prod_type, sq_abs, mul_one, one_pow] at h
  have hm0 : 0 ≤ ∑ x, ∑ y, w x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hw x y
  have h2 : (∑ x, ∑ y, w x y * |u x|) ^ 2 ≤ c ^ 2 * A * 1 := by
    calc _ ≤ _ := h
      _ ≤ (c * A) * c := mul_le_mul hu hm hm0 (mul_nonneg hc hA)
      _ = c ^ 2 * A * 1 := by ring
  have h3 := abs_le_of_sq_le_mul hc hA zero_le_one h2
  rw [Real.sqrt_one, mul_one] at h3
  exact (le_abs_self _).trans h3

/-- **The density comparison, pointwise**: `|J − J₀| ≤ δ J₀ + L` gives
`|Σ (J − J₀) u v| ≤ δ Σ J₀ |u| |v| + Σ L |u| |v|`. -/
theorem abs_diff_le {J₀ J L : α → α → ℝ} {δ : ℝ}
    (hd : ∀ x y, |J x y - J₀ x y| ≤ δ * J₀ x y + L x y) (u v : α → ℝ) :
    |∑ x, ∑ y, (J x y - J₀ x y) * u x * v y|
      ≤ δ * (∑ x, ∑ y, J₀ x y * |u x| * |v y|) + ∑ x, ∑ y, L x y * |u x| * |v y| := by
  calc |∑ x, ∑ y, (J x y - J₀ x y) * u x * v y|
      ≤ ∑ x, |∑ y, (J x y - J₀ x y) * u x * v y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |(J x y - J₀ x y) * u x * v y| :=
        Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, (δ * (J₀ x y * |u x| * |v y|) + L x y * |u x| * |v y|) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_mul]
        have h1 : 0 ≤ |u x| * |v y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_right (hd x y) h1]
    _ = δ * (∑ x, ∑ y, J₀ x y * |u x| * |v y|) + ∑ x, ∑ y, L x y * |u x| * |v y| := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- **The density comparison, one reading.** -/
theorem abs_diff_le₁ {J₀ J L : α → α → ℝ} {δ : ℝ}
    (hd : ∀ x y, |J x y - J₀ x y| ≤ δ * J₀ x y + L x y) (u : α → ℝ) :
    |∑ x, ∑ y, (J x y - J₀ x y) * u x|
      ≤ δ * (∑ x, ∑ y, J₀ x y * |u x|) + ∑ x, ∑ y, L x y * |u x| := by
  calc |∑ x, ∑ y, (J x y - J₀ x y) * u x|
      ≤ ∑ x, |∑ y, (J x y - J₀ x y) * u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |(J x y - J₀ x y) * u x| :=
        Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, (δ * (J₀ x y * |u x|) + L x y * |u x|) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul]
        nlinarith [mul_le_mul_of_nonneg_right (hd x y) (abs_nonneg (u x))]
    _ = δ * (∑ x, ∑ y, J₀ x y * |u x|) + ∑ x, ∑ y, L x y * |u x| := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- **The density comparison, one squared reading.** -/
theorem abs_diff_le_sq {J₀ J L : α → α → ℝ} {δ : ℝ}
    (hd : ∀ x y, |J x y - J₀ x y| ≤ δ * J₀ x y + L x y) (u : α → ℝ) :
    |∑ x, ∑ y, (J x y - J₀ x y) * u x ^ 2|
      ≤ δ * (∑ x, ∑ y, J₀ x y * u x ^ 2) + ∑ x, ∑ y, L x y * u x ^ 2 := by
  calc |∑ x, ∑ y, (J x y - J₀ x y) * u x ^ 2|
      ≤ ∑ x, |∑ y, (J x y - J₀ x y) * u x ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |(J x y - J₀ x y) * u x ^ 2| :=
        Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, (δ * (J₀ x y * u x ^ 2) + L x y * u x ^ 2) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg (u x))]
        nlinarith [mul_le_mul_of_nonneg_right (hd x y) (sq_nonneg (u x))]
    _ = δ * (∑ x, ∑ y, J₀ x y * u x ^ 2) + ∑ x, ∑ y, L x y * u x ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- **Near-free, relative to the readings.** The two-slice law `J` is within `δ` of the reference
(free) law `J₀` in density, `|J − J₀| ≤ δ J₀ + L`, up to a nonnegative large-field excess `L` whose
weight relative to every reading `f ∈ W` is at most `ε` (`Σ L f(x)² ≤ ε ‖f‖²_{π₀}`, the same in the
second slice) and whose mass is at most `ε`. -/
structure NearFree (π₀ : α → ℝ) (J₀ J L : α → α → ℝ) (W : Set (α → ℝ)) (δ ε : ℝ) : Prop where
  δ_nonneg : 0 ≤ δ
  ε_nonneg : 0 ≤ ε
  L_nonneg : ∀ x y, 0 ≤ L x y
  dens : ∀ x y, |J x y - J₀ x y| ≤ δ * J₀ x y + L x y
  large₀ : ∀ f ∈ W, ∑ x, ∑ y, L x y * f x ^ 2 ≤ ε * nsq π₀ f
  large₁ : ∀ g ∈ W, ∑ x, ∑ y, L x y * g y ^ 2 ≤ ε * nsq π₀ g
  mass : ∑ x, ∑ y, L x y ≤ ε

/-- **The perturbed rate** `(r₀ + κ + κ²) / (1 − κ − κ²)`. -/
def nearFreeRate (r₀ κ : ℝ) : ℝ := (r₀ + κ + κ ^ 2) / (1 - κ - κ ^ 2)

variable {π₀ π : α → ℝ} {J₀ J L : α → α → ℝ} {W : Set (α → ℝ)} {r₀ δ ε : ℝ}

/-- The mean of a reference-centred reading under the true law: `|⟨F⟩_π| ≤ (δ + ε) ‖F‖_{π₀}`. -/
theorem nearFree_mean (h₀ : Joint π₀ J₀) (h : Joint π J) (hN : NearFree π₀ J₀ J L W δ ε)
    {F : α → ℝ} (hF : F ∈ W) (hF0 : mean π₀ F = 0) :
    |mean π F| ≤ (δ + ε) * Real.sqrt (nsq π₀ F) := by
  have hA := nsq_nonneg h₀.pi_nonneg F
  have e : mean π F = ∑ x, ∑ y, (J x y - J₀ x y) * F x := by
    have h1 := h.mean_eq F
    have h2 := h₀.mean_eq F
    rw [hF0] at h2
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  rw [e]
  have h3 := abs_diff_le₁ hN.dens F
  have h4 : ∑ x, ∑ y, J₀ x y * |F x| ≤ 1 * Real.sqrt (nsq π₀ F) :=
    dsum_bound₁ h₀.nonneg zero_le_one hA (le_of_eq (by rw [one_mul, h₀.nsq_eq₀ F]))
      (le_of_eq h₀.total)
  have h5 : ∑ x, ∑ y, L x y * |F x| ≤ ε * Real.sqrt (nsq π₀ F) :=
    dsum_bound₁ hN.L_nonneg hN.ε_nonneg hA (hN.large₀ F hF) hN.mass
  nlinarith [mul_le_mul_of_nonneg_left h4 hN.δ_nonneg]

/-- The norm of a reading under the true law: `(1 − δ − ε) ‖F‖²_{π₀} ≤ ‖F‖²_π`. -/
theorem nearFree_nsq (h₀ : Joint π₀ J₀) (h : Joint π J) (hN : NearFree π₀ J₀ J L W δ ε)
    {F : α → ℝ} (hF : F ∈ W) : (1 - (δ + ε)) * nsq π₀ F ≤ nsq π F := by
  have e : nsq π F = nsq π₀ F + ∑ x, ∑ y, (J x y - J₀ x y) * F x ^ 2 := by
    rw [h.nsq_eq₀ F, h₀.nsq_eq₀ F]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have h3 := abs_diff_le_sq hN.dens F
  rw [← h₀.nsq_eq₀ F] at h3
  have h5 := hN.large₀ F hF
  have h6 := neg_abs_le (∑ x, ∑ y, (J x y - J₀ x y) * F x ^ 2)
  rw [e]
  nlinarith

/-- The cross term of two reference-centred readings: `|Σ J F G| ≤ (r₀ + δ + ε) ‖F‖ ‖G‖`. -/
theorem nearFree_jc (h₀ : Joint π₀ J₀) (hr₀ : CorrW π₀ J₀ W r₀) (hN : NearFree π₀ J₀ J L W δ ε)
    {F G : α → ℝ} (hF : F ∈ W) (hG : G ∈ W) (hF0 : mean π₀ F = 0) (hG0 : mean π₀ G = 0) :
    |jc J F G| ≤ (r₀ + (δ + ε)) * (Real.sqrt (nsq π₀ F) * Real.sqrt (nsq π₀ G)) := by
  have hA := nsq_nonneg h₀.pi_nonneg F
  have hB := nsq_nonneg h₀.pi_nonneg G
  have hsplit : jc J F G = jc J₀ F G + ∑ x, ∑ y, (J x y - J₀ x y) * F x * G y := by
    simp only [jc, sub_mul, Finset.sum_sub_distrib]
    ring
  have h1 := abs_le_of_sq_le_mul hr₀.1 hA hB (hr₀.2 F hF G hG hF0 hG0)
  have h2 := abs_diff_le hN.dens F G
  have h3 : ∑ x, ∑ y, J₀ x y * |F x| * |G y|
      ≤ 1 * (Real.sqrt (nsq π₀ F) * Real.sqrt (nsq π₀ G)) :=
    dsum_bound h₀.nonneg zero_le_one hA hB (le_of_eq (by rw [one_mul, h₀.nsq_eq₀ F]))
      (le_of_eq (by rw [one_mul, h₀.nsq_eq₁ G]))
  have h4 := dsum_bound hN.L_nonneg hN.ε_nonneg hA hB (hN.large₀ F hF) (hN.large₁ G hG)
  have h5 := abs_add_le (jc J₀ F G) (∑ x, ∑ y, (J x y - J₀ x y) * F x * G y)
  rw [← hsplit] at h5
  nlinarith [mul_le_mul_of_nonneg_left h3 hN.δ_nonneg]

/-- **The perturbation step on a pair of readings**, centred at the true means. -/
theorem nearFree_pair (h₀ : Joint π₀ J₀) (h : Joint π J) (hr₀ : CorrW π₀ J₀ W r₀)
    (hN : NearFree π₀ J₀ J L W δ ε) (hκ : (δ + ε) + (δ + ε) ^ 2 < 1) {F G f g : α → ℝ}
    (hF : F ∈ W) (hG : G ∈ W) (hF0 : mean π₀ F = 0) (hG0 : mean π₀ G = 0)
    (hf : f = fun x => F x - mean π F) (hg : g = fun y => G y - mean π G) :
    jc J f g ^ 2 ≤ nearFreeRate r₀ (δ + ε) ^ 2 * nsq π f * nsq π g := by
  subst hf hg
  have hκ0 : 0 ≤ δ + ε := add_nonneg hN.δ_nonneg hN.ε_nonneg
  have hq : 0 < 1 - (δ + ε) - (δ + ε) ^ 2 := by linarith
  have hA := nsq_nonneg h₀.pi_nonneg F
  have hB := nsq_nonneg h₀.pi_nonneg G
  have sA := Real.sqrt_nonneg (nsq π₀ F)
  have sB := Real.sqrt_nonneg (nsq π₀ G)
  have hA2 : Real.sqrt (nsq π₀ F) ^ 2 = nsq π₀ F := Real.sq_sqrt hA
  have hB2 : Real.sqrt (nsq π₀ G) ^ 2 = nsq π₀ G := Real.sq_sqrt hB
  have hj := abs_le.1 (nearFree_jc h₀ hr₀ hN hF hG hF0 hG0)
  have hmF := nearFree_mean h₀ h hN hF hF0
  have hmG := nearFree_mean h₀ h hN hG hG0
  have hmm : |mean π F * mean π G|
      ≤ ((δ + ε) * Real.sqrt (nsq π₀ F)) * ((δ + ε) * Real.sqrt (nsq π₀ G)) := by
    rw [abs_mul]; exact mul_le_mul hmF hmG (abs_nonneg _) (mul_nonneg hκ0 sA)
  have hmm' := abs_le.1 hmm
  have hsh : jc J (fun x => F x - mean π F) (fun y => G y - mean π G)
      = jc J F G - mean π F * mean π G := by
    rw [h.jc_shift F G (mean π F) (mean π G)]; ring
  have hnF : (1 - (δ + ε) - (δ + ε) ^ 2) * nsq π₀ F ≤ nsq π (fun x => F x - mean π F) := by
    have e := nsq_split h.pi_sum F
    have h1 := nearFree_nsq h₀ h hN hF
    have h2 : mean π F ^ 2 ≤ (δ + ε) ^ 2 * nsq π₀ F := by
      have := pow_le_pow_left₀ (abs_nonneg _) hmF 2
      rw [sq_abs, mul_pow, hA2] at this; exact this
    linarith
  have hnG : (1 - (δ + ε) - (δ + ε) ^ 2) * nsq π₀ G ≤ nsq π (fun y => G y - mean π G) := by
    have e := nsq_split h.pi_sum G
    have h1 := nearFree_nsq h₀ h hN hG
    have h2 : mean π G ^ 2 ≤ (δ + ε) ^ 2 * nsq π₀ G := by
      have := pow_le_pow_left₀ (abs_nonneg _) hmG 2
      rw [sq_abs, mul_pow, hB2] at this; exact this
    linarith
  have hRq : nearFreeRate r₀ (δ + ε) * (1 - (δ + ε) - (δ + ε) ^ 2)
      = r₀ + (δ + ε) + (δ + ε) ^ 2 := by
    rw [nearFreeRate, div_mul_cancel₀ _ hq.ne']
  have hP : |jc J (fun x => F x - mean π F) (fun y => G y - mean π G)|
      ≤ nearFreeRate r₀ (δ + ε) * (1 - (δ + ε) - (δ + ε) ^ 2)
        * (Real.sqrt (nsq π₀ F) * Real.sqrt (nsq π₀ G)) := by
    rw [hRq, hsh]
    refine abs_le.2 ⟨?_, ?_⟩
    · nlinarith [hj.1, hmm'.2]
    · nlinarith [hj.2, hmm'.1]
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hP 2
  rw [sq_abs] at hsq
  calc _ ≤ _ := hsq
    _ = (nearFreeRate r₀ (δ + ε) * (1 - (δ + ε) - (δ + ε) ^ 2)) ^ 2
          * (Real.sqrt (nsq π₀ F) ^ 2 * Real.sqrt (nsq π₀ G) ^ 2) := by ring
    _ = nearFreeRate r₀ (δ + ε) ^ 2 * ((1 - (δ + ε) - (δ + ε) ^ 2) * nsq π₀ F)
          * ((1 - (δ + ε) - (δ + ε) ^ 2) * nsq π₀ G) := by rw [hA2, hB2]; ring
    _ ≤ nearFreeRate r₀ (δ + ε) ^ 2 * nsq π (fun x => F x - mean π F)
          * nsq π (fun y => G y - mean π G) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnF (sq_nonneg _)) hnG (mul_nonneg hq.le hB)
          (mul_nonneg (sq_nonneg _) (nsq_nonneg h.pi_nonneg _))

/-- **Link (1), the perturbation lemma.** If the reference (free) two-slice law `J₀` has rate `r₀`
on a set `W` of readings closed under adding constants, and the true law `J` is near-free relative
to the readings (`NearFree`, density within `δ`, large-field excess of relative weight `ε`), with
`κ = δ + ε` and `κ + κ² < 1`, then `J` has rate `(r₀ + κ + κ²) / (1 − κ − κ²)` on `W`. -/
theorem corrW_of_nearFree (h₀ : Joint π₀ J₀) (h : Joint π J)
    (hW : ∀ f ∈ W, ∀ c : ℝ, (fun x => f x - c) ∈ W) (hr₀ : CorrW π₀ J₀ W r₀)
    (hN : NearFree π₀ J₀ J L W δ ε) (hκ : (δ + ε) + (δ + ε) ^ 2 < 1) :
    CorrW π J W (nearFreeRate r₀ (δ + ε)) := by
  have hκ0 : 0 ≤ δ + ε := add_nonneg hN.δ_nonneg hN.ε_nonneg
  have hq : 0 < 1 - (δ + ε) - (δ + ε) ^ 2 := by linarith
  have hnum : 0 ≤ r₀ + (δ + ε) + (δ + ε) ^ 2 :=
    add_nonneg (add_nonneg hr₀.1 hκ0) (sq_nonneg _)
  refine ⟨div_nonneg hnum hq.le, fun f hf g hg hf0 hg0 => ?_⟩
  have hF0 : mean π₀ (fun x => f x - mean π₀ f) = 0 := by
    rw [mean_sub_const h₀.pi_sum, sub_self]
  have hG0 : mean π₀ (fun y => g y - mean π₀ g) = 0 := by
    rw [mean_sub_const h₀.pi_sum, sub_self]
  have hmF : mean π (fun x => f x - mean π₀ f) = -mean π₀ f := by
    rw [mean_sub_const h.pi_sum, hf0, zero_sub]
  have hmG : mean π (fun y => g y - mean π₀ g) = -mean π₀ g := by
    rw [mean_sub_const h.pi_sum, hg0, zero_sub]
  refine nearFree_pair h₀ h hr₀ hN hκ (hW f hf (mean π₀ f)) (hW g hg (mean π₀ g)) hF0 hG0 ?_ ?_
  · funext x
    rw [hmF]
    show f x = f x - mean π₀ f - -mean π₀ f
    ring
  · funext y
    rw [hmG]
    show g y = g y - mean π₀ g - -mean π₀ g
    ring

/-- **At `κ = 0` the rate is the reference rate.** -/
theorem nearFreeRate_zero (r₀ : ℝ) : nearFreeRate r₀ 0 = r₀ := by
  simp [nearFreeRate]

/-- **The perturbed rate is `r₀ + O(κ)`**: `≤ r₀ + 4κ` at `r₀ ≤ 1`, `0 ≤ κ ≤ 1/4`. -/
theorem nearFreeRate_le {r₀ κ : ℝ} (hr1 : r₀ ≤ 1) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 4) :
    nearFreeRate r₀ κ ≤ r₀ + 4 * κ := by
  have hq : 0 < 1 - κ - κ ^ 2 := by nlinarith
  unfold nearFreeRate
  rw [div_le_iff₀ hq]
  have h1 : r₀ * (κ + κ ^ 2) ≤ 1 * (κ + κ ^ 2) :=
    mul_le_mul_of_nonneg_right hr1 (add_nonneg hκ0 (sq_nonneg κ))
  have h2 : 0 ≤ κ * (1 - 3 * κ - 2 * κ ^ 2) := mul_nonneg hκ0 (by nlinarith)
  nlinarith [h1, h2]

/-- **Below `1` near the free point** `r₀ = e^{−arccosh 2} = 2 − √3`: at `0 ≤ κ ≤ 1/4` with
`4κ < √3 − 1` the perturbed rate is `< 1`. -/
theorem freeNearRate_lt_one {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 4)
    (h : 4 * κ < Real.sqrt 3 - 1) :
    nearFreeRate (Real.exp (-Real.log (2 + Real.sqrt 3))) κ < 1 := by
  rw [exp_neg_arccosh_two]
  have h3 : (1 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  calc nearFreeRate (2 - Real.sqrt 3) κ ≤ 2 - Real.sqrt 3 + 4 * κ :=
        nearFreeRate_le (by linarith) hκ0 hκ
    _ < 1 := by linarith

/-- **The large-field weight from a sup ratio**: if every reading of `W` has
`f(x)² ≤ M ‖f‖²_{π₀}` and the excess has mass `≤ P`, its relative weight is `≤ M P`. -/
theorem large_of_sup₀ {L : α → α → ℝ} (hL : ∀ x y, 0 ≤ L x y) {M P : ℝ} (hM : 0 ≤ M)
    (hP : ∑ x, ∑ y, L x y ≤ P) (hπ₀ : ∀ x, 0 ≤ π₀ x) {f : α → ℝ}
    (hf : ∀ x, f x ^ 2 ≤ M * nsq π₀ f) :
    ∑ x, ∑ y, L x y * f x ^ 2 ≤ M * P * nsq π₀ f := by
  calc ∑ x, ∑ y, L x y * f x ^ 2 ≤ ∑ x, ∑ y, L x y * (M * nsq π₀ f) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hf x) (hL x y)
    _ = (∑ x, ∑ y, L x y) * (M * nsq π₀ f) := by simp only [Finset.sum_mul]
    _ ≤ P * (M * nsq π₀ f) :=
        mul_le_mul_of_nonneg_right hP (mul_nonneg hM (nsq_nonneg hπ₀ f))
    _ = M * P * nsq π₀ f := by ring

/-- The second-slice form of `large_of_sup₀`. -/
theorem large_of_sup₁ {L : α → α → ℝ} (hL : ∀ x y, 0 ≤ L x y) {M P : ℝ} (hM : 0 ≤ M)
    (hP : ∑ x, ∑ y, L x y ≤ P) (hπ₀ : ∀ x, 0 ≤ π₀ x) {g : α → ℝ}
    (hg : ∀ y, g y ^ 2 ≤ M * nsq π₀ g) :
    ∑ x, ∑ y, L x y * g y ^ 2 ≤ M * P * nsq π₀ g := by
  calc ∑ x, ∑ y, L x y * g y ^ 2 ≤ ∑ x, ∑ y, L x y * (M * nsq π₀ g) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hg y) (hL x y)
    _ = (∑ x, ∑ y, L x y) * (M * nsq π₀ g) := by simp only [Finset.sum_mul]
    _ ≤ P * (M * nsq π₀ g) :=
        mul_le_mul_of_nonneg_right hP (mul_nonneg hM (nsq_nonneg hπ₀ g))
    _ = M * P * nsq π₀ g := by ring

/-- **Link (1) in contraction form on one fibre**: for Markov pairs `(π₀, Q₀)` (free) and `(π, Q)`
(true fibre transfer), `Q` mapping `W` into itself, the near-free comparison of their two-slice laws
gives the per-step contraction of the mean-zero readings of `W` by `nearFreeRate r₀ (δ + ε)` — the
`hstep` of `CondGap.hW_of_condGap` on that fibre. -/
theorem contrOn_of_nearFree {Q₀ Q : Matrix α α ℝ} (M₀ : Markov π₀ Q₀) (M : Markov π Q)
    (hW : ∀ f ∈ W, ∀ c : ℝ, (fun x => f x - c) ∈ W) (hinv : ∀ g ∈ W, Q *ᵥ g ∈ W)
    (hr₀ : CorrW π₀ (fun x y => π₀ x * Q₀ x y) W r₀)
    (hN : NearFree π₀ (fun x y => π₀ x * Q₀ x y) (fun x y => π x * Q x y) L W δ ε)
    (hκ : (δ + ε) + (δ + ε) ^ 2 < 1) :
    ∀ g ∈ W, mean π g = 0 → nsq π (Q *ᵥ g) ≤ nearFreeRate r₀ (δ + ε) ^ 2 * nsq π g :=
  contrOn_of_corrOn M hinv fun f hf g hg hf0 hg0 => by
    have := (corrW_of_nearFree (Joint.of_markov M₀) (Joint.of_markov M) hW hr₀ hN hκ).2
      f hf g hg hf0 hg0
    rwa [jc_kernel] at this

end NearFree

section Realise

variable {Ω F : Type*} [MeasurableSpace Ω] [Fintype F]

/-- **Link (1) gives `StepCorr` on a realised fibre**: a rate of the two-slice law `π Q` on `W`
is the per-step correlation bound `CondGap.StepCorr` of any fibre measure realised by `(π, Q)`. -/
theorem stepCorr_of_corrW {m : Measure Ω} {X₀ X₁ : Ω → F} {π : F → ℝ} {Q : Matrix F F ℝ} {Z : ℝ}
    (hR : Realises m X₀ X₁ π Q Z) {W : Set (F → ℝ)} {r : ℝ}
    (h : CorrW π (fun x y => π x * Q x y) W r) : StepCorr m X₀ X₁ W r := by
  refine ⟨h.1, fun f hf g hg _ _ hf0 hg0 => ?_⟩
  have hZ := hR.pos
  have hf' : mean π f = 0 := by
    rw [hR.mean₀] at hf0; exact (mul_eq_zero.1 hf0).resolve_left hZ.ne'
  have hg' : mean π g = 0 := by
    rw [hR.mean₁] at hg0; exact (mul_eq_zero.1 hg0).resolve_left hZ.ne'
  have h1 := h.2 f hf g hg hf' hg'
  rw [jc_kernel] at h1
  rw [hR.cross, hR.sq₀, hR.sq₁]
  have e : r ^ 2 * (Z * nsq π f) * (Z * nsq π g) = Z ^ 2 * (r ^ 2 * nsq π f * nsq π g) := by ring
  rw [e, mul_pow]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg Z)

end Realise

/-! ## 2. Link (2): the aperture is fixed relative to the observer -/

section Observer

variable {β β' O : Type*} [Fintype β] [Fintype β']

/-- **The observer's marginal**: the law of the observer's coarse value `c(y)` under `π`. -/
def obsPush [DecidableEq O] (π : β → ℝ) (c : β → O) : O → ℝ :=
  fun x => ∑ y, if c y = x then π y else 0

section Push

variable [Fintype O] [DecidableEq O]

theorem sum_obsPush (π : β → ℝ) (c : β → O) (u : O → ℝ) :
    ∑ x, obsPush π c x * u x = ∑ y, π y * u (c y) := by
  simp only [obsPush, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [ite_mul, zero_mul]
  exact Fintype.sum_ite_eq (c y) (fun x => π y * u x)

theorem mean_comp (π : β → ℝ) (c : β → O) (u : O → ℝ) : mean π (u ∘ c) = mean (obsPush π c) u :=
  (sum_obsPush π c u).symm

theorem nsq_comp (π : β → ℝ) (c : β → O) (u : O → ℝ) : nsq π (u ∘ c) = nsq (obsPush π c) u :=
  (sum_obsPush π c fun x => u x ^ 2).symm

theorem ip_comp (π : β → ℝ) (c : β → O) (f g : O → ℝ) :
    ip π (f ∘ c) (g ∘ c) = ip (obsPush π c) f g := by
  have h := sum_obsPush π c (fun x => f x * g x)
  unfold ip
  simp only [Function.comp_apply, mul_assoc]
  exact h.symm

/-- **The observer's readings at two zooms are isometric** when its marginal is the same: the
correspondence `f ∘ c ↔ f ∘ c'` preserves the mean, the `L²` norm and the inner product. -/
theorem obs_isometry {π : β → ℝ} {π' : β' → ℝ} {c : β → O} {c' : β' → O}
    (hc : obsPush π' c' = obsPush π c) (f g : O → ℝ) :
    mean π' (f ∘ c') = mean π (f ∘ c) ∧ nsq π' (f ∘ c') = nsq π (f ∘ c) ∧
      ip π' (f ∘ c') (g ∘ c') = ip π (f ∘ c) (g ∘ c) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mean_comp, mean_comp, hc]
  · rw [nsq_comp, nsq_comp, hc]
  · rw [ip_comp, ip_comp, hc]

end Push

/-- **The observer's rate**: mean-zero readings `f ∘ c`, `g ∘ c` of the observer's fixed coarse
variable have correlation at most `r` across the slab `(π, K)`, relative to their own norms. -/
def ObsCorr (π : β → ℝ) (K : Matrix β β ℝ) (c : β → O) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ f g : O → ℝ, mean π (f ∘ c) = 0 → mean π (g ∘ c) = 0 →
    ip π (f ∘ c) (K *ᵥ (g ∘ c)) ^ 2 ≤ r ^ 2 * nsq π (f ∘ c) * nsq π (g ∘ c)

/-- **`ObsCorr` is `RelativeGap.CorrOn` on the readings of `c`.** -/
theorem obsCorr_iff_corrOn {π : β → ℝ} {K : Matrix β β ℝ} {c : β → O} {r : ℝ} :
    ObsCorr π K c r ↔ CorrOn π K (readings c) r := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ hu hv
    exact h u v hu hv
  · rintro ⟨h0, h⟩
    exact ⟨h0, fun f g hf hg => h _ ⟨f, rfl⟩ _ ⟨g, rfl⟩ hf hg⟩

/-- **The observer reads at most the fine correlation.** -/
theorem obsCorr_maxCorr {π : β → ℝ} {K : Matrix β β ℝ} (M : Markov π K) (c : β → O) :
    ObsCorr π K c (maxCorr π K) :=
  ⟨maxCorr_nonneg M, fun _ _ hf hg => (corr_maxCorr M).2 _ _ hf hg⟩

/-- **A reading-preserving isometry fixes the observer's mean and norm**: if `e` preserves the
inner product and carries `f ∘ c` to `f ∘ c'`, then `f ∘ c'` has the mean and norm of `f ∘ c`. -/
theorem obs_of_e {π : β → ℝ} {π' : β' → ℝ} {c : β → O} {c' : β' → O} (e : (β → ℝ) → (β' → ℝ))
    (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v) (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c')
    (f : O → ℝ) : mean π' (f ∘ c') = mean π (f ∘ c) ∧ nsq π' (f ∘ c') = nsq π (f ∘ c) := by
  have h1 : (fun _ : β' => (1 : ℝ)) = (fun _ : O => (1 : ℝ)) ∘ c' := rfl
  have h0 : (fun _ : β => (1 : ℝ)) = (fun _ : O => (1 : ℝ)) ∘ c := rfl
  refine ⟨?_, ?_⟩
  · rw [mean_eq_ip, mean_eq_ip, h1, h0, ← he_obs, ← he_obs, he_ip]
  · rw [nsq_eq_ip, nsq_eq_ip, ← he_obs, he_ip]

/-- **A reading-preserving isometry forces the observer's marginal to be the same at both zooms.** -/
theorem obsPush_eq_of_e [Fintype O] [DecidableEq O] {π : β → ℝ} {π' : β' → ℝ} {c : β → O}
    {c' : β' → O}
    (e : (β → ℝ) → (β' → ℝ)) (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v)
    (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c') : obsPush π' c' = obsPush π c := by
  funext x
  have h := (obs_of_e e he_ip he_obs (fun z => if z = x then (1 : ℝ) else 0)).1
  rw [mean_comp, mean_comp] at h
  simpa only [mean, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] using h

theorem ip_diff_right (π f u v : β' → ℝ) : ip π f u - ip π f v = ip π f (u - v) := by
  unfold ip
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.sub_apply]
  ring

variable {π : β → ℝ} {π' : β' → ℝ} {K : Matrix β β ℝ} {K' : Matrix β' β' ℝ} {c : β → O}
  {c' : β' → O}

/-- **The observer's reading changes by at most the intertwining defect.** With `e` an isometry
(inner products) carrying the observer's readings at zoom `k` to those at zoom `k+1`, and
`‖K' (e u) − e (K u)‖² ≤ η² ‖u‖²` on the mean-zero readings, the observer's two-slice form moves by
`|⟨f∘c', K' (g∘c')⟩ − ⟨f∘c, K (g∘c)⟩| ≤ η ‖f∘c‖ ‖g∘c‖`. -/
theorem obs_law_diff (hπ' : ∀ y, 0 ≤ π' y) (e : (β → ℝ) → (β' → ℝ))
    (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v) (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c')
    {η : ℝ} (hη : 0 ≤ η)
    (hdef : ∀ g : O → ℝ, mean π (g ∘ c) = 0 →
      nsq π' (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) ≤ η ^ 2 * nsq π (g ∘ c))
    (f g : O → ℝ) (hg : mean π (g ∘ c) = 0) :
    |ip π' (f ∘ c') (K' *ᵥ (g ∘ c')) - ip π (f ∘ c) (K *ᵥ (g ∘ c))|
      ≤ η * (Real.sqrt (nsq π (f ∘ c)) * Real.sqrt (nsq π (g ∘ c))) := by
  have e1 : ip π' (f ∘ c') (K' *ᵥ (g ∘ c')) - ip π (f ∘ c) (K *ᵥ (g ∘ c))
      = ip π' (e (f ∘ c)) (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) := by
    rw [← he_obs f, ← he_obs g, ← he_ip (f ∘ c) (K *ᵥ (g ∘ c)), ip_diff_right]
  rw [e1]
  have hn : ∀ u, nsq π' (e u) = nsq π u := fun u => by rw [nsq_eq_ip, nsq_eq_ip, he_ip]
  have hA : 0 ≤ nsq π (f ∘ c) := by rw [← hn]; exact nsq_nonneg hπ' _
  have hB : 0 ≤ nsq π (g ∘ c) := by rw [← hn]; exact nsq_nonneg hπ' _
  refine abs_le_of_sq_le_mul hη hA hB ?_
  calc _ ≤ nsq π' (e (f ∘ c)) * nsq π' (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) :=
        ip_sq_le hπ' _ _
    _ ≤ nsq π (f ∘ c) * (η ^ 2 * nsq π (g ∘ c)) := by
        rw [hn]; exact mul_le_mul_of_nonneg_left (hdef g hg) hA
    _ = η ^ 2 * nsq π (f ∘ c) * nsq π (g ∘ c) := by ring

/-- **Link (2), forward**: the observer's rate at zoom `k+1` is at most its rate at zoom `k`
plus the intertwining defect `η`. -/
theorem obsCorr_step (hπ' : ∀ y, 0 ≤ π' y) (e : (β → ℝ) → (β' → ℝ))
    (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v) (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c')
    {η : ℝ} (hη : 0 ≤ η)
    (hdef : ∀ g : O → ℝ, mean π (g ∘ c) = 0 →
      nsq π' (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) ≤ η ^ 2 * nsq π (g ∘ c))
    {r : ℝ} (h : ObsCorr π K c r) : ObsCorr π' K' c' (r + η) := by
  refine ⟨add_nonneg h.1 hη, fun f g hf hg => ?_⟩
  obtain ⟨hmf, hnf⟩ := obs_of_e e he_ip he_obs f
  obtain ⟨hmg, hng⟩ := obs_of_e e he_ip he_obs g
  have hf0 : mean π (f ∘ c) = 0 := by rw [← hmf]; exact hf
  have hg0 : mean π (g ∘ c) = 0 := by rw [← hmg]; exact hg
  have hA : 0 ≤ nsq π (f ∘ c) := by rw [← hnf]; exact nsq_nonneg hπ' _
  have hB : 0 ≤ nsq π (g ∘ c) := by rw [← hng]; exact nsq_nonneg hπ' _
  have h1 := abs_le.1 (abs_le_of_sq_le_mul h.1 hA hB (h.2 f g hf0 hg0))
  have h2 := abs_le.1 (obs_law_diff hπ' e he_ip he_obs hη hdef f g hg0)
  have h3 : |ip π' (f ∘ c') (K' *ᵥ (g ∘ c'))|
      ≤ (r + η) * (Real.sqrt (nsq π (f ∘ c)) * Real.sqrt (nsq π (g ∘ c))) :=
    abs_le.2 ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [sq_abs] at hsq
  rw [hnf, hng]
  calc _ ≤ _ := hsq
    _ = (r + η) ^ 2 * (Real.sqrt (nsq π (f ∘ c)) ^ 2 * Real.sqrt (nsq π (g ∘ c)) ^ 2) := by ring
    _ = (r + η) ^ 2 * nsq π (f ∘ c) * nsq π (g ∘ c) := by
        rw [Real.sq_sqrt hA, Real.sq_sqrt hB]; ring

/-- **Link (2), backward**: the observer's rate at zoom `k` is at most its rate at zoom `k+1` plus
`η`. With `obsCorr_step`, the two rates differ by at most `η`. -/
theorem obsCorr_step_back (hπ' : ∀ y, 0 ≤ π' y) (e : (β → ℝ) → (β' → ℝ))
    (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v) (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c')
    {η : ℝ} (hη : 0 ≤ η)
    (hdef : ∀ g : O → ℝ, mean π (g ∘ c) = 0 →
      nsq π' (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) ≤ η ^ 2 * nsq π (g ∘ c))
    {s : ℝ} (h : ObsCorr π' K' c' s) : ObsCorr π K c (s + η) := by
  refine ⟨add_nonneg h.1 hη, fun f g hf hg => ?_⟩
  obtain ⟨hmf, hnf⟩ := obs_of_e e he_ip he_obs f
  obtain ⟨hmg, hng⟩ := obs_of_e e he_ip he_obs g
  have hf' : mean π' (f ∘ c') = 0 := by rw [hmf]; exact hf
  have hg' : mean π' (g ∘ c') = 0 := by rw [hmg]; exact hg
  have hA : 0 ≤ nsq π (f ∘ c) := by rw [← hnf]; exact nsq_nonneg hπ' _
  have hB : 0 ≤ nsq π (g ∘ c) := by rw [← hng]; exact nsq_nonneg hπ' _
  have h1 := h.2 f g hf' hg'
  rw [hnf, hng] at h1
  have h1' := abs_le.1 (abs_le_of_sq_le_mul h.1 hA hB h1)
  have h2 := abs_le.1 (obs_law_diff hπ' e he_ip he_obs hη hdef f g hg)
  have h3 : |ip π (f ∘ c) (K *ᵥ (g ∘ c))|
      ≤ (s + η) * (Real.sqrt (nsq π (f ∘ c)) * Real.sqrt (nsq π (g ∘ c))) :=
    abs_le.2 ⟨by linarith [h1'.1, h2.2], by linarith [h1'.2, h2.1]⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [sq_abs] at hsq
  calc _ ≤ _ := hsq
    _ = (s + η) ^ 2 * (Real.sqrt (nsq π (f ∘ c)) ^ 2 * Real.sqrt (nsq π (g ∘ c)) ^ 2) := by ring
    _ = (s + η) ^ 2 * nsq π (f ∘ c) * nsq π (g ∘ c) := by
        rw [Real.sq_sqrt hA, Real.sq_sqrt hB]; ring

/-- **Exact intertwining fixes the observer's law**: at `η = 0` the observer's connected two-slice
form is the same at both zooms. -/
theorem obsLaw_eq_of_exact (hπ' : ∀ y, 0 ≤ π' y) (e : (β → ℝ) → (β' → ℝ))
    (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v) (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c')
    (hdef : ∀ g : O → ℝ, mean π (g ∘ c) = 0 →
      nsq π' (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) ≤ 0 ^ 2 * nsq π (g ∘ c))
    (f g : O → ℝ) (hg : mean π (g ∘ c) = 0) :
    ip π' (f ∘ c') (K' *ᵥ (g ∘ c')) = ip π (f ∘ c) (K *ᵥ (g ∘ c)) := by
  have h := obs_law_diff hπ' e he_ip he_obs le_rfl hdef f g hg
  rw [zero_mul] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

/-- **A moving observer law forces a positive defect**: if the observer's two-slice form differs
between the zooms, every admissible intertwining defect `η` is positive. -/
theorem eta_pos_of_flow (hπ' : ∀ y, 0 ≤ π' y) (e : (β → ℝ) → (β' → ℝ))
    (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v) (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c')
    {η : ℝ} (hη : 0 ≤ η)
    (hdef : ∀ g : O → ℝ, mean π (g ∘ c) = 0 →
      nsq π' (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) ≤ η ^ 2 * nsq π (g ∘ c))
    {f g : O → ℝ} (hg : mean π (g ∘ c) = 0)
    (hne : ip π' (f ∘ c') (K' *ᵥ (g ∘ c')) ≠ ip π (f ∘ c) (K *ᵥ (g ∘ c))) : 0 < η := by
  rcases hη.lt_or_eq with h | h
  · exact h
  · subst h
    exact absurd (obsLaw_eq_of_exact hπ' e he_ip he_obs hdef f g hg) hne

end Observer

/-- **A step bound accumulates the defects**: `P K₀ r₀` and `P k r → P (k+1) (r + η k)` give
`P k (r₀ + Σ_{K₀ ≤ j < k} η j)`. -/
theorem drift {P : ℕ → ℝ → Prop} {η : ℕ → ℝ} {K₀ : ℕ} {r₀ : ℝ} (h0 : P K₀ r₀)
    (hstep : ∀ k, K₀ ≤ k → ∀ r, P k r → P (k + 1) (r + η k)) :
    ∀ k, K₀ ≤ k → P k (r₀ + ∑ j ∈ Finset.Ico K₀ k, η j) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using h0
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← add_assoc]
    exact hstep n hn _ ih

/-- **Link (2) along the zoom**: the observer's rate at every zoom `k ≥ K₀` is at most its rate at
`K₀` plus the summed intertwining defects. -/
theorem obsCorr_along_zoom {O : Type*} {B : ℕ → Type*} [∀ k, Fintype (B k)]
    {π : ∀ k, B k → ℝ} {K : ∀ k, Matrix (B k) (B k) ℝ} {c : ∀ k, B k → O} {η : ℕ → ℝ}
    {K₀ : ℕ} {r₀ : ℝ} (h0 : ObsCorr (π K₀) (K K₀) (c K₀) r₀)
    (hstep : ∀ k, K₀ ≤ k → ∀ r, ObsCorr (π k) (K k) (c k) r →
      ObsCorr (π (k + 1)) (K (k + 1)) (c (k + 1)) (r + η k)) :
    ∀ k, K₀ ≤ k → ObsCorr (π k) (K k) (c k) (r₀ + ∑ j ∈ Finset.Ico K₀ k, η j) :=
  drift (P := fun k r => ObsCorr (π k) (K k) (c k) r) h0 hstep

/-! ## 3. Link (3): a finer layer adds by `max` -/

section Max

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Link (3) under exact intertwining is `RelativeGap.refine_step`**: `LayerRate.refine_step_sq`
at `η = 0`, `δ = 0` gives `ρ_{k+1}² ≤ max(ρ_k², r_W²)`. -/
theorem link3_exact {π : α → ℝ} {K : Matrix α α ℝ} {π' : β → ℝ} {K' : Matrix β β ℝ}
    (M : Markov π K) (M' : Markov π' K') (e : (α → ℝ) → (β → ℝ))
    (he_nsq : ∀ u, nsq π' (e u) = nsq π u) (he_int : ∀ u, mean π u = 0 → K' *ᵥ e u = e (K *ᵥ u))
    {W : Set (β → ℝ)} {rW : ℝ} (hrW : 0 ≤ rW)
    (hW : ∀ w ∈ W, nsq π' (K' *ᵥ w) ≤ rW ^ 2 * nsq π' w)
    (hdec : ∀ g, mean π' g = 0 → ∃ u, mean π u = 0 ∧ ∃ w ∈ W, g = e u + w ∧
      ip π' (e u) w = 0 ∧ ip π' (K' *ᵥ e u) (K' *ᵥ w) = 0) :
    maxCorr π' K' ^ 2 ≤ max (maxCorr π K ^ 2) (rW ^ 2) := by
  have h := refine_step_sq M M' e he_nsq le_rfl
    (fun u hu => by rw [he_int u hu, sub_self]; simp [nsq]) hrW le_rfl hW
    (fun g hg => by
      obtain ⟨u, hu, w, hw, h1, h2, h3⟩ := hdec g hg
      exact ⟨u, hu, w, hw, h1, h2, by rw [h3]; simp⟩)
  have e0 : (0 : ℝ) * (2 + 0) + 0 = 0 := by norm_num
  rw [e0, add_zero] at h
  exact h

/-- `a² ≤ max(b², c²)` with `a, b, c ≥ 0` gives `a ≤ max(b, c)`. -/
theorem le_max_of_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 2 ≤ max (b ^ 2) (c ^ 2)) : a ≤ max b c := by
  have hm : max (b ^ 2) (c ^ 2) = max b c ^ 2 := by
    rcases le_total b c with hbc | hbc
    · rw [max_eq_right hbc, max_eq_right (pow_le_pow_left₀ hb hbc 2)]
    · rw [max_eq_left hbc, max_eq_left (pow_le_pow_left₀ hc hbc 2)]
  rw [hm] at h
  have h' := abs_le_of_sq_le_sq h (le_max_of_le_left hb)
  rwa [abs_of_nonneg ha] at h'

/-- **The summed error is zero only under exact data**: at `η, δ ≥ 0`,
`η (2 + η) + δ = 0 ↔ η = 0 ∧ δ = 0`. -/
theorem error_zero_iff {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    η * (2 + η) + δ = 0 ↔ η = 0 ∧ δ = 0 := by
  constructor
  · intro h
    have h1 : 0 ≤ η * (2 + η) := mul_nonneg hη (by linarith)
    have hd : δ = 0 := by linarith
    have he : η * (2 + η) = 0 := by linarith
    refine ⟨?_, hd⟩
    rcases mul_eq_zero.1 he with h2 | h2
    · exact h2
    · linarith
  · rintro ⟨rfl, rfl⟩
    ring

end Max

/-- **No budget forces a fixed observer law**: if the step error `η (2 + η) + δ` of
`LayerRate.refine_step_sq` is `0`, the defect `η` vanishes, and the observer's connected two-slice
form is the same at both zooms (`obsLaw_eq_of_exact`): the observer's coarse law is a fixed point
of the refinement. -/
theorem fixedObs_of_noBudget {β β' O : Type*} [Fintype β] [Fintype β']
    {π : β → ℝ} {π' : β' → ℝ} {K : Matrix β β ℝ} {K' : Matrix β' β' ℝ} {c : β → O}
    {c' : β' → O} (hπ' : ∀ y, 0 ≤ π' y) (e : (β → ℝ) → (β' → ℝ))
    (he_ip : ∀ u v, ip π' (e u) (e v) = ip π u v) (he_obs : ∀ f : O → ℝ, e (f ∘ c) = f ∘ c')
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hdef : ∀ g : O → ℝ, mean π (g ∘ c) = 0 →
      nsq π' (K' *ᵥ e (g ∘ c) - e (K *ᵥ (g ∘ c))) ≤ η ^ 2 * nsq π (g ∘ c))
    (h0 : η * (2 + η) + δ = 0) (f g : O → ℝ) (hg : mean π (g ∘ c) = 0) :
    ip π' (f ∘ c') (K' *ᵥ (g ∘ c')) = ip π (f ∘ c) (K *ᵥ (g ∘ c)) := by
  obtain ⟨hz, -⟩ := (error_zero_iff hη hδ).1 h0
  subst hz
  exact obsLaw_eq_of_exact hπ' e he_ip he_obs hdef f g hg

/-! ## 4. The measure form and the Wilson box -/

section Hilbert

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-- **The approximate refinement step on inner product spaces**: `ι` a linear isometry of the
coarser space into the finer one, intertwining defect `η` on `e₀⊥`, a layer `W` of rate `r_W`, and
every `g ⊥ e₀'` split as `ι u + w` with `u ⊥ e₀`, `w ∈ W`, `⟨ι u, w⟩ = 0` and relative cross term
`δ`. Then `ρ(P')² ≤ max((ρ(P) + η)², r_W²) + δ`. -/
theorem refine_step_H (P : E →L[ℝ] E) (e₀ : E) (P' : E' →L[ℝ] E') (e₀' : E') (ι : E →ₗᵢ[ℝ] E')
    {η δ rW : ℝ} (hδ : 0 ≤ δ)
    (hint : ∀ u, inner ℝ u e₀ = 0 → ‖P' (ι u) - ι (P u)‖ ≤ η * ‖u‖)
    {W : Set E'} (hW : ∀ w ∈ W, ‖P' w‖ ≤ rW * ‖w‖)
    (hdec : ∀ g, inner ℝ g e₀' = 0 → ∃ u, inner ℝ u e₀ = 0 ∧ ∃ w ∈ W, g = ι u + w ∧
      inner ℝ (ι u) w = 0 ∧ inner ℝ (P' (ι u)) (P' w) ^ 2 ≤ δ ^ 2 * ‖ι u‖ ^ 2 * ‖w‖ ^ 2) :
    rhoH P' e₀' ^ 2 ≤ max ((rhoH P e₀ + η) ^ 2) (rW ^ 2) + δ := by
  have hc := contrH_rhoH P e₀
  have hρ0 := rhoH_nonneg P e₀
  set M := max (rhoH P e₀ + η) rW with hM
  have hM1 : rhoH P e₀ + η ≤ M := le_max_left _ _
  have hM2 : rW ≤ M := le_max_right _ _
  have hMδ : 0 ≤ M ^ 2 + δ := add_nonneg (sq_nonneg _) hδ
  have key : ContrH P' e₀' (Real.sqrt (M ^ 2 + δ)) := by
    refine ⟨Real.sqrt_nonneg _, fun g hg => ?_⟩
    obtain ⟨u, hu, w, hw, rfl, h1, h2⟩ := hdec g hg
    have hnu : ‖ι u‖ = ‖u‖ := ι.norm_map u
    have hA : ‖P' (ι u)‖ ≤ M * ‖ι u‖ := by
      have h3 : ‖P' (ι u)‖ ≤ ‖ι (P u)‖ + ‖P' (ι u) - ι (P u)‖ := by
        have : P' (ι u) = ι (P u) + (P' (ι u) - ι (P u)) := by abel
        calc ‖P' (ι u)‖ = ‖ι (P u) + (P' (ι u) - ι (P u))‖ := congrArg norm this
          _ ≤ _ := norm_add_le _ _
      rw [ι.norm_map] at h3
      have h4 := hc.2 u hu
      have h5 := hint u hu
      rw [hnu]
      nlinarith [mul_le_mul_of_nonneg_right hM1 (norm_nonneg u)]
    have hB : ‖P' w‖ ≤ M * ‖w‖ :=
      (hW w hw).trans (mul_le_mul_of_nonneg_right hM2 (norm_nonneg w))
    have hX : 2 * inner ℝ (P' (ι u)) (P' w) ≤ δ * (‖ι u‖ ^ 2 + ‖w‖ ^ 2) := by
      have hab : 0 ≤ δ * (‖ι u‖ * ‖w‖) :=
        mul_nonneg hδ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have h6 : inner ℝ (P' (ι u)) (P' w) ≤ δ * (‖ι u‖ * ‖w‖) := by
        refine (abs_le_of_sq_le_sq' ?_ hab).2
        calc _ ≤ δ ^ 2 * ‖ι u‖ ^ 2 * ‖w‖ ^ 2 := h2
          _ = (δ * (‖ι u‖ * ‖w‖)) ^ 2 := by ring
      nlinarith [mul_nonneg hδ (sq_nonneg (‖ι u‖ - ‖w‖))]
    have hA2 : ‖P' (ι u)‖ ^ 2 ≤ M ^ 2 * ‖ι u‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hA 2; rwa [mul_pow] at this
    have hB2 : ‖P' w‖ ^ 2 ≤ M ^ 2 * ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hB 2; rwa [mul_pow] at this
    have e1 : ‖P' (ι u + w)‖ ^ 2
        = ‖P' (ι u)‖ ^ 2 + 2 * inner ℝ (P' (ι u)) (P' w) + ‖P' w‖ ^ 2 := by
      rw [map_add, norm_add_sq_real]
    have e2 : ‖ι u + w‖ ^ 2 = ‖ι u‖ ^ 2 + ‖w‖ ^ 2 := by
      rw [norm_add_sq_real, h1]; ring
    have hsq : ‖P' (ι u + w)‖ ^ 2 ≤ (Real.sqrt (M ^ 2 + δ) * ‖ι u + w‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hMδ, e1, e2]
      nlinarith [hA2, hB2, hX]
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
  have h1 : rhoH P' e₀' ≤ Real.sqrt (M ^ 2 + δ) := rhoH_le key
  have h2 : rhoH P' e₀' ^ 2 ≤ M ^ 2 + δ := by
    have := pow_le_pow_left₀ (rhoH_nonneg P' e₀') h1 2
    rwa [Real.sq_sqrt hMδ] at this
  have hmx : M ^ 2 ≤ max ((rhoH P e₀ + η) ^ 2) (rW ^ 2) := by
    rcases le_total (rhoH P e₀ + η) rW with h | h
    · rw [hM, max_eq_right h]; exact le_max_right _ _
    · rw [hM, max_eq_left h]; exact le_max_left _ _
  linarith

end Hilbert

/-- **The split data of one refinement step of `L²(π)` slabs**: a linear isometry `ι` of the
zoom-`k` space into the zoom-`(k+1)` space, intertwining defect `η` on mean-zero functions, a layer
`W` of rate `r_W`, and every mean-zero `g` split as `ι u + w` (`u` mean-zero, `w ∈ W`, orthogonal)
with relative cross term `δ`. -/
def SplitM (S S' : SlabM) (η δ rW : ℝ) : Prop :=
  0 ≤ η ∧ 0 ≤ δ ∧ 0 ≤ rW ∧ ∃ ι : Lp ℝ 2 S.π →ₗᵢ[ℝ] Lp ℝ 2 S'.π, ∃ W : Set (Lp ℝ 2 S'.π),
    (∀ u, inner ℝ u (oneLp S.π) = 0 → ‖S'.P (ι u) - ι (S.P u)‖ ≤ η * ‖u‖) ∧
    (∀ w ∈ W, ‖S'.P w‖ ≤ rW * ‖w‖) ∧
    (∀ g, inner ℝ g (oneLp S'.π) = 0 → ∃ u, inner ℝ u (oneLp S.π) = 0 ∧ ∃ w ∈ W,
      g = ι u + w ∧ inner ℝ (ι u) w = 0 ∧
      inner ℝ (S'.P (ι u)) (S'.P w) ^ 2 ≤ δ ^ 2 * ‖ι u‖ ^ 2 * ‖w‖ ^ 2)

/-- **The refinement step on `SlabM`**: `ρ'² ≤ max((ρ + η)², r_W²) + δ`. -/
theorem refine_step_M {S S' : SlabM} {η δ rW : ℝ} (h : SplitM S S' η δ rW) :
    S'.rho ^ 2 ≤ max ((S.rho + η) ^ 2) (rW ^ 2) + δ := by
  obtain ⟨-, hδ, -, ι, W, hint, hW, hdec⟩ := h
  exact refine_step_H S.P (oneLp S.π) S'.P (oneLp S'.π) ι hδ hint hW hdec

/-- **The Wilson box slab** of `WilsonSlab`: the Doob slab of `m 2ᵏ` steps of the slice transfer
of the periodic box with `m 2ᵏ` sites on every side, time direction `μ`, coupling `β m k > 0`. -/
abbrev boxSlab (μ : Fin 4) {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ) (hβ : ∀ m k, 0 < β m k)
    (m k : ℕ) : SlabM :=
  (perronKT μ (boxT μ m k) N hN (β m k) (hβ m k).le).slab (m * 2 ^ k)

/-- **The box slab rate is at most `1`** (`rho_slab`, `ratio_lt_one_wilson`). -/
theorem boxSlab_rho_le_one (μ : Fin 4) {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ)
    (hβ : ∀ m k, 0 < β m k) {m : ℕ} (hm : 0 < m) (k : ℕ) : (boxSlab μ hN β hβ m k).rho ≤ 1 := by
  have hn : 1 ≤ m * 2 ^ k :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' (pow_ne_zero _ two_ne_zero))
  show ((perronKT μ (boxT μ m k) N hN (β m k) (hβ m k).le).slab (m * 2 ^ k)).rho ≤ 1
  rw [PerronKernel.rho_slab _ hn]
  exact pow_le_one₀ (PerronKernel.ratio_nonneg _) (ratio_lt_one_wilson hN (hβ m k).le).le

/-- **`RelFloorM` on the Wilson box from the three links' data.** At every aperture `m > 0`: a start
`ρ_{K m}² ≤ ρb_m²`; at every zoom `k ≥ K m` the split data `SplitM` of the step `k → k+1` with
defect `η m k`, cross term `δ m k` (link (2)) and layer rate `r_W m k` with `r_W² ≤ ρb_m²` (link (1));
layers combined by `max` (link (3)); errors `η (2 + η) + δ` with partial sums `≤ E m` and
`ρb_m² + E m < 1`. Then `RelFloorM` holds on the box slabs with rate `√(ρb² + E)`. -/
theorem relFloorM_box_of_splits (μ : Fin 4) {N : ℕ} (hN : N ≠ 0) (β : ℕ → ℕ → ℝ)
    (hβ : ∀ m k, 0 < β m k) {ρb E : ℕ → ℝ} {K : ℕ → ℕ} {η δ rW : ℕ → ℕ → ℝ}
    (hη : ∀ m k, 0 ≤ η m k) (hδ : ∀ m k, 0 ≤ δ m k)
    (hb : ∀ m, 0 < m → 0 < ρb m ∧ ρb m ^ 2 + E m < 1)
    (h0 : ∀ m, 0 < m → (boxSlab μ hN β hβ m (K m)).rho ^ 2 ≤ ρb m ^ 2)
    (hsplit : ∀ m, 0 < m → ∀ k, K m ≤ k →
      SplitM (boxSlab μ hN β hβ m k) (boxSlab μ hN β hβ m (k + 1)) (η m k) (δ m k) (rW m k))
    (hh : ∀ m, 0 < m → ∀ k, K m ≤ k → rW m k ^ 2 ≤ ρb m ^ 2)
    (hE : ∀ m, 0 < m → ∀ k, ∑ j ∈ Finset.Ico (K m) k, (η m j * (2 + η m j) + δ m j) ≤ E m) :
    RelFloorM (fun m k => boxSlab μ hN β hβ m k) (fun m => Real.sqrt (ρb m ^ 2 + E m)) K := by
  intro m hm
  obtain ⟨hb0, hb1⟩ := hb m hm
  have hE0 : 0 ≤ E m := by simpa using hE m hm (K m)
  have hpos : 0 < ρb m ^ 2 + E m := by positivity
  refine ⟨Real.sqrt_pos.2 hpos, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hb1),
    fun k hk => ?_⟩
  have hf := floor_of_layers_approx (s := fun k => (boxSlab μ hN β hβ m k).rho ^ 2)
    (h := fun k => rW m k ^ 2) (e := fun k => η m k * (2 + η m k) + δ m k) (h0 m hm)
    (fun k hk => (refine_step_M (hsplit m hm k hk)).trans
      (max_sq_add_le (boxSlab_rho_le_one μ hN β hβ hm k) (hη m k)))
    (hh m hm) (fun k => add_nonneg (mul_nonneg (hη m k) (by linarith [hη m k])) (hδ m k)) k hk
  have hsq : (boxSlab μ hN β hβ m k).rho ^ 2 ≤ ρb m ^ 2 + E m :=
    hf.trans (by linarith [hE m hm k])
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

/-- **The (A)-chain on the Wilson box from the three links' data**: with `relFloorM_box_of_splits`
and an observer reading in `(0, R]`, `FixedApertureFloor` for the box gap `−log ratio / a_k`
(`WilsonSlab.fixedApertureFloor_wilson_box`), at `2 ≤ N`. -/
theorem fixedApertureFloor_box_of_splits (μ : Fin 4) {N : ℕ} (hN : N ≠ 0) (hN2 : 2 ≤ N)
    (β : ℕ → ℕ → ℝ) (hβ : ∀ m k, 0 < β m k) {a₀ : ℝ} (ha : 0 < a₀) {rLat : ℕ → ℝ} {R : ℝ}
    (hR : 0 < R) (hr : ∀ k, 0 < rLat k ∧ rLat k ≤ R) {ρb E : ℕ → ℝ} {K : ℕ → ℕ}
    {η δ rW : ℕ → ℕ → ℝ} (hη : ∀ m k, 0 ≤ η m k) (hδ : ∀ m k, 0 ≤ δ m k)
    (hb : ∀ m, 0 < m → 0 < ρb m ∧ ρb m ^ 2 + E m < 1)
    (h0 : ∀ m, 0 < m → (boxSlab μ hN β hβ m (K m)).rho ^ 2 ≤ ρb m ^ 2)
    (hsplit : ∀ m, 0 < m → ∀ k, K m ≤ k →
      SplitM (boxSlab μ hN β hβ m k) (boxSlab μ hN β hβ m (k + 1)) (η m k) (δ m k) (rW m k))
    (hh : ∀ m, 0 < m → ∀ k, K m ≤ k → rW m k ^ 2 ≤ ρb m ^ 2)
    (hE : ∀ m, 0 < m → ∀ k, ∑ j ∈ Finset.Ico (K m) k, (η m j * (2 + η m j) + δ m j) ≤ E m) :
    FixedApertureFloor
      (fun m k => (perronKT μ (boxT μ m k) N hN (β m k) (hβ m k).le).boxGap (aZ a₀ k))
      rLat (MassGap.RelativeGap.relValue (fun m => Real.sqrt (ρb m ^ 2 + E m)) (LA a₀) R) K :=
  fixedApertureFloor_wilson_box μ hN hN2 β hβ ha
    (relFloorM_box_of_splits μ hN β hβ hη hδ hb h0 hsplit hh hE) hR hr

#print axioms Joint.pi_nonneg
#print axioms Joint.of_markov
#print axioms jc_kernel
#print axioms Joint.mean_eq
#print axioms Joint.mean_eq₁
#print axioms Joint.nsq_eq₀
#print axioms Joint.nsq_eq₁
#print axioms Joint.total
#print axioms Joint.jc_shift
#print axioms abs_le_of_sq_le_mul
#print axioms dsum_cs
#print axioms dsum_bound
#print axioms dsum_bound₁
#print axioms abs_diff_le
#print axioms abs_diff_le₁
#print axioms abs_diff_le_sq
#print axioms nearFree_mean
#print axioms nearFree_nsq
#print axioms nearFree_jc
#print axioms nearFree_pair
#print axioms corrW_of_nearFree
#print axioms nearFreeRate_zero
#print axioms nearFreeRate_le
#print axioms freeNearRate_lt_one
#print axioms large_of_sup₀
#print axioms large_of_sup₁
#print axioms contrOn_of_nearFree
#print axioms stepCorr_of_corrW
#print axioms sum_obsPush
#print axioms mean_comp
#print axioms nsq_comp
#print axioms ip_comp
#print axioms obsCorr_iff_corrOn
#print axioms obsCorr_maxCorr
#print axioms obs_isometry
#print axioms obs_of_e
#print axioms obsPush_eq_of_e
#print axioms ip_diff_right
#print axioms obs_law_diff
#print axioms obsCorr_step
#print axioms obsCorr_step_back
#print axioms obsLaw_eq_of_exact
#print axioms eta_pos_of_flow
#print axioms drift
#print axioms obsCorr_along_zoom
#print axioms link3_exact
#print axioms le_max_of_sq
#print axioms error_zero_iff
#print axioms fixedObs_of_noBudget
#print axioms refine_step_H
#print axioms refine_step_M
#print axioms boxSlab_rho_le_one
#print axioms relFloorM_box_of_splits
#print axioms fixedApertureFloor_box_of_splits

end MassGap.FineLinks
