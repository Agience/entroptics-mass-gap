import Mathlib
import MassGap.BareRatioProof

/-!
# MassGap.PlaqSummable — what the tree gives toward relative summability of the plaquette correlator

`PlaqShortDistance` (named here, not imported) leaves one inequality of `SplitRatio`: at zero momentum, `∑_z C_k(z) ≤ K ν_k(cv_l A_l)`,
the bare symmetrized plaquette correlator summed over the screen box at most a fixed multiple of one link's
conditional variance of the local reading, eventually along `schedSU N` (`β_k = dyBeta k → ∞`), one `K`. This
module proves two state-level facts that hold at every coupling, splits the inequality into a short-distance part
(proved, with a constant free of `β`) and a tail (open), and records which decorrelation tools of the tree give a
bound relative to the variance and which degrade as `β` grows. Declarations are in the namespace
`MassGap.PlaqSummable`.

Throughout, `ν` is a `DLRLimit.State` on a compact space, `var ν h = ν(h²) − ν(h)²`, and for a weight `w` with
`A ≤ w ≤ B`, `0 < A`, the tilted state reads `h ↦ ν(w h)/ν(w)` with variance `tvar ν w h`.

## 1. A bounded tilt moves a variance ratio by at most `(B/A)²` (proved)

`shift_expand`: `ν(f (h − c)²) = ν(f h²) − 2c ν(f h) + c² ν(f)`. `tilt_shift`: `ν(w (h − c)²) =
ν(w)(tvar + (tmean − c)²)`; `var_shift`: `ν((h − c)²) = var + (ν h − c)²`. `tvar_nonneg`.

`tvar_le`: `tvar ν w h ≤ (B/A) var ν h`. `var_le_tvar`: `var ν h ≤ (B/A) tvar ν w h`. `relVar_transfer`: if
`var ν G ≤ K var ν H` with `K ≥ 0`, then `tvar ν w G ≤ (B/A)² K tvar ν w H`. With `w = e^{−V}`, `B/A = e^{osc V}`:
this is the Holley–Stroock transfer of a relative bound (covariance sum against a local variance), in the form a
comparison with a Gaussian reference would use. The factor is the exponential of the sup-norm oscillation.

## 2. The short-distance part of the row sum is free of the coupling (proved)

`abs_state_mul_le`: `|ν(f g)| ≤ (ν(f²) + ν(g²))/2` for every state. `opNorm_of_shortTail`: for readings `P_x` on a
finite index set with `ν(P_y²) ≤ d`, neighbourhoods `near x` of at most `n` points and tail row sums
`∑_{y ∉ near x} |ν(P_x P_y)| ≤ τ`, the bare covariance has operator norm at most `n d + τ` (through
`BareRatioProof.schur_rowSum`). `ratio_of_shortTail`: if also `d ≤ κ F` and `τ ≤ κ' F` for a floor `F`, some
`c ≥ 0` bounds the operator norm with `c ≤ (n κ + κ') F`. At `F = splitFloor` of a sparse split this is the shape of
`SplitRatio`'s last clause with `Q' = n κ + κ'`. The short part (`|z| ≤ R`, `n` the ball count) costs `n`, at every
coupling and every state; no decorrelation enters it.

## 3. The candidates, read for a bound relative to the variance uniform in `β`

Argued from the module headers named; none of these is formalized here.

* `BoxGapHS` (Holley–Stroock): `link_action_osc` gives `24β` per link; on a box the oscillation is extensive,
  `~ 10⁶ β` at side `15`. The factor of §1 is `e^{2 osc}`, which grows with `β` and with the box. Strong coupling only.
* `BoxGapBE`, `BoxGap` (pair defects), `PairCorr`: defect `Δ(β)` grows with `β`; reach `β ≈ 0.08` (`SU(2)`),
  `≈ 0.19` (`SU(3)`). `FibrePerturb`: factor `e^ε (c + 2(e^ε − 1))` with `ε ~ β`. Both absolute in `β`.
* `BoxDobrushin`, `DSBoxFloor`, `OneCubeBridge` (Dobrushin–Shlosman, influence): Wilson pair influence `~ 4β`, row
  sum below `1` only at `β ≤ 1/40`. After gauge fixing at large `β` the Gaussian is massless and the box influence
  is `1` at every side (`DSBoxFloor` Gaussian unit; the flat-field filter of `OneCubeBridge`): it fails for every
  `β`, not only as `β` grows. Influence bounds control absolute discrepancies; they do not read a ratio.
* `CondGap` §6 (Bakry–Émery): curvature `N/4 − βH → −∞`. In Lie-algebra coordinates `A = √β log U` after a
  maximal-tree gauge on the box, the Hessian is `M + O(|A|/√β)` on the small-field set, `M` the gauge-fixed box
  Laplacian; Brascamp–Lieb would then bound `Var(∑ P_x)` by the free quantity times `(1 − O(R/√β))⁻¹` with no
  extensive factor. It needs convexity off the small-field set, which fails (compact group, `U_p` near `−1`), and
  `CondGap` cites Brascamp–Lieb without formalizing it.
* `ChiForest`: variance-relative increments `δ_k √Var_k`, given `χ²` summability along a forest, which is a
  hypothesis, not a bound.
* `HeatBathLocal`: locality and ergodicity at every extent, with no rate free of the extent.

## 4. The paper test of the Gaussian comparison

Argued, not formalized.

* Free field: `C(z) ~ |z|^{−8}`, `C(z)/C(0)` free of the coupling (`BareRatioProof` §5); `∑_z C(z) ≤ K₀ C(0)` and,
  with the per-link floor `ν(cv_l A_l) ≥ κ C(0)` at Gaussian order (`PlaqShortDistance` §5), the inequality holds.
* Perturbation after a maximal-tree gauge on a box of side `n`: `S = ½⟨A, M A⟩ + β^{−1/2} V₃ + β^{−1} V₄ + …`. On
  `|A_l| ≤ R` the oscillation is `≤ c n⁴ (R³/√β + R⁴/β)`, so of order `n⁴/√β`. Two obstructions to §1 with this
  `V`: (a) in sup norm over the compact group the oscillation is the full action range, `~ β n⁴`, so the small-field
  restriction needs a large-field bound (`e^{−cβε²}` per plaquette) that §1 does not supply; (b) the box is the
  screen box, side `L_k = ⌈ρ/a_k⌉`, and `a_k = aRun N 1 / 2^{k+1}` along `dyBeta`, while `β_k` grows like `k`; so
  even on the small-field set the oscillation is `~ 2^{4k}/√k → ∞`, and `e^{2 osc}` is unbounded along the tower.
  The cubic and quartic terms are small in units of the variance per plaquette, not summed over the box.
* What remains after §2: the tail `∑_{R < |z| ≤ L_k} C_k(z) ≤ κ' C_k(0)` for one `R`, uniformly in `k`. It reads
  every scale between `R` and `L_k`, a number of scales growing like `k`; a single-scale comparison loses a factor
  per scale. Controlling it with one constant is the multiscale small-field/large-field analysis of Bałaban's
  renormalization group for the Wilson measure (cited, not in the tree): Gaussian domination with
  running-coupling corrections at each block scale and large-field suppression.

## What does not follow

* `SplitRatio`'s last clause is not proved along any tower; `ratio_of_shortTail` reduces it to two hypotheses.
* The missing inequalities are exactly: (i) the tail `τ_k ≤ κ' F_k` with `τ_k` the row sum of
  `|ν_k(P_x P_y)|` over `y` beyond distance `R` in the screen box and `F_k` the split floor, one `κ'` eventually;
  (ii) the diagonal against the floor, `ν_k(P_y²) ≤ κ F_k` (the per-link floor of `PlaqShortDistance`).
* No `SparseSplit` of the lowest-mode field is built here, and `ratio_of_shortTail` is not instantiated at
  `schedSU N`.
* §1 does not give a bound uniform in `β` for any Wilson perturbation in the tree: its factor is the exponential of
  a sup-norm oscillation, extensive in the box.
* Brascamp–Lieb, Helffer–Sjöstrand and Bałaban's renormalization group are cited only.

Foundational footprint only (`#print axioms` after each section).

DERIVED (module-wide): `0` the signs; `1` the unit observable; `2` the squares, the cross term `2c` and the AM–GM
halving. `R`, `κ`, `κ'`, `c`, the exponents and `10⁶` appear only in the argued text; `A`, `B`, `K`, `n`, `d`, `τ`,
`F` are hypotheses. The values `24β`, `0.08`, `0.19`, `1/40`, `4β`, `N/4`, `aRun N 1 / 2^{k+1}` are Inherited from
the modules named beside them.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.PlaqSummable

open Finset
open MassGap.DLRLimit (State)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ## 1. A bounded tilt moves a variance ratio by at most `(B/A)²` -/

section Tilt

/-- **The variance under a state**: `ν(h²) − ν(h)²`. DERIVED: `2` the square. -/
def var (ν : State X) (h : C(X, ℝ)) : ℝ := ν (h * h) - ν h ^ 2

/-- **The tilted mean**: `ν(w h)/ν(w)`. DERIVED: no numeral. -/
def tmean (ν : State X) (w h : C(X, ℝ)) : ℝ := ν (w * h) / ν w

/-- **The tilted variance**: `ν(w h²)/ν(w) − (ν(w h)/ν(w))²`. DERIVED: `2` the square. -/
def tvar (ν : State X) (w h : C(X, ℝ)) : ℝ := ν (w * h * h) / ν w - tmean ν w h ^ 2

/-- **A shifted square, expanded**: `ν(f (h − c)²) = ν(f h²) − 2c ν(f h) + c² ν(f)`. DERIVED: `2` the square and
the cross term. -/
theorem shift_expand (ν : State X) (f h : C(X, ℝ)) (c : ℝ) :
    ν (f * ((h - c • 1) * (h - c • 1))) = ν (f * h * h) - 2 * c * ν (f * h) + c ^ 2 * ν f := by
  have e : f * ((h - c • 1) * (h - c • 1)) = f * h * h - (2 * c) • (f * h) + (c ^ 2) • f := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [e, ν.map_add, ν.map_sub, ν.map_smul, ν.map_smul]

omit [CompactSpace X] in
/-- A shifted square is non-negative pointwise. DERIVED: `0` the sign. -/
theorem sqShift_nonneg (h : C(X, ℝ)) (c : ℝ) (x : X) : 0 ≤ ((h - c • 1) * (h - c • 1)) x := by
  rw [ContinuousMap.mul_apply]
  exact mul_self_nonneg _

/-- A pointwise lower bound passes to the state. DERIVED: `1` the unit observable. -/
theorem le_state (ν : State X) {w : C(X, ℝ)} {A : ℝ} (hA : ∀ x, A ≤ w x) : A ≤ ν w := by
  have h := ν.nonneg (w - A • 1) (fun x => by
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
      mul_one]
    linarith [hA x])
  rw [ν.map_sub, ν.map_smul, ν.map_one] at h
  linarith

/-- A pointwise upper bound passes to the state. DERIVED: `1` the unit observable. -/
theorem state_le (ν : State X) {w : C(X, ℝ)} {B : ℝ} (hB : ∀ x, w x ≤ B) : ν w ≤ B := by
  have h := ν.nonneg (B • 1 - w) (fun x => by
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
      mul_one]
    linarith [hB x])
  rw [ν.map_sub, ν.map_smul, ν.map_one] at h
  linarith

/-- **A weight bounded above**: `ν(w q) ≤ B ν(q)` for `w ≤ B` and `q ≥ 0`. DERIVED: `1` the unit observable. -/
theorem state_mul_le (ν : State X) {w q : C(X, ℝ)} {B : ℝ} (hB : ∀ x, w x ≤ B) (hq : ∀ x, 0 ≤ q x) :
    ν (w * q) ≤ B * ν q := by
  have h := ν.nonneg ((B • 1 - w) * q) (fun x => by
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact mul_nonneg (by linarith [hB x]) (hq x))
  have e : (B • 1 - w) * q = B • q - w * q := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [e, ν.map_sub, ν.map_smul] at h
  linarith

/-- **A weight bounded below**: `A ν(q) ≤ ν(w q)` for `A ≤ w` and `q ≥ 0`. DERIVED: `1` the unit observable. -/
theorem le_state_mul (ν : State X) {w q : C(X, ℝ)} {A : ℝ} (hA : ∀ x, A ≤ w x) (hq : ∀ x, 0 ≤ q x) :
    A * ν q ≤ ν (w * q) := by
  have h := ν.nonneg ((w - A • 1) * q) (fun x => by
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact mul_nonneg (by linarith [hA x]) (hq x))
  have e : (w - A • 1) * q = w * q - A • q := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul]
    ring
  rw [e, ν.map_sub, ν.map_smul] at h
  linarith

/-- **The tilted shifted square**: `ν(w (h − c)²) = ν(w)(tvar + (tmean − c)²)` when `ν(w) ≠ 0`. DERIVED: `2` the
squares. -/
theorem tilt_shift (ν : State X) (w h : C(X, ℝ)) (c : ℝ) (hZ : ν w ≠ 0) :
    ν (w * ((h - c • 1) * (h - c • 1))) = ν w * (tvar ν w h + (tmean ν w h - c) ^ 2) := by
  rw [shift_expand, tvar, tmean]
  field_simp
  ring

/-- **The shifted square**: `ν((h − c)²) = var + (ν h − c)²`. DERIVED: `2` the squares. -/
theorem var_shift (ν : State X) (h : C(X, ℝ)) (c : ℝ) :
    ν ((h - c • 1) * (h - c • 1)) = var ν h + (ν h - c) ^ 2 := by
  have e := shift_expand ν 1 h c
  simp only [one_mul, ν.map_one] at e
  rw [e, var]
  ring

/-- **The tilted variance is non-negative** for a positive weight. DERIVED: `0` the signs. -/
theorem tvar_nonneg (ν : State X) {w : C(X, ℝ)} {A : ℝ} (hApos : 0 < A) (hA : ∀ x, A ≤ w x) (h : C(X, ℝ)) :
    0 ≤ tvar ν w h := by
  have hZ : 0 < ν w := lt_of_lt_of_le hApos (le_state ν hA)
  have e := tilt_shift ν w h (tmean ν w h) hZ.ne'
  rw [sub_self, sq (0 : ℝ), mul_zero, add_zero] at e
  have h0 : 0 ≤ ν (w * ((h - tmean ν w h • 1) * (h - tmean ν w h • 1))) :=
    ν.nonneg _ fun x => by
      rw [ContinuousMap.mul_apply]
      exact mul_nonneg (by linarith [hA x]) (sqShift_nonneg h _ x)
  rw [e] at h0
  exact nonneg_of_mul_nonneg_right (by linarith) hZ

/-- **The tilted variance is at most `B/A` times the variance**, for `0 < A ≤ w ≤ B`. DERIVED: `2` the square. -/
theorem tvar_le (ν : State X) {w : C(X, ℝ)} {A B : ℝ} (hApos : 0 < A) (hA : ∀ x, A ≤ w x)
    (hB : ∀ x, w x ≤ B) (h : C(X, ℝ)) : tvar ν w h ≤ B / A * var ν h := by
  have hZA := le_state ν hA
  have hZ : 0 < ν w := lt_of_lt_of_le hApos hZA
  have ht := tvar_nonneg ν hApos hA h
  have e := tilt_shift ν w h (ν h) hZ.ne'
  have hup := state_mul_le ν hB (sqShift_nonneg h (ν h))
  rw [var_shift, sub_self, sq (0 : ℝ), mul_zero, add_zero] at hup
  rw [e] at hup
  have h1 : A * tvar ν w h ≤ ν w * tvar ν w h := mul_le_mul_of_nonneg_right hZA ht
  have h2 : 0 ≤ ν w * (tmean ν w h - ν h) ^ 2 := mul_nonneg hZ.le (sq_nonneg _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hApos]
  nlinarith

/-- **The variance is at most `B/A` times the tilted variance**, for `0 < A ≤ w ≤ B`. DERIVED: `2` the square. -/
theorem var_le_tvar (ν : State X) {w : C(X, ℝ)} {A B : ℝ} (hApos : 0 < A) (hA : ∀ x, A ≤ w x)
    (hB : ∀ x, w x ≤ B) (h : C(X, ℝ)) : var ν h ≤ B / A * tvar ν w h := by
  have hZ : 0 < ν w := lt_of_lt_of_le hApos (le_state ν hA)
  have hZB := state_le ν hB
  have ht := tvar_nonneg ν hApos hA h
  have e := tilt_shift ν w h (tmean ν w h) hZ.ne'
  rw [sub_self, sq (0 : ℝ), mul_zero, add_zero] at e
  have hlo := le_state_mul ν hA (sqShift_nonneg h (tmean ν w h))
  rw [e, var_shift] at hlo
  have h1 : ν w * tvar ν w h ≤ B * tvar ν w h := mul_le_mul_of_nonneg_right hZB ht
  have h2 : 0 ≤ A * (ν h - tmean ν w h) ^ 2 := mul_nonneg hApos.le (sq_nonneg _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hApos]
  nlinarith

/-- **A relative bound survives a bounded tilt with the factor `(B/A)²`**: if `var ν G ≤ K var ν H` with
`K ≥ 0`, then `tvar ν w G ≤ (B/A)² K tvar ν w H` for `0 < A ≤ w ≤ B`. DERIVED: `2` the square of the factor. -/
theorem relVar_transfer (ν : State X) {w G H : C(X, ℝ)} {A B K : ℝ} (hApos : 0 < A) (hA : ∀ x, A ≤ w x)
    (hB : ∀ x, w x ≤ B) (hK : 0 ≤ K) (hGH : var ν G ≤ K * var ν H) :
    tvar ν w G ≤ (B / A) ^ 2 * K * tvar ν w H := by
  have hBA : 0 ≤ B / A :=
    div_nonneg ((hApos.le.trans (le_state ν hA)).trans (state_le ν hB)) hApos.le
  have h1 := tvar_le ν hApos hA hB G
  have h2 := var_le_tvar ν hApos hA hB H
  calc tvar ν w G ≤ B / A * var ν G := h1
    _ ≤ B / A * (K * var ν H) := mul_le_mul_of_nonneg_left hGH hBA
    _ ≤ B / A * (K * (B / A * tvar ν w H)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hK) hBA
    _ = (B / A) ^ 2 * K * tvar ν w H := by ring

end Tilt

#print axioms var
#print axioms tmean
#print axioms tvar
#print axioms shift_expand
#print axioms sqShift_nonneg
#print axioms le_state
#print axioms state_le
#print axioms state_mul_le
#print axioms le_state_mul
#print axioms tilt_shift
#print axioms var_shift
#print axioms tvar_nonneg
#print axioms tvar_le
#print axioms var_le_tvar
#print axioms relVar_transfer

/-! ## 2. The short-distance part of the row sum is free of the coupling -/

section ShortTail

/-- **An entry is at most the mean of its diagonals**: `|ν(f g)| ≤ (ν(f²) + ν(g²))/2`, from `ν((f ∓ g)²) ≥ 0`.
DERIVED: `2` the squares and the halving. -/
theorem abs_state_mul_le (ν : State X) (f g : C(X, ℝ)) :
    |ν (f * g)| ≤ (ν (f * f) + ν (g * g)) / 2 := by
  have h1 := ν.nonneg ((f - g) * (f - g)) (fun x => mul_self_nonneg _)
  have h2 := ν.nonneg ((f + g) * (f + g)) (fun x => mul_self_nonneg _)
  have e1 : (f - g) * (f - g) = f * f - (2 : ℝ) • (f * g) + g * g := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.add_apply, smul_eq_mul]
    ring
  have e2 : (f + g) * (f + g) = f * f + (2 : ℝ) • (f * g) + g * g := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul]
    ring
  rw [e1, ν.map_add, ν.map_sub, ν.map_smul] at h1
  rw [e2, ν.map_add, ν.map_add, ν.map_smul] at h2
  rw [abs_le]
  constructor <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The operator norm from a short part and a tail**: with `ν(P_y²) ≤ d`, neighbourhoods of at most `n` points
and tail row sums at most `τ`, `ν((∑ u_x P_x)²) ≤ (n d + τ) ∑ u_x²`. DERIVED: `2` the squares. -/
theorem opNorm_of_shortTail (ν : State X) (P : ι → C(X, ℝ)) (near : ι → Finset ι) {n : ℕ} {d τ : ℝ}
    (hd : ∀ y, ν (P y * P y) ≤ d) (hn : ∀ x, (near x).card ≤ n)
    (hτ : ∀ x, ∑ y ∈ univ.filter (fun y => y ∉ near x), |ν (P x * P y)| ≤ τ) (u : ι → ℝ) :
    ν ((∑ x, u x • P x) ^ 2) ≤ (n * d + τ) * ∑ x, u x ^ 2 := by
  refine MassGap.BareRatioProof.schur_rowSum ν P (fun x => ?_) u
  have hd0 : 0 ≤ d := (ν.nonneg (P x * P x) fun z => mul_self_nonneg (P x z)).trans (hd x)
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset ι) (fun y => y ∈ near x)
    (fun y => |ν (P x * P y)|)
  have hentry : ∀ y ∈ univ.filter (fun y => y ∈ near x), |ν (P x * P y)| ≤ d := fun y _ =>
    (abs_state_mul_le ν (P x) (P y)).trans (by linarith [hd x, hd y])
  have hshort := Finset.sum_le_card_nsmul _ _ d hentry
  have hcard : (univ.filter (fun y => y ∈ near x)).card ≤ n :=
    (Finset.card_le_card fun y hy => (Finset.mem_filter.mp hy).2).trans (hn x)
  have hcard' : ((univ.filter (fun y => y ∈ near x)).card : ℝ) * d ≤ n * d :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hd0
  rw [nsmul_eq_mul] at hshort
  linarith [hτ x]

/-- **The ratio from a short part and a tail**: if moreover `d ≤ κ F` and `τ ≤ κ' F`, with `0 ≤ d`, `0 ≤ τ`, some
`c ≥ 0` bounds the bare covariance in operator norm and `c ≤ (n κ + κ') F`. DERIVED: `2` the squares; `0` the
signs. -/
theorem ratio_of_shortTail (ν : State X) (P : ι → C(X, ℝ)) (near : ι → Finset ι) {n : ℕ} {d τ F κ κ' : ℝ}
    (hd : ∀ y, ν (P y * P y) ≤ d) (hn : ∀ x, (near x).card ≤ n)
    (hτ : ∀ x, ∑ y ∈ univ.filter (fun y => y ∉ near x), |ν (P x * P y)| ≤ τ)
    (hd0 : 0 ≤ d) (hτ0 : 0 ≤ τ) (hdF : d ≤ κ * F) (hτF : τ ≤ κ' * F) :
    ∃ c : ℝ, 0 ≤ c ∧ (∀ u : ι → ℝ, ν ((∑ x, u x • P x) ^ 2) ≤ c * ∑ x, u x ^ 2) ∧
      c ≤ (n * κ + κ') * F := by
  refine ⟨n * d + τ, add_nonneg (mul_nonneg (Nat.cast_nonneg n) hd0) hτ0, opNorm_of_shortTail ν P near hd hn hτ, ?_⟩
  have h1 : (n : ℝ) * d ≤ n * (κ * F) := mul_le_mul_of_nonneg_left hdF (Nat.cast_nonneg n)
  nlinarith

end ShortTail

#print axioms abs_state_mul_le
#print axioms opNorm_of_shortTail
#print axioms ratio_of_shortTail

end MassGap.PlaqSummable

end
