import Mathlib

/-!
# Entropy is monotone along a concentrating segment (the deterministic `χ_v ≥ 0`)

Pure, deterministic, algebraic. No probability. Fix probability vectors `r, q` and the straight segment
`p(s) = (1-s)·r + s·q = r + (q-r)·s`. The Shannon entropy `H(p(s)) = ∑ negMulLog(pₖ(s))` is
**non-increasing** in `s ∈ [0,1)` under one start condition:

  `0 ≤ ∑ₖ (qₖ - rₖ) · log rₖ`.

Proof: `d/ds H = -∑ₖ (qₖ - rₖ) log pₖ(s)`, and this is `≤ 0` at every `s` because, termwise,
`(qₖ - rₖ)(log pₖ(s) - log rₖ) = rₖ · xₖ log(1 + s xₖ) ≥ 0` with `xₖ = (qₖ-rₖ)/rₖ`, using the
elementary `x·log(1+sx) ≥ 0`. So the derivative never exceeds its value at `s=0`, which the condition
makes `≤ 0`. Then `H(p(s))` is antitone.

This is the framework-native form of the disorder-susceptibility sign `χ_v = -dH/dβ ≥ 0` (PAPER §8.4):
`r` the start (disordered) spectrum, `q` the ordered limit; the condition holds iff `q` concentrates on
the heavy coordinates of `r`.
-/

namespace MassGap.Majorization

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The straight segment `p(s) = r + (q - r)·s` (so `p(0) = r`, `p(1) = q`).

DERIVED: the `0` and `1` are the endpoints of the segment parameter, not constants of the model — the
definition carries no numeral at all, and `s` ranges over whatever interval the caller supplies. -/
def pseg (r q : ι → ℝ) (k : ι) (s : ℝ) : ℝ := r k + (q k - r k) * s

/-- Shannon entropy along the segment, `H(p(s)) = ∑ₖ negMulLog(pₖ(s))`. -/
noncomputable def Hseg (r q : ι → ℝ) (s : ℝ) : ℝ := ∑ k, Real.negMulLog (pseg r q k s)

/-- Its derivative in `s`: `-∑ₖ (qₖ - rₖ) log pₖ(s)`. -/
noncomputable def D1 (r q : ι → ℝ) (s : ℝ) : ℝ := - ∑ k, (q k - r k) * Real.log (pseg r q k s)

/-- **The elementary inequality.** For `s ≥ 0` and `1 + s·x > 0`, `x · log(1 + s·x) ≥ 0`. -/
theorem mul_log_one_add_nonneg {x s : ℝ} (hs : 0 ≤ s) (h : 0 < 1 + s * x) :
    0 ≤ x * Real.log (1 + s * x) := by
  rcases le_or_gt 0 x with hx | hx
  · exact mul_nonneg hx (Real.log_nonneg (by nlinarith))
  · have hlog : Real.log (1 + s * x) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
    nlinarith [mul_nonneg (neg_nonneg.mpr hx.le) (neg_nonneg.mpr hlog)]

omit [Fintype ι] in
theorem pseg_pos (r q : ι → ℝ) (hr : ∀ k, 0 < r k) (hq : ∀ k, 0 ≤ q k)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (k : ι) : 0 < pseg r q k s := by
  have : pseg r q k s = (1 - s) * r k + s * q k := by unfold pseg; ring
  rw [this]
  have h1 : 0 < (1 - s) * r k := mul_pos (by linarith) (hr k)
  have h2 : 0 ≤ s * q k := mul_nonneg hs0 (hq k)
  linarith

omit [Fintype ι] in
theorem hasDerivAt_pseg (r q : ι → ℝ) (k : ι) (s : ℝ) :
    HasDerivAt (pseg r q k) (q k - r k) s := by
  have h := ((hasDerivAt_id s).const_mul (q k - r k)).const_add (r k)
  rw [mul_one] at h
  exact h

omit [Fintype ι] in
/-- **Termwise concavity step.** `(qₖ - rₖ) log rₖ ≤ (qₖ - rₖ) log pₖ(s)`: moving along the segment
raises `(qₖ-rₖ)·log`. Sign-split on `qₖ` vs `rₖ`, using monotonicity of `log`. -/
theorem term_le (r q : ι → ℝ) (hr : ∀ k, 0 < r k) (hq : ∀ k, 0 ≤ q k)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (k : ι) :
    (q k - r k) * Real.log (r k) ≤ (q k - r k) * Real.log (pseg r q k s) := by
  have hpos := pseg_pos r q hr hq hs0 hs1 k
  rcases le_or_gt (r k) (q k) with hqr | hqr
  · -- q k ≥ r k: `q-r ≥ 0` and `pₖ(s) ≥ rₖ`, so `log` rises.
    have hp : r k ≤ pseg r q k s := by unfold pseg; nlinarith [hs0, hqr]
    have hlog : Real.log (r k) ≤ Real.log (pseg r q k s) := Real.log_le_log (hr k) hp
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ q k - r k)
      (by linarith : (0:ℝ) ≤ Real.log (pseg r q k s) - Real.log (r k))]
  · -- q k < r k: `q-r < 0` and `pₖ(s) ≤ rₖ`, so `log` falls; product flips to `≥ 0`.
    have hp : pseg r q k s ≤ r k := by unfold pseg; nlinarith [hs0, hqr]
    have hlog : Real.log (pseg r q k s) ≤ Real.log (r k) := Real.log_le_log hpos hp
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r k - q k)
      (by linarith : (0:ℝ) ≤ Real.log (r k) - Real.log (pseg r q k s))]

/-- **The derivative is nonpositive** on `[0,1)`, given the start condition. -/
theorem D1_nonpos (r q : ι → ℝ) (hr : ∀ k, 0 < r k) (hq : ∀ k, 0 ≤ q k)
    (hcond : 0 ≤ ∑ k, (q k - r k) * Real.log (r k))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : D1 r q s ≤ 0 := by
  have hsum : ∑ k, (q k - r k) * Real.log (r k)
      ≤ ∑ k, (q k - r k) * Real.log (pseg r q k s) :=
    Finset.sum_le_sum (fun k _ => term_le r q hr hq hs0 hs1 k)
  unfold D1; linarith

theorem hasDerivAt_Hseg (r q : ι → ℝ) (hr : ∀ k, 0 < r k) (hq : ∀ k, 0 ≤ q k)
    (hrs : ∑ k, r k = 1) (hqs : ∑ k, q k = 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : HasDerivAt (Hseg r q) (D1 r q s) s := by
  have hfun : Hseg r q = ∑ k, (fun s => Real.negMulLog (pseg r q k s)) := by
    funext s'; simp only [Hseg, Finset.sum_apply]
  have hraw : HasDerivAt (Hseg r q)
      (∑ k, -((q k - r k) * Real.log (pseg r q k s)
        + pseg r q k s * ((q k - r k) / pseg r q k s))) s := by
    rw [hfun]
    apply HasDerivAt.sum
    intro k _
    have hp := hasDerivAt_pseg r q k s
    have hpos := pseg_pos r q hr hq hs0 hs1 k
    have hmul := hp.mul (hp.log (ne_of_gt hpos))
    have heqf : (fun s => Real.negMulLog (pseg r q k s))
        = (fun s => -(pseg r q k s * Real.log (pseg r q k s))) := by
      funext s'; simp only [Real.negMulLog]; ring
    rw [heqf]; exact hmul.neg
  have hz : ∑ k, (q k - r k) = 0 := by
    rw [Finset.sum_sub_distrib, hqs, hrs, sub_self]
  have heq : (∑ k, -((q k - r k) * Real.log (pseg r q k s)
      + pseg r q k s * ((q k - r k) / pseg r q k s))) = D1 r q s := by
    have hstep : ∀ k, pseg r q k s * ((q k - r k) / pseg r q k s) = q k - r k := by
      intro k
      have hne := ne_of_gt (pseg_pos r q hr hq hs0 hs1 k)
      field_simp
    simp only [hstep]
    unfold D1
    rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    have hterm : ∀ k, -((q k - r k) * Real.log (pseg r q k s) + (q k - r k))
        + (q k - r k) * Real.log (pseg r q k s) = r k - q k := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib, hrs, hqs, sub_self]
  rw [heq] at hraw; exact hraw

/-- **Main theorem.** Under the start condition `0 ≤ ∑ₖ (qₖ - rₖ) log rₖ`, the Shannon entropy along the
segment `p(s) = (1-s)r + s q` is non-increasing on `[0,1)`. Elementary, deterministic, no probability;
the whole content is the one scalar start inequality. -/
theorem entropy_antitone (r q : ι → ℝ) (hr : ∀ k, 0 < r k) (hq : ∀ k, 0 ≤ q k)
    (hrs : ∑ k, r k = 1) (hqs : ∑ k, q k = 1)
    (hcond : 0 ≤ ∑ k, (q k - r k) * Real.log (r k)) :
    AntitoneOn (Hseg r q) (Set.Ico 0 1) := by
  have hcont : Continuous (Hseg r q) := by
    unfold Hseg
    exact continuous_finsetSum _ fun k _ =>
      Real.continuous_negMulLog.comp (by unfold pseg; fun_prop)
  apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1) hcont.continuousOn
  · rw [interior_Ico]
    exact fun x hx =>
      (hasDerivAt_Hseg r q hr hq hrs hqs hx.1.le hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Ico]
    intro x hx
    rw [(hasDerivAt_Hseg r q hr hq hrs hqs hx.1.le hx.2).deriv]
    exact D1_nonpos r q hr hq hcond hx.1.le hx.2

/-! ## The single-cut case: the concentration condition is automatic

When the ordered limit is a single dominant mode `q = e_j` (the leading correlation mode, `r_j` the
heaviest component of the disordered start `r`), the start condition `0 ≤ ∑(q-r)log r` is not an
assumption: it equals `∑_k r_k log(r_j/r_k) ≥ 0`, a divergence, nonnegative because `r_j` is the maximum.
So for the single-cut spectral flow (`ρ'(1) < 1`, one dominant mode), the entropy is monotone with no
extra input. This is the deterministic form of `χ_v ≥ 0`: no probability, no reflection positivity. -/

/-- **The concentration condition holds at the dominant-mode limit.** For a probability vector `r` whose
`j`-th component is maximal, concentrating fully onto mode `j` (`q = e_j`) gives
`0 ≤ ∑_k (e_j - r)_k log r_k = ∑_k r_k log(r_j/r_k)`. Unconditional. -/
theorem concentration_at_dominant [DecidableEq ι] (r : ι → ℝ) (hr : ∀ k, 0 < r k)
    (hrs : ∑ k, r k = 1) (j : ι) (hmax : ∀ k, r k ≤ r j) :
    0 ≤ ∑ k, ((if k = j then (1 : ℝ) else 0) - r k) * Real.log (r k) := by
  have e1 : (∑ k, (if k = j then (1 : ℝ) else 0) * Real.log (r k)) = Real.log (r j) := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : (∑ k, ((if k = j then (1 : ℝ) else 0) - r k) * Real.log (r k))
      = ∑ k, r k * (Real.log (r j) - Real.log (r k)) := by
    calc (∑ k, ((if k = j then (1 : ℝ) else 0) - r k) * Real.log (r k))
        = (∑ k, ((if k = j then (1 : ℝ) else 0) * Real.log (r k) - r k * Real.log (r k))) := by
          apply Finset.sum_congr rfl; intro k _; ring
      _ = (∑ k, (if k = j then (1 : ℝ) else 0) * Real.log (r k)) - ∑ k, r k * Real.log (r k) := by
          rw [Finset.sum_sub_distrib]
      _ = Real.log (r j) - ∑ k, r k * Real.log (r k) := by rw [e1]
      _ = (∑ k, r k) * Real.log (r j) - ∑ k, r k * Real.log (r k) := by rw [hrs, one_mul]
      _ = (∑ k, r k * Real.log (r j)) - ∑ k, r k * Real.log (r k) := by rw [Finset.sum_mul]
      _ = ∑ k, r k * (Real.log (r j) - Real.log (r k)) := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro k _; ring
  rw [key]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hr k).le (by rw [sub_nonneg]; exact Real.log_le_log (hr k) (hmax k))

/-- **Entropy is monotone when concentrating onto the dominant mode.** For a probability vector `r` with
maximal `j`-th component, the Shannon entropy along the segment from `r` to the point mass `e_j` is
non-increasing. Unconditional (the concentration condition is discharged by `concentration_at_dominant`):
this is `χ_v = -dH/dβ ≥ 0` for a single-cut spectral flow, deterministically. -/
theorem entropy_antitone_at_dominant [DecidableEq ι] (r : ι → ℝ) (hr : ∀ k, 0 < r k)
    (hrs : ∑ k, r k = 1) (j : ι) (hmax : ∀ k, r k ≤ r j) :
    AntitoneOn (Hseg r (fun k => if k = j then 1 else 0)) (Set.Ico 0 1) :=
  entropy_antitone r (fun k => if k = j then 1 else 0) hr
    (fun k => by split_ifs <;> norm_num) hrs (by simp) (concentration_at_dominant r hr hrs j hmax)

/-- **Concentration condition, general aligned form.** If `r` is sorted non-increasing on `[0,n)` and the
ordered limit `q` majorizes `r` (partial sums of `q - r` are `≥ 0`, with equal totals), then
`0 ≤ ∑_k (q-r)_k log r_k`. Summation-by-parts turns it into `∑_m D_m · (log r_{m-1} - log r_m)` with
`D_m = ∑_{k<m}(q-r)_k ≥ 0` and `log r_{m-1} - log r_m ≥ 0`. The partial-concentration generalisation of
`concentration_at_dominant` (the point-mass case `q = e_j`). -/
theorem concentration_of_majorizes {n : ℕ} (r q : ℕ → ℝ)
    (hr : ∀ k, k < n → 0 < r k)
    (hsort : ∀ i, i + 1 < n → r (i + 1) ≤ r i)
    (hmaj : ∀ m, 0 ≤ ∑ k ∈ Finset.range m, (q k - r k))
    (htot : ∑ k ∈ Finset.range n, (q k - r k) = 0) :
    0 ≤ ∑ k ∈ Finset.range n, (q k - r k) * Real.log (r k) := by
  have hcomm : (∑ k ∈ Finset.range n, (q k - r k) * Real.log (r k))
      = ∑ k ∈ Finset.range n, Real.log (r k) * (q k - r k) :=
    Finset.sum_congr rfl fun k _ => by ring
  have key := Finset.sum_range_by_parts (fun k => Real.log (r k)) (fun k => q k - r k) (n := n)
  simp only [smul_eq_mul] at key
  rw [hcomm, key, htot, mul_zero, zero_sub, neg_nonneg]
  apply Finset.sum_nonpos
  intro i hi
  rw [Finset.mem_range] at hi
  have hi1 : i + 1 < n := by omega
  have h1 : Real.log (r (i + 1)) - Real.log (r i) ≤ 0 := by
    rw [sub_nonpos]; exact Real.log_le_log (hr (i + 1) hi1) (hsort i hi1)
  nlinarith [mul_nonneg (neg_nonneg.mpr h1) (hmaj (i + 1))]

/-- **Entropy is monotone under any aligned majorizing concentration** (the general Schur-concave form).
For a strictly positive, sorted non-increasing probability vector `r` on `[0,n)` and an ordered limit `q`
(also a probability vector) that majorizes it, the Shannon entropy along the segment `r → q` is
non-increasing on `[0,1)`. This feeds `concentration_of_majorizes` (the start condition, by
summation-by-parts) into `entropy_antitone` (the monotonicity), indexed over `Fin n`. The single dominant
mode `q = e_j` of `entropy_antitone_at_dominant` is the special case; here `q` may spread over several
heavy modes, provided it majorizes `r`. Deterministic, no probability, no reflection positivity. -/
theorem entropy_antitone_of_majorizes {n : ℕ} (r q : ℕ → ℝ)
    (hr : ∀ k, k < n → 0 < r k) (hq : ∀ k, k < n → 0 ≤ q k)
    (hrs : ∑ k ∈ Finset.range n, r k = 1) (hqs : ∑ k ∈ Finset.range n, q k = 1)
    (hsort : ∀ i, i + 1 < n → r (i + 1) ≤ r i)
    (hmaj : ∀ m, 0 ≤ ∑ k ∈ Finset.range m, (q k - r k))
    (htot : ∑ k ∈ Finset.range n, (q k - r k) = 0) :
    AntitoneOn (Hseg (fun k : Fin n => r k.val) (fun k : Fin n => q k.val)) (Set.Ico 0 1) := by
  refine entropy_antitone (fun k : Fin n => r k.val) (fun k : Fin n => q k.val)
    (fun k => hr k.val k.isLt) (fun k => hq k.val k.isLt) ?_ ?_ ?_
  · show ∑ k : Fin n, r k.val = 1
    rw [Fin.sum_univ_eq_sum_range r]; exact hrs
  · show ∑ k : Fin n, q k.val = 1
    rw [Fin.sum_univ_eq_sum_range q]; exact hqs
  · show (0 : ℝ) ≤ ∑ k : Fin n, (q k.val - r k.val) * Real.log (r k.val)
    rw [Fin.sum_univ_eq_sum_range (fun m => (q m - r m) * Real.log (r m))]
    exact concentration_of_majorizes r q hr hsort hmaj htot

#print axioms hasDerivAt_Hseg
#print axioms D1_nonpos
#print axioms entropy_antitone
#print axioms concentration_at_dominant
#print axioms entropy_antitone_at_dominant
#print axioms concentration_of_majorizes
#print axioms entropy_antitone_of_majorizes

end MassGap.Majorization
