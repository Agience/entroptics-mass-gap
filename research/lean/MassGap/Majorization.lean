import Mathlib

/-!
# MassGap.Majorization — Shannon entropy is antitone along a straight segment between two
probability vectors

Fix two functions `r, q : ι → ℝ` on a `Fintype` and the straight segment
`pseg r q k s = r k + (q k - r k) * s`, so the segment runs from `r` at `s = 0` to `q` at `s = 1`.
`Hseg r q s` is the Shannon entropy `∑ k, Real.negMulLog (pseg r q k s)` along it, and `D1 r q s` is
`-∑ k, (q k - r k) * Real.log (pseg r q k s)`.

`entropy_antitone` concludes `AntitoneOn (Hseg r q) (Set.Ico 0 1)` from: `r` strictly positive, `q`
nonnegative, both summing to `1`, and one scalar start condition,

    0 ≤ ∑ k, (q k - r k) * Real.log (r k).

The route is `hasDerivAt_Hseg` (the derivative of `Hseg` is `D1`, the two terms of the product rule
collapsing because `∑ (q k - r k) = 0`), `term_le` (moving along the segment raises
`(q k - r k) * log`, by a sign split on `q k` against `r k`), `D1_nonpos` (summing `term_le`), and
`antitoneOn_of_deriv_nonpos`.

Two families of results discharge the start condition rather than assuming it:
* `concentration_at_dominant` and `entropy_antitone_at_dominant`, where `q` is the point mass at an
  index `j` at which `r` is maximal, and the condition reduces to `∑ k, r k * log (r j / r k) ≥ 0`.
* `concentration_of_majorizes` and `entropy_antitone_of_majorizes`, where `r` is sorted
  non-increasing on `Finset.range n` and `q` majorizes it — all partial sums of `q - r` nonnegative,
  total zero. Summation by parts turns the condition into a sum of nonnegative products.

Scope: the segment is the straight line in the simplex, and antitonicity is stated on `Set.Ico 0 1`,
the half-open interval, since `pseg_pos` needs `s < 1` to keep every coordinate positive. All
statements are about real vectors and sums; no measure, probability space or dynamics appears.
-/

namespace MassGap.Majorization

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The straight segment between two vectors, coordinatewise: `pseg r q k s = r k + (q k - r k) * s`.
At segment parameter zero it is `r k` and at one it is `q k`, but the definition places no
restriction on `s`.

DERIVED: no numeral occurs in the definition. `s` ranges over whatever the caller supplies; the
endpoints are properties of `pseg`, not constants written into it. -/
def pseg (r q : ι → ℝ) (k : ι) (s : ℝ) : ℝ := r k + (q k - r k) * s

/-- Shannon entropy along the segment: `∑ k, Real.negMulLog (pseg r q k s)`, a sum over the whole
`Fintype` index. `Real.negMulLog t` is `-t * log t`, defined at every real `t`, so `Hseg` is total
and does not presuppose that `pseg` is positive.

DERIVED: no numeral occurs. -/
noncomputable def Hseg (r q : ι → ℝ) (s : ℝ) : ℝ := ∑ k, Real.negMulLog (pseg r q k s)

/-- The candidate derivative of `Hseg` in `s`: `-∑ k, (q k - r k) * Real.log (pseg r q k s)`. A
definition; `hasDerivAt_Hseg` is what identifies it with the derivative, and only under the
hypotheses stated there.

DERIVED: no numeral occurs. -/
noncomputable def D1 (r q : ι → ℝ) (s : ℝ) : ℝ := - ∑ k, (q k - r k) * Real.log (pseg r q k s)

/-- For `0 ≤ s` and `0 < 1 + s * x`, the product `x * Real.log (1 + s * x)` is nonnegative. The
proof splits on the sign of `x`: for `0 ≤ x` the logarithm's argument is at least one, so the
logarithm is nonnegative; for `x < 0` it is at most one and positive, so the logarithm is
non-positive and the product of two non-positive factors is nonnegative.

DERIVED: `0` is the lower bound on `s`, the strict lower bound on the logarithm's argument, and the
bound asserted on the product; `1` is the base point of the logarithm's argument `1 + s * x`, the
value at which `Real.log` changes sign. -/
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
/-- Termwise: `(q k - r k) * Real.log (r k) ≤ (q k - r k) * Real.log (pseg r q k s)`, given `r`
strictly positive, `q` nonnegative, `0 ≤ s` and `s < 1`. The proof splits on `r k ≤ q k` against
`q k < r k`. In the first case `pseg` has moved up and the factor is nonnegative; in the second both
have flipped sign, so the product is nonnegative either way. Positivity of `pseg r q k s` comes from
`pseg_pos`, which is where `s < 1` is used.

DERIVED: `0` is the strict lower bound on `r`, the lower bound on `q`, and the lower bound on `s`;
`1` is the strict upper bound on `s`, the endpoint at which a coordinate of `pseg` could reach zero
and the logarithm cease to be monotone-usable. -/
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

/-- `D1 r q s ≤ 0` for `0 ≤ s` and `s < 1`, given `r` strictly positive, `q` nonnegative, and the
start condition `0 ≤ ∑ k, (q k - r k) * Real.log (r k)`. `Finset.sum_le_sum` applied to `term_le`
raises the start-condition sum to the sum at `s`, and `linarith` concludes after unfolding `D1`.

Scope: the start condition is a hypothesis; only the value at `s = 0` is assumed, and the inequality
at every other `s` follows from it.

DERIVED: `0` is the lower bounds on `r`, `q` and `s`, the bound in the start condition, and the
upper bound on `D1`; `1` is the strict upper bound on `s`, inherited from `term_le`. -/
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

/-- `AntitoneOn (Hseg r q) (Set.Ico 0 1)`, given `r` strictly positive, `q` nonnegative, both
summing to `1`, and the start condition `0 ≤ ∑ k, (q k - r k) * Real.log (r k)`. The proof supplies
continuity of `Hseg`, differentiability on `interior (Set.Ico 0 1) = Set.Ioo 0 1` via
`hasDerivAt_Hseg`, and `D1_nonpos` for the sign of the derivative, to
`antitoneOn_of_deriv_nonpos` over `convex_Ico 0 1`.

Scope: the conclusion is on the half-open interval `Set.Ico 0 1`; the endpoint `1`, where a
coordinate of `pseg` may vanish, is excluded. The normalisation hypotheses `hrs` and `hqs` are used
to make `∑ (q k - r k) = 0`, which is what collapses the product rule in `hasDerivAt_Hseg`.

DERIVED: `0` is the strict lower bound on `r`, the lower bound on `q`, the bound in the start
condition, and the left endpoint of the interval; `1` is the common value of both sums, fixing the
vectors to the probability simplex, and the right endpoint of the interval. -/
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

/-! ## Discharging the start condition: a point-mass limit

When `q` is the indicator of a single index `j` at which `r` attains its maximum, the start
condition is provable rather than assumed. The sum `∑ k, (q k - r k) * log (r k)` rearranges to
`∑ k, r k * (log (r j) - log (r k))`, every term of which is nonnegative because `r k ≤ r j`. -/

/-- The start condition at a point-mass limit. For `r` strictly positive with `∑ k, r k = 1`, an
index `j` with `r k ≤ r j` for every `k`, and `q` the indicator `if k = j then 1 else 0`, the
conclusion is `0 ≤ ∑ k, ((if k = j then (1 : ℝ) else 0) - r k) * Real.log (r k)`. The proof
rearranges the sum to `∑ k, r k * (Real.log (r j) - Real.log (r k))`, using `hrs` to replace
`Real.log (r j)` by `(∑ k, r k) * Real.log (r j)`, and concludes by `Finset.sum_nonneg` with
`Real.log_le_log` at `hmax`.

Scope: `hmax` requires `j` to be a maximiser of `r`, not merely a large coordinate. `DecidableEq ι`
is needed for the indicator.

DERIVED: `0` is the strict lower bound on `r`, the off-index value of the indicator, and the bound
asserted on the sum; `1` is the total mass of `r` and the on-index value of the indicator, so the
indicator is a probability vector too. -/
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

/-- `AntitoneOn (Hseg r (fun k => if k = j then 1 else 0)) (Set.Ico 0 1)`, for `r` strictly positive
with total mass `1` and `j` a maximiser of `r`. `entropy_antitone` with the indicator as `q`: its
nonnegativity is `split_ifs`, its total mass is `simp`, and its start condition is
`concentration_at_dominant`. No start condition is left for the caller.

DERIVED: `0` is the strict lower bound on `r`, the off-index value of the indicator, and the left
endpoint of the interval; `1` is the total mass of `r`, the on-index value of the indicator, and the
right endpoint of the interval. -/
theorem entropy_antitone_at_dominant [DecidableEq ι] (r : ι → ℝ) (hr : ∀ k, 0 < r k)
    (hrs : ∑ k, r k = 1) (j : ι) (hmax : ∀ k, r k ≤ r j) :
    AntitoneOn (Hseg r (fun k => if k = j then 1 else 0)) (Set.Ico 0 1) :=
  entropy_antitone r (fun k => if k = j then 1 else 0) hr
    (fun k => by split_ifs <;> norm_num) hrs (by simp) (concentration_at_dominant r hr hrs j hmax)

/-- The start condition from a majorization hypothesis. For `r q : ℕ → ℝ` with `r` strictly
positive and sorted non-increasing on `Finset.range n`, all partial sums `∑ k ∈ range m, (q k - r k)`
nonnegative, and total `∑ k ∈ range n, (q k - r k) = 0`, the conclusion is
`0 ≤ ∑ k ∈ range n, (q k - r k) * Real.log (r k)`. `Finset.sum_range_by_parts` converts the sum into
the boundary term, which `htot` kills, minus a sum of products of a partial sum with a logarithm
increment; each such product is non-positive because `r` is sorted, so the negated sum is
nonnegative.

Scope: `hmaj` is required at every `m : ℕ`, not only for `m ≤ n`. `hsort` is a consecutive
comparison, which gives the monotone ordering across `range n` by transitivity in the proof.

DERIVED: `0` is the strict lower bound on `r`, the bound on every partial sum, the value of the
total, and the bound asserted on the conclusion; `1` is the step between consecutive indices in
`hsort` and in the summation-by-parts increments. -/
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

/-- Antitonicity under a majorization hypothesis. For `r q : ℕ → ℝ` with `r` strictly positive and
`q` nonnegative below `n`, both summing to `1` over `Finset.range n`, `r` sorted non-increasing, all
partial sums of `q - r` nonnegative and their total zero, the conclusion is
`AntitoneOn (Hseg (fun k : Fin n => r k.val) (fun k : Fin n => q k.val)) (Set.Ico 0 1)`.
`entropy_antitone` over the index type `Fin n`, with the three `Fin n` sums converted to
`Finset.range n` sums by `Fin.sum_univ_eq_sum_range` and the start condition supplied by
`concentration_of_majorizes`.

Scope: the conclusion is about the restrictions of `r` and `q` to `Fin n`; values at indices `≥ n`
are unconstrained by `hr` and `hq` and do not enter `Hseg`. The interval is again half-open.

DERIVED: `0` is the strict lower bound on `r`, the lower bound on `q`, the bound on the partial
sums, the value of the total, and the left endpoint of the interval; `1` is the common total mass of
`r` and `q`, the consecutive-index step in `hsort`, and the right endpoint of the interval. -/
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
