import Mathlib
import MassGap.BasinGrowth

/-!
# MassGap.LevelRate — the coupling rate of a doubling defect is a level rate times a Shannon count

`BasinGrowth.RelLip` asks `|∂_β D| ≤ K D log(1/D)` in the basin `D ≤ 1/1000`, uniformly in the window. Along one
direction the window defect is built from directional defects (`DefectBound.Dw_succ_eq`:
`D(w+1) = 8P₀ + 4P₁ + 2P₂ + P₃`), and each directional defect is `log` of the Rényi-2 count of a transfer spectrum at
the window time (`CountDoubling`, `DefectBound.stepD_eq`). This module computes the `β`-derivative of such a defect on
a finite positive spectrum exactly, and splits the relative bound into two reads of different kind: a rate of the
levels in `β`, which sees no time, and a Shannon count of the excited levels at the window time, which sees no `β`
rate. Declarations are in the namespace `MassGap.LevelRate`.

Setting. `t` a finite family of levels with top `i₀ ∈ t`; `g i β ≥ 0` the gap of level `i` to the top at coupling `β`
(`g i₀ = 0`), so the transfer levels are `λ_i = λ₀ e^{−g_i}`. At time `m ≥ 0`, `z_i = e^{−m g_i}` (`z_{i₀} = 1`).

* `tr m β = Σ_i e^{−m g_i}`, the trace normalized by the top; `exc m β = Σ_{i ≠ i₀} e^{−m g_i}` the excited weight `s`;
  `tr_eq`: `tr = 1 + exc`.
* `pdef m β = 2 log tr(m) − log tr(2m)`, the defect. `pdef_shift`: it is `2 log a(m) − log a(2m)` for the raw trace
  `a(k) = Σ e^{−k(E₀ + g_i)}` at every top energy `E₀`, so it is `DoublingPower.defect` of that trace.
* `ent m β = Σ_i e^{−m g_i} · m g_i = Σ_i z_i log(1/z_i)`, the Shannon read of the levels at time `m`.

## 1. The exact derivative (proved)

* `hasDerivAt_tr`: `∂_β tr(k) = −k Σ_i e^{−k g_i} ∂_β g_i`.
* `hasDerivAt_pdef`: `∂_β pdef = 2 ∂tr(m)/tr(m) − ∂tr(2m)/tr(2m)`. With `q_i(k) = e^{−k g_i}/tr(k)` this is
  `2m Σ_i (q_i(2m) − q_i(m)) ∂_β g_i`: the Hellmann–Feynman form, read on the trace, with no eigenvector.

## 2. The rate bound (proved)

`LevelLip t g Λ β`: `|∂_β g_i| ≤ Λ g_i` at every level (the top has `g′ = 0`), `Λ ≥ 0`: the relative rate of every
gap in `β`.

* `abs_deriv_tr_le`: `|∂tr(k)| ≤ Λ ent(k)` (`k ≥ 0`).
* `ent_double_le`: `ent(2m) ≤ 2 ent(m)`.
* `abs_deriv_pdef_le`: `|∂_β pdef| ≤ 4Λ ent(m)`. `4 = 2 · 2`: the doubled time of `log tr(m)²` and the two terms,
  the second at most the first by `ent_double_le`.

## 3. The Shannon split of the read (proved)

* `ent_eq_excited`: the top contributes nothing, `ent = Σ_{i ≠ i₀} z_i log(1/z_i)`.
* `ent_eq_shannon`: for `s = exc m β > 0` and `π_i = z_i/s`, `ent = s log(1/s) + s · H(π)` with
  `H(π) = Σ π_i log(1/π_i)` the Shannon entropy of the excited distribution at time `m`. So `ent ≤ (1 + C) s log(1/s)`
  (`CountRead`) is exactly `H(π) ≤ C log(1/s)` (`countRead_of_shannon`): the Shannon count `e^H` of occupied excited
  levels at the window time is at most `(1/s)^C`.
* `shannon_uniform`: `k` equal excited levels have `H = log k`. With `log k` comparable to `log(1/s)` the read
  `ent` is not a bounded multiple of `s log(1/s)`: the count is load-bearing.
* `top_share_double_le`: the share `z₁/Σ z` of the top excited level does not fall when the time doubles,
  `z₁/Σz ≤ z₁²/Σz²`. It is a ratio, so it does not see the scale. It is a lower bound on the min-entropy share and
  bounds no Shannon count from above (the rest of the weight may spread), and it compares one operator only: across
  a transverse doubling the slice and its levels change, as in `CountDoubling` §4.

## 4. The defect against its excited weight (proved)

* `log_one_add_exc_le`: `log(1 + s) ≤ pdef` (`m ≥ 0`): purity, `exc(2m) ≤ exc(m)`.
* `exc_le_two_pdef`: `s ≤ 2 pdef` when `pdef < 1` and `pdef ≤ 1/2` (`e^p − 1 ≤ p/(1−p) ≤ 2p`).
* `negMulLog_le_of_le`: `x log(1/x) ≤ y log(1/y)` for `0 ≤ x ≤ y ≤ e^{−1}`. Proof: `log(y/x) ≤ y/x − 1` and
  `log(1/y) ≥ 1`.

## 5. The relative bound (proved)

* `axis_relLip`: `LevelLip Λ`, `CountRead C` (`C ≥ −1`) and `pdef ≤ 1/1000` (the basin seed; DERIVED: `1000` inherited from `DoublingSharp.rec_sharp`) give
  `|∂_β pdef| ≤ 8Λ(1 + C) · pdef · log(1/pdef)`. `8 = 4 · 2`: the `4` of §2 and the `2` of `exc_le_two_pdef`.
* `window_relLip`: four directional defects `P_i ≥ 0` with `|P_i′| ≤ K P_i log(1/P_i)` and `D = 8P₀ + 4P₁ + 2P₂ + P₃`
  at most `e^{−1}` (which the basin `D ≤ 1/1000` meets, `two_seed_le`) give
  `|8P₀′ + 4P₁′ + 2P₂′ + P₃′| ≤ 15K D log(1/D)`, `15 = 8 + 4 + 2 + 1`. This is the shape of
  `BasinGrowth.RelLip` at window `w + 1`.

## The remaining inequality

On a spectral reading of the four step slices, `BasinGrowth.RelLip N β₀ K` follows with `K = 120 Λ (1 + C)` from two
statements, uniform in the window `w` and in `β ≥ β₀` inside the basin:

* (L) `LevelLip`: `|∂_β g_i| ≤ Λ g_i` for every excited level `i` of every step slice transfer operator, `g_i` the
  gap `log(λ₀/λ_i)` in lattice units at the slice of side `2^w`.
* (Cnt) `CountRead`: `H(π) ≤ C log(1/s)` for the excited distribution of the slice at the window time `2^{w+1}`.

(L) is the beta function restated as a relative level rate. At the lightest level it is `|∂_β log m(β)| ≤ Λ` for the
lattice mass `m = g₁` of the slice: a bounded lattice beta function, read level by level. It is `BasinGrowth.RelLip` with the window removed, not a consequence of it or of
anything here; on `D = e^{−m 2^w}` the two are the same statement (`BasinGrowth.expFamily_bound_iff`). (Cnt) is a
read of a different kind: a count of levels at one coupling, with no `β`-derivative, of the kind `ApertureCount.ApertureCountAt` (H3)
carries and `FreeLevels` proves for the free flowed spectrum.

## Why (L) is not provable from the tree (argued)

Every structural input the tree has for the Wilson torus (reflection positivity and the chessboard bound `D ≥ 0`,
convexity of `log Z` in `β` (`GapPersist.logZ_wilson_convex`), the exact block structure of `16` tori of side `n` in
one of side `2n`, purity squaring (`DoublingSharp.rec_sharp`), and the count monotonicity
`CountDoubling.count2_double_le`) holds for every compact gauge group, `U(1)` included (`DefectBound.count_tests`,
`StallRigid.instGaugeGroupCircle`). For `U(1)` in four dimensions (L) is expected to fail at the transition into the
Coulomb phase, where the lightest gap closes or jumps. If it does, no combination of those inputs gives (L) (argued,
not proved): a proof has to read a property
of `SU(N)` that `U(1)` lacks (asymptotic freedom, a non-abelian centre, or the absence of a massless phase). The
`U(1)` failure is argued (`BasinGrowth` §5), not proved.

## What does not follow

* No theorem here is about the Wilson measure. The levels are a finite family; the slice transfer operator has
  infinitely many, and the tree has no eigenvalue list of it, so `axis_relLip` is not instantiated at any step
  slice. `window_relLip` reads four real numbers and their derivatives, not `DefectBound.stepD`.
* (L) and (Cnt) are not proved for `SU(N)` at any coupling. `BasinGrowth.RelLip` is not proved.
* (L) is the bounded beta function, so this module moves the window uniformity of `RelLip` onto the slice size in
  (L) and onto the count in (Cnt); it does not remove it.

## Parameters

| symbol | meaning |
|---|---|
| `t`, `i₀` | the finite family of levels and its top |
| `g i β` | the gap of level `i` to the top at coupling `β`, `≥ 0`, `g i₀ = 0` |
| `g′ i` | its `β`-derivative at the point read |
| `m` | the time (the window time `2^{w+1}` on a step slice), `≥ 0` |
| `Λ` | the relative level rate of (L); no value is chosen |
| `C` | the count exponent of (Cnt); no value is chosen |
| `K` | a relative rate of directional defects in `window_relLip` |

DERIVED (module-wide): `2` the doubled time and the square in `log tr(m)²`; `4 = 2 · 2` in `abs_deriv_pdef_le`;
`8 = 4 · 2` in `axis_relLip`; `8, 4, 2, 1` the corner-path weights of `DefectBound.path_eq` and `15` their sum;
`120 = 8 · 15`; `1` the top's weight `e^0`, the numerator of `1/x` and `log(1/y) ≥ 1` at `y ≤ e^{−1}`; `0` the signs.
DERIVED: `1000` inherited from `DoublingSharp.rec_sharp` (`BasinGrowth.basinSeed = 1/1000`). CHOSEN: `1/2`, the
threshold on the defect under which `e^p − 1 ≤ 2p`; `e^{−1}`, the largest point where `x log(1/x)` increases.
COMPUTED: `3`, an upper bound for `e` (via `Real.exp_one_lt_d9`), so that `2/1000 ≤ e^{−1}`.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.LevelRate

open Finset Real

variable {ι : Type} (t : Finset ι) (g : ι → ℝ → ℝ)

/-! ## 0. The reads -/

/-- **The trace normalized by the top**: `tr k β = Σ_i e^{−k g_i(β)}`. DERIVED: no numeral. -/
def tr (k β : ℝ) : ℝ := ∑ i ∈ t, Real.exp (-(k * g i β))

/-- **The excited weight** `s = Σ_{i ≠ i₀} e^{−k g_i}`. DERIVED: no numeral. -/
def exc [DecidableEq ι] (i₀ : ι) (k β : ℝ) : ℝ := ∑ i ∈ t.erase i₀, Real.exp (-(k * g i β))

/-- **The defect** `2 log tr(m) − log tr(2m)`. DERIVED: `2` the square and the doubled time. -/
def pdef (m β : ℝ) : ℝ := 2 * Real.log (tr t g m β) - Real.log (tr t g (2 * m) β)

/-- **The Shannon read** `Σ_i e^{−m g_i} · m g_i = Σ_i z_i log(1/z_i)`. DERIVED: no numeral. -/
def ent (m β : ℝ) : ℝ := ∑ i ∈ t, Real.exp (-(m * g i β)) * (m * g i β)

/-- **The levels**: the top `i₀ ∈ t` has gap `0`, every gap is `≥ 0`. DERIVED: `0` the top's gap and the sign. -/
structure Levels (i₀ : ι) : Prop where
  mem : i₀ ∈ t
  top : ∀ β, g i₀ β = 0
  nonneg : ∀ i ∈ t, ∀ β, 0 ≤ g i β

variable {t g}

/-- `tr = 1 + exc`. DERIVED: `1` the top's weight `e^0`. -/
theorem tr_eq [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) (k β : ℝ) :
    tr t g k β = 1 + exc t g i₀ k β := by
  rw [tr, exc, ← add_sum_erase t _ hL.mem, hL.top, mul_zero, neg_zero, Real.exp_zero]

/-- DERIVED: `0` the sign. -/
theorem exc_nonneg [DecidableEq ι] (i₀ : ι) (k β : ℝ) : 0 ≤ exc t g i₀ k β :=
  sum_nonneg fun _ _ => (Real.exp_pos _).le

/-- `tr ≥ 1`. DERIVED: `1` the top's weight. -/
theorem one_le_tr [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) (k β : ℝ) : 1 ≤ tr t g k β := by
  rw [tr_eq hL]; linarith [exc_nonneg (t := t) (g := g) i₀ k β]

/-- DERIVED: `0` the sign. -/
theorem tr_pos [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) (k β : ℝ) : 0 < tr t g k β :=
  lt_of_lt_of_le one_pos (one_le_tr hL k β)

/-- **The defect sees only the gaps**: for the raw trace `a(k) = Σ e^{−k(E₀ + g_i)}` at any top energy `E₀`,
`2 log a(m) − log a(2m) = pdef`. DERIVED: `2` the square and the doubled time. -/
theorem pdef_shift [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) (E₀ m β : ℝ) :
    2 * Real.log (∑ i ∈ t, Real.exp (-(m * (E₀ + g i β))))
      - Real.log (∑ i ∈ t, Real.exp (-((2 * m) * (E₀ + g i β)))) = pdef t g m β := by
  have hk : ∀ k : ℝ, ∑ i ∈ t, Real.exp (-(k * (E₀ + g i β))) = Real.exp (-(k * E₀)) * tr t g k β := by
    intro k
    rw [tr, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← Real.exp_add]; congr 1; ring
  rw [hk, hk, Real.log_mul (Real.exp_pos _).ne' (tr_pos hL m β).ne',
    Real.log_mul (Real.exp_pos _).ne' (tr_pos hL (2 * m) β).ne', Real.log_exp, Real.log_exp, pdef]
  ring

/-! ## 1. The exact derivative -/

/-- **The derivative of the trace**: `∂_β tr(k) = Σ_i e^{−k g_i} · (−k ∂_β g_i)`. DERIVED: no numeral. -/
theorem hasDerivAt_tr {g' : ι → ℝ} {β : ℝ} (hg : ∀ i ∈ t, HasDerivAt (fun x => g i x) (g' i) β) (k : ℝ) :
    HasDerivAt (fun x => tr t g k x) (∑ i ∈ t, Real.exp (-(k * g i β)) * (-(k * g' i))) β := by
  unfold tr
  exact HasDerivAt.fun_sum fun i hi => ((hg i hi).const_mul k).neg.exp

/-- **The derivative of the defect** (the Hellmann–Feynman form on the trace):
`∂_β pdef = 2 ∂tr(m)/tr(m) − ∂tr(2m)/tr(2m)`. DERIVED: `2` the square and the doubled time. -/
theorem hasDerivAt_pdef [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {g' : ι → ℝ} {β : ℝ}
    (hg : ∀ i ∈ t, HasDerivAt (fun x => g i x) (g' i) β) (m : ℝ) :
    HasDerivAt (fun x => pdef t g m x)
      (2 * ((∑ i ∈ t, Real.exp (-(m * g i β)) * (-(m * g' i))) / tr t g m β)
        - (∑ i ∈ t, Real.exp (-((2 * m) * g i β)) * (-((2 * m) * g' i))) / tr t g (2 * m) β) β := by
  have h1 := ((hasDerivAt_tr hg m).log (tr_pos hL m β).ne').const_mul 2
  have h2 := (hasDerivAt_tr hg (2 * m)).log (tr_pos hL (2 * m) β).ne'
  exact h1.sub h2

/-! ## 2. The rate bound -/

/-- **(L) The level rate**: `|∂_β g_i| ≤ Λ g_i` at every level (the top has `g′ = 0`), `Λ ≥ 0`. A hypothesis.
DERIVED: `0` the sign. -/
def LevelLip (t : Finset ι) (g : ι → ℝ → ℝ) (g' : ι → ℝ) (Λ : ℝ) (β : ℝ) : Prop :=
  0 ≤ Λ ∧ ∀ i ∈ t, |g' i| ≤ Λ * g i β

/-- **The trace rate is at most the Shannon read**: `|∂tr(k)| ≤ Λ ent(k)` for `k ≥ 0`. DERIVED: `0` the sign. -/
theorem abs_deriv_tr_le {g' : ι → ℝ} {Λ β k : ℝ} (hk : 0 ≤ k) (hΛ : LevelLip t g g' Λ β) :
    |∑ i ∈ t, Real.exp (-(k * g i β)) * (-(k * g' i))| ≤ Λ * ent t g k β := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [ent, mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_mul, abs_of_nonneg hk]
  have := hΛ.2 i hi
  have he := (Real.exp_pos (-(k * g i β))).le
  calc Real.exp (-(k * g i β)) * (k * |g' i|) ≤ Real.exp (-(k * g i β)) * (k * (Λ * g i β)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hk) he
    _ = Λ * (Real.exp (-(k * g i β)) * (k * g i β)) := by ring

/-- **The doubled-time read is at most twice the read**: `ent(2m) ≤ 2 ent(m)`. DERIVED: `2` the doubled time. -/
theorem ent_double_le [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {m : ℝ} (hm : 0 ≤ m) (β : ℝ) :
    ent t g (2 * m) β ≤ 2 * ent t g m β := by
  rw [ent, ent, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hg := hL.nonneg i hi β
  have hmg : 0 ≤ m * g i β := mul_nonneg hm hg
  have hE : Real.exp (-((2 * m) * g i β)) ≤ Real.exp (-(m * g i β)) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (-((2 * m) * g i β)) * ((2 * m) * g i β)
        ≤ Real.exp (-(m * g i β)) * ((2 * m) * g i β) :=
          mul_le_mul_of_nonneg_right hE (by nlinarith)
    _ = 2 * (Real.exp (-(m * g i β)) * (m * g i β)) := by ring

/-- DERIVED: `0` the sign. -/
theorem ent_nonneg [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {m : ℝ} (hm : 0 ≤ m) (β : ℝ) :
    0 ≤ ent t g m β :=
  sum_nonneg fun i hi => mul_nonneg (Real.exp_pos _).le (mul_nonneg hm (hL.nonneg i hi β))

/-- **The defect rate is at most four level rates of the Shannon read**: `|∂_β pdef| ≤ 4Λ ent(m)`.
DERIVED: `4 = 2 · 2`, the doubled time and the two terms; `2` the doubled time. -/
theorem abs_deriv_pdef_le [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {g' : ι → ℝ} {Λ β m : ℝ}
    (hm : 0 ≤ m) (hΛ : LevelLip t g g' Λ β) :
    |2 * ((∑ i ∈ t, Real.exp (-(m * g i β)) * (-(m * g' i))) / tr t g m β)
        - (∑ i ∈ t, Real.exp (-((2 * m) * g i β)) * (-((2 * m) * g' i))) / tr t g (2 * m) β|
      ≤ 4 * Λ * ent t g m β := by
  set A := ∑ i ∈ t, Real.exp (-(m * g i β)) * (-(m * g' i))
  set B := ∑ i ∈ t, Real.exp (-((2 * m) * g i β)) * (-((2 * m) * g' i))
  have hA := abs_deriv_tr_le (t := t) (g := g) hm hΛ
  have hB := abs_deriv_tr_le (t := t) (g := g) (by linarith : (0 : ℝ) ≤ 2 * m) hΛ
  have h1 := one_le_tr hL m β
  have h2 := one_le_tr hL (2 * m) β
  have hAd : |A / tr t g m β| ≤ |A| := by
    rw [abs_div, abs_of_pos (tr_pos hL m β)]; exact div_le_self (abs_nonneg _) h1
  have hBd : |B / tr t g (2 * m) β| ≤ |B| := by
    rw [abs_div, abs_of_pos (tr_pos hL (2 * m) β)]; exact div_le_self (abs_nonneg _) h2
  have hD := ent_double_le hL hm β
  have hΛ0 := hΛ.1
  have hDΛ : Λ * ent t g (2 * m) β ≤ Λ * (2 * ent t g m β) := mul_le_mul_of_nonneg_left hD hΛ0
  calc |2 * (A / tr t g m β) - B / tr t g (2 * m) β|
        ≤ |2 * (A / tr t g m β)| + |B / tr t g (2 * m) β| := abs_sub _ _
    _ = 2 * |A / tr t g m β| + |B / tr t g (2 * m) β| := by rw [abs_mul, abs_two]
    _ ≤ 2 * (Λ * ent t g m β) + Λ * (2 * ent t g m β) := by linarith
    _ = 4 * Λ * ent t g m β := by ring

/-! ## 3. The Shannon split of the read -/

/-- **The top contributes nothing to the read.** DERIVED: `0` the top's gap. -/
theorem ent_eq_excited [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) (m β : ℝ) :
    ent t g m β = ∑ i ∈ t.erase i₀, Real.exp (-(m * g i β)) * (m * g i β) := by
  rw [ent, ← add_sum_erase t _ hL.mem, hL.top, mul_zero, mul_zero, zero_add]

/-- **The Shannon split**: with `s = exc > 0`, `ent = s log(1/s) + s Σ_{i ≠ i₀} π_i log(1/π_i)`, `π_i = z_i/s`.
DERIVED: `1` the numerator of `1/x`. -/
theorem ent_eq_shannon [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) (m β : ℝ)
    (hs : 0 < exc t g i₀ m β) :
    ent t g m β = exc t g i₀ m β * Real.log (1 / exc t g i₀ m β)
      + exc t g i₀ m β * ∑ i ∈ t.erase i₀,
          (Real.exp (-(m * g i β)) / exc t g i₀ m β)
            * Real.log (1 / (Real.exp (-(m * g i β)) / exc t g i₀ m β)) := by
  set s := exc t g i₀ m β with hsdef
  rw [ent_eq_excited hL, mul_sum]
  have hsum : s * Real.log (1 / s) = ∑ i ∈ t.erase i₀, Real.exp (-(m * g i β)) * Real.log (1 / s) := by
    rw [← sum_mul, hsdef, exc]
  rw [hsum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have hz := Real.exp_pos (-(m * g i β))
  have e1 : 1 / (Real.exp (-(m * g i β)) / s) = s / Real.exp (-(m * g i β)) := by
    field_simp
  rw [e1, Real.log_div hs.ne' hz.ne', Real.log_exp, one_div, Real.log_inv]
  field_simp
  ring

/-- **(Cnt) The count read**: `ent(m) ≤ (1 + C) s log(1/s)`. A hypothesis. DERIVED: `1` the single-level read. -/
def CountRead [DecidableEq ι] (t : Finset ι) (g : ι → ℝ → ℝ) (i₀ : ι) (C m β : ℝ) : Prop :=
  ent t g m β ≤ (1 + C) * (exc t g i₀ m β * Real.log (1 / exc t g i₀ m β))

/-- **The count read is a Shannon count bound**: `H(π) ≤ C log(1/s)` gives `CountRead`. DERIVED: `1` the numerator. -/
theorem countRead_of_shannon [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {C m β : ℝ}
    (hs : 0 < exc t g i₀ m β)
    (hH : ∑ i ∈ t.erase i₀, (Real.exp (-(m * g i β)) / exc t g i₀ m β)
            * Real.log (1 / (Real.exp (-(m * g i β)) / exc t g i₀ m β))
          ≤ C * Real.log (1 / exc t g i₀ m β)) :
    CountRead t g i₀ C m β := by
  unfold CountRead
  rw [ent_eq_shannon hL m β hs]
  have := mul_le_mul_of_nonneg_left hH hs.le
  nlinarith [this]

/-- **`k` equal levels have Shannon entropy `log k`** (the count is load-bearing). DERIVED: `1` the numerator. -/
theorem shannon_uniform {k : ℕ} (hk : 0 < k) :
    ∑ _i ∈ Finset.range k, ((1 : ℝ) / k) * Real.log (1 / (1 / k)) = Real.log k := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  rw [sum_const, card_range, nsmul_eq_mul, one_div_one_div, ← mul_assoc, mul_one_div_cancel hk'.ne',
    one_mul]

/-- **The top excited share does not fall along a time doubling**: for weights `0 ≤ z_i ≤ z₁`, `z₁ > 0`, `i₁ ∈ u`,
`z₁/Σ z ≤ z₁²/Σ z²`. A ratio, so scale-free; along one direction only (same operator).
DERIVED: `2` the doubled time (the square). -/
theorem top_share_double_le {u : Finset ι} {z : ι → ℝ} {i₁ : ι} (hi₁ : i₁ ∈ u) (hz1 : 0 < z i₁)
    (hz : ∀ i ∈ u, 0 ≤ z i) (htop : ∀ i ∈ u, z i ≤ z i₁) :
    z i₁ / ∑ i ∈ u, z i ≤ z i₁ ^ 2 / ∑ i ∈ u, z i ^ 2 := by
  have hS : 0 < ∑ i ∈ u, z i := lt_of_lt_of_le hz1 (single_le_sum hz hi₁)
  have hS2 : 0 < ∑ i ∈ u, z i ^ 2 :=
    lt_of_lt_of_le (pow_pos hz1 2) (single_le_sum (fun i hi => sq_nonneg (z i)) hi₁)
  have hle : ∑ i ∈ u, z i ^ 2 ≤ z i₁ * ∑ i ∈ u, z i := by
    rw [mul_sum]; exact sum_le_sum fun i hi => by
      rw [sq]; exact mul_le_mul_of_nonneg_right (htop i hi) (hz i hi)
  rw [div_le_div_iff₀ hS hS2]
  nlinarith [mul_le_mul_of_nonneg_left hle hz1.le]

/-! ## 4. The defect against its excited weight -/

/-- **Purity**: `log(1 + s) ≤ pdef` at `m ≥ 0`. DERIVED: `1` the top's weight; `2` the square and the doubled time. -/
theorem log_one_add_exc_le [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {m : ℝ} (hm : 0 ≤ m) (β : ℝ) :
    Real.log (1 + exc t g i₀ m β) ≤ pdef t g m β := by
  have hle : exc t g i₀ (2 * m) β ≤ exc t g i₀ m β := by
    refine sum_le_sum fun i hi => Real.exp_le_exp.2 ?_
    have := hL.nonneg i (mem_of_mem_erase hi) β
    nlinarith
  have h0 := exc_nonneg (t := t) (g := g) i₀ (2 * m) β
  rw [pdef, tr_eq hL, tr_eq hL]
  have := Real.log_le_log (by linarith) (by linarith : 1 + exc t g i₀ (2 * m) β ≤ 1 + exc t g i₀ m β)
  have hp : 0 ≤ Real.log (1 + exc t g i₀ m β) :=
    Real.log_nonneg (by linarith [exc_nonneg (t := t) (g := g) i₀ m β])
  linarith

/-- **The excited weight is at most twice the defect** when the defect is at most `1/2`.
CHOSEN: `1/2`, the threshold under which `e^p − 1 ≤ p/(1 − p) ≤ 2p`. DERIVED: `2` the factor. -/
theorem exc_le_two_pdef [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {m : ℝ} (hm : 0 ≤ m) (β : ℝ)
    (hp : pdef t g m β ≤ 1 / 2) : exc t g i₀ m β ≤ 2 * pdef t g m β := by
  set s := exc t g i₀ m β
  set p := pdef t g m β
  have hs0 : 0 ≤ s := exc_nonneg i₀ m β
  have hl := log_one_add_exc_le hL hm β
  have hp0 : 0 ≤ p := (Real.log_nonneg (by linarith)).trans hl
  have h1 : 1 + s ≤ Real.exp p := by
    calc 1 + s = Real.exp (Real.log (1 + s)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp p := Real.exp_le_exp.2 hl
  have h2 : Real.exp p ≤ 1 / (1 - p) := Real.exp_bound_div_one_sub_of_interval hp0 (by linarith)
  have h3 : 1 / (1 - p) ≤ 1 + 2 * p := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- **`x log(1/x)` increases on `[0, e^{−1}]`**: `0 ≤ x ≤ y ≤ e^{−1}` gives `x log(1/x) ≤ y log(1/y)`.
CHOSEN: `e^{−1}`, the largest point where `x log(1/x)` increases. DERIVED: `1` the numerator and `log(1/y) ≥ 1`;
`0` the sign. -/
theorem negMulLog_le_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.exp (-1)) :
    x * Real.log (1 / x) ≤ y * Real.log (1 / y) := by
  rcases eq_or_lt_of_le hx with h0 | h0
  · rw [← h0, zero_mul]
    rcases eq_or_lt_of_le (hx.trans hxy) with hy0 | hy0
    · rw [← hy0, zero_mul]
    · have : Real.log y ≤ -1 := by
        calc Real.log y ≤ Real.log (Real.exp (-1)) := Real.log_le_log hy0 hy
          _ = -1 := Real.log_exp _
      rw [one_div, Real.log_inv]; nlinarith
  · have hyp : 0 < y := h0.trans_le hxy
    have hL : 1 ≤ Real.log (1 / y) := by
      rw [one_div, Real.log_inv, le_neg]
      calc Real.log y ≤ Real.log (Real.exp (-1)) := Real.log_le_log hyp hy
        _ = -1 := Real.log_exp _
    have e : Real.log (1 / x) = Real.log (1 / y) + Real.log (y / x) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have hq : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hyp h0)
    have hxq : x * Real.log (y / x) ≤ y - x := by
      have := mul_le_mul_of_nonneg_left hq h0.le
      rw [mul_sub, mul_div_cancel₀ _ h0.ne', mul_one] at this; exact this
    rw [e, mul_add]
    nlinarith [mul_le_mul_of_nonneg_right (sub_nonneg.2 hxy) (by linarith : (0 : ℝ) ≤ Real.log (1 / y) - 1)]

/-- `2 · (1/1000) ≤ e^{−1}`. COMPUTED: `3`, an upper bound for `e` (via `Real.exp_one_lt_d9`). CHOSEN: `e^{−1}`, the
largest point where `x log(1/x)` increases. DERIVED: `2` the factor of `exc_le_two_pdef`; `1000` inherited from
`DoublingSharp.rec_sharp` (`BasinGrowth.basinSeed`). -/
theorem two_seed_le : 2 * BasinGrowth.basinSeed ≤ Real.exp (-1) := by
  rw [BasinGrowth.basinSeed, Real.exp_neg]
  have h := Real.exp_one_lt_d9
  rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
  norm_num at h ⊢; linarith

/-! ## 5. The relative bound -/

/-- **The relative bound on one direction**: (L) at rate `Λ`, (Cnt) at exponent `C ≥ −1`, and `pdef ≤ 1/1000` give
`|∂_β pdef| ≤ 8Λ(1 + C) · pdef · log(1/pdef)`. DERIVED: `8 = 4 · 2`; `1000` inherited from `DoublingSharp.rec_sharp`;
`1` the numerator. -/
theorem axis_relLip [DecidableEq ι] {i₀ : ι} (hL : Levels t g i₀) {g' : ι → ℝ} {Λ C β m : ℝ} (hm : 0 ≤ m)
    (hg : ∀ i ∈ t, HasDerivAt (fun x => g i x) (g' i) β) (hΛ : LevelLip t g g' Λ β) (hC : -1 ≤ C)
    (hcount : CountRead t g i₀ C m β) (hp : pdef t g m β ≤ BasinGrowth.basinSeed) :
    |deriv (fun x => pdef t g m x) β|
      ≤ 8 * Λ * (1 + C) * (pdef t g m β * Real.log (1 / pdef t g m β)) := by
  rw [(hasDerivAt_pdef hL hg m).deriv]
  refine (abs_deriv_pdef_le hL hm hΛ).trans ?_
  set s := exc t g i₀ m β
  set p := pdef t g m β
  have hseed : BasinGrowth.basinSeed ≤ 1 / 2 := by rw [BasinGrowth.basinSeed]; norm_num
  have hs0 : 0 ≤ s := exc_nonneg i₀ m β
  have hs2 : s ≤ 2 * p := exc_le_two_pdef hL hm β (hp.trans hseed)
  have hp0 : 0 ≤ p := by linarith
  have h2p : 2 * p ≤ Real.exp (-1) := by have := two_seed_le; linarith
  have hneg : s * Real.log (1 / s) ≤ 2 * p * Real.log (1 / (2 * p)) := negMulLog_le_of_le hs0 hs2 h2p
  have hlog2 : 2 * p * Real.log (1 / (2 * p)) ≤ 2 * (p * Real.log (1 / p)) := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h]; simp
    · rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul two_ne_zero h.ne']
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      nlinarith
  have hC0 : 0 ≤ 1 + C := by linarith
  have hcount' : ent t g m β ≤ (1 + C) * (2 * (p * Real.log (1 / p))) :=
    hcount.trans (mul_le_mul_of_nonneg_left (hneg.trans hlog2) hC0)
  have h4 : 0 ≤ 4 * Λ := by linarith [hΛ.1]
  calc 4 * Λ * ent t g m β ≤ 4 * Λ * ((1 + C) * (2 * (p * Real.log (1 / p)))) :=
        mul_le_mul_of_nonneg_left hcount' h4
    _ = 8 * Λ * (1 + C) * (p * Real.log (1 / p)) := by ring

/-- **The window from four directions**: `P_i ≥ 0` with `|P_i′| ≤ K P_i log(1/P_i)`, `K ≥ 0`, and
`D = 8P₀ + 4P₁ + 2P₂ + P₃ ≤ e^{−1}` give `|8P₀′ + 4P₁′ + 2P₂′ + P₃′| ≤ 15 K D log(1/D)`.
CHOSEN: `e^{−1}`, the largest point where `x log(1/x)` increases. DERIVED: `8, 4, 2, 1` the corner-path weights of `DefectBound.path_eq`; `15 = 8 + 4 + 2 + 1`; `1` the numerator;
`0`–`3` the direction labels of `Fin 4`. -/
theorem window_relLip {P d : Fin 4 → ℝ} {K : ℝ} (hK : 0 ≤ K) (hP : ∀ i, 0 ≤ P i)
    (hd : ∀ i, |d i| ≤ K * (P i * Real.log (1 / P i)))
    (hD : 8 * P 0 + 4 * P 1 + 2 * P 2 + P 3 ≤ Real.exp (-1)) :
    |8 * d 0 + 4 * d 1 + 2 * d 2 + d 3|
      ≤ 15 * K * ((8 * P 0 + 4 * P 1 + 2 * P 2 + P 3)
          * Real.log (1 / (8 * P 0 + 4 * P 1 + 2 * P 2 + P 3))) := by
  set D := 8 * P 0 + 4 * P 1 + 2 * P 2 + P 3 with hDdef
  have h0 := hP 0; have h1 := hP 1; have h2 := hP 2; have h3 := hP 3
  have hle : ∀ i, P i ≤ D := by
    intro i; fin_cases i <;> simp <;> linarith
  have hm : ∀ i, |d i| ≤ K * (D * Real.log (1 / D)) := fun i =>
    (hd i).trans (mul_le_mul_of_nonneg_left (negMulLog_le_of_le (hP i) (hle i) hD) hK)
  have a0 := hm 0; have a1 := hm 1; have a2 := hm 2; have a3 := hm 3
  calc |8 * d 0 + 4 * d 1 + 2 * d 2 + d 3|
        ≤ |8 * d 0| + |4 * d 1| + |2 * d 2| + |d 3| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
    _ = 8 * |d 0| + 4 * |d 1| + 2 * |d 2| + |d 3| := by
          rw [abs_mul, abs_mul, abs_mul]; norm_num
    _ ≤ 15 * K * (D * Real.log (1 / D)) := by linarith

/-- **The window from the levels**: four directional rate bounds `hd` at rate `8Λ(1 + C)` (the conclusion of
`axis_relLip` on each directional spectrum) and the weighted sum at most `e^{−1}` give the window bound with
`K = 120 Λ (1 + C)`. CHOSEN: `e^{−1}`, the largest point where `x log(1/x)` increases. DERIVED: `120 = 8 · 15`;
`8, 4, 2, 1` the corner-path weights; `1` the numerator; `0`–`3` the direction labels of `Fin 4`. -/
theorem window_of_levels {P d : Fin 4 → ℝ} {Λ C : ℝ} (hΛ : 0 ≤ Λ) (hC : -1 ≤ C) (hP : ∀ i, 0 ≤ P i)
    (hd : ∀ i, |d i| ≤ 8 * Λ * (1 + C) * (P i * Real.log (1 / P i)))
    (hD : 8 * P 0 + 4 * P 1 + 2 * P 2 + P 3 ≤ Real.exp (-1)) :
    |8 * d 0 + 4 * d 1 + 2 * d 2 + d 3|
      ≤ 120 * Λ * (1 + C) * ((8 * P 0 + 4 * P 1 + 2 * P 2 + P 3)
          * Real.log (1 / (8 * P 0 + 4 * P 1 + 2 * P 2 + P 3))) := by
  have hK : 0 ≤ 8 * Λ * (1 + C) := by have : 0 ≤ 1 + C := by linarith
                                      positivity
  have := window_relLip hK hP hd hD
  calc _ ≤ _ := this
    _ = _ := by ring

end MassGap.LevelRate

end

#print axioms MassGap.LevelRate.tr_eq
#print axioms MassGap.LevelRate.pdef_shift
#print axioms MassGap.LevelRate.hasDerivAt_tr
#print axioms MassGap.LevelRate.hasDerivAt_pdef
#print axioms MassGap.LevelRate.abs_deriv_tr_le
#print axioms MassGap.LevelRate.ent_double_le
#print axioms MassGap.LevelRate.abs_deriv_pdef_le
#print axioms MassGap.LevelRate.ent_eq_excited
#print axioms MassGap.LevelRate.ent_eq_shannon
#print axioms MassGap.LevelRate.countRead_of_shannon
#print axioms MassGap.LevelRate.shannon_uniform
#print axioms MassGap.LevelRate.top_share_double_le
#print axioms MassGap.LevelRate.log_one_add_exc_le
#print axioms MassGap.LevelRate.exc_le_two_pdef
#print axioms MassGap.LevelRate.negMulLog_le_of_le
#print axioms MassGap.LevelRate.two_seed_le
#print axioms MassGap.LevelRate.axis_relLip
#print axioms MassGap.LevelRate.window_relLip
#print axioms MassGap.LevelRate.window_of_levels
