import Mathlib
import MassGap.BetaFlow
import MassGap.ZoomDown

/-!
# MassGap.BasinGrowth — the basin grows by a fixed coupling step per window under a relative Lipschitz bound

Write `D(β, w) = CouplingTower.windowCoupling N β w` (the doubling defect of the periodic Wilson torus of side `2^w`)
and `ε = 1/1000`, the seed of `DoublingSharp` (Inherited). The basin at window `k`, read from a base coupling `β₀`,
is the largest interval `[β₀, B_k]` on which `D(·, k) ≤ ε`. This module states that interval through the predicate
`InBasin N β₀ b k` (every `β ∈ [β₀, b]` has `D(β, k) ≤ ε`, i.e. `B_k ≥ b`) and proves that, under one relative
Lipschitz bound in `β` inside the basin, the basin edge moves up by a fixed step `c` from each window to the next.
The step reaches every coupling, so the window coupling vanishes at every `β ≥ β₀`. Declarations are in the
namespace `MassGap.BasinGrowth`.

`(S)` is not proved here. The input `RelLip` is a hypothesis, open for `SU(N)` at every base coupling.

## 0. What the tree had (map)

* `CouplingTower.windowCoupling_succ_le` (from `DoublingSharp.rec_sharp`): `D(β, w) ≤ ε ⇒ D(β, w+1) ≤ 250 D(β, w)²`.
  `CouplingTower.windowCoupling_nonneg`, `windowCoupling_zero` (`D(0, w) = 0`), `continuous_windowCoupling`,
  `hasDerivAt_windowCoupling` (`∂_β D(w) = ⟨S⟩_{2·2^w} − 16 ⟨S⟩_{2^w}`, the cut energy).
* `StrongAnchor`: `Vanishes N β`, `vanishes_iff_seed`, the anchor `strongAnchor` (on `[0, b)`, `b > 0` existential),
  `noStall_iff`, `strongEnd_of_noStall`.
* `BetaFlow`: a flow in `β` at fixed window under the Osgood form `∂_β D ≤ K D (1 + D) log(1 + 1/D)` at every `D > 0`,
  with no threshold. `RelLip` below asks a bound of the same shape only inside the basin (`D ≤ ε`); outside the
  basin it asks nothing, and the squaring recursion carries the basin from one window to the next.

## 1. The step length (proved; COMPUTED)

* `basinSeed = 1/1000` (Inherited), `squareLevel = 250 ε² = 1/4000 = ε/4` (COMPUTED from the `250` of `rec_sharp`,
  Inherited, and `ε`): `squareLevel_eq`, `squareLevel_eq_quarter`.
* `stepRatio = log((250 ε²)⁻¹) / log(ε⁻¹) = log 4000 / log 1000` (COMPUTED; `stepRatio_eq`), `one_lt_stepRatio`.
* `stepLen K = log(stepRatio) / K = log(log 4000 / log 1000) / K` (COMPUTED; `stepLen_eq`), `stepLen_pos`.

## 2. The barrier (proved)

* `barrier ℓ k a x = exp(−ℓ e^{−k(x−a)})` solves `B′ = k B log(1/B)` (`hasDerivAt_barrier`, `neg_log_barrier`).
* `le_barrier`: if `u a ≤ e^{−ℓ}`, `ℓ > 0`, `K < k`, `k ≥ 0`, the barrier at `b` is at most `ε`, and
  `u′ ≤ K u log(1/u)` wherever `0 < u ≤ ε` on `[a, b)`, then `u ≤ barrier` on `[a, b]`. The rate `k > K` makes
  the barrier strictly faster at a touching point (`image_le_of_deriv_right_lt_deriv_boundary'`).
* `stay_in_basin`: from `u a ≤ ε/4` and that bound with `K > 0`, `u ≤ ε` on `[a, a + stepLen K]`. This is the
  Grönwall step on `L = log(1/u)`: `L′ ≥ −K L` while `u ≤ ε`, so `L ≥ log 4000 · e^{−K(x−a)} ≥ log 1000`.
  The closed end comes from continuity.

## 3. The input (stated, not proved)

* `RelLip N β₀ K`: for every `β ≥ β₀` and every window `w ≥ 1` with `D(β, w) ≤ ε`,
  `|∂_β D(β, w)| ≤ K · D(β, w) · log(1/D(β, w))`. At `D = 0` the bound reads `0`. `RelLipUp` is the one-sided
  form (`∂_β D ≤ …`), which is all the proofs read: `relLipUp_of_relLip`, `relLipUp_mono`.
* `relLipUp_of_osgoodFlow`: at `β₀ > 0`, `BetaFlow.OsgoodFlow N β₀ (fun _ => K)` with `K ≥ 0` gives
  `RelLipUp N β₀ (2K)` (CHOSEN `2`: any factor above `(1 + ε)(1 + ε/log 1000)` serves). So `RelLip` asks no more
  than the constant-speed Osgood form of `BetaFlow`, and asks nothing outside the basin.

## 4. The reduction (proved)

* (a) `next_le_squareLevel`, `inBasin_succ`: `D(β, k) ≤ ε ⇒ D(β, k+1) ≤ 250 ε² = ε/4`; so `B_{k+1} ≥ B_k`.
* (c) `inBasin_step`: under `RelLipUp N β₀ K`, `K > 0`: `InBasin N β₀ b k ⇒ InBasin N β₀ (b + stepLen K) (k + 1)`,
  i.e. `B_{k+1} ≥ B_k + c` with `c = log(log 4000 / log 1000)/K`.
* (d) `inBasin_iter`: `InBasin N β₀ (β₀ + j c) (k + j)` for every `j`; `inBasin_of_vanishes`: the base window
  from `Vanishes N β₀`; `vanishes_of_inBasin`: a window in the basin gives the vanishing read.
* `vanishes_of_relLipUp`, `vanishes_of_relLip` (capstone at one base): `Vanishes N β₀`, `RelLip N β₀ K`, `K > 0`
  give `Tendsto (windowCoupling N β) atTop (𝓝 0)` at every `β ≥ β₀`; `strongEnd_of_relLip`: hence `StrongEnd N`.
* `RelLipNearZero N`: frequently as `β₀ → 0⁺`, some `K > 0` has `RelLip N β₀ K` (`K` may depend on `β₀`).
  `vanishes_of_relLipNearZero` (capstone): the window coupling tends to `0` at every `β ≥ 0`, with no base
  hypothesis (the anchor `StrongAnchor.strongAnchor` supplies the base). `strongEnd_of_relLipNearZero`:
  `StrongEnd N`. `relLipNearZero_of_forall`: a bound at every `β₀ > 0`, with `K` depending on `β₀`, is an instance.

## 5. Tests (proved and argued)

* The base must sit at `β₀ > 0` (proved). `relLipUp_zero_trivial`: `RelLipUp N 0 K`, `K > 0`, forces `D ≡ 0` at every
  window and every `β ≥ 0`: `D(0, w) = 0` and `D log(1/D)` is an Osgood modulus, so the flow never leaves `0`.
  `not_relLip_zero`: for `N ≥ 2` that is false (`ZoomDown.window_out_of_basin`), so `RelLip N 0 K` fails for
  every `K > 0`. Physically `K` must blow up as `β₀ → 0⁺`: at strong coupling `m(β) ≈ 4 log(1/β)` and
  `|d log m/dβ| ≈ 1/(β log(1/β))`. This is why the capstone reads `RelLipNearZero`.
* Physical reading (proved on the family, argued for `D`). `expFamily_bound_iff`: on `D = e^{−m(β) n}`,
  `n = 2^w`, the bound is `|m′| ≤ K m`, the same at every window. So in the basin, where `D ~ e^{−m 2^w}`, `RelLip`
  says `|d log m/dβ| ≤ K`: a bounded lattice beta function, read in window form. It is consistent with the growth
  it produces: window `k` enters the basin once `m(β) 2^k` exceeds a fixed level, so `B_k` grows linearly in `k`
  exactly when `log ξ(β) = −log m(β)` grows at most linearly in `β`.
* `U(1)` (argued). The `U(1)` Wilson theory has no `(S)` at large `β` (Coulomb phase), so the conclusion fails
  there and `RelLip` must fail for every `K` and every `β₀`. It fails at the transition `β_c`: either `m → 0` at
  `β_c` (then `|d log m/dβ|` is unbounded there) or the transition is first order (then at finite volume `∂_β D`
  carries a latent-heat term growing with the volume, not bounded by `K D log(1/D)` uniformly in `w`). Either way the
  growth step `c` cannot be uniform across `β_c`.
* The free massless field never enters the basin at large windows: `RelLip` is vacuous there and the reduction
  says nothing about it. `TwoDVanish` (vanishing in `d = 2` at every `β`) is consistent with the conclusion.
* `BetaFlow.sharp_form_fails` (the form `∂d ≤ K d log(1/d)` fails at `d = 1`) does not touch `RelLip`: `d = 1` is
  outside the basin, where `RelLip` asks nothing.

## 6. What remains of `RelLip` (argued)

By `CouplingTower.hasDerivAt_windowCoupling`, `RelLip` is a bound on the cut energy
`⟨S⟩_{2·2^w} − 16 ⟨S⟩_{2^w}` by `K D log(1/D)` inside the basin. In the basin the seed gives a transverse transfer gap
at rate `log 2/2^w` (`DoublingSharp`, `StrongEndVanishing`), and `D` is carried by the excited slices of the
transfer operator: `D ≈ Σ_i e^{−E_i 2^w}` up to prefactors, with `E_i` the excitation energies on the slice. By
Hellmann–Feynman, `∂_β E_i` is the action excess of excitation `i` per unit time. Term by term, `RelLip` is then

  `|∂_β E_1| ≤ K E_1` (plus a prefactor term `|∂_β log C| ≤ K log 1000`),

the action excess of the lightest excitation bounded by a fixed multiple of its energy. The upper side is local
(a sum of plaquette-action differences over the support of the excitation), but the support has extent `ξ = 1/E_1`,
so the local bound gives `|∂_β E_1| ≲ ξ³`, not `≲ K E_1`. Closing it needs the action excess to scale like the mass
across all scales between the lattice and `ξ`: a statement about the lattice beta function having no zero
(asymptotic scaling), which is multiscale, not local.

## Parameters

| symbol | meaning |
|---|---|
| `N` | rank of `SU(N)` |
| `β`, `β₀`, `a`, `b`, `x` | couplings; `β₀` the base, `b` a basin edge |
| `w`, `k`, `j` | window indices; the window is the torus of side `2^w`; `j` counts steps |
| `K` | the relative Lipschitz constant of the input; no value is chosen |
| `k` (in the barrier) | the barrier rate, `> K`; proof-internal |
| `ℓ` | a level: the start reads at most `e^{−ℓ}` |

Numerals: Inherited `1/1000` (`ε`, `DoublingSharp`) and `250` (`rec_sharp`); COMPUTED `1/4000 = 250 ε²`,
`4000 = 4 · 1000`, `log(log 4000/log 1000)`; CHOSEN `2` in `relLipUp_of_osgoodFlow` (a factor above
`(1 + ε)(1 + ε/log 1000)`); `0`, `1`, `2`, `4` otherwise the signs, the least window, the doubling and the quarter.

## What does not follow

`RelLip N β₀ K` is not proved for `SU(N)` at any `β₀ > 0` for any `K`, and so `(S)` (`StrongEnd N`) is not proved
here. Nothing bounds `K` from above. `RelLip N 0 K` is false for `N ≥ 2` (`not_relLip_zero`), so the input must be
asked at positive base couplings, with `K` allowed to grow as `β₀ → 0⁺`. The failure of `RelLip` for `U(1)` is
argued, not proved of the `U(1)` lattice theory. The spectral reading of `D` and the Hellmann–Feynman form of the
residual in section 6 are argued, not formalised. The basin edge `B_k` is read through `InBasin`; no supremum is
formed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.BasinGrowth

open Filter Topology Set

/-! ## 1. The step length -/

/-- **The basin seed** `ε`. DERIVED: `1000` inherited from `DoublingSharp.rec_sharp` (`ε = 1/1000`). -/
def basinSeed : ℝ := 1 / 1000

/-- **The squared seed** `250 ε²`. DERIVED: `250` inherited from `DoublingSharp.rec_sharp`; `2` the square. -/
def squareLevel : ℝ := 250 * basinSeed ^ 2

/-- COMPUTED: `250 ε² = 1/4000`. -/
theorem squareLevel_eq : squareLevel = 1 / 4000 := by
  rw [squareLevel, basinSeed]; norm_num

/-- COMPUTED: `250 ε² = ε/4`; `4` the squaring margin. -/
theorem squareLevel_eq_quarter : squareLevel = basinSeed / 4 := by
  rw [squareLevel, basinSeed]; norm_num

/-- DERIVED: `0` the sign. -/
theorem squareLevel_pos : 0 < squareLevel := by rw [squareLevel_eq]; norm_num

/-- DERIVED: `0` the sign. -/
theorem basinSeed_pos : 0 < basinSeed := by rw [basinSeed]; norm_num

/-- COMPUTED: `250 ε² < ε`. -/
theorem squareLevel_lt : squareLevel < basinSeed := by
  rw [squareLevel_eq, basinSeed]; norm_num

/-- **The step ratio** `log((250 ε²)⁻¹) / log(ε⁻¹)`. DERIVED: `250` and `1000` inherited from `DoublingSharp.rec_sharp` through `squareLevel` and `basinSeed`. -/
def stepRatio : ℝ := Real.log squareLevel⁻¹ / Real.log basinSeed⁻¹

/-- COMPUTED: the step ratio is `log 4000 / log 1000`. -/
theorem stepRatio_eq : stepRatio = Real.log 4000 / Real.log 1000 := by
  rw [stepRatio, squareLevel_eq, basinSeed]; norm_num

/-- COMPUTED: `log 1000 > 0`. -/
theorem log_thousand_pos : 0 < Real.log 1000 := Real.log_pos (by norm_num)

/-- COMPUTED: `log 4000 > log 1000`, so the ratio exceeds `1`. -/
theorem one_lt_stepRatio : 1 < stepRatio := by
  rw [stepRatio_eq, one_lt_div log_thousand_pos]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- **The step length** `c = log(stepRatio) / K`. No numeral beyond the inherited ones. -/
def stepLen (K : ℝ) : ℝ := Real.log stepRatio / K

/-- COMPUTED: `c = log(log 4000 / log 1000) / K`. -/
theorem stepLen_eq (K : ℝ) : stepLen K = Real.log (Real.log 4000 / Real.log 1000) / K := by
  rw [stepLen, stepRatio_eq]

/-- DERIVED: `0` the sign. -/
theorem stepLen_pos {K : ℝ} (hK : 0 < K) : 0 < stepLen K :=
  div_pos (Real.log_pos one_lt_stepRatio) hK

/-! ## 2. The barrier -/

/-- **The barrier** `exp(−ℓ e^{−k(x−a)})`, the solution of `B′ = k B log(1/B)` with `B a = e^{−ℓ}`.
DERIVED: no numeral. -/
def barrier (ℓ k a x : ℝ) : ℝ := Real.exp (-(ℓ * Real.exp (-(k * (x - a)))))

/-- DERIVED: `0` the sign. -/
theorem barrier_pos (ℓ k a x : ℝ) : 0 < barrier ℓ k a x := Real.exp_pos _

/-- `log(1/B) = ℓ e^{−k(x−a)}`. DERIVED: no numeral. -/
theorem neg_log_barrier (ℓ k a x : ℝ) :
    -Real.log (barrier ℓ k a x) = ℓ * Real.exp (-(k * (x - a))) := by
  rw [barrier, Real.log_exp, neg_neg]

/-- **The barrier solves its equation**: `B′ = k B ℓ e^{−k(x−a)} = k B log(1/B)`. DERIVED: no numeral. -/
theorem hasDerivAt_barrier (ℓ k a x : ℝ) :
    HasDerivAt (barrier ℓ k a) (k * barrier ℓ k a x * (ℓ * Real.exp (-(k * (x - a))))) x := by
  have h1 : HasDerivAt (fun s => -(k * (s - a))) (-k) x :=
    (((hasDerivAt_id' x).sub_const a).const_mul k).neg.congr_deriv (by ring)
  have h2 : HasDerivAt (fun s => ℓ * Real.exp (-(k * (s - a))))
      (ℓ * (Real.exp (-(k * (x - a))) * -k)) x := h1.exp.const_mul ℓ
  have h3 : HasDerivAt (fun s => -(ℓ * Real.exp (-(k * (s - a)))))
      (-(ℓ * (Real.exp (-(k * (x - a))) * -k))) x := h2.neg
  have h4 := h3.exp
  show HasDerivAt (fun s => Real.exp (-(ℓ * Real.exp (-(k * (s - a))))))
    (k * Real.exp (-(ℓ * Real.exp (-(k * (x - a))))) * (ℓ * Real.exp (-(k * (x - a))))) x
  exact h4.congr_deriv (by ring)

/-- **The barrier bound**: if `u a ≤ e^{−ℓ}`, `ℓ > 0`, `0 ≤ k`, `K < k`, the barrier at `b` is at most `ε`
(`log(1/ε) ≤ ℓ e^{−k(b−a)}`), and `u′ ≤ K u log(1/u)` wherever `0 < u ≤ ε` on `[a, b)`, then `u ≤ barrier` on
`[a, b]`. DERIVED: `0` the sign. -/
theorem le_barrier {u u' : ℝ → ℝ} {K k ε ℓ a b : ℝ} (_hab : a ≤ b) (hk : 0 ≤ k) (hKk : K < k)
    (hℓ : 0 < ℓ) (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (h0 : u a ≤ Real.exp (-ℓ)) (hε : 0 < ε)
    (hεb : -Real.log ε ≤ ℓ * Real.exp (-(k * (b - a))))
    (hflow : ∀ x ∈ Ico a b, 0 < u x → u x ≤ ε → u' x ≤ K * u x * (-Real.log (u x))) :
    ∀ x ∈ Icc a b, u x ≤ barrier ℓ k a x := by
  have hP : ∀ x, 0 < ℓ * Real.exp (-(k * (x - a))) := fun x => mul_pos hℓ (Real.exp_pos _)
  have hle : ∀ x ∈ Icc a b, barrier ℓ k a x ≤ ε := by
    intro x hx
    have hE : Real.exp (-(k * (b - a))) ≤ Real.exp (-(k * (x - a))) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 a) hk))
    have h1 : -Real.log ε ≤ ℓ * Real.exp (-(k * (x - a))) :=
      hεb.trans (mul_le_mul_of_nonneg_left hE hℓ.le)
    calc barrier ℓ k a x ≤ Real.exp (Real.log ε) := by
          unfold barrier; exact Real.exp_le_exp.2 (by linarith)
      _ = ε := Real.exp_log hε
  have hbound : ∀ x ∈ Ico a b, u x = barrier ℓ k a x →
      u' x < k * barrier ℓ k a x * (ℓ * Real.exp (-(k * (x - a)))) := by
    intro x hx heq
    have hB := barrier_pos ℓ k a x
    have hf := hflow x hx (heq ▸ hB) (heq ▸ hle x (Ico_subset_Icc_self hx))
    rw [heq, neg_log_barrier] at hf
    have hpos : 0 < (k - K) * (barrier ℓ k a x * (ℓ * Real.exp (-(k * (x - a))))) :=
      mul_pos (sub_pos.2 hKk) (mul_pos hB (hP x))
    nlinarith [hpos, hf]
  have ha : u a ≤ barrier ℓ k a a := by
    rw [barrier, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]; exact h0
  intro x hx
  exact image_le_of_deriv_right_lt_deriv_boundary' (f := u) (f' := u') (a := a) (b := b)
    (B := barrier ℓ k a) (B' := fun x => k * barrier ℓ k a x * (ℓ * Real.exp (-(k * (x - a)))))
    (fun y hy => (hu y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hu y (Ico_subset_Icc_self hy)).hasDerivWithinAt)
    ha
    (fun y _ => (hasDerivAt_barrier ℓ k a y).continuousAt.continuousWithinAt)
    (fun y _ => (hasDerivAt_barrier ℓ k a y).hasDerivWithinAt)
    hbound hx

/-- **One basin step** (the Grönwall step on `log(1/u)`): from `u a ≤ 250 ε²` and `u′ ≤ K u log(1/u)` wherever
`0 < u ≤ ε` beyond `a`, with `K > 0`, `u ≤ ε` on `[a, a + stepLen K]`. DERIVED: `0` the sign. -/
theorem stay_in_basin {u u' : ℝ → ℝ} {K a : ℝ} (hK : 0 < K)
    (hu : ∀ x, a ≤ x → HasDerivAt u (u' x) x) (h0 : u a ≤ squareLevel)
    (hflow : ∀ x, a ≤ x → 0 < u x → u x ≤ basinSeed → u' x ≤ K * u x * (-Real.log (u x))) :
    ∀ x ∈ Icc a (a + stepLen K), u x ≤ basinSeed := by
  have hc := stepLen_pos hK
  have hR : 0 < Real.log stepRatio := Real.log_pos one_lt_stepRatio
  have hRpos : 0 < stepRatio := lt_trans one_pos one_lt_stepRatio
  have hL4 : 0 < Real.log squareLevel⁻¹ := Real.log_pos (by rw [squareLevel_eq]; norm_num)
  have hopen : ∀ x ∈ Ico a (a + stepLen K), u x ≤ basinSeed := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact h0.trans squareLevel_lt.le
    · have hxa : 0 < x - a := sub_pos.2 h
      have hKk : K < Real.log stepRatio / (x - a) := by
        rw [lt_div_iff₀ hxa]
        have h2 : x - a < Real.log stepRatio / K := by have := hx.2; rw [stepLen] at this; linarith
        rw [lt_div_iff₀ hK] at h2; linarith
      have hkx : Real.log stepRatio / (x - a) * (x - a) = Real.log stepRatio :=
        div_mul_cancel₀ _ hxa.ne'
      have hlev : Real.log squareLevel⁻¹ * Real.exp (-(Real.log stepRatio / (x - a) * (x - a)))
          = Real.log basinSeed⁻¹ := by
        rw [hkx, Real.exp_neg, Real.exp_log hRpos, stepRatio, inv_div]
        exact mul_div_cancel₀ _ hL4.ne'
      have hb := le_barrier (u := u) (u' := u') (K := K) (k := Real.log stepRatio / (x - a))
        (ε := basinSeed) (ℓ := Real.log squareLevel⁻¹) (a := a) (b := x) h.le
        (div_pos hR hxa).le hKk hL4 (fun y hy => hu y hy.1)
        (by rw [Real.log_inv, neg_neg, Real.exp_log squareLevel_pos]; exact h0) basinSeed_pos
        (by rw [hlev, Real.log_inv])
        (fun y hy h1 h2 => hflow y hy.1 h1 h2) x ⟨h.le, le_rfl⟩
      have e : barrier (Real.log squareLevel⁻¹) (Real.log stepRatio / (x - a)) a x = basinSeed := by
        rw [barrier, hlev, Real.log_inv, neg_neg, Real.exp_log basinSeed_pos]
      rw [e] at hb; exact hb
  intro x hx
  rcases eq_or_lt_of_le hx.2 with h | h
  · have hlim : Tendsto u (𝓝[<] x) (𝓝 (u x)) :=
      (hu x hx.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    have hmem : Iio x ∩ Ioi a ∈ 𝓝[<] x :=
      inter_mem_nhdsWithin _ (Ioi_mem_nhds (by rw [h]; linarith))
    filter_upwards [hmem] with y hy
    exact hopen y ⟨hy.2.le, h ▸ hy.1⟩
  · exact hopen x ⟨hx.1, h⟩

/-! ## 3. The input -/

variable {N : ℕ}

/-- **The relative Lipschitz bound in the basin**: at every `β ≥ β₀` and window `w ≥ 1` with `D(β, w) ≤ ε`,
`|∂_β D(β, w)| ≤ K D(β, w) log(1/D(β, w))`. A hypothesis; not proved for `SU(N)`.
DERIVED: `1` the least window index and the numerator of `1/D`. -/
def RelLip (N : ℕ) (β₀ K : ℝ) : Prop :=
  ∀ β : ℝ, β₀ ≤ β → ∀ w : ℕ, 1 ≤ w → CouplingTower.windowCoupling N β w ≤ basinSeed →
    |deriv (fun x => CouplingTower.windowCoupling N x w) β|
      ≤ K * CouplingTower.windowCoupling N β w * Real.log (1 / CouplingTower.windowCoupling N β w)

/-- **The one-sided form**, all that the proofs read. DERIVED: `1` the least window index and the numerator. -/
def RelLipUp (N : ℕ) (β₀ K : ℝ) : Prop :=
  ∀ β : ℝ, β₀ ≤ β → ∀ w : ℕ, 1 ≤ w → CouplingTower.windowCoupling N β w ≤ basinSeed →
    deriv (fun x => CouplingTower.windowCoupling N x w) β
      ≤ K * CouplingTower.windowCoupling N β w * Real.log (1 / CouplingTower.windowCoupling N β w)

/-- DERIVED: no numeral. -/
theorem relLipUp_of_relLip {β₀ K : ℝ} (h : RelLip N β₀ K) : RelLipUp N β₀ K :=
  fun β hβ w hw hD => (le_abs_self _).trans (h β hβ w hw hD)

/-- `log(1/d) ≥ log 1000 > 0` in the basin. DERIVED: `0` the sign; `1` the numerator; `1000` inherited from `DoublingSharp.rec_sharp` through `basinSeed`. -/
theorem log_inv_ge {d : ℝ} (hd : 0 < d) (hD : d ≤ basinSeed) : Real.log 1000 ≤ Real.log (1 / d) := by
  apply Real.log_le_log (by norm_num)
  rw [basinSeed] at hD
  rw [le_div_iff₀ hd]; linarith

/-- **Monotone in `K`**: the right side is `≥ 0` in the basin. DERIVED: `0` the sign; `1` the least window. -/
theorem relLipUp_mono (hN : N ≠ 0) {β₀ K K' : ℝ} (hβ₀ : 0 ≤ β₀) (hKK : K ≤ K')
    (h : RelLipUp N β₀ K) : RelLipUp N β₀ K' := by
  intro β hβ w hw hD
  refine (h β hβ w hw hD).trans ?_
  have h0 := CouplingTower.windowCoupling_nonneg hN (hβ₀.trans hβ) hw
  rcases eq_or_lt_of_le h0 with h1 | h1
  · rw [← h1]; simp
  · have hl := (log_thousand_pos.trans_le (log_inv_ge h1 hD)).le
    have := mul_nonneg h0 hl
    nlinarith [mul_le_mul_of_nonneg_right hKK this]

/-- `-log d` written as `log(1/d)`. DERIVED: `1` the numerator. -/
theorem log_one_div (d : ℝ) : Real.log (1 / d) = -Real.log d := by
  rw [one_div, Real.log_inv]

/-- **The Osgood form of `BetaFlow` at constant speed gives the bound** with factor `2` at `β₀ > 0`.
CHOSEN: `2`, any factor above `(1 + ε)(1 + ε/log 1000)`. DERIVED: `0` the sign; `1` the least window and the nat. -/
theorem relLipUp_of_osgoodFlow (hN : N ≠ 0) {β₀ K : ℝ} (hβ₀ : 0 < β₀) (hK : 0 ≤ K)
    (hF : BetaFlow.OsgoodFlow N β₀ (fun _ => K)) : RelLipUp N β₀ (2 * K) := by
  intro β hβ w hw hD
  have hβ0 : 0 < β := hβ₀.trans_le hβ
  have h0 := CouplingTower.windowCoupling_nonneg hN hβ0.le hw
  rcases eq_or_lt_of_le h0 with h1 | h1
  · -- `D = 0` at an interior point of `β ≥ 0`: a local minimum, so the derivative is `0`
    have hmin : IsLocalMin (fun x => CouplingTower.windowCoupling N x w) β := by
      filter_upwards [Ioi_mem_nhds hβ0] with x hx
      show CouplingTower.windowCoupling N β w ≤ CouplingTower.windowCoupling N x w
      rw [← h1]; exact CouplingTower.windowCoupling_nonneg hN (le_of_lt hx) hw
    rw [hmin.deriv_eq_zero, ← h1]; simp
  · set d := CouplingTower.windowCoupling N β w with hd
    have hf : deriv (fun x => CouplingTower.windowCoupling N x w) β
        ≤ K * d * (1 + d) * BetaFlow.occ d := hF w hw β hβ h1
    have hL : Real.log 1000 ≤ -Real.log d := by rw [← log_one_div]; exact log_inv_ge h1 hD
    have hL1 : 1 ≤ Real.log 1000 := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log 1000 :=
          Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
    have hocc : BetaFlow.occ d ≤ -Real.log d + d := by
      unfold BetaFlow.occ
      have e : 1 + d⁻¹ = d⁻¹ * (1 + d) := by rw [mul_add, mul_one, inv_mul_cancel₀ h1.ne']; ring
      rw [e, Real.log_mul (inv_ne_zero h1.ne') (ne_of_gt (by linarith)), Real.log_inv]
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + d)
      linarith
    have hd1 : d ≤ 1 / 1000 := by rw [basinSeed] at hD; exact hD
    have hocc0 : 0 ≤ BetaFlow.occ d := (BetaFlow.occ_pos h1).le
    have key : (1 + d) * BetaFlow.occ d ≤ 2 * (-Real.log d) := by
      have h2 : (1 + d) * BetaFlow.occ d ≤ (1 + d) * (-Real.log d + d) :=
        mul_le_mul_of_nonneg_left hocc (by linarith)
      have p1 := mul_nonneg (sub_nonneg.2 hd1) (by linarith : (0 : ℝ) ≤ -Real.log d)
      have p2 := mul_nonneg h0 (sub_nonneg.2 hd1)
      nlinarith [h2, hL, hL1, h0, hd1, p1, p2]
    rw [log_one_div]
    have hKd : 0 ≤ K * d := mul_nonneg hK h0
    have := mul_le_mul_of_nonneg_left key hKd
    calc deriv (fun x => CouplingTower.windowCoupling N x w) β ≤ K * d * (1 + d) * BetaFlow.occ d := hf
      _ = K * d * ((1 + d) * BetaFlow.occ d) := by ring
      _ ≤ K * d * (2 * (-Real.log d)) := this
      _ = 2 * K * d * (-Real.log d) := by ring

/-! ## 4. The reduction -/

/-- **The basin at window `k` reaches `b`** from the base `β₀`: `B_k ≥ b`. DERIVED: no numeral. -/
def InBasin (N : ℕ) (β₀ b : ℝ) (k : ℕ) : Prop :=
  ∀ β ∈ Icc β₀ b, CouplingTower.windowCoupling N β k ≤ basinSeed

/-- **(a) The squaring step**: `D(β, w) ≤ ε ⇒ D(β, w+1) ≤ 250 ε²`. Inherited: `250`, `1/1000`.
DERIVED: `1` the least window and the next window; `2` the square. -/
theorem next_le_squareLevel (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (h : CouplingTower.windowCoupling N β w ≤ basinSeed) :
    CouplingTower.windowCoupling N β (w + 1) ≤ squareLevel := by
  have h0 := CouplingTower.windowCoupling_nonneg hN hβ hw
  have hs := CouplingTower.windowCoupling_succ_le hN hβ hw (by rw [basinSeed] at h; exact h)
  have hsq := mul_le_mul h h h0 basinSeed_pos.le
  rw [squareLevel]; nlinarith [hs, hsq]

/-- **(a) Upward closure**: `B_{k+1} ≥ B_k`. DERIVED: `1` the least window and the next window. -/
theorem inBasin_succ (hN : N ≠ 0) {β₀ b : ℝ} {k : ℕ} (hβ₀ : 0 ≤ β₀) (hk : 1 ≤ k)
    (h : InBasin N β₀ b k) : InBasin N β₀ b (k + 1) :=
  fun β hβ => (next_le_squareLevel hN (hβ₀.trans hβ.1) hk (h β hβ)).trans squareLevel_lt.le

/-- **(c) The growth step**: under `RelLipUp N β₀ K`, `K > 0`, `B_{k+1} ≥ B_k + stepLen K`.
DERIVED: `1` the least window and the next window. -/
theorem inBasin_step (hN : N ≠ 0) {β₀ b K : ℝ} {k : ℕ} (hβ₀ : 0 ≤ β₀) (hb : β₀ ≤ b) (hk : 1 ≤ k)
    (hK : 0 < K) (hR : RelLipUp N β₀ K) (h : InBasin N β₀ b k) :
    InBasin N β₀ (b + stepLen K) (k + 1) := by
  intro β hβ
  rcases le_or_gt β b with hle | hlt
  · exact inBasin_succ hN hβ₀ hk h β ⟨hβ.1, hle⟩
  · have hst := stay_in_basin (u := fun x => CouplingTower.windowCoupling N x (k + 1))
      (u' := deriv fun x => CouplingTower.windowCoupling N x (k + 1)) (K := K) (a := b) hK
      (fun x _ => (CouplingTower.hasDerivAt_windowCoupling hN (k + 1) x).differentiableAt.hasDerivAt)
      (next_le_squareLevel hN (hβ₀.trans hb) hk (h b ⟨hb, le_rfl⟩))
      (fun x hx _ hD => by
        have := hR x (hb.trans hx) (k + 1) (by omega) hD
        rw [log_one_div] at this; exact this)
    exact hst β ⟨hlt.le, hβ.2⟩

/-- **(d) Iterated growth**: `B_{k+j} ≥ β₀ + j · stepLen K`. DERIVED: `0` the start of the count; `1` the step. -/
theorem inBasin_iter (hN : N ≠ 0) {β₀ K : ℝ} (hβ₀ : 0 ≤ β₀) (hK : 0 < K) (hR : RelLipUp N β₀ K)
    {k : ℕ} (hk : 1 ≤ k) (h : InBasin N β₀ β₀ k) :
    ∀ j : ℕ, InBasin N β₀ (β₀ + j * stepLen K) (k + j) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have hb : β₀ ≤ β₀ + (j : ℝ) * stepLen K :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) (stepLen_pos hK).le)
    have := inBasin_step hN hβ₀ hb (by omega) hK hR ih
    have e : β₀ + (j : ℝ) * stepLen K + stepLen K = β₀ + ((j + 1 : ℕ) : ℝ) * stepLen K := by
      push_cast; ring
    rw [← e]; exact this

/-- **The base window**: the vanishing read at `β₀` puts some window `k ≥ 1` in the basin at `β₀`.
DERIVED: `1` the least window. -/
theorem inBasin_of_vanishes (hN : N ≠ 0) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hV : StrongAnchor.Vanishes N β₀) :
    ∃ k : ℕ, 1 ≤ k ∧ InBasin N β₀ β₀ k := by
  obtain ⟨c, hc, hlt⟩ := (StrongAnchor.vanishes_iff_seed hN hβ₀).1 hV
  refine ⟨c, hc, fun β hβ => ?_⟩
  rw [le_antisymm hβ.2 hβ.1, basinSeed]; exact hlt.le

/-- **A window in the basin gives the vanishing read.** DERIVED: `1` the least window and the next window. -/
theorem vanishes_of_inBasin (hN : N ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {k : ℕ} (hk : 1 ≤ k)
    (hD : CouplingTower.windowCoupling N β k ≤ basinSeed) : StrongAnchor.Vanishes N β := by
  refine (StrongAnchor.vanishes_iff_seed hN hβ).2 ⟨k + 1, by omega, ?_⟩
  have := (next_le_squareLevel hN hβ hk hD).trans_lt squareLevel_lt
  rw [basinSeed] at this; exact this

/-- **The capstone at one base** (one-sided form): `Vanishes N β₀`, `RelLipUp N β₀ K`, `K > 0` give the vanishing
of the window coupling at every `β ≥ β₀`. DERIVED: `0` the limit. -/
theorem vanishes_of_relLipUp (hN : N ≠ 0) {β₀ K : ℝ} (hβ₀ : 0 ≤ β₀) (hK : 0 < K)
    (hV : StrongAnchor.Vanishes N β₀) (hR : RelLipUp N β₀ K) :
    ∀ β : ℝ, β₀ ≤ β → Tendsto (CouplingTower.windowCoupling N β) atTop (𝓝 0) := by
  obtain ⟨k, hk, hB⟩ := inBasin_of_vanishes hN hβ₀ hV
  intro β hβ
  have hc := stepLen_pos hK
  obtain ⟨j, hj⟩ := exists_nat_ge ((β - β₀) / stepLen K)
  have hle : β ≤ β₀ + j * stepLen K := by
    have := (div_le_iff₀ hc).1 hj; linarith
  exact vanishes_of_inBasin hN (hβ₀.trans hβ) (by omega) (inBasin_iter hN hβ₀ hK hR hk hB j β ⟨hβ, hle⟩)

/-- **The capstone at one base**: `Vanishes N β₀`, `RelLip N β₀ K`, `K > 0` give the vanishing at every `β ≥ β₀`.
DERIVED: `0` the limit. -/
theorem vanishes_of_relLip (hN : N ≠ 0) {β₀ K : ℝ} (hβ₀ : 0 ≤ β₀) (hK : 0 < K)
    (hV : StrongAnchor.Vanishes N β₀) (hR : RelLip N β₀ K) :
    ∀ β : ℝ, β₀ ≤ β → Tendsto (CouplingTower.windowCoupling N β) atTop (𝓝 0) :=
  vanishes_of_relLipUp hN hβ₀ hK hV (relLipUp_of_relLip hR)

/-- **`StrongEnd` at one base.** DERIVED: no numeral. -/
theorem strongEnd_of_relLip (hN : N ≠ 0) {β₀ K : ℝ} (hβ₀ : 0 ≤ β₀) (hK : 0 < K)
    (hV : StrongAnchor.Vanishes N β₀) (hR : RelLip N β₀ K) : CouplingTower.StrongEnd N :=
  ((eventually_ge_atTop β₀).mono fun β hβ => vanishes_of_relLip hN hβ₀ hK hV hR β hβ).frequently

/-- **The input near the strong end**: frequently as `β₀ → 0⁺`, some `K > 0` has `RelLip N β₀ K`.
DERIVED: `0` the lower end and the sign. -/
def RelLipNearZero (N : ℕ) : Prop :=
  ∃ᶠ β₀ in 𝓝[>] (0 : ℝ), ∃ K > 0, RelLip N β₀ K

/-- **A bound at every positive base is an instance.** DERIVED: `0` the lower end and the sign. -/
theorem relLipNearZero_of_forall (h : ∀ β₀ : ℝ, 0 < β₀ → ∃ K > 0, RelLip N β₀ K) : RelLipNearZero N := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∃ K > 0, RelLip N x K :=
    eventually_mem_nhdsWithin.mono fun β₀ hβ₀ => h β₀ hβ₀
  exact hev.frequently

/-- **The capstone**: under `RelLipNearZero N`, the window coupling tends to `0` at every `β ≥ 0`.
DERIVED: `0` the lower end and the limit. -/
theorem vanishes_of_relLipNearZero (hN : N ≠ 0) (h : RelLipNearZero N) :
    ∀ β : ℝ, 0 ≤ β → Tendsto (CouplingTower.windowCoupling N β) atTop (𝓝 0) := by
  obtain ⟨b, hb, hA⟩ := StrongAnchor.strongAnchor hN
  have hev1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < b := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < b ∧ 0 < x := hev1.and self_mem_nhdsWithin
  obtain ⟨β₀, ⟨K, hK, hR⟩, hlt, hpos⟩ := (h.and_eventually hev).exists
  intro β hβ
  rcases lt_or_ge β β₀ with h1 | h1
  · exact hA β hβ (h1.trans hlt)
  · exact vanishes_of_relLip hN hpos.le hK (hA β₀ hpos.le hlt) hR β h1

/-- **`StrongEnd` from the input near the strong end.** DERIVED: `0` the lower end. -/
theorem strongEnd_of_relLipNearZero (hN : N ≠ 0) (h : RelLipNearZero N) : CouplingTower.StrongEnd N :=
  StrongAnchor.strongEnd_of_noStall hN
    ((StrongAnchor.noStall_iff hN).2 (vanishes_of_relLipNearZero hN h))

/-! ## 5. Tests -/

/-- **The input from `β = 0` is trivial**: `RelLipUp N 0 K` with `K > 0` forces `D ≡ 0` at every window `w ≥ 1`
and every `β ≥ 0` (Osgood: `D(0, w) = 0` and `D log(1/D)` never leaves `0`). Proof-internal: the barrier rate `2K`
(any rate above `K`). DERIVED: `0` the lower end and the limit; `1` the least window. -/
theorem relLipUp_zero_trivial (hN : N ≠ 0) {K : ℝ} (hK : 0 < K) (hR : RelLipUp N 0 K) {w : ℕ}
    (hw : 1 ≤ w) {β : ℝ} (hβ : 0 ≤ β) : CouplingTower.windowCoupling N β w = 0 := by
  have h0 := CouplingTower.windowCoupling_nonneg hN hβ hw
  by_contra hne
  have hpos : 0 < CouplingTower.windowCoupling N β w := lt_of_le_of_ne h0 (Ne.symm hne)
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℝ, Real.log 1000 ≤ M ∧
      -M < Real.log (CouplingTower.windowCoupling N β w) := by
    refine ⟨Real.log 1000 + max 0 (-Real.log (CouplingTower.windowCoupling N β w)) + 1, ?_, ?_⟩
    · have := le_max_left 0 (-Real.log (CouplingTower.windowCoupling N β w)); linarith
    · have := le_max_right 0 (-Real.log (CouplingTower.windowCoupling N β w))
      have := log_thousand_pos; linarith
  have hMpos : 0 < M := log_thousand_pos.trans_le hM1
  have hE : M * Real.exp (2 * K * β) * Real.exp (-(2 * K * (β - 0))) = M := by
    rw [mul_assoc, ← Real.exp_add]; simp
  have hb := le_barrier (u := fun x => CouplingTower.windowCoupling N x w)
    (u' := deriv fun x => CouplingTower.windowCoupling N x w) (K := K) (k := 2 * K)
    (ε := basinSeed) (ℓ := M * Real.exp (2 * K * β)) (a := 0) (b := β) hβ (by linarith) (by linarith)
    (mul_pos hMpos (Real.exp_pos _))
    (fun x _ => (CouplingTower.hasDerivAt_windowCoupling hN w x).differentiableAt.hasDerivAt)
    (by
      show CouplingTower.windowCoupling N 0 w ≤ _
      rw [CouplingTower.windowCoupling_zero]; exact (Real.exp_pos _).le)
    basinSeed_pos
    (by rw [hE, basinSeed, one_div, Real.log_inv, neg_neg]; exact hM1)
    (fun x hx _ hD => by
      have := hR x hx.1 w hw hD
      rw [log_one_div] at this; exact this)
    β ⟨hβ, le_rfl⟩
  have e : barrier (M * Real.exp (2 * K * β)) (2 * K) 0 β = Real.exp (-M) := by
    rw [barrier, hE]
  rw [e] at hb
  have hlt : Real.exp (-M) < CouplingTower.windowCoupling N β w := by
    calc Real.exp (-M) < Real.exp (Real.log (CouplingTower.windowCoupling N β w)) :=
          Real.exp_lt_exp.2 hM2
      _ = CouplingTower.windowCoupling N β w := Real.exp_log hpos
  exact absurd hb (not_le.2 hlt)

/-- **The input from `β = 0` fails** for `N ≥ 2` at every `K > 0`: some window leaves the basin at weak coupling
(`ZoomDown.window_out_of_basin`). DERIVED: `2` the least rank; `1` the least window; `0` the lower end. -/
theorem not_relLip_zero (hN2 : 2 ≤ N) {K : ℝ} (hK : 0 < K) : ¬ RelLip N 0 K := by
  intro hR
  have hN : N ≠ 0 := by omega
  obtain ⟨β, hgt, hβ⟩ :=
    ((ZoomDown.window_out_of_basin hN2 (le_refl 1)).and (eventually_ge_atTop (0 : ℝ))).exists
  rw [relLipUp_zero_trivial hN hK (relLipUp_of_relLip hR) (le_refl 1) hβ] at hgt
  norm_num at hgt

/-- **The physical reading**: on `D = e^{−m(β) n}` with `n > 0` (`n = 2^w`), the bound
`|∂_β D| ≤ K D log(1/D)` is `|m′| ≤ K m`, the same at every window. DERIVED: `1` the numerator; `0` the sign. -/
theorem expFamily_bound_iff {m : ℝ → ℝ} {m' β : ℝ} (hm : HasDerivAt m m' β) {n : ℝ} (hn : 0 < n)
    (K : ℝ) :
    |deriv (fun x => Real.exp (-(m x * n))) β|
        ≤ K * Real.exp (-(m β * n)) * Real.log (1 / Real.exp (-(m β * n)))
      ↔ |m'| ≤ K * m β := by
  have hd : HasDerivAt (fun x => Real.exp (-(m x * n))) (Real.exp (-(m β * n)) * -(m' * n)) β :=
    (hm.mul_const n).neg.exp
  have he := Real.exp_pos (-(m β * n))
  rw [hd.deriv, log_one_div, Real.log_exp, neg_neg, abs_mul, abs_of_pos he, abs_neg, abs_mul,
    abs_of_pos hn]
  have hen := mul_pos he hn
  constructor
  · intro h
    have h2 : (Real.exp (-(m β * n)) * n) * |m'| ≤ (Real.exp (-(m β * n)) * n) * (K * m β) := by
      linarith
    exact le_of_mul_le_mul_left h2 hen
  · intro h
    have := mul_le_mul_of_nonneg_left h hen.le
    linarith

end MassGap.BasinGrowth

end

#print axioms MassGap.BasinGrowth.squareLevel_eq
#print axioms MassGap.BasinGrowth.squareLevel_eq_quarter
#print axioms MassGap.BasinGrowth.squareLevel_pos
#print axioms MassGap.BasinGrowth.basinSeed_pos
#print axioms MassGap.BasinGrowth.squareLevel_lt
#print axioms MassGap.BasinGrowth.stepRatio_eq
#print axioms MassGap.BasinGrowth.log_thousand_pos
#print axioms MassGap.BasinGrowth.one_lt_stepRatio
#print axioms MassGap.BasinGrowth.stepLen_eq
#print axioms MassGap.BasinGrowth.stepLen_pos
#print axioms MassGap.BasinGrowth.barrier_pos
#print axioms MassGap.BasinGrowth.neg_log_barrier
#print axioms MassGap.BasinGrowth.hasDerivAt_barrier
#print axioms MassGap.BasinGrowth.le_barrier
#print axioms MassGap.BasinGrowth.stay_in_basin
#print axioms MassGap.BasinGrowth.relLipUp_of_relLip
#print axioms MassGap.BasinGrowth.log_inv_ge
#print axioms MassGap.BasinGrowth.relLipUp_mono
#print axioms MassGap.BasinGrowth.log_one_div
#print axioms MassGap.BasinGrowth.relLipUp_of_osgoodFlow
#print axioms MassGap.BasinGrowth.next_le_squareLevel
#print axioms MassGap.BasinGrowth.inBasin_succ
#print axioms MassGap.BasinGrowth.inBasin_step
#print axioms MassGap.BasinGrowth.inBasin_iter
#print axioms MassGap.BasinGrowth.inBasin_of_vanishes
#print axioms MassGap.BasinGrowth.vanishes_of_inBasin
#print axioms MassGap.BasinGrowth.vanishes_of_relLipUp
#print axioms MassGap.BasinGrowth.vanishes_of_relLip
#print axioms MassGap.BasinGrowth.strongEnd_of_relLip
#print axioms MassGap.BasinGrowth.relLipNearZero_of_forall
#print axioms MassGap.BasinGrowth.vanishes_of_relLipNearZero
#print axioms MassGap.BasinGrowth.strongEnd_of_relLipNearZero
#print axioms MassGap.BasinGrowth.relLipUp_zero_trivial
#print axioms MassGap.BasinGrowth.not_relLip_zero
#print axioms MassGap.BasinGrowth.expFamily_bound_iff
