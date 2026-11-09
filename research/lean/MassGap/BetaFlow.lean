import Mathlib
import MassGap.StrongAnchor
import MassGap.FinalBridge

/-!
# MassGap.BetaFlow — a flow in the coupling: the inverse Bose occupation moves at bounded speed

An attack on the bridge by a flow in `β` at fixed window, in place of a flow in the zoom `w` at fixed `β`. Write
`D(β,w) = CouplingTower.windowCoupling N β w`, which is `≥ 0` at `β ≥ 0`, `w ≥ 1`, and `y(D) = log(1 + 1/D)`, positive
at every `D > 0`. The input is the Osgood form

  `∂_β D ≤ K(β) · D (1 + D) · log(1 + 1/D)` for `β ≥ β₀` at windows with `D > 0`,

equivalently `y′ ≥ −K y` (`hasDerivAt_occ`, `form_iff_occ_speed`). It has no threshold and no exempt region, and it
carries one function `K` that does not depend on the window. Declarations are in the namespace `MassGap.BetaFlow`.

`y` is the inverse of the Bose occupation: `bose x = 1/(e^x − 1)` has `y(bose x) = x` (`occ_bose`), and
`bose (y d) = d` (`bose_occ`).

## 1. Why this form

The form `|∂_β D| ≤ K(β) D` is wrong twice, and both are proved here. From `D(0,w) = 0` it forces `D ≡ 0`
(`naive_forces_trivial`). On the expected shape `D = bose(m(β) 2^w)`, `∂_β log D` grows with the window, so a
window-uniform `K` forces `m` constant (`no_uniform_K`). The Osgood form holds on that shape exactly when
`−m′ ≤ K m` (`boseFamily_form_iff`). `y` has no zero at finite `D`; the form `∂d ≤ K d log(1/d)`, whose logarithm has
a zero at `d = 1`, fails at a crossing with `m′ < 0` for every `K` (`sharp_form_fails`, `sharp_form_fails_toy`).

## 2. The abstract lemma (proved)

* `osgood_bound`, `osgood_bound_integral`: if `u a ≤ bose ℓ` with `ℓ > 0` and `u′ ≤ K u (1 + u) y(u)` wherever `u > 0`
  on `[a, b)`, then `u b ≤ bose (ℓ · exp(−∫_a^b K))`. No clamp, and no `u ≥ 0`, is needed: the start is stated through
  a level `ℓ`, every finite start has one (`ℓ = y(u a)` if `u a > 0`, any `ℓ` otherwise), and where `u ≤ 0` the
  barrier is already above `u`. `K` has no sign condition and is continuous on `[a, ∞)`.
* `osgood_log_bound`: the closed form `y(u a) · exp(−∫_a^b K) ≤ y(u b)` for `u a, u b > 0`.
* `osgood_zero_persists`: `u a ≤ 0` gives `u b ≤ 0`. The form never leaves `0`.

## 3. The named input and the theorem (proved)

* `OsgoodForm d β₀ K`, for any family `d`; `OsgoodFlow N β₀ K` is that form on the true `D`, at windows `w ≥ 1`.
* `window_bound`, `window_log_bound`: the closed form at each window; `K`, `ℓ` and the bound do not see `w`.
* `vanishes_of_osgoodFlow`: `Vanishes N β₀` and `OsgoodFlow N β₀ K` with `K` continuous on `[β₀, ∞)` give
  `Vanishes N β` at every `β ≥ β₀`. `strongEnd_of_osgoodFlow`: hence `StrongEnd N`. The proof reads no seed.

## 4. The base (proved in the tree; the hypothesis drops)

`Vanishes N β₀` is proved at positive couplings: `StrongAnchor.strongAnchor` gives it on `[0, b)` for an existential
`b > 0` (continuity at `β = 0`, where every window reads `0`), `StrongAnchor.exists_pos_vanishes` at one `β > 0`.
The base must sit at `β₀ > 0`: `osgoodFlow_at_zero_trivial` shows that `OsgoodFlow N 0 K` with `K` continuous on
`[0, ∞)` forces `D ≡ 0` at every window `w ≥ 1`. So the existential `b` is what the input has to meet:

* `OsgoodFromZero N`: frequently as `β₀ → 0⁺`, `OsgoodFlow N β₀ K` for a `K` continuous on `[β₀, ∞)`, which may
  depend on `β₀`. A `K` continuous on `(0, ∞)` that serves `(0, ∞)` is an instance.
* `vanishes_of_osgoodFromZero`: under it, `Vanishes N β` at every `β ≥ 0`, with no base hypothesis.
  `noStall_of_osgoodFromZero`, `strongEnd_of_osgoodFromZero`, `massReadOpens_of_osgoodFromZero`: the same read as
  `NoStall N`, `StrongEnd N` and the bridge `FinalBridge.MassReadOpens N`.

## 5. The unit of `D` (proved)

The `1` in `y` is the nat, the unit of `D`. With unit `c > 0` the cost is `unitCost c D = D (1 + D/c) log(1 + c/D)`,
and `unitCost 1 D = D (1 + D) y(D)` (`unitCost_one`). `unitCost_comparable`: the two costs agree up to a positive
factor `C` that depends on `c` only, at every `D > 0`. `osgoodForm_unit_change`: so for `K ≥ 0` the form in unit `1`
with `K` gives the form in unit `c` with `C K`, and conversely. The sign condition is needed for this argument;
`K < 0` is not covered.

## 6. Load tests (proved)

* `boseFamily m β w = bose (m(β) 2^w)`. `boseFamily_form_iff`: for `m` differentiable, the form is `−m′ ≤ K m` where
  `m > 0`, and `d > 0` exactly there. `boseFamily_form_of_ratio_bound`: `|m′/m| ≤ K` satisfies it.
* `no_uniform_K`: for `m > 0`, a window-uniform `|∂_β d| ≤ K d` forces `m` constant.
* `naive_forces_trivial`: on the true `D`, `|∂_β D| ≤ K D` from `β = 0` forces `D ≡ 0`, whatever `K`.
* `sharp_form_fails`: at `m 2^w = log 2` with `m′ < 0`, where `d = 1`, `∂d ≤ K d log(1/d)` fails for every `K`.
* `toyMass βc β = βc − β` (CHOSEN, a toy for `U(1)`: the mass reaches `0` at a finite `βc`, and `m′/m` is unbounded
  there). `toy_form_fails`: the form fails for every `K` bounded above near `βc`. `toy_no_continuous_K`: so for every
  `K` continuous on `[β₀, ∞)`. `toy_form_blowup`: it holds with `K = 1/(βc − β)`, which blows up at `βc`.
* `driftFamily` (CHOSEN): `bose (exp(w(w − β)))` vanishes at every `β`, and the form fails for every `K` at every
  `β₀` (`driftFamily_tendsto`, `drift_not_form`, `vanishing_does_not_give_form`).

## 7. The input as local data (proved), and the direction to the bridge

`osgoodFlow_iff_meanAction`: `OsgoodFlow N β₀ K` is the same statement with `∂_β D` replaced by the mean actions
`⟨S⟩_{2·2^w} − 16 ⟨S⟩_{2^w}`, the cut energy of `hasDerivAt_windowCoupling`.

The direction that exists is `OsgoodFromZero N ⇒ NoStall N ⇒ MassReadOpens N`. The converse has no proof: the
vanishing read at every coupling carries no information on `∂_β` at fixed window. On the chosen drift family the vanishing
read holds at every `β` and the form fails; whether `D` obeys the form is not shown.

## Parameters

| symbol | meaning |
|---|---|
| `N` | rank of `SU(N)` |
| `β`, `β₀`, `a`, `b` | couplings; `β₀` the base of the flow |
| `w` | window index; the window is the torus of side `2^w` |
| `K` | the speed of `log y`, a function of `β` only; no value is chosen |
| `ℓ` | a level: the start reads at most `bose ℓ` |
| `c` | a change of unit of `D`, arbitrary; its factor `C` is computed from it |
| `βc` | CHOSEN critical point of the toy, arbitrary |

DERIVED (module-wide): `0` the limit, the lower end, the ultralocal coupling, the zero mass and the signs; `1` the
least window index, and in `y` the nat, the unit of `D`, in `bose` the Bose denominator; `2` the doubling, `16 = 2⁴`;
`log 2` the crossing `d = 1`, where `y = log 2`; `ε` proof-internal, sent to `0`. Proof-internal in
`toy_form_fails`: `1/2`, any number below `1` (against `1 ≤ K t`). No tree constant appears in this module's
statements or proofs; the seed `1/1000` of `DoublingSharp` is inherited only inside the proved anchor it imports.

## What does not follow

`OsgoodFlow N β₀ K` is not proved for `SU(N)`, at any `β₀`, for any `K`. Nothing bounds `K` from above. What is shown
about `K` is negative: no `K` continuous on `[0, ∞)` works unless `D ≡ 0` at every window. Bounded `m′/m` for `SU(N)`
is an expectation, not a theorem here. The failure for `U(1)` is proved only of a chosen toy, not of the `U(1)` lattice
theory. The growth of `D` at fixed `w` as `β → ∞` is not proved, and whether the form holds at any window at
large `β` is not shown. Every theorem reaching `Vanishes`, `NoStall`, `StrongEnd` or `MassReadOpens` above carries the
hypothesis. The uniformity in `w` is the content of the hypothesis and is what remains to be proved. The anchor's `b`
is existential, so the input must hold at couplings arbitrarily close to `0`, or the input and the anchor do not meet.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.BetaFlow

open Filter Topology Set
open MassGap.CouplingTower

/-! ## 1. The occupation and its inverse -/

section Abstract

/-- **The inverse occupation** `y(d) = log(1 + 1/d)`. DERIVED: `1` the nat, the unit of `d`. -/
def occ (d : ℝ) : ℝ := Real.log (1 + d⁻¹)

/-- **The Bose occupation** `1/(e^x − 1)`. DERIVED: `1` the Bose denominator. -/
def bose (x : ℝ) : ℝ := (Real.exp x - 1)⁻¹

/-- DERIVED: `0` the sign; `1` the Bose denominator. -/
theorem bose_denom_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 :=
  sub_pos.2 (Real.one_lt_exp_iff.2 hx)

/-- DERIVED: `0` the sign. -/
theorem bose_pos {x : ℝ} (hx : 0 < x) : 0 < bose x := inv_pos.2 (bose_denom_pos hx)

/-- DERIVED: `0` the sign; `1` the Bose denominator. -/
theorem bose_nonpos {x : ℝ} (hx : x ≤ 0) : bose x ≤ 0 :=
  inv_nonpos.2 (sub_nonpos.2 (Real.exp_le_one_iff.2 hx))

/-- **`y` inverts the occupation.** DERIVED: `0` the sign; `1` the nat. -/
theorem occ_bose {x : ℝ} : occ (bose x) = x := by
  simp only [occ, bose, inv_inv, add_sub_cancel, Real.log_exp]

/-- **The occupation inverts `y`.** DERIVED: `0` the sign; `1` the nat. -/
theorem bose_occ {d : ℝ} (hd : 0 < d) : bose (occ d) = d := by
  have hp : 0 < 1 + d⁻¹ := by positivity
  simp only [bose, occ, Real.exp_log hp, add_sub_cancel_left, inv_inv]

/-- `y > 0`. DERIVED: `0` the sign; `1` the nat. -/
theorem occ_pos {d : ℝ} (hd : 0 < d) : 0 < occ d :=
  Real.log_pos (by have := inv_pos.2 hd; linarith)

/-- `y` is antitone on `d > 0`. DERIVED: `0` the sign; `1` the nat. -/
theorem occ_anti {d e : ℝ} (hd : 0 < d) (h : d ≤ e) : occ e ≤ occ d := by
  have he : 0 < e := hd.trans_le h
  have hi : e⁻¹ ≤ d⁻¹ := inv_anti₀ hd h
  exact Real.log_le_log (by positivity) (by linarith)

/-- A small algebraic identity for the derivative of the occupation. DERIVED: `1`, `2` the square. -/
theorem bose_deriv_alg {a : ℝ} (ha : a ≠ 0) : -(a + 1) / a ^ 2 = -(a⁻¹ * (1 + a⁻¹)) := by
  field_simp

/-- **The occupation solves `b′ = −b(1 + b)`.** DERIVED: `0` the sign; `1` the Bose denominator. -/
theorem hasDerivAt_bose {x : ℝ} (hx : 0 < x) : HasDerivAt bose (-(bose x * (1 + bose x))) x := by
  have hne : Real.exp x - 1 ≠ 0 := (bose_denom_pos hx).ne'
  have h : HasDerivAt (fun t => (Real.exp t - 1)⁻¹) (-Real.exp x / (Real.exp x - 1) ^ 2) x :=
    HasDerivAt.inv ((Real.hasDerivAt_exp x).sub_const 1) hne
  refine h.congr_deriv ?_
  have e := bose_deriv_alg hne
  rw [sub_add_cancel] at e
  exact e

/-- **`y′ = −u′/(u (1 + u))`.** DERIVED: `0` the sign; `1` the nat. -/
theorem hasDerivAt_occ {u : ℝ → ℝ} {u' x : ℝ} (hu : HasDerivAt u u' x) (h0 : 0 < u x) :
    HasDerivAt (fun s => occ (u s)) (-u' / (u x * (1 + u x))) x := by
  have hne : u x ≠ 0 := h0.ne'
  have h1 : HasDerivAt (fun s => (u s)⁻¹) (-u' / u x ^ 2) x := HasDerivAt.inv hu hne
  have h2 : HasDerivAt (fun s => 1 + (u s)⁻¹) (-u' / u x ^ 2) x := h1.const_add 1
  have hp : (1 + (u x)⁻¹) ≠ 0 := by positivity
  refine (h2.log hp).congr_deriv ?_
  have hq : 1 + u x ≠ 0 := by positivity
  have e : 1 + (u x)⁻¹ = (1 + u x) / u x := by field_simp; ring
  rw [e]
  field_simp

/-- **The form is `y′ ≥ −K y`**: for `d > 0`, `u′ ≤ K d (1 + d) y(d) ↔ −K y(d) ≤ −u′/(d (1 + d))`.
DERIVED: `0` the sign; `1` the nat. -/
theorem form_iff_occ_speed {u' k d : ℝ} (hd : 0 < d) :
    u' ≤ k * d * (1 + d) * occ d ↔ -k * occ d ≤ -u' / (d * (1 + d)) := by
  have hq : 0 < d * (1 + d) := by positivity
  rw [le_div_iff₀ hq]
  constructor <;> intro h <;> nlinarith [h]

/-- The barrier's exponent, proof-internal: `ℓ · exp(−(A s − A a) − ε (s − a))`. DERIVED: no numeral. -/
def barrierRate (ℓ a ε : ℝ) (A : ℝ → ℝ) (s : ℝ) : ℝ :=
  ℓ * Real.exp (-(A s - A a) - ε * (s - a))

/-- The exponent solves its linear equation. DERIVED: no numeral. -/
theorem hasDerivAt_barrierRate {ℓ a ε k x : ℝ} {A : ℝ → ℝ} (hA : HasDerivAt A k x) :
    HasDerivAt (barrierRate ℓ a ε A) (barrierRate ℓ a ε A x * (-k - ε)) x := by
  have h1 : HasDerivAt (fun s => -(A s - A a)) (-k) x := HasDerivAt.neg (hA.sub_const (A a))
  have h2 : HasDerivAt (fun s => ε * (s - a)) ε x := by
    have h := ((hasDerivAt_id' x).sub_const a).const_mul ε
    exact h.congr_deriv (by ring)
  have h3 : HasDerivAt (fun s => -(A s - A a) - ε * (s - a)) (-k - ε) x := h1.sub h2
  have h4 := h3.exp.const_mul ℓ
  exact h4.congr_deriv (by simp only [barrierRate]; ring)

/-- DERIVED: `0` the sign. -/
theorem barrierRate_self (ℓ a ε : ℝ) (A : ℝ → ℝ) : barrierRate ℓ a ε A a = ℓ := by
  simp [barrierRate]

/-- **The Osgood bound through an antiderivative**: if `u a ≤ bose ℓ`, `ℓ > 0`, and `u′ ≤ K u (1 + u) y(u)` wherever
`u > 0` on `[a, b)`, with `A′ = K`, then `u b ≤ bose (ℓ exp(−(A b − A a)))`. The barrier solves the equation with
`K + ε`, so it is strictly faster at a touching point; `ε → 0`. DERIVED: `0` the sign; `1` the nat. -/
theorem osgood_bound {u u' K A : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x) (hA : ∀ x ∈ Icc a b, HasDerivAt A (K x) x)
    (hℓ : 0 < ℓ) (h0 : u a ≤ bose ℓ)
    (hflow : ∀ x ∈ Ico a b, 0 < u x → u' x ≤ K x * u x * (1 + u x) * occ (u x)) :
    u b ≤ bose (ℓ * Real.exp (-(A b - A a))) := by
  have key : ∀ ε : ℝ, 0 < ε → u b ≤ bose (ℓ * Real.exp (-(A b - A a) - ε * (b - a))) := by
    intro ε hε
    have hPpos : ∀ x, 0 < barrierRate ℓ a ε A x := fun x => mul_pos hℓ (Real.exp_pos _)
    have hdB : ∀ x ∈ Icc a b, HasDerivAt (fun s => bose (barrierRate ℓ a ε A s))
        ((K x + ε) * bose (barrierRate ℓ a ε A x) * (1 + bose (barrierRate ℓ a ε A x))
          * barrierRate ℓ a ε A x) x := by
      intro x hx
      have h1 := (hasDerivAt_bose (hPpos x)).comp x (hasDerivAt_barrierRate (hA x hx))
      exact h1.congr_deriv (by ring)
    have hle := image_le_of_deriv_right_lt_deriv_boundary' (f := u) (f' := u') (a := a) (b := b)
      (B := fun s => bose (barrierRate ℓ a ε A s))
      (B' := fun x => (K x + ε) * bose (barrierRate ℓ a ε A x)
        * (1 + bose (barrierRate ℓ a ε A x)) * barrierRate ℓ a ε A x)
      (fun x hx => (hu x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hu x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (by show u a ≤ bose (barrierRate ℓ a ε A a); rw [barrierRate_self]; exact h0)
      (fun x hx => (hdB x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hdB x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
      (by
        intro x hx heq
        have hP := hPpos x
        have hB0 : 0 < bose (barrierRate ℓ a ε A x) := bose_pos hP
        have heq' : u x = bose (barrierRate ℓ a ε A x) := heq
        have hf := hflow x hx (heq' ▸ hB0)
        rw [heq', occ_bose] at hf
        have hpos : 0 < ε * bose (barrierRate ℓ a ε A x) * (1 + bose (barrierRate ℓ a ε A x))
            * barrierRate ℓ a ε A x := by positivity
        show u' x < (K x + ε) * bose (barrierRate ℓ a ε A x)
          * (1 + bose (barrierRate ℓ a ε A x)) * barrierRate ℓ a ε A x
        nlinarith [hpos, hf])
    have hb := hle (right_mem_Icc.2 hab)
    simpa only [barrierRate] using hb
  have hne : ℓ * Real.exp (-(A b - A a)) ≠ 0 := (mul_pos hℓ (Real.exp_pos _)).ne'
  have hc : ContinuousAt (fun ε : ℝ => bose (ℓ * Real.exp (-(A b - A a) - ε * (b - a)))) 0 := by
    have hg : Continuous fun ε : ℝ => Real.exp (ℓ * Real.exp (-(A b - A a) - ε * (b - a))) - 1 := by
      fun_prop
    have hg0 : Real.exp (ℓ * Real.exp (-(A b - A a) - (0 : ℝ) * (b - a))) - 1 ≠ 0 := by
      have e : -(A b - A a) - (0 : ℝ) * (b - a) = -(A b - A a) := by ring
      rw [e]
      exact (bose_denom_pos (mul_pos hℓ (Real.exp_pos _))).ne'
    exact hg.continuousAt.inv₀ hg0
  have ht : Tendsto (fun ε : ℝ => bose (ℓ * Real.exp (-(A b - A a) - ε * (b - a))))
      (𝓝[>] 0) (𝓝 (bose (ℓ * Real.exp (-(A b - A a))))) := by
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have e : -(A b - A a) - (0 : ℝ) * (b - a) = -(A b - A a) := by ring
    simpa only [e] using h
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

/-- A function continuous on `[a, ∞)` agrees there with a continuous function on `ℝ`. DERIVED: no numeral. -/
theorem exists_continuous_extension {K : ℝ → ℝ} {a : ℝ} (hK : ContinuousOn K (Ici a)) :
    ∃ K' : ℝ → ℝ, Continuous K' ∧ ∀ x, a ≤ x → K' x = K x :=
  ⟨fun x => K (max a x),
    hK.comp_continuous (continuous_const.max continuous_id) (fun x => le_max_left a x),
    fun x hx => by simp only [max_eq_right hx]⟩

/-- **The Osgood bound**: for `K` continuous on `[a, ∞)`, `u a ≤ bose ℓ`, `ℓ > 0`, and `u′ ≤ K u (1 + u) y(u)` wherever
`u > 0` on `[a, b)`, one has `u b ≤ bose (ℓ exp(−∫_a^b K))`. DERIVED: `0` the sign; `1` the nat. -/
theorem osgood_bound_integral {u u' K : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b)
    (hK : ContinuousOn K (Ici a)) (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hℓ : 0 < ℓ) (h0 : u a ≤ bose ℓ)
    (hflow : ∀ x ∈ Ico a b, 0 < u x → u' x ≤ K x * u x * (1 + u x) * occ (u x)) :
    u b ≤ bose (ℓ * Real.exp (-∫ x in a..b, K x)) := by
  obtain ⟨K', hK', hE⟩ := exists_continuous_extension hK
  have hA : ∀ x ∈ Icc a b, HasDerivAt (fun s => ∫ t in a..s, K' t) (K' x) x :=
    fun x _ => (hK'.integral_hasStrictDerivAt a x).hasDerivAt
  have h1 : u b ≤ bose (ℓ * Real.exp
      (-((∫ t in a..b, K' t) - ∫ t in a..a, K' t))) :=
    osgood_bound hab hu hA hℓ h0 (fun x hx h1 => by rw [hE x hx.1]; exact hflow x hx h1)
  have hint : (∫ t in a..b, K' t) = ∫ t in a..b, K t :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact hE x hx.1
  rw [intervalIntegral.integral_same, sub_zero, hint] at h1
  exact h1

/-- **The closed form**: `y(u a) · exp(−∫_a^b K) ≤ y(u b)`, for `u a, u b > 0`. DERIVED: `0` the sign; `1` the nat. -/
theorem osgood_log_bound {u u' K : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hK : ContinuousOn K (Ici a)) (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (ha0 : 0 < u a) (hb0 : 0 < u b)
    (hflow : ∀ x ∈ Ico a b, 0 < u x → u' x ≤ K x * u x * (1 + u x) * occ (u x)) :
    occ (u a) * Real.exp (-∫ x in a..b, K x) ≤ occ (u b) := by
  have hb := osgood_bound_integral hab hK hu (occ_pos ha0) (bose_occ ha0).ge hflow
  have h := occ_anti hb0 hb
  rwa [occ_bose] at h

/-- A level below any positive target. DERIVED: `1` the Bose denominator and the margin; `0` the sign. -/
theorem exists_level {E η : ℝ} (hE : 0 < E) (hη : 0 < η) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ bose (ℓ * E) < η := by
  have hq : 0 < 1 / η := by positivity
  refine ⟨(1 / η + 1) / E, by positivity, ?_⟩
  have e : (1 / η + 1) / E * E = 1 / η + 1 := div_mul_cancel₀ _ hE.ne'
  rw [e]
  have h := Real.add_one_le_exp (1 / η + 1)
  have ha : 1 / η < Real.exp (1 / η + 1) - 1 := by linarith
  have hpos : 0 < Real.exp (1 / η + 1) - 1 := hq.trans ha
  have h1 := (div_lt_iff₀ hη).1 ha
  show (Real.exp (1 / η + 1) - 1)⁻¹ < η
  rw [← one_div, div_lt_iff₀ hpos]
  linarith

/-- **The form never leaves `0`**: `u a ≤ 0` gives `u b ≤ 0`. DERIVED: `0` the sign; `1` the nat. -/
theorem osgood_zero_persists {u u' K : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hK : ContinuousOn K (Ici a)) (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x) (h0 : u a ≤ 0)
    (hflow : ∀ x ∈ Ico a b, 0 < u x → u' x ≤ K x * u x * (1 + u x) * occ (u x)) :
    u b ≤ 0 := by
  by_contra hc
  obtain ⟨ℓ, hℓ, hlt⟩ := exists_level (Real.exp_pos (-∫ x in a..b, K x)) (not_le.1 hc)
  have hb := osgood_bound_integral hab hK hu hℓ (h0.trans (bose_pos hℓ).le) hflow
  linarith

/-! ### The unit of `D` -/

/-- **The cost in unit `c`**: `D (1 + D/c) log(1 + c/D)`. DERIVED: `1` the nat, here scaled by `c`. -/
def unitCost (c D : ℝ) : ℝ := D * (1 + D / c) * Real.log (1 + c / D)

/-- In unit `1` the cost is `D (1 + D) y(D)`. DERIVED: `1` the nat. -/
theorem unitCost_one (D : ℝ) : unitCost 1 D = D * (1 + D) * occ D := by
  rw [unitCost, occ, div_one, one_div]

/-- The comparison for `c ≥ 1`; Bernoulli's inequality on the logarithm. DERIVED: `0` the sign; `1` the nat. -/
theorem unitCost_le_of_one_le {c D : ℝ} (hc : 1 ≤ c) (hD : 0 < D) :
    unitCost 1 D ≤ c * unitCost c D ∧ unitCost c D ≤ c * unitCost 1 D := by
  have hc0 : 0 < c := one_pos.trans_le hc
  have ht : 0 < 1 / D := by positivity
  have ht' : c / D = c * (1 / D) := by ring
  have hp1 : 0 < 1 + 1 / D := by positivity
  have hL1 : 0 < Real.log (1 + 1 / D) := Real.log_pos (by linarith)
  have hmono : Real.log (1 + 1 / D) ≤ Real.log (1 + c / D) := by
    refine Real.log_le_log hp1 ?_
    rw [ht']
    nlinarith
  have hLc : 0 < Real.log (1 + c / D) := hL1.trans_le hmono
  have hbern : Real.log (1 + c / D) ≤ c * Real.log (1 + 1 / D) := by
    have h := one_add_mul_self_le_rpow_one_add (s := 1 / D) (by linarith) hc
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_rpow hp1, ← ht'] at h2
    exact h2
  have hsplit : c * (1 + D / c) = c + D := by field_simp
  have hdc : D / c ≤ D := div_le_self hD.le hc
  have hdc0 : 0 < D / c := by positivity
  constructor
  · have e : c * unitCost c D = D * (c * (1 + D / c)) * Real.log (1 + c / D) := by
      simp only [unitCost]; ring
    rw [e, hsplit, unitCost, div_one]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hD.le) hmono hL1.le (by positivity)
  · have e : c * unitCost 1 D = D * (1 + D) * (c * Real.log (1 + 1 / D)) := by
      simp only [unitCost, div_one]; ring
    rw [e, unitCost]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hD.le) hbern hLc.le (by positivity)

/-- Rescaling: `unitCost c D = c · unitCost 1 (D/c)`. DERIVED: `1` the nat. -/
theorem unitCost_scale {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    unitCost c D = c * unitCost 1 (D / c) := by
  have e : 1 / (D / c) = c / D := by field_simp
  have e2 : c * (D / c) = D := by field_simp
  simp only [unitCost, div_one, e]
  calc D * (1 + D / c) * Real.log (1 + c / D)
      = (c * (D / c)) * (1 + D / c) * Real.log (1 + c / D) := by rw [e2]
    _ = _ := by ring

/-- Rescaling: `unitCost 1 D = c · unitCost (1/c) (D/c)`. DERIVED: `1` the nat. -/
theorem unitCost_scale_inv {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    unitCost 1 D = c * unitCost (1 / c) (D / c) := by
  have e : (1 / c) / (D / c) = 1 / D := by field_simp
  have e1 : (D / c) / (1 / c) = D := by field_simp
  have e2 : c * (D / c) = D := by field_simp
  simp only [unitCost, div_one, e, e1]
  calc D * (1 + D) * Real.log (1 + 1 / D)
      = (c * (D / c)) * (1 + D) * Real.log (1 + 1 / D) := by rw [e2]
    _ = _ := by ring

/-- **The unit does not change the class of costs**: for `c > 0` there is `C > 0`, computed from `c` alone, with
`unitCost 1 D ≤ C unitCost c D` and `unitCost c D ≤ C unitCost 1 D` at every `D > 0`. DERIVED: `0` the sign; `1` the
nat; `C = c` or `1/c`, whichever is `≥ 1`. -/
theorem unitCost_comparable {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 0 < D →
      unitCost 1 D ≤ C * unitCost c D ∧ unitCost c D ≤ C * unitCost 1 D := by
  rcases le_total 1 c with h | h
  · exact ⟨c, hc, fun D hD => unitCost_le_of_one_le h hD⟩
  · refine ⟨1 / c, by positivity, fun D hD => ?_⟩
    have hb : 1 ≤ 1 / c := (one_le_div hc).2 h
    have hE : 0 < D / c := by positivity
    obtain ⟨h1, h2⟩ := unitCost_le_of_one_le hb hE
    rw [unitCost_scale hc hD, unitCost_scale_inv hc hD]
    have hcc : c * (1 / c) = 1 := by field_simp
    constructor
    · calc c * unitCost (1 / c) (D / c)
          ≤ c * (1 / c * unitCost 1 (D / c)) := mul_le_mul_of_nonneg_left h2 hc.le
        _ = 1 / c * (c * unitCost 1 (D / c)) := by ring
    · calc c * unitCost 1 (D / c)
          ≤ c * (1 / c * unitCost (1 / c) (D / c)) := mul_le_mul_of_nonneg_left h1 hc.le
        _ = 1 / c * (c * unitCost (1 / c) (D / c)) := by ring

end Abstract

/-! ## 2. The named input and the theorem -/

/-- **The Osgood form of a family**: at windows `w ≥ 1` and `β ≥ β₀`, where `d > 0`,
`∂_β d ≤ K(β) · d (1 + d) · y(d)`. DERIVED: `1` the least window index and the nat; `0` the sign. -/
def OsgoodForm (d : ℝ → ℕ → ℝ) (β₀ : ℝ) (K : ℝ → ℝ) : Prop :=
  ∀ w : ℕ, 1 ≤ w → ∀ β : ℝ, β₀ ≤ β → 0 < d β w →
    deriv (fun x => d x w) β ≤ K β * d β w * (1 + d β w) * occ (d β w)

/-- The form in unit `c`. DERIVED: `1` the least window index; `0` the sign. -/
def OsgoodFormAt (c : ℝ) (d : ℝ → ℕ → ℝ) (β₀ : ℝ) (K : ℝ → ℝ) : Prop :=
  ∀ w : ℕ, 1 ≤ w → ∀ β : ℝ, β₀ ≤ β → 0 < d β w →
    deriv (fun x => d x w) β ≤ K β * unitCost c (d β w)

/-- **The form in unit `1` and the form in unit `c` are the same class**, up to a positive factor on `K ≥ 0`.
DERIVED: `0` the sign; `1` the nat. -/
theorem osgoodForm_unit_change {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℝ → ℕ → ℝ) (β₀ : ℝ) (K : ℝ → ℝ), (∀ β, 0 ≤ K β) →
      (OsgoodForm d β₀ K → OsgoodFormAt c d β₀ fun β => C * K β) ∧
      (OsgoodFormAt c d β₀ K → OsgoodForm d β₀ fun β => C * K β) := by
  obtain ⟨C, hC, h⟩ := unitCost_comparable hc
  refine ⟨C, hC, fun d β₀ K hK => ⟨fun hf w hw β hβ h0 => ?_, fun hf w hw β hβ h0 => ?_⟩⟩
  · calc deriv (fun x => d x w) β
        ≤ K β * d β w * (1 + d β w) * occ (d β w) := hf w hw β hβ h0
      _ = K β * unitCost 1 (d β w) := by rw [unitCost_one]; ring
      _ ≤ K β * (C * unitCost c (d β w)) := mul_le_mul_of_nonneg_left (h _ h0).1 (hK β)
      _ = C * K β * unitCost c (d β w) := by ring
  · calc deriv (fun x => d x w) β
        ≤ K β * unitCost c (d β w) := hf w hw β hβ h0
      _ ≤ K β * (C * unitCost 1 (d β w)) := mul_le_mul_of_nonneg_left (h _ h0).2 (hK β)
      _ = C * K β * d β w * (1 + d β w) * occ (d β w) := by rw [unitCost_one]; ring

/-- **(Osgood flow)**, assumed: the Osgood form on the window coupling. `K` does not see the window.
DERIVED: no numeral. -/
def OsgoodFlow (N : ℕ) (β₀ : ℝ) (K : ℝ → ℝ) : Prop :=
  OsgoodForm (windowCoupling N) β₀ K

variable {N : ℕ}

/-- **The bound at one window**, uniform in the window. DERIVED: `1` the least window index; `0` the sign. -/
theorem window_bound (hN : N ≠ 0) {β₀ β ℓ : ℝ} {K : ℝ → ℝ} (hK : ContinuousOn K (Ici β₀))
    (hF : OsgoodFlow N β₀ K) (hβ : β₀ ≤ β) {w : ℕ} (hw : 1 ≤ w) (hℓ : 0 < ℓ)
    (h0 : windowCoupling N β₀ w ≤ bose ℓ) :
    windowCoupling N β w ≤ bose (ℓ * Real.exp (-∫ x in β₀..β, K x)) :=
  osgood_bound_integral (u := fun x => windowCoupling N x w)
    (u' := deriv fun x => windowCoupling N x w) hβ hK
    (fun x _ => (hasDerivAt_windowCoupling hN w x).differentiableAt.hasDerivAt) hℓ h0
    (fun x hx h1 => hF w hw x hx.1 h1)

/-- **The closed form at one window**. DERIVED: `1` the least window index; `0` the sign. -/
theorem window_log_bound (hN : N ≠ 0) {β₀ β : ℝ} {K : ℝ → ℝ} (hK : ContinuousOn K (Ici β₀))
    (hF : OsgoodFlow N β₀ K) (hβ : β₀ ≤ β) {w : ℕ} (hw : 1 ≤ w)
    (h0 : 0 < windowCoupling N β₀ w) (hb : 0 < windowCoupling N β w) :
    occ (windowCoupling N β₀ w) * Real.exp (-∫ x in β₀..β, K x) ≤ occ (windowCoupling N β w) :=
  osgood_log_bound (u := fun x => windowCoupling N x w)
    (u' := deriv fun x => windowCoupling N x w) hβ hK
    (fun x _ => (hasDerivAt_windowCoupling hN w x).differentiableAt.hasDerivAt) h0 hb
    (fun x hx h1 => hF w hw x hx.1 h1)

/-- **The flow carries the vanishing read upward**: `Vanishes N β₀` and `OsgoodFlow N β₀ K` give `Vanishes N β` at
every `β ≥ β₀`. No threshold and no seed. DERIVED: `0` the lower end and the limit; `1` the least window index. -/
theorem vanishes_of_osgoodFlow (hN : N ≠ 0) {β₀ : ℝ} {K : ℝ → ℝ} (hβ₀ : 0 ≤ β₀)
    (hK : ContinuousOn K (Ici β₀)) (hF : OsgoodFlow N β₀ K) (hV : StrongAnchor.Vanishes N β₀) :
    ∀ β : ℝ, β₀ ≤ β → StrongAnchor.Vanishes N β := by
  intro β hβ
  have hV' : Tendsto (windowCoupling N β₀) atTop (𝓝 0) := hV
  show Tendsto (windowCoupling N β) atTop (𝓝 0)
  refine Metric.tendsto_nhds.2 fun η hη => ?_
  obtain ⟨ℓ, hℓ, hlt⟩ := exists_level (Real.exp_pos (-∫ x in β₀..β, K x)) hη
  have hev := hV'.eventually (eventually_lt_nhds (bose_pos hℓ))
  filter_upwards [hev, eventually_ge_atTop 1] with w h hw
  have hb := window_bound hN hK hF hβ hw hℓ h.le
  have hnn := windowCoupling_nonneg hN (hβ₀.trans hβ) hw
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hb.trans_lt hlt

/-- **The flow gives the strong end.** DERIVED: `0` the lower end. -/
theorem strongEnd_of_osgoodFlow (hN : N ≠ 0) {β₀ : ℝ} {K : ℝ → ℝ} (hβ₀ : 0 ≤ β₀)
    (hK : ContinuousOn K (Ici β₀)) (hF : OsgoodFlow N β₀ K) (hV : StrongAnchor.Vanishes N β₀) :
    StrongEnd N := by
  refine StrongAnchor.strongEnd_iff_frequently_vanishes.2 (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop β₀] with β hβ
  exact vanishes_of_osgoodFlow hN hβ₀ hK hF hV β hβ

/-! ## 3. The base -/

/-- **The flow cannot start at `β = 0`**: `OsgoodFlow N 0 K` with `K` continuous on `[0, ∞)` forces `D = 0` at every
window `w ≥ 1` and `β ≥ 0` (`windowCoupling_zero`, `osgood_zero_persists`). DERIVED: `0` the ultralocal coupling; `1`
the least window index. -/
theorem osgoodFlow_at_zero_trivial (hN : N ≠ 0) {K : ℝ → ℝ} (hK : ContinuousOn K (Ici 0))
    (hF : OsgoodFlow N 0 K) {w : ℕ} (hw : 1 ≤ w) {β : ℝ} (hβ : 0 ≤ β) :
    windowCoupling N β w = 0 := by
  refine le_antisymm ?_ (windowCoupling_nonneg hN hβ hw)
  exact osgood_zero_persists (u := fun x => windowCoupling N x w)
    (u' := deriv fun x => windowCoupling N x w) hβ hK
    (fun x _ => (hasDerivAt_windowCoupling hN w x).differentiableAt.hasDerivAt)
    (windowCoupling_zero N w).le (fun x hx h1 => hF w hw x hx.1 h1)

/-- **(Osgood flow from the anchor)**, assumed: frequently as `β₀ → 0⁺`, the flow holds from `β₀` for a `K`
continuous on `[β₀, ∞)`. `K` may depend on `β₀`, and it cannot extend continuously to `0`
(`osgoodFlow_at_zero_trivial`) for a non-trivial `D`. DERIVED: `0` the anchor's lower end. -/
def OsgoodFromZero (N : ℕ) : Prop :=
  ∃ᶠ β₀ in 𝓝[>] (0 : ℝ), ∃ K : ℝ → ℝ, ContinuousOn K (Ici β₀) ∧ OsgoodFlow N β₀ K

/-- **The base drops**: the proved anchor `StrongAnchor.strongAnchor` supplies `Vanishes N β₀`, so the flow alone
gives the read at every `β ≥ 0`. DERIVED: `0` the lower end. -/
theorem vanishes_of_osgoodFromZero (hN : N ≠ 0) (h : OsgoodFromZero N) :
    ∀ β : ℝ, 0 ≤ β → StrongAnchor.Vanishes N β := by
  obtain ⟨b, hb, hA⟩ := StrongAnchor.strongAnchor hN
  have hev1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < b := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < b ∧ 0 < x := hev1.and self_mem_nhdsWithin
  obtain ⟨β₀, ⟨K, hK, hF⟩, hlt, hpos⟩ := (Frequently.and_eventually h hev).exists
  intro β hβ
  by_cases hc : β < β₀
  · exact hA β hβ (hc.trans hlt)
  · exact vanishes_of_osgoodFlow hN hpos.le hK hF (hA β₀ hpos.le hlt) β (not_lt.1 hc)

/-- The flow from the anchor is at least `NoStall N`. DERIVED: no numeral. -/
theorem noStall_of_osgoodFromZero (hN : N ≠ 0) (h : OsgoodFromZero N) : StrongAnchor.NoStall N :=
  (StrongAnchor.noStall_iff hN).2 (vanishes_of_osgoodFromZero hN h)

/-- The flow from the anchor gives the strong end. DERIVED: `0` the lower end. -/
theorem strongEnd_of_osgoodFromZero (hN : N ≠ 0) (h : OsgoodFromZero N) : StrongEnd N := by
  refine StrongAnchor.strongEnd_iff_frequently_vanishes.2 (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  exact vanishes_of_osgoodFromZero hN h β hβ

/-- The flow from the anchor gives the bridge `B` (`FinalBridge.massReadOpens_of_noStall`).
DERIVED: `2` the least rank. -/
theorem massReadOpens_of_osgoodFromZero [NeZero N] (hN2 : 2 ≤ N) (h : OsgoodFromZero N) :
    FinalBridge.MassReadOpens N :=
  FinalBridge.massReadOpens_of_noStall hN2 (noStall_of_osgoodFromZero (NeZero.ne N) h)

/-! ## 4. Load tests -/

/-- **The expected shape**: the Bose occupation of `m(β) 2^w`. DERIVED: `2` the doubling. -/
def boseFamily (m : ℝ → ℝ) (β : ℝ) (w : ℕ) : ℝ := bose (m β * 2 ^ w)

/-- DERIVED: `2` the doubling. -/
theorem occ_boseFamily (m : ℝ → ℝ) (β : ℝ) (w : ℕ) : occ (boseFamily m β w) = m β * 2 ^ w :=
  occ_bose

/-- DERIVED: `0` the sign; `1` the nat; `2` the doubling. -/
theorem hasDerivAt_boseFamily {m : ℝ → ℝ} {m' β : ℝ} (w : ℕ) (hm : HasDerivAt m m' β)
    (hpos : 0 < m β * 2 ^ w) :
    HasDerivAt (fun x => boseFamily m x w)
      (-(boseFamily m β w * (1 + boseFamily m β w)) * (m' * 2 ^ w)) β :=
  (hasDerivAt_bose hpos).comp β (hm.mul_const ((2 : ℝ) ^ w))

/-- Cancel the positive window factor. DERIVED: `0` the sign; `1` the nat. -/
theorem family_core {m' K m p d : ℝ} (hp : 0 < p) (hd : 0 < d) :
    -(d * (1 + d)) * (m' * p) ≤ K * d * (1 + d) * (m * p) ↔ -m' ≤ K * m := by
  have hq : 0 < p * (d * (1 + d)) := by positivity
  have e1 : -(d * (1 + d)) * (m' * p) = -m' * (p * (d * (1 + d))) := by ring
  have e2 : K * d * (1 + d) * (m * p) = K * m * (p * (d * (1 + d))) := by ring
  rw [e1, e2]
  exact ⟨fun h => le_of_mul_le_mul_right h hq, fun h => mul_le_mul_of_nonneg_right h hq.le⟩

/-- **The form on the expected shape**: `−m′ ≤ K m` where `m > 0`, at `β ≥ β₀`. The window has gone. DERIVED: `0` the
zero mass; `1` the least window index and the nat; `2` the doubling. -/
theorem boseFamily_form_iff {m m' K : ℝ → ℝ} {β₀ : ℝ} (hm : ∀ β, HasDerivAt m (m' β) β) :
    OsgoodForm (boseFamily m) β₀ K ↔ ∀ β : ℝ, β₀ ≤ β → 0 < m β → -m' β ≤ K β * m β := by
  constructor
  · intro h β hβ hpos
    have hp : (0 : ℝ) < 2 ^ 1 := by norm_num
    have hlt := mul_pos hpos hp
    have hd : 0 < boseFamily m β 1 := bose_pos hlt
    have hf := h 1 le_rfl β hβ hd
    rw [(hasDerivAt_boseFamily 1 (hm β) hlt).deriv, occ_boseFamily] at hf
    exact (family_core hp hd).1 hf
  · intro h w _ β hβ h0
    have hp : (0 : ℝ) < 2 ^ w := by positivity
    have hlt : 0 < m β * 2 ^ w := by
      by_contra hc
      have h2 : boseFamily m β w ≤ 0 := bose_nonpos (not_lt.1 hc)
      linarith
    have hm0 : 0 < m β := (mul_pos_iff_of_pos_right hp).1 hlt
    rw [(hasDerivAt_boseFamily w (hm β) hlt).deriv, occ_boseFamily]
    exact (family_core hp h0).2 (h β hβ hm0)

/-- **Bounded `m′/m` satisfies the form.** DERIVED: `0` the zero mass. -/
theorem boseFamily_form_of_ratio_bound {m m' K : ℝ → ℝ} {β₀ : ℝ} (hm : ∀ β, HasDerivAt m (m' β) β)
    (hb : ∀ β : ℝ, β₀ ≤ β → 0 < m β → |m' β / m β| ≤ K β) : OsgoodForm (boseFamily m) β₀ K := by
  refine (boseFamily_form_iff hm).2 fun β hβ hpos => ?_
  have h := neg_le_of_abs_le (hb β hβ hpos)
  rw [le_div_iff₀ hpos] at h
  linarith

/-- **The naive form is not window-uniform**: for `m > 0`, `|∂_β d| ≤ K(β) d` at every window forces `m` constant.
DERIVED: `0` the derivative and the sign; `1`, `2` the doubling is unbounded. -/
theorem no_uniform_K {m K : ℝ → ℝ} (hm : Differentiable ℝ m) (hpos : ∀ β, 0 < m β)
    (h : ∀ (β : ℝ) (w : ℕ), |deriv (fun x => boseFamily m x w) β| ≤ K β * boseFamily m β w)
    (x y : ℝ) : m x = m y := by
  refine is_const_of_deriv_eq_zero hm (fun β => ?_) x y
  by_contra hne
  have hab : 0 < |deriv m β| := abs_pos.2 hne
  obtain ⟨w, hw⟩ := pow_unbounded_of_one_lt (K β / |deriv m β|) (one_lt_two : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ w := by positivity
  have hlt := mul_pos (hpos β) hp
  have hd : 0 < boseFamily m β w := bose_pos hlt
  have hb := h β w
  rw [(hasDerivAt_boseFamily w (hm β).hasDerivAt hlt).deriv, abs_mul, abs_neg, abs_mul, abs_mul,
    abs_of_pos hd, abs_of_pos (by positivity : 0 < 1 + boseFamily m β w), abs_of_pos hp] at hb
  have h1 : (1 + boseFamily m β w) * (|deriv m β| * 2 ^ w) ≤ K β := by
    refine le_of_mul_le_mul_right ?_ hd
    calc (1 + boseFamily m β w) * (|deriv m β| * 2 ^ w) * boseFamily m β w
        = boseFamily m β w * (1 + boseFamily m β w) * (|deriv m β| * 2 ^ w) := by ring
      _ ≤ K β * boseFamily m β w := hb
  have h2 : 0 < boseFamily m β w * (|deriv m β| * 2 ^ w) := by positivity
  rw [div_lt_iff₀ hab] at hw
  nlinarith [h1, h2, hw]

/-- **The naive form forces the trivial read**: `|∂_β D| ≤ K(β) D` from `β = 0`, with `K` continuous on `[0, ∞)` and
any values, gives `D = 0` along `β ≥ 0` at that window (`windowCoupling_zero` and Grönwall). DERIVED: `0` the
ultralocal coupling; `1` the least window index. -/
theorem naive_forces_trivial (hN : N ≠ 0) {K : ℝ → ℝ} (hK : ContinuousOn K (Ici 0)) {w : ℕ}
    (hw : 1 ≤ w)
    (h : ∀ β : ℝ, 0 ≤ β →
      |deriv (fun x => windowCoupling N x w) β| ≤ K β * windowCoupling N β w)
    {β : ℝ} (hβ : 0 ≤ β) : windowCoupling N β w = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := β)).exists_bound_of_continuousOn
    (hK.mono Icc_subset_Ici_self)
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun x => windowCoupling N x w) (f' := deriv fun x => windowCoupling N x w)
    (δ := 0) (K := C) (ε := 0) (a := 0) (b := β)
    (fun x _ => (hasDerivAt_windowCoupling hN w x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_windowCoupling hN w x).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (by simp [windowCoupling_zero])
    (by
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) β := Ico_subset_Icc_self hx
      have hnn := windowCoupling_nonneg hN hx.1 hw
      have hb := hC x hx'
      rw [Real.norm_eq_abs] at hb
      have h1 := h x hx.1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, add_zero]
      exact h1.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hb) hnn))
    β (right_mem_Icc.2 hβ)
  rw [gronwallBound_ε0_δ0] at hG
  exact norm_le_zero_iff.1 hG

/-- The crossing: `bose (log 2) = 1`. DERIVED: `2 = 1 + 1/d` at `d = 1`. -/
theorem bose_log_two : bose (Real.log 2) = 1 := by
  rw [bose, Real.exp_log two_pos]
  norm_num

/-- **The form with `log(1/d)` fails at the crossing**, for every `K`: on the Bose family at a window with
`m 2^w = log 2`, where `d = 1`, and `m′ < 0`, the bound `∂d ≤ K d log(1/d)` has right side `0` while `∂d > 0`.
DERIVED: `0` the sign; `1` the crossing; `2` the doubling and `1 + 1/d` at `d = 1`. -/
theorem sharp_form_fails {m : ℝ → ℝ} {m' β : ℝ} {w : ℕ} (hm : HasDerivAt m m' β) (hm' : m' < 0)
    (hc : m β * 2 ^ w = Real.log 2) (K : ℝ) :
    ¬ deriv (fun x => boseFamily m x w) β
        ≤ K * boseFamily m β w * Real.log (1 / boseFamily m β w) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hd : boseFamily m β w = 1 := by rw [boseFamily, hc, bose_log_two]
  have hp : (0 : ℝ) < 2 ^ w := by positivity
  rw [(hasDerivAt_boseFamily w hm (hc ▸ hlog)).deriv, hd]
  have h := mul_pos (neg_pos.2 hm') hp
  norm_num
  nlinarith [h]

/-- **The toy mass**, CHOSEN as a toy for `U(1)`: linear, reaching `0` at the finite `βc`. DERIVED: no numeral. -/
def toyMass (βc β : ℝ) : ℝ := βc - β

/-- DERIVED: `1` the slope. -/
theorem hasDerivAt_toyMass (βc β : ℝ) : HasDerivAt (toyMass βc) (-1) β := by
  show HasDerivAt (fun x => βc - x) (-1) β
  have h : HasDerivAt (fun x => βc - x) (0 - 1) β := (hasDerivAt_const β βc).sub (hasDerivAt_id' β)
  exact h.congr_deriv (by norm_num)

/-- **The crossing happens at every window of the toy**, so the form with `log(1/d)` has no `K` there.
DERIVED: `1` the slope; `2` the doubling and the crossing. -/
theorem sharp_form_fails_toy (βc : ℝ) (w : ℕ) (K : ℝ) :
    ∃ β : ℝ, ¬ deriv (fun x => boseFamily (toyMass βc) x w) β
      ≤ K * boseFamily (toyMass βc) β w * Real.log (1 / boseFamily (toyMass βc) β w) := by
  refine ⟨βc - Real.log 2 / 2 ^ w, sharp_form_fails (hasDerivAt_toyMass βc _) (by norm_num) ?_ K⟩
  have hp : (2 : ℝ) ^ w ≠ 0 := by positivity
  simp only [toyMass]
  field_simp
  ring

/-- **The toy fails for every `K` bounded near its critical point**. Proof-internal: `1/2`, any number below `1`.
DERIVED: `0` the zero mass; `1`, `2` the unit slope and the halving. -/
theorem toy_form_fails {βc β₀ C δ : ℝ} {K : ℝ → ℝ} (hβ₀ : β₀ < βc) (hδ : 0 < δ)
    (hK : ∀ β : ℝ, βc - δ < β → β < βc → K β ≤ C) :
    ¬ OsgoodForm (boseFamily (toyMass βc)) β₀ K := by
  intro h
  have h' : ∀ β : ℝ, β₀ ≤ β → 0 < toyMass βc β → (1 : ℝ) ≤ K β * toyMass βc β := by
    intro β hβ hp
    have hf := (boseFamily_form_iff (m' := fun _ => -1) (hasDerivAt_toyMass βc)).1 h β hβ hp
    calc (1 : ℝ) = -(-1) := by norm_num
      _ ≤ _ := hf
  have hCp : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨t, ht0, htδ, htβ, htC⟩ :
      ∃ t : ℝ, 0 < t ∧ t < δ ∧ t ≤ βc - β₀ ∧ max C 1 * t ≤ 1 / 2 := by
    have hq : 0 < 1 / (2 * max C 1) := div_pos one_pos (mul_pos two_pos hCp)
    refine ⟨min (min (δ / 2) (βc - β₀)) (1 / (2 * max C 1)),
      lt_min (lt_min (half_pos hδ) (sub_pos.2 hβ₀)) hq, ?_, ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · calc max C 1 * min (min (δ / 2) (βc - β₀)) (1 / (2 * max C 1))
          ≤ max C 1 * (1 / (2 * max C 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hCp.le
        _ = 1 / 2 := by field_simp
  have e : toyMass βc (βc - t) = t := by simp [toyMass]
  have hb := hK (βc - t) (by linarith) (by linarith)
  have h1 := h' (βc - t) (by linarith) (by rw [e]; exact ht0)
  rw [e] at h1
  have h2 : K (βc - t) * t ≤ max C 1 * t :=
    mul_le_mul_of_nonneg_right (hb.trans (le_max_left _ _)) ht0.le
  linarith

/-- **The toy fails for every `K` continuous on `[β₀, ∞)`**, by compactness of `[β₀, βc]`. DERIVED: no numeral. -/
theorem toy_no_continuous_K {βc β₀ : ℝ} {K : ℝ → ℝ} (hβ₀ : β₀ < βc)
    (hK : ContinuousOn K (Ici β₀)) : ¬ OsgoodForm (boseFamily (toyMass βc)) β₀ K := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := β₀) (b := βc)).exists_bound_of_continuousOn
    (hK.mono Icc_subset_Ici_self)
  refine toy_form_fails hβ₀ (sub_pos.2 hβ₀) (C := C) fun β h1 h2 => ?_
  have hb := hC β ⟨by linarith, h2.le⟩
  rw [Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb

/-- **The toy holds with a `K` that blows up at `βc`**, on all of `β ≥ β₀`. DERIVED: `0` the zero mass; `1` the unit
slope. -/
theorem toy_form_blowup (βc β₀ : ℝ) :
    OsgoodForm (boseFamily (toyMass βc)) β₀ (fun β => 1 / (βc - β)) := by
  refine (boseFamily_form_iff (m' := fun _ => -1) (hasDerivAt_toyMass βc)).2 fun β _ hp => ?_
  have hne : βc - β ≠ 0 := hp.ne'
  have e : (1 / (βc - β)) * toyMass βc β = 1 := by
    simp only [toyMass]
    field_simp
  show -(-1 : ℝ) ≤ (1 / (βc - β)) * toyMass βc β
  rw [e]
  norm_num

/-- **The drifting family**, CHOSEN: `y = exp(w(w − β))` has `∂_β log y = −w`, unbounded in `w`, while `y → ∞` at
every `β`. DERIVED: no numeral. -/
def driftFamily (β : ℝ) (w : ℕ) : ℝ := bose (Real.exp ((w : ℝ) * ((w : ℝ) - β)))

/-- DERIVED: `1` the nat. -/
theorem hasDerivAt_drift (β : ℝ) (w : ℕ) :
    HasDerivAt (fun x => driftFamily x w)
      (driftFamily β w * (1 + driftFamily β w) * (Real.exp ((w : ℝ) * ((w : ℝ) - β)) * (w : ℝ))) β := by
  have h0 : HasDerivAt (fun x : ℝ => (w : ℝ) - x) (0 - 1) β :=
    (hasDerivAt_const β (w : ℝ)).sub (hasDerivAt_id' β)
  have h1 : HasDerivAt (fun x : ℝ => (w : ℝ) * ((w : ℝ) - x)) (-(w : ℝ)) β :=
    (h0.const_mul (w : ℝ)).congr_deriv (by ring)
  have h2 := (hasDerivAt_bose (Real.exp_pos ((w : ℝ) * ((w : ℝ) - β)))).comp β h1.exp
  exact h2.congr_deriv (by simp only [driftFamily]; ring)

/-- **The occupation vanishes at infinity.** DERIVED: `0` the limit; `1` the Bose denominator. -/
theorem bose_tendsto : Tendsto bose atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.exp x + -1) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_add tendsto_const_nhds
  refine (tendsto_inv_atTop_zero.comp h1).congr fun x => ?_
  simp only [Function.comp, bose, sub_eq_add_neg]

/-- **The drifting family vanishes at every coupling.** DERIVED: `0` the limit. -/
theorem driftFamily_tendsto (β : ℝ) : Tendsto (driftFamily β) atTop (𝓝 0) := by
  have h1 : Tendsto (fun w : ℕ => (w : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun w : ℕ => (w : ℝ) + -β) atTop atTop := h1.atTop_add tendsto_const_nhds
  have h3 : Tendsto (fun w : ℕ => (w : ℝ) * ((w : ℝ) + -β)) atTop atTop :=
    h1.atTop_mul_atTop₀ h2
  have h4 := bose_tendsto.comp (Real.tendsto_exp_atTop.comp h3)
  refine h4.congr fun w => ?_
  simp only [driftFamily, Function.comp, sub_eq_add_neg]

/-- **The form fails on the drifting family**, for every `K` at every `β₀`: vanishing at every coupling does not
give the form. DERIVED: `0` the sign; `1` the least window index and the nat. -/
theorem drift_not_form (β₀ : ℝ) (K : ℝ → ℝ) : ¬ OsgoodForm driftFamily β₀ K := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (max (K β₀) 0)
  have hK : K β₀ < n := (le_max_left _ _).trans_lt hn
  have h0 : (0 : ℝ) < n := (le_max_right _ _).trans_lt hn
  have hn1 : 1 ≤ n := Nat.cast_pos.mp h0
  have hL : 0 < Real.exp ((n : ℝ) * ((n : ℝ) - β₀)) := Real.exp_pos _
  have hd0 : 0 < driftFamily β₀ n := bose_pos hL
  have hf := h n hn1 β₀ le_rfl hd0
  have hocc : occ (driftFamily β₀ n) = Real.exp ((n : ℝ) * ((n : ℝ) - β₀)) := occ_bose
  rw [(hasDerivAt_drift β₀ n).deriv, hocc] at hf
  have hp : 0 < driftFamily β₀ n * (1 + driftFamily β₀ n) * Real.exp ((n : ℝ) * ((n : ℝ) - β₀)) := by
    positivity
  have e1 : driftFamily β₀ n * (1 + driftFamily β₀ n) * (Real.exp ((n : ℝ) * ((n : ℝ) - β₀)) * (n : ℝ))
      = (n : ℝ) * (driftFamily β₀ n * (1 + driftFamily β₀ n) * Real.exp ((n : ℝ) * ((n : ℝ) - β₀))) := by
    ring
  have e2 : K β₀ * driftFamily β₀ n * (1 + driftFamily β₀ n) * Real.exp ((n : ℝ) * ((n : ℝ) - β₀))
      = K β₀ * (driftFamily β₀ n * (1 + driftFamily β₀ n) * Real.exp ((n : ℝ) * ((n : ℝ) - β₀))) := by
    ring
  rw [e1, e2] at hf
  exact absurd (le_of_mul_le_mul_right hf hp) (not_le.2 hK)

/-- **Vanishing at every coupling does not give the form**, on the chosen family. DERIVED: `0` the limit. -/
theorem vanishing_does_not_give_form :
    (∀ β : ℝ, Tendsto (driftFamily β) atTop (𝓝 0)) ∧
      ∀ (β₀ : ℝ) (K : ℝ → ℝ), ¬ OsgoodForm driftFamily β₀ K :=
  ⟨driftFamily_tendsto, drift_not_form⟩

/-! ## 5. The input as local data -/

/-- **The flow as mean actions**: `∂_β D` is the cut energy `⟨S⟩_{2·2^w} − 16⟨S⟩_{2^w}`.
DERIVED: `16 = 2⁴`, `2` the doubling; `0` the sign; `1` the least window index and the nat. -/
theorem osgoodFlow_iff_meanAction (hN : N ≠ 0) {β₀ : ℝ} {K : ℝ → ℝ} :
    OsgoodFlow N β₀ K ↔
      ∀ w : ℕ, 1 ≤ w → ∀ β : ℝ, β₀ ≤ β → 0 < windowCoupling N β w →
        EffectiveCoupling.meanAction N (fun _ => 2 * 2 ^ w) β
            - 16 * EffectiveCoupling.meanAction N (fun _ => 2 ^ w) β
          ≤ K β * windowCoupling N β w * (1 + windowCoupling N β w) * occ (windowCoupling N β w) := by
  constructor
  · intro h w hw β hβ h0
    have hf : deriv (fun x => windowCoupling N x w) β
        ≤ K β * windowCoupling N β w * (1 + windowCoupling N β w) * occ (windowCoupling N β w) :=
      h w hw β hβ h0
    rwa [(hasDerivAt_windowCoupling hN w β).deriv] at hf
  · intro h w hw β hβ h0
    show deriv (fun x => windowCoupling N x w) β ≤ _
    rw [(hasDerivAt_windowCoupling hN w β).deriv]
    exact h w hw β hβ h0

end MassGap.BetaFlow

end

#print axioms MassGap.BetaFlow.bose_denom_pos
#print axioms MassGap.BetaFlow.bose_pos
#print axioms MassGap.BetaFlow.bose_nonpos
#print axioms MassGap.BetaFlow.occ_bose
#print axioms MassGap.BetaFlow.bose_occ
#print axioms MassGap.BetaFlow.occ_pos
#print axioms MassGap.BetaFlow.occ_anti
#print axioms MassGap.BetaFlow.bose_deriv_alg
#print axioms MassGap.BetaFlow.hasDerivAt_bose
#print axioms MassGap.BetaFlow.hasDerivAt_occ
#print axioms MassGap.BetaFlow.form_iff_occ_speed
#print axioms MassGap.BetaFlow.hasDerivAt_barrierRate
#print axioms MassGap.BetaFlow.barrierRate_self
#print axioms MassGap.BetaFlow.osgood_bound
#print axioms MassGap.BetaFlow.exists_continuous_extension
#print axioms MassGap.BetaFlow.osgood_bound_integral
#print axioms MassGap.BetaFlow.osgood_log_bound
#print axioms MassGap.BetaFlow.exists_level
#print axioms MassGap.BetaFlow.osgood_zero_persists
#print axioms MassGap.BetaFlow.unitCost_one
#print axioms MassGap.BetaFlow.unitCost_le_of_one_le
#print axioms MassGap.BetaFlow.unitCost_scale
#print axioms MassGap.BetaFlow.unitCost_scale_inv
#print axioms MassGap.BetaFlow.unitCost_comparable
#print axioms MassGap.BetaFlow.osgoodForm_unit_change
#print axioms MassGap.BetaFlow.window_bound
#print axioms MassGap.BetaFlow.window_log_bound
#print axioms MassGap.BetaFlow.vanishes_of_osgoodFlow
#print axioms MassGap.BetaFlow.strongEnd_of_osgoodFlow
#print axioms MassGap.BetaFlow.osgoodFlow_at_zero_trivial
#print axioms MassGap.BetaFlow.vanishes_of_osgoodFromZero
#print axioms MassGap.BetaFlow.noStall_of_osgoodFromZero
#print axioms MassGap.BetaFlow.strongEnd_of_osgoodFromZero
#print axioms MassGap.BetaFlow.massReadOpens_of_osgoodFromZero
#print axioms MassGap.BetaFlow.occ_boseFamily
#print axioms MassGap.BetaFlow.hasDerivAt_boseFamily
#print axioms MassGap.BetaFlow.family_core
#print axioms MassGap.BetaFlow.boseFamily_form_iff
#print axioms MassGap.BetaFlow.boseFamily_form_of_ratio_bound
#print axioms MassGap.BetaFlow.no_uniform_K
#print axioms MassGap.BetaFlow.naive_forces_trivial
#print axioms MassGap.BetaFlow.bose_log_two
#print axioms MassGap.BetaFlow.sharp_form_fails
#print axioms MassGap.BetaFlow.hasDerivAt_toyMass
#print axioms MassGap.BetaFlow.sharp_form_fails_toy
#print axioms MassGap.BetaFlow.toy_form_fails
#print axioms MassGap.BetaFlow.toy_no_continuous_K
#print axioms MassGap.BetaFlow.toy_form_blowup
#print axioms MassGap.BetaFlow.hasDerivAt_drift
#print axioms MassGap.BetaFlow.bose_tendsto
#print axioms MassGap.BetaFlow.driftFamily_tendsto
#print axioms MassGap.BetaFlow.drift_not_form
#print axioms MassGap.BetaFlow.vanishing_does_not_give_form
#print axioms MassGap.BetaFlow.osgoodFlow_iff_meanAction
