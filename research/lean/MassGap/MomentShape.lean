import Mathlib
import MassGap.LogConvex
import MassGap.Substrate

/-!
# MassGap.MomentShape — circle symmetry of the lag correlation, and the shape log-convexity earns

Two facts about `ρ = corrClay`, both new here:

* **CIRCLE SYMMETRY**, `ρ(d) = ρ(−d)`, at EVERY extent and EVERY real coupling, with no hypothesis
  at all (`corrHyper_neg`, `corrClay_neg`, `wilsonCorrAt_neg`). Its useful form is
  `wilsonCorrAt_circLag_congr`: the correlation depends on the lag ONLY through `Moment.circLag`.
* **THE EVEN-LAG SHAPE.** At even extent `n = 2m` with `m ≥ 3`, and given nonnegativity, `ρ`
  restricted to the EVEN lags is non-increasing in `Moment.circLag` (`corrClay_even_antitone`), and
  the odd lags are bounded ABOVE by their two even neighbours (`corrClay_odd_le`).

## Why circle symmetry was worth proving

`Moment.circLag d = min d (n − d)` is built as if `ρ(d) = ρ(n − d)` held, and `Complete`'s docstrings
record it as ASSUMED — "no theorem in the tree asserts it of `wilsonCorrAt`, `corrClay`, `corrHyper`
or `wilsonCorrConn`". It is now a theorem, and it costs one line of geometry:
`LogConvex.EW_plaqE_pair_shift` at `P = 0`, `Q = d` reads `⟨φ₀ φ_d⟩ = ⟨φ₀ φ_{0−d}⟩` directly, and the
one-point term `corrHyper` subtracts does not move with the lag (`ReflectPositive.EW_plaqE_lag`). No
commutativity argument, no evenness, no sign condition on the coupling.

## What the log-convexity actually earns, and what it cannot

`LogConvex.corrClay_log_convex` gives `ρ(e₁+e₂)² ≤ ρ(2e₁)·ρ(2e₂)` for `e₁.val, e₂.val < m`. Writing
`g c = ρ(2c)`, the decomposition `(c−1) + (c+1) = 2c` turns that into `g(c)² ≤ g(c−1)·g(c+1)` — log
convexity of `g` — and circle symmetry makes `g` symmetric about `m/2`. A convex function with equal
endpoints is non-increasing on its first half, which is `corrClay_even_antitone`.

**THE ODD LAGS ARE BOUNDED ABOVE AND NEVER BELOW, AND THAT IS STRUCTURAL.** Every right-hand lag the
theorem produces is `2e`, hence EVEN. So the admissible set is closed under `ρ(d) ↦ t·ρ(d)` at the
ODD lags alone, for any `t ∈ [0,1]`: that scales the left side of an odd-midpoint constraint by `t²`
and leaves every right side untouched, and it preserves nonnegativity and circle symmetry, because on
an even period `d` and `n − d` have the same parity. `odd_scaling_admissible` proves exactly this.

The consequence is a no-go, not a gap to be filled later: NO theorem derived from log-convexity,
circle symmetry and nonnegativity can lower-bound `ρ` at an odd lag. `Moment.circLag = 1` is odd, so
`ρ(1) ≥ ρ(2)` is unreachable from this premise set, and `ρ` is NOT non-increasing in `circLag` as a
whole profile. `not_antitone_circLag_of_shape` exhibits the failure concretely at extent eight.

## This route does not reach the confinement criterion

`confinement_of_growth_ratio` needs `substrateRatio` below `(1 − 3^{−1/4})/(2π²) = 0.0121…`; the
unconditional bound is `Substrate.substrateRatio_le_quarter`. Nothing here improves that bound, and
this file proves no bound on `substrateRatio` at all — deliberately. Two reasons, either sufficient:

* at extent four the constraints are vacuous for the purpose. Only `ρ(1)² ≤ ρ(0)·ρ(2)` survives, and
  the antipodal point mass satisfies it while attaining `substrateRatio = 1/4` exactly
  (`Substrate.antipodeRead_moment_eq_quarter_sq`), so the theorem buys nothing over
  `substrateRatio_le_quarter` there;
* the best case this shape could ever describe is the FLAT correlation, and
  `Substrate.flatRead_exceeds_ceiling` already proves the flat read's ratio is above the ceiling at
  every aperture. A route whose best case was proved insufficient before the route was attempted has
  no payoff for the mass gap.

Foundational footprint only (`#print axioms` at the end). Nonnegativity is carried as an explicit
hypothesis rather than taken from `Complete.wilson_reflection_positive_at`, so no named axiom enters;
`corrClay_even_antitone_of_nonneg_coupling` discharges it from the PROVED
`Complete.wilson_reflection_positive_at_even` at nonnegative coupling.

Build: `python code/lean_build.py build MassGap.MomentShape`.
-/

namespace MassGap.MomentShape

open MeasureTheory
open MassGap MassGap.Reflect MassGap.WilsonHypercubic MassGap.ReflectionPositivity
open MassGap.WilsonLattice MassGap.CompactGauge MassGap.WilsonReal MassGap.WilsonAction
open MassGap.ActionSplit MassGap.ReflectPositive MassGap.WilsonBridge MassGap.LogConvex

/-! ## Part 1 — circle symmetry

`ρ(−d) = ρ(d)`. One application of `EW_plaqE_pair_shift` at constant `P = 0`, plus the fact that the
subtracted one-point function does not move with the lag. No hypothesis on the extent, the parity or
the coupling. -/

section Symmetry

variable {d n Nc : ℕ} [NeZero n]

/-- **THE CONNECTED LAG CORRELATION IS EVEN IN THE LAG.** `ρ(−d) = ρ(d)` on the periodic lattice, at
every extent and every real coupling.

`EW_plaqE_pair_shift hμ hν β 0 d` says `⟨φ₀ · φ_d⟩ = ⟨φ₀ · φ_{0−d}⟩` — the reflection at constant
zero carries the pair `(0, d)` to the pair `(0, −d)` — and `EW_plaqE_lag` says the one-point function
`corrHyper` subtracts is the same at `d`, at `−d` and at the origin. Subtracting the same number from
both sides of the first identity is the whole proof.

DERIVED: no numeral enters. The `0` is the base of the reflection, which is the origin because
`corrHyper` is based there. -/
theorem corrHyper_neg {μ ν τ : Fin d} (hμ : μ ≠ τ) (hν : ν ≠ τ) (β : ℝ) (lag : Fin n) :
    corrHyper (d := d) Nc n μ ν τ β (-lag) = corrHyper (d := d) Nc n μ ν τ β lag := by
  have hpair := EW_plaqE_pair_shift (n := n) (Nc := Nc) hμ hν β (0 : Fin n) lag
  rw [siteAtHyper_zero (d := d) (n := n) τ, zero_sub] at hpair
  rw [corrHyper_unfold Nc μ ν τ β (-lag), corrHyper_unfold Nc μ ν τ β lag,
    EW_plaqE_lag Nc hμ hν (-lag) β, EW_plaqE_lag Nc hμ hν lag β, ← hpair]

#print axioms corrHyper_neg

end Symmetry

section SymmetryClay

/-- **Circle symmetry of the Clay correlation** — `SU(3)`, four dimensions, every extent, every real
coupling, no hypothesis.

DERIVED: `3` is the gauge group's rank and `4` the dimension, both `WilsonBridge.corrClay`'s own. -/
theorem corrClay_neg (n : ℕ) [NeZero n] (β : ℝ) (lag : Fin n) :
    MassGap.WilsonBridge.corrClay n β (-lag) = MassGap.WilsonBridge.corrClay n β lag :=
  corrHyper_neg (Nc := 3) (d := 4) (n := n) (by decide) (by decide) β lag

#print axioms corrClay_neg

/-- The same on the aperture-carrying correlation the substrate read consumes.
`wilsonCorrAt N β = corrClay (N+1) β` by definition. -/
theorem wilsonCorrAt_neg (N : ℕ) (β : ℝ) (lag : Fin (N + 1)) :
    MassGap.wilsonCorrAt N β (-lag) = MassGap.wilsonCorrAt N β lag :=
  corrClay_neg (N + 1) β lag

#print axioms wilsonCorrAt_neg

/-- **Equal circle lags come from equal or opposite lags.** `circLag d = min d (n − d)`, so the fibre
over a value is `{d, −d}` and nothing else — the arithmetic behind `Moment.sum_circLag_le_two_mul`,
here as an identification rather than a count. -/
theorem eq_or_eq_neg_of_circLag_eq {N : ℕ} {d₁ d₂ : Fin (N + 1)}
    (h : Moment.circLag d₁ = Moment.circLag d₂) : d₁ = d₂ ∨ d₁ = -d₂ := by
  have h1 := d₁.isLt
  have h2 := d₂.isLt
  have hv : ((-d₂ : Fin (N + 1)) : ℕ) = (N + 1 - (d₂ : ℕ)) % (N + 1) := by
    simp [Fin.neg_def]
  unfold Moment.circLag at h
  rcases Nat.eq_zero_or_pos (d₂ : ℕ) with hb | hb
  · exact Or.inl (Fin.ext (by omega))
  · rcases (show (d₁ : ℕ) = (d₂ : ℕ) ∨ (d₁ : ℕ) = N + 1 - (d₂ : ℕ) by omega) with he | he
    · exact Or.inl (Fin.ext he)
    · refine Or.inr (Fin.ext ?_)
      rw [hv, Nat.mod_eq_of_lt (by omega)]
      exact he

#print axioms eq_or_eq_neg_of_circLag_eq

/-- **THE CORRELATION READS THE LAG ONLY THROUGH THE CIRCLE DISTANCE.**

    circLag d₁ = circLag d₂  ⟹  ρ(d₁) = ρ(d₂)

This is the statement `Moment.circLag` is BUILT as if it held, and which `Complete`'s docstrings
record as ASSUMED. It is now proved, at every aperture and every real coupling, from circle symmetry
alone. -/
theorem wilsonCorrAt_circLag_congr (N : ℕ) (β : ℝ) {d₁ d₂ : Fin (N + 1)}
    (h : Moment.circLag d₁ = Moment.circLag d₂) :
    MassGap.wilsonCorrAt N β d₁ = MassGap.wilsonCorrAt N β d₂ := by
  rcases eq_or_eq_neg_of_circLag_eq h with he | he
  · rw [he]
  · rw [he]; exact wilsonCorrAt_neg N β d₂

#print axioms wilsonCorrAt_circLag_congr

end SymmetryClay

/-! ## Part 2 — convex, symmetric, nonnegative: the shape lemma, abstractly

A nonnegative `g : ℕ → ℝ` that is log-convex on `[1, m−2]` and symmetric under `c ↦ m − c` is
non-increasing on the first half. Zeros are the only delicacy and they are handled by a dichotomy:
log-convexity propagates a zero UPWARD (`shape_zero_step`), and symmetry then pulls it back, so
either `g` is strictly positive throughout or it vanishes on the whole interior. -/

section Shape

variable {m : ℕ}

/-- **A zero propagates outward.** `g(c+1)² ≤ g(c)·g(c+2) = 0` forces `g(c+1) = 0`. -/
theorem shape_zero_step (g : ℕ → ℝ) (hg : ∀ c, 0 ≤ g c)
    (hconv : ∀ c, 1 ≤ c → c + 1 ≤ m → g c ^ 2 ≤ g (c - 1) * g (c + 1))
    {c : ℕ} (hc : c + 2 ≤ m) (h0 : g c = 0) : g (c + 1) = 0 := by
  have h := hconv (c + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at h
  rw [h0, zero_mul] at h
  exact sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))

#print axioms shape_zero_step

/-- **Log-convexity extends to the last interior point, through symmetry.** The theorem supplies
`g(c)² ≤ g(c−1)·g(c+1)` for `c + 2 ≤ m` directly; at `c = m − 1` the same inequality reads
`g(1)² ≤ g(2)·g(0)` once symmetry is applied to all three terms, which is the case `c = 1`. -/
theorem shape_conv_top (hm : 3 ≤ m) (g : ℕ → ℝ)
    (hsym : ∀ c, c ≤ m → g c = g (m - c))
    (hconv : ∀ c, 1 ≤ c → c + 2 ≤ m → g c ^ 2 ≤ g (c - 1) * g (c + 1)) :
    ∀ c, 1 ≤ c → c + 1 ≤ m → g c ^ 2 ≤ g (c - 1) * g (c + 1) := by
  intro k hk1 hk2
  rcases Nat.lt_or_ge (k + 1) m with h | h
  · exact hconv k hk1 (by omega)
  · have hkm : k = m - 1 := by omega
    subst hkm
    have e1 : g (m - 1) = g 1 := (hsym 1 (by omega)).symm
    have e2 : g (m - 1 - 1) = g 2 := by
      have hr : m - 1 - 1 = m - 2 := by omega
      rw [hr]; exact (hsym 2 (by omega)).symm
    have e3 : g (m - 1 + 1) = g 0 := by
      have hr : m - 1 + 1 = m - 0 := by omega
      rw [hr]; exact (hsym 0 (by omega)).symm
    rw [e1, e2, e3, mul_comm]
    exact hconv 1 le_rfl (by omega)

#print axioms shape_conv_top

/-- **CONVEX PLUS SYMMETRIC IS NON-INCREASING ON THE FIRST HALF**, one step at a time.

Log-convexity makes the ratios `g(c+1)/g(c)` non-decreasing; symmetry makes the ratio at `c` the
reciprocal of the ratio at `m − 1 − c`. Below the midpoint the first is at most the second, so it is
at most its own reciprocal, hence at most one. Zeros are handled by the dichotomy above.

DERIVED: nothing is chosen. `m` is half the extent, carried in from the reflection geometry, and
`2c + 1 ≤ m` is exactly "below the midpoint". -/
theorem shape_step (hm : 3 ≤ m) (g : ℕ → ℝ) (hg : ∀ c, 0 ≤ g c)
    (hsym : ∀ c, c ≤ m → g c = g (m - c))
    (hconv : ∀ c, 1 ≤ c → c + 2 ≤ m → g c ^ 2 ≤ g (c - 1) * g (c + 1))
    (c : ℕ) (hc : 2 * c + 1 ≤ m) : g (c + 1) ≤ g c := by
  have hconv' := shape_conv_top hm g hsym hconv
  by_cases hposall : ∀ k, k ≤ m → 0 < g k
  · -- every value is strictly positive: divide
    have hratio : ∀ k, k + 2 ≤ m → g (k + 1) * g (k + 1) ≤ g k * g (k + 1 + 1) := by
      intro k hk
      have h := hconv' (k + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at h
      nlinarith [h]
    have hmono : ∀ i j, i ≤ j → j + 1 ≤ m → g (i + 1) / g i ≤ g (j + 1) / g j := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ j hij ih =>
        intro hj
        have h1 : g (i + 1) / g i ≤ g (j + 1) / g j := ih (by omega)
        have h2 : g (j + 1) / g j ≤ g (j + 1 + 1) / g (j + 1) := by
          rw [div_le_div_iff₀ (hposall j (by omega)) (hposall (j + 1) (by omega))]
          nlinarith [hratio j (by omega)]
        linarith
    have hsymr : ∀ k, k + 1 ≤ m → g (m - 1 - k + 1) / g (m - 1 - k) = g k / g (k + 1) := by
      intro k hk
      have e1 : m - 1 - k + 1 = m - k := by omega
      have e2 : g (m - k) = g k := (hsym k (by omega)).symm
      have e3 : g (m - 1 - k) = g (k + 1) := by
        have hr : m - 1 - k = m - (k + 1) := by omega
        rw [hr]; exact (hsym (k + 1) (by omega)).symm
      rw [e1, e2, e3]
    have hkey := hmono c (m - 1 - c) (by omega) (by omega)
    rw [hsymr c (by omega)] at hkey
    rw [div_le_div_iff₀ (hposall c (by omega)) (hposall (c + 1) (by omega))] at hkey
    nlinarith [hposall c (show c ≤ m by omega), hposall (c + 1) (show c + 1 ≤ m by omega), hkey]
  · -- some value vanishes: then the whole interior does
    push Not at hposall
    obtain ⟨k0, hk0m, hk0⟩ := hposall
    have hk0z : g k0 = 0 := le_antisymm hk0 (hg k0)
    obtain ⟨k1, hk1m, hk1z⟩ : ∃ k1, k1 + 1 ≤ m ∧ g k1 = 0 := by
      rcases Nat.lt_or_ge k0 m with h | h
      · exact ⟨k0, by omega, hk0z⟩
      · have hkm : k0 = m := by omega
        refine ⟨0, by omega, ?_⟩
        have h0 := hsym 0 (by omega)
        rw [Nat.sub_zero] at h0
        rw [h0, ← hkm]; exact hk0z
    have hup : ∀ j, k1 ≤ j → j + 1 ≤ m → g j = 0 := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; exact hk1z
      | succ j hj ih =>
        intro hj1
        exact shape_zero_step g hg hconv' (by omega) (ih (by omega))
    have hmm1 : g (m - 1) = 0 := hup (m - 1) (by omega) (by omega)
    have hone : g 1 = 0 := by rw [hsym 1 (by omega)]; exact hmm1
    have hall : ∀ j, 1 ≤ j → j + 1 ≤ m → g j = 0 := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; exact hone
      | succ j hj ih =>
        intro hj1
        exact shape_zero_step g hg hconv' (by omega) (ih (by omega))
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · subst hc0
      rw [hone]
      exact hg 0
    · rw [hall c hc0 (by omega), hall (c + 1) (by omega) (by omega)]

#print axioms shape_step

/-- The step statement chained: non-increasing across the whole first half. -/
theorem shape_antitone (hm : 3 ≤ m) (g : ℕ → ℝ) (hg : ∀ c, 0 ≤ g c)
    (hsym : ∀ c, c ≤ m → g c = g (m - c))
    (hconv : ∀ c, 1 ≤ c → c + 2 ≤ m → g c ^ 2 ≤ g (c - 1) * g (c + 1))
    (c₁ c₂ : ℕ) (h12 : c₁ ≤ c₂) (hc : 2 * c₂ ≤ m) : g c₂ ≤ g c₁ := by
  induction c₂, h12 using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact le_trans (shape_step hm g hg hsym hconv j (by omega)) (ih (by omega))

#print axioms shape_antitone

end Shape

/-! ## Part 3 — the shape, on the Wilson correlation

`g c = ρ(2c)` carries the hypotheses of Part 2: nonnegativity is the caller's, symmetry is Part 1,
and log-convexity is `LogConvex.corrClay_log_convex` at `e₁ = c − 1`, `e₂ = c + 1`. -/

section EvenShape

variable {Nap m : ℕ}

/-- The lag `c`, reduced into `Fin (Nap + 1)`. Written out rather than as a numeral cast because
`Fin (Nap + 1)` carries its additive group but no `NatCast` instance.

DERIVED: `Nap + 1` is the LAG ARITY at aperture `Nap` — `wilsonCorrAt`'s own index type, one index
per lag with the extra `1` being the contact lag `0` — so the `+ 1` counts a lag rather than shifting
a scale. The same `Nap + 1` is the modulus because that arity IS the period of the circle the lags
live on: `finOf_period` records `finOf Nap (Nap + 1) = 0`, and `finOf_add` that reduction commutes
with addition, which is the whole reason the reduction is written at all. `Nat.succ_pos` is what
makes it total. No magnitude. -/
def finOf (Nap c : ℕ) : Fin (Nap + 1) := ⟨c % (Nap + 1), Nat.mod_lt _ (Nat.succ_pos Nap)⟩

@[simp] theorem finOf_val (Nap c : ℕ) : (finOf Nap c : ℕ) = c % (Nap + 1) := rfl

theorem finOf_val_of_lt {Nap c : ℕ} (h : c < Nap + 1) : (finOf Nap c : ℕ) = c :=
  Nat.mod_eq_of_lt h

theorem finOf_add (Nap a b : ℕ) : finOf Nap a + finOf Nap b = finOf Nap (a + b) := by
  apply Fin.ext
  rw [Fin.val_add, finOf_val, finOf_val, finOf_val]
  exact (Nat.add_mod a b (Nap + 1)).symm

theorem finOf_period (Nap : ℕ) : finOf Nap (Nap + 1) = 0 := by
  apply Fin.ext
  rw [finOf_val, Nat.mod_self]
  rfl

/-- The even lag `2c`, as an element of `Fin (Nap + 1)`.

DERIVED: the only numeral in the definition is `finOf`'s `Nap + 1`, the lag arity, carried through
unchanged. The doubling is written as `finOf Nap c + finOf Nap c` in `Fin (Nap + 1)`'s own additive
group rather than as a numeral, and `ev_eq` proves it equals `finOf Nap (2 * c)`. The step of `2` is
not chosen here either: `LogConvex.corrClay_log_convex` produces its right-hand lags as `2e₁` and
`2e₂`, always even, so the even sublattice is the set of lags the constraint actually reaches —
`odd_scaling_admissible` below turns that observation into a theorem. -/
def ev (Nap c : ℕ) : Fin (Nap + 1) := finOf Nap c + finOf Nap c

theorem ev_eq (Nap c : ℕ) : ev Nap c = finOf Nap (2 * c) := by
  rw [ev, finOf_add]
  congr 1
  ring

/-- **The even lag `2c` really does sit at circle distance `2c`**, while it is inside the half range.
Recorded so that "non-increasing in `circLag`" below is a statement about the circle distance and not
about the raw index. -/
theorem circLag_ev (hm : Nap + 1 = 2 * m) (c : ℕ) (hc : 2 * c ≤ m) :
    Moment.circLag (ev Nap c) = 2 * c := by
  have hv : ((ev Nap c : Fin (Nap + 1)) : ℕ) = 2 * c := by
    rw [ev_eq]; exact finOf_val_of_lt (by omega)
  unfold Moment.circLag
  omega

#print axioms circLag_ev

/-- **THE EVEN LAGS ARE NON-INCREASING IN THE CIRCLE DISTANCE.**

    2c₂ ≤ m  and  c₁ ≤ c₂   ⟹   ρ(2c₂) ≤ ρ(2c₁)

at even extent `n = 2m` with `m ≥ 3`, for every real coupling, given nonnegativity. `circLag_ev`
says the indices sit at circle distances `2c₁ ≤ 2c₂`, so this is exactly "non-increasing in
`Moment.circLag`, over the even lags".

WHY ONLY THE EVEN LAGS. The right-hand lags `LogConvex.corrClay_log_convex` produces are `2e₁` and
`2e₂`, always even, so the odd lags never appear on the right of any constraint and are bounded above
only — see `odd_scaling_admissible`, which turns that observation into a theorem. This is NOT a
partial result on the way to a monotone profile: the whole profile is not monotone in `circLag` and
`not_antitone_circLag_of_shape` shows it.

DERIVED: `m` is half the extent, the reflection geometry's own bound, carried in from
`corrClay_log_convex`. `m ≥ 3` is where the hypotheses stop being vacuous — at `m = 2` the only
surviving constraint is `ρ(1)² ≤ ρ(0)·ρ(2)`, which says nothing about the even lags at all. No
constant is introduced. -/
theorem corrClay_even_antitone (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m) (β : ℝ)
    (hρ : ∀ d : Fin (Nap + 1), 0 ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β d)
    (c₁ c₂ : ℕ) (h12 : c₁ ≤ c₂) (hc : 2 * c₂ ≤ m) :
    MassGap.WilsonBridge.corrClay (Nap + 1) β (ev Nap c₂)
      ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β (ev Nap c₁) := by
  set g : ℕ → ℝ := fun c => MassGap.WilsonBridge.corrClay (Nap + 1) β (ev Nap c) with hgdef
  have hg : ∀ c, 0 ≤ g c := fun c => hρ _
  have hsym : ∀ c, c ≤ m → g c = g (m - c) := by
    intro c hcm
    have hneg : ev Nap (m - c) = -(ev Nap c) := by
      have h0 : ev Nap (m - c) + ev Nap c = 0 := by
        rw [ev_eq, ev_eq, finOf_add]
        have harith : 2 * (m - c) + 2 * c = Nap + 1 := by omega
        rw [harith, finOf_period]
      calc ev Nap (m - c) = ev Nap (m - c) + ev Nap c - ev Nap c := by abel
        _ = 0 - ev Nap c := by rw [h0]
        _ = -(ev Nap c) := by abel
    show MassGap.WilsonBridge.corrClay (Nap + 1) β (ev Nap c)
      = MassGap.WilsonBridge.corrClay (Nap + 1) β (ev Nap (m - c))
    rw [hneg, corrClay_neg]
  have hconv : ∀ c, 1 ≤ c → c + 2 ≤ m → g c ^ 2 ≤ g (c - 1) * g (c + 1) := by
    intro c hc1 hc2
    have hlt1 : ((finOf Nap (c - 1) : Fin (Nap + 1)) : ℕ) < m := by
      rw [finOf_val_of_lt (by omega)]; omega
    have hlt2 : ((finOf Nap (c + 1) : Fin (Nap + 1)) : ℕ) < m := by
      rw [finOf_val_of_lt (by omega)]; omega
    have h := MassGap.LogConvex.corrClay_log_convex Nap m hm (by omega) β
      (e₁ := finOf Nap (c - 1)) (e₂ := finOf Nap (c + 1)) hlt1 hlt2
    have hmid : finOf Nap (c - 1) + finOf Nap (c + 1) = ev Nap c := by
      rw [finOf_add, ev_eq]
      congr 1
      omega
    have hlo : finOf Nap (c - 1) + finOf Nap (c - 1) = ev Nap (c - 1) := rfl
    have hhi : finOf Nap (c + 1) + finOf Nap (c + 1) = ev Nap (c + 1) := rfl
    rw [hmid, hlo, hhi] at h
    exact h
  exact shape_antitone hm3 g hg hsym hconv c₁ c₂ h12 hc

#print axioms corrClay_even_antitone

/-- **THE ODD LAGS ARE BOUNDED ABOVE BY THEIR TWO EVEN NEIGHBOURS.**

    ρ(2c+1)²  ≤  ρ(2c) · ρ(2c+2)

immediate from `corrClay_log_convex` at `e₁ = c`, `e₂ = c + 1`. This is the ONLY thing the proved
log-convexity says about an odd lag, and it is an upper bound. There is no companion lower bound and
none is derivable — `odd_scaling_admissible`.

DERIVED: `m` is half the extent. No constant. -/
theorem corrClay_odd_le (hm : Nap + 1 = 2 * m) (hm0 : 0 < m) (β : ℝ) (c : ℕ) (hc : c + 1 < m) :
    MassGap.WilsonBridge.corrClay (Nap + 1) β (finOf Nap c + finOf Nap (c + 1)) ^ 2
      ≤ MassGap.WilsonBridge.corrClay (Nap + 1) β (ev Nap c)
        * MassGap.WilsonBridge.corrClay (Nap + 1) β (ev Nap (c + 1)) := by
  have hlt1 : ((finOf Nap c : Fin (Nap + 1)) : ℕ) < m := by
    rw [finOf_val_of_lt (by omega)]; omega
  have hlt2 : ((finOf Nap (c + 1) : Fin (Nap + 1)) : ℕ) < m := by
    rw [finOf_val_of_lt (by omega)]; omega
  exact MassGap.LogConvex.corrClay_log_convex Nap m hm hm0 β hlt1 hlt2

#print axioms corrClay_odd_le

/-- **The even-lag shape with nonnegativity discharged**, at nonnegative coupling.

`Complete.wilson_reflection_positive_at_even` PROVES `0 ≤ wilsonCorrAt N β d` at even extent with
`m ≥ 2` and `0 ≤ β`, with a foundational footprint, so the hypothesis above is carried by a theorem
rather than by the named axiom. -/
theorem corrClay_even_antitone_of_nonneg_coupling (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) (c₁ c₂ : ℕ) (h12 : c₁ ≤ c₂) (hc : 2 * c₂ ≤ m) :
    MassGap.wilsonCorrAt Nap β (ev Nap c₂) ≤ MassGap.wilsonCorrAt Nap β (ev Nap c₁) :=
  corrClay_even_antitone hm hm3 β
    (fun d => (MassGap.wilson_reflection_positive_at_even Nap m hm (by omega) hβ).1 d) c₁ c₂ h12 hc

#print axioms corrClay_even_antitone_of_nonneg_coupling

/-- **NON-VACUITY — the smallest extent that meets the hypotheses, with a pair that is not the
diagonal.** At extent six the half is three, so `c₁ = 0` and `c₂ = 1` are both admissible and the
statement reads `ρ(2) ≤ ρ(0)`: a genuine two-lag statement about the even sublattice, at circle
distances `0` and `2` by `circLag_ev`. -/
theorem corrClay_even_antitone_at_extent_six {β : ℝ} (hβ : 0 ≤ β) :
    MassGap.wilsonCorrAt 5 β (ev 5 1) ≤ MassGap.wilsonCorrAt 5 β (ev 5 0) :=
  corrClay_even_antitone_of_nonneg_coupling (Nap := 5) (m := 3) (by norm_num) (by norm_num) hβ
    0 1 (by norm_num) (by norm_num)

#print axioms corrClay_even_antitone_at_extent_six

end EvenShape

/-! ## Part 4 — why the odd lags cannot be reached, as a theorem

Every constraint `corrClay_log_convex` produces has the form `ρ(e₁+e₂)² ≤ ρ(2e₁)·ρ(2e₂)`, so every
right-hand lag is EVEN. Shrinking `ρ` at the ODD lags alone therefore shrinks left-hand sides and
leaves right-hand sides fixed, and on an even period it preserves circle symmetry too. So the premise
set admits an arbitrarily small value at every odd lag, and no lower bound on one can follow from it.
-/

section NoGo

/-- The premise set this file works from, as a predicate: nonnegative, symmetric under the circle
reflection, and log-convex in the lag below half the extent. -/
structure Shape (n m : ℕ) [NeZero n] (ρ : Fin n → ℝ) : Prop where
  nonneg : ∀ d, 0 ≤ ρ d
  symm : ∀ d, ρ (-d) = ρ d
  logConvex : ∀ e₁ e₂ : Fin n, (e₁ : ℕ) < m → (e₂ : ℕ) < m →
    ρ (e₁ + e₂) ^ 2 ≤ ρ (e₁ + e₁) * ρ (e₂ + e₂)

/-- **THE WILSON CORRELATION SATISFIES `Shape`.** So the premise set the no-go below is stated about
is exactly what this tree proves — nonnegativity from `Complete.wilson_reflection_positive_at_even`,
circle symmetry from `wilsonCorrAt_neg` above, log-convexity from `LogConvex.corrClay_log_convex` —
and not an invented predicate that happens to be weak. -/
theorem shape_wilsonCorrAt (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm2 : 2 ≤ m) {β : ℝ} (hβ : 0 ≤ β) :
    Shape (Nap + 1) m (MassGap.wilsonCorrAt Nap β) where
  nonneg := (MassGap.wilson_reflection_positive_at_even Nap m hm hm2 hβ).1
  symm := wilsonCorrAt_neg Nap β
  logConvex := fun _ _ h1 h2 =>
    MassGap.LogConvex.corrClay_log_convex Nap m hm (by omega) β h1 h2

#print axioms shape_wilsonCorrAt

/-- Doubling lands on an even residue, because the period is even. -/
theorem even_val_add_self {n m : ℕ} [NeZero n] (hn : n = 2 * m) (e : Fin n) :
    Even ((e + e : Fin n) : ℕ) := by
  subst hn
  have hv : ((e + e : Fin (2 * m)) : ℕ) = (2 * (e : ℕ)) % (2 * m) := by
    rw [Fin.val_add, ← two_mul]
  rw [hv, Nat.mul_mod_mul_left]
  exact ⟨(e : ℕ) % m, by ring⟩

/-- The circle reflection preserves parity, because the period is even. -/
theorem even_val_neg {n m : ℕ} [NeZero n] (hn : n = 2 * m) (d : Fin n) :
    Even ((-d : Fin n) : ℕ) ↔ Even ((d : Fin n) : ℕ) := by
  have hlt := d.isLt
  have hv : ((-d : Fin n) : ℕ) = (n - (d : ℕ)) % n := by simp [Fin.neg_def]
  rcases Nat.eq_zero_or_pos (d : ℕ) with h0 | h0
  · rw [hv, h0, Nat.sub_zero, Nat.mod_self]
  · rw [hv, Nat.mod_eq_of_lt (by omega)]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨m - k, by omega⟩
    · rintro ⟨k, hk⟩; exact ⟨m - k, by omega⟩

/-- **THE ODD LAGS CAN BE SCALED DOWN FREELY, AND THE PREMISES STILL HOLD.**

Shrinking `ρ` at the odd lags by any factor `t ∈ [0,1]` — leaving the even lags alone — preserves
nonnegativity, circle symmetry and log-convexity. Both because every lag
`LogConvex.corrClay_log_convex` puts on the RIGHT of an inequality is `2e`, hence even, and because
on an even period `d` and `−d` share a parity.

**THIS IS A NO-GO.** Taking `t → 0` drives `ρ` at every odd lag to zero while the premises still
hold, so no theorem with these premises can lower-bound `ρ` at an odd lag. `Moment.circLag = 1` is
odd, so `ρ(1) ≥ ρ(2)` is not derivable here, and neither is monotonicity of the whole profile in the
circle distance.

DERIVED: nothing is chosen. `t` is quantified over, the parity is the lattice's — the period `2m` is
even because the reflection argument needs a midpoint — and `2e` is the theorem's own right-hand
lag. -/
theorem odd_scaling_admissible {n m : ℕ} [NeZero n] (hn : n = 2 * m) (ρ : Fin n → ℝ)
    (hshape : Shape n m ρ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Shape n m (fun d => if Even ((d : Fin n) : ℕ) then ρ d else t * ρ d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    by_cases h : Even ((d : Fin n) : ℕ)
    · rw [if_pos h]; exact hshape.nonneg d
    · rw [if_neg h]; exact mul_nonneg ht0 (hshape.nonneg d)
  · intro d
    by_cases h : Even ((d : Fin n) : ℕ)
    · rw [if_pos ((even_val_neg hn d).mpr h), if_pos h, hshape.symm]
    · rw [if_neg (fun hc => h ((even_val_neg hn d).mp hc)), if_neg h, hshape.symm]
  · intro e₁ e₂ h1 h2
    rw [if_pos (even_val_add_self hn e₁), if_pos (even_val_add_self hn e₂)]
    have hbase := hshape.logConvex e₁ e₂ h1 h2
    by_cases h : Even ((e₁ + e₂ : Fin n) : ℕ)
    · rw [if_pos h]; exact hbase
    · rw [if_neg h]
      have hsq : (t * ρ (e₁ + e₂)) ^ 2 = t ^ 2 * ρ (e₁ + e₂) ^ 2 := by ring
      rw [hsq]
      have ht2 : t ^ 2 ≤ 1 := by nlinarith
      calc t ^ 2 * ρ (e₁ + e₂) ^ 2
          ≤ 1 * ρ (e₁ + e₂) ^ 2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)
        _ = ρ (e₁ + e₂) ^ 2 := one_mul _
        _ ≤ ρ (e₁ + e₁) * ρ (e₂ + e₂) := hbase

#print axioms odd_scaling_admissible

/-- **THE WHOLE PROFILE IS NOT NON-INCREASING IN THE CIRCLE DISTANCE, AND THE PREMISES CANNOT MAKE IT
SO.** At extent eight the profile that is `1` at every lag except the two at circle distance three,
where it is `1/2`, satisfies every premise — and it DIPS at circle distance three and rises again at
circle distance four.

The reason is the scaling above: every right-hand lag is even, `1/2` appears only at the odd distance
three, and every constraint whose left side sits there has an untouched right side equal to `1`.

DERIVED: `8 = 2·4` is the smallest extent with an interior odd distance to exhibit; `1/2` is any
value strictly between `0` and `1` and `0` would do as well — `odd_scaling_admissible` quantifies
over all of them. Nothing here is fitted. -/
theorem not_antitone_circLag_of_shape :
    ∃ ρ : Fin 8 → ℝ, Shape 8 4 ρ ∧
      ¬ (∀ d₁ d₂ : Fin 8,
          Moment.circLag (N := 7) d₁ ≤ Moment.circLag (N := 7) d₂ → ρ d₂ ≤ ρ d₁) := by
  refine ⟨fun d => if (d : ℕ) = 3 ∨ (d : ℕ) = 5 then (1 : ℝ) / 2 else 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro d
    by_cases h : (d : ℕ) = 3 ∨ (d : ℕ) = 5
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num
  · intro d
    have hiff : (((-d : Fin 8) : ℕ) = 3 ∨ ((-d : Fin 8) : ℕ) = 5)
        ↔ ((d : ℕ) = 3 ∨ (d : ℕ) = 5) := by
      fin_cases d <;> decide
    simp only [hiff]
  · intro e₁ e₂ h1 h2
    have hr1 : ¬ (((e₁ + e₁ : Fin 8) : ℕ) = 3 ∨ ((e₁ + e₁ : Fin 8) : ℕ) = 5) := by
      revert h1; fin_cases e₁ <;> decide
    have hr2 : ¬ (((e₂ + e₂ : Fin 8) : ℕ) = 3 ∨ ((e₂ + e₂ : Fin 8) : ℕ) = 5) := by
      revert h2; fin_cases e₂ <;> decide
    rw [if_neg hr1, if_neg hr2]
    by_cases hc : ((e₁ + e₂ : Fin 8) : ℕ) = 3 ∨ ((e₁ + e₂ : Fin 8) : ℕ) = 5
    · rw [if_pos hc]; norm_num
    · rw [if_neg hc]; norm_num
  · intro h
    have h1 := h 3 4 (by decide)
    have e3 : ((3 : Fin 8) : ℕ) = 3 := rfl
    have e4 : ((4 : Fin 8) : ℕ) = 4 := rfl
    simp only [e3, e4] at h1
    norm_num at h1

#print axioms not_antitone_circLag_of_shape

end NoGo

section Audit
#print axioms corrHyper_neg
#print axioms corrClay_neg
#print axioms wilsonCorrAt_neg
#print axioms eq_or_eq_neg_of_circLag_eq
#print axioms wilsonCorrAt_circLag_congr
#print axioms shape_zero_step
#print axioms shape_conv_top
#print axioms shape_step
#print axioms shape_antitone
#print axioms finOf
#print axioms finOf_val
#print axioms finOf_val_of_lt
#print axioms finOf_add
#print axioms finOf_period
#print axioms ev
#print axioms ev_eq
#print axioms circLag_ev
#print axioms corrClay_even_antitone
#print axioms corrClay_odd_le
#print axioms corrClay_even_antitone_of_nonneg_coupling
#print axioms corrClay_even_antitone_at_extent_six
#print axioms shape_wilsonCorrAt
#print axioms even_val_add_self
#print axioms even_val_neg
#print axioms odd_scaling_admissible
#print axioms not_antitone_circLag_of_shape
end Audit

end MassGap.MomentShape
