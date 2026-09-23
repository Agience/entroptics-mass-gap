import Mathlib
import MassGap.Complete
import MassGap.LogConvex
import MassGap.MomentShape
import MassGap.Hankel
import MassGap.ZeroMode
import MassGap.EvenAperture
import MassGap.ApertureRoute

/-!
# MassGap.ShapeNoGo — six coupling-free shape properties do not bound the cosine average

Collects, as the structure `ShapeFacts m ρ`, six properties of a lag correlation
`ρ : Fin (N + 1) → ℝ`, each transcribed from a lemma this tree proves about
`ρ = MassGap.wilsonCorrAt N β`:

* `nonneg`, `posMass` — `0 ≤ ρ d` at every lag and `0 < ∑ d, ρ d`, the two conjuncts of
  `Complete.wilson_reflection_positive_at_even`;
* `symm` — `ρ (-d) = ρ d`, from `MomentShape.wilsonCorrAt_neg`;
* `logConvex` — `ρ (e₁ + e₂) ^ 2 ≤ ρ (e₁ + e₁) * ρ (e₂ + e₂)` for levels below `m`, from
  `LogConvex.corrClay_log_convex`;
* `evenAntitone` — `ρ (ev N c₂) ≤ ρ (ev N c₁)` for `c₁ ≤ c₂` with `2 * c₂ ≤ m`, from
  `MomentShape.corrClay_even_antitone`;
* `hankel` — `0 ≤ ∑ i, ∑ j, c i * c j * ρ (e i + e j)` for level maps constrained below `m`, from
  `Hankel.corrClay_hankel_psd`.

`wilsonCorrAt_shapeFacts` proves all six for `MassGap.wilsonCorrAt Nap β` at even extent
`Nap + 1 = 2 * m` with `3 ≤ m` and `0 ≤ β`.

`flatRead` is the constant read `ρ ≡ 1`, which `flatRead_eq_default` identifies with
`Moment.Read`'s `Inhabited` witness. `flatRead_shapeFacts` proves all six clauses for it at every
`N` and every `m`, and `flat_cosAvg_eq_zero` computes its cosine average as `0` for `1 ≤ N`, since
the `N + 1` angles are those of the `(N + 1)`-th roots of unity
(`ZeroMode.sum_cos_theta_eq_zero`).

`shape_facts_do_not_imply_confinement` and its unwrapped form `..._'` conclude the negation of
`∀ R, ShapeFacts m R.ρ → (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvg R`, at every `N ≥ 1` and every `m`.

Scope. The negated implication is about the six listed properties only; nothing here evaluates
`wilsonCorrAt` at any lag, and no claim is made about whether the Wilson correlator clears the
floor. Every clause of `ShapeFacts` is a statement across the lag index at fixed `β`, so the
witness `flatRead`, which carries no coupling, satisfies all of them.
`wilsonCorrAt_shapeFacts` is stated at even extent with `3 ≤ m`, which is extent at least six; the
no-go quantifies `m` universally, so that restriction does not narrow it.
-/

namespace MassGap.ShapeNoGo

open Finset

/-! ## 1. The six proved shape facts, as one predicate -/

/-- Five properties of a lag correlation `ρ : Fin (N + 1) → ℝ`, bundled as one `Prop`-valued
structure indexed by a half-extent bound `m`. Each field transcribes the conclusion of a lemma of
this tree, side conditions included; see the field docstrings.

`m` is a parameter of the structure because `logConvex`, `evenAntitone` and `hankel` each restrict
their indices relative to it, as `MomentShape.Shape n m ρ` does.

The `hankel` field specialises `Hankel.corrClay_hankel_psd`'s arbitrary `Fintype ι` to `Fin k`,
keeping the level map `e` and its `(e i).val < m` constraint. That constraint is part of the
statement: the entries are correlations at sums of levels below the reflection plane, not at
arbitrary index sums.

DERIVED: `1` is the `+ 1` in the index type `Fin (N + 1)`, so the correlation is indexed by `N + 1`
lags; `0` is the lower bound in `nonneg`, `posMass` and `hankel`; `2` appears as the exponent in
`ρ (e₁ + e₂) ^ 2`, the square of the middle term in log-convexity, and as the doubling in
`2 * c₂ ≤ m`, which is the even lag `ev N c₂` expressed in the half-extent bound. -/
structure ShapeFacts {N : ℕ} (m : ℕ) (ρ : Fin (N + 1) → ℝ) : Prop where
  /-- Reflection positivity, first conjunct: the correlation is nonnegative at every lag. -/
  nonneg : ∀ d, 0 ≤ ρ d
  /-- Reflection positivity, second conjunct: the total mass is strictly positive. -/
  posMass : 0 < ∑ d, ρ d
  /-- Circle symmetry: the correlation at `−d` is the correlation at `d`. -/
  symm : ∀ d, ρ (-d) = ρ d
  /-- Log-convexity in the lag, below half the extent. -/
  logConvex : ∀ e₁ e₂ : Fin (N + 1), (e₁ : ℕ) < m → (e₂ : ℕ) < m →
    ρ (e₁ + e₂) ^ 2 ≤ ρ (e₁ + e₁) * ρ (e₂ + e₂)
  /-- The even lags are non-increasing in the circle distance. -/
  evenAntitone : ∀ c₁ c₂ : ℕ, c₁ ≤ c₂ → 2 * c₂ ≤ m →
    ρ (MassGap.MomentShape.ev N c₂) ≤ ρ (MassGap.MomentShape.ev N c₁)
  /-- The reflection Gram matrix is positive-semidefinite in Hankel form. -/
  hankel : ∀ (k : ℕ) (e : Fin k → Fin (N + 1)), (∀ i, ((e i : Fin (N + 1)) : ℕ) < m) →
    ∀ c : Fin k → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * ρ (e i + e j)

/-! ## 2. The real correlator satisfies them -/

/-- `ShapeFacts m (MassGap.wilsonCorrAt Nap β)` at even extent. Takes `hm : Nap + 1 = 2 * m`,
`hm3 : 3 ≤ m` and `hβ : 0 ≤ β`, and builds the structure field by field:

* `nonneg` and `posMass` are the two conjuncts of
  `Complete.wilson_reflection_positive_at_even Nap m hm _ hβ`, which uses the coupling sign;
* `symm` is `MomentShape.wilsonCorrAt_neg Nap β`, which takes no hypothesis on extent or coupling;
* `logConvex` is `LogConvex.corrClay_log_convex Nap m hm _ β`, with the even-extent geometry and no
  coupling hypothesis;
* `evenAntitone` is `MomentShape.corrClay_even_antitone_of_nonneg_coupling hm hm3 hβ`, the clause
  that consumes `3 ≤ m`;
* `hankel` is `Hankel.corrClay_hankel_psd (Nap + 1) m hm _ β`.

Scope: the hypotheses differ across the clauses and `3 ≤ m` is the strongest of them, so the
 theorem as a whole holds at extent at least six. The even-extent and nonnegative-coupling
restrictions are what let every clause go through a theorem rather than through the named axiom
`Complete.wilson_reflection_positive_at`; `#print axioms` on this declaration reports
`propext, Classical.choice, Quot.sound`.

DERIVED: `1` is the `+ 1` of the extent relation `Nap + 1 = 2 * m` and of the index type; `2` is the
doubling in that relation, which is what makes the extent even; `3` is `corrClay_even_antitone`'s own
lower bound on the half-extent, transcribed; `0` is the lower bound on the coupling, required by
`wilson_reflection_positive_at_even`. `m` is half the extent, carried in from the cited lemmas. -/
theorem wilsonCorrAt_shapeFacts (Nap m : ℕ) (hm : Nap + 1 = 2 * m) (hm3 : 3 ≤ m)
    {β : ℝ} (hβ : 0 ≤ β) :
    ShapeFacts (N := Nap) m (MassGap.wilsonCorrAt Nap β) where
  nonneg := (MassGap.wilson_reflection_positive_at_even Nap m hm (by omega) hβ).1
  posMass := (MassGap.wilson_reflection_positive_at_even Nap m hm (by omega) hβ).2
  symm := MassGap.MomentShape.wilsonCorrAt_neg Nap β
  logConvex := fun _ _ h1 h2 =>
    MassGap.LogConvex.corrClay_log_convex Nap m hm (by omega) β h1 h2
  evenAntitone := fun c₁ c₂ h12 hc =>
    MassGap.MomentShape.corrClay_even_antitone_of_nonneg_coupling hm hm3 hβ c₁ c₂ h12 hc
  hankel := fun k e he c =>
    MassGap.Hankel.corrClay_hankel_psd (Nap + 1) m hm (by omega) β e he c

/-! ## 3. The flat read -/

/-- **The flat read** `ρ ≡ 1` — the tree's own `Moment.Read` `Inhabited` witness, named so it can be
reasoned about. `flatRead_eq_default` records that this is the same term and not a copy of it.

DERIVED: `1` is the constant value of `Moment.Read`'s own `Inhabited` witness and `0` is the
lower bound its `hρ` field discharges. Both come from `Moment.lean:125-129`; neither is
chosen here, which is the point -- the counterexample is the tree's own default read. -/
def flatRead (N : ℕ) : MassGap.Moment.Read N where
  ρ := fun _ => 1
  hρ := fun _ => zero_le_one
  hpos := Finset.sum_pos (fun _ _ => one_pos) ⟨0, Finset.mem_univ 0⟩

/-- `flatRead N = (default : Moment.Read N)`, by `rfl`: the two are the same term, so results about
`flatRead` are results about the tree's own default read.

DERIVED: no numeral occurs in the statement. -/
theorem flatRead_eq_default (N : ℕ) : flatRead N = (default : MassGap.Moment.Read N) := rfl

/-- `(flatRead N).ρ = fun _ : Fin (N + 1) => (1 : ℝ)`, by `rfl`: the flat read's correlation is the
constant one at every lag.

DERIVED: `1` is the `+ 1` in the index type `Fin (N + 1)` and the constant value of the
correlation. -/
theorem flatRead_rho (N : ℕ) : (flatRead N).ρ = fun _ : Fin (N + 1) => (1 : ℝ) := rfl

/-- `ShapeFacts m (fun _ : Fin (N + 1) => (1 : ℝ))` at every `N` and every `m`. Clause by clause:
`nonneg` is `zero_le_one`; `posMass` is `Finset.sum_pos` over the nonempty index type; `symm` is
`rfl`, since the function is constant; `logConvex` holds with equality; `evenAntitone` is
`le_refl`; and `hankel` reduces to `0 ≤ (∑ i, c i) * (∑ i, c i)`, which is `mul_self_nonneg`.

Scope: `m` is unconstrained, so the constant correlation satisfies the structure at every
half-extent bound at once.

DERIVED: `1` is the `+ 1` of the index type `Fin (N + 1)` and the constant value of the
correlation. That value is not a scale: `cosAvg` divides by the total mass, so any positive constant
gives the same average and `1` is the representative. -/
theorem flatRead_shapeFacts (N m : ℕ) : ShapeFacts (N := N) m (fun _ : Fin (N + 1) => (1 : ℝ)) where
  nonneg := fun _ => zero_le_one
  posMass := Finset.sum_pos (fun _ _ => one_pos) ⟨0, Finset.mem_univ 0⟩
  symm := fun _ => rfl
  logConvex := fun _ _ _ _ => by norm_num
  evenAntitone := fun _ _ _ _ => le_refl (1 : ℝ)
  hankel := by
    intro k _e _he c
    show (0 : ℝ) ≤ ∑ i : Fin k, ∑ j : Fin k, c i * c j * (1 : ℝ)
    calc (0 : ℝ) ≤ (∑ i, c i) * (∑ i, c i) := mul_self_nonneg _
      _ = ∑ i : Fin k, ∑ j : Fin k, c i * c j * (1 : ℝ) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => (mul_one _).symm)

/-! ## 4. The flat read's cosine average is exactly zero -/

/-- The cosine average of a read: `∑ d, R.p d * Real.cos (R.θ d)`, the scalar
`ApertureRoute.cosAvgEven` is and the one whose negative logarithm is the tension.

DERIVED: no numeral occurs; the weights and angles are the read's own. -/
noncomputable def cosAvg {N : ℕ} (R : MassGap.Moment.Read N) : ℝ :=
  ∑ d, R.p d * Real.cos (R.θ d)

/-- `ApertureRoute.cosAvgEven a β = cosAvg (EvenAperture.readEven a β)`, by `rfl`. So the
statements below are about the scalar `ApertureRoute.ConfinesAtAnAperture` bounds.

DERIVED: no numeral occurs in the statement. -/
theorem cosAvgEven_eq (a : MassGap.EvenAperture.EvenAp) (β : ℝ) :
    MassGap.ApertureRoute.cosAvgEven a β = cosAvg (MassGap.EvenAperture.readEven a β) := rfl

/-- **The flat read's cosine average is exactly zero.**

    ∑_d p_d cos θ_d = (1/(N+1)) ∑_{d<N+1} cos(2πd/(N+1)) = 0

because the `N+1` angles are the arguments of the `(N+1)`-th roots of unity and those sum to zero
for `N+1 ≥ 2` — `ZeroMode.sum_cos_circle_eq_zero`, off `Complex.isPrimitiveRoot_exp` and
`IsPrimitiveRoot.geom_sum_eq_zero`, already proved in this tree and used here rather than rebuilt.
`ZeroMode.sum_cos_theta_eq_zero` is that identity already transported onto `Moment.Read.θ`.

The flat read's `p` is constant, so the weight factors straight out of the sum; nothing else
happens. This is the same mechanism `ZeroMode.zero_mode_lt_of_tension` runs on — a constant
component contributes nothing to the circular first moment while still diluting the normalisation —
taken to its limit, where the correlation is nothing but the constant component.

DERIVED: `1 ≤ N` is `2 ≤ N+1`, the root-of-unity identity's own hypothesis; at `N = 0` the single
angle is `0` and the average is `1`, so the bound is not an artefact of the proof. -/
theorem flat_cosAvg_eq_zero (N : ℕ) (hN : 1 ≤ N) :
    ∑ d, (flatRead N).p d * Real.cos ((flatRead N).θ d) = 0 := by
  have hzero := MassGap.ZeroMode.sum_cos_theta_eq_zero (flatRead N) hN
  have hstep : ∀ d : Fin (N + 1),
      (flatRead N).p d * Real.cos ((flatRead N).θ d)
        = (1 / ∑ d', (flatRead N).ρ d') * Real.cos ((flatRead N).θ d) := fun _ => rfl
  calc ∑ d, (flatRead N).p d * Real.cos ((flatRead N).θ d)
      = ∑ d, (1 / ∑ d', (flatRead N).ρ d') * Real.cos ((flatRead N).θ d) :=
        Finset.sum_congr rfl (fun d _ => hstep d)
    _ = (1 / ∑ d', (flatRead N).ρ d') * ∑ d, Real.cos ((flatRead N).θ d) := by
        rw [Finset.mul_sum]
    _ = 0 := by rw [hzero, mul_zero]

/-- `cosAvg (flatRead N) = 0` for `1 ≤ N`. The previous theorem with the sum folded into `cosAvg`,
which is definitionally that sum.

DERIVED: `1` is the lower bound on the extent index, inherited from `flat_cosAvg_eq_zero`; `0` is
the value of the average. -/
theorem flat_cosAvg (N : ℕ) (hN : 1 ≤ N) : cosAvg (flatRead N) = 0 :=
  flat_cosAvg_eq_zero N hN

/-! ## 5. The capstone -/

/-- **The shape facts do not imply confinement.**

There is no implication of the form

    ∀ read, ShapeFacts (its correlation) → 3^{−1/4} < ⟨cos θ⟩ of that read

at any extent `N ≥ 1` and any half-extent bound `m`. The flat read satisfies the premise
(`flatRead_shapeFacts`) and its cosine average is `0` (`flat_cosAvg_eq_zero`), strictly below the
floor `3^{−1/4} > 0`.

**What this does and does not say.** It does not say `ConfinesAtAnAperture` is false — nothing here
evaluates `wilsonCorrAt` at any lag, and the Wilson correlator may well clear the floor. It says
that the six coupling-free facts listed at the head of this file are not enough to show that it
does, because a coupling-free object satisfies all six and fails the floor. So the remaining work
is on the `β`-dependence, and a further fact of the same kind will not close it.

The `m` is universally quantified, so the statement is not evaded by taking the half-extent bound
large: the flat read satisfies `ShapeFacts m` for every `m` at once.

DERIVED: `3` is the base of the floor `(3 : ℝ) ^ (-(1 : ℝ) / 4)`, and the `1` and `4` are its
exponent `-1/4`; together they are `exp (-κ₀)` for `κ₀ = (1 / 4) * log 3`, transcribed unchanged from
`ApertureRoute.ConfinesAtAnAperture`. The other `1` is the lower bound `1 ≤ N`, which
`flat_cosAvg_eq_zero` requires so that the angles are those of at least two roots of unity. -/
theorem shape_facts_do_not_imply_confinement (N m : ℕ) (hN : 1 ≤ N) :
    ¬ (∀ R : MassGap.Moment.Read N, ShapeFacts m R.ρ →
        (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvg R) := by
  intro h
  have hfacts : ShapeFacts m (flatRead N).ρ := flatRead_shapeFacts N m
  have hflat := h (flatRead N) hfacts
  rw [flat_cosAvg N hN] at hflat
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  linarith

/-- The same negation over bare correlations `ρ : Fin (N + 1) → ℝ`, with the cosine average written
out as `∑ d, (ρ d / ∑ d', ρ d') * Real.cos (2 * Real.pi * d / (N + 1))`. That sum is
`Moment.Read.p` and `Moment.Read.θ` unfolded, so the step from `flat_cosAvg_eq_zero` is `rfl`; the
floor compared against is the same.

DERIVED: `3`, `1` and `4` are the floor `(3 : ℝ) ^ (-(1 : ℝ) / 4)`, as above; `2` is the `2 * π` of
a full turn, so the angles are `2πd / (N + 1)`; the `1`s in `Fin (N + 1)` and `(N : ℝ) + 1` are the
number of lags, and the remaining `1` is the bound `1 ≤ N`. -/
theorem shape_facts_do_not_imply_confinement' (N m : ℕ) (hN : 1 ≤ N) :
    ¬ (∀ ρ : Fin (N + 1) → ℝ, ShapeFacts m ρ →
        (3 : ℝ) ^ (-(1 : ℝ) / 4)
          < ∑ d : Fin (N + 1),
              (ρ d / ∑ d', ρ d') * Real.cos (2 * Real.pi * (d : ℝ) / ((N : ℝ) + 1))) := by
  intro h
  have hflat := h (fun _ => (1 : ℝ)) (flatRead_shapeFacts N m)
  have heq : ∑ d : Fin (N + 1),
      ((fun _ : Fin (N + 1) => (1 : ℝ)) d / ∑ d', (fun _ : Fin (N + 1) => (1 : ℝ)) d')
        * Real.cos (2 * Real.pi * (d : ℝ) / ((N : ℝ) + 1))
      = ∑ d, (flatRead N).p d * Real.cos ((flatRead N).θ d) := rfl
  rw [heq, flat_cosAvg_eq_zero N hN] at hflat
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  linarith

/-! ## 6. Audit -/

section Audit

#print axioms ShapeFacts
#print axioms wilsonCorrAt_shapeFacts
#print axioms flatRead
#print axioms flatRead_eq_default
#print axioms flatRead_shapeFacts
#print axioms cosAvg
#print axioms cosAvgEven_eq
#print axioms flat_cosAvg_eq_zero
#print axioms flat_cosAvg
#print axioms shape_facts_do_not_imply_confinement
#print axioms shape_facts_do_not_imply_confinement'

end Audit

end MassGap.ShapeNoGo
