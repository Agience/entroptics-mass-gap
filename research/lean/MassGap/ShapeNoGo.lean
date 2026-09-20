import Mathlib
import MassGap.Complete
import MassGap.LogConvex
import MassGap.MomentShape
import MassGap.Hankel
import MassGap.ZeroMode
import MassGap.EvenAperture
import MassGap.ApertureRoute

/-!
# MassGap.ShapeNoGo — the coupling-free route to B5 is closed

`ApertureRoute.ConfinesAtAnAperture` — `∃ a : EvenAp, ∀ β, 3^{−1/4} < cosAvgEven a β` — is the
development's one open hypothesis. Over the last weeks the tree has accumulated a series of
COUPLING-FREE SHAPE FACTS about the lag correlation `ρ = wilsonCorrAt N β`, each proved at every
even extent and (mostly) every coupling, each saying something about the SHAPE of `ρ` across the
lag index and nothing about how `ρ` moves with `β`:

* `Complete.wilson_reflection_positive_at_even` — `0 ≤ ρ d` and `0 < ∑ ρ`;
* `MomentShape.wilsonCorrAt_neg` / `MomentShape.corrClay_neg` — `ρ(−d) = ρ(d)`, circle symmetry;
* `LogConvex.corrClay_log_convex` — `ρ(e₁+e₂)² ≤ ρ(2e₁)·ρ(2e₂)` below half the extent;
* `MomentShape.corrClay_even_antitone` (and `_of_nonneg_coupling`) — the even lags are
  non-increasing in the circle distance;
* `Hankel.corrClay_hankel_psd` — the reflection Gram matrix `ρ(eᵢ + eⱼ)` is positive-semidefinite.

`ShapeFacts` below is exactly that list, each clause transcribed from the statement of the lemma
that proves it. `wilsonCorrAt_shapeFacts` discharges all five for the real Wilson correlator, so the
predicate is about the right object and is not an invented weakening.

**THE RESULT.** `shape_facts_do_not_imply_confinement`: no implication of the form
"`ShapeFacts` ⟹ the cosine average clears `3^{−1/4}`" can hold, at any extent and any half-extent
bound. The witness is the FLAT read `ρ ≡ 1` — the tree's own `Moment.Read` `Inhabited` instance,
here named `flatRead`, with `flatRead_eq_default` recording that they are the same term. The flat
read satisfies every clause (`flatRead_shapeFacts`, foundational footprint), and its cosine average
is EXACTLY ZERO (`flat_cosAvg_eq_zero`), because the `(N+1)`-th roots of unity sum to zero —
`ZeroMode.sum_cos_theta_eq_zero`, already in the tree. Zero is strictly below `3^{−1/4} > 0`.

**WHAT THIS CLOSES, AND IT IS A NARROWING, NOT A DEFEAT.** The five lemmas above are a large part of
what the last weeks produced, and this file says where the remaining work is: not in adding a sixth
shape fact of the same kind, and not in combining the five more cleverly. Any argument that closes
B5 must read the COUPLING DEPENDENCE — how `wilsonCorrAt N β` moves as `β` moves — because the
shape facts are all satisfied by an object with no coupling in it at all. A future session that
finds itself deriving confinement from nonnegativity, symmetry, log-convexity, even-antitonicity and
Hankel positive-semidefiniteness, in any combination, can stop here: the derivation is refuted, not
merely unfinished.

This is the third no-go stated about the same premise set and the strongest. `MomentShape`'s
`odd_scaling_admissible` shows the odd lags cannot be lower-bounded from nonnegativity, symmetry and
log-convexity, and `not_antitone_circLag_of_shape` shows the full profile need not be monotone in
the circle distance. Both are statements about the PROFILE. This one is about the CONCLUSION: the
scalar the flagship actually consumes. `Spectral.lean` observes in prose that "nothing in the tree
proves `wilsonCorrAt` is non-constant" and that "the RP axiom is satisfied by a constant positive
`ρ`"; this file turns that observation into a theorem against the full five-fact premise set and
carries it all the way to the floor comparison.

**DERIVED, NOT CHOSEN.** No numeral is introduced. `3^{−1/4} = e^{−κ₀}` with `κ₀ = ¼log3` is
`Floor.lean`'s, carried in unchanged from `ApertureRoute.ConfinesAtAnAperture`. `m` is half the
extent, the reflection geometry's own bound, carried in from `LogConvex.corrClay_log_convex` and
`Hankel.corrClay_hankel_psd`. The `1` of the flat read is not a scale: the cosine average is
invariant under rescaling `ρ`, so every positive constant read gives the same zero.
-/

namespace MassGap.ShapeNoGo

open Finset

/-! ## 1. The five proved shape facts, as one predicate -/

/-- **THE COUPLING-FREE SHAPE FACTS, COLLECTED.** Each field is the statement of a lemma this tree
proves about `wilsonCorrAt`, transcribed rather than weakened:

* `nonneg`, `posMass` — `Complete.wilson_reflection_positive_at_even`'s two conjuncts;
* `symm` — `MomentShape.wilsonCorrAt_neg`;
* `logConvex` — `LogConvex.corrClay_log_convex`, including its `< m` side conditions;
* `evenAntitone` — `MomentShape.corrClay_even_antitone`, at `MomentShape.ev` and with its
  `2 * c₂ ≤ m` side condition;
* `hankel` — `Hankel.corrClay_hankel_psd`.

`m` is carried because three of the five clauses are stated relative to half the extent and cannot
be written without it, exactly as `MomentShape.Shape n m ρ` carries it.

**THE SPELLING OF THE HANKEL CLAUSE.** `Hankel.corrClay_hankel_psd` quantifies over an arbitrary
`ι : Type` with `[Fintype ι]`, over a level map `e : ι → Fin n` constrained by `(e i).val < m`, and
over coefficients `c : ι → ℝ`, concluding `0 ≤ ∑ i, ∑ j, c i * c j * ρ (e i + e j)`. This field is
that statement with `ι` specialised to `Fin k`, which loses nothing — every finite index type is
equivalent to one — and keeps the level map and its `< m` constraint, which the suggested spelling
`0 ≤ ∑ i, ∑ j, v i * v j * ρ (i + j)` over `Fin m` would have dropped. The constraint is not
decoration: the Hankel argument is a reflection Gram matrix and the levels have to sit below the
reflection plane for the entries to be the correlation at all. Dropping it would have made this
predicate assert something the tree has not proved. -/
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

/-- **THE WILSON CORRELATOR SATISFIES ALL FIVE SHAPE FACTS**, at even extent with `3 ≤ m` and
nonnegative coupling. This is what makes `ShapeFacts` non-vacuous and about the right object.

**THE HYPOTHESES ARE NOT UNIFORM ACROSS THE CLAUSES, and the strongest one is `evenAntitone`'s.**
Read the proof term rather than this list, but it is:

* `symm` takes NO hypothesis — `MomentShape.wilsonCorrAt_neg` holds at every extent and every real
  coupling;
* `logConvex` and `hankel` take the even-extent geometry and `0 < m`, and no coupling hypothesis —
  the even-lag weld is a conditional square against a strictly positive Boltzmann weight;
* `nonneg` and `posMass` take `2 ≤ m` and `0 ≤ β` — `Complete.wilson_reflection_positive_at_even`'s
  own hypotheses, the coupling sign being load-bearing there by
  `CharacterExpansion.NegControl.su3_kernel_nonneg_iff`;
* `evenAntitone` takes `3 ≤ m` — `MomentShape.corrClay_even_antitone`'s own bound, where its
  hypotheses stop being vacuous. So this theorem is stated at extent at least SIX, not four.

That is carried rather than hidden, and it does not weaken the no-go: `flatRead_shapeFacts` holds at
EVERY `m`, so the capstone is quantified over all of them and the `3 ≤ m` here only makes the
premise set the no-go refutes larger.

**FOOTPRINT: FOUNDATIONAL-ONLY, and that was not a foregone conclusion.** `Complete.wilsonCorrAt`
is the correlation the named axiom `Complete.wilson_reflection_positive_at` is stated about, so a
nonnegativity clause about it would ordinarily carry that axiom. It does not, because the even
extent and the nonnegative coupling let every clause go through `wilson_reflection_positive_at_even`
and `corrClay_even_antitone_of_nonneg_coupling`, which are THEOREMS — that restriction is exactly
what buys the foundational footprint, and it is why this theorem is stated on that domain rather
than at every extent and every real coupling. `#print axioms` at the foot of this file reports
`[propext, Classical.choice, Quot.sound]` and nothing else.

Every declaration in this file is foundational-only. The no-go therefore rests on no cited physics:
it is a statement about what these five inequalities do and do not entail, and it would stand even
if the named axiom were withdrawn.

DERIVED: `m` is half the extent, carried in from the cited lemmas; no numeral is introduced here. -/
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

/-- **THE FLAT READ** `ρ ≡ 1` — the tree's own `Moment.Read` `Inhabited` witness, named so it can be
reasoned about. `flatRead_eq_default` records that this is the same term and not a copy of it.

DERIVED: `1` is the constant value of `Moment.Read`'s own `Inhabited` witness and `0` is the
lower bound its `hρ` field discharges. Both come from `Moment.lean:125-129`; neither is
chosen here, which is the point -- the counterexample is the tree's own default read. -/
def flatRead (N : ℕ) : MassGap.Moment.Read N where
  ρ := fun _ => 1
  hρ := fun _ => zero_le_one
  hpos := Finset.sum_pos (fun _ _ => one_pos) ⟨0, Finset.mem_univ 0⟩

/-- The flat read IS `Moment.Read`'s `Inhabited` default, definitionally. -/
theorem flatRead_eq_default (N : ℕ) : flatRead N = (default : MassGap.Moment.Read N) := rfl

/-- The flat read's correlation, by definition. -/
theorem flatRead_rho (N : ℕ) : (flatRead N).ρ = fun _ : Fin (N + 1) => (1 : ℝ) := rfl

/-- **THE FLAT READ SATISFIES EVERY SHAPE FACT**, at every extent and every half-extent bound, with
a foundational footprint.

Clause by clause: `1 ≥ 0`; the total mass is `N+1 > 0`; `−d` and `d` carry the same value because
every lag does; `1² ≤ 1·1` with equality, so log-convexity holds as an equality; `1 ≤ 1`, so the
even lags are non-increasing non-strictly; and the Hankel form collapses to `(∑ c)² ≥ 0`.

This is the whole no-go: the five facts are a description of a shape, and the constant shape has it.

DERIVED: the `1` is not a scale. The cosine average is invariant under rescaling `ρ` by any positive
constant, so every constant read gives the same answer and `1` is the representative. -/
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

/-- The cosine average of a read — the scalar `ApertureRoute.cosAvgEven` is, and the scalar the
tension is the negative logarithm of. Named here so the capstone's conclusion is the floor
comparison the flagship actually consumes and not a paraphrase of it. -/
noncomputable def cosAvg {N : ℕ} (R : MassGap.Moment.Read N) : ℝ :=
  ∑ d, R.p d * Real.cos (R.θ d)

/-- **THIS IS `cosAvgEven`.** `ApertureRoute.cosAvgEven a β` is `cosAvg` of `EvenAperture.readEven`,
definitionally — so the capstone below is about the scalar `ConfinesAtAnAperture` bounds and nothing
adjacent to it. -/
theorem cosAvgEven_eq (a : MassGap.EvenAperture.EvenAp) (β : ℝ) :
    MassGap.ApertureRoute.cosAvgEven a β = cosAvg (MassGap.EvenAperture.readEven a β) := rfl

/-- **THE FLAT READ'S COSINE AVERAGE IS EXACTLY ZERO.**

    ∑_d p_d cos θ_d = (1/(N+1)) ∑_{d<N+1} cos(2πd/(N+1)) = 0

because the `N+1` angles are the arguments of the `(N+1)`-th roots of unity and those sum to zero
for `N+1 ≥ 2` — `ZeroMode.sum_cos_circle_eq_zero`, off `Complex.isPrimitiveRoot_exp` and
`IsPrimitiveRoot.geom_sum_eq_zero`, already proved in this tree and used here rather than rebuilt.
`ZeroMode.sum_cos_theta_eq_zero` is that identity already transported onto `Moment.Read.θ`.

The flat read's `p` is constant, so the weight factors straight out of the sum; nothing else
happens. This is the same mechanism `ZeroMode.zero_mode_lt_of_tension` runs on — a constant
component contributes NOTHING to the circular first moment while still diluting the normalisation —
taken to its limit, where the correlation is nothing BUT the constant component.

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

/-- The same, at `cosAvg`. -/
theorem flat_cosAvg (N : ℕ) (hN : 1 ≤ N) : cosAvg (flatRead N) = 0 :=
  flat_cosAvg_eq_zero N hN

/-! ## 5. The capstone -/

/-- **THE SHAPE FACTS DO NOT IMPLY CONFINEMENT.**

There is no implication of the form

    ∀ read, ShapeFacts (its correlation) → 3^{−1/4} < ⟨cos θ⟩ of that read

at any extent `N ≥ 1` and any half-extent bound `m`. The flat read satisfies the premise
(`flatRead_shapeFacts`) and its cosine average is `0` (`flat_cosAvg_eq_zero`), strictly below the
floor `3^{−1/4} > 0`.

**WHAT THIS DOES AND DOES NOT SAY.** It does NOT say `ConfinesAtAnAperture` is false — nothing here
evaluates `wilsonCorrAt` at any lag, and the Wilson correlator may well clear the floor. It says
that the five coupling-free facts listed at the head of this file are not enough to show that it
does, because a coupling-free object satisfies all five and fails the floor. So the remaining work
is on the `β`-dependence, and a sixth fact of the same kind will not close it.

The `m` is universally quantified, so the statement is not evaded by taking the half-extent bound
large: the flat read satisfies `ShapeFacts m` for every `m` at once.

DERIVED: `3^{−1/4} = e^{−κ₀}` is `ApertureRoute.ConfinesAtAnAperture`'s own floor, transcribed. -/
theorem shape_facts_do_not_imply_confinement (N m : ℕ) (hN : 1 ≤ N) :
    ¬ (∀ R : MassGap.Moment.Read N, ShapeFacts m R.ρ →
        (3 : ℝ) ^ (-(1 : ℝ) / 4) < cosAvg R) := by
  intro h
  have hfacts : ShapeFacts m (flatRead N).ρ := flatRead_shapeFacts N m
  have hflat := h (flatRead N) hfacts
  rw [flat_cosAvg N hN] at hflat
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  linarith

/-- **THE SAME, WITHOUT THE `Moment.Read` WRAPPER** — quantified over bare correlations, with the
cosine average written out. Stated so the no-go cannot be read as an artefact of packaging the
correlation into a `Read`: the conclusion here is the explicit sum

    ∑_d (ρ_d / ∑ ρ) · cos(2π d/(N+1))

which is `Moment.Read.p` and `Moment.Read.θ` unfolded, and the comparison is the same floor. -/
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
