import Mathlib
import MassGap.DefectBound
import MassGap.WindowRead

/-!
# MassGap.MasslessExclude — what the coupling derivatives, the curvature and the vertex read of case (M)

`StallRigid.stall_dichotomy` leaves case (M) for a bounded stall: `D` bounded and the window read `Y(w)` eventually
in `[c₀, 1 − δ]`, a zero-flux level at gap of order `1/L`. Exclusion (ZM) asks that for `SU(N)` this does not happen,
frequently in `β`. This module tests three routes to (ZM) and proves what each one reads. Declarations are in the
namespace `MassGap.MasslessExclude`. No route excludes (M); each section ends at a named obstruction.

## 1. The case-(M) term of `log Tr T^L` and its coupling slope (proved)

Write the excited part of the normalized trace at time `L` as `mTerm x β = log(1 + Σ_i e^{−x_i(β)})`, with
`x_i = L (E_i − E₀)` the scaled levels; case (M) is `x_i ≍ 1`.

* `hasDerivAt_mTerm`: `∂_β mTerm = −Σ_i x_i' e^{−x_i} / (1 + Σ_i e^{−x_i})`.
* `abs_deriv_mTerm_le`: `|∂_β mTerm| ≤ B` when `|x_i'| ≤ B`. The bound has no `L` in it: the case-(M) contribution to
  `∂_β log Z` is of order `L⁰` in total, so of order `L⁻⁴` per site, and the same holds for each further derivative.
* `fixed_levels_flat`: scaled levels that do not move with `β` (an infrared-attractive scale-invariant limit, where
  `x_i` is universal) give `∂_β mTerm = 0`.

## 2. Windows read per site cannot see it (proved)

A family `log Z(2^w) = 16^w f(β) + g(β)` (bulk plus a bounded finite-size term).

* `split_defect`: its defect is `D = 15 g`, from `DefectBound.log_term`.
* `perSite_tendsto`: `(16^w a + b)/16^w → a`. Applied to the value, the first and the second `β`-derivative, the free
  energy, the mean action (`GapPersist.window_slope_tendsto` reads this one) and the specific heat per site converge
  to the bulk, whatever `g` is. Convexity and Griffiths' lemma read `f`, never `g`.
* `hasDerivAt_cutE`: on the Wilson torus, `∂_β cut = 16 Var_n S − Var_{2n} S`, so `∂²_β D(w)` is the doubling defect of
  the action variance, an exact identity (from `WindowRead.hasDerivAt_meanAction`). Case (M) with a moving level
  shape feeds this defect by `15 g''`, of order `1` in total: a quantity no per-site read controls.

## 3. The coupling slope of `D` separates the line, not the point (proved)

* `line_strictMono`: the rotor term `g = log(1 + 2 e^{−1/(2β)})` (`StallRigid.rotor_read` with inertia `b = β`, the
  `U(1)` shape, a line of fixed points) makes `D = 15 g` strictly increasing on `β > 0`.
* `point_blind`: a constant term `g = c > 0` (scaled levels free of `β`: an attractive scale-invariant limit, case
  (M) when the levels sit at `x ≍ 1`) has `D = 15 c > 0` at every `β` and `∂_β D = 0`, the same slope as the gapped
  family `g = 0`. Only the value of `D_∞` separates them, which is (ZM) itself.
* `not_antitone_SU`: at a fixed window the Wilson defect of `SU(N)` is not decreasing on `[0, β]` once `D(β, w) > 0`,
  from `D(0, w) = 0` (`CouplingTower.windowCoupling_zero`). So "a gapped `D` decreases in `β`" is false at every
  fixed window; it can only be a statement about `D_∞`, where gapped means `D_∞ = 0` and an attractive scale-invariant
  limit means `D_∞` constant. A monotonicity in `β` of `D_∞` excludes the line (the `U(1)` shape) and nothing else.

## 4. Curvature: the gauge-invariant direction of negative Hessian (proved at `SU(2)`, argued in general)

`CondGap` records the Bakry–Émery constant `N/4 − β H`. The question is whether restriction to gauge-invariant
observables removes the `β Hess S` part.

* `su2_class_curve`: on the Cartan curve `t ↦ −diag(e^{it}, e^{−it})` through the action maximum `−1` of `SU(2)`, the
  plaquette density is `1 − ½ Re tr U = 1 + cos t`. Its value depends only on the trace, a class function, and the
  curve changes the conjugacy class, so the direction is gauge-invariant.
* `su2_class_hess`: the second derivative at `t = 0` is `−1`.
* `cd_fails`: so the curvature-dimension sum along that direction, `κ + β · (−1)`, is negative for `β > κ`, whatever
  `κ = Ric` the group supplies. The bad part does not cancel on gauge-invariant observables.

Argued for every compact connected `G`: at the maximum `U*` of the class function `S = 1 − Re χ/d` the Hessian vanishes
on the conjugacy-orbit directions (a critical point of a function constant on the orbit), so its trace is carried by
the transverse, gauge-invariant directions, and it equals `ΔS(U*) = c₂ Re χ(U*)/d < 0` (`Δχ = −c₂ χ`, and
`min Re χ < 0` since `∫ χ = 0`). One transverse direction has Hessian at most `ΔS(U*)/rank`, so the invariant
curvature constant is negative for `β` above a multiple of `Ric · d · rank / c₂`: Bakry–Émery covers only bounded `β`
on invariant observables too.

## 5. The non-abelian vertex (argued and cited)

`HarmonicVertex.cubic_comm`, `cubic_su2_ne`: the cubic vertex vanishes on commuting data and not at `su(2)`. The vertex
does not exclude (M): `𝒩 = 4` super-Yang–Mills and `SU(N)` with enough massless flavours in the conformal window
(Banks–Zaks) are interacting, scale invariant, massless, and carry the same `f^{abc}` vertex (cited). What separates
pure `SU(N)` from them is the sign of the running (`b₀ = 11N/3` against `11N/3 − 2n_f/3`), a perturbative reading the
rules here exclude. In the tree, `HarmonicVertex.secondOrder_coupling_nonneg` gives a sign of mode coupling, and that
sign is the same in the conformal theories.

## 6. Tests

* `U(1)`: (M) stays: `line_strictMono` is its shape (`D` rising like the `log β` count), and `cd_fails` holds at
  `κ = 0` at every `β > 0` (the plaquette angle at `π` has the same `1 + cos t`), so neither route touches the Coulomb
  phase, consistent.
* `A₅`: (T), not (M): `point_blind` with `c = log M` is also the exact-degeneracy shape (`StallRigid.defect_const`),
  with no level at `x ≍ 1`; the derivatives read it as they read a fixed point. No curvature (finite group).
* `G₂`: §4's argued statement applies (`G₂` is compact connected with `Ric > 0`), so Bakry–Émery fails for `G₂` at
  large `β` as for `SU(N)`; §1–§3 are group-free. Nothing here excludes (M) at `G₂`, and nothing here is claimed for
  all simple `G`.

DERIVED (module-wide): `16 = 2⁴` the copies and `15 = 16 − 1`; `2` in `1 + 2 e^{−1/(2β)}` the two rotor levels `±1`
and in `2β` the rotor's `2b`; `½` the `1/N` at `N = 2`; `1`, `0` the top level, limits and signs. CHOSEN: `b = β` in
`line_strictMono` (the rotor inertia proportional to the coupling, any positive multiple gives the same monotonicity);
the Cartan curve `diag(e^{it}, e^{−it})` of §4 (any regular torus direction through the maximum).

## What does not follow

(ZM) is not proved, at any `β`, for any group. §1–§2 show the case-(M) term is of order `L⁰` in `log Z` and its
`β`-derivatives, and every per-site read (convexity, Griffiths, the specific heat per site) is blind to it. §3 shows
the `β`-slope of `D` detects a line of fixed points and not an attractive scale-invariant limit, whose `D_∞` is a
constant like the gapped `0`: excluding (M) there is excluding a constant `D_∞ > 0`, which is (ZM) restated. §4 shows
the curvature route fails on gauge-invariant observables at large `β` (proved at `SU(2)` on one curve; the general
statement is argued). §5 is argued and cited. The families of §2–§3 are models, not Wilson measures; only
`hasDerivAt_cutE` and `not_antitone_SU` are statements about the Wilson torus. `su2_class_*` is a single-plaquette `SU(2)` computation, and `cd_fails` is arithmetic on `κ + β·(−1)`, with `−1` taken from that computation; `cd_fails` does not itself use the Hessian. With (H) in `DefectBound` and (ZP) in
`GapPersist`, all three exclusions are now blocked: each reduces to a bound at the window scale on the zero-flux
spectrum that none of positivity, convexity, Perron–Frobenius, curvature or the vertex reaches.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MassGap.MasslessExclude

open Filter Topology

/-! ## 1. The case-(M) term -/

/-- The excited part of the normalized trace at the window time, from the scaled levels `x_i = L (E_i − E₀)`. -/
def mTerm {n : ℕ} (x : Fin n → ℝ → ℝ) (β : ℝ) : ℝ := Real.log (1 + ∑ i, Real.exp (-(x i β)))

theorem one_add_pos {n : ℕ} (x : Fin n → ℝ → ℝ) (β : ℝ) : 0 < 1 + ∑ i, Real.exp (-(x i β)) := by
  have : 0 ≤ ∑ i, Real.exp (-(x i β)) := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  linarith

/-- **The coupling slope of the case-(M) term.** DERIVED: `1` the top level. -/
theorem hasDerivAt_mTerm {n : ℕ} {x : Fin n → ℝ → ℝ} {x' : Fin n → ℝ} {β : ℝ}
    (hx : ∀ i, HasDerivAt (x i) (x' i) β) :
    HasDerivAt (mTerm x)
      ((∑ i, Real.exp (-(x i β)) * -(x' i)) / (1 + ∑ i, Real.exp (-(x i β)))) β := by
  have hs : HasDerivAt (fun y => ∑ i, Real.exp (-(x i y))) (∑ i, Real.exp (-(x i β)) * -(x' i)) β :=
    HasDerivAt.fun_sum fun i _ => (hx i).neg.exp
  exact (hs.const_add 1).log (one_add_pos x β).ne'

/-- **The case-(M) slope has no `L` in it.** `|∂_β mTerm| ≤ B` when every scaled level moves at most at rate `B`. -/
theorem abs_deriv_mTerm_le {n : ℕ} {x : Fin n → ℝ → ℝ} {x' : Fin n → ℝ} {β B : ℝ} (hB : 0 ≤ B)
    (hx' : ∀ i, |x' i| ≤ B) :
    |(∑ i, Real.exp (-(x i β)) * -(x' i)) / (1 + ∑ i, Real.exp (-(x i β)))| ≤ B := by
  set S := ∑ i, Real.exp (-(x i β))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  have hpos : 0 < 1 + S := by linarith
  have hnum : |∑ i, Real.exp (-(x i β)) * -(x' i)| ≤ B * S := by
    calc |∑ i, Real.exp (-(x i β)) * -(x' i)| ≤ ∑ i, |Real.exp (-(x i β)) * -(x' i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, Real.exp (-(x i β)) * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (hx' i) (Real.exp_pos _).le
      _ = B * S := by rw [← Finset.sum_mul, mul_comm]
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith

/-- **Scaled levels free of `β` give a flat case-(M) term.** -/
theorem fixed_levels_flat {n : ℕ} (c : Fin n → ℝ) (β : ℝ) :
    HasDerivAt (mTerm fun i (_ : ℝ) => c i) 0 β := by
  have h := hasDerivAt_mTerm (x := fun i (_ : ℝ) => c i) (x' := fun _ => 0) (β := β)
    (fun i => hasDerivAt_const β (c i))
  simpa using h

/-! ## 2. Per-site reads -/

/-- **The defect of a bulk-plus-bounded family** is `15` times the bounded term. DERIVED: `15 = 16 − 1`. -/
theorem split_defect (f g : ℝ) (w : ℕ) :
    16 * ((16 : ℝ) ^ w * f + g) - ((16 : ℝ) ^ (w + 1) * f + g) = 15 * g := by
  have h := DefectBound.log_term f 0 g w
  simp only [zero_mul, mul_zero, add_zero, sub_zero] at h
  simpa using h

/-- **Per-site reads converge to the bulk, whatever the bounded term.** DERIVED: `16` the copies. -/
theorem perSite_tendsto (a b : ℝ) :
    Tendsto (fun w : ℕ => ((16 : ℝ) ^ w * a + b) / (16 : ℝ) ^ w) atTop (𝓝 a) := by
  have h16 : Tendsto (fun w : ℕ => (16 : ℝ) ^ w) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hb : Tendsto (fun w : ℕ => b / (16 : ℝ) ^ w) atTop (𝓝 0) := h16.const_div_atTop b
  have he : (fun w : ℕ => ((16 : ℝ) ^ w * a + b) / (16 : ℝ) ^ w) = fun w => a + b / (16 : ℝ) ^ w := by
    funext w
    have : (16 : ℝ) ^ w ≠ 0 := by positivity
    field_simp
  rw [he]
  simpa using (tendsto_const_nhds (x := a)).add hb

/-- **The second coupling derivative of the defect is the doubling defect of the action variance**, on the
Wilson torus of `SU(N)`: `∂_β cut = 16 Var_n S − Var_{2n} S`. DERIVED: `16` the copies, `2` the doubling. -/
theorem hasDerivAt_cutE {N : ℕ} (hN : N ≠ 0) (n : ℕ) (β : ℝ) :
    HasDerivAt (StallRigid.cutE N n)
      (16 * WindowRead.varAction N (fun _ => n) β - WindowRead.varAction N (fun _ => 2 * n) β) β := by
  have h2 := WindowRead.hasDerivAt_meanAction hN (fun _ => 2 * n) β
  have h1 := WindowRead.hasDerivAt_meanAction hN (fun _ => n) β
  have h := h2.sub (h1.const_mul 16)
  have hv : -WindowRead.varAction N (fun _ => 2 * n) β - 16 * -WindowRead.varAction N (fun _ => n) β
      = 16 * WindowRead.varAction N (fun _ => n) β - WindowRead.varAction N (fun _ => 2 * n) β := by ring
  rw [hv] at h
  exact h

/-! ## 3. The coupling slope of `D` -/

/-- **The line shape rises.** The rotor term with inertia `β` makes `D = 15 log(1 + 2 e^{−1/(2β)})` strictly
increasing on `β > 0`. DERIVED: `15` from `split_defect`, `2` the rotor levels `±1` and the rotor's `2b`. -/
theorem line_strictMono :
    StrictMonoOn (fun β : ℝ => 15 * Real.log (1 + 2 * Real.exp (-(1 / (2 * β))))) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have h1 : 1 / (2 * b) < 1 / (2 * a) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h2 : Real.exp (-(1 / (2 * a))) < Real.exp (-(1 / (2 * b))) := Real.exp_lt_exp.mpr (by linarith)
  have hpa : 0 < 1 + 2 * Real.exp (-(1 / (2 * a))) := by positivity
  have h3 := Real.log_lt_log hpa (by linarith : 1 + 2 * Real.exp (-(1 / (2 * a))) < 1 + 2 * Real.exp (-(1 / (2 * b))))
  simp only
  linarith

/-- **The point shape is flat, like the gapped one.** A constant term `c > 0` has `D = 15 c > 0` at every coupling
and coupling slope `0`, the slope of the gapped family `g = 0`. DERIVED: `15` from `split_defect`; `16 = 2⁴`
the copies, `15 = 16 − 1`. -/
theorem point_blind {c : ℝ} (hc : 0 < c) (β : ℝ) :
    (∀ w : ℕ, 16 * ((16 : ℝ) ^ w * 0 + c) - ((16 : ℝ) ^ (w + 1) * 0 + c) = 15 * c) ∧ 0 < 15 * c ∧
      HasDerivAt (fun _ : ℝ => 15 * c) 0 β ∧ HasDerivAt (fun _ : ℝ => 15 * (0 : ℝ)) 0 β :=
  ⟨fun w => split_defect 0 c w, by positivity, hasDerivAt_const β _, hasDerivAt_const β _⟩

/-- **At a fixed window the `SU(N)` defect does not decrease from `β = 0`.** -/
theorem not_antitone_SU {N : ℕ} [NeZero N] {β : ℝ} (hβ : 0 ≤ β) {w : ℕ}
    (hD : 0 < StallRigid.Dw (MassGap.SUN.SU N) β w) :
    ¬ AntitoneOn (fun b => StallRigid.Dw (MassGap.SUN.SU N) b w) (Set.Icc 0 β) := by
  intro h
  have := h (Set.left_mem_Icc.mpr hβ) (Set.right_mem_Icc.mpr hβ) hβ
  simp only [StallRigid.Dw_SU, CouplingTower.windowCoupling_zero] at this
  rw [StallRigid.Dw_SU] at hD
  linarith

/-! ## 4. Curvature on a gauge-invariant direction -/

/-- The plaquette density `1 − ½ Re tr U` of `SU(2)` on the Cartan curve through `−1`. -/
def su2Curve (t : ℝ) : ℝ :=
  1 - (1 / 2) * (Matrix.trace (-(Matrix.diagonal
    ![Complex.exp (t * Complex.I), Complex.exp ((-t : ℝ) * Complex.I)]))).re

/-- **The curve is `1 + cos t`.** DERIVED: `½` the `1/N` at `N = 2`. -/
theorem su2_class_curve (t : ℝ) : su2Curve t = 1 + Real.cos t := by
  unfold su2Curve
  rw [Matrix.trace_neg, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.neg_re, Complex.add_re,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- **The Hessian on the invariant direction at the maximum is `−1`.** -/
theorem su2_class_hess : HasDerivAt (fun t => -Real.sin t) (-1) 0 ∧
    ∀ t, HasDerivAt su2Curve (-Real.sin t) t := by
  refine ⟨?_, fun t => ?_⟩
  · have h := (Real.hasDerivAt_sin 0).neg
    rw [Real.cos_zero] at h
    exact h
  · have he : su2Curve = fun t => 1 + Real.cos t := funext su2_class_curve
    rw [he]
    simpa using (Real.hasDerivAt_cos t).const_add 1

/-- **The curvature-dimension sum is negative on the invariant direction for `β > κ`.** -/
theorem cd_fails {κ β : ℝ} (h : κ < β) : κ + β * (-1) < 0 := by linarith

end MassGap.MasslessExclude
#print axioms MassGap.MasslessExclude.one_add_pos
#print axioms MassGap.MasslessExclude.hasDerivAt_mTerm
#print axioms MassGap.MasslessExclude.abs_deriv_mTerm_le
#print axioms MassGap.MasslessExclude.fixed_levels_flat
#print axioms MassGap.MasslessExclude.split_defect
#print axioms MassGap.MasslessExclude.perSite_tendsto
#print axioms MassGap.MasslessExclude.hasDerivAt_cutE
#print axioms MassGap.MasslessExclude.line_strictMono
#print axioms MassGap.MasslessExclude.point_blind
#print axioms MassGap.MasslessExclude.not_antitone_SU
#print axioms MassGap.MasslessExclude.su2_class_curve
#print axioms MassGap.MasslessExclude.su2_class_hess
#print axioms MassGap.MasslessExclude.cd_fails
