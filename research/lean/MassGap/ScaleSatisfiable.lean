import Mathlib
import MassGap.ScaleIdentityNoGo
import MassGap.ExistenceFlow
import MassGap.ClassicalLimit

/-!
# MassGap.ScaleSatisfiable — what the scale clause of the substrate asks, and what meets it

`SU2Best.SubstrateCoreAt W z b Wf` carries `scale : MultiScaleAll.ScaleControlAll b Wf` and
`top : Wf b = W`. `ScaleIdentityNoGo` shows the clause is false when `Wf b` is eventually the identity. This
module places the clause: which flows meet it outright, what the `top` field reduces it to, and what it asks
of `W = ObserverFlowSUN.sunFam hN2 c hc0 hc s₀` in `ClayNarrow.NarrowInputsN`. Declarations are in the
namespace `MassGap.ScaleSatisfiable`.

## 1. A flow with pure-gauge output meets the clause at every scale (proved)

* **`mField_one`**: every channel field of the clause (every admissible bare monomial `bR N i` and every
  symmetrised plaquette density) reads `0` at the unit configuration (`ClassicalLimit.monoV_one`,
  `ReflAvg.reflAvg_one`, `ExistenceFlow.symPlaq_one`); by gauge invariance also at every gauge transform of
  it (`mField_pureGauge`).
* **`scaleControlAll_of_pureGauge`**: if, eventually in the step, at every `s ∈ [a_k, b]` the map
  `(Wf s).V k` sends every configuration to a gauge transform of the unit configuration, then
  `ScaleControlAll b Wf` holds with `t = 1`, `C = 1`, `γ = γP = 0`. Every flowed field is `0`, so every
  exponential moment is `1`. The clause reads every `s ∈ [a_k, b]`, and here each is met.
* **`not_V_eq_one`**: at `N ≥ 2` no `ConfFlow` sends every configuration to the unit configuration: gauge
  covariance would give `1 = g · 1` for every gauge function `g`, false at `g = diag(i, −i, 1, …)` on the
  sites with `x₀ = 0` (`ObserverFlowSUN.witness_mem`). The constant map is not a configuration flow. Whether
  some `ConfFlow` meets the hypothesis of `scaleControlAll_of_pureGauge` (finite range, gauge and reflection
  covariant, flat output on all of `ℤ⁴`) is not decided here. `ExistenceFlow.flatFlow` is flat only inside
  the box `[-L_k, L_k]⁴` and returns the bare link outside it, so it does not meet the hypothesis; the clause
  quantifies over every plaquette `q` at one step, and a plaquette outside the box reads its bare value.

## 2. The `top` field pins the clause to `W` at `s = b` (proved)

* **`scaleAt_top`**: `ScaleControlAll b Wf` and `Wf b = W` give the moment of `W` itself at `s = b`:
  `∃ t C γ γP, 0 < t ∧ ∀ᶠ k, ScaleAt (fun _ => W) t C γ γP k b`. So a degenerate choice of `Wf` at `s < b`
  does not lighten the clause: the moment at `s = b` is read on `W`. In `NarrowInputsN`,
  `W = sunFam … s₀` (`substrateCoreAt_scale`).
* **`msMu_one`**: at `s = 1` the strength is `t` for every index and every `γ` (`afLog γ 1 = 1`), so
  `ScaleAt … k 1` does not read `γ`, `γP` (`scaleAt_one_iff`).
* **`scaleControlAll_one_iff`**: `(∃ Wf, Wf 1 = W ∧ ScaleControlAll 1 Wf)` iff
  `∃ t > 0, ∃ C, ∀ᶠ k, ∀ j, ν_k(exp(t a_k^{−d_j} |O_j ∘ W_k|)) ≤ C` (the moment of `W` alone at `s = 1`,
  `γ = 0`). The reverse direction is `MultiScaleAll.scale_const` (the constant family).
* **`substrateCoreAt_const`**: that moment and `af` give `SubstrateCoreAt W z 1 (fun _ => W)`.

So at the physical scale `b = 1` the fields `b_pos`, `top`, `scale` of the substrate core are, at any `W`,
exactly the one statement

  `(M_W)`  `∃ t > 0, ∃ C, ∀ᶠ k, ∀ j ∈ MIx, ν_k(exp(t a_k^{−d_j} |O_j ∘ W_k|)) ≤ C`,

`O_j` the bare monomials `bR N i` (dimension `cdim i`) and the symmetrised plaquette densities (dimension
`4`), uniformly over the infinitely many indices `j`. Other values of `b` add the per-index factor
`b^{d_j} / (1 + |log b|)^{γ_j}` to the rate. The choice of `Wf` at `s < b` matters to the rest of the bundle
(`ExpandStrong` reads `Wf s` at small `s`), not to `scale`, which the constant family meets once `(M_W)`
holds.

## 3. What `(M_W)` asks at `W = sunFam … s₀` (argued; no declaration)

The rooted lower bounds do not reach a non-identity flow. `PlaquetteFloor.stateK_plaq_ge` bounds the bare
plaquette (`ν_k(plaq) ≥ c/β_k²`), which is what `ScaleIdentityNoGo` uses at `V_k = id`.
`FlowMoments.not_classMoments_of_reachBlowup` takes `ReachBlowup` as a hypothesis and needs
`a_k · range_k → 0`; at `sunFam … s₀` the reach is `a_k (⌊s₀/a_k⌋ + 3) → s₀ > 0`. No declaration in the
tree states a lower bound on the flowed plaquette of `sunFam … s₀` at `s₀ > 0`, `c > 0`.

`(M_W)` asks, through `1 + x ≤ eˣ`, at least `ν_k(sym plaq_q ∘ V_k) = O(a_k⁴)`, and through the exponential,
`P(a_k^{−4} sym plaq_q ∘ V_k > x) ≤ C e^{−t x}`. The flowed plaquette of a smoothing to radius `ρ` is of
order `g² a⁴/ρ⁴` in the bulk. The construction of `sunFam` carries a second contribution. Each output link
is computed by `n = ⌊(s₀/a)²⌋` block steps inside its own box of half-width `R = ⌊s₀/a⌋`, the configuration
held at its bare value outside the box (`ObserverFlowSUN.obsFlowG`). Linearised, one block step moves a
link toward its six staples with weight `6c/(1 + 6c)`, a walk with per-direction variance `2c/(1 + 6c)` per
step; after `n` steps the spread is `σ = s₀ √(2c/(1 + 6c))` against a box of half-width `s₀`. The weight
of the held boundary in the output link is of order `e^{−(1 + 6c)/(4c)}`: a constant, not vanishing as
`a → 0`. The boxes of the four links of one plaquette are shifted against each other, so the bare boundary
fluctuations (size `g` per lattice plaquette, spread over the `R³` boundary sites with weight
`e^{−(1+6c)/(4c)}/R³` each) do not cancel in the plaquette, and the flowed plaquette receives a term of order
`e^{−(1+6c)/(2c)} g² R^{−3} ∝ a³`. Then `a⁻⁴ ν_k(sym plaq ∘ V_k) → ∞` and `(M_W)` fails at every `t > 0`,
as at the identity flow. This is an estimate on the measure (a sum of `R³` weakly correlated boundary
contributions), not a declaration, and it is the open point of the scale clause at `sunFam`: either a proof
that the boundary leakage is `O(a⁴)` in the plaquette, or a lower bound of order `a^{4−δ}` that makes
`SubstrateCoreAt (sunFam … s₀) z b Wf` false for every `b`, `Wf`. The estimate depends on the box being of
the same physical size as the smoothing radius; any finite-reach observer whose smoothing kernel has a
fixed fraction of its weight at the reach meets the same term.

Foundational footprint only (`#print axioms` at the end).

DERIVED (module-wide): `0` the axis and site of the witness link, the exponents `γ`, the value of a flat
field; `1` the unit configuration, the scale `s = 1` where `afLog` is `1`, the rate and the bound of the
pure-gauge discharge; `2` the least colour count.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.ScaleSatisfiable

open Filter
open scoped Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumFlow MassGap.ObserverEnergyMoments MassGap.ObserverSymField MassGap.ObserverEnergyBox
  MassGap.MultiScaleAll MassGap.SU2Best MassGap.ObserverFlowSUN MassGap.CompositesBuild MassGap.ClayData
  MassGap.ReflAvg MassGap.ClayStatement

variable {N : ℕ}

/-! ## 1. Pure-gauge output -/

/-- **Every channel field reads `0` at the unit configuration.** DERIVED: `0` the value; `1` the unit
configuration. -/
theorem mField_one [NeZero N] : ∀ j : MIx, (mField j : LField (MassGap.SUN.SU N)).1 (1 : Cfg N) = 0
  | Sum.inl i => reflAvg_one _ _ (ClassicalLimit.monoV_one i.2.1 i.2.2)
  | Sum.inr q => ExistenceFlow.symPlaq_one (NeZero.ne N) _ ⟨q, rfl⟩

/-- **Every channel field reads `0` at a gauge transform of the unit configuration.** DERIVED: `0` the
value; `1` the unit configuration. -/
theorem mField_pureGauge [NeZero N] (j : MIx) (g : ISite → MassGap.SUN.SU N) :
    (mField j : LField (MassGap.SUN.SU N)).1 (GaugeInvariantAlgebra.igaugeTransform g (1 : Cfg N)) = 0 := by
  rw [(mField j : LField (MassGap.SUN.SU N)).2.2 g 1]
  exact mField_one j

/-- **A flow with pure-gauge output at every scale meets `ScaleControlAll`**, with `t = C = 1` and
`γ = γP = 0`. DERIVED: `0` the exponents and the flat field; `1` the rate, the bound and the unit
configuration. -/
theorem scaleControlAll_of_pureGauge [NeZero N] {b : ℝ} {Wf : ℝ → ConfFlow N}
    (h : ∀ᶠ k in atTop, ∀ s : ℝ, dySpacing N k ≤ s → s ≤ b → ∀ U : Cfg N,
      ∃ g : ISite → MassGap.SUN.SU N, (Wf s).V k U = GaugeInvariantAlgebra.igaugeTransform g 1) :
    ScaleControlAll b Wf := by
  refine ⟨1, 1, fun _ => 0, 0, one_pos, ?_⟩
  filter_upwards [h] with k hk s hs hsb j
  have hz : expC ((msMu 1 (fun _ => 0) 0 j s / dySpacing N k ^ mDim j)
      • msAbs ((Wf s).fieldMap k (mField j)).1) = 1 := by
    refine ContinuousMap.ext fun U => ?_
    obtain ⟨g, hg⟩ := hk s hs hsb U
    have hF : ((Wf s).fieldMap k (mField j)).1 U = 0 := by
      show (mField j : LField (MassGap.SUN.SU N)).1 ((Wf s).V k U) = 0
      rw [hg]
      exact mField_pureGauge j g
    simp only [expC_apply, ContinuousMap.smul_apply, msAbs_apply, smul_eq_mul, hF, abs_zero, mul_zero,
      Real.exp_zero, ContinuousMap.one_apply]
  rw [hz, (stateK (NeZero.ne N) k).map_one]

/-- **No configuration flow sends every configuration to the unit configuration** (`N ≥ 2`): gauge
covariance would make the unit configuration fixed by every gauge function. DERIVED: `0` the axis and the
site of the witness link; `1` the unit configuration; `2` the least colour count. -/
theorem not_V_eq_one (hN2 : 2 ≤ N) (W : ConfFlow N) (k : ℕ) : ¬ ∀ U : Cfg N, W.V k U = 1 := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  let w : MassGap.SUN.SU (m + 2) := ⟨Matrix.diagonal (witnessVec m), witness_mem m⟩
  let g : ISite → MassGap.SUN.SU (m + 2) := fun x => if x 0 = 0 then w else 1
  have h1 := W.gauge k g 1
  rw [h (GaugeInvariantAlgebra.igaugeTransform g 1), h 1] at h1
  have h2 := congrFun h1 ((0 : Fin 4), (0 : ISite))
  have hg0 : g (0 : ISite) = w := if_pos rfl
  have hg1 : g (MassGap.GibbsSpec.ishift 0 (0 : ISite)) = 1 :=
    if_neg (by simp [MassGap.GibbsSpec.ishift])
  have h3 : (1 : MassGap.SUN.SU (m + 2)) = w := by
    have e : GaugeInvariantAlgebra.igaugeTransform g (1 : Cfg (m + 2)) ((0 : Fin 4), (0 : ISite))
        = g (0 : ISite) * 1 * (g (MassGap.GibbsSpec.ishift 0 (0 : ISite)))⁻¹ := rfl
    rw [e, hg0, hg1] at h2
    simpa using h2
  have h4 := congrArg (fun A : MassGap.SUN.SU (m + 2) => (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) 0 0) h3
  simp [w, witnessVec, Complex.ext_iff] at h4

/-! ## 2. The `top` field -/

/-- **`ScaleControlAll` and `Wf b = W` give the moment of `W` at `s = b`.** DERIVED: no numeral. -/
theorem scaleAt_top [NeZero N] {W : ConfFlow N} {b : ℝ} {Wf : ℝ → ConfFlow N} (hb : 0 < b)
    (htop : Wf b = W) (h : ScaleControlAll b Wf) :
    ∃ (t C : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < t ∧
      ∀ᶠ k in atTop, ScaleAt (fun _ => W) t C γ γP k b := by
  obtain ⟨t, C, γ, γP, ht, hev⟩ := h
  refine ⟨t, C, γ, γP, ht, ?_⟩
  filter_upwards [hev, (tendsto_dySpacing N).eventually (eventually_le_nhds hb)] with k hk hkb
  have hk' := hk b hkb le_rfl
  simpa only [ScaleAt, htop] using hk'

/-- **The scale field of the substrate core reads `W` at `s = b`.** DERIVED: no numeral. -/
theorem substrateCoreAt_scale [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {b : ℝ}
    {Wf : ℝ → ConfFlow N} (S : SubstrateCoreAt W z b Wf) :
    ∃ (t C : ℝ) (γ : Ix0 → ℝ) (γP : ℝ), 0 < t ∧
      ∀ᶠ k in atTop, ScaleAt (fun _ => W) t C γ γP k b :=
  scaleAt_top S.b_pos S.top S.scale

/-- **At `s = 1` the strength is `t`**, every index and every exponent. DERIVED: `1` the scale. -/
theorem msMu_one (t : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (j : MIx) : msMu t γ γP j 1 = t := by
  cases j <;> simp [msMu, afLog]

/-- **`ScaleAt` at `s = 1` does not read the exponents.** DERIVED: `0` the exponents; `1` the scale. -/
theorem scaleAt_one_iff [NeZero N] (Wf : ℝ → ConfFlow N) (t C : ℝ) (γ : Ix0 → ℝ) (γP : ℝ) (k : ℕ) :
    ScaleAt Wf t C γ γP k 1 ↔ ScaleAt Wf t C (fun _ => 0) 0 k 1 := by
  simp only [ScaleAt, msMu_one]

/-- **At `b = 1` the scale and top fields are the moment of `W` alone**: a family with `Wf 1 = W` meeting
`ScaleControlAll 1` exists iff `W` has the exponential moments at `s = 1` with `γ = γP = 0`.
DERIVED: `0` the exponents; `1` the scale. -/
theorem scaleControlAll_one_iff [NeZero N] (W : ConfFlow N) :
    (∃ Wf : ℝ → ConfFlow N, Wf 1 = W ∧ ScaleControlAll 1 Wf) ↔
      ∃ t C : ℝ, 0 < t ∧ ∀ᶠ k in atTop, ScaleAt (fun _ => W) t C (fun _ => 0) 0 k 1 := by
  constructor
  · rintro ⟨Wf, htop, h⟩
    obtain ⟨t, C, γ, γP, ht, hev⟩ := scaleAt_top one_pos htop h
    exact ⟨t, C, ht, hev.mono fun k hk => (scaleAt_one_iff _ t C γ γP k).1 hk⟩
  · rintro ⟨t, C, ht, h⟩
    exact ⟨fun _ => W, rfl, scale_const ht h⟩

/-- **The substrate core at the constant family** from the moment of `W` at `s = 1` and `af`.
DERIVED: `0` the exponents; `1` the scale. -/
theorem substrateCoreAt_const [NeZero N] {W : ConfFlow N} {z : Chan → ℕ → ℝ} {t C : ℝ} (ht : 0 < t)
    (hm : ∀ᶠ k in atTop, ScaleAt (fun _ => W) t C (fun _ => 0) 0 k 1)
    (haf : ∃ G : ℝ → ℝ, TwoPointKernel (NeZero.ne N) (rhoD (fR N) z) G ∧ AFCoefficient N G) :
    SubstrateCoreAt W z 1 (fun _ => W) :=
  ⟨one_pos, rfl, scale_const ht hm, haf⟩

end MassGap.ScaleSatisfiable

end

#print axioms MassGap.ScaleSatisfiable.mField_one
#print axioms MassGap.ScaleSatisfiable.mField_pureGauge
#print axioms MassGap.ScaleSatisfiable.scaleControlAll_of_pureGauge
#print axioms MassGap.ScaleSatisfiable.not_V_eq_one
#print axioms MassGap.ScaleSatisfiable.scaleAt_top
#print axioms MassGap.ScaleSatisfiable.substrateCoreAt_scale
#print axioms MassGap.ScaleSatisfiable.msMu_one
#print axioms MassGap.ScaleSatisfiable.scaleAt_one_iff
#print axioms MassGap.ScaleSatisfiable.scaleControlAll_one_iff
#print axioms MassGap.ScaleSatisfiable.substrateCoreAt_const
