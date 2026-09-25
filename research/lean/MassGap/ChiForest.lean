import Mathlib
import MassGap.EntropyTools
import MassGap.ZoomForest
import MassGap.WeakCouplingWindow

/-!
# MassGap.ChiForest — the same forest in `χ²`, with variance-relative increments

## What it gives

1. **The entropy Props of `ZoomForest` hold.** `pinskerObs : ZoomForest.PinskerObs` and
   `klDataProcessing : ZoomForest.KLDataProcessing`, from `EntropyTools`. Consequently
   `sameForestAt_of_sameForestKL` (entropy forest to observable forest) and `sameForestKL_comp`
   (a coarser observer inherits the entropy forest) take no stated Prop.
2. **`χ²` bounds a mean relative to the variance.** `chiSq P Q = ∫ (dP/dQ − 1)² dQ` and
   `obsVar Q h = ∫ (h − ∫ h dQ)² dQ`. For probability measures `P`, `Q` with `ChiFinite P Q`
   (`P ≪ Q`, `(dP/dQ − 1)²` integrable), and `h` and `h²` integrable under `Q` and `h` integrable
   under `P`:
   `|∫ h dP − ∫ h dQ| ≤ √(chiSq P Q) · √(obsVar Q h)` (`abs_integral_sub_le_sqrt_chiSq_mul`). The
   proof is Cauchy–Schwarz in linear form: `∫ h dP − ∫ h dQ = ∫ (ρ − 1)(h − m) dQ` for the density
   `ρ` and any constant `m`, and `2 c s (ρ − 1)(h − m) ≤ c² (ρ − 1)² + s² (h − m)²`
   (`two_mul_integral_sub_le_of_density`), closed by `EntropyTools.sq_le_mul_of_forall_two_mul_le`.
3. **`ChiForest m δ`**: `δ` summable, successive laws `ChiFinite`, and `√(chiSq (m (k+1)) (m k)) ≤ δ k`.
   At probability laws `m k`:
   * `ChiForest.abs_step_le`: `|E_{k+1} f − E_k f| ≤ δ k · √(Var_k f)` for every `f` square-integrable
     along the sequence (`SqIntAlong`): the variance-relative increment.
   * `ChiForest.tendsto`: with `Var_k f ≤ V` at every step, `E_k f → forestLimit m f` at the rate
     `√V · ∑' i, δ (n + i)`.
   * `ChiForest.abs_conn_sub_le`: for `a`, `b`, `a b` square-integrable along the sequence with
     `Var_k a ≤ Va`, `Var_k b ≤ Vb`,
     `Var_k (a b) ≤ Vab` at every step, `|E_n b| ≤ B` and `|forestLimit m a| ≤ A`, the step-`n`
     connected correlation is within `(√Vab + B √Va + A √Vb) · ∑' i, δ (n + i)` of the limit's;
     `ChiForest.abs_conn_le` is the resulting bound on the step-`n` value.
4. **The window factor from a class-uniform relative remainder** (`eventually_factor_of_relative`).
   Over a class `S` of observables, let `cn n x`, `sn n x` be the step-`n` connected pairing at the
   window and at lag zero, `cL x`, `sL x` the limit's, with `sn n x ≥ 0`. If the limit decays by
   `q₀ ≥ 0` (`cL x ≤ q₀ sL x`), and both remainders are relative with one constant `κ` for the
   whole class (`cn n x ≤ cL x + T n · κ · sn n x`, `sL x ≤ sn n x + T n · κ · sn n x`), and
   `T n → 0`, then for every `q > q₀`, eventually in `n`, `cn n x ≤ q · sn n x` for all `x ∈ S`.

## What `ChiForest` at a fixed physical observer scale gives toward `FixedWindowDecay`

`WeakCouplingWindow.FixedWindowDecay τ p hN L` asks for one `q` with `0 < q < 1` such that for all
large `β` there is a lag `m ≠ 0` with `m · aRun N β ≤ L` at which every
`x ∈ gaugeInvHalfSpaceAlg τ p` and every `ε > 0` have, eventually along `periodicUltra hN β`,
`torusConn τ p hN β j x m ≤ q · torusConn τ p hN β j x 0 + ε`. Along one observer map at a fixed
physical resolution, `ChiForest` gives
each observable pair the remainder `(√Vab + B √Va + A √Vb) · T n` with `T n = ∑' i, δ (n + i) → 0`
(item 3), and item 4 turns a limit factor `q₀ < q` into the factor `q` at the step-`n` window,
uniformly over a class, once the remainder coefficient is bounded by `κ` times the step-`n` lag-zero
value with one `κ` for the class. So `ChiForest` supplies the relative form: the remainder carries
no sup-norm and scales with standard deviations.

## What remains

* **Class-uniform `κ`.** `√Vab + B √Va + A √Vb ≤ κ · sn n x` for every `x` in the class and every
  large `n`. `Va`, `Vb` bound the variances at every step, so this needs the variances along the
  zoom comparable to the step-`n` lag-zero value; `Vab` is a variance of a product, a fourth moment,
  so it needs a class-uniform bound of fourth moments by squared second moments.
* **The limit's factor.** `cL x ≤ q₀ · sL x` with `q₀ < 1` at the physical window: decay of the
  connected pairing of the forest limit at one physical distance.
* **The carriers** (as in `ZoomForest`): `FixedWindowDecay` is stated on the periodic tori along
  `periodicUltra`, at every large real `β`, for the lattice-scale class `gaugeInvHalfSpaceAlg`; the
  forest runs along the dyadic couplings in the infinite-volume states, and at a fixed resolution
  `ℓ` it controls functions of the `ℓ`-coarse field only.
* **The producer.** `ChiForest` of the Wilson observer laws is itself an input: a bound on
  `√(chiSq)` between successive views, summable in `k`.
-/

noncomputable section

namespace MassGap.ChiForest

open MeasureTheory Filter InformationTheory MassGap.ZoomForest MassGap.EntropyTools
open scoped Topology ENNReal

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-! ## 1. The entropy Props of `ZoomForest` -/

section Discharge

/-- **`ZoomForest.PinskerObs` holds**, by `EntropyTools.abs_integral_sub_le_sqrt_two_mul_klDiv`.

DERIVED: no numeral. -/
theorem pinskerObs : PinskerObs := by
  intro δ _ P Q hP hQ hkl f hf hb
  exact abs_integral_sub_le_sqrt_two_mul_klDiv P Q hkl hf hb

#print axioms pinskerObs

/-- **`ZoomForest.KLDataProcessing` holds**, by `EntropyTools.klDiv_map_le`.

DERIVED: no numeral. -/
theorem klDataProcessing : KLDataProcessing := by
  intro δ η _ _ P Q χ hP hQ hχ
  exact klDiv_map_le P Q hχ

#print axioms klDataProcessing

/-- **Entropy gives the forest, unconditionally.** `SameForestKL μ φ` at probability measures and
measurable observer maps gives `SameForestAt μ φ ε` with `ε k = √(2 · KL_k)`.

DERIVED: `2` is Pinsker's constant; `1` the step. -/
theorem sameForestAt_of_sameForestKL {μ : ℕ → Measure α} {φ : ℕ → α → β}
    (h : SameForestKL μ φ) (hprob : ∀ k, IsProbabilityMeasure (μ k))
    (hφ : ∀ k, Measurable (φ k)) :
    SameForestAt μ φ
      (fun k => Real.sqrt (2 * (klDiv ((μ (k + 1)).map (φ (k + 1))) ((μ k).map (φ k))).toReal)) :=
  h.sameForestAt pinskerObs hprob hφ

#print axioms sameForestAt_of_sameForestKL

/-- **A coarser observer inherits the entropy forest, unconditionally.**

DERIVED: no numeral. -/
theorem sameForestKL_comp {μ : ℕ → Measure α} {φ : ℕ → α → β} (h : SameForestKL μ φ)
    (hprob : ∀ k, IsProbabilityMeasure (μ k)) (hφ : ∀ k, Measurable (φ k)) {χ : β → γ}
    (hχ : Measurable χ) : SameForestKL μ (fun k => χ ∘ φ k) :=
  h.comp klDataProcessing hprob hφ hχ

#print axioms sameForestKL_comp

end Discharge

/-! ## 2. `χ²` and the variance-relative mean bound -/

section Chi

/-- **The `χ²` divergence** of `P` from `Q`: `∫ (dP/dQ − 1)² dQ`, as a real number. It is the `χ²`
divergence when `ChiFinite P Q` holds.

DERIVED: `1` is the density of `Q` against itself; `2` the square. -/
def chiSq (P Q : Measure β) : ℝ := ∫ x, ((P.rnDeriv Q x).toReal - 1) ^ 2 ∂Q

/-- **The variance of an observable** under `Q`: `∫ (h − ∫ h dQ)² dQ`.

DERIVED: `2` is the square. -/
def obsVar (Q : Measure β) (h : β → ℝ) : ℝ := ∫ x, (h x - ∫ y, h y ∂Q) ^ 2 ∂Q

/-- **Finite `χ²`**: `P ≪ Q` and `(dP/dQ − 1)²` is `Q`-integrable.

DERIVED: `1` and `2` are `chiSq`'s. -/
structure ChiFinite (P Q : Measure β) : Prop where
  /-- `P` is absolutely continuous with respect to `Q`. -/
  ac : P ≪ Q
  /-- The squared deviation of the density from one is integrable. -/
  sq_int : Integrable (fun x => ((P.rnDeriv Q x).toReal - 1) ^ 2) Q

/-- The pointwise Cauchy–Schwarz step: `2 c s (r h − h − m r + m) ≤ c² (r − 1)² + s² (h − m)²`,
since `r h − h − m r + m = (r − 1)(h − m)` and the difference is `(c (r − 1) − s (h − m))²`.

DERIVED: `2` is the cross term and the squares; `1` the mean of a density. -/
theorem chi_pointwise (r h m c s : ℝ) :
    2 * c * s * (r * h - h - m * r + m) ≤ c ^ 2 * (r - 1) ^ 2 + s ^ 2 * (h - m) ^ 2 := by
  nlinarith [sq_nonneg (c * (r - 1) - s * (h - m))]

#print axioms chi_pointwise

/-- **Cauchy–Schwarz for a mean difference, linear form.** Let `Q` be a probability measure, `ρ` a
`Q`-integrable function with `∫ ρ dQ = 1`, `ρ h` integrable with `∫ ρ h dQ = ∫ h dP`, and
`(ρ − 1)²`, `h`, `h²` integrable under `Q`. For all reals `m`, `c`, `s`:
`2 c s (∫ h dP − ∫ h dQ) ≤ c² ∫ (ρ − 1)² dQ + s² ∫ (h − m)² dQ`. The left side is
`2 c s ∫ (ρ − 1)(h − m) dQ`, and `chi_pointwise` integrates.

DERIVED: `2` is `chi_pointwise`'s; `1` the total mass of `P` read through `ρ`. -/
theorem two_mul_integral_sub_le_of_density {P Q : Measure β} [IsProbabilityMeasure Q]
    {ρ h : β → ℝ} (hρ : Integrable ρ Q) (hρ1 : ∫ x, ρ x ∂Q = 1)
    (hρh : Integrable (fun x => ρ x * h x) Q) (hρP : ∫ x, ρ x * h x ∂Q = ∫ x, h x ∂P)
    (hU : Integrable (fun x => (ρ x - 1) ^ 2) Q) (hQ1 : Integrable h Q)
    (hQ2 : Integrable (fun x => h x ^ 2) Q) (m c s : ℝ) :
    2 * c * s * (∫ x, h x ∂P - ∫ x, h x ∂Q)
      ≤ c ^ 2 * ∫ x, (ρ x - 1) ^ 2 ∂Q + s ^ 2 * ∫ x, (h x - m) ^ 2 ∂Q := by
  have i1 : Integrable (fun x => ρ x * h x - h x) Q := hρh.sub hQ1
  have i2 : Integrable (fun x => ρ x * h x - h x - m * ρ x) Q := i1.sub (hρ.const_mul m)
  have iE : Integrable (fun x => ρ x * h x - h x - m * ρ x + m) Q := i2.add (integrable_const m)
  have hV : Integrable (fun x => (h x - m) ^ 2) Q := by
    refine ((hQ2.sub (hQ1.const_mul (2 * m))).add (integrable_const (m ^ 2))).congr
      (ae_of_all _ (fun x => ?_))
    show h x ^ 2 - 2 * m * h x + m ^ 2 = (h x - m) ^ 2
    ring
  have e1 : ∫ x, (ρ x * h x - h x - m * ρ x + m) ∂Q
      = ∫ x, (ρ x * h x - h x - m * ρ x) ∂Q + ∫ _x, m ∂Q := integral_add i2 (integrable_const m)
  have e2 : ∫ x, (ρ x * h x - h x - m * ρ x) ∂Q
      = ∫ x, (ρ x * h x - h x) ∂Q - ∫ x, m * ρ x ∂Q := integral_sub i1 (hρ.const_mul m)
  have e3 : ∫ x, (ρ x * h x - h x) ∂Q = ∫ x, ρ x * h x ∂Q - ∫ x, h x ∂Q := integral_sub hρh hQ1
  have e4 : ∫ x, m * ρ x ∂Q = m * ∫ x, ρ x ∂Q := integral_const_mul m _
  have e5 : ∫ _x, m ∂Q = m := by rw [integral_const, probReal_univ, one_smul]
  rw [hρ1, mul_one] at e4
  have hE : ∫ x, (ρ x * h x - h x - m * ρ x + m) ∂Q = ∫ x, h x ∂P - ∫ x, h x ∂Q := by
    linarith
  have eL : ∫ x, 2 * c * s * (ρ x * h x - h x - m * ρ x + m) ∂Q
      = 2 * c * s * ∫ x, (ρ x * h x - h x - m * ρ x + m) ∂Q := integral_const_mul _ _
  have eR : ∫ x, (c ^ 2 * (ρ x - 1) ^ 2 + s ^ 2 * (h x - m) ^ 2) ∂Q
      = c ^ 2 * ∫ x, (ρ x - 1) ^ 2 ∂Q + s ^ 2 * ∫ x, (h x - m) ^ 2 ∂Q := by
    rw [integral_add (hU.const_mul (c ^ 2)) (hV.const_mul (s ^ 2)), integral_const_mul,
      integral_const_mul]
  rw [← hE, ← eL, ← eR]
  exact integral_mono (iE.const_mul _) ((hU.const_mul (c ^ 2)).add (hV.const_mul (s ^ 2)))
    (fun x => chi_pointwise _ _ _ _ _)

#print axioms two_mul_integral_sub_le_of_density

/-- **`χ²` bounds a mean difference relative to the variance.** For probability measures with
`ChiFinite P Q`, and `h` with `h`, `h²` integrable under `Q` and `h` integrable under `P`:
`|∫ h dP − ∫ h dQ| ≤ √(chiSq P Q) · √(obsVar Q h)`.

DERIVED: `2` is the square in `h²`; `1` and `−1` are the two signs of the difference; `0` the sign
split. -/
theorem abs_integral_sub_le_sqrt_chiSq_mul {P Q : Measure β} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : ChiFinite P Q) {h : β → ℝ} (hQ1 : Integrable h Q)
    (hQ2 : Integrable (fun x => h x ^ 2) Q) (hP1 : Integrable h P) :
    |∫ x, h x ∂P - ∫ x, h x ∂Q| ≤ Real.sqrt (chiSq P Q) * Real.sqrt (obsVar Q h) := by
  have hρ : Integrable (fun x => (P.rnDeriv Q x).toReal) Q := Measure.integrable_toReal_rnDeriv
  have hρ1 : ∫ x, (P.rnDeriv Q x).toReal ∂Q = 1 := by
    rw [Measure.integral_toReal_rnDeriv hPQ.ac, probReal_univ]
  have hρh : Integrable (fun x => (P.rnDeriv Q x).toReal * h x) Q :=
    (integrable_toReal_rnDeriv_mul_iff hPQ.ac).mpr hP1
  have hρP : ∫ x, (P.rnDeriv Q x).toReal * h x ∂Q = ∫ x, h x ∂P :=
    integral_toReal_rnDeriv_mul hPQ.ac
  have key : ∀ c s : ℝ, 2 * c * s * (∫ x, h x ∂P - ∫ x, h x ∂Q)
      ≤ c ^ 2 * chiSq P Q + s ^ 2 * obsVar Q h := fun c s =>
    two_mul_integral_sub_le_of_density (ρ := fun x => (P.rnDeriv Q x).toReal) hρ hρ1 hρh hρP
      hPQ.sq_int hQ1 hQ2 (∫ y, h y ∂Q) c s
  have hA : 0 ≤ chiSq P Q := by
    unfold chiSq
    exact integral_nonneg (fun x => sq_nonneg _)
  have hB : 0 ≤ obsVar Q h := by
    unfold obsVar
    exact integral_nonneg (fun x => sq_nonneg _)
  have hsq : (∫ x, h x ∂P - ∫ x, h x ∂Q) ^ 2 ≤ chiSq P Q * obsVar Q h := by
    rcases le_total 0 (∫ x, h x ∂P - ∫ x, h x ∂Q) with hX | hX
    · exact sq_le_mul_of_forall_two_mul_le hX hA hB (fun c _ => by linarith [key c 1])
    · have h' := sq_le_mul_of_forall_two_mul_le (neg_nonneg.mpr hX) hA hB
        (fun c _ => by linarith [key c (-1)])
      nlinarith [h']
  rw [← Real.sqrt_mul hA]
  exact Real.abs_le_sqrt hsq

#print axioms abs_integral_sub_le_sqrt_chiSq_mul

end Chi

/-! ## 3. The forest in `χ²` -/

section Forest

/-- **Square-integrable along a sequence of laws**: `f` and `f²` are integrable under every `m k`.

DERIVED: `2` is the square. -/
structure SqIntAlong (m : ℕ → Measure β) (f : β → ℝ) : Prop where
  /-- `f` is integrable at every step. -/
  integrable : ∀ k, Integrable f (m k)
  /-- `f²` is integrable at every step. -/
  integrable_sq : ∀ k, Integrable (fun x => f x ^ 2) (m k)

/-- **The same forest in `χ²`, with its increments.** `δ` is summable, successive laws have finite
`χ²`, and `√(chiSq (m (k+1)) (m k)) ≤ δ k`.

DERIVED: `1` is the step. -/
structure ChiForest (m : ℕ → Measure β) (δ : ℕ → ℝ) : Prop where
  /-- The increments are summable. -/
  summable : Summable δ
  /-- Successive laws have finite `χ²`. -/
  finite : ∀ k, ChiFinite (m (k + 1)) (m k)
  /-- The square root of the successive `χ²` is at most the increment. -/
  step : ∀ k, Real.sqrt (chiSq (m (k + 1)) (m k)) ≤ δ k

/-- The increments of a `ChiForest` are nonnegative.

DERIVED: `0` is the sign. -/
theorem ChiForest.nonneg {m : ℕ → Measure β} {δ : ℕ → ℝ} (h : ChiForest m δ) (k : ℕ) :
    0 ≤ δ k :=
  (Real.sqrt_nonneg _).trans (h.step k)

#print axioms ChiForest.nonneg

/-- **The variance-relative increment.** Under `ChiForest m δ` at probability laws, for `f`
square-integrable along the sequence: `|E_{k+1} f − E_k f| ≤ δ k · √(Var_k f)`.

DERIVED: `1` is the step. -/
theorem ChiForest.abs_step_le {m : ℕ → Measure β} {δ : ℕ → ℝ} (h : ChiForest m δ)
    (hprob : ∀ k, IsProbabilityMeasure (m k)) {f : β → ℝ} (hf : SqIntAlong m f) (k : ℕ) :
    |∫ x, f x ∂(m (k + 1)) - ∫ x, f x ∂(m k)| ≤ δ k * Real.sqrt (obsVar (m k) f) := by
  haveI := hprob (k + 1)
  haveI := hprob k
  exact (abs_integral_sub_le_sqrt_chiSq_mul (h.finite k) (hf.integrable k) (hf.integrable_sq k)
    (hf.integrable (k + 1))).trans (mul_le_mul_of_nonneg_right (h.step k) (Real.sqrt_nonneg _))

#print axioms ChiForest.abs_step_le

/-- **Every observable with bounded variances converges, at a variance-relative rate.** Under
`ChiForest m δ` at probability laws, for `f` square-integrable along the sequence with
`Var_k f ≤ V` at every step: `E_k f → forestLimit m f` along `atTop`, and
`|E_n f − forestLimit m f| ≤ √V · ∑' i, δ (n + i)` at every `n`.

DERIVED: `1` is the step. -/
theorem ChiForest.tendsto {m : ℕ → Measure β} {δ : ℕ → ℝ} (h : ChiForest m δ)
    (hprob : ∀ k, IsProbabilityMeasure (m k)) {f : β → ℝ} (hf : SqIntAlong m f) {V : ℝ}
    (hV : ∀ k, obsVar (m k) f ≤ V) :
    Tendsto (fun k => ∫ x, f x ∂(m k)) atTop (𝓝 (forestLimit m f)) ∧
      ∀ n, |∫ x, f x ∂(m n) - forestLimit m f| ≤ Real.sqrt V * ∑' i, δ (n + i) := by
  obtain ⟨L, hL, hrate⟩ := exists_tendsto_of_abs_sub_le (s := fun k => ∫ x, f x ∂(m k))
    (h.summable.mul_left (Real.sqrt V)) (fun k =>
      (h.abs_step_le hprob hf k).trans (by
        calc δ k * Real.sqrt (obsVar (m k) f) ≤ δ k * Real.sqrt V :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hV k)) (h.nonneg k)
          _ = Real.sqrt V * δ k := mul_comm _ _))
  have hlim : forestLimit m f = L := hL.limUnder_eq
  refine ⟨by rw [hlim]; exact hL, fun n => ?_⟩
  rw [hlim, ← tsum_mul_left]
  exact hrate n

#print axioms ChiForest.tendsto

end Forest

/-! ## 4. Connected correlations with relative remainders -/

section Connected

/-- The algebra of the relative connected-correlation comparison: if `xab`, `xa`, `xb` are within
`Tab`, `Ta`, `Tb` of `lab`, `la`, `lb`, with `|xb| ≤ B` and `|la| ≤ A`, the connected combinations
are within `Tab + Ta B + A Tb`.

DERIVED: no numeral. -/
theorem abs_conn_sub_le_rel {xab xa xb lab la lb Tab Ta Tb A B : ℝ} (hab : |xab - lab| ≤ Tab)
    (ha : |xa - la| ≤ Ta) (hb : |xb - lb| ≤ Tb) (hxb : |xb| ≤ B) (hla : |la| ≤ A) :
    |(xab - xa * xb) - (lab - la * lb)| ≤ Tab + Ta * B + A * Tb := by
  have hTa : 0 ≤ Ta := (abs_nonneg _).trans ha
  have hA : 0 ≤ A := (abs_nonneg _).trans hla
  have e : (xab - xa * xb) - (lab - la * lb)
      = (xab - lab) - ((xa - la) * xb + la * (xb - lb)) := by ring
  have hY : |(xa - la) * xb| ≤ Ta * B := by
    rw [abs_mul]
    exact mul_le_mul ha hxb (abs_nonneg _) hTa
  have hZ : |la * (xb - lb)| ≤ A * Tb := by
    rw [abs_mul]
    exact mul_le_mul hla hb (abs_nonneg _) hA
  rw [e, abs_le]
  constructor
  · linarith [neg_abs_le (xab - lab), le_abs_self ((xa - la) * xb), le_abs_self (la * (xb - lb))]
  · linarith [le_abs_self (xab - lab), neg_abs_le ((xa - la) * xb), neg_abs_le (la * (xb - lb))]

#print axioms abs_conn_sub_le_rel

/-- **The step-`n` connected correlation is within a variance-relative remainder of the
limit's.** Under `ChiForest m δ` at probability laws, for `a`, `b`, `a b` square-integrable along
the sequence with `Var_k a ≤ Va`, `Var_k b ≤ Vb`, `Var_k (a b) ≤ Vab` at every step,
`|forestLimit m a| ≤ A` and `|E_n b| ≤ B`:
`|(E_n[a b] − E_n a · E_n b) − (L(a b) − L(a) L(b))| ≤ (√Vab + B √Va + A √Vb) · ∑' i, δ (n + i)`,
`L = forestLimit m`.

DERIVED: no numeral. -/
theorem ChiForest.abs_conn_sub_le {m : ℕ → Measure β} {δ : ℕ → ℝ} (h : ChiForest m δ)
    (hprob : ∀ k, IsProbabilityMeasure (m k)) {a b : β → ℝ} (ha : SqIntAlong m a)
    (hb : SqIntAlong m b) (hab : SqIntAlong m (fun x => a x * b x)) {Va Vb Vab A B : ℝ}
    (hVa : ∀ k, obsVar (m k) a ≤ Va) (hVb : ∀ k, obsVar (m k) b ≤ Vb)
    (hVab : ∀ k, obsVar (m k) (fun x => a x * b x) ≤ Vab)
    (hA : |forestLimit m a| ≤ A) (n : ℕ) (hB : |∫ x, b x ∂(m n)| ≤ B) :
    |(∫ x, a x * b x ∂(m n) - (∫ x, a x ∂(m n)) * ∫ x, b x ∂(m n))
      - (forestLimit m (fun x => a x * b x) - forestLimit m a * forestLimit m b)|
      ≤ (Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb) * ∑' i, δ (n + i) := by
  obtain ⟨-, hrab⟩ := h.tendsto hprob hab hVab
  obtain ⟨-, hra⟩ := h.tendsto hprob ha hVa
  obtain ⟨-, hrb⟩ := h.tendsto hprob hb hVb
  have h1 := abs_conn_sub_le_rel (hrab n) (hra n) (hrb n) hB hA
  refine h1.trans (le_of_eq ?_)
  ring

#print axioms ChiForest.abs_conn_sub_le

/-- **Decay of the limit transfers to every step, up to a relative remainder.** Under the
hypotheses of `ChiForest.abs_conn_sub_le`, if the limit's connected correlation of `a`, `b` is at
most `D` in absolute value, the step-`n` one is at most
`D + (√Vab + B √Va + A √Vb) · ∑' i, δ (n + i)`.

DERIVED: no numeral. -/
theorem ChiForest.abs_conn_le {m : ℕ → Measure β} {δ : ℕ → ℝ} (h : ChiForest m δ)
    (hprob : ∀ k, IsProbabilityMeasure (m k)) {a b : β → ℝ} (ha : SqIntAlong m a)
    (hb : SqIntAlong m b) (hab : SqIntAlong m (fun x => a x * b x)) {Va Vb Vab A B : ℝ}
    (hVa : ∀ k, obsVar (m k) a ≤ Va) (hVb : ∀ k, obsVar (m k) b ≤ Vb)
    (hVab : ∀ k, obsVar (m k) (fun x => a x * b x) ≤ Vab)
    (hA : |forestLimit m a| ≤ A) (n : ℕ) (hB : |∫ x, b x ∂(m n)| ≤ B) {D : ℝ}
    (hD : |forestLimit m (fun x => a x * b x) - forestLimit m a * forestLimit m b| ≤ D) :
    |∫ x, a x * b x ∂(m n) - (∫ x, a x ∂(m n)) * ∫ x, b x ∂(m n)|
      ≤ D + (Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb) * ∑' i, δ (n + i) := by
  have h1 := h.abs_conn_sub_le hprob ha hb hab hVa hVb hVab hA n hB
  have h2 := abs_add_le
    ((∫ x, a x * b x ∂(m n) - (∫ x, a x ∂(m n)) * ∫ x, b x ∂(m n))
      - (forestLimit m (fun x => a x * b x) - forestLimit m a * forestLimit m b))
    (forestLimit m (fun x => a x * b x) - forestLimit m a * forestLimit m b)
  rw [sub_add_cancel] at h2
  linarith

#print axioms ChiForest.abs_conn_le

end Connected

/-! ## 5. The window factor from a class-uniform relative remainder -/

section Window

/-- **A limit factor `q₀` becomes a step factor `q > q₀`, uniformly over a class, once the
remainders are relative with one constant.** Over `S : Set ι`, let `cn n x`, `sn n x` be step-`n`
values (the connected pairing at the window and at lag zero), `cL x`, `sL x` the limit's, with
`sn n x ≥ 0`. If `cL x ≤ q₀ sL x` with `q₀ ≥ 0`, `cn n x ≤ cL x + T n · κ · sn n x`,
`sL x ≤ sn n x + T n · κ · sn n x`, and `T n → 0`, then for every `q > q₀`, eventually in `n`,
`cn n x ≤ q · sn n x` for every `x ∈ S`. `ChiForest.abs_conn_sub_le` supplies the two remainders
with `T n = ∑' i, δ (n + i)` whenever its coefficient `√Vab + B √Va + A √Vb` is at most
`κ · sn n x` on the class.

DERIVED: `0` is the limit of `T`, the lower end of `q₀` and of `sn`; `1` is the weight of the window
remainder in `κ (1 + q₀)`, beside the weight `q₀` of the lag-zero remainder. -/
theorem eventually_factor_of_relative {ι : Type*} (S : Set ι) (cn sn : ℕ → ι → ℝ)
    (cL sL : ι → ℝ) {T : ℕ → ℝ} (hT : Tendsto T atTop (𝓝 0)) {q₀ q κ : ℝ} (hq0 : 0 ≤ q₀)
    (hq : q₀ < q) (hlim : ∀ x ∈ S, cL x ≤ q₀ * sL x)
    (hc : ∀ n, ∀ x ∈ S, cn n x ≤ cL x + T n * (κ * sn n x))
    (hs : ∀ n, ∀ x ∈ S, sL x ≤ sn n x + T n * (κ * sn n x))
    (hsn : ∀ n, ∀ x ∈ S, 0 ≤ sn n x) :
    ∀ᶠ n in atTop, ∀ x ∈ S, cn n x ≤ q * sn n x := by
  have hT' := hT.mul_const (κ * (1 + q₀))
  rw [zero_mul] at hT'
  have hev : ∀ᶠ n in atTop, T n * (κ * (1 + q₀)) < q - q₀ :=
    (tendsto_order.1 hT').2 _ (sub_pos.mpr hq)
  filter_upwards [hev] with n hn x hx
  have h1 := hc n x hx
  have h2 := hs n x hx
  have h3 := hlim x hx
  have h4 := hsn n x hx
  have h5 : q₀ * sL x ≤ q₀ * (sn n x + T n * (κ * sn n x)) := mul_le_mul_of_nonneg_left h2 hq0
  have h6 : T n * (κ * (1 + q₀)) * sn n x ≤ (q - q₀) * sn n x :=
    mul_le_mul_of_nonneg_right hn.le h4
  nlinarith [h1, h3, h5, h6]

#print axioms eventually_factor_of_relative

end Window

end MassGap.ChiForest
