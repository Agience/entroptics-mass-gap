import Mathlib
import MassGap.RestoreShimsClay
import MassGap.ChiForest

noncomputable section

/-!
# MassGap.OneCubeShims — what the restored Dobrushin–Shlosman chain reads from the live tree

The chain `DSBlockContract`, `DSOllivier`, `DSBoxFloor`, `OverlapSweep` reads through `ClayRoutes` some names that now
live in `RestoreShimsClay`, one lemma that no live module carries (`exp_half_sq`), and the `χ²` forest section of
`ClayRoutes`, which `ObserverEnergyM` states one theorem from. This module supplies them and is imported once, by
`ObserverGapSplit`, the root of that chain, so the rest of the chain reads as archived. The `ClayRoutes` section below is
the text of commit `a396ae5`, less `stepConn` and `ChiCarrierBridge`, which the live `ClayRoutes` keeps.

DERIVED (module-wide): `2` the halving and the square; `0`, `1` as noted on each declaration.
-/

namespace MassGap

/-- The square of the rate at half the spacing is the rate at the spacing.

DERIVED: `2` is the halving and the square. -/
theorem exp_half_sq (K a : ℝ) : Real.exp (-(K * (a / 2))) ^ 2 = Real.exp (-(K * a)) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

#print axioms exp_half_sq

end MassGap

namespace MassGap.ClayRoutes

variable {N : ℕ}

section Chi

open MeasureTheory Filter
open scoped Topology

variable {Ω : Type} [MeasurableSpace Ω] {ι : Type*}

/-- **The limit connected pairing** of `a`, `b` along `m`:
`L(a b) − L(a) L(b)`, `L = ZoomForest.forestLimit m`.

DERIVED: no numeral. -/
def limConn (m : ℕ → MeasureTheory.Measure Ω) (a b : Ω → ℝ) : ℝ :=
  ZoomForest.forestLimit m (fun x => a x * b x)
    - ZoomForest.forestLimit m a * ZoomForest.forestLimit m b

/-- **A relative remainder for one pair.** `a`, `b` and `a b` are square-integrable along `m`, with
variance bounds `Va`, `Vb`, `Vab` at every step and `|forestLimit m a| ≤ A`, and at every step `n`
some `B ≥ |E_n b|` has `√Vab + B √Va + A √Vb ≤ κ · s n`: the coefficient of
`ChiForest.ChiForest.abs_conn_sub_le` is at most `κ` times the scale `s n`.

DERIVED: no numeral. -/
def RelRemainder (m : ℕ → MeasureTheory.Measure Ω) (a b : Ω → ℝ) (s : ℕ → ℝ) (κ : ℝ) : Prop :=
  ChiForest.SqIntAlong m a ∧ ChiForest.SqIntAlong m b ∧ ChiForest.SqIntAlong m (fun x => a x * b x) ∧
    ∃ Va Vb Vab A : ℝ, (∀ k, ChiForest.obsVar (m k) a ≤ Va) ∧ (∀ k, ChiForest.obsVar (m k) b ≤ Vb) ∧
      (∀ k, ChiForest.obsVar (m k) (fun x => a x * b x) ≤ Vab) ∧
      |ZoomForest.forestLimit m a| ≤ A ∧
      ∀ n : ℕ, ∃ B : ℝ, |∫ x, b x ∂(m n)| ≤ B ∧
        Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb ≤ κ * s n

/-- **The class-uniform `κ`.** For every `i ∈ S`: the step-`n` lag-zero pairing
`stepConn m n (a0 i) (b0 i)` is non-negative at every `n`, and both the window pair `(aw i, bw i)`
and the lag-zero pair `(a0 i, b0 i)` have a `RelRemainder` at the scale of that lag-zero pairing,
with the one constant `κ`.

DERIVED: `0` is the sign of the lag-zero pairing. -/
def ClassKappa (m : ℕ → MeasureTheory.Measure Ω) (S : Set ι) (aw bw a0 b0 : ι → Ω → ℝ)
    (κ : ℝ) : Prop :=
  ∀ i ∈ S, (∀ n, 0 ≤ stepConn m n (a0 i) (b0 i)) ∧
    RelRemainder m (aw i) (bw i) (fun n => stepConn m n (a0 i) (b0 i)) κ ∧
    RelRemainder m (a0 i) (b0 i) (fun n => stepConn m n (a0 i) (b0 i)) κ

/-- **The limit factor at the window.** `0 ≤ q₀ < 1` and, for every `i ∈ S`, the limit window pairing
is at most `q₀` times the limit lag-zero pairing.

DERIVED: `0` is the lower end of `q₀`; `1` is the factor the decay must beat. -/
def LimitFactor (m : ℕ → MeasureTheory.Measure Ω) (S : Set ι) (aw bw a0 b0 : ι → Ω → ℝ)
    (q₀ : ℝ) : Prop :=
  0 ≤ q₀ ∧ q₀ < 1 ∧ ∀ i ∈ S, limConn m (aw i) (bw i) ≤ q₀ * limConn m (a0 i) (b0 i)

/-- **The step pairing is within the relative remainder of the limit's.** Under
`ChiForest.ChiForest m δ` at probability laws and `RelRemainder m a b s κ`:
`|stepConn m n a b − limConn m a b| ≤ (∑' i, δ (n + i)) · κ · s n` at every `n`
(`ChiForest.ChiForest.abs_conn_sub_le`, with the tail sum non-negative by `ChiForest.ChiForest.nonneg`).

DERIVED: no numeral. -/
theorem abs_stepConn_sub_le {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ}
    (h : ChiForest.ChiForest m δ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {a b : Ω → ℝ} {s : ℕ → ℝ} {κ : ℝ} (hR : RelRemainder m a b s κ) (n : ℕ) :
    |stepConn m n a b - limConn m a b| ≤ (∑' i, δ (n + i)) * (κ * s n) := by
  obtain ⟨ha, hb, hab, Va, Vb, Vab, A, hVa, hVb, hVab, hA, hB⟩ := hR
  obtain ⟨B, hBn, hcoef⟩ := hB n
  have h1 := h.abs_conn_sub_le hprob ha hb hab hVa hVb hVab hA n hBn
  have hT : 0 ≤ ∑' i, δ (n + i) := tsum_nonneg (fun i => h.nonneg (n + i))
  calc |stepConn m n a b - limConn m a b|
      ≤ (Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb) * ∑' i, δ (n + i) := h1
    _ = (∑' i, δ (n + i)) * (Real.sqrt Vab + B * Real.sqrt Va + A * Real.sqrt Vb) := mul_comm _ _
    _ ≤ (∑' i, δ (n + i)) * (κ * s n) := mul_le_mul_of_nonneg_left hcoef hT

#print axioms abs_stepConn_sub_le

/-- **Every factor above the limit's is a step factor, uniformly on the class.** Under
`ChiForest.ChiForest m δ` at probability laws, `ClassKappa m S aw bw a0 b0 κ` and
`LimitFactor m S aw bw a0 b0 q₀`: for every `q > q₀`, for all large `n`, every `i ∈ S` has
`stepConn m n (aw i) (bw i) ≤ q · stepConn m n (a0 i) (b0 i)`. The tail sums `∑' i, δ (n + i)` tend
to `0` (`tendsto_sum_nat_add`), `abs_stepConn_sub_le` gives the two relative remainders, and
`ChiForest.eventually_factor_of_relative` concludes.

DERIVED: no numeral in the statement. -/
theorem eventually_window_factor {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ}
    (h : ChiForest.ChiForest m δ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ} (hK : ClassKappa m S aw bw a0 b0 κ)
    (hq : LimitFactor m S aw bw a0 b0 q₀) {q : ℝ} (hqq : q₀ < q) :
    ∀ᶠ n in atTop, ∀ i ∈ S, stepConn m n (aw i) (bw i) ≤ q * stepConn m n (a0 i) (b0 i) := by
  obtain ⟨hq0, -, hlim⟩ := hq
  have hT : Tendsto (fun n => ∑' i, δ (n + i)) atTop (𝓝 0) := by
    refine (tendsto_sum_nat_add δ).congr (fun n => ?_)
    exact tsum_congr (fun i => congrArg δ (add_comm i n))
  have hc : ∀ n, ∀ i ∈ S, stepConn m n (aw i) (bw i)
      ≤ limConn m (aw i) (bw i) + (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := by
    intro n i hi
    obtain ⟨-, hRw, -⟩ := hK i hi
    have h1 : |stepConn m n (aw i) (bw i) - limConn m (aw i) (bw i)|
        ≤ (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := abs_stepConn_sub_le h hprob hRw n
    linarith [le_abs_self (stepConn m n (aw i) (bw i) - limConn m (aw i) (bw i))]
  have hs : ∀ n, ∀ i ∈ S, limConn m (a0 i) (b0 i)
      ≤ stepConn m n (a0 i) (b0 i) + (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := by
    intro n i hi
    obtain ⟨-, -, hR0⟩ := hK i hi
    have h1 : |stepConn m n (a0 i) (b0 i) - limConn m (a0 i) (b0 i)|
        ≤ (∑' k, δ (n + k)) * (κ * stepConn m n (a0 i) (b0 i)) := abs_stepConn_sub_le h hprob hR0 n
    linarith [neg_abs_le (stepConn m n (a0 i) (b0 i) - limConn m (a0 i) (b0 i))]
  have hsn : ∀ n, ∀ i ∈ S, 0 ≤ stepConn m n (a0 i) (b0 i) := by
    intro n i hi
    obtain ⟨hnn, -, -⟩ := hK i hi
    exact hnn n
  exact ChiForest.eventually_factor_of_relative S (fun n i => stepConn m n (aw i) (bw i))
    (fun n i => stepConn m n (a0 i) (b0 i)) (fun i => limConn m (aw i) (bw i))
    (fun i => limConn m (a0 i) (b0 i)) hT hq0 hqq hlim hc hs hsn

#print axioms eventually_window_factor

/-- **One step factor strictly below `1`.** Under the hypotheses of `eventually_window_factor`:
some `0 < q < 1` has, for all large `n`, `stepConn m n (aw i) (bw i) ≤ q · stepConn m n (a0 i) (b0 i)`
at every `i ∈ S`.

DERIVED: `0` and `1` are the ends of `q`. CHOSEN: `q = (1 + q₀)/2` in the proof; any `q ∈ (q₀, 1)`
serves. -/
theorem exists_window_factor {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ}
    (h : ChiForest.ChiForest m δ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ} (hK : ClassKappa m S aw bw a0 b0 κ)
    (hq : LimitFactor m S aw bw a0 b0 q₀) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ n in atTop, ∀ i ∈ S, stepConn m n (aw i) (bw i) ≤ q * stepConn m n (a0 i) (b0 i) := by
  obtain ⟨hq0, hq1, hlim⟩ := hq
  exact ⟨(1 + q₀) / 2, by linarith, by linarith,
    eventually_window_factor h hprob hK ⟨hq0, hq1, hlim⟩ (by linarith)⟩

#print axioms exists_window_factor

/-- **`FixedWindowDecay` from the `χ²` forest, modulo the carrier bridge.** Under
`ChiForest.ChiForest m δ` at probability laws, `ClassKappa m S aw bw a0 b0 κ`,
`LimitFactor m S aw bw a0 b0 q₀` and `ChiCarrierBridge τ p hN L m S aw bw a0 b0`:
`WeakCouplingWindow.FixedWindowDecay τ p hN L`. `exists_window_factor` gives `0 < q < 1` at all
large steps; the bridge's step assignment carries it to all large `β`, and at each `x` and `ε`
the torus pairing at `lag` is at most `q ·` (torus pairing at lag `0` `+ ε/2`) `+ ε/2`.

DERIVED: `4` is the spacetime dimension; `0` is the excluded rank. CHOSEN: `ε/2` in the proof, the
slack handed to the bridge; any split of `ε` serves. -/
theorem fixedWindowDecay_of_chiForest (τ : Fin 4) (p : ℤ) (hN : N ≠ 0) {L : ℝ}
    {m : ℕ → MeasureTheory.Measure Ω} {δ : ℕ → ℝ} (h : ChiForest.ChiForest m δ)
    (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (m k))
    {S : Set ι} {aw bw a0 b0 : ι → Ω → ℝ} {κ q₀ : ℝ} (hK : ClassKappa m S aw bw a0 b0 κ)
    (hq : LimitFactor m S aw bw a0 b0 q₀) (hbr : ChiCarrierBridge τ p hN L m S aw bw a0 b0) :
    WeakCouplingWindow.FixedWindowDecay τ p hN L := by
  obtain ⟨q, hq0, hq1, hev⟩ := exists_window_factor h hprob hK hq
  obtain ⟨step, hstep, hbev⟩ := hbr
  refine ⟨q, hq0, hq1, ?_⟩
  filter_upwards [hstep.eventually hev, hbev] with β hfac hb
  obtain ⟨lag, hlag0, hlagL, hx⟩ := hb
  refine ⟨lag, hlag0, hlagL, fun x hxS ε hε => ?_⟩
  obtain ⟨i, hi, hij⟩ := hx x hxS
  filter_upwards [hij (ε / 2) (half_pos hε)] with j hj
  obtain ⟨h1, h2⟩ := hj
  have h3 : stepConn m (step β) (aw i) (bw i) ≤ q * stepConn m (step β) (a0 i) (b0 i) := hfac i hi
  have h4 : q * stepConn m (step β) (a0 i) (b0 i)
      ≤ q * (MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε / 2) :=
    mul_le_mul_of_nonneg_left h2 hq0.le
  have h5 : q * (ε / 2) ≤ ε / 2 := mul_le_of_le_one_left (half_pos hε).le hq1.le
  have h6 : q * (MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + ε / 2)
      = q * MassGap.PeriodicReduce.torusConn τ p hN β j x 0 + q * (ε / 2) := mul_add _ _ _
  linarith

#print axioms fixedWindowDecay_of_chiForest

end Chi

end MassGap.ClayRoutes
