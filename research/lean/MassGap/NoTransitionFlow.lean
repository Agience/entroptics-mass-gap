import Mathlib
import MassGap.MatchAt
import MassGap.NoTransition
import MassGap.ReadsSlabWilson

/-!
# MassGap.NoTransitionFlow — no transition along the zoom-out, as a statement about the chunk flow

The owner: "the aperture is fixed relative to the observer"; "it's the same aperture whether you are
near or far, zoomed or not"; "the observer is constant"; "nothing absolute, measure relative to the
reading". Read on the zoom-out from the length where Bałaban's control ends (`BalabanUV`) to the
length where chunks are nearly independent (`MatchAt`): the observer's chunk law runs through a
sequence of chunk theories `T₀ → T₁ → …` under `ℓ → 2ℓ`, every quantity read in the observer's own
chunk units, and its type cannot change along the way.

This module states that on sequences of chunk-unit readings, proves which readings are monotone or
grow along the zoom-out, and names what each leaves open. Chunk side at step `k`:
`side ℓ₀ k = 2ᵏ ℓ₀`.

## 1. Type and transition (`Scales`, `Grows`, `Transition`)

* `Scales c s`: `s (k+1) = c · s k` (an exact doubling law); `Grows c s`: `c · s k ≤ s (k+1)`.
  The type at step `k` is the sign of `s k` (`0 < s k`: confined in the observer's units);
  `Transition s`: the type differs between two consecutive steps.
* `scales_iter`, `type_const_of_scales`, `zero_const_of_scales`, `noTransition_of_scales`: under an
  exact law with `c > 0` the type is the same at every step; there is no transition.
* `grows_pos`: under `Grows` with `c > 0` the confined type is kept (Coulomb → confined is allowed).
  `grows_tendsto`: with `c > 1` and `s 0 > 0`, `s → ∞`. `grows_one_not_sufficient`: with `c = 1`
  (monotone only) the reading need not exceed every threshold. So any factor `c > 0` keeps the
  confined type; a factor `c > 1` is what drives the reading to infinity.
* `scales_four_fixed_iff`: a reading assumed to obey the units law `Scales 4` and also constant along
  the steps is `0` at every step (it restates `4s = s ⇒ s = 0`). Read on a cost of the form `σ ℓ²`:
  a chunk law left unchanged by every step (as route (3)'s invariance, `MatchAt.matchAt_of_fixedPoint`,
  would leave it; that theorem is about activities, not about this sequence) can carry such a cost
  only at `σ = 0`. Interpretation, not proved here: the other end of the flow is the strong-coupling
  end, zero activities, which satisfy `MatchAt` (`matchAt_zero`).

## 2. The edge cost in chunk units (`chunkTension`)

`chunkTension σ ℓ = σ ℓ²`: a tension `σ` read in units of the chunk.

* `chunkTension_double`: `σ (2ℓ)² = 4 σ ℓ²`. `scales_tension`: `σ f (2ᵏ ℓ₀)²` obeys `Scales 4`
  (`f > 0` a face factor; an identity of the definition). So the reading `σ ℓ²` of a fixed tension
  grows geometrically along the zoom-out if `σ > 0` and stays zero if `σ = 0`: for that reading there
  is no transition. That the cost per chunk of an actual chunk law is `σ ℓ²` is not shown here, and
  the proxy below shows it need not be at weak coupling.
* `kpCost z κ = 1 + κ + log(4z + 1)`, `count_cond_of_ge`: a cost per chunk above it meets
  `4 z e^{1+κ−τ} ≤ 1`, the condition of `MatchAt.matchAt_of_count`.
* `matchAt_along_flow`: chunk theories whose activities obey the count with a cost per chunk `s k`
  that grows by a factor `c > 1` from `s 0 > 0` satisfy `MatchAt` from some step on.
  `matchAt_of_tension_flow`: the case `s k = σ f (2ᵏ ℓ₀)²`, `σ > 0`. `eventually_length_match`: the
  same threshold read through `MatchAt.exists_length_match` along `side ℓ₀ k → ∞`; the two agree.
  The zoom-out of one measure reduces to `σ > 0` plus the count hypothesis at each step (the control
  of the chunk activities by `σ`).

### One-way running on the chunk cost (`RunsOneWay`)

`RunsOneWay b s`: `s k + b (s k)² ≤ s (k+1)` at every doubling, `s k` the cost per chunk of the chunk
theory at step `k` (link 1 of `NoTransition`, "running is one-way", read on the chunk flow at every
step and not only at one loop).

* `runsOneWay_lower`: `s k ≥ s 0 + k b (s 0)²`. `runsOneWay_tendsto`: with `b > 0`, `s 0 > 0`, the
  cost tends to infinity. `runsOneWay_zero_fixed`: at `b = 0` a fixed cost `s ≡ c` is allowed (the
  Coulomb fixed point of the proxy below) and does not grow.
* `uniform_steps_of_runsOneWay`: a start `s j 0 ≥ s₀` at every zoom `j` (an assumption; the intended
  reading is the coupling at the fixed physical length, which in the one-loop form is the same at
  every zoom on the observer's line, `NoTransition.coupling_at_observer_const`) and one `b` give one
  number of doublings `K` with `s j k ≥ T` at every zoom and every `k ≥ K`; the proof takes any
  natural `K ≥ (T − s₀)/(b s₀²)` (the bound is in the proof, not in the statement). `matchAt_uniform_of_runsOneWay`: with the count at
  cost `s j k`, `MatchAt` at every zoom from step `K` on: one physical length `2ᴷ r*` for every zoom.
  This form needs no `σ` as input, but its hypothesis `∀ j, RunsOneWay b (s j)` with `b > 0` is
  unsatisfiable for every flow that grows at most linearly per doubling, including the confining
  reading `Scales 4` and the Migdal–Kadanoff strong end (`OneWayCost.not_runsOneWay_of_linear`,
  `OneWayCost.runsOneWay_family_unsat`): these two theorems hold, and no intended flow meets their
  hypothesis. The per-doubling route is the capped form `OneWayCost.RunsOneWayTo` (the rise `b s²`
  is required only below the target cost), consumed by `OneWayCost.matchAt_uniform_of_runsOneWayTo`.
  The floor route of section 3 does not depend on either form.

## 3. One length for every zoom (the Clay content)

A line of measures, zoom `j` (finer spacing), physical tension `σ j`; chunks of physical side `L`.

* `uniform_length_of_floor`: a floor `NoTransition.Floor σ` (a positive lower bound at every zoom)
  gives one physical length `L₀` with the count condition at every zoom and every `L ≥ L₀`.
  `floor_of_uniform_length`, `uniform_length_iff_floor`: for `z ≥ 1/4` the converse holds, so one
  length for every zoom is exactly a floor on the tension.
* `kp_fails_of_tendsto_zero`, `no_uniform_length_of_tendsto_zero`: if `σ j → 0` (and `z ≥ 1/4`), at
  every `L` the condition fails at all fine enough zooms: no uniform length.
  `fade_confined_no_uniform`: the `fade` line has `σ j > 0` at every zoom, no floor, and no length
  that serves every zoom. (With the count hypothesis, `matchAt_of_tension_flow` would give each zoom
  the match at its own length.) `σ > 0` at one zoom, or at every zoom separately, is not enough.
* `matchAt_uniform_of_edgesCannotEndNA`: for `SU(N)`, `N ≥ 2`, `NoTransition.EdgesCannotEndNA` on the
  line (link 2 with its escape named; at `SU(N)` it is exactly `Floor σ`,
  `NoTransition.edgesCannotEndNA_SU_iff`) and the count hypothesis at every zoom and every length `L`
  give one `L₀` with `MatchAt` at every zoom and every `L ≥ L₀`.

## 4. The observer's relative rate (data processing)

* `obs_rate_zoomOut`: any coarse reading `c` of a Markov slab `(π, K)` has, across `n` slabs, rate
  at most `ρ(K)ⁿ` (`RelativeGap.corrOn_of_maxCorr`, `GapL2.maxCorr_pow_le`); `obs_coarser_zoomOut`: a
  coarser reading `h ∘ c` keeps the bound (`RelativeGap.readings_comp`). The observer's correlation
  cannot exceed the fine one.
* `fullRate_zoomOut`: for a reversible kernel `ρ(K^{2ᵏ}) = ρ(K)^{2ᵏ}`
  (`ReadsSlabWilson.maxCorr_pow_eq`). `fullGap_scales`: the fine gap in chunk units,
  `−log ρ(K^{2ᵏ})`, obeys `Scales 2` (the physical mass is the same at every chunk size).
  `fullRate_type_const`: `ρ(K^{2ᵏ}) < 1 ↔ ρ(K) < 1`. The type of the fine reading does not change
  along the zoom-out, and that type is the gap of the measure itself.
* `observer_rate_not_monotone` (control): a reversible Markov slab (the swap of two independent
  fair bits) on which the observer's reading of the first bit has rate `0` across one slab and no
  rate below `1` across two. The observer's own coarse rate is not monotone along the zoom-out
  (`ρ_obs(2ℓ) ≤ ρ_obs(ℓ)²` fails); only the fine rate is submultiplicative. The example is degenerate:
  `swapK² = 1`, so its fine rate is `ρ(K) = 1` (no gap); it shows the failure of the inequality, not
  its failure on a gapped slab.

## 5. The `U(1)` control

* `u1_flow`: at `σ = 0` the chunk-unit edge cost is `0` at every step (`Scales 4`, so no transition
  along the zoom-out either) and the count condition fails at every step for `z ≥ 1/4`.
* `u1_line_no_uniform`: the `U(1)` line of measures (positive tension below zoom `k₁`, zero from
  `k₁` on: the Coulomb phase, Guth 1980, Fröhlich–Spencer 1982, cited, not proved here) has no
  uniform length. For `U(1)` the type changes across the line of measures (the bare coupling), not
  along the zoom-out of one measure; the monotone quantity that fails is the floor along the line,
  `NoTransition.u1_oneWay_no_floor`. `NoTransition.u1_escapes`: link 2 says nothing at `U(1)`.

## What it reduces to

Along the zoom-out of one measure, "no transition" holds for every reading assumed covariant under
the units change (`noTransition_of_scales`; proved for the fine rate of a reversible slab,
`fullRate_type_const`; by definition for `σ ℓ²`) and carries no content beyond the type at one
length: for the fine reading the type is the gap of that measure; for the edge cost it is `σ > 0`. The residual for 4D `SU(N)`, in the owner's terms, takes one of two forms.

Through the edge cost (`matchAt_uniform_of_edgesCannotEndNA`):

* (R1) the edge cost does not fade along the line of measures: a positive floor on the physical
  string tension of the 4D `SU(N)` Wilson measure uniformly in the zoom (`Floor σ`, equal to
  `EdgesCannotEndNA` at `SU(N)`; with a limit it is `EdgeCost.StringScalingAt`);
* (R2) the chunk activities are controlled by it: the count hypothesis of `matchAt_of_count` with
  cost `σ f L²` for the block-spin effective action at every zoom and every chunk side `L` (as the
  theorem assumes it; only `L ≥ L₀` is used).

Through the running (`OneWayCost.matchAt_uniform_of_runsOneWayTo`, the capped form; the uncapped
`matchAt_uniform_of_runsOneWay` has a hypothesis no flow with at most linear growth per doubling
meets, `OneWayCost.runsOneWay_family_unsat`):

* (R1') at every doubling past the fixed length, at every zoom, the cost per chunk of the block-spin
  effective action rises by at least `b s²` with one `b > 0` while it is below the target
  `kpCost z κ`, and does not fall below that target once reached (`OneWayCost.RunsOneWayTo`);
* (R2') the chunk activities obey the count at that cost.

The floor route (`uniform_length_of_floor`, `uniform_length_iff_floor`,
`matchAt_uniform_of_edgesCannotEndNA`) does not use (R1') in either form.

(R1) at one zoom alone is the lattice area law at one bare coupling: proved at strong coupling
(Osterwalder–Seiler 1978; cited, not proved here), open for 4D `SU(N)` at weak coupling, and by
`fade_confined_no_uniform` not enough. (R1) uniformly in the zoom is the continuum confinement
statement, which is a separate property from the mass gap: neither is derived from the other here.
(R1') is local in the scale (one doubling at a time, like `FineEnd.FineEndStep` at the fine end) and
asks no `σ`, but it is a statement about the block-spin effective actions of the stretch, which no
declaration constructs for 4D `SU(N)` beyond the weak-coupling regime of `BalabanUV`; it fails for the
`U(1)` proxy at weak coupling; for the `SU(2)` proxy the rise by `b s²` holds on the tracked steps
from step 1 up to `kpCost` (not at step 0, the step out of the Wilson action, at `β = 2.5, 4`),
checked at three couplings and at most 17 steps, with (R2') not checked. Above `kpCost` the proxy's
running coefficient behaves like `(3 s − 4 log 4)/s² → 0`, so the proxy meets the capped form and
not the uncapped one. Either way this
route moves the open stretch to a named pair of hypotheses; it does not make it weaker than the gap.
The pairs are not independent: `σ` (or `s`) is tied to the chunk activities only through the count
hypothesis, so given the floor, the count at `σ j` implies the count at the constant `σ₀`, and each
pair is one hypothesis — the block-spin chunk activities at every zoom obey the count at one uniform
cost `σ₀ f L²`.

## Numerics (`research/code/no_transition_flow_checks.py`, under 10 s, no Monte Carlo)

Migdal–Kadanoff recursion (`b = 2`, `d = 4`: bond moving `f → f⁴`, decimation `t → t⁴`) on class
functions, used as a proxy only: an approximation, not a bound on the true RG and not a statement
about the 4D Wilson measure. `s = −log t_F` the proxy's cost per renormalised plaquette (not
assumed to be of the form `σ ℓ²`), `ρ` the
largest normalised character coefficient (the observer's rate per chunk), `D` the relative entropy of
the plaquette weight to Haar measure, `v = w(−1)/w(1)` the centre-vortex weight of one plaquette.

* `SU(2)`, `β_std = 1, 2.5, 4`: from step 1 on `s` rises, `ρ` and `D` fall and `v` rises at every
  step; step 0 (out of the Wilson action) breaks all four at `β = 2.5, 4`. The running coefficient
  `(s_{k+1} − s_k)/s_k²` is at least `0.26, 0.16, 0.15` on the tracked steps from step 1 on while
  `s < kpCost` (negative at step 0 for `β = 2.5, 4`); above `kpCost` it behaves like
  `(3 s − 4 log 4)/s² → 0`; `s ≥ kpCost = 6.39` at step `4, 10, 15`; where `s > 4`,
  `|s_{k+1} − 4(s_k − log 4)| ≤ 7.3·10⁻³` (the units law `Scales 4` less the entropy of the four
  moved plaquettes).
* `U(1)`, `β = 2, 4`: `s` falls over the first two or three steps and then stops at a fixed cost
  (`0.264`, `0.128`),
  `ρ` rises to a fixed value below `1` (`0.768`, `0.880`), the running coefficient tends to `0`, the
  count condition never holds. The chunk law reaches a fixed point at a finite cost per plaquette;
  since a fixed `s` is not `4ᵏ` times anything positive, it is not a positive `σ` read as `σ ℓ²`
  (`scales_four_fixed_iff` on that reading). At `β = 0.5` (strong coupling) `U(1)` reaches the count
  condition at step 5.
* At every tracked step of both groups decimation (a 4-fold convolution, a Markov operator fixing
  Haar measure) lowers `D`, as data processing requires (for `ρ` it is automatic: `t ↦ t⁴`), and
  bond moving raises `D`.
* Data processing on random reversible 12-state slabs: `ρ(K²) = ρ(K)²` and the observer's coarse
  rate across `n = 1, 2, 4` slabs is below `ρ(K)ⁿ`; the swap control reads `0` and `1`.
* The `K` of the proof of `uniform_steps_of_runsOneWay` at `b = 0.15`, `s₀ = 0.4` is `250`; the
  recursion `s_{k+1} = s_k + b s_k²` itself passes the count condition after 19 steps, the `SU(2)`
  proxy at `β = 4` after 15.

DERIVED (module-wide): `2` the doubling `ℓ → 2ℓ`; `4 = 2²` the area of a chunk face in chunk units;
`1` the growth factor at which `Grows` stops forcing a limit and the KP constant `a = 1` of
`matchAt_of_count`; `1/4` the entropy at which `4z ≥ 1`, so that `4 z e^{1+κ} > 1`; `1/4` also the
uniform weight of the four states of the swap control; `0` the sign defining the type.
-/

set_option autoImplicit false

noncomputable section

namespace MassGap.NoTransitionFlow

open Filter Topology Finset
open MassGap.MatchAt MassGap.NoTransition GapL2 MassGap.RelativeGap

/-! ## 1. Type and transition -/

/-- The chunk side at step `k` of the zoom-out: `2ᵏ ℓ₀`. -/
def side (ℓ₀ : ℝ) (k : ℕ) : ℝ := 2 ^ k * ℓ₀

/-- **An exact doubling law** with factor `c`. -/
def Scales (c : ℝ) (s : ℕ → ℝ) : Prop := ∀ k, s (k + 1) = c * s k

/-- **Growth by a factor** `c` at every step. -/
def Grows (c : ℝ) (s : ℕ → ℝ) : Prop := ∀ k, c * s k ≤ s (k + 1)

/-- **A transition along the zoom-out**: the type (the sign of the reading) differs between two
consecutive steps. -/
def Transition (s : ℕ → ℝ) : Prop := ∃ k, ¬ (0 < s k ↔ 0 < s (k + 1))

theorem scales_iter {c : ℝ} {s : ℕ → ℝ} (h : Scales c s) (k : ℕ) : s k = c ^ k * s 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [h k, ih, pow_succ]; ring

/-- **Under an exact law the confined type is the same at every step.** -/
theorem type_const_of_scales {c : ℝ} {s : ℕ → ℝ} (hc : 0 < c) (h : Scales c s) (k : ℕ) :
    (0 < s k ↔ 0 < s 0) := by
  rw [scales_iter h k]
  exact ⟨fun hx => pos_of_mul_pos_right hx (pow_pos hc k).le, fun hx => mul_pos (pow_pos hc k) hx⟩

/-- **Under an exact law a zero reading stays zero.** -/
theorem zero_const_of_scales {c : ℝ} {s : ℕ → ℝ} (hc : 0 < c) (h : Scales c s) (k : ℕ) :
    (s k = 0 ↔ s 0 = 0) := by
  rw [scales_iter h k, mul_eq_zero]
  exact ⟨fun hx => hx.resolve_left (pow_ne_zero k hc.ne'), Or.inr⟩

/-- **No transition under an exact law.** -/
theorem noTransition_of_scales {c : ℝ} {s : ℕ → ℝ} (hc : 0 < c) (h : Scales c s) :
    ¬ Transition s := by
  rintro ⟨k, hk⟩
  exact hk ((type_const_of_scales hc h k).trans (type_const_of_scales hc h (k + 1)).symm)

theorem Scales.grows {c : ℝ} {s : ℕ → ℝ} (h : Scales c s) : Grows c s := fun k => (h k).ge

theorem grows_iter {c : ℝ} {s : ℕ → ℝ} (hc : 0 ≤ c) (h : Grows c s) (k : ℕ) :
    c ^ k * s 0 ≤ s k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc c ^ (k + 1) * s 0 = c * (c ^ k * s 0) := by ring
      _ ≤ c * s k := mul_le_mul_of_nonneg_left ih hc
      _ ≤ s (k + 1) := h k

/-- **Growth keeps the confined type.** -/
theorem grows_pos {c : ℝ} {s : ℕ → ℝ} (hc : 0 < c) (h : Grows c s) (h0 : 0 < s 0) (k : ℕ) :
    0 < s k :=
  lt_of_lt_of_le (mul_pos (pow_pos hc k) h0) (grows_iter hc.le h k)

/-- **Growth by a factor above one drives the reading to infinity.** -/
theorem grows_tendsto {c : ℝ} {s : ℕ → ℝ} (hc : 1 < c) (h : Grows c s) (h0 : 0 < s 0) :
    Tendsto s atTop atTop :=
  tendsto_atTop_mono (grows_iter (by linarith) h)
    ((tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const h0)

/-- **Monotone alone is not enough**: the constant reading `1` grows by the factor `1` and does not
tend to infinity. -/
theorem grows_one_not_sufficient :
    Grows 1 (fun _ => (1 : ℝ)) ∧ ¬ Tendsto (fun _ : ℕ => (1 : ℝ)) atTop atTop := by
  refine ⟨fun _ => by norm_num, fun h => ?_⟩
  obtain ⟨k, hk⟩ := (tendsto_atTop.1 h 2).exists
  norm_num at hk

/-- **An exact fixed point of a units-covariant edge cost is at zero.** A reading with
`s (k+1) = 4 s k` that every step leaves unchanged is `0` at every step. -/
theorem scales_four_fixed_iff {s : ℕ → ℝ} (h : Scales 4 s) :
    (∀ k, s (k + 1) = s k) ↔ ∀ k, s k = 0 := by
  constructor
  · intro hf k
    have := h k
    rw [hf k] at this
    linarith
  · intro hz k
    rw [hz, hz]

/-- **The strong-coupling end**: zero activities (independent chunks) satisfy `MatchAt`. -/
theorem matchAt_zero {V : Type*} [Fintype V] [DecidableEq V] {a κ : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hκ : 0 ≤ κ) : MatchAt (fun _ : Finset V => (0 : ℝ)) a κ :=
  ⟨rfl, ha0, ha1, hκ, fun _ => by simp [ha0]⟩

/-! ## 2. The edge cost in chunk units -/

/-- **A tension read in units of the chunk**: `σ ℓ²`. -/
def chunkTension (σ ℓ : ℝ) : ℝ := σ * ℓ ^ 2

/-- **Doubling the chunk quadruples the edge cost in chunk units.** -/
theorem chunkTension_double (σ ℓ : ℝ) : chunkTension σ (2 * ℓ) = 4 * chunkTension σ ℓ := by
  unfold chunkTension; ring

/-- **The chunk-unit edge cost along the zoom-out obeys `Scales 4`.** -/
theorem scales_tension (σ f ℓ₀ : ℝ) : Scales 4 (fun k => σ * f * side ℓ₀ k ^ 2) := by
  intro k
  simp only [side]
  ring

/-- The cost per chunk above which the count condition holds: `1 + κ + log(4z + 1)`. -/
def kpCost (z κ : ℝ) : ℝ := 1 + κ + Real.log (4 * z + 1)

/-- **A cost per chunk above `kpCost` meets the count condition** `4 z e^{1+κ−τ} ≤ 1`. -/
theorem count_cond_of_ge {z κ τ : ℝ} (hz : 0 ≤ z) (hτ : kpCost z κ ≤ τ) :
    4 * z * Real.exp (1 + κ - τ) ≤ 1 := by
  have hpos : 0 < 4 * z + 1 := by linarith
  have hexp : Real.exp (1 + κ - τ) ≤ (4 * z + 1)⁻¹ := by
    rw [← Real.exp_log hpos, ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by unfold kpCost at hτ; linarith)
  calc 4 * z * Real.exp (1 + κ - τ) ≤ (4 * z + 1) * Real.exp (1 + κ - τ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (4 * z + 1) * (4 * z + 1)⁻¹ := mul_le_mul_of_nonneg_left hexp hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

/-- **Kotecký–Preiss along a growing flow.** Chunk theories whose activities obey the count with cost
per chunk `s k`, growing by a factor `c > 1` from `s 0 > 0`, satisfy `MatchAt` from some step on. -/
theorem matchAt_along_flow {V : ℕ → Type*} [∀ k, Fintype (V k)] [∀ k, DecidableEq (V k)]
    (w : ∀ k, Finset (V k) → ℝ) {z κ c : ℝ} {s : ℕ → ℝ} (hz : 0 ≤ z) (hκ : 0 ≤ κ) (hc : 1 < c)
    (hgrow : Grows c s) (h0 : 0 < s 0) (hw0 : ∀ k, w k ∅ = 0)
    (hcount : ∀ k (v : V k) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w k X|
      ≤ (z * Real.exp (-(s k))) ^ n) :
    ∀ᶠ k in atTop, MatchAt (w k) 1 κ :=
  ((grows_tendsto hc hgrow h0).eventually_ge_atTop (kpCost z κ)).mono fun k hk =>
    matchAt_of_count (hw0 k) hz hκ (hcount k) (count_cond_of_ge hz hk)

/-- **The zoom-out of one confining measure reaches the match.** With cost `σ f (2ᵏ ℓ₀)²` per chunk,
`σ, f, ℓ₀ > 0`, and the count at every step, `MatchAt` holds from some step on. -/
theorem matchAt_of_tension_flow {V : ℕ → Type*} [∀ k, Fintype (V k)] [∀ k, DecidableEq (V k)]
    (w : ∀ k, Finset (V k) → ℝ) {z κ σ f ℓ₀ : ℝ} (hz : 0 ≤ z) (hκ : 0 ≤ κ) (hσ : 0 < σ)
    (hf : 0 < f) (hℓ₀ : 0 < ℓ₀) (hw0 : ∀ k, w k ∅ = 0)
    (hcount : ∀ k (v : V k) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w k X|
      ≤ (z * Real.exp (-(σ * f * side ℓ₀ k ^ 2))) ^ n) :
    ∀ᶠ k in atTop, MatchAt (w k) 1 κ := by
  have h0 : 0 < σ * f * side ℓ₀ 0 ^ 2 := by
    simp only [side, pow_zero, one_mul]
    positivity
  exact matchAt_along_flow w hz hκ (by norm_num : (1 : ℝ) < 4) (scales_tension σ f ℓ₀).grows h0
    hw0 hcount

theorem side_tendsto {ℓ₀ : ℝ} (h : 0 < ℓ₀) : Tendsto (fun k => side ℓ₀ k) atTop atTop := by
  simp only [side]
  exact (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const h

/-- **Agreement with `MatchAt.exists_length_match`**: along `side ℓ₀ k → ∞` its threshold length is
passed, so the count condition holds from some step on. -/
theorem eventually_length_match {z σ f κ ℓ₀ : ℝ} (hz : 0 ≤ z) (hσ : 0 < σ) (hf : 0 < f)
    (hℓ₀ : 0 < ℓ₀) : ∀ᶠ k in atTop, 4 * z * Real.exp (1 + κ - σ * f * side ℓ₀ k ^ 2) ≤ 1 := by
  obtain ⟨L₀, -, hL⟩ := exists_length_match (κ := κ) hz hσ hf
  exact ((side_tendsto hℓ₀).eventually_ge_atTop L₀).mono fun k hk => hL _ hk

/-! ### One-way running on the chunk cost -/

/-- **Running is one-way, read on the chunk cost**: at every doubling the chunk cost rises by at
least `b s²` (the one-loop form of asymptotic freedom, here asked at every step of the stretch). -/
def RunsOneWay (b : ℝ) (s : ℕ → ℝ) : Prop := ∀ k, s k + b * s k ^ 2 ≤ s (k + 1)

/-- **Linear lower bound**: `s k ≥ s 0 + k b (s 0)²`. -/
theorem runsOneWay_lower {b : ℝ} {s : ℕ → ℝ} (hb : 0 ≤ b) (h : RunsOneWay b s) (h0 : 0 ≤ s 0)
    (k : ℕ) : s 0 + k * (b * s 0 ^ 2) ≤ s k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : 0 ≤ (k : ℝ) * (b * s 0 ^ 2) :=
      mul_nonneg (Nat.cast_nonneg k) (mul_nonneg hb (sq_nonneg (s 0)))
    have hk0 : s 0 ≤ s k := by linarith
    have hsq : s 0 ^ 2 ≤ s k ^ 2 := pow_le_pow_left₀ h0 hk0 2
    have hstep := h k
    have hb2 := mul_le_mul_of_nonneg_left hsq hb
    push_cast
    linarith

/-- **One-way running drives the chunk cost to infinity.** -/
theorem runsOneWay_tendsto {b : ℝ} {s : ℕ → ℝ} (hb : 0 < b) (h : RunsOneWay b s) (h0 : 0 < s 0) :
    Tendsto s atTop atTop :=
  tendsto_atTop_mono (runsOneWay_lower hb.le h h0.le)
    (tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos hb (pow_pos h0 2))))

/-- **A fixed chunk cost runs with `b = 0`**: the constant reading `c` (a fixed point of the chunk
law at a finite cost, the Coulomb end of the proxy) satisfies `RunsOneWay 0` and does not tend to
infinity. -/
theorem runsOneWay_zero_fixed (c : ℝ) :
    RunsOneWay 0 (fun _ => c) ∧ ¬ Tendsto (fun _ : ℕ => c) atTop atTop := by
  refine ⟨fun _ => by simp, fun h => ?_⟩
  obtain ⟨k, hk⟩ := (tendsto_atTop.1 h (c + 1)).exists
  linarith

/-- **One number of doublings for every zoom.** If at every zoom `j` the chunk cost starts at least
at `s₀` (the coupling at the fixed physical length, the same on the observer's line) and runs one way
with the same `b`, there is one `K` with `s j k ≥ T` at every zoom and every `k ≥ K`. -/
theorem uniform_steps_of_runsOneWay {s : ℕ → ℕ → ℝ} {b s₀ T : ℝ} (hb : 0 ≤ b)
    (hbs : 0 < b * s₀ ^ 2) (hs₀ : 0 ≤ s₀) (hstart : ∀ j, s₀ ≤ s j 0)
    (hrun : ∀ j, RunsOneWay b (s j)) : ∃ K : ℕ, ∀ j k, K ≤ k → T ≤ s j k := by
  obtain ⟨K, hK⟩ := exists_nat_ge ((T - s₀) / (b * s₀ ^ 2))
  refine ⟨K, fun j k hk => ?_⟩
  have h1 := runsOneWay_lower hb (hrun j) (hs₀.trans (hstart j)) k
  have hsq : s₀ ^ 2 ≤ s j 0 ^ 2 := pow_le_pow_left₀ hs₀ (hstart j) 2
  have hk' : (K : ℝ) ≤ k := Nat.cast_le.2 hk
  have h2 : T - s₀ ≤ K * (b * s₀ ^ 2) := (div_le_iff₀ hbs).1 hK
  have h3 : (K : ℝ) * (b * s₀ ^ 2) ≤ k * (b * s j 0 ^ 2) :=
    mul_le_mul hk' (mul_le_mul_of_nonneg_left hsq hb) hbs.le (Nat.cast_nonneg k)
  linarith [hstart j]

/-- **The match at one number of doublings for every zoom.** Chunk activities `w j k` (zoom `j`,
step `k`) obeying the count with cost `s j k`, the cost starting at `≥ s₀ > 0` and running one way
with `b > 0` at every zoom, give one `K` with `MatchAt` at every zoom and every step `k ≥ K`. -/
theorem matchAt_uniform_of_runsOneWay {V : ℕ → ℕ → Type*} [∀ j k, Fintype (V j k)]
    [∀ j k, DecidableEq (V j k)] (w : ∀ j k, Finset (V j k) → ℝ) {s : ℕ → ℕ → ℝ} {z κ b s₀ : ℝ}
    (hz : 0 ≤ z) (hκ : 0 ≤ κ) (hb : 0 < b) (hs₀ : 0 < s₀) (hstart : ∀ j, s₀ ≤ s j 0)
    (hrun : ∀ j, RunsOneWay b (s j)) (hw0 : ∀ j k, w j k ∅ = 0)
    (hcount : ∀ j k (v : V j k) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j k X|
      ≤ (z * Real.exp (-(s j k))) ^ n) :
    ∃ K : ℕ, ∀ j k, K ≤ k → MatchAt (w j k) 1 κ := by
  obtain ⟨K, hK⟩ := uniform_steps_of_runsOneWay (T := kpCost z κ) hb.le
    (mul_pos hb (pow_pos hs₀ 2)) hs₀.le hstart hrun
  exact ⟨K, fun j k hk =>
    matchAt_of_count (hw0 j k) hz hκ (hcount j k) (count_cond_of_ge hz (hK j k hk))⟩

/-! ## 3. One length for every zoom -/

/-- **A floor on the tension gives one physical length for every zoom.** -/
theorem uniform_length_of_floor {σ : ℕ → ℝ} {z f κ : ℝ} (hz : 0 ≤ z) (hf : 0 < f)
    (hfl : NoTransition.Floor σ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → 4 * z * Real.exp (1 + κ - σ j * f * L ^ 2) ≤ 1 := by
  obtain ⟨σ₀, hσ₀, hlow⟩ := hfl
  obtain ⟨L₀, hL₀, hL⟩ := exists_length_match (κ := κ) hz hσ₀ hf
  refine ⟨L₀, hL₀, fun j L hL' => (hL L hL').trans' ?_⟩
  have hprod := mul_nonneg (mul_nonneg (sub_nonneg.2 (hlow j)) hf.le) (sq_nonneg L)
  have hle : σ₀ * f * L ^ 2 ≤ σ j * f * L ^ 2 := by nlinarith [hprod]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by linarith)

/-- **The floor is also necessary**: one length serving every zoom (with `z ≥ 1/4`) forces
`σ j ≥ (1 + κ)/(f L₀²)` at every zoom. -/
theorem floor_of_uniform_length {σ : ℕ → ℝ} {z f κ : ℝ} (hz : 1 / 4 ≤ z) (hκ : 0 ≤ κ) (hf : 0 < f)
    (h : ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → 4 * z * Real.exp (1 + κ - σ j * f * L ^ 2) ≤ 1) :
    NoTransition.Floor σ := by
  obtain ⟨L₀, hL₀, hL⟩ := h
  have hd : 0 < f * L₀ ^ 2 := by positivity
  refine ⟨(1 + κ) / (f * L₀ ^ 2), div_pos (by linarith) hd, fun j => ?_⟩
  have h1 := hL j L₀ le_rfl
  have h2 := Real.add_one_le_exp (1 + κ - σ j * f * L₀ ^ 2)
  have h3 : Real.exp (1 + κ - σ j * f * L₀ ^ 2) ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * z - 1)
      (Real.exp_pos (1 + κ - σ j * f * L₀ ^ 2)).le]
  rw [div_le_iff₀ hd]
  nlinarith

/-- **One length for every zoom exactly when the tension has a floor** (`z ≥ 1/4`). -/
theorem uniform_length_iff_floor {σ : ℕ → ℝ} {z f κ : ℝ} (hz : 1 / 4 ≤ z) (hκ : 0 ≤ κ)
    (hf : 0 < f) :
    (∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → 4 * z * Real.exp (1 + κ - σ j * f * L ^ 2) ≤ 1) ↔
      NoTransition.Floor σ :=
  ⟨floor_of_uniform_length hz hκ hf, uniform_length_of_floor (by linarith) hf⟩

/-- **A fading tension fails the count condition at every length, at all fine enough zooms.** -/
theorem kp_fails_of_tendsto_zero {σ : ℕ → ℝ} {z f κ : ℝ} (hz : 1 / 4 ≤ z) (hκ : 0 ≤ κ)
    (hσ : Tendsto σ atTop (𝓝 0)) (L : ℝ) :
    ∀ᶠ j in atTop, 1 < 4 * z * Real.exp (1 + κ - σ j * f * L ^ 2) := by
  have hlim : Tendsto (fun j => 4 * z * Real.exp (1 + κ - σ j * f * L ^ 2)) atTop
      (𝓝 (4 * z * Real.exp (1 + κ - 0 * f * L ^ 2))) := by
    exact ((Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.sub ((hσ.mul_const f).mul_const (L ^ 2)))).const_mul _
  have hval : 1 < 4 * z * Real.exp (1 + κ - 0 * f * L ^ 2) := by
    rw [show (1 : ℝ) + κ - 0 * f * L ^ 2 = 1 + κ by ring]
    have h1 := Real.add_one_le_exp (1 + κ)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * z - 1) (Real.exp_pos (1 + κ)).le]
  exact hlim.eventually (lt_mem_nhds hval)

/-- **A fading tension has no uniform length.** -/
theorem no_uniform_length_of_tendsto_zero {σ : ℕ → ℝ} {z f κ : ℝ} (hz : 1 / 4 ≤ z) (hκ : 0 ≤ κ)
    (hσ : Tendsto σ atTop (𝓝 0)) :
    ¬ ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → 4 * z * Real.exp (1 + κ - σ j * f * L ^ 2) ≤ 1 := by
  rintro ⟨L₀, -, h⟩
  obtain ⟨j, hj⟩ := (kp_fails_of_tendsto_zero (f := f) hz hκ hσ L₀).exists
  exact absurd (h j L₀ le_rfl) (not_le.2 hj)

/-- **Confined at every zoom, still no uniform length**: the `fade` line has a positive tension at
every zoom, no floor, and no length that serves every zoom. -/
theorem fade_confined_no_uniform {z f κ : ℝ} (hz : 1 / 4 ≤ z) (hκ : 0 ≤ κ) :
    (∀ j, 0 < fade j) ∧ ¬ NoTransition.Floor fade ∧
      ¬ ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → 4 * z * Real.exp (1 + κ - fade j * f * L ^ 2) ≤ 1 :=
  ⟨fade_pos, fade_not_floor,
    no_uniform_length_of_tendsto_zero hz hκ tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-- **For `SU(N)`, link 2 on the line and the count give one length with the match at every zoom.**
`EdgesCannotEndNA` at `SU(N)`, `N ≥ 2`, is exactly `Floor σ` (`edgesCannotEndNA_SU_iff`); `σ j` is
the physical tension at zoom `j`, `L` the physical chunk side, `w j L` the chunk activities. -/
theorem matchAt_uniform_of_edgesCannotEndNA {N : ℕ} (hN : 2 ≤ N)
    {V : ℕ → ℝ → Type*} [∀ j L, Fintype (V j L)] [∀ j L, DecidableEq (V j L)]
    (w : ∀ j L, Finset (V j L) → ℝ) {σ : ℕ → ℝ} {z f κ : ℝ} (hz : 0 ≤ z) (hf : 0 < f)
    (hκ : 0 ≤ κ) (hedge : EdgesCannotEndNA (MassGap.SUN.SU N) σ) (hw0 : ∀ j L, w j L ∅ = 0)
    (hcount : ∀ j L (v : V j L) n, ∑ X ∈ (site v).filter (fun X => X.card = n), |w j L X|
      ≤ (z * Real.exp (-(σ j * f * L ^ 2))) ^ n) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L → MatchAt (w j L) 1 κ := by
  obtain ⟨L₀, hL₀, h⟩ :=
    uniform_length_of_floor (κ := κ) hz hf ((edgesCannotEndNA_SU_iff hN σ).1 hedge)
  exact ⟨L₀, hL₀, fun j L hL => matchAt_of_count (hw0 j L) hz hκ (hcount j L) (h j L hL)⟩

/-! ## 4. The observer's relative rate -/

section Observer

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Data processing along the zoom-out**: every coarse reading of a Markov slab has, across `n`
slabs, at most the fine rate to the `n`. -/
theorem obs_rate_zoomOut {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) {O : Type*}
    (c : α → O) (n : ℕ) : CorrOn π (K ^ n) (readings c) (maxCorr π K ^ n) := by
  have h := corrOn_of_maxCorr (M.pow n) (readings c)
  have hle := maxCorr_pow_le M n
  have h0 := maxCorr_nonneg (M.pow n)
  refine ⟨pow_nonneg (maxCorr_nonneg M) n, fun f hf g hg hf0 hg0 =>
    (h.2 f hf g hg hf0 hg0).trans ?_⟩
  have hsq : maxCorr π (K ^ n) ^ 2 ≤ (maxCorr π K ^ n) ^ 2 := pow_le_pow_left₀ h0 hle 2
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (nsq_nonneg M.pi_nonneg f))
    (nsq_nonneg M.pi_nonneg g)

/-- **A coarser observer keeps the bound.** -/
theorem obs_coarser_zoomOut {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) {O O' : Type*}
    (c : α → O) (h : O → O') (n : ℕ) :
    CorrOn π (K ^ n) (readings (h ∘ c)) (maxCorr π K ^ n) :=
  (obs_rate_zoomOut M c n).anti (readings_comp c h)

/-- **The fine rate of a reversible slab at chunk `2ᵏ` is the `2ᵏ`-th power.** -/
theorem fullRate_zoomOut {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    (k : ℕ) : maxCorr π (K ^ (2 ^ k)) = maxCorr π K ^ (2 ^ k) :=
  ReadsSlabWilson.maxCorr_pow_eq M hrev Nat.one_le_two_pow

/-- **The fine gap in chunk units doubles at each step**: the physical mass is the same at every
chunk size. -/
theorem fullGap_scales {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K) :
    Scales 2 (fun k => -Real.log (maxCorr π (K ^ (2 ^ k)))) := by
  intro k
  show -Real.log (maxCorr π (K ^ (2 ^ (k + 1)))) = 2 * -Real.log (maxCorr π (K ^ (2 ^ k)))
  rw [fullRate_zoomOut M hrev, fullRate_zoomOut M hrev, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **The type of the fine reading is the same at every chunk size.** -/
theorem fullRate_type_const {π : α → ℝ} {K : Matrix α α ℝ} (M : Markov π K) (hrev : Rev π K)
    (k : ℕ) : maxCorr π (K ^ (2 ^ k)) < 1 ↔ maxCorr π K < 1 := by
  rw [fullRate_zoomOut M hrev]
  exact pow_lt_one_iff_of_nonneg (maxCorr_nonneg M) (pow_ne_zero _ two_ne_zero)

end Observer

section SwapControl

open Matrix

/-- The uniform law on two bits. -/
def piU : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4

/-- The swap of the two bits. -/
def swapK : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := fun p q => if q = p.swap then 1 else 0

theorem swapK_mulVec (h : Fin 2 × Fin 2 → ℝ) : swapK *ᵥ h = fun p => h p.swap := by
  funext p
  simp [Matrix.mulVec, dotProduct, swapK]

theorem markov_swapK : Markov piU swapK where
  pi_nonneg := fun _ => by norm_num [piU]
  pi_sum := by simp [piU]
  nonneg := fun p q => by unfold swapK; split_ifs <;> norm_num
  row := fun p => by simp [swapK]
  stat := fun y => by
    rcases y with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [piU, swapK, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem rev_swapK : Rev piU swapK := by
  rintro ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [piU, swapK]

/-- Across one slab the observer of the first bit reads no correlation. -/
theorem swap_obs_zero : CorrOn piU swapK (readings (Prod.fst : Fin 2 × Fin 2 → Fin 2)) 0 := by
  refine ⟨le_rfl, ?_⟩
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ hu _
  rw [swapK_mulVec]
  have hu' : u 0 + u 1 = 0 := by
    have h := hu
    simp only [mean, piU, Fintype.sum_prod_type, Fin.sum_univ_two, Function.comp_apply] at h
    linarith
  have hip : ip piU (u ∘ Prod.fst) (fun p => (v ∘ Prod.fst) p.swap)
      = 1 / 4 * ((u 0 + u 1) * (v 0 + v 1)) := by
    simp only [ip, piU, Fintype.sum_prod_type, Fin.sum_univ_two, Function.comp_apply,
      Prod.swap_prod_mk]
    ring
  rw [hip, hu']
  simp

/-- Across two slabs the same observer reads the full correlation: no rate below `1`. -/
theorem swap_obs_two_not {r : ℝ} (hr : r < 1) :
    ¬ CorrOn piU (swapK ^ 2) (readings (Prod.fst : Fin 2 × Fin 2 → Fin 2)) r := by
  rintro ⟨hr0, h⟩
  have hK2 : ∀ g : Fin 2 × Fin 2 → ℝ, (swapK ^ 2) *ᵥ g = g := fun g => by
    rw [pow_two, ← Matrix.mulVec_mulVec, swapK_mulVec, swapK_mulVec]
    simp
  have hm : mean piU (NonAbelianForget.fluxBit ∘ Prod.fst) = 0 := by
    simp [mean, piU, NonAbelianForget.fluxBit, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hc := h _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ hm hm
  rw [hK2] at hc
  have hn : nsq piU (NonAbelianForget.fluxBit ∘ Prod.fst) = 1 := by
    simp [nsq, piU, NonAbelianForget.fluxBit, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
  have hi : ip piU (NonAbelianForget.fluxBit ∘ Prod.fst) (NonAbelianForget.fluxBit ∘ Prod.fst)
      = 1 := by
    rw [← nsq_eq_ip, hn]
  rw [hi, hn] at hc
  nlinarith

/-- **The observer's own rate is not monotone along the zoom-out.** A reversible Markov slab on which
the observer's rate is `0` across one slab and no rate below `1` holds across two. -/
theorem observer_rate_not_monotone :
    Markov piU swapK ∧ Rev piU swapK ∧
      CorrOn piU swapK (readings (Prod.fst : Fin 2 × Fin 2 → Fin 2)) 0 ∧
      ∀ r : ℝ, r < 1 → ¬ CorrOn piU (swapK ^ 2) (readings (Prod.fst : Fin 2 × Fin 2 → Fin 2)) r :=
  ⟨markov_swapK, rev_swapK, swap_obs_zero, fun _ hr => swap_obs_two_not hr⟩

end SwapControl

/-! ## 5. The `U(1)` control -/

/-- **At `σ = 0` the edge cost in chunk units stays `0` and the count condition fails at every
step.** -/
theorem u1_flow {z κ f ℓ₀ : ℝ} (hz : 1 / 4 ≤ z) (hκ : 0 ≤ κ) :
    Scales 4 (fun k => 0 * f * side ℓ₀ k ^ 2) ∧ ¬ Transition (fun k => 0 * f * side ℓ₀ k ^ 2) ∧
      ∀ k, 1 < 4 * z * Real.exp (1 + κ - 0 * f * side ℓ₀ k ^ 2) := by
  refine ⟨scales_tension 0 f ℓ₀, noTransition_of_scales (by norm_num) (scales_tension 0 f ℓ₀),
    fun k => ?_⟩
  rw [show (1 : ℝ) + κ - 0 * f * side ℓ₀ k ^ 2 = 1 + κ by ring]
  have h1 := Real.add_one_le_exp (1 + κ)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * z - 1) (Real.exp_pos (1 + κ)).le]

/-- **The `U(1)` line of measures has no uniform length**: positive tension below zoom `k₁`, zero
from `k₁` on (the model of the Coulomb phase; cited, not proved here). -/
theorem u1_line_no_uniform (k₁ : ℕ) {hi z f κ : ℝ} (hz : 1 / 4 ≤ z) (hκ : 0 ≤ κ) :
    ¬ NoTransition.Floor (stepProfile k₁ hi 0) ∧
      ¬ ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ j L, L₀ ≤ L →
        4 * z * Real.exp (1 + κ - stepProfile k₁ hi 0 j * f * L ^ 2) ≤ 1 := by
  refine ⟨fun ⟨c, hc, hk⟩ => ?_, fun ⟨L₀, _, h⟩ => ?_⟩
  · have := hk k₁
    simp [stepProfile] at this
    linarith
  · have h0 := h k₁ L₀ le_rfl
    have hs : stepProfile k₁ hi 0 k₁ = 0 := by simp [stepProfile]
    rw [hs, show (1 : ℝ) + κ - 0 * f * L₀ ^ 2 = 1 + κ by ring] at h0
    have h1 := Real.add_one_le_exp (1 + κ)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * z - 1) (Real.exp_pos (1 + κ)).le]

#print axioms scales_iter
#print axioms type_const_of_scales
#print axioms zero_const_of_scales
#print axioms noTransition_of_scales
#print axioms grows_pos
#print axioms grows_tendsto
#print axioms grows_one_not_sufficient
#print axioms scales_four_fixed_iff
#print axioms matchAt_zero
#print axioms chunkTension_double
#print axioms scales_tension
#print axioms count_cond_of_ge
#print axioms matchAt_along_flow
#print axioms matchAt_of_tension_flow
#print axioms eventually_length_match
#print axioms runsOneWay_lower
#print axioms runsOneWay_tendsto
#print axioms runsOneWay_zero_fixed
#print axioms uniform_steps_of_runsOneWay
#print axioms matchAt_uniform_of_runsOneWay
#print axioms uniform_length_of_floor
#print axioms floor_of_uniform_length
#print axioms uniform_length_iff_floor
#print axioms kp_fails_of_tendsto_zero
#print axioms no_uniform_length_of_tendsto_zero
#print axioms fade_confined_no_uniform
#print axioms matchAt_uniform_of_edgesCannotEndNA
#print axioms obs_rate_zoomOut
#print axioms obs_coarser_zoomOut
#print axioms fullRate_zoomOut
#print axioms fullGap_scales
#print axioms fullRate_type_const
#print axioms observer_rate_not_monotone
#print axioms u1_flow
#print axioms u1_line_no_uniform

end MassGap.NoTransitionFlow
