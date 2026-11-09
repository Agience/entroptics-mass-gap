import Mathlib
import MassGap.LocalLink

/-!
# MassGap.ApertureFixed — the observer reads a fixed finite aperture; a gap from the readings

The observer's aperture is a fixed number `K` of cells of fixed physical side. Each cell returns one
reading, a bounded function of the substrate configuration in that cell; the readings of one time
slab of fixed physical thickness form one point of the fixed space `X = Fin K → Y`. Neither `K`, the
cell side, the slab thickness nor the range `Y` depends on the zoom `k`. Everything finer is
integrated out: what the observer has is the law of the reading process `x₀, x₁, x₂, …` (one point
of `X` per slab), and that law is described by the conditional law of the next slab's readings given
the whole past of readings — a chain with complete connections. It need not be Markov in the readings.

The cross-section obstruction of `StrongPhys.PhysStrong` was a supremum over all fine face
configurations, extensive in `(L/a)³`. Here the faces are the readings: every supremum below runs
over pasts of readings, points of the fixed space `X`, never over fine links.

## 1. Two measures with a common part (`abs_integral_sub_le_of_common`)

`P = m + r`, `P' = m + r'` probability measures with common part of mass at least `1 − v`. For
measurable `φ, ψ` with `|φ − ψ| ≤ α` and both valued in one interval of length `β ≥ α`:
`|∫φ dP − ∫ψ dP'| ≤ (1 − v) α + v β`. This is the one-step coupling, stated without a coupling.

## 2. The reading chain and the oscillation recursion

* `ReadingChain X`: one Markov kernel `κ t` per slab `t`, from the path `ω : ℕ → X` to the next
  reading. `step t F ω = ∫ F(ω[t ↦ y]) dκ_t(ω)(y)` is the conditional expectation over slab `t`;
  `seg a n` composes `step a ∘ … ∘ step (a + n − 1)`. The law of the readings up to slab `T` with
  boundary path `ω₀` is `seg 0 (T + 1) · ω₀`.
* `Agree t ℓ ω ω'`: the paths agree on the `ℓ` slabs `[t − ℓ, t)` before `t`. `OscLe t ℓ F δ`:
  `|F ω − F ω'| ≤ δ` whenever `Agree t ℓ ω ω'` (`ℓ = 0`: every pair).
* `Overlap v`: whenever two pasts agree on their last `ℓ` slabs, the two conditional laws of the
  next slab share a common part of mass at least `1 − v ℓ` (total variation at most `v ℓ`).
* `step_osc`: `OscLe (t+1) (ℓ+1) G α`, `OscLe (t+1) 0 G β` give
  `OscLe t ℓ (step t G) ((1 − v ℓ) α + v ℓ β)` — the renewal recursion of the coupling.
* `seg_osc`: a profile `w` with `w 0 = 1`, `w ≥ 0` and `(1 − v ℓ) w(ℓ+1) + v ℓ ≤ ρ w ℓ` turns
  `OscLe (a+n) ℓ F (B w ℓ)` into `OscLe a ℓ (seg a n F) (B ρⁿ w ℓ)`: the conditional expectation of a
  far reading forgets the past at rate `ρ` per slab.
* `cov_le`: for `g` read on slabs `≤ s` and `f` with that profile at slab `s + n`,
  `|E(g f) − E g E f| ≤ 2 G (B ρⁿ)`.

## 3. Minorisation and memory give the rate (`reading_cluster`)

* `Doeblin c μ₀`: every conditional law of the next slab, given any past, is `μ₀ + r` with `μ₀` a
  fixed measure of mass at least `c` (`μ₀ = c ν`, `ν` the fixed reference law of one slab's
  readings). This is the minorisation; it controls `ℓ = 0`.
* `Memory η θ`: two pasts that agree on their last `ℓ ≥ 1` slabs give conditional laws within total
  variation `η θ^ℓ`. This is the continuity of the complete connections; it controls `ℓ ≥ 1`.
* `reading_cluster`: `0 < c`, `0 ≤ θ < 1`, `η ≥ 0`, `η θ < 1 − θ` give one `ρ ∈ (0, 1)`,
  depending on `(c, η, θ)` only, with `|Cov(g, φ(x_{s+n}))| ≤ 4 G B ρⁿ` for every chain with those
  constants, every boundary path and every `n`.
* `aperture_cluster`: for an `ApertureReading` whose zoom-`k` chains all carry the same `(c, η, θ)`,
  a mass `m > 0` in physical units with `|Cov_k| ≤ 4 G B e^{−m n ℓ_slab}` at every zoom `k`.

The memory clause cannot be dropped. Minorisation by a fixed `c > 0` given the whole past does not
give uniqueness of the stationary law of a chain with complete connections (Bramson–Kalikow 1993: a
continuous `g`-function bounded away from `0` with two `g`-measures), hence no clustering. At
`Memory 0 θ` (Markov readings) the profile condition reads `1 − c ≤ ρ`.

The unit tests (2D `SU(2)` holonomy reading; 4D massive and massless Gaussian slab-and-cell averages)
show the division of labour: the conditional spread of the next reading given the whole past is `O(1)`
and zoom-independent for the massive and the massless field alike, while the memory tail decays
exponentially only in the massive case (`∝ 1/ℓ` when massless). Minorisation is blind to the gap; the
memory clause carries the mass.

## 4. Wiring to the observer's gap (`gapAt_of_readingRep`)

* `flowClusterAbs_of_lattice`: a lattice connected-kernel bound `C e^{−(c/L) aₘ n}` eventually in the
  zoom, with `c` independent of the pair and the step, passes through the ultrafilter limit to
  `FlowCapstone.FlowClusterAbs`.
* `ReadingRep`: every connected flowed lattice kernel of a pair of margin monomials, at step `m` and
  time shift `n`, eventually in the zoom equals a reading-chain covariance at slab distance `j` with
  `aₘ n ≤ ℓ j`, for chains with the fixed constants `(c, η, θ)`.
* `gapAt_of_readingRep`: `ReadingRep` gives `GapAt (transferN …) ρ` with `ρ < 1` at every step: input
  4 of `ClayFull`.

`ReadingRep` is a hypothesis here; no declaration constructs it for the Wilson measure. Its definition
does not tie the chain to the Wilson readings: as stated it asks only for some chain with the fixed
constants whose covariance equals the lattice number, and a chain can be built for any number below
`4 G B ρ^j`, so as stated it is no weaker than the lattice clustering bound it feeds. Its content is the
case where the chain is the law of the actual readings. What it asks
of Wilson is that the readings carrying the margin monomials have conditional laws given their own
past that are minorised by `c` and forget the past at the rate `θ`, with `(c, η, θ)` independent of
the zoom and of the pair. The fixed reading space may depend on the pair; the constants may not.

DERIVED (module-wide): `1` the mass of a probability measure and the top of every rate; `0` the
empty window and the zero-th slab; `2` and `4` from `cov_le` (two terms) and from `osc φ ≤ 2B`;
`1 − θ` the geometric sum `Σ θ^ℓ` at `ρ = 1` in the profile condition.
-/

noncomputable section

namespace MassGap.ApertureFixed

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ## 1. Two measures with a common part -/

section Common

variable {X : Type*} [MeasurableSpace X]

/-- **The one-step coupling bound.** `m + r`, `m + r'` of total mass `1`, common part `m` of mass at
least `1 − v`; `|φ − ψ| ≤ α ≤ β` and both valued in `[u, u + β]`. Then
`|∫φ d(m + r) − ∫ψ d(m + r')| ≤ (1 − v) α + v β`.

DERIVED: `1` the total mass. -/
theorem abs_integral_sub_le_of_common {m r r' : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure r]
    [IsFiniteMeasure r'] (h1 : (m + r).real univ = 1) (h1' : (m + r').real univ = 1)
    {φ ψ : X → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {α β u v : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hdiff : ∀ y, |φ y - ψ y| ≤ α) (hφr : ∀ y, u ≤ φ y ∧ φ y ≤ u + β)
    (hψr : ∀ y, u ≤ ψ y ∧ ψ y ≤ u + β) (hm : 1 - v ≤ m.real univ) :
    |∫ y, φ y ∂(m + r) - ∫ y, ψ y ∂(m + r')| ≤ (1 - v) * α + v * β := by
  have hβ : 0 ≤ β := hα.trans hαβ
  have bφ : ∀ y, ‖φ y‖ ≤ |u| + β := fun y => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le u, le_abs_self u, (hφr y).1, (hφr y).2]
  have bψ : ∀ y, ‖ψ y‖ ≤ |u| + β := fun y => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [neg_abs_le u, le_abs_self u, (hψr y).1, (hψr y).2]
  have iφm : Integrable φ m := Integrable.of_bound hφ.aestronglyMeasurable _ (Eventually.of_forall bφ)
  have iφr : Integrable φ r := Integrable.of_bound hφ.aestronglyMeasurable _ (Eventually.of_forall bφ)
  have iψm : Integrable ψ m := Integrable.of_bound hψ.aestronglyMeasurable _ (Eventually.of_forall bψ)
  have iψr : Integrable ψ r' :=
    Integrable.of_bound hψ.aestronglyMeasurable _ (Eventually.of_forall bψ)
  rw [integral_add_measure iφm iφr, integral_add_measure iψm iψr]
  have hM : m.real univ + r.real univ = 1 := by rw [← measureReal_add_apply]; exact h1
  have hM' : m.real univ + r'.real univ = 1 := by rw [← measureReal_add_apply]; exact h1'
  have hA : |∫ y, φ y ∂m - ∫ y, ψ y ∂m| ≤ α * m.real univ := by
    rw [← integral_sub iφm iψm]
    have h := norm_integral_le_of_norm_le_const (μ := m) (f := fun y => φ y - ψ y) (C := α)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hdiff y)
    rwa [Real.norm_eq_abs] at h
  have hR : ∀ (ρ : Measure X) [IsFiniteMeasure ρ] (χ : X → ℝ), Integrable χ ρ →
      (∀ y, u ≤ χ y ∧ χ y ≤ u + β) →
      0 ≤ ∫ y, χ y ∂ρ - u * ρ.real univ ∧ ∫ y, χ y ∂ρ - u * ρ.real univ ≤ β * ρ.real univ := by
    intro ρ _ χ hχ hχr
    have e : ∫ y, χ y ∂ρ - u * ρ.real univ = ∫ y, (χ y - u) ∂ρ := by
      rw [integral_sub hχ (integrable_const u), integral_const, smul_eq_mul]
      ring
    rw [e]
    refine ⟨integral_nonneg fun y => by show (0 : ℝ) ≤ χ y - u; linarith [(hχr y).1], ?_⟩
    have h := integral_mono (f := fun y => χ y - u) (g := fun _ => β) (hχ.sub (integrable_const u))
      (integrable_const β) (fun y => show χ y - u ≤ β by linarith [(hχr y).2])
    rw [integral_const, smul_eq_mul] at h
    linarith
  obtain ⟨hr1, hr2⟩ := hR r φ iφr hφr
  obtain ⟨hr1', hr2'⟩ := hR r' ψ iψr hψr
  have hRR : r.real univ = r'.real univ := by linarith
  rw [hRR] at hr1 hr2
  have hβR : β * r'.real univ = β - β * m.real univ := by
    rw [show r'.real univ = 1 - m.real univ by linarith]; ring
  have key : 0 ≤ β * m.real univ - β + β * v - α * m.real univ + α - α * v := by
    have h0 := mul_nonneg (sub_nonneg.2 hαβ) (sub_nonneg.2 hm)
    have e0 : (β - α) * (m.real univ - (1 - v))
        = β * m.real univ - β + β * v - α * m.real univ + α - α * v := by ring
    linarith
  have e1 : (1 - v) * α + v * β = α - α * v + β * v := by ring
  rw [e1]
  rw [abs_le] at hA ⊢
  obtain ⟨hA1, hA2⟩ := hA
  constructor <;> linarith

#print axioms abs_integral_sub_le_of_common

end Common

/-! ## 2. The reading chain -/

/-- **A reading chain with complete connections** on the slab-reading space `X`: at slab `t`, the
conditional law of the next reading given the whole path, `κ t ω`. A Markov kernel per slab. The
kernel may read every coordinate of `ω`; only coordinates before `t` are meaningful, and no
statement below uses the others. -/
structure ReadingChain (X : Type*) [MeasurableSpace X] where
  /-- The conditional law of the reading of slab `t` given the path. -/
  κ : ℕ → Kernel (ℕ → X) X
  /-- Each conditional law is a probability measure. -/
  markov : ∀ t, IsMarkovKernel (κ t)

/-- Two paths agree on the `ℓ` slabs `[t − ℓ, t)` before `t`. At `ℓ = 0` there is no constraint.

DERIVED: no numeral. -/
def Agree {X : Type*} (t ℓ : ℕ) (ω ω' : ℕ → X) : Prop :=
  ∀ j, t - ℓ ≤ j → j < t → ω j = ω' j

/-- `F` varies by at most `δ` between paths agreeing on the `ℓ` slabs before `t`.

DERIVED: no numeral. -/
def OscLe {X : Type*} (t ℓ : ℕ) (F : (ℕ → X) → ℝ) (δ : ℝ) : Prop :=
  ∀ ω ω', Agree t ℓ ω ω' → |F ω - F ω'| ≤ δ

/-- Bounded and measurable.

DERIVED: no numeral. -/
def BM {X : Type*} [MeasurableSpace X] (F : (ℕ → X) → ℝ) : Prop :=
  Measurable F ∧ ∃ B, ∀ ω, |F ω| ≤ B

/-- `g` reads only the slabs before `s`.

DERIVED: no numeral. -/
def ReadsBelow {X : Type*} (s : ℕ) (g : (ℕ → X) → ℝ) : Prop :=
  ∀ ω ω', (∀ j, j < s → ω j = ω' j) → g ω = g ω'

theorem osc_mono {X : Type*} {t ℓ : ℕ} {F : (ℕ → X) → ℝ} {δ δ' : ℝ} (h : OscLe t ℓ F δ)
    (hδ : δ ≤ δ') : OscLe t ℓ F δ' := fun ω ω' hω => (h ω ω' hω).trans hδ

theorem agree_update {X : Type*} {t ℓ : ℕ} {ω ω' : ℕ → X} (h : Agree t ℓ ω ω') (y : X) :
    Agree (t + 1) (ℓ + 1) (Function.update ω t y) (Function.update ω' t y) := by
  intro j hj1 hj2
  by_cases hjt : j = t
  · subst hjt; simp
  · rw [Function.update_of_ne hjt, Function.update_of_ne hjt]
    exact h j (by omega) (by omega)

/-- At window `0` every pair agrees.

DERIVED: `0` the empty window. -/
theorem agree_zero {X : Type*} (t : ℕ) (ω ω' : ℕ → X) : Agree t 0 ω ω' :=
  fun j h1 h2 => absurd h2 (by omega)

/-- The `0`-window oscillation puts `F` in one interval of length `β`.

DERIVED: `0` the empty window. -/
theorem rangeIn_of_osc {X : Type*} {t : ℕ} {F : (ℕ → X) → ℝ} {β : ℝ} (h : OscLe t 0 F β)
    (ω₀ : ℕ → X) : ∃ u, ∀ ω, u ≤ F ω ∧ F ω ≤ u + β := by
  haveI : Nonempty (ℕ → X) := ⟨ω₀⟩
  have hall : ∀ ω ω', |F ω - F ω'| ≤ β := fun ω ω' => h ω ω' (agree_zero t ω ω')
  have hbdd : BddBelow (range F) := ⟨F ω₀ - β, by
    rintro _ ⟨ω, rfl⟩
    linarith [(abs_le.1 (hall ω₀ ω)).2]⟩
  refine ⟨⨅ ω, F ω, fun ω => ⟨ciInf_le hbdd ω, ?_⟩⟩
  have : F ω - β ≤ ⨅ ω', F ω' := le_ciInf fun ω' => by linarith [(abs_le.1 (hall ω ω')).2]
  linarith

namespace ReadingChain

variable {X : Type*} [MeasurableSpace X] (Ch : ReadingChain X)

/-- The conditional expectation over slab `t`: `∫ F(ω[t ↦ y]) dκ_t(ω)(y)`.

DERIVED: no numeral. -/
def step (t : ℕ) (F : (ℕ → X) → ℝ) (ω : ℕ → X) : ℝ :=
  ∫ y, F (Function.update ω t y) ∂(Ch.κ t ω)

/-- `seg a n F = step a (step (a+1) (… step (a+n−1) F))`: the conditional expectation over the `n`
slabs `[a, a + n)`.

DERIVED: `0` and `1` the recursion. -/
def seg : ℕ → ℕ → ((ℕ → X) → ℝ) → (ℕ → X) → ℝ
  | _, 0, F => F
  | a, n + 1, F => Ch.step a (seg (a + 1) n F)

theorem seg_zero (a : ℕ) (F : (ℕ → X) → ℝ) : Ch.seg a 0 F = F := rfl

theorem seg_succ (a n : ℕ) (F : (ℕ → X) → ℝ) : Ch.seg a (n + 1) F = Ch.step a (Ch.seg (a + 1) n F) :=
  rfl

/-- The overlap profile: pasts agreeing on their last `ℓ` slabs give next-slab laws with a common
part of mass at least `1 − v ℓ`.

DERIVED: `1` the total mass. -/
def Overlap (v : ℕ → ℝ) : Prop :=
  ∀ t ℓ (ω ω' : ℕ → X), Agree t ℓ ω ω' → ∃ m r r' : Measure X, IsFiniteMeasure m ∧
    IsFiniteMeasure r ∧ IsFiniteMeasure r' ∧ Ch.κ t ω = m + r ∧ Ch.κ t ω' = m + r' ∧
      1 - v ℓ ≤ m.real univ

theorem step_bm {t : ℕ} {F : (ℕ → X) → ℝ} (hF : BM F) : BM (Ch.step t F) := by
  haveI := Ch.markov t
  obtain ⟨hm, B, hB⟩ := hF
  refine ⟨?_, B, fun ω => ?_⟩
  · have hs : StronglyMeasurable (fun p : (ℕ → X) × X => F (Function.update p.1 t p.2)) :=
      (hm.comp (measurable_update' (X := fun _ : ℕ => X) (a := t))).stronglyMeasurable
    exact (hs.integral_kernel_prod_right' (κ := Ch.κ t)).measurable
  · have h := norm_integral_le_of_norm_le_const (μ := Ch.κ t ω)
      (f := fun y => F (Function.update ω t y)) (C := B)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB _)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
    exact h

theorem seg_bm {F : (ℕ → X) → ℝ} (hF : BM F) (n : ℕ) : ∀ a, BM (Ch.seg a n F) := by
  induction n with
  | zero => intro a; exact hF
  | succ n ih => intro a; rw [seg_succ]; exact Ch.step_bm (ih (a + 1))

/-- **The coupling step.** Window `ℓ + 1` oscillation `α` and global oscillation `β` after slab `t`
give window `ℓ` oscillation `(1 − v ℓ) α + v ℓ β` before it.

DERIVED: `0` the global window; `1` the slab. -/
theorem step_osc {v : ℕ → ℝ} (hO : Ch.Overlap v) (hv : ∀ ℓ, v ℓ ≤ 1) {t ℓ : ℕ}
    {G : (ℕ → X) → ℝ} (hG : Measurable G) {α β : ℝ} (hα0 : 0 ≤ α)
    (hα : OscLe (t + 1) (ℓ + 1) G α) (hβ : OscLe (t + 1) 0 G β) :
    OscLe t ℓ (Ch.step t G) ((1 - v ℓ) * α + v ℓ * β) := by
  intro ω ω' hω
  haveI := Ch.markov t
  obtain ⟨u, hu⟩ := rangeIn_of_osc hβ ω
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ ω ω (agree_zero _ ω ω))
  obtain ⟨m, r, r', hm, hr, hr', e, e', hM⟩ := hO t ℓ ω ω' hω
  have h1 : (m + r).real univ = 1 := by rw [← e]; exact probReal_univ
  have h1' : (m + r').real univ = 1 := by rw [← e']; exact probReal_univ
  have hdiff : ∀ y, |G (Function.update ω t y) - G (Function.update ω' t y)| ≤ min α β :=
    fun y => le_min (hα _ _ (agree_update hω y)) (hβ _ _ (agree_zero _ _ _))
  have key := abs_integral_sub_le_of_common h1 h1' (φ := fun y => G (Function.update ω t y))
    (ψ := fun y => G (Function.update ω' t y)) (hG.comp (measurable_update ω))
    (hG.comp (measurable_update ω')) (le_min hα0 hβ0) (min_le_right α β) hdiff
    (fun y => hu _) (fun y => hu _) hM
  unfold step
  rw [e, e']
  refine key.trans ?_
  have : (1 - v ℓ) * min α β ≤ (1 - v ℓ) * α :=
    mul_le_mul_of_nonneg_left (min_le_left α β) (by linarith [hv ℓ])
  linarith

#print axioms step_osc

/-- **The far reading forgets the past at rate `ρ`.** A profile `w` (`w 0 = 1`, `w ≥ 0`,
`(1 − v ℓ) w(ℓ+1) + v ℓ ≤ ρ w ℓ`) turns window bounds `B w ℓ` at slab `a + n` into window bounds
`B ρⁿ w ℓ` at slab `a`.

DERIVED: `0` the global window; `1` the slab. -/
theorem seg_osc {v : ℕ → ℝ} (hO : Ch.Overlap v) (hv : ∀ ℓ, v ℓ ≤ 1) {w : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hw0 : w 0 = 1) (hw : ∀ ℓ, 0 ≤ w ℓ)
    (hstep : ∀ ℓ, (1 - v ℓ) * w (ℓ + 1) + v ℓ ≤ ρ * w ℓ) :
    ∀ (n a : ℕ) (F : (ℕ → X) → ℝ) (B : ℝ), BM F → 0 ≤ B →
      (∀ ℓ, OscLe (a + n) ℓ F (B * w ℓ)) → ∀ ℓ, OscLe a ℓ (Ch.seg a n F) (B * ρ ^ n * w ℓ) := by
  intro n
  induction n with
  | zero =>
    intro a F B _ _ h ℓ
    simpa [seg_zero] using h ℓ
  | succ n ih =>
    intro a F B hF hB h ℓ
    have h' : ∀ ℓ, OscLe (a + 1 + n) ℓ F (B * w ℓ) := by
      intro ℓ
      rw [show a + 1 + n = a + (n + 1) by omega]
      exact h ℓ
    have hG := ih (a + 1) F B hF hB h'
    have hGm := (Ch.seg_bm hF n (a + 1)).1
    have hBρ : 0 ≤ B * ρ ^ n := mul_nonneg hB (pow_nonneg hρ n)
    have hs := Ch.step_osc hO hv hGm (mul_nonneg hBρ (hw (ℓ + 1))) (hG (ℓ + 1)) (hG 0)
    rw [seg_succ]
    refine osc_mono hs ?_
    rw [hw0, pow_succ]
    have hk := mul_le_mul_of_nonneg_left (hstep ℓ) hBρ
    nlinarith [hk]

#print axioms seg_osc

/-! ### Linearity, constants and the slabs a function does not read -/

theorem step_const (t : ℕ) (c : ℝ) : Ch.step t (fun _ => c) = fun _ => c := by
  funext ω
  haveI := Ch.markov t
  simp only [step, integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem seg_const (c : ℝ) (n : ℕ) : ∀ a, Ch.seg a n (fun _ => c) = fun _ => c := by
  induction n with
  | zero => intro a; rfl
  | succ n ih => intro a; rw [seg_succ, ih (a + 1), Ch.step_const]

theorem step_pull {s t : ℕ} {g : (ℕ → X) → ℝ} (hg : ReadsBelow s g) (hst : s ≤ t)
    (F : (ℕ → X) → ℝ) : Ch.step t (fun ω => g ω * F ω) = fun ω => g ω * Ch.step t F ω := by
  funext ω
  have hgu : ∀ y, g (Function.update ω t y) = g ω := fun y =>
    hg _ _ (fun j hj => Function.update_of_ne (by omega) _ _)
  simp only [step]
  simp_rw [hgu]
  exact integral_const_mul _ _

theorem seg_pull {s : ℕ} {g : (ℕ → X) → ℝ} (hg : ReadsBelow s g) (F : (ℕ → X) → ℝ) (n : ℕ) :
    ∀ a, s ≤ a → Ch.seg a n (fun ω => g ω * F ω) = fun ω => g ω * Ch.seg a n F ω := by
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a ha
    rw [seg_succ, seg_succ, ih (a + 1) (by omega), Ch.step_pull hg ha]

theorem seg_reads {s : ℕ} {g : (ℕ → X) → ℝ} (hg : ReadsBelow s g) (n a : ℕ) (ha : s ≤ a) :
    Ch.seg a n g = g := by
  have h := Ch.seg_pull hg (fun _ => 1) n a ha
  rw [Ch.seg_const] at h
  simpa using h

theorem seg_add (n₁ : ℕ) : ∀ (n₂ a : ℕ) (F : (ℕ → X) → ℝ),
    Ch.seg a (n₁ + n₂) F = Ch.seg a n₁ (Ch.seg (a + n₁) n₂ F) := by
  induction n₁ with
  | zero => intro n₂ a F; simp [seg_zero]
  | succ n₁ ih =>
    intro n₂ a F
    rw [show n₁ + 1 + n₂ = (n₁ + n₂) + 1 by omega, seg_succ, seg_succ, ih n₂ (a + 1) F,
      show a + 1 + n₁ = a + (n₁ + 1) by omega]

theorem step_lin {t : ℕ} {F₁ F₂ : (ℕ → X) → ℝ} (h₁ : BM F₁) (h₂ : BM F₂) (u : ℝ) :
    Ch.step t (fun ω => F₁ ω - u * F₂ ω) = fun ω => Ch.step t F₁ ω - u * Ch.step t F₂ ω := by
  funext ω
  haveI := Ch.markov t
  obtain ⟨m₁, B₁, hB₁⟩ := h₁
  obtain ⟨m₂, B₂, hB₂⟩ := h₂
  have i₁ : Integrable (fun y => F₁ (Function.update ω t y)) (Ch.κ t ω) :=
    Integrable.of_bound (m₁.comp (measurable_update ω)).aestronglyMeasurable B₁
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB₁ _)
  have i₂ : Integrable (fun y => F₂ (Function.update ω t y)) (Ch.κ t ω) :=
    Integrable.of_bound (m₂.comp (measurable_update ω)).aestronglyMeasurable B₂
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB₂ _)
  simp only [step]
  rw [integral_sub i₁ (i₂.const_mul u), integral_const_mul]

theorem seg_lin {F₁ F₂ : (ℕ → X) → ℝ} (h₁ : BM F₁) (h₂ : BM F₂) (u : ℝ) (n : ℕ) :
    ∀ a, Ch.seg a n (fun ω => F₁ ω - u * F₂ ω)
      = fun ω => Ch.seg a n F₁ ω - u * Ch.seg a n F₂ ω := by
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    rw [seg_succ, seg_succ, seg_succ, ih (a + 1),
      Ch.step_lin (Ch.seg_bm h₁ n (a + 1)) (Ch.seg_bm h₂ n (a + 1)) u]

theorem seg_abs_le {F : (ℕ → X) → ℝ} {K : ℝ} (hF : ∀ ω, |F ω| ≤ K) (n : ℕ) :
    ∀ (a : ℕ) (ω : ℕ → X), |Ch.seg a n F ω| ≤ K := by
  induction n with
  | zero => intro a ω; exact hF ω
  | succ n ih =>
    intro a ω
    haveI := Ch.markov a
    rw [seg_succ]
    have h := norm_integral_le_of_norm_le_const (μ := Ch.κ a ω)
      (f := fun y => Ch.seg (a + 1) n F (Function.update ω a y)) (C := K)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact ih (a + 1) _)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
    exact h

/-- **Covariance of a past reading and a far reading.** `g` reads slabs `≤ s`, `|g| ≤ G`; `f` has
window bounds `B w ℓ` at slab `s + 1 + n`. Then the covariance under the reading law with boundary
`ω₀` is at most `2 G (B ρⁿ)`.

DERIVED: `2` the two terms of the covariance split; `0` the first slab; `1` the slab of `g`. -/
theorem cov_le {v : ℕ → ℝ} (hO : Ch.Overlap v) (hv : ∀ ℓ, v ℓ ≤ 1) {w : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hw0 : w 0 = 1) (hw : ∀ ℓ, 0 ≤ w ℓ)
    (hstep : ∀ ℓ, (1 - v ℓ) * w (ℓ + 1) + v ℓ ≤ ρ * w ℓ) {s n : ℕ} {g f : (ℕ → X) → ℝ}
    (hgm : BM g) (hgr : ReadsBelow (s + 1) g) {G : ℝ} (hG : ∀ ω, |g ω| ≤ G) (hfm : BM f) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ ℓ, OscLe (s + 1 + n) ℓ f (B * w ℓ)) (ω₀ : ℕ → X) :
    |Ch.seg 0 (s + 1 + n) (fun ω => g ω * f ω) ω₀
        - Ch.seg 0 (s + 1 + n) g ω₀ * Ch.seg 0 (s + 1 + n) f ω₀| ≤ 2 * G * (B * ρ ^ n) := by
  obtain ⟨H, hHdef⟩ : ∃ H, H = Ch.seg (s + 1) n f := ⟨_, rfl⟩
  have hH := Ch.seg_osc hO hv hρ hw0 hw hstep n (s + 1) f B hfm hB hf
  rw [← hHdef] at hH
  have hH0 : OscLe (s + 1) 0 H (B * ρ ^ n) := by
    have := hH 0; rwa [hw0, mul_one] at this
  obtain ⟨u, hu⟩ := rangeIn_of_osc hH0 ω₀
  have hHbm : BM H := by rw [hHdef]; exact Ch.seg_bm hfm n (s + 1)
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG ω₀)
  have e1 : Ch.seg 0 (s + 1 + n) (fun ω => g ω * f ω) = Ch.seg 0 (s + 1) (fun ω => g ω * H ω) := by
    rw [Ch.seg_add (s + 1) n 0, zero_add, Ch.seg_pull hgr f n (s + 1) le_rfl, hHdef]
  have e2 : Ch.seg 0 (s + 1 + n) g = Ch.seg 0 (s + 1) g := by
    rw [Ch.seg_add (s + 1) n 0, zero_add, Ch.seg_reads hgr n (s + 1) le_rfl]
  have e3 : Ch.seg 0 (s + 1 + n) f = Ch.seg 0 (s + 1) H := by
    rw [Ch.seg_add (s + 1) n 0, zero_add, hHdef]
  rw [e1, e2, e3]
  obtain ⟨hgm', Bg, hBg⟩ := hgm
  obtain ⟨hHm, BH, hBH⟩ := hHbm
  have hgH : BM (fun ω => g ω * H ω) := ⟨hgm'.mul hHm, Bg * BH, fun ω => by
    show |g ω * H ω| ≤ Bg * BH
    rw [abs_mul]
    exact mul_le_mul (hBg ω) (hBH ω) (abs_nonneg _) ((abs_nonneg _).trans (hBg ω))⟩
  have hone : BM (fun _ : ℕ → X => (1 : ℝ)) := ⟨measurable_const, 1, fun _ => by simp⟩
  -- `E(gH) − u E g = E(g (H − u))`
  have l1 : Ch.seg 0 (s + 1) (fun ω => g ω * H ω - u * g ω) ω₀
      = Ch.seg 0 (s + 1) (fun ω => g ω * H ω) ω₀ - u * Ch.seg 0 (s + 1) g ω₀ :=
    congrFun (Ch.seg_lin hgH ⟨hgm', Bg, hBg⟩ u (s + 1) 0) ω₀
  have b1 : |Ch.seg 0 (s + 1) (fun ω => g ω * H ω - u * g ω) ω₀| ≤ G * (B * ρ ^ n) := by
    refine Ch.seg_abs_le (fun ω => ?_) (s + 1) 0 ω₀
    show |g ω * H ω - u * g ω| ≤ G * (B * ρ ^ n)
    rw [show g ω * H ω - u * g ω = g ω * (H ω - u) by ring, abs_mul]
    have : |H ω - u| ≤ B * ρ ^ n := by
      rw [abs_le]; constructor <;> linarith [(hu ω).1, (hu ω).2]
    exact mul_le_mul (hG ω) this (abs_nonneg _) hG0
  -- `E H − u = E (H − u)`
  have l2 : Ch.seg 0 (s + 1) (fun ω => H ω - u * 1) ω₀ = Ch.seg 0 (s + 1) H ω₀ - u * 1 := by
    have h := congrFun (Ch.seg_lin ⟨hHm, BH, hBH⟩ hone u (s + 1) 0) ω₀
    rw [Ch.seg_const] at h
    exact h
  have b2 : |Ch.seg 0 (s + 1) (fun ω => H ω - u * 1) ω₀| ≤ B * ρ ^ n := by
    refine Ch.seg_abs_le (fun ω => ?_) (s + 1) 0 ω₀
    show |H ω - u * 1| ≤ B * ρ ^ n
    rw [mul_one, abs_le]; constructor <;> linarith [(hu ω).1, (hu ω).2]
  have b3 : |Ch.seg 0 (s + 1) g ω₀| ≤ G := Ch.seg_abs_le hG (s + 1) 0 ω₀
  rw [l1] at b1
  rw [l2, mul_one] at b2
  have hsplit : Ch.seg 0 (s + 1) (fun ω => g ω * H ω) ω₀ - Ch.seg 0 (s + 1) g ω₀ * Ch.seg 0 (s + 1) H ω₀
      = (Ch.seg 0 (s + 1) (fun ω => g ω * H ω) ω₀ - u * Ch.seg 0 (s + 1) g ω₀)
        - Ch.seg 0 (s + 1) g ω₀ * (Ch.seg 0 (s + 1) H ω₀ - u) := by ring
  rw [hsplit]
  have hprod : |Ch.seg 0 (s + 1) g ω₀ * (Ch.seg 0 (s + 1) H ω₀ - u)| ≤ G * (B * ρ ^ n) := by
    rw [abs_mul]; exact mul_le_mul b3 b2 (abs_nonneg _) hG0
  have hb1 := abs_le.1 b1
  have hp := abs_le.1 hprod
  rw [abs_le]
  constructor <;> linarith [hb1.1, hb1.2, hp.1, hp.2]

#print axioms cov_le

/-! ## 3. Minorisation and memory -/

/-- **Minorisation (Doeblin).** Every conditional law of the next slab, given any past, contains the
fixed measure `μ₀` of mass at least `c` (`μ₀ = c ν`, `ν` the fixed reference law).

DERIVED: no numeral. -/
def Doeblin (c : ℝ) (μ₀ : Measure X) : Prop :=
  IsFiniteMeasure μ₀ ∧ c ≤ μ₀.real univ ∧
    ∀ t (ω : ℕ → X), ∃ r : Measure X, IsFiniteMeasure r ∧ Ch.κ t ω = μ₀ + r

/-- **Memory (continuity of the complete connections).** Pasts agreeing on their last `ℓ ≥ 1` slabs
give next-slab laws within total variation `η θ^ℓ`.

DERIVED: `1` the least window. -/
def Memory (η θ : ℝ) : Prop :=
  ∀ t ℓ, 1 ≤ ℓ → ∀ ω ω' : ℕ → X, Agree t ℓ ω ω' → ∃ m r r' : Measure X, IsFiniteMeasure m ∧
    IsFiniteMeasure r ∧ IsFiniteMeasure r' ∧ Ch.κ t ω = m + r ∧ Ch.κ t ω' = m + r' ∧
      1 - η * θ ^ ℓ ≤ m.real univ

end ReadingChain

/-- The overlap profile of minorisation `c` and memory `(η, θ)`.

DERIVED: `0` the global window; `1` the cap of a total variation. -/
def vDM (c η θ : ℝ) (ℓ : ℕ) : ℝ := if ℓ = 0 then 1 - c else min (η * θ ^ ℓ) 1

theorem overlap_of_doeblin_memory {X : Type*} [MeasurableSpace X] {Ch : ReadingChain X} {c η θ : ℝ}
    {μ₀ : Measure X} (hD : Ch.Doeblin c μ₀) (hM : Ch.Memory η θ) : Ch.Overlap (vDM c η θ) := by
  intro t ℓ ω ω' hω
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · obtain ⟨hfin, hc, hall⟩ := hD
    obtain ⟨r, hr, e⟩ := hall t ω
    obtain ⟨r', hr', e'⟩ := hall t ω'
    refine ⟨μ₀, r, r', hfin, hr, hr', e, e', ?_⟩
    rw [show vDM c η θ 0 = 1 - c from if_pos rfl]
    linarith
  · obtain ⟨m, r, r', hm, hr, hr', e, e', hM'⟩ := hM t ℓ hℓ ω ω' hω
    refine ⟨m, r, r', hm, hr, hr', e, e', ?_⟩
    rw [show vDM c η θ ℓ = min (η * θ ^ ℓ) 1 from if_neg (Nat.pos_iff_ne_zero.1 hℓ)]
    rcases min_cases (η * θ ^ ℓ) 1 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · exact hM'
    · simp only [sub_self]; exact measureReal_nonneg

/-- The Lyapunov profile of exponential memory: `w 0 = 1`, `w ℓ = (η/(ρ − θ)) θ^ℓ` for `ℓ ≥ 1`.

DERIVED: `0` and `1` the global window and its weight. -/
def wExp (η θ ρ : ℝ) (ℓ : ℕ) : ℝ := if ℓ = 0 then 1 else η / (ρ - θ) * θ ^ ℓ

theorem wExp_step {c η θ ρ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hθρ : θ < ρ) (hcond : 1 - c + c * (η / (ρ - θ) * θ) ≤ ρ) (ℓ : ℕ) :
    (1 - vDM c η θ ℓ) * wExp η θ ρ (ℓ + 1) + vDM c η θ ℓ ≤ ρ * wExp η θ ρ ℓ := by
  have hκ0 : 0 ≤ η / (ρ - θ) := div_nonneg hη (by linarith)
  have hκe : η / (ρ - θ) * (ρ - θ) = η := div_mul_cancel₀ η (by linarith)
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have e0 : vDM c η θ 0 = 1 - c := if_pos rfl
    have e1 : wExp η θ ρ (0 + 1) = η / (ρ - θ) * θ := by
      rw [show wExp η θ ρ (0 + 1) = η / (ρ - θ) * θ ^ (0 + 1) from if_neg (Nat.succ_ne_zero 0),
        zero_add, pow_one]
    have e2 : wExp η θ ρ 0 = 1 := if_pos rfl
    rw [e0, e1, e2]
    linarith
  · have hne : ℓ ≠ 0 := Nat.pos_iff_ne_zero.1 hℓ
    have e0 : vDM c η θ ℓ = min (η * θ ^ ℓ) 1 := if_neg hne
    have e1 : wExp η θ ρ (ℓ + 1) = η / (ρ - θ) * θ ^ (ℓ + 1) := if_neg (Nat.succ_ne_zero ℓ)
    have e2 : wExp η θ ρ ℓ = η / (ρ - θ) * θ ^ ℓ := if_neg hne
    rw [e0, e1, e2, pow_succ]
    have hT0 : 0 ≤ θ ^ ℓ := pow_nonneg hθ ℓ
    have hv0 : 0 ≤ min (η * θ ^ ℓ) 1 := le_min (mul_nonneg hη hT0) zero_le_one
    have hv1 : min (η * θ ^ ℓ) 1 ≤ η * θ ^ ℓ := min_le_left _ _
    have hprod : 0 ≤ min (η * θ ^ ℓ) 1 * (η / (ρ - θ) * (θ ^ ℓ * θ)) :=
      mul_nonneg hv0 (mul_nonneg hκ0 (mul_nonneg hT0 hθ))
    have hkT : η / (ρ - θ) * (ρ - θ) * θ ^ ℓ = η * θ ^ ℓ := by rw [hκe]
    nlinarith [hprod, hkT, hv1]

/-- **A rate below one exists** when `η θ < 1 − θ`: some `ρ ∈ (θ, 1)` satisfies the profile condition
`1 − c + c (η/(ρ − θ)) θ ≤ ρ`.

DERIVED: `1` the top of the rate; `0` the lower bound. -/
theorem exists_rate {c η θ : ℝ} (hc : 0 < c) (hθ1 : θ < 1) (hsmall : η * θ < 1 - θ) :
    ∃ ρ : ℝ, θ < ρ ∧ 0 < ρ ∧ ρ < 1 ∧ 1 - c + c * (η / (ρ - θ) * θ) ≤ ρ := by
  have hcont : ContinuousAt (fun ρ : ℝ => ρ - (1 - c + c * (η / (ρ - θ) * θ))) 1 := by
    refine continuousAt_id.sub (continuousAt_const.add (continuousAt_const.mul
      ((continuousAt_const.div (continuousAt_id.sub continuousAt_const) ?_).mul continuousAt_const)))
    show (1 : ℝ) - θ ≠ 0
    exact sub_ne_zero.2 (ne_of_gt hθ1)
  have hpos : 0 < 1 - (1 - c + c * (η / (1 - θ) * θ)) := by
    have h1 : η * θ / (1 - θ) < 1 := (div_lt_one (by linarith)).2 hsmall
    have e : η / (1 - θ) * θ = η * θ / (1 - θ) := div_mul_eq_mul_div η (1 - θ) θ
    rw [e]
    nlinarith [mul_pos hc (sub_pos.2 h1)]
  have h1 : ∀ᶠ ρ in 𝓝 (1 : ℝ), 0 < ρ - (1 - c + c * (η / (ρ - θ) * θ)) :=
    hcont.tendsto.eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ ρ in 𝓝 (1 : ℝ), θ < ρ := lt_mem_nhds hθ1
  have h3 : ∀ᶠ ρ in 𝓝 (1 : ℝ), 0 < ρ := lt_mem_nhds one_pos
  have h4 : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ < 1 := self_mem_nhdsWithin
  obtain ⟨ρ, ⟨hφρ, hθρ, hρ0⟩, hρ1⟩ :=
    (((h1.and (h2.and h3)).filter_mono nhdsWithin_le_nhds).and h4).exists
  exact ⟨ρ, hθρ, hρ0, hρ1, by linarith⟩

/-- **Uniform minorisation and exponential memory of the reading process give clustering at one
rate.** For `0 < c`, `0 ≤ θ < 1`, `η ≥ 0`, `η θ < 1 − θ` there is `ρ ∈ (0, 1)`, depending on
`(c, η, θ)` only, such that for every reading chain with `Doeblin c` and `Memory η θ`, every past
reading function `g` (slabs `≤ s`, `|g| ≤ G`), every bounded reading `φ` of slab `s + n` (`|φ| ≤ B`)
and every boundary path, `|Cov(g, φ(x_{s+n}))| ≤ 4 G B ρⁿ`.

DERIVED: `4 = 2 · 2` (`cov_le` and `osc φ ≤ 2B`); `1` the slab of `g`. -/
theorem reading_cluster {c η θ : ℝ} (hc : 0 < c) (hη : 0 ≤ η) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hsmall : η * θ < 1 - θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ {X : Type} [MeasurableSpace X] (Ch : ReadingChain X)
      (μ₀ : Measure X), Ch.Doeblin c μ₀ → Ch.Memory η θ → ∀ (s n : ℕ) (g : (ℕ → X) → ℝ)
      (φ : X → ℝ) (G B : ℝ), BM g → ReadsBelow (s + 1) g → (∀ ω, |g ω| ≤ G) → Measurable φ →
      (∀ x, |φ x| ≤ B) → ∀ ω₀ : ℕ → X,
        |Ch.seg 0 (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀
          - Ch.seg 0 (s + 1 + n) g ω₀ * Ch.seg 0 (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀|
          ≤ 4 * G * B * ρ ^ n := by
  obtain ⟨ρ, hθρ, hρ0, hρ1, hcond⟩ := exists_rate hc hθ1 hsmall
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro X _ Ch μ₀ hD hM s n g φ G B hg hgr hG hφ hB ω₀
  have hO := overlap_of_doeblin_memory hD hM
  have hv : ∀ ℓ, vDM c η θ ℓ ≤ 1 := fun ℓ => by
    unfold vDM; split_ifs
    · linarith
    · exact min_le_right _ _
  have hκ0 : 0 ≤ η / (ρ - θ) := div_nonneg hη (by linarith)
  have hw0 : wExp η θ ρ 0 = 1 := by simp [wExp]
  have hw : ∀ ℓ, 0 ≤ wExp η θ ρ ℓ := fun ℓ => by
    unfold wExp; split_ifs
    · exact zero_le_one
    · exact mul_nonneg hκ0 (pow_nonneg hθ0 ℓ)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (ω₀ 0))
  have hf : ∀ ℓ, OscLe (s + 1 + n) ℓ (fun ω : ℕ → X => φ (ω (s + n))) (2 * B * wExp η θ ρ ℓ) := by
    intro ℓ ω ω' hω
    show |φ (ω (s + n)) - φ (ω' (s + n))| ≤ 2 * B * wExp η θ ρ ℓ
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · rw [hw0, mul_one]
      have ha := abs_le.1 (hB (ω (s + n)))
      have hb := abs_le.1 (hB (ω' (s + n)))
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    · have : ω (s + n) = ω' (s + n) := hω (s + n) (by omega) (by omega)
      rw [this, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg zero_le_two hB0) (hw ℓ)
  have hfm : BM (fun ω : ℕ → X => φ (ω (s + n))) :=
    ⟨hφ.comp (measurable_pi_apply (s + n)), B, fun ω => hB _⟩
  have h := Ch.cov_le hO hv hρ0.le hw0 hw (wExp_step hη hθ0 hθρ hcond) hg hgr hG hfm
    (mul_nonneg zero_le_two hB0) hf ω₀
  calc _ ≤ 2 * G * (2 * B * ρ ^ n) := h
    _ = 4 * G * B * ρ ^ n := by ring

#print axioms reading_cluster

/-! ## 3b. The aperture: fixed cells, fixed range, one chain per zoom -/

/-- **The observer's aperture.** `K` cells of physical side `side`, each returning one reading in the
fixed measurable range `Y`; slabs of physical thickness `slab`. At zoom `k` the configuration space
is `Config k` and `read k` gives the readings of every slab; `chain k` is the law of those readings
as a chain with complete connections (the conditional law of the next slab's readings given all past
readings). `K`, `Y`, `side`, `slab` carry no zoom index.

The identification of `chain k` with the law of `read k` under the zoom-`k` measure is not a field:
no statement here reads `Config` or `read`; they name what the chain is the law of.

DERIVED: no numeral. -/
structure ApertureReading where
  /-- The number of cells. -/
  K : ℕ
  /-- The range of one cell's reading. -/
  Y : Type
  [mY : MeasurableSpace Y]
  /-- The physical side of a cell. -/
  side : ℝ
  /-- The physical thickness of a slab. -/
  slab : ℝ
  side_pos : 0 < side
  slab_pos : 0 < slab
  /-- The substrate configurations at zoom `k`. -/
  Config : ℕ → Type
  /-- The readings of every slab of a zoom-`k` configuration. -/
  read : ∀ k, Config k → ℕ → Fin K → Y
  /-- The law of the readings at zoom `k`. -/
  chain : ℕ → @ReadingChain (Fin K → Y) (@MeasurableSpace.pi (Fin K) (fun _ => Y) fun _ => mY)

attribute [instance] ApertureReading.mY

/-- **The aperture clusters at a fixed physical mass, uniformly in the zoom.** If every zoom's reading
chain has minorisation `c` and memory `(η, θ)` (the same constants at every `k`, with reference
measures that may depend on `k`), there is `m > 0` with
`|Cov_k(g, φ(x_{s+n}))| ≤ 4 G B e^{−m (n · slab)}` at every zoom, every slab distance `n` and every
boundary. `n · slab` is the physical time separation.

DERIVED: `4` from `reading_cluster`; `1` the slab of `g`. -/
theorem aperture_cluster (A : ApertureReading) {c η θ : ℝ} (hc : 0 < c) (hη : 0 ≤ η)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hsmall : η * θ < 1 - θ) (μ₀ : ℕ → Measure (Fin A.K → A.Y))
    (hD : ∀ k, (A.chain k).Doeblin c (μ₀ k)) (hM : ∀ k, (A.chain k).Memory η θ) :
    ∃ m : ℝ, 0 < m ∧ ∀ (k s n : ℕ) (g : (ℕ → Fin A.K → A.Y) → ℝ) (φ : (Fin A.K → A.Y) → ℝ)
      (G B : ℝ), BM g → ReadsBelow (s + 1) g → (∀ ω, |g ω| ≤ G) → Measurable φ →
      (∀ x, |φ x| ≤ B) → ∀ ω₀ : ℕ → Fin A.K → A.Y,
        |(A.chain k).seg 0 (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀
          - (A.chain k).seg 0 (s + 1 + n) g ω₀
            * (A.chain k).seg 0 (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀|
          ≤ 4 * G * B * Real.exp (-(m * (n * A.slab))) := by
  obtain ⟨ρ, hρ0, hρ1, hcl⟩ := reading_cluster hc hη hθ0 hθ1 hsmall
  have hlog : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  refine ⟨-Real.log ρ / A.slab, div_pos (by linarith) A.slab_pos, ?_⟩
  intro k s n g φ G B hg hgr hG hφ hB ω₀
  have h := hcl (A.chain k) (μ₀ k) (hD k) (hM k) s n g φ G B hg hgr hG hφ hB ω₀
  have e : Real.exp (-(-Real.log ρ / A.slab * (n * A.slab))) = ρ ^ n := by
    rw [show -(-Real.log ρ / A.slab * (n * A.slab)) = n * Real.log ρ by
      field_simp [A.slab_pos.ne']]
    rw [Real.exp_nat_mul, Real.exp_log hρ0]
  rw [e]
  exact h

#print axioms aperture_cluster

/-! ## 4. Wiring to the observer's gap -/

section Wiring

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumCluster MassGap.ContinuumSep MassGap.ContinuumFlow MassGap.ContinuumHypercubic

variable {N : ℕ}

/-- **Lattice clustering eventually in the zoom gives the observer's clustering.** A bound
`C e^{−(c/L) aₘ n}` on the connected flowed lattice kernel, eventually in the zoom, with `c` fixed
and `C` depending on the step and the pair, passes through the ultrafilter limit to
`FlowClusterAbs`.

DERIVED: `0` the lower end of `c`; `4` in `Fin 4` the dimension. -/
theorem flowClusterAbs_of_lattice (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r L : ℝ}
    (h : ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (P Q : MarginMono N τ r), ∃ C : ℝ, ∀ n : ℕ,
      ∀ᶠ k in atTop,
        |latSF hN Φ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
          - latSF hN Φ k (pairFam τ P.1 (emptyMono N)) * latSF hN Φ k (pairFam τ (emptyMono N) Q.1)|
          ≤ C * Real.exp (-(c / L) * (dySpacing N m * n))) :
    FlowCapstone.FlowClusterAbs hN Φ τ r L := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  obtain ⟨c, hc, hcl⟩ := h
  refine ⟨c, hc, fun m P Q => ?_⟩
  obtain ⟨C, hC⟩ := hcl m P Q
  refine ⟨C, fun n => ?_⟩
  have tl : ∀ X Y : Mono N, Tendsto (fun k => latSF hN Φ k (pairFam τ X Y)) (ultra : Filter ℕ)
      (𝓝 (kernF hN Φ τ X Y)) := fun X Y => tendsto_contSF hN Φ hB (pairFam τ X Y)
  have hf := ((tl P.1 (Mono.shift (timeVec N m τ n) Q.1)).sub
    ((tl P.1 (emptyMono N)).mul (tl (emptyMono N) Q.1))).abs
  exact le_of_tendsto hf ((hC n).filter_mono ultra_le)

#print axioms flowClusterAbs_of_lattice

/-- **The reading representation.** For every step `m` and pair of margin monomials there is `A`
such that for every time shift `n`, eventually in the zoom, the connected flowed lattice kernel is
the covariance of a past reading function `g` and a reading `φ` of a slab `j` slabs later, under a
reading chain with minorisation `c` and memory `(η, θ)`, with `4 G B ≤ A` and the physical shift
`aₘ n` at most `j` slabs of thickness `ℓ`. The reading space may depend on the step and the pair; the
constants `(c, η, θ)` and `ℓ` may not.

DERIVED: `4` from `reading_cluster`; `0` the first slab; `1` the slab of `g`. -/
def ReadingRep (hN : N ≠ 0) (Φ : Flow N) (τ : Fin 4) (r ℓ c η θ : ℝ) : Prop :=
  ∀ (m : ℕ) (P Q : MarginMono N τ r), ∃ A : ℝ, ∀ n : ℕ, ∀ᶠ k in atTop,
    ∃ (X : Type) (_ : MeasurableSpace X) (Ch : ReadingChain X) (μ₀ : Measure X) (s j : ℕ)
      (g : (ℕ → X) → ℝ) (φ : X → ℝ) (G B : ℝ) (ω₀ : ℕ → X),
      Ch.Doeblin c μ₀ ∧ Ch.Memory η θ ∧ BM g ∧ ReadsBelow (s + 1) g ∧ (∀ ω, |g ω| ≤ G) ∧
        Measurable φ ∧ (∀ x, |φ x| ≤ B) ∧ 4 * G * B ≤ A ∧ dySpacing N m * n ≤ ℓ * j ∧
        latSF hN Φ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
            - latSF hN Φ k (pairFam τ P.1 (emptyMono N)) * latSF hN Φ k (pairFam τ (emptyMono N) Q.1)
          = Ch.seg 0 (s + 1 + j) (fun ω => g ω * φ (ω (s + j))) ω₀
            - Ch.seg 0 (s + 1 + j) g ω₀ * Ch.seg 0 (s + 1 + j) (fun ω => φ (ω (s + j))) ω₀

/-- **Input 4 from the reading representation.** `ReadingRep` with `0 < c`, `0 ≤ θ < 1`,
`η ≥ 0`, `η θ < 1 − θ` and slab thickness `ℓ > 0` gives, at every step `m₀`, `GapAt (transferN …) ρ`
for some `ρ ∈ (0, 1)`.

DERIVED: `0`, `1` bracket the rate; `4` in `Fin 4` the dimension. -/
theorem gapAt_of_readingRep (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4)
    {r ℓ c η θ : ℝ} (hphys : Φ.PhysRange r) (hℓ : 0 < ℓ) (hc : 0 < c) (hη : 0 ≤ η)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hsmall : η * θ < 1 - θ) (hrep : ReadingRep hN Φ τ r ℓ c η θ)
    (m0 : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN Φ hB τ hphys m0) ρ := by
  obtain ⟨ρ, hρ0, hρ1, hcl⟩ := reading_cluster hc hη hθ0 hθ1 hsmall
  have hlog : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hlat : ∃ c' : ℝ, 0 < c' ∧ ∀ (m : ℕ) (P Q : MarginMono N τ r), ∃ C : ℝ, ∀ n : ℕ,
      ∀ᶠ k in atTop,
        |latSF hN Φ k (pairFam τ P.1 (Mono.shift (timeVec N m τ n) Q.1))
          - latSF hN Φ k (pairFam τ P.1 (emptyMono N)) * latSF hN Φ k (pairFam τ (emptyMono N) Q.1)|
          ≤ C * Real.exp (-(c' / ℓ) * (dySpacing N m * n)) := by
    refine ⟨-Real.log ρ, by linarith, fun m P Q => ?_⟩
    obtain ⟨A, hA⟩ := hrep m P Q
    refine ⟨A, fun n => ?_⟩
    filter_upwards [hA n] with k hk
    obtain ⟨X, _, Ch, μ₀, s, j, g, φ, G, B, ω₀, hD, hM, hg, hgr, hG, hφ, hBφ, hAle, hsep, heq⟩ := hk
    rw [heq]
    have h := hcl Ch μ₀ hD hM s j g φ G B hg hgr hG hφ hBφ ω₀
    have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG ω₀)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hBφ (ω₀ 0))
    have hA0 : 0 ≤ A := le_trans (by positivity) hAle
    have hpow : ρ ^ j ≤ Real.exp (-(-Real.log ρ / ℓ) * (dySpacing N m * n)) := by
      rw [← Real.exp_log hρ0, ← Real.exp_nat_mul, Real.exp_log hρ0, Real.exp_le_exp]
      have h1 : -(-Real.log ρ / ℓ) * (dySpacing N m * n) = Real.log ρ / ℓ * (dySpacing N m * n) := by
        ring
      rw [h1]
      have h2 : (j : ℝ) * Real.log ρ = Real.log ρ / ℓ * (ℓ * j) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonpos_left hsep (div_nonpos_of_nonpos_of_nonneg hlog.le hℓ.le)
    calc _ ≤ 4 * G * B * ρ ^ j := h
      _ ≤ A * ρ ^ j := mul_le_mul_of_nonneg_right hAle (pow_nonneg hρ0.le j)
      _ ≤ A * Real.exp (-(-Real.log ρ / ℓ) * (dySpacing N m * n)) :=
          mul_le_mul_of_nonneg_left hpow hA0
  have hcl' := flowClusterAbs_of_lattice hN Φ hB τ (L := ℓ) hlat
  exact (ObserverGapScale.flowClusterAbs_iff_gapAt hN Φ hB τ
    (Flow.posPreserving_of_physRange hN Φ hphys τ) m0 hℓ).mp hcl'

#print axioms gapAt_of_readingRep

end Wiring

end MassGap.ApertureFixed
