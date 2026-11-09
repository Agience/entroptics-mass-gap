import Mathlib
import MassGap.ApertureFixed

/-!
# MassGap.FiniteInformation — a finite aperture passes a bounded fraction forward per slab

The step stated in words: the aperture is finite and fixed relative to the observer; it reads from an
infinite substrate; it holds a fixed, finite amount of information; each slab can pass on only a
bounded fraction of what it holds, so the past is squeezed out geometrically, a fixed factor per fixed
length. This module makes that a statement and proves what it gives.

## 1. Finite information: a channel on a finite alphabet (`Chan`, `Minor`, `Contracts`)

The aperture's readings of one slab take values in a finite alphabet `X` (`K` cells, each read to
finite precision). One slab is a channel `Chan X Y`: a stochastic matrix `P x y`.

* `Contracts K η`: every test `f` of oscillation at most `δ` is sent to `K f` of oscillation at most
  `η δ`. The least such `η` is the Dobrushin coefficient; `sdpi_tv` shows it is the strong
  data-processing (SDPI) coefficient for total variation: `tv(μK, νK) ≤ η · tv(μ, ν)`.
* `Minor K c`: any two rows share mass at least `c` (`Σ_y min(P x y, P x' y) ≥ c`).
* `contracts_of_minor`: `Minor K c` gives `Contracts K (1 − c)`.
* `minor_of_floor`: a full-support channel with every entry at least `ε` has
  `Minor K (|Y| ε)`, so its coefficient is at most `1 − |Y| ε < 1`. This is the place where the
  alphabet being finite enters: on an infinite alphabet a positive entry floor is impossible.
* `contracts_comp`: coefficients multiply under composition.

## 2. Geometric forgetting (`forget`, `geometric_forgetting`, `aperture_forgetting`)

For slab channels `K t` all with `Minor c`, the `n`-slab conditional expectation `iter K a n f` has
oscillation at most `(1 − c)ⁿ δ`, and the covariance of a reading at slab `a` with a reading `n` slabs
later is at most `G δ (1 − c)ⁿ`. With zoom-independent `c` and slab length this is a mass in physical
units, uniform in the zoom.

## 3. The reading chain of `ApertureFixed` (`toChain`, `markov_reading_cluster`)

A finite-state Markov reading process is a `ReadingChain` with `Memory 0 θ` (exactly) and, under a
Doeblin floor `c ν`, `Doeblin c`. So `ApertureFixed.reading_cluster` applies with the memory clause
satisfied identically.

## 4. The crux: what is passed forward is only what the aperture holds

The substrate is a state space `Ω` of unrestricted size (infinite information); one slab of the
substrate is an operator `T` on functions of the substrate state (the conditional expectation over the
next slab given the whole present substrate state); `π : Ω → X` is the aperture's reading.

* `Passes T π K` (the exact form of the step): `T (f ∘ π) = (K f) ∘ π` for every reading test `f`.
  The conditional law of the next slab's readings, given the whole substrate state, depends on that
  state only through what the aperture holds, and is the finite channel `K`. (Lumpability of the
  substrate transfer onto the aperture's alphabet.)
* `substrate_forgets`: `Passes` and `Minor c` give: the dependence of a reading `n` slabs ahead on the
  whole present substrate state is at most `(1 − c)ⁿ δ`. The infinite substrate is forgotten
  geometrically, not only the past readings.
* `PassesWithin T π K ε` (the approximate form): the next reading's conditional expectation given the
  whole substrate state is within `ε δ` of `(K f) ∘ π`.
* `substrate_forgets_to_floor`: `PassesWithin ε` (with `T` non-expansive) and `Minor c` give
  dependence at most `(1 − c)ⁿ δ + 2 ε δ / c`: geometric decay down to a floor `2 ε δ / c`, not to `0`.
* `floor_attained`: the floor is attained. A hidden bit that the substrate keeps forever and that tilts
  each reading by `ε` satisfies `PassesWithin (ε/2)` with `Minor 1`, and the dependence of every later
  reading on that bit is exactly `ε = 2 (ε/2) · 1 / 1` at every `n ≥ 1`. A per-slab error that does not
  vanish is never squeezed out.

So the form needed is the exact one, `Passes`, with `Minor c` for one `c`, at every zoom
(`FiniteInformationStep`, consumed by `finite_information_mass`); or an approximate form whose error
vanishes. A fixed per-slab error `ε > 0`, however small, leaves a floor and gives no mass. The
approximate form that does give a mass is the one in `ApertureFixed`: an error that decays
geometrically in the depth of agreeing past (`Memory η θ`), not a per-slab `ε`.

`FiniteInformationStep` is a hypothesis; no declaration constructs it for the Wilson measure.

## Tests (`research/code/finite_information_checks.py`)

4D lattice Gaussian, two cell-and-slab readings, zooms `n = 2, 3, 4`: the one-slab coefficient is
below one and zoom-stable for the massive and the massless field alike (maximal correlation
`0.22–0.27` and `0.31–0.36`; Dobrushin coefficient of the 9-letter discretised channel `0.24–0.30` and
`0.33–0.38`). Neither reading process is Markov: the per-slab defect of the 3-letter one-cell reading
is `ε ≈ 0.01–0.02` in both, so `Passes` fails for both at finite resolution and the floor `2ε/c`
exceeds both fields' dependence beyond a few slabs. What separates them is the depth decay of the
defect: past-to-future maximal correlation decays at `≈ 1.1` per slab (massive, box-independent)
against a power law of slope `≈ 2` (massless, its rate tracking the box). 2D `SU(2)`: the Polyakov
class is an exact Markov chain (`Passes` onto the class, a compact one-parameter state), maximal
correlation `a_{1/2}(β)^{n²} → e^{−3/8}` and two-slab Doeblin floor `≈ 0.009`, uniform in `β = 4n²`;
binning the class into four letters gives a defect `ε ≈ 0.11`, also uniform in `β`. The step's
"finite" holds there as a fixed compact state, not as a finite alphabet.

DERIVED (module-wide): `1` the mass of a probability vector and the top of every coefficient; `0` the
empty iteration; `2` the two endpoints of an oscillation (`|u ω − u ω'|` through a reference point);
`1/2` and `(1 ± ε)/2` the uniform channel and its tilt on two letters in `floor_attained`; `c/2` the
midpoint between `1 − c` and `1` used to place a rate strictly below one.
-/

noncomputable section

namespace MassGap.FiniteInformation

open MeasureTheory ProbabilityTheory Finset
open MassGap.ApertureFixed

/-! ## 1. Channels on finite alphabets -/

/-- **One slab as a channel on a finite alphabet.** `P x y` is the probability that the next slab's
reading is `y` when the aperture holds `x`.

DERIVED: `1` the mass of a row. -/
structure Chan (X Y : Type*) [Fintype Y] where
  /-- The transition probabilities. -/
  P : X → Y → ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  sum_one : ∀ x, ∑ y, P x y = 1

/-- A probability vector on a finite alphabet.

DERIVED: `0`, `1` the range and mass of a probability. -/
def IsProb {Y : Type*} [Fintype Y] (μ : Y → ℝ) : Prop := (∀ y, 0 ≤ μ y) ∧ ∑ y, μ y = 1

namespace Chan

variable {X Y Z : Type*} [Fintype Y] [Fintype Z]

/-- The channel applied to a test: `(K f) x = Σ_y P x y f y`, the conditional expectation of `f` of
the next reading. -/
def app (K : Chan X Y) (f : Y → ℝ) (x : X) : ℝ := ∑ y, K.P x y * f y

/-- Two slabs in sequence. -/
def comp (K : Chan X Y) (L : Chan Y Z) : Chan X Z where
  P x z := ∑ y, K.P x y * L.P y z
  nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (K.nonneg x y) (L.nonneg y z)
  sum_one x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, L.sum_one, mul_one, K.sum_one]

theorem app_comp (K : Chan X Y) (L : Chan Y Z) (f : Z → ℝ) (x : X) :
    (K.comp L).app f x = K.app (L.app f) x := by
  simp only [app, comp, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem row_prob (K : Chan X Y) (x : X) : IsProb (K.P x) := ⟨K.nonneg x, K.sum_one x⟩

end Chan

/-- `f` varies by at most `δ`: `f y − f y' ≤ δ` for every pair. -/
def OscB {Y : Type*} (f : Y → ℝ) (δ : ℝ) : Prop := ∀ y y', f y - f y' ≤ δ

theorem oscB_nonneg {Y : Type*} [Nonempty Y] {f : Y → ℝ} {δ : ℝ} (h : OscB f δ) : 0 ≤ δ := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  simpa using h y y

/-- **Two masses of equal size against one test.** `a, b ≥ 0` with `Σ a = Σ b = s` and `f` of
oscillation at most `δ`: `Σ a f − Σ b f ≤ s δ`. -/
theorem two_mass {Y : Type*} [Fintype Y] [Nonempty Y] {a b f : Y → ℝ} {s δ : ℝ}
    (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y) (hsa : ∑ y, a y = s) (hsb : ∑ y, b y = s)
    (hf : OscB f δ) : ∑ y, a y * f y - ∑ y, b y * f y ≤ s * δ := by
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have ea : ∑ y, a y * (f y - f y₀) = ∑ y, a y * f y - s * f y₀ := by
    rw [← hsa, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have eb : ∑ y, b y * (f y - f y₀) = ∑ y, b y * f y - s * f y₀ := by
    rw [← hsb, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h1 : ∑ y, a y * (f y - f y₀) ≤ ∑ y, a y * δ :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf y y₀) (ha y)
  have h1' : ∑ y, a y * δ = s * δ := by rw [← Finset.sum_mul, hsa]
  have h2 : 0 ≤ ∑ y, b y * (f y - f y₀) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hb y) (sub_nonneg.2 (hy₀ y (Finset.mem_univ _)))
  linarith

/-- The common mass of two vectors, `Σ_y min(μ y, ν y)`. -/
def ov {Y : Type*} [Fintype Y] (μ ν : Y → ℝ) : ℝ := ∑ y, min (μ y) (ν y)

/-- Total variation of two probability vectors, `1 − Σ min`.

DERIVED: `1` the mass of a probability vector. -/
def tv {Y : Type*} [Fintype Y] (μ ν : Y → ℝ) : ℝ := 1 - ov μ ν

section Coefficient

variable {X Y : Type*} [Fintype Y]

/-- **Minorisation (pairwise).** Any two rows share mass at least `c`. -/
def Minor (K : Chan X Y) (c : ℝ) : Prop := ∀ x x', c ≤ ov (K.P x) (K.P x')

/-- **The contraction (Dobrushin / SDPI) coefficient bound.** Every test of oscillation `δ` is sent to
one of oscillation `η δ`. -/
def Contracts (K : Chan X Y) (η : ℝ) : Prop :=
  ∀ (f : Y → ℝ) (δ : ℝ), OscB f δ → OscB (K.app f) (η * δ)

/-- A pairwise minorisation constant is at most `1`.

DERIVED: `1` the mass of a row. -/
theorem minor_le_one [Nonempty X] {K : Chan X Y} {c : ℝ} (h : Minor K c) : c ≤ 1 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have := h x x
  simpa [ov, min_self, K.sum_one x] using this

/-- **Minorisation contracts.** `Minor K c` gives `Contracts K (1 − c)`.

DERIVED: `1` the mass of a row. -/
theorem contracts_of_minor [Nonempty Y] {K : Chan X Y} {c : ℝ} (hK : Minor K c) :
    Contracts K (1 - c) := by
  intro f δ hf x x'
  have hδ := oscB_nonneg hf
  have ha : ∀ y, 0 ≤ K.P x y - min (K.P x y) (K.P x' y) := fun y => sub_nonneg.2 (min_le_left _ _)
  have hb : ∀ y, 0 ≤ K.P x' y - min (K.P x y) (K.P x' y) :=
    fun y => sub_nonneg.2 (min_le_right _ _)
  have hsa : ∑ y, (K.P x y - min (K.P x y) (K.P x' y)) = 1 - ov (K.P x) (K.P x') := by
    rw [Finset.sum_sub_distrib, K.sum_one]; rfl
  have hsb : ∑ y, (K.P x' y - min (K.P x y) (K.P x' y)) = 1 - ov (K.P x) (K.P x') := by
    rw [Finset.sum_sub_distrib, K.sum_one]; rfl
  have h := two_mass ha hb hsa hsb hf
  have e : K.app f x - K.app f x' = ∑ y, (K.P x y - min (K.P x y) (K.P x' y)) * f y
      - ∑ y, (K.P x' y - min (K.P x y) (K.P x' y)) * f y := by
    simp only [Chan.app, sub_mul, Finset.sum_sub_distrib]; ring
  rw [e]
  calc _ ≤ (1 - ov (K.P x) (K.P x')) * δ := h
    _ ≤ (1 - c) * δ := mul_le_mul_of_nonneg_right (by linarith [hK x x']) hδ

/-- **Full support on a finite alphabet minorises.** Every entry at least `ε` gives
`Minor K (|Y| ε)`. -/
theorem minor_of_floor {K : Chan X Y} {ε : ℝ} (hε : ∀ x y, ε ≤ K.P x y) :
    Minor K (Fintype.card Y * ε) := by
  intro x x'
  unfold ov
  calc (Fintype.card Y : ℝ) * ε = ∑ _y : Y, ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun y _ => le_min (hε x y) (hε x' y)

/-- **The coefficient of a full-support channel.** Every entry at least `ε`:
`Contracts K (1 − |Y| ε)`. -/
theorem contracts_of_floor [Nonempty Y] {K : Chan X Y} {ε : ℝ} (hε : ∀ x y, ε ≤ K.P x y) :
    Contracts K (1 - Fintype.card Y * ε) :=
  contracts_of_minor (minor_of_floor hε)

/-- **A Doeblin floor minorises.** `c ν ≤ P x ·` for a probability vector `ν` gives `Minor K c`. -/
theorem minor_of_doeblin {K : Chan X Y} {c : ℝ} {ν : Y → ℝ} (hν : IsProb ν)
    (h : ∀ x y, c * ν y ≤ K.P x y) : Minor K c := by
  intro x x'
  unfold ov
  calc c = ∑ y, c * ν y := by rw [← Finset.mul_sum, hν.2, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun y _ => le_min (h x y) (h x' y)

/-- **Coefficients multiply along slabs.** -/
theorem contracts_comp {Z : Type*} [Fintype Z] {K : Chan X Y} {L : Chan Y Z} {η₁ η₂ : ℝ}
    (hK : Contracts K η₁) (hL : Contracts L η₂) : Contracts (K.comp L) (η₁ * η₂) := by
  intro f δ hf x x'
  have h := hK _ _ (hL f δ hf) x x'
  rw [Chan.app_comp, Chan.app_comp, mul_assoc]
  exact h

end Coefficient

/-! ### The coefficient is the SDPI coefficient for total variation -/

section SDPI

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The law of the next reading when the current reading has law `μ`. -/
def push (μ : X → ℝ) (K : Chan X Y) (y : Y) : ℝ := ∑ x, μ x * K.P x y

theorem push_prob {μ : X → ℝ} (hμ : IsProb μ) (K : Chan X Y) : IsProb (push μ K) := by
  refine ⟨fun y => Finset.sum_nonneg fun x _ => mul_nonneg (hμ.1 x) (K.nonneg x y), ?_⟩
  unfold push
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, K.sum_one, mul_one]
  exact hμ.2

theorem sum_push (μ : X → ℝ) (K : Chan X Y) (g : Y → ℝ) :
    ∑ y, push μ K y * g y = ∑ x, μ x * K.app g x := by
  simp only [push, Chan.app, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **A test against two laws.** `Σ μ h − Σ ν h ≤ tv(μ, ν) δ` for `h` of oscillation `δ`. -/
theorem test_le [Nonempty Y] {μ ν h : Y → ℝ} {δ : ℝ} (hμ : IsProb μ) (hν : IsProb ν)
    (hh : OscB h δ) : ∑ y, μ y * h y - ∑ y, ν y * h y ≤ tv μ ν * δ := by
  have ha : ∀ y, 0 ≤ μ y - min (μ y) (ν y) := fun y => sub_nonneg.2 (min_le_left _ _)
  have hb : ∀ y, 0 ≤ ν y - min (μ y) (ν y) := fun y => sub_nonneg.2 (min_le_right _ _)
  have hsa : ∑ y, (μ y - min (μ y) (ν y)) = tv μ ν := by rw [Finset.sum_sub_distrib, hμ.2]; rfl
  have hsb : ∑ y, (ν y - min (μ y) (ν y)) = tv μ ν := by rw [Finset.sum_sub_distrib, hν.2]; rfl
  have key := two_mass ha hb hsa hsb hh
  have e : ∑ y, μ y * h y - ∑ y, ν y * h y = ∑ y, (μ y - min (μ y) (ν y)) * h y
      - ∑ y, (ν y - min (μ y) (ν y)) * h y := by
    simp only [sub_mul, Finset.sum_sub_distrib]; ring
  rw [e]; exact key

/-- **Total variation is attained by an indicator test.**

DERIVED: `1` the oscillation of an indicator. -/
theorem tv_eq_test {μ ν : Y → ℝ} (hμ : IsProb μ) :
    ∃ g : Y → ℝ, OscB g 1 ∧ tv μ ν = ∑ y, μ y * g y - ∑ y, ν y * g y := by
  refine ⟨fun y => if ν y < μ y then 1 else 0, fun y y' => by dsimp only; split_ifs <;> norm_num,
    ?_⟩
  have e : tv μ ν = ∑ y, μ y - ov μ ν := by rw [hμ.2]; rfl
  rw [e, ov, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  dsimp only
  split_ifs with h
  · rw [min_eq_right h.le]; ring
  · rw [min_eq_left (not_lt.1 h)]; ring

/-- **Strong data processing for total variation.** `Contracts K η`, `η ≥ 0`:
`tv(μK, νK) ≤ η · tv(μ, ν)`. -/
theorem sdpi_tv [Nonempty X] {K : Chan X Y} {η : ℝ} (hK : Contracts K η) {μ ν : X → ℝ}
    (hμ : IsProb μ) (hν : IsProb ν) : tv (push μ K) (push ν K) ≤ η * tv μ ν := by
  obtain ⟨g, hg, e⟩ := tv_eq_test (ν := push ν K) (push_prob hμ K)
  rw [e, sum_push, sum_push]
  calc _ ≤ tv μ ν * (η * 1) := test_le hμ hν (hK g 1 hg)
    _ = η * tv μ ν := by ring

end SDPI

/-! ## 2. Geometric forgetting along slabs -/

section Forgetting

variable {X : Type*} [Fintype X]

/-- `iter K a n f = K a (K (a+1) (… K (a+n−1) f))`: the conditional expectation, given the reading at
slab `a`, of `f` of the reading at slab `a + n`.

DERIVED: `0`, `1` the recursion. -/
def iter (K : ℕ → Chan X X) : ℕ → ℕ → (X → ℝ) → X → ℝ
  | _, 0, f => f
  | a, n + 1, f => (K a).app (iter K (a + 1) n f)

/-- **Coefficients compose along the slabs.** -/
theorem forget {K : ℕ → Chan X X} {η : ℝ} (hK : ∀ t, Contracts (K t) η) (n : ℕ) :
    ∀ (a : ℕ) (f : X → ℝ) (δ : ℝ), OscB f δ → OscB (iter K a n f) (η ^ n * δ) := by
  induction n with
  | zero => intro a f δ hf; rw [pow_zero, one_mul]; exact hf
  | succ n ih =>
    intro a f δ hf
    have h := hK a _ _ (ih (a + 1) f δ hf)
    rw [pow_succ', mul_assoc]
    exact h

/-- The covariance of `g` and `h` under `μ`. With `h = iter K a n f` and `μ` the law of the reading
at slab `a`, it is the covariance of `g` of the reading at slab `a` with `f` of the reading `n` slabs
later. -/
def cov (μ g h : X → ℝ) : ℝ := ∑ x, μ x * g x * h x - (∑ x, μ x * g x) * (∑ x, μ x * h x)

theorem cov_le [Nonempty X] {μ g h : X → ℝ} {G δ : ℝ} (hμ : IsProb μ) (hg : ∀ x, |g x| ≤ G)
    (hh : OscB h δ) : |cov μ g h| ≤ G * δ := by
  set m := ∑ x, μ x * h x with hm
  have e : cov μ g h = ∑ x, μ x * g x * (h x - m) := by
    simp only [cov, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hm]
  have hd : ∀ x, |h x - m| ≤ δ := by
    intro x
    have ex : h x - m = ∑ y, μ y * (h x - h y) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ.2, one_mul, hm]
    rw [ex, abs_le]
    constructor
    · have := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_left (show -δ ≤ h x - h y by linarith [hh y x]) (hμ.1 y)
      rw [← Finset.sum_mul, hμ.2, one_mul] at this
      linarith
    · have := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_left (hh x y) (hμ.1 y)
      rw [← Finset.sum_mul, hμ.2, one_mul] at this
      linarith
  have hδ := oscB_nonneg hh
  rw [e]
  calc |∑ x, μ x * g x * (h x - m)| ≤ ∑ x, |μ x * g x * (h x - m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, μ x * (G * δ) := Finset.sum_le_sum fun x _ => by
        rw [abs_mul, abs_mul, abs_of_nonneg (hμ.1 x), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hg x) (hd x) (abs_nonneg _) ((abs_nonneg _).trans (hg x))) (hμ.1 x)
    _ = G * δ := by rw [← Finset.sum_mul, hμ.2, one_mul]

/-- **Geometric forgetting.** Slab channels all minorised by `c`: the covariance of a reading at slab
`a` and a reading `n` slabs later is at most `G δ (1 − c)ⁿ`. -/
theorem geometric_forgetting [Nonempty X] {K : ℕ → Chan X X} {c : ℝ} (hK : ∀ t, Minor (K t) c)
    {μ g f : X → ℝ} {G δ : ℝ} (hμ : IsProb μ) (hg : ∀ x, |g x| ≤ G) (hf : OscB f δ) (a n : ℕ) :
    |cov μ g (iter K a n f)| ≤ G * δ * (1 - c) ^ n := by
  have h := cov_le hμ hg (forget (fun t => contracts_of_minor (hK t)) n a f δ hf)
  calc _ ≤ G * ((1 - c) ^ n * δ) := h
    _ = G * δ * (1 - c) ^ n := by ring

/-- **A coefficient below one is a rate in physical units.** `0 < c ≤ 1`, slab length `s > 0`: some
`m > 0` has `(1 − c)ⁿ ≤ e^{−m n s}` for every `n`.

DERIVED: `2` in `c/2`, the midpoint placing the rate strictly below `1`. -/
theorem rate_of_minor {c s : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hs : 0 < s) :
    ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, (1 - c) ^ n ≤ Real.exp (-(m * (n * s))) := by
  have hρ0 : 0 < 1 - c / 2 := by linarith
  have hρ1 : 1 - c / 2 < 1 := by linarith
  have hlog : Real.log (1 - c / 2) < 0 := Real.log_neg hρ0 hρ1
  refine ⟨-Real.log (1 - c / 2) / s, div_pos (by linarith) hs, fun n => ?_⟩
  have e : Real.exp (-(-Real.log (1 - c / 2) / s * (n * s))) = (1 - c / 2) ^ n := by
    rw [show -(-Real.log (1 - c / 2) / s * (n * s)) = n * Real.log (1 - c / 2) by
      field_simp [hs.ne']]
    rw [Real.exp_nat_mul, Real.exp_log hρ0]
  rw [e]
  exact pow_le_pow_left₀ (by linarith) (by linarith) n

/-- **The aperture forgets at one physical mass, uniformly in the zoom.** Slab channels `K k t` on one
fixed finite alphabet, all minorised by one `c > 0` at every zoom `k` and slab `t`, slab length
`s > 0`: there is `m > 0` with `|Cov_k| ≤ G δ e^{−m n s}` at every zoom. -/
theorem aperture_forgetting [Nonempty X] {K : ℕ → ℕ → Chan X X} {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hK : ∀ k t, Minor (K k t) c) :
    ∃ m : ℝ, 0 < m ∧ ∀ (k a n : ℕ) (μ g f : X → ℝ) (G δ : ℝ), IsProb μ → (∀ x, |g x| ≤ G) →
      OscB f δ → |cov μ g (iter (K k) a n f)| ≤ G * δ * Real.exp (-(m * (n * s))) := by
  obtain ⟨m, hm, hr⟩ := rate_of_minor hc (minor_le_one (hK 0 0)) hs
  refine ⟨m, hm, fun k a n μ g f G δ hμ hg hf => ?_⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg x)
  have hδ := oscB_nonneg hf
  calc _ ≤ G * δ * (1 - c) ^ n := geometric_forgetting (hK k) hμ hg hf a n
    _ ≤ _ := mul_le_mul_of_nonneg_left (hr n) (mul_nonneg hG hδ)

end Forgetting

/-! ## 3. The reading chain of `ApertureFixed` -/

section Chain

variable {X : Type} [Fintype X] [MeasurableSpace X]

/-- The measure of a vector on a finite alphabet, `Σ_y p y δ_y`. -/
def toMeas (p : X → ℝ) : Measure X := ∑ y, ENNReal.ofReal (p y) • Measure.dirac y

theorem toMeas_univ (p : X → ℝ) : toMeas p Set.univ = ∑ y, ENNReal.ofReal (p y) := by
  rw [toMeas, Measure.finsetSum_apply]
  simp

theorem toMeas_finite (p : X → ℝ) : IsFiniteMeasure (toMeas p) :=
  ⟨by rw [toMeas_univ]; exact ENNReal.sum_lt_top.2 fun _ _ => ENNReal.ofReal_lt_top⟩

theorem toMeas_real_univ {p : X → ℝ} (hp : ∀ y, 0 ≤ p y) :
    (toMeas p).real Set.univ = ∑ y, p y := by
  rw [measureReal_def, toMeas_univ, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun y _ => ENNReal.toReal_ofReal (hp y)

theorem toMeas_prob {p : X → ℝ} (hp : IsProb p) : IsProbabilityMeasure (toMeas p) :=
  ⟨by rw [toMeas_univ, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp.1 i), hp.2,
    ENNReal.ofReal_one]⟩

theorem toMeas_add {p q : X → ℝ} (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 ≤ q y) :
    toMeas p + toMeas q = toMeas (fun y => p y + q y) := by
  unfold toMeas
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.ofReal_add (hp y) (hq y), add_smul]

variable [DiscreteMeasurableSpace X]

/-- A channel as a kernel. -/
def chanKernel (K : Chan X X) : Kernel X X := ⟨fun x => toMeas (K.P x), Measurable.of_discrete⟩

/-- The kernels of the Markov reading chain: slab `0` has law `ι`; slab `t + 1` has law
`K t (ω t)`, a function of the previous slab's reading only. -/
def kap (K : ℕ → Chan X X) (ι : X → ℝ) : ℕ → Kernel (ℕ → X) X
  | 0 => Kernel.const (ℕ → X) (toMeas ι)
  | t + 1 => Kernel.comap (chanKernel (K t)) (fun ω => ω t) (measurable_pi_apply t)

theorem kap_zero (K : ℕ → Chan X X) (ι : X → ℝ) (ω : ℕ → X) : kap K ι 0 ω = toMeas ι := rfl

theorem kap_succ (K : ℕ → Chan X X) (ι : X → ℝ) (t : ℕ) (ω : ℕ → X) :
    kap K ι (t + 1) ω = toMeas ((K t).P (ω t)) := rfl

/-- **The finite-state Markov reading chain** as an `ApertureFixed.ReadingChain`. -/
def toChain (K : ℕ → Chan X X) {ι : X → ℝ} (hι : IsProb ι) : ReadingChain X where
  κ := kap K ι
  markov t := by
    cases t with
    | zero => exact ⟨fun ω => by rw [kap_zero]; exact toMeas_prob hι⟩
    | succ t => exact ⟨fun ω => by rw [kap_succ]; exact toMeas_prob ((K t).row_prob (ω t))⟩

/-- **A Markov reading chain has no memory beyond the last slab:** `Memory 0 θ` for every `θ`.

DERIVED: `0` the memory amplitude; `1` the mass of a probability measure. -/
theorem toChain_memory (K : ℕ → Chan X X) {ι : X → ℝ} (hι : IsProb ι) (θ : ℝ) :
    (toChain K hι).Memory 0 θ := by
  intro t ℓ hℓ ω ω' hag
  haveI := (toChain K hι).markov t
  have heq : (toChain K hι).κ t ω' = (toChain K hι).κ t ω := by
    cases t with
    | zero => rfl
    | succ t =>
      show kap K ι (t + 1) ω' = kap K ι (t + 1) ω
      rw [kap_succ, kap_succ, hag t (by omega) (by omega)]
  refine ⟨(toChain K hι).κ t ω, 0, 0, inferInstance, inferInstance, inferInstance,
    (add_zero _).symm, by rw [heq, add_zero], ?_⟩
  rw [measureReal_def, measure_univ]
  simp

/-- **A Doeblin floor on the channels gives `ApertureFixed.Doeblin`.** -/
theorem toChain_doeblin (K : ℕ → Chan X X) {ι ν : X → ℝ} (hι : IsProb ι) (hν : IsProb ν) {c : ℝ}
    (hc : 0 ≤ c) (hK : ∀ t x y, c * ν y ≤ (K t).P x y) (hι' : ∀ y, c * ν y ≤ ι y) :
    (toChain K hι).Doeblin c (toMeas (fun y => c * ν y)) := by
  have hcν : ∀ y, 0 ≤ c * ν y := fun y => mul_nonneg hc (hν.1 y)
  refine ⟨toMeas_finite _, ?_, fun t ω => ?_⟩
  · rw [toMeas_real_univ hcν, ← Finset.mul_sum, hν.2, mul_one]
  · cases t with
    | zero =>
      refine ⟨toMeas (fun y => ι y - c * ν y), toMeas_finite _, ?_⟩
      show kap K ι 0 ω = _
      rw [kap_zero, toMeas_add hcν (fun y => sub_nonneg.2 (hι' y))]
      congr 1; funext y; ring
    | succ t =>
      refine ⟨toMeas (fun y => (K t).P (ω t) y - c * ν y), toMeas_finite _, ?_⟩
      show kap K ι (t + 1) ω = _
      rw [kap_succ, toMeas_add hcν (fun y => sub_nonneg.2 (hK t (ω t) y))]
      congr 1; funext y; ring

/-- **A finite-state Markov reading process with a Doeblin floor clusters at a rate fixed by `c`.**
`ApertureFixed.reading_cluster` at memory `(0, 0)`: there is `ρ ∈ (0, 1)`, depending on `c` only,
with `|Cov(g, φ(x_{s+n}))| ≤ 4 G B ρⁿ` for every such chain.

DERIVED: `4` from `reading_cluster`; `0` the memory constants; `1` the slab of `g`. -/
theorem markov_reading_cluster {c : ℝ} (hc : 0 < c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ {X : Type} [Fintype X] [MeasurableSpace X]
      [DiscreteMeasurableSpace X] (K : ℕ → Chan X X) (ι ν : X → ℝ) (hι : IsProb ι), IsProb ν →
      (∀ t x y, c * ν y ≤ (K t).P x y) → (∀ y, c * ν y ≤ ι y) →
      ∀ (s n : ℕ) (g : (ℕ → X) → ℝ) (φ : X → ℝ) (G B : ℝ), BM g → ReadsBelow (s + 1) g →
        (∀ ω, |g ω| ≤ G) → Measurable φ → (∀ x, |φ x| ≤ B) → ∀ ω₀ : ℕ → X,
        |(toChain K hι).seg 0 (s + 1 + n) (fun ω => g ω * φ (ω (s + n))) ω₀
          - (toChain K hι).seg 0 (s + 1 + n) g ω₀
            * (toChain K hι).seg 0 (s + 1 + n) (fun ω => φ (ω (s + n))) ω₀|
          ≤ 4 * G * B * ρ ^ n := by
  obtain ⟨ρ, hρ0, hρ1, hcl⟩ := reading_cluster hc (le_refl 0) (le_refl 0) zero_lt_one
    (by norm_num : (0 : ℝ) * 0 < 1 - 0)
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro X _ _ _ K ι ν hι hν hK hι' s n g φ G B hg hgr hG hφ hB ω₀
  exact hcl (toChain K hι) _ (toChain_doeblin K hι hν hc.le hK hι') (toChain_memory K hι 0)
    s n g φ G B hg hgr hG hφ hB ω₀

end Chain

/-! ## 4. The crux: the substrate passes forward only what the aperture holds -/

section Substrate

variable {Ω X : Type*} [Fintype X]

/-- `T` is non-expansive in the uniform norm (every conditional expectation is). -/
def NonExp (T : (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ (u v : Ω → ℝ) (a : ℝ), (∀ ω, |u ω - v ω| ≤ a) → ∀ ω, |T u ω - T v ω| ≤ a

/-- **What is passed forward is only what the aperture holds (exact).** The conditional expectation
over the next slab, given the whole substrate state, of any test of the next reading is a function of
the present reading only, and equals the finite channel `K` applied to it. -/
def Passes (T : (Ω → ℝ) → Ω → ℝ) (π : Ω → X) (K : Chan X X) : Prop :=
  ∀ f : X → ℝ, T (fun ω => f (π ω)) = fun ω => K.app f (π ω)

/-- **The approximate form.** The same within `ε δ` for tests of oscillation `δ`. -/
def PassesWithin (T : (Ω → ℝ) → Ω → ℝ) (π : Ω → X) (K : Chan X X) (ε : ℝ) : Prop :=
  ∀ (f : X → ℝ) (δ : ℝ), OscB f δ → ∀ ω, |T (fun ω => f (π ω)) ω - K.app f (π ω)| ≤ ε * δ

theorem passesWithin_of_passes {T : (Ω → ℝ) → Ω → ℝ} {π : Ω → X} {K : Chan X X}
    (h : Passes T π K) : PassesWithin T π K 0 := by
  intro f δ _ ω
  rw [h f]; simp

/-- The substrate's `n`-slab conditional expectation, slabs `a, …, a + n − 1`.

DERIVED: `0`, `1` the recursion. -/
def titer (T : ℕ → (Ω → ℝ) → Ω → ℝ) : ℕ → ℕ → (Ω → ℝ) → Ω → ℝ
  | _, 0, u => u
  | a, n + 1, u => T a (titer T (a + 1) n u)

theorem titer_passes {T : ℕ → (Ω → ℝ) → Ω → ℝ} {π : Ω → X} {K : ℕ → Chan X X}
    (hP : ∀ t, Passes (T t) π (K t)) (n : ℕ) :
    ∀ (a : ℕ) (f : X → ℝ), titer T a n (fun ω => f (π ω)) = fun ω => iter K a n f (π ω) := by
  induction n with
  | zero => intro a f; rfl
  | succ n ih =>
    intro a f
    show T a (titer T (a + 1) n (fun ω => f (π ω))) = _
    rw [ih (a + 1) f]
    exact hP a _

/-- **The infinite substrate is forgotten geometrically.** Under `Passes` and `Minor c` at every slab,
the dependence of `f` of the reading `n` slabs ahead on the whole present substrate state is at most
`(1 − c)ⁿ δ`. -/
theorem substrate_forgets [Nonempty X] {T : ℕ → (Ω → ℝ) → Ω → ℝ} {π : Ω → X} {K : ℕ → Chan X X}
    {c : ℝ} (hP : ∀ t, Passes (T t) π (K t)) (hK : ∀ t, Minor (K t) c) {f : X → ℝ} {δ : ℝ}
    (hf : OscB f δ) (a n : ℕ) (ω ω' : Ω) :
    titer T a n (fun ω => f (π ω)) ω - titer T a n (fun ω => f (π ω)) ω' ≤ (1 - c) ^ n * δ := by
  rw [titer_passes hP]
  exact forget (fun t => contracts_of_minor (hK t)) n a f δ hf (π ω) (π ω')

/-- **The approximate step tracks the finite chain to within a geometric sum.** -/
theorem titer_within [Nonempty X] {T : ℕ → (Ω → ℝ) → Ω → ℝ} {π : Ω → X} {K : ℕ → Chan X X}
    {c ε : ℝ} (hT : ∀ t, NonExp (T t)) (hP : ∀ t, PassesWithin (T t) π (K t) ε)
    (hK : ∀ t, Minor (K t) c) {f : X → ℝ} {δ : ℝ} (hf : OscB f δ) (n : ℕ) :
    ∀ (a : ℕ) (ω : Ω), |titer T a n (fun ω => f (π ω)) ω - iter K a n f (π ω)|
      ≤ ε * δ * ∑ j ∈ Finset.range n, (1 - c) ^ j := by
  induction n with
  | zero => intro a ω; simp [titer, iter]
  | succ n ih =>
    intro a ω
    have h1 := hT a (titer T (a + 1) n (fun ω => f (π ω))) (fun ω => iter K (a + 1) n f (π ω))
      _ (ih (a + 1)) ω
    have hw := forget (fun t => contracts_of_minor (hK t)) n (a + 1) f δ hf
    have h2 := hP a (iter K (a + 1) n f) _ hw ω
    show |T a (titer T (a + 1) n (fun ω => f (π ω))) ω - (K a).app (iter K (a + 1) n f) (π ω)| ≤ _
    rw [Finset.sum_range_succ]
    calc _ ≤ |T a (titer T (a + 1) n (fun ω => f (π ω))) ω
              - T a (fun ω => iter K (a + 1) n f (π ω)) ω|
            + |T a (fun ω => iter K (a + 1) n f (π ω)) ω - (K a).app (iter K (a + 1) n f) (π ω)| :=
          abs_sub_le _ _ _
      _ ≤ ε * δ * ∑ j ∈ Finset.range n, (1 - c) ^ j + ε * ((1 - c) ^ n * δ) := add_le_add h1 h2
      _ = _ := by ring

/-- **An approximate step forgets down to a floor.** `PassesWithin ε` (with `T` non-expansive) and
`Minor c`, `c > 0`, `ε ≥ 0`: the dependence of `f` of the reading `n` slabs ahead on the whole present
substrate state is at most `(1 − c)ⁿ δ + 2 ε δ / c`.

DERIVED: `2` the two substrate states compared. -/
theorem substrate_forgets_to_floor [Nonempty X] {T : ℕ → (Ω → ℝ) → Ω → ℝ} {π : Ω → X}
    {K : ℕ → Chan X X} {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) (hT : ∀ t, NonExp (T t))
    (hP : ∀ t, PassesWithin (T t) π (K t) ε) (hK : ∀ t, Minor (K t) c) {f : X → ℝ} {δ : ℝ}
    (hf : OscB f δ) (a n : ℕ) (ω ω' : Ω) :
    titer T a n (fun ω => f (π ω)) ω - titer T a n (fun ω => f (π ω)) ω'
      ≤ (1 - c) ^ n * δ + 2 * ε * δ / c := by
  have hδ := oscB_nonneg hf
  have A := titer_within hT hP hK hf n a ω
  have B := titer_within hT hP hK hf n a ω'
  have C := forget (fun t => contracts_of_minor (hK t)) n a f δ hf (π ω) (π ω')
  have hS : (∑ j ∈ Finset.range n, (1 - c) ^ j) * c ≤ 1 := by
    have g := geom_sum_mul (1 - c) n
    have hp : 0 ≤ (1 - c) ^ n :=
      pow_nonneg (by linarith [minor_le_one (hK 0)]) n
    nlinarith
  have hS' : ε * δ * ∑ j ∈ Finset.range n, (1 - c) ^ j ≤ ε * δ / c := by
    rw [le_div_iff₀ hc, mul_assoc]
    calc ε * δ * ((∑ j ∈ Finset.range n, (1 - c) ^ j) * c) ≤ ε * δ * 1 :=
          mul_le_mul_of_nonneg_left hS (mul_nonneg hε hδ)
      _ = ε * δ := mul_one _
  rw [abs_le] at A B
  have e : 2 * ε * δ / c = ε * δ / c + ε * δ / c := by ring
  linarith [A.1, A.2, B.1, B.2]

/-! ### The floor is attained: a hidden bit that the substrate keeps -/

/-- The tilt of the reading toward the hidden bit: `(1 + ε)/2` on the bit's own letter.

DERIVED: `1/2` the uniform law on two letters; `ε/2` the tilt. -/
def tilt (ε : ℝ) (h r : Bool) : ℝ := if r = h then (1 + ε) / 2 else (1 - ε) / 2

/-- The substrate slab: state `(reading, hidden bit)`; the next reading is drawn with the tilt, the
bit is kept. -/
def Tbit (ε : ℝ) (u : Bool × Bool → ℝ) (ω : Bool × Bool) : ℝ :=
  tilt ε ω.2 true * u (true, ω.2) + tilt ε ω.2 false * u (false, ω.2)

/-- The uniform channel on two letters: its rows coincide, so `Minor 1`.

DERIVED: `1/2` the uniform law on two letters. -/
def uniform2 : Chan Bool Bool where
  P _ _ := 1 / 2
  nonneg _ _ := by norm_num
  sum_one _ := by rw [Fintype.sum_bool]; norm_num

theorem tilt_sum (ε : ℝ) (h : Bool) : tilt ε h true + tilt ε h false = 1 := by
  cases h <;> simp [tilt] <;> ring

/-- **The floor of `substrate_forgets_to_floor` is attained.** For `0 ≤ ε ≤ 1` the hidden-bit
substrate is non-expansive, passes the uniform channel within `ε/2`, the uniform channel has
`Minor 1`, and at every `n ≥ 1` the indicator of the letter `true` read `n` slabs ahead differs by
exactly `ε` between the two values of the hidden bit: `ε = 2 (ε/2) · 1 / 1`, the floor, never
squeezed out.

DERIVED: `1/2` the uniform law; `2` the two substrate states; `1` the indicator's oscillation and the
minorisation of the uniform channel. -/
theorem floor_attained {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (NonExp (Tbit ε)) ∧ PassesWithin (Tbit ε) Prod.fst uniform2 (ε / 2) ∧ Minor uniform2 1 ∧
      OscB (fun r : Bool => if r then (1 : ℝ) else 0) 1 ∧
      ∀ (a n : ℕ), titer (fun _ => Tbit ε) a (n + 1)
          (fun ω => (fun r : Bool => if r then (1 : ℝ) else 0) ω.1) (true, true)
        - titer (fun _ => Tbit ε) a (n + 1)
          (fun ω => (fun r : Bool => if r then (1 : ℝ) else 0) ω.1) (true, false) = ε := by
  have ht0 : ∀ h r, 0 ≤ tilt ε h r := fun h r => by
    unfold tilt; split_ifs <;> linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v a hu ω
    have e : Tbit ε u ω - Tbit ε v ω = tilt ε ω.2 true * (u (true, ω.2) - v (true, ω.2))
        + tilt ε ω.2 false * (u (false, ω.2) - v (false, ω.2)) := by unfold Tbit; ring
    rw [e]
    calc _ ≤ |tilt ε ω.2 true * (u (true, ω.2) - v (true, ω.2))|
            + |tilt ε ω.2 false * (u (false, ω.2) - v (false, ω.2))| := abs_add_le _ _
      _ ≤ tilt ε ω.2 true * a + tilt ε ω.2 false * a := by
          rw [abs_mul, abs_mul, abs_of_nonneg (ht0 _ _), abs_of_nonneg (ht0 _ _)]
          exact add_le_add (mul_le_mul_of_nonneg_left (hu _) (ht0 _ _))
            (mul_le_mul_of_nonneg_left (hu _) (ht0 _ _))
      _ = a := by rw [← add_mul, tilt_sum, one_mul]
  · intro f δ hf ω
    have e : Tbit ε (fun ω => f ω.1) ω - uniform2.app f ω.1
        = (ε / 2) * (if ω.2 = true then f true - f false else f false - f true) := by
      unfold Tbit Chan.app uniform2 tilt
      rw [Fintype.sum_bool]
      cases ω.2 <;> simp <;> ring
    rw [e, abs_mul, abs_of_nonneg (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    split_ifs
    · rw [abs_le]; constructor <;> linarith [hf true false, hf false true]
    · rw [abs_le]; constructor <;> linarith [hf true false, hf false true]
  · intro x x'
    simp [ov, uniform2]
  · intro y y'; cases y <;> cases y' <;> norm_num
  · have hkeep : ∀ g : Bool → ℝ, Tbit ε (fun ω => g ω.2) = fun ω => g ω.2 := by
      intro g; funext ω
      unfold Tbit
      rw [← add_mul, tilt_sum, one_mul]
    have hone : ∀ (n a : ℕ), titer (fun _ => Tbit ε) a (n + 1)
        (fun ω => (fun r : Bool => if r then (1 : ℝ) else 0) ω.1)
        = fun ω => tilt ε ω.2 true := by
      intro n
      induction n with
      | zero =>
        intro a; funext ω
        show Tbit ε _ ω = _
        simp [Tbit, titer]
      | succ n ih =>
        intro a
        show Tbit ε (titer (fun _ => Tbit ε) (a + 1) (n + 1) _) = _
        rw [ih (a + 1)]
        exact hkeep (fun h => tilt ε h true)
    intro a n
    rw [hone n a]
    simp [tilt]
    ring

end Substrate

/-! ## 5. The step for an aperture family, and what it asks of Yang–Mills -/

/-- **A finite aperture on a substrate, one per zoom.** A fixed finite alphabet `X` (cells × finite
precision), a fixed slab length; at zoom `k` the substrate states `Ω k` (no size restriction), the
aperture's reading `π k`, the substrate's slab operators `T k t` and the finite slab channels `K k t`.
`X` and `slab` carry no zoom index. -/
structure FiniteAperture where
  /-- The finite alphabet of one slab's readings. -/
  X : Type
  [fX : Fintype X]
  [nX : Nonempty X]
  /-- The physical slab length. -/
  slab : ℝ
  slab_pos : 0 < slab
  /-- The substrate states at zoom `k`. -/
  Ω : ℕ → Type
  /-- What the aperture reads. -/
  π : ∀ k, Ω k → X
  /-- One slab of the substrate at zoom `k`: the conditional expectation over the next slab. -/
  T : ∀ k, ℕ → (Ω k → ℝ) → Ω k → ℝ
  /-- The finite slab channels. -/
  K : ℕ → ℕ → Chan X X

attribute [instance] FiniteAperture.fX FiniteAperture.nX

/-- **The finite-information step.** At every zoom and slab, what is passed forward is only what the
aperture holds (`Passes`), through a channel minorised by one `c > 0`. This is the assumption on the
substrate that the step makes. -/
def FiniteInformationStep (A : FiniteAperture) (c : ℝ) : Prop :=
  0 < c ∧ ∀ k t, Passes (A.T k t) (A.π k) (A.K k t) ∧ Minor (A.K k t) c

/-- **The finite-information step gives one physical mass, uniformly in the zoom.** There is `m > 0`
such that, at every zoom, the dependence of any reading test (oscillation `δ`) `n` slabs ahead on the
whole present substrate state is at most `δ e^{−m n · slab}`. -/
theorem finite_information_mass (A : FiniteAperture) {c : ℝ} (h : FiniteInformationStep A c) :
    ∃ m : ℝ, 0 < m ∧ ∀ (k a n : ℕ) (f : A.X → ℝ) (δ : ℝ), OscB f δ → ∀ ω ω' : A.Ω k,
      titer (A.T k) a n (fun ω => f (A.π k ω)) ω - titer (A.T k) a n (fun ω => f (A.π k ω)) ω'
        ≤ δ * Real.exp (-(m * (n * A.slab))) := by
  obtain ⟨hc, hall⟩ := h
  obtain ⟨m, hm, hr⟩ := rate_of_minor hc (minor_le_one (hall 0 0).2) A.slab_pos
  refine ⟨m, hm, fun k a n f δ hf ω ω' => ?_⟩
  have hδ := oscB_nonneg hf
  calc _ ≤ (1 - c) ^ n * δ :=
        substrate_forgets (fun t => (hall k t).1) (fun t => (hall k t).2) hf a n ω ω'
    _ ≤ Real.exp (-(m * (n * A.slab))) * δ := mul_le_mul_of_nonneg_right (hr n) hδ
    _ = _ := mul_comm _ _

end MassGap.FiniteInformation

#print axioms MassGap.FiniteInformation.contracts_of_minor
#print axioms MassGap.FiniteInformation.contracts_of_floor
#print axioms MassGap.FiniteInformation.contracts_comp
#print axioms MassGap.FiniteInformation.sdpi_tv
#print axioms MassGap.FiniteInformation.geometric_forgetting
#print axioms MassGap.FiniteInformation.aperture_forgetting
#print axioms MassGap.FiniteInformation.toChain_memory
#print axioms MassGap.FiniteInformation.toChain_doeblin
#print axioms MassGap.FiniteInformation.markov_reading_cluster
#print axioms MassGap.FiniteInformation.substrate_forgets
#print axioms MassGap.FiniteInformation.substrate_forgets_to_floor
#print axioms MassGap.FiniteInformation.floor_attained
#print axioms MassGap.FiniteInformation.finite_information_mass
