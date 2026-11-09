import Mathlib
import MassGap.BoxDobrushinSpatial

noncomputable section

/-!
# MassGap.DobrushinGeneral — Dobrushin's theorem for a general finite specification

`BoxDobrushinCoupling` and `BoxDobrushinSpatial` prove the oscillation step, the sweep contraction,
uniqueness and spatial covariance decay for the heat baths `wAvg Φ` of a positive continuous weight
`Φ`. Those proofs read only five properties of the single-link kernels and two of the state. This
module states the five properties as a structure and proves the same results from them alone.

1. **A finite specification** (`Spec`). On the configurations `Lk → SU(N)` of a finite set of links,
   one kernel `P l` per link, acting on real functions: it maps continuous functions to continuous
   functions (Feller), is linear and unital, is monotone on each fibre `{W[l ↦ g] : g}` (so `P l f W`
   reads `f` only on the fibre of `W`), and does not read the variable at `l`. These are the
   properties of `f ↦ ∫ f(W[l ↦ g]) γ_l(dg | W)` for a weakly continuous probability kernel `γ_l`
   that does not read `l`.
2. **The total-variation influence** (`SInfl`). `C l k` bounds, for `k ≠ l`, the change of the
   `P l`-mean of every continuous `[0, 1]`-valued function of the variable at `l` when the variable at
   `k` changes. For probability measures on the compact metric group this supremum over continuous
   `[0, 1]` test functions is the total-variation distance, so `C` is Dobrushin's matrix
   `sup TV(γ_l(·|ω), γ_l(·|ω'))` over neighbourhoods differing at `k`.
3. **Invariance** (`Invariant`). A state `σ` on the continuous observables with `σ(P l f) = σ f` for
   every `l` and continuous `f`: `σ` is consistent with the specification (DLR at one link).
4. **The results** (`osc_stepS`, `osc_runS`, `osc_sweep_fullS`, `sweep_mixingS`,
   `state_unique_of_inflS`, `sweep_to_stateS`, `cov_stepS`, `cov_runS`, `cov_le_weightedS`,
   `cov_spatialS`). With `C ≥ 0` of row sums `≤ α < 1`: a sweep contracts total oscillation by `α`,
   two invariant states agree, sweeps converge to the invariant state at rate `αⁿ`, and for `g` read on
   `B` and `f` read off the `d`-step influence neighbourhood `reach C B d`,
   `|σ(f g) − σ f σ g| ≤ V_g θ/(θ − α) · θ^{d+1} Σ v_f` for every `θ ∈ (α, 1]`.
5. **The heat bath is an instance** (`heatSpec`, `sInfl_heat`, `invariant_gibbs`): the heat baths of
   any positive continuous weight form a specification, `Infl Φ C` is `SInfl (heatSpec) C`, and the
   Gibbs state is invariant.

## Scope

The covariance step uses the state only through invariance (`ex_P`) and the specification only
through the five fields: detailed balance is derived (`pull`: a factor not reading `l` leaves the
kernel), not assumed. Nothing here assumes the state is a Gibbs state of a weight.
-/

namespace MassGap.DobrushinGeneral

open MeasureTheory Filter Topology
open MassGap.SUN (SU)
open MassGap.CompactGauge (probHaar)
open MassGap.HeatBath (exists_abs_le)
open MassGap.WeightedHeatBath (wAvg wNum wPart wPart_pos wAvg_update wAvg_of_readsNot
  continuous_wAvg)
open MassGap.WeightedTorus (wAvg_add wAvg_const_mul)
open MassGap.BoxDobrushinCoupling (OscLe Infl oscStep gibbsState gibbsState_invariant
  abs_sub_le_sum_osc integrable_cont oscLe_of_continuous)
open MassGap.BoxDobrushinSpatial (oscRun oscCost cost_le reach level level_loc level_of_mem
  level_far rep oscStep_nonneg)

variable {N : ℕ}

/-! ## 0. Continuity in pointwise form -/

section Cont

variable {X : Type} [TopologicalSpace X]

/-- Product in pointwise form. DERIVED: no numeral. -/
theorem cmul {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x * g x) := hf.mul hg

#print axioms cmul

/-- Scalar multiple in pointwise form. DERIVED: no numeral. -/
theorem csmul (c : ℝ) {f : X → ℝ} (hf : Continuous f) : Continuous (fun x => c * f x) :=
  continuous_const.mul hf

#print axioms csmul

/-- Sum in pointwise form. DERIVED: no numeral. -/
theorem cadd {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := hf.add hg

#print axioms cadd

/-- Difference in pointwise form. DERIVED: no numeral. -/
theorem csub {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x - g x) := hf.sub hg

#print axioms csub

/-- Adding a constant in pointwise form. DERIVED: no numeral. -/
theorem caddc {f : X → ℝ} (hf : Continuous f) (c : ℝ) : Continuous (fun x => f x + c) :=
  hf.add continuous_const

#print axioms caddc

/-- Subtracting a constant in pointwise form. DERIVED: no numeral. -/
theorem csubc {f : X → ℝ} (hf : Continuous f) (c : ℝ) : Continuous (fun x => f x - c) :=
  hf.sub continuous_const

#print axioms csubc

end Cont

/-! ## 1. Finite specifications -/

section Spec

/-- **A finite specification on `Lk → SU(N)`**: a kernel `P l` per link that is Feller, linear,
unital, monotone on the fibre of `l`, and does not read the variable at `l`.

DERIVED: `1` is the constant function and its mean. -/
structure Spec (N : ℕ) (Lk : Type) [DecidableEq Lk] where
  /-- The kernel at `l`, acting on real functions of the configuration. -/
  P : Lk → ((Lk → SU N) → ℝ) → (Lk → SU N) → ℝ
  /-- Feller: continuous functions go to continuous functions. -/
  cont : ∀ (l : Lk) {f : (Lk → SU N) → ℝ}, Continuous f → Continuous (P l f)
  /-- Linear on continuous functions. -/
  lin : ∀ (l : Lk) {f f' : (Lk → SU N) → ℝ}, Continuous f → Continuous f' → ∀ (a b : ℝ)
    (W : Lk → SU N), P l (fun V => a * f V + b * f' V) W = a * P l f W + b * P l f' W
  /-- Unital. DERIVED: `1` the constant function and its mean. -/
  one : ∀ (l : Lk) (W : Lk → SU N), P l (fun _ => 1) W = 1
  /-- Monotone on the fibre of `l` at `W`. -/
  mono : ∀ (l : Lk) {f f' : (Lk → SU N) → ℝ}, Continuous f → Continuous f' → ∀ W : Lk → SU N,
    (∀ g, f (Function.update W l g) ≤ f' (Function.update W l g)) → P l f W ≤ P l f' W
  /-- The kernel at `l` does not read the variable at `l`. -/
  upd : ∀ (l : Lk) (f : (Lk → SU N) → ℝ) (W : Lk → SU N) (x : SU N),
    P l f (Function.update W l x) = P l f W

namespace Spec

variable {Lk : Type} [DecidableEq Lk] (S : Spec N Lk)

/-- **The kernel reads `f` only on the fibre of `l`.**

DERIVED: no numeral. -/
theorem fibre_eq (l : Lk) {f f' : (Lk → SU N) → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (W : Lk → SU N) (e : ∀ g, f (Function.update W l g) = f' (Function.update W l g)) :
    S.P l f W = S.P l f' W :=
  le_antisymm (S.mono l hf hf' W fun g => (e g).le) (S.mono l hf' hf W fun g => (e g).ge)

#print axioms fibre_eq

/-- Constants are fixed.

DERIVED: `0`, `1` the coefficients used in `lin`. -/
theorem const (l : Lk) (c : ℝ) (W : Lk → SU N) : S.P l (fun _ => c) W = c := by
  have h := S.lin l (f := fun _ => (1 : ℝ)) (f' := fun _ => (1 : ℝ)) continuous_const
    continuous_const c 0 W
  simp only [S.one, mul_one, zero_mul, add_zero] at h
  exact h

#print axioms const

/-- Adding a constant commutes with the kernel.

DERIVED: `1` the coefficient and the constant function. -/
theorem add_const (l : Lk) {F : (Lk → SU N) → ℝ} (hF : Continuous F) (c : ℝ) (W : Lk → SU N) :
    S.P l (fun V => F V + c) W = S.P l F W + c := by
  have h := S.lin l (f' := fun _ => (1 : ℝ)) hF continuous_const 1 c W
  simp only [S.one, one_mul, mul_one] at h
  exact h

#print axioms add_const

/-- The kernel of an affine function of `h`.

DERIVED: `1` the constant function. -/
theorem affine (l : Lk) {h : (Lk → SU N) → ℝ} (hh : Continuous h) (a b : ℝ) (W : Lk → SU N) :
    S.P l (fun V => a + b * h V) W = a + b * S.P l h W := by
  have e := S.lin l (f := fun _ => (1 : ℝ)) continuous_const hh a b W
  simp only [S.one, mul_one] at e
  exact e

#print axioms affine

/-- Linear combination plus a constant.

DERIVED: no numeral. -/
theorem lin_const (l : Lk) {f f' : (Lk → SU N) → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (a b c : ℝ) (W : Lk → SU N) :
    S.P l (fun V => a * f V + b * f' V + c) W = a * S.P l f W + b * S.P l f' W + c := by
  rw [S.add_const l (F := fun V => a * f V + b * f' V)
    (cadd (csmul a hf) (csmul b hf')) c W, S.lin l hf hf' a b W]

#print axioms lin_const

/-- **The kernel is a normalised average on the fibre**: functions within `c` of each other on the
fibre of `l` at `W` have kernel means within `c`.

DERIVED: no numeral. -/
theorem sub_le (l : Lk) {f f' : (Lk → SU N) → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (W : Lk → SU N) {c : ℝ}
    (hc : ∀ g, |f (Function.update W l g) - f' (Function.update W l g)| ≤ c) :
    |S.P l f W - S.P l f' W| ≤ c := by
  have h1 := S.mono l hf (caddc hf' c) W (f' := fun V => f' V + c)
    (fun g => by
      show f (Function.update W l g) ≤ f' (Function.update W l g) + c
      linarith [(abs_le.mp (hc g)).2])
  have h2 := S.mono l hf' (caddc hf c) W (f' := fun V => f V + c)
    (fun g => by
      show f' (Function.update W l g) ≤ f (Function.update W l g) + c
      linarith [(abs_le.mp (hc g)).1])
  rw [S.add_const l hf' c W] at h1
  rw [S.add_const l hf c W] at h2
  rw [abs_le]
  constructor <;> linarith

#print axioms sub_le

/-- **A factor not reading `l` comes out of the kernel** (pull-out, from `fibre_eq` and `lin`).

DERIVED: `0` the second coefficient. -/
theorem pull (l : Lk) {a f : (Lk → SU N) → ℝ} (ha : Continuous a) (hf : Continuous f)
    (har : ∀ V g, a (Function.update V l g) = a V) (W : Lk → SU N) :
    S.P l (fun V => a V * f V) W = a W * S.P l f W := by
  have e := S.fibre_eq l (cmul ha hf) (f' := fun V => a W * f V + 0 * f V)
    (cadd (csmul (a W) hf) (csmul 0 hf)) W (fun g => by
      show a (Function.update W l g) * f (Function.update W l g)
        = a W * f (Function.update W l g) + 0 * f (Function.update W l g)
      rw [har]; ring)
  rw [e, S.lin l hf hf (a W) 0 W]
  ring

#print axioms pull

/-- **A function not reading `l` is fixed.**

DERIVED: no numeral. -/
theorem fix (l : Lk) {f : (Lk → SU N) → ℝ} (hf : Continuous f)
    (hr : ∀ V g, f (Function.update V l g) = f V) (W : Lk → SU N) : S.P l f W = f W := by
  rw [S.fibre_eq l hf continuous_const W (f' := fun _ => f W) (fun g => hr W g), S.const]

#print axioms fix

/-- **A kernel moves an observable by at most its oscillation at that link.**

DERIVED: no numeral. -/
theorem abs_sub_P_le (l : Lk) {f : (Lk → SU N) → ℝ} (hf : Continuous f) {v : Lk → ℝ}
    (hv : OscLe f v) (W : Lk → SU N) : |f W - S.P l f W| ≤ v l := by
  have h := S.sub_le l (f := fun _ => f W) continuous_const hf W (c := v l) (fun g => by
    show |f W - f (Function.update W l g)| ≤ v l
    rw [abs_sub_comm]
    exact hv W l g)
  rwa [S.const] at h

#print axioms abs_sub_P_le

/-- **The conditional covariance at one link**: `|P(f g) − P f · P g| ≤ v_f(l) v_g(l)`.

DERIVED: no numeral. -/
theorem condCov_le (l : Lk) {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {vf vg : Lk → ℝ} (hvf : OscLe f vf) (hvg : OscLe g vg) (W : Lk → SU N) :
    |S.P l (fun V => f V * g V) W - S.P l f W * S.P l g W| ≤ vf l * vg l := by
  obtain ⟨a, ha⟩ : ∃ a, a = S.P l f W := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = S.P l g W := ⟨_, rfl⟩
  have hfib : ∀ (F : (Lk → SU N) → ℝ), Continuous F → ∀ {u : Lk → ℝ}, OscLe F u → ∀ x,
      |F (Function.update W l x) - S.P l F W| ≤ u l := fun F hF u hu x => by
    have h := S.abs_sub_P_le l hF hu (Function.update W l x)
    rwa [S.upd] at h
  have hs := S.sub_le l (cmul hf hg) (f' := fun V => b * f V + a * g V + -(a * b))
    (caddc (cadd (csmul b hf) (csmul a hg)) (-(a * b))) W
    (c := vf l * vg l) (fun x => by
      show |f (Function.update W l x) * g (Function.update W l x)
        - (b * f (Function.update W l x) + a * g (Function.update W l x) + -(a * b))| ≤ vf l * vg l
      have e : f (Function.update W l x) * g (Function.update W l x)
          - (b * f (Function.update W l x) + a * g (Function.update W l x) + -(a * b))
          = (f (Function.update W l x) - a) * (g (Function.update W l x) - b) := by ring
      rw [e, abs_mul]
      have h1 := hfib f hf hvf x
      have h2 := hfib g hg hvg x
      rw [← ha] at h1
      rw [← hb] at h2
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  rw [S.lin_const l hf hg b a (-(a * b)) W, ← ha, ← hb] at hs
  have e : b * a + a * b + -(a * b) = a * b := by ring
  rw [e] at hs
  rw [← ha, ← hb]
  exact hs

#print axioms condCov_le

end Spec

variable {Lk : Type} [DecidableEq Lk]

/-- **The total-variation influence matrix of a specification**: changing the link `k ≠ l` moves
the `P l`-mean of every continuous `[0, 1]`-valued function of the variable at `l` by at most
`C l k`. On a compact metric group the supremum over these test functions is the total-variation
distance of the two single-link conditional laws.

DERIVED: `0`, `1` the range of the test functions. -/
def SInfl (S : Spec N Lk) (C : Lk → Lk → ℝ) : Prop :=
  ∀ l k, l ≠ k → ∀ (W : Lk → SU N) (x : SU N) (φ : SU N → ℝ), Continuous φ → (∀ e, 0 ≤ φ e) →
    (∀ e, φ e ≤ 1) →
    |S.P l (fun V => φ (V l)) (Function.update W k x) - S.P l (fun V => φ (V l)) W| ≤ C l k

/-- **Dobrushin's comparison for a general specification (Föllmer's step).** If `v` bounds the
single-link oscillations of a continuous `f` and `C` is a TV influence matrix of `S`, then
`oscStep C l v` bounds those of `P l f`.

DERIVED: `0` the sign of `C` and the oscillation at `l`; `1` the range of the rescaled fibre
function. -/
theorem osc_stepS {S : Spec N Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) {f : (Lk → SU N) → ℝ}
    (hf : Continuous f) {v : Lk → ℝ} (hv : OscLe f v) (l : Lk) :
    OscLe (S.P l f) (oscStep C l v) := by
  intro W k x
  unfold oscStep
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, S.upd, sub_self, abs_zero]
  rw [if_neg hkl]
  have hlk : l ≠ k := Ne.symm hkl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SU N → ℝ, ∀ g, ψ g = f (Function.update W l g) := ⟨_, fun _ => rfl⟩
  have hu : Continuous (fun g : SU N => Function.update W l g) :=
    continuous_const.update l continuous_id
  have hψc : Continuous ψ := by
    have : ψ = fun g => f (Function.update W l g) := funext hψ
    rw [this]; exact hf.comp hu
  have hF : Continuous (fun V : Lk → SU N => ψ (V l)) := hψc.comp (continuous_apply l)
  have s1 : |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) (Function.update W k x)|
      ≤ v k := by
    refine S.sub_le l hf hF _ fun g => ?_
    show |f (Function.update (Function.update W k x) l g)
      - ψ (Function.update (Function.update W k x) l g l)| ≤ v k
    rw [Function.update_self, hψ, Function.update_comm hkl x g W]
    exact hv _ k x
  have s0 : S.P l (fun V => ψ (V l)) W = S.P l f W :=
    S.fibre_eq l hF hf W fun g => by
      show ψ (Function.update W l g l) = f (Function.update W l g)
      rw [Function.update_self, hψ]
  obtain ⟨g0, -, hg0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hψc.continuousOn
  have hmin : ∀ g, ψ g0 ≤ ψ g := fun g => hg0 (Set.mem_univ g)
  have hrng : ∀ g, ψ g - ψ g0 ≤ v l := fun g => by
    have h := hv (Function.update W l g0) l g
    rw [Function.update_idem, ← hψ, ← hψ] at h
    exact (le_abs_self _).trans h
  have hvl : 0 ≤ v l := hv.nonneg l
  have hC0 : 0 ≤ C l k := by
    have h := hC l k hlk W x (fun _ => 0) continuous_const (fun _ => le_rfl)
      (fun _ => zero_le_one)
    exact (abs_nonneg _).trans h
  have s2 : |S.P l (fun V => ψ (V l)) (Function.update W k x) - S.P l (fun V => ψ (V l)) W|
      ≤ C l k * v l := by
    rcases hvl.eq_or_lt with h0 | hpos'
    · have hconst : ∀ g, ψ g = ψ g0 := fun g => le_antisymm (by linarith [hrng g]) (hmin g)
      have e : (fun V : Lk → SU N => ψ (V l)) = fun V => ψ g0 + 0 * ψ (V l) := by
        funext V; rw [hconst]; ring
      rw [e, S.affine l hF, S.affine l hF]
      simp only [zero_mul, add_zero, sub_self, abs_zero]
      exact mul_nonneg hC0 hvl
    · obtain ⟨φ, hφ⟩ : ∃ φ : SU N → ℝ, ∀ g, φ g = (ψ g - ψ g0) / v l := ⟨_, fun _ => rfl⟩
      have hφc : Continuous φ := by
        have : φ = fun g => (ψ g - ψ g0) / v l := funext hφ
        rw [this]; exact (hψc.sub continuous_const).div_const _
      have hφ0 : ∀ g, 0 ≤ φ g := fun g => by
        rw [hφ]; exact div_nonneg (by linarith [hmin g]) hvl
      have hφ1 : ∀ g, φ g ≤ 1 := fun g => by
        rw [hφ, div_le_one hpos']; exact hrng g
      have e : (fun V : Lk → SU N => ψ (V l)) = fun V => ψ g0 + v l * φ (V l) := by
        funext V; rw [hφ]; field_simp; ring
      have hφF : Continuous (fun V : Lk → SU N => φ (V l)) := hφc.comp (continuous_apply l)
      rw [e, S.affine l hφF, S.affine l hφF]
      have h := hC l k hlk W x φ hφc hφ0 hφ1
      rw [show ψ g0 + v l * S.P l (fun V => φ (V l)) (Function.update W k x)
          - (ψ g0 + v l * S.P l (fun V => φ (V l)) W)
          = v l * (S.P l (fun V => φ (V l)) (Function.update W k x)
            - S.P l (fun V => φ (V l)) W) by ring, abs_mul, abs_of_nonneg hvl]
      nlinarith
  rw [← s0]
  calc |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) W|
      ≤ |S.P l f (Function.update W k x) - S.P l (fun V => ψ (V l)) (Function.update W k x)|
        + |S.P l (fun V => ψ (V l)) (Function.update W k x) - S.P l (fun V => ψ (V l)) W| :=
        abs_sub_le _ _ _
    _ ≤ v k + C l k * v l := by linarith

#print axioms osc_stepS

end Spec

/-! ## 2. Sweeps: contraction, mixing, uniqueness -/

section Sweep

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **The sweep along a list of links**: the kernels at the links of `L`, in order. -/
def sweepS (S : Spec N Lk) : List Lk → ((Lk → SU N) → ℝ) → ((Lk → SU N) → ℝ)
  | [], f => f
  | l :: L, f => sweepS S L (S.P l f)

omit [Fintype Lk] in
/-- A sweep keeps continuity.

DERIVED: no numeral. -/
theorem continuous_sweepS (S : Spec N Lk) :
    ∀ (L : List Lk) {f : (Lk → SU N) → ℝ}, Continuous f → Continuous (sweepS S L f)
  | [], _, hf => hf
  | l :: L, _, hf => continuous_sweepS S L (S.cont l hf)

#print axioms continuous_sweepS

omit [Fintype Lk] in
/-- **The vector form**: along any list, `oscRun C L v` bounds the oscillations of the swept
observable (`osc_stepS` at each step).

DERIVED: no numeral. -/
theorem osc_runS {S : Spec N Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) :
    ∀ (L : List Lk) {f : (Lk → SU N) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
      OscLe (sweepS S L f) (oscRun C L v)
  | [], _, _, _, hv => hv
  | l :: L, _, hf, _, hv => osc_runS hC L (S.cont l hf) (osc_stepS hC hf hv l)

#print axioms osc_runS

/-- **The oscillation budget along a sweep** (as `BoxDobrushinCoupling.osc_sweep`, for a general
specification).

DERIVED: `0` the sign; `1` the bound on `α`. -/
theorem osc_sweepS {S : Spec N Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k)
    {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) (v : Lk → ℝ) :
    ∀ (L : List Lk) (T : Finset Lk) (f : (Lk → SU N) → ℝ) (u : Lk → ℝ), Continuous f →
      OscLe f u → (∀ k ∉ T, v k ≤ u k) → ∑ k, u k ≤ α * ∑ k ∈ T, v k + ∑ k ∈ Tᶜ, v k →
      ∃ u' : Lk → ℝ, OscLe (sweepS S L f) u' ∧ (∀ k ∉ T ∪ L.toFinset, v k ≤ u' k) ∧
        ∑ k, u' k ≤ α * ∑ k ∈ T ∪ L.toFinset, v k + ∑ k ∈ (T ∪ L.toFinset)ᶜ, v k
  | [], T, f, u, _, hu, hS, hsum => ⟨u, hu, by simpa using hS, by simpa using hsum⟩
  | l :: L, T, f, u, hf, hu, hS, hsum => by
    have hu0 : ∀ k, 0 ≤ u k := hu.nonneg
    set u1 := oscStep C l u with hu1
    have hosc : OscLe (S.P l f) u1 := osc_stepS hC hf hu l
    have hS1 : ∀ k ∉ insert l T, v k ≤ u1 k := fun k hk => by
      have hkl : k ≠ l := fun h => hk (h ▸ Finset.mem_insert_self l T)
      have hkS : k ∉ T := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hu1, oscStep, if_neg hkl]
      have := mul_nonneg (hC0 l k) (hu0 l)
      linarith [hS k hkS]
    have htot : ∑ k, u1 k ≤ ∑ k, u k - (1 - α) * u l := by
      have e : ∑ k, u1 k = ∑ k ∈ Finset.univ.erase l, (u k + C l k * u l) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
        simp only [hu1, oscStep, ↓reduceIte, zero_add]
        exact Finset.sum_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]
      have e2 : ∑ k ∈ Finset.univ.erase l, (u k + C l k * u l)
          = (∑ k, u k - u l) + (∑ k ∈ Finset.univ.erase l, C l k) * u l := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          ← Finset.add_sum_erase _ u (Finset.mem_univ l)]
        ring
      have hCe : ∑ k ∈ Finset.univ.erase l, C l k ≤ α := by
        refine le_trans ?_ (hrow l)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
        linarith [hC0 l l]
      rw [e, e2]
      nlinarith [hu0 l]
    have hsum1 : ∑ k, u1 k ≤ α * ∑ k ∈ insert l T, v k + ∑ k ∈ (insert l T)ᶜ, v k := by
      by_cases hlS : l ∈ T
      · rw [Finset.insert_eq_of_mem hlS]
        nlinarith [hu0 l]
      · rw [Finset.sum_insert hlS, Finset.compl_insert]
        have hc : ∑ k ∈ Tᶜ, v k = v l + ∑ k ∈ Tᶜ.erase l, v k :=
          (Finset.add_sum_erase _ _ (Finset.mem_compl.mpr hlS)).symm
        rw [hc] at hsum
        have := hS l hlS
        nlinarith
    obtain ⟨u', h1, h2, h3⟩ := osc_sweepS hC hC0 hrow hα1 v L (insert l T) (S.P l f) u1
      (S.cont l hf) hosc hS1 hsum1
    have eS : insert l T ∪ L.toFinset = T ∪ (l :: L).toFinset := by
      rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
    rw [eS] at h2 h3
    exact ⟨u', h1, h2, h3⟩

#print axioms osc_sweepS

/-- **A full sweep contracts the total oscillation by `α`.**

DERIVED: `1` the bound on `α`. -/
theorem osc_sweep_fullS {S : Spec N Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) {L : List Lk}
    (hL : ∀ l, l ∈ L) {f : (Lk → SU N) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : OscLe f v) :
    ∃ u' : Lk → ℝ, OscLe (sweepS S L f) u' ∧ ∑ k, u' k ≤ α * ∑ k, v k := by
  obtain ⟨u', h1, -, h3⟩ := osc_sweepS hC hC0 hrow hα1 v L ∅ f v hf hv
    (fun _ _ => le_rfl) (by simp)
  have hU : (∅ : Finset Lk) ∪ L.toFinset = Finset.univ := by
    ext l; simp [hL l]
  rw [hU, Finset.compl_univ, Finset.sum_empty, add_zero] at h3
  exact ⟨u', h1, h3⟩

#print axioms osc_sweep_fullS

/-- **`n` full sweeps leave total oscillation `≤ αⁿ Σ v`.**

DERIVED: `0` the sign of `α`; `1` the bound on `α`. -/
theorem osc_iterS {S : Spec N Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k)
    {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk}
    (hL : ∀ l, l ∈ L) :
    ∀ (n : ℕ) {f : (Lk → SU N) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
      ∃ u : Lk → ℝ, OscLe ((sweepS S L)^[n] f) u ∧ ∑ k, u k ≤ α ^ n * ∑ k, v k
  | 0, _, _, v, hv => ⟨v, hv, by simp⟩
  | n + 1, f, hf, v, hv => by
    obtain ⟨u1, h1, h1s⟩ := osc_sweep_fullS hC hC0 hrow hα1 hL hf hv
    obtain ⟨u, hu, hus⟩ := osc_iterS hC hC0 hrow hα0 hα1 hL n (continuous_sweepS S L hf) h1
    refine ⟨u, by rwa [Function.iterate_succ_apply], hus.trans ?_⟩
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left h1s (pow_nonneg hα0 n)
    linarith

#print axioms osc_iterS

/-- **Mixing of the sweep**: after `n` full sweeps a continuous `f` with oscillation bound `v` varies
by at most `αⁿ Σ v` over all configurations.

DERIVED: `0`, `1` as in `osc_iterS`. -/
theorem sweep_mixingS {S : Spec N Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {L : List Lk} (hL : ∀ l, l ∈ L) (n : ℕ) {f : (Lk → SU N) → ℝ} (hf : Continuous f)
    {v : Lk → ℝ} (hv : OscLe f v) (W W' : Lk → SU N) :
    |(sweepS S L)^[n] f W - (sweepS S L)^[n] f W'| ≤ α ^ n * ∑ k, v k := by
  obtain ⟨u, hu, hus⟩ := osc_iterS hC hC0 hrow hα0 hα1 hL n hf hv
  exact (abs_sub_le_sum_osc hu W W').trans hus

#print axioms sweep_mixingS

omit [Fintype Lk] in
/-- The `n`-fold sweep is continuous.

DERIVED: `0`, `1` the recursion on `n`. -/
theorem continuous_iterS (S : Spec N Lk) (L : List Lk) :
    ∀ (n : ℕ) {f : (Lk → SU N) → ℝ}, Continuous f → Continuous ((sweepS S L)^[n] f)
  | 0, _, hf => hf
  | n + 1, _, hf => by
      rw [Function.iterate_succ_apply]
      exact continuous_iterS S L n (continuous_sweepS S L hf)

#print axioms continuous_iterS

/-- The `n`-fold full sweep as a map of continuous observables.

DERIVED: no numeral. -/
def sweepCS (S : Spec N Lk) (L : List Lk) (n : ℕ) (f : C(Lk → SU N, ℝ)) : C(Lk → SU N, ℝ) :=
  ⟨(sweepS S L)^[n] f, continuous_iterS S L n f.continuous⟩

/-- **A state consistent with the specification**: invariant under every single-link kernel.

DERIVED: no numeral. -/
def Invariant (S : Spec N Lk) (σ : DLRLimit.State (Lk → SU N)) : Prop :=
  ∀ l (f : C(Lk → SU N, ℝ)), σ ⟨S.P l f, S.cont l f.continuous⟩ = σ f

/-- An invariant state is invariant under every sweep.

DERIVED: no numeral. -/
theorem state_sweepS {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ) :
    ∀ (L : List Lk) (f : C(Lk → SU N, ℝ)),
      σ ⟨sweepS S L f, continuous_sweepS S L f.continuous⟩ = σ f
  | [], f => rfl
  | l :: L, f => by
    have h := state_sweepS hσ L ⟨S.P l f, S.cont l f.continuous⟩
    exact h.trans (hσ l f)

#print axioms state_sweepS

/-- An invariant state is invariant under every `n`-fold sweep.

DERIVED: `0`, `1` the recursion on `n`. -/
theorem state_iterS {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ)
    (L : List Lk) : ∀ (n : ℕ) (f : C(Lk → SU N, ℝ)), σ (sweepCS S L n f) = σ f
  | 0, f => rfl
  | n + 1, f => by
      have e : sweepCS S L (n + 1) f
          = sweepCS S L n ⟨sweepS S L f, continuous_sweepS S L f.continuous⟩ := by
        ext W
        show (sweepS S L)^[n + 1] f W = (sweepS S L)^[n] (sweepS S L f) W
        rw [Function.iterate_succ_apply]
      rw [e, state_iterS hσ L n]
      exact state_sweepS hσ L f

#print axioms state_iterS

/-- **Uniqueness under Dobrushin's condition for a general specification**: two states invariant
under every kernel of a specification with TV influence `C ≥ 0` of row sums `≤ α < 1` agree
(`sweep_mixingS`, `DLRLimit.dlr_eq_at_of_kernel_near_const`).

DERIVED: `0` the sign of `α`, `ε`; `1` the strict bound on `α` and the identity configuration. -/
theorem state_unique_of_inflS {S : Spec N Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ν ν' : DLRLimit.State (Lk → SU N)} (hν : Invariant S ν) (hν' : Invariant S ν')
    (f : C(Lk → SU N, ℝ)) : ν f = ν' f := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  have hdlr : ∀ σ : DLRLimit.State (Lk → SU N), Invariant S σ →
      DLRLimit.IsDLR (sweepCS S L) σ := fun σ hσ n g => state_iterS hσ L n g
  obtain ⟨v, hv⟩ := oscLe_of_continuous f.continuous
  refine DLRLimit.dlr_eq_at_of_kernel_near_const (fun ε hε => ?_) (hdlr ν hν) (hdlr ν' hν')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (|∑ k, v k| + 1) by positivity) hα1
  obtain ⟨W0⟩ : Nonempty (Lk → SU N) := ⟨fun _ => 1⟩
  refine ⟨n, sweepCS S L n f W0, fun W => ?_⟩
  have h := sweep_mixingS hC hC0 hrow hα0 hα1.le hL n f.continuous hv W W0
  have hαn : 0 ≤ α ^ n := pow_nonneg hα0 n
  have h2 : α ^ n * (|∑ k, v k| + 1) < ε := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |∑ k, v k| + 1)).1 hn
    linarith
  have h3 : α ^ n * ∑ k, v k ≤ α ^ n * (|∑ k, v k| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self (∑ k, v k)]) hαn
  show |(sweepS S L)^[n] f W - (sweepS S L)^[n] f W0| ≤ ε
  linarith

#print axioms state_unique_of_inflS

/-- **The sweep converges to the invariant state geometrically**: `|Tⁿ f (W) − σ f| ≤ αⁿ Σ v`.

DERIVED: `0`, `1` as in `osc_iterS`. -/
theorem sweep_to_stateS {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    (n : ℕ) (f : C(Lk → SU N, ℝ)) {v : Lk → ℝ} (hv : OscLe f v) (W : Lk → SU N) :
    |(sweepS S L)^[n] f W - σ f| ≤ α ^ n * ∑ k, v k := by
  set B := α ^ n * ∑ k, v k
  have hinv := state_iterS hσ L n f
  have hmix := fun V => sweep_mixingS hC hC0 hrow hα0 hα1 hL n f.continuous hv V W
  have hlo : ∀ V, (((sweepS S L)^[n] f W - B) • (1 : C(Lk → SU N, ℝ))) V
      ≤ sweepCS S L n f V := fun V => by
    have := (abs_le.mp (hmix V)).1
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show _ ≤ (sweepS S L)^[n] f V
    linarith
  have hhi : ∀ V, sweepCS S L n f V
      ≤ (((sweepS S L)^[n] f W + B) • (1 : C(Lk → SU N, ℝ))) V := fun V => by
    have := (abs_le.mp (hmix V)).2
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show (sweepS S L)^[n] f V ≤ _
    linarith
  have h1 := σ.mono hlo
  have h2 := σ.mono hhi
  rw [σ.map_smul, σ.map_one, mul_one, hinv] at h1 h2
  rw [abs_le]
  constructor <;> linarith

#print axioms sweep_to_stateS

end Sweep

/-! ## 3. Expectations of functions -/

section Ex

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

open Classical in
/-- **The value of a state on a real function**: `σ ⟨F, _⟩` when `F` is continuous, `0` otherwise.

DERIVED: `0` the value off the continuous functions. -/
def ex (σ : DLRLimit.State X) (F : X → ℝ) : ℝ :=
  if h : Continuous F then σ ⟨F, h⟩ else 0

/-- On a continuous function, `ex` is the state.

DERIVED: no numeral. -/
theorem ex_mk (σ : DLRLimit.State X) {F : X → ℝ} (hF : Continuous F) : ex σ F = σ ⟨F, hF⟩ := by
  unfold ex
  rw [dif_pos hF]

#print axioms ex_mk

/-- `ex` is additive under subtraction on continuous functions.

DERIVED: no numeral. -/
theorem ex_sub (σ : DLRLimit.State X) {F G : X → ℝ} (hF : Continuous F) (hG : Continuous G) :
    ex σ (fun x => F x - G x) = ex σ F - ex σ G := by
  rw [ex_mk σ (csub hF hG), ex_mk σ hF, ex_mk σ hG, ← σ.map_sub]
  rfl

#print axioms ex_sub

/-- `ex` is homogeneous on continuous functions.

DERIVED: no numeral. -/
theorem ex_const_mul (σ : DLRLimit.State X) (c : ℝ) {F : X → ℝ} (hF : Continuous F) :
    ex σ (fun x => c * F x) = c * ex σ F := by
  rw [ex_mk σ (csmul c hF), ex_mk σ hF, ← σ.map_smul]
  rfl

#print axioms ex_const_mul

/-- **A bounded function has a bounded value**: `|F| ≤ c` gives `|ex σ F| ≤ c`.

DERIVED: no numeral. -/
theorem abs_ex_le (σ : DLRLimit.State X) {F : X → ℝ} (hF : Continuous F) {c : ℝ}
    (hc : ∀ x, |F x| ≤ c) : |ex σ F| ≤ c := by
  rw [ex_mk σ hF]
  have h1 := σ.mono (f := ⟨F, hF⟩) (g := c • (1 : C(X, ℝ))) fun x => by
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact (abs_le.mp (hc x)).2
  have h2 := σ.mono (f := (-c) • (1 : C(X, ℝ))) (g := ⟨F, hF⟩) fun x => by
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    exact (abs_le.mp (hc x)).1
  rw [σ.map_smul, σ.map_one, mul_one] at h1 h2
  rw [abs_le]
  exact ⟨h2, h1⟩

#print axioms abs_ex_le

end Ex

/-! ## 4. Covariance decay for a general specification -/

section Cov

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- Invariance in the `ex` form.

DERIVED: no numeral. -/
theorem ex_P {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ) (l : Lk)
    {F : (Lk → SU N) → ℝ} (hF : Continuous F) : ex σ (S.P l F) = ex σ F := by
  rw [ex_mk σ (S.cont l hF), ex_mk σ hF]
  exact hσ l ⟨F, hF⟩

#print axioms ex_P

/-- **One kernel in the covariance**: replacing `f` by `P l f` in `σ(f g)` costs at most
`v_f(l) v_g(l)`. The difference is `σ(P(f g) − P f · P g)`, the conditional covariance at `l`
(invariance and `pull`).

DERIVED: no numeral. -/
theorem cov_stepS {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ) (l : Lk)
    {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : OscLe f vf) (hvg : OscLe g vg) :
    |ex σ (fun W => f W * g W) - ex σ (fun W => S.P l f W * g W)| ≤ vf l * vg l := by
  have hPf := S.cont l hf
  have hPg := S.cont l hg
  have i1 := ex_P hσ l (cmul hf hg)
  have i2 := ex_P hσ l (cmul hPf hg)
  have e2 : S.P l (fun W => S.P l f W * g W) = fun W => S.P l f W * S.P l g W :=
    funext fun W => S.pull l hPf hg (fun V x => S.upd l f V x) W
  rw [e2] at i2
  rw [← i1, ← i2, ← ex_sub σ (S.cont l (cmul hf hg)) (cmul hPf hPg)]
  exact abs_ex_le σ (csub (S.cont l (cmul hf hg)) (cmul hPf hPg))
    fun W => S.condCov_le l hf hg hvf hvg W

#print axioms cov_stepS

/-- **The covariance telescope**: along any list `L`,
`|σ(f g) − σ((sweep L f) g)| ≤ oscCost C v_g L v_f`.

DERIVED: `0` the cost of the empty run. -/
theorem cov_runS {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) {g : (Lk → SU N) → ℝ} (hg : Continuous g)
    {vg : Lk → ℝ} (hvg : OscLe g vg) :
    ∀ (L : List Lk) {f : (Lk → SU N) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
      |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L f W * g W)| ≤ oscCost C vg L v
  | [], f, _, v, _ => by
      show |ex σ (fun W => f W * g W) - ex σ (fun W => f W * g W)| ≤ 0
      simp
  | l :: L, f, hf, v, hv => by
      have h1 := cov_stepS hσ l hf hg hv hvg
      have h2 := cov_runS hσ hC hg hvg L (S.cont l hf) (osc_stepS hC hf hv l)
      show |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L (S.P l f) W * g W)|
        ≤ v l * vg l + oscCost C vg L (oscStep C l v)
      calc |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S L (S.P l f) W * g W)|
          ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => S.P l f W * g W)|
            + |ex σ (fun W => S.P l f W * g W)
              - ex σ (fun W => sweepS S L (S.P l f) W * g W)| := abs_sub_le _ _ _
        _ ≤ v l * vg l + oscCost C vg L (oscStep C l v) := add_le_add h1 h2

#print axioms cov_runS

omit [Fintype Lk] in
/-- A sweep along a concatenation is the composite sweep.

DERIVED: no numeral. -/
theorem sweepS_append (S : Spec N Lk) :
    ∀ (L1 L2 : List Lk) (f : (Lk → SU N) → ℝ), sweepS S (L1 ++ L2) f = sweepS S L2 (sweepS S L1 f)
  | [], _, _ => rfl
  | l :: L1, L2, f => sweepS_append S L1 L2 (S.P l f)

#print axioms sweepS_append

omit [Fintype Lk] in
/-- `n` iterated sweeps along `L` are one sweep along `rep L n`.

DERIVED: `0`, `1` the recursion on `n`. -/
theorem sweepS_rep (S : Spec N Lk) (L : List Lk) :
    ∀ (n : ℕ) (f : (Lk → SU N) → ℝ), (sweepS S L)^[n] f = sweepS S (rep L n) f
  | 0, _ => rfl
  | n + 1, f => by
      show (sweepS S L)^[n + 1] f = sweepS S (L ++ rep L n) f
      rw [Function.iterate_succ_apply, sweepS_rep S L n, sweepS_append]

#print axioms sweepS_rep

/-- **Dobrushin's covariance bound for a general specification, weighted form.** For an invariant
state of a specification with TV influence `C ≥ 0` of row sums `≤ α`, any `α < θ ≤ 1`, any level
`ψ` that one influence step changes by at most one, continuous `f, g` with oscillation bounds
`v_f, v_g` and `v_g ≤ V_g θ^ψ`: `|σ(f g) − σ f σ g| ≤ V_g θ/(θ − α) · Σ_k θ^{ψ k} v_f(k)`.

DERIVED: `0` the sign of `α` and the limit of `αⁿ`; `1` the bound on `θ`. -/
theorem cov_le_weightedS {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) (ψ : Lk → ℕ)
    (hloc : ∀ l k, C l k ≠ 0 → ψ l ≤ ψ k + 1) {f g : (Lk → SU N) → ℝ} (hf : Continuous f)
    (hg : Continuous g) {vf vg : Lk → ℝ} (hvf : OscLe f vf) (hvg : OscLe g vg) {Vg : ℝ}
    (hVg : 0 ≤ Vg) (hw : ∀ k, vg k ≤ Vg * θ ^ ψ k) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  obtain ⟨B, hB⟩ := exists_abs_le hg
  have hθ0 : 0 ≤ θ := by linarith
  have hα1 : α < 1 := by linarith
  have hθα : 0 < θ - α := by linarith
  have hvf0 : ∀ k, 0 ≤ vf k := hvf.nonneg
  have hS0 : 0 ≤ ∑ k, vf k := Finset.sum_nonneg fun k _ => hvf0 k
  have hn : ∀ n : ℕ, |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k + α ^ n * (∑ k, vf k) * B := by
    intro n
    have h1 := cov_runS hσ hC hg hvg (rep L n) hf hvf
    have h2 := cost_le hC0 hrow hαθ.le hθ0 hθ1 ψ hloc hVg hw (rep L n) vf hvf0
    have h3 : oscCost C vg (rep L n) vf ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k := by
      have e : Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k
          = Vg * (θ * ∑ k, θ ^ ψ k * vf k) / (θ - α) := by ring
      rw [e, le_div_iff₀ hθα]
      linarith
    have hc : Continuous (sweepS S (rep L n) f) := continuous_sweepS S _ hf
    have hT : ∀ W, |(sweepS S (rep L n) f W - ex σ f) * g W| ≤ α ^ n * (∑ k, vf k) * B := by
      intro W
      have h := sweep_to_stateS hσ hC hC0 hrow hα0 hα1.le hL n ⟨f, hf⟩ hvf W
      rw [sweepS_rep] at h
      rw [abs_mul, ex_mk σ hf]
      exact mul_le_mul h (hB W) (abs_nonneg _) (mul_nonneg (pow_nonneg hα0 n) hS0)
    have e : ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g
        = ex σ (fun W => (sweepS S (rep L n) f W - ex σ f) * g W) := by
      have e1 : (fun W => (sweepS S (rep L n) f W - ex σ f) * g W)
          = fun W => sweepS S (rep L n) f W * g W - ex σ f * g W :=
        funext fun W => by ring
      rw [e1, ex_sub σ (F := fun W => sweepS S (rep L n) f W * g W)
        (G := fun W => ex σ f * g W) (cmul hc hg) (csmul _ hg),
        ex_const_mul σ _ hg]
    have h4 : |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g|
        ≤ α ^ n * (∑ k, vf k) * B := by
      rw [e]
      exact abs_ex_le σ (cmul (csubc hc (ex σ f)) hg) hT
    calc |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
        ≤ |ex σ (fun W => f W * g W) - ex σ (fun W => sweepS S (rep L n) f W * g W)|
          + |ex σ (fun W => sweepS S (rep L n) f W * g W) - ex σ f * ex σ g| :=
          abs_sub_le _ _ _
      _ ≤ Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k + α ^ n * (∑ k, vf k) * B := by
          linarith [h1.trans h3]
  have ht : Tendsto (fun n : ℕ => Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k
      + α ^ n * (∑ k, vf k) * B)
      atTop (𝓝 (Vg * θ / (θ - α) * ∑ k, θ ^ ψ k * vf k + 0 * (∑ k, vf k) * B)) :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const _).mul_const _).const_add _
  have hle := ge_of_tendsto' ht hn
  simpa using hle

#print axioms cov_le_weightedS

/-- **Spatial Dobrushin decay for a general specification.** Under the TV influence hypotheses with
row sums `≤ α < θ ≤ 1`: if `g` has oscillation `≤ V_g` on `B` and `0` off it, and `f` has
oscillation `0` on `reach C B d`, then `|σ(f g) − σ f σ g| ≤ V_g θ/(θ − α) · θ^{d+1} Σ_k v_f(k)`
for every invariant state `σ` (`cov_le_weightedS` at `level C B (d + 1)`).

DERIVED: `0` the sign and the oscillations off the supports; `1` the bound on `θ` and the cap
beyond `d`. -/
theorem cov_spatialS {S : Spec N Lk} {σ : DLRLimit.State (Lk → SU N)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1)
    {f g : (Lk → SU N) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
    (hvf : OscLe f vf) (hvg : OscLe g vg) (B : Finset Lk) {Vg : ℝ} (hVg : 0 ≤ Vg)
    (hgB : ∀ k, k ∉ B → vg k = 0) (hgV : ∀ k, vg k ≤ Vg) (d : ℕ)
    (hfar : ∀ k, vf k ≠ 0 → k ∉ reach C B d) :
    |ex σ (fun W => f W * g W) - ex σ f * ex σ g|
      ≤ Vg * θ / (θ - α) * (θ ^ (d + 1) * ∑ k, vf k) := by
  have hθ0 : 0 ≤ θ := by linarith
  have hw : ∀ k, vg k ≤ Vg * θ ^ level C B (d + 1) k := by
    intro k
    by_cases hk : k ∈ B
    · rw [level_of_mem C (d + 1) hk, pow_zero, mul_one]
      exact hgV k
    · rw [hgB k hk]
      exact mul_nonneg hVg (pow_nonneg hθ0 _)
  have h := cov_le_weightedS hσ hC hC0 hrow hα0 hαθ hθ1 (level C B (d + 1))
    (fun l k hlk => level_loc C B (d + 1) hlk) hf hg hvf hvg hVg hw
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : vf k = 0
    · rw [hk]; simp
    · rw [level_far C B (hfar k hk)]
  · exact div_nonneg (mul_nonneg hVg hθ0) (by linarith)

#print axioms cov_spatialS

end Cov

/-! ## 5. The heat bath of a positive continuous weight is a specification -/

section Heat

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

omit [Fintype Lk] in
/-- **The heat bath is monotone on the fibre.**

DERIVED: `0` the sign of the weight. -/
theorem wAvg_mono {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) (l : Lk)
    {f f' : (Lk → SU N) → ℝ} (hf : Continuous f) (hf' : Continuous f') (W : Lk → SU N)
    (hle : ∀ g, f (Function.update W l g) ≤ f' (Function.update W l g)) :
    wAvg Φ l f W ≤ wAvg Φ l f' W := by
  have hu : Continuous (fun g : SU N => Function.update W l g) :=
    continuous_const.update l continuous_id
  unfold wAvg
  refine div_le_div_of_nonneg_right ?_ (wPart_pos hpos hcont l W).le
  unfold wNum
  exact integral_mono (integrable_cont ((hf.comp hu).mul (hcont.comp hu)))
    (integrable_cont ((hf'.comp hu).mul (hcont.comp hu)))
    fun g => mul_le_mul_of_nonneg_right (hle g) (hpos _).le

#print axioms wAvg_mono

/-- **The heat baths of a positive continuous weight form a specification**
(`continuous_wAvg`, `wAvg_add`, `wAvg_const_mul`, `wAvg_of_readsNot`, `wAvg_mono`, `wAvg_update`).

DERIVED: no numeral. -/
def heatSpec {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) : Spec N Lk where
  P := wAvg Φ
  cont := fun l {_} hf => continuous_wAvg hpos hcont l hf
  lin := fun l {f f'} hf hf' a b W => by
    rw [wAvg_add hcont l (csmul a hf) (csmul b hf') W,
      wAvg_const_mul, wAvg_const_mul]
  one := fun l W => wAvg_of_readsNot hpos hcont l (f := fun _ => 1) (fun _ _ => rfl) W
  mono := fun l {_ _} hf hf' W hle => wAvg_mono hpos hcont l hf hf' W hle
  upd := fun l f W x => wAvg_update Φ l f W x

/-- **The heat-bath influence matrix is a TV influence matrix of `heatSpec`**, by definition.

DERIVED: no numeral. -/
theorem sInfl_heat {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ)
    {C : Lk → Lk → ℝ} (hC : Infl Φ C) : SInfl (heatSpec hpos hcont) C := hC

#print axioms sInfl_heat

/-- **The Gibbs state of the weight is invariant under `heatSpec`**
(`BoxDobrushinCoupling.gibbsState_invariant`).

DERIVED: no numeral. -/
theorem invariant_gibbs {Φ : (Lk → SU N) → ℝ} (hpos : ∀ W, 0 < Φ W) (hcont : Continuous Φ) :
    Invariant (heatSpec hpos hcont) (gibbsState hpos hcont) :=
  fun l f => gibbsState_invariant hpos hcont l f

#print axioms invariant_gibbs

end Heat

end MassGap.DobrushinGeneral
