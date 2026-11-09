import Mathlib
import MassGap.DobrushinGeneral
import MassGap.ObserverEnergyCoarseN

noncomputable section

/-!
# MassGap.DobrushinUnbounded — Dobrushin's theorem for real-valued spins, by truncation

`DobrushinGeneral` proves Dobrushin's oscillation contraction, uniqueness and covariance decay for a
finite specification with spins in `SU(N)`. The proofs read the spin space only through compactness
(the fibre minimum in `osc_stepS`) and non-emptiness (the sign of an oscillation bound). This module
proves the same results for spins in any non-empty compact space, and uses them to control real-valued,
unbounded spins (the energies of the cells of a physical grid) by truncation.

1. **Compact spins** (`Spec`, `SInfl`, `Invariant`, `osc_stepS`, `osc_sweep_fullS`, `sweep_mixingS`,
   `state_unique_of_inflS`, `sweep_to_stateS`, `cov_le_weightedS`, `cov_spatialS`): the statements of
   `DobrushinGeneral` with `SU(N)` replaced by a compact space `Ω`. The oscillation calculus
   (`OscLe`, `abs_sub_le_sum_osc`, `oscLe_of_continuous`) is restated for `Ω`.
2. **Truncation** (`Tsp`, `clampL`, `sq_sub_clampL_mul_le`, `truncMap`): the truncation of a real
   reading at level `L` is its clamp to `[-|L|, |L|]`, a spin in a compact interval. The truncation
   error obeys `(x − clamp x)² |L|⁴ ≤ x⁶`.
3. **The truncated law** (`TruncLaw`): a state read through the truncated field at level `L` is a
   limit of states on finite boxes, each invariant under a specification with spins in `[-|L|, |L|]`
   whose TV influence matrix has row sums `≤ α`; influence steps are at most one unit of a distance
   `cd` on the cells.
4. **Clustering of affine cell readings** (`truncLaw_cov`, `cov_affine_unbounded`,
   `cov_affine_rate`): for readings `b + Σ_{c ∈ A} w_c e_c` of finitely many cells, separated by more
   than `d` in `cd`, the truncated covariance is `≤ 4 W_F W_G θ²/(θ − α) · L² θ^d` and the truncation
   costs `2 μ₆ (W_F Q_G + Q_F W_G)/L²`, with `μ₆²` a bound on the sixth moments and `Q` built from the
   second moments. At `L = θ^{−d/4}` both are `(√θ)^d`.

## Scope

The truncated law is a hypothesis on the state; nothing here derives it. The moments enter only as
bounds on `ν(e_c²)` and `ν(e_c⁶)` for the cells read.
-/

namespace MassGap.DobrushinUnbounded

open MeasureTheory Filter Topology
open MassGap.HeatBath (exists_abs_le)
open MassGap.BoxDobrushinCoupling (oscStep)
open MassGap.BoxDobrushinSpatial (oscRun oscCost cost_le reach level level_loc level_of_mem
  level_far rep oscStep_nonneg)
open MassGap.DobrushinGeneral (cmul csmul cadd csub caddc csubc ex ex_mk ex_sub ex_const_mul
  abs_ex_le)

variable {Ω : Type} [TopologicalSpace Ω] [CompactSpace Ω] [Nonempty Ω]

/-! ## 0. Oscillations on a compact spin space -/

section Osc

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- **`v` bounds the single-site oscillations of `f`**: changing the spin at `k` moves `f` by at
most `v k`.

DERIVED: no numeral. -/
def OscLe (f : (Lk → Ω) → ℝ) (v : Lk → ℝ) : Prop :=
  ∀ W k g, |f (Function.update W k g) - f W| ≤ v k

omit [Fintype Lk] in
/-- An oscillation bound is non-negative.

DERIVED: `0` the sign. -/
theorem OscLe.nonneg {f : (Lk → Ω) → ℝ} {v : Lk → ℝ} (hv : OscLe f v) (k : Lk) : 0 ≤ v k := by
  have h := hv (fun _ => Classical.arbitrary Ω) k (Classical.arbitrary Ω)
  have e : Function.update (fun _ : Lk => Classical.arbitrary Ω) k (Classical.arbitrary Ω)
      = fun _ => Classical.arbitrary Ω := by
    funext j; by_cases hj : j = k <;> simp [Function.update, hj]
  rw [e, sub_self, abs_zero] at h
  exact h

#print axioms OscLe.nonneg

/-- **Oscillations add up**: changing the links of a finite set `s` one at a time moves `F` by at
most `Σ_{k ∈ s} u k`.

DERIVED: no numeral. -/
theorem abs_sub_le_osc_finset {F : (Lk → Ω) → ℝ} {u : Lk → ℝ} (hu : OscLe F u)
    (W W' : Lk → Ω) (s : Finset Lk) :
    |F W - F (fun k => if k ∈ s then W' k else W k)| ≤ ∑ k ∈ s, u k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have e : (fun k => if k ∈ insert a s then W' k else W k)
        = Function.update (fun k => if k ∈ s then W' k else W k) a (W' a) := by
      funext k
      by_cases hk : k = a
      · subst hk; simp
      · simp [Function.update, hk]
    rw [e, Finset.sum_insert ha]
    have h2 := hu (fun k => if k ∈ s then W' k else W k) a (W' a)
    calc |F W - F (Function.update (fun k => if k ∈ s then W' k else W k) a (W' a))|
        ≤ |F W - F (fun k => if k ∈ s then W' k else W k)|
          + |F (fun k => if k ∈ s then W' k else W k)
            - F (Function.update (fun k => if k ∈ s then W' k else W k) a (W' a))| :=
          abs_sub_le _ _ _
      _ ≤ ∑ k ∈ s, u k + u a := by rw [abs_sub_comm] at h2; linarith
      _ = u a + ∑ k ∈ s, u k := by ring

#print axioms abs_sub_le_osc_finset

/-- **Total oscillation bounds the range**: `|F W − F W'| ≤ Σ u`.

DERIVED: no numeral. -/
theorem abs_sub_le_sum_osc {F : (Lk → Ω) → ℝ} {u : Lk → ℝ} (hu : OscLe F u)
    (W W' : Lk → Ω) : |F W - F W'| ≤ ∑ k, u k := by
  have h := abs_sub_le_osc_finset hu W W' Finset.univ
  simpa using h

#print axioms abs_sub_le_sum_osc

/-- A continuous function on the compact configuration space has a finite oscillation bound.

DERIVED: `2` the two values compared. -/
theorem oscLe_of_continuous {f : (Lk → Ω) → ℝ} (hf : Continuous f) :
    ∃ v : Lk → ℝ, OscLe f v := by
  obtain ⟨B, hB⟩ := exists_abs_le hf
  refine ⟨fun _ => 2 * B, fun W k g => ?_⟩
  have h1 := abs_le.mp (hB (Function.update W k g))
  have h2 := abs_le.mp (hB W)
  rw [abs_le]
  constructor <;> linarith

#print axioms oscLe_of_continuous

end Osc

/-! ## 1. Finite specifications -/

section Spec

/-- **A finite specification on `Lk → SU(N)`**: a kernel `P l` per link that is Feller, linear,
unital, monotone on the fibre of `l`, and does not read the variable at `l`.

DERIVED: `1` is the constant function and its mean. -/
structure Spec (Ω : Type) [TopologicalSpace Ω] (Lk : Type) [DecidableEq Lk] where
  /-- The kernel at `l`, acting on real functions of the configuration. -/
  P : Lk → ((Lk → Ω) → ℝ) → (Lk → Ω) → ℝ
  /-- Feller: continuous functions go to continuous functions. -/
  cont : ∀ (l : Lk) {f : (Lk → Ω) → ℝ}, Continuous f → Continuous (P l f)
  /-- Linear on continuous functions. -/
  lin : ∀ (l : Lk) {f f' : (Lk → Ω) → ℝ}, Continuous f → Continuous f' → ∀ (a b : ℝ)
    (W : Lk → Ω), P l (fun V => a * f V + b * f' V) W = a * P l f W + b * P l f' W
  /-- Unital. DERIVED: `1` the constant function and its mean. -/
  one : ∀ (l : Lk) (W : Lk → Ω), P l (fun _ => 1) W = 1
  /-- Monotone on the fibre of `l` at `W`. -/
  mono : ∀ (l : Lk) {f f' : (Lk → Ω) → ℝ}, Continuous f → Continuous f' → ∀ W : Lk → Ω,
    (∀ g, f (Function.update W l g) ≤ f' (Function.update W l g)) → P l f W ≤ P l f' W
  /-- The kernel at `l` does not read the variable at `l`. -/
  upd : ∀ (l : Lk) (f : (Lk → Ω) → ℝ) (W : Lk → Ω) (x : Ω),
    P l f (Function.update W l x) = P l f W

namespace Spec

variable {Lk : Type} [DecidableEq Lk] (S : Spec Ω Lk)

/-- **The kernel reads `f` only on the fibre of `l`.**

DERIVED: no numeral. -/
theorem fibre_eq (l : Lk) {f f' : (Lk → Ω) → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (W : Lk → Ω) (e : ∀ g, f (Function.update W l g) = f' (Function.update W l g)) :
    S.P l f W = S.P l f' W :=
  le_antisymm (S.mono l hf hf' W fun g => (e g).le) (S.mono l hf' hf W fun g => (e g).ge)

#print axioms fibre_eq

/-- Constants are fixed.

DERIVED: `0`, `1` the coefficients used in `lin`. -/
theorem const (l : Lk) (c : ℝ) (W : Lk → Ω) : S.P l (fun _ => c) W = c := by
  have h := S.lin l (f := fun _ => (1 : ℝ)) (f' := fun _ => (1 : ℝ)) continuous_const
    continuous_const c 0 W
  simp only [S.one, mul_one, zero_mul, add_zero] at h
  exact h

#print axioms const

/-- Adding a constant commutes with the kernel.

DERIVED: `1` the coefficient and the constant function. -/
theorem add_const (l : Lk) {F : (Lk → Ω) → ℝ} (hF : Continuous F) (c : ℝ) (W : Lk → Ω) :
    S.P l (fun V => F V + c) W = S.P l F W + c := by
  have h := S.lin l (f' := fun _ => (1 : ℝ)) hF continuous_const 1 c W
  simp only [S.one, one_mul, mul_one] at h
  exact h

#print axioms add_const

/-- The kernel of an affine function of `h`.

DERIVED: `1` the constant function. -/
theorem affine (l : Lk) {h : (Lk → Ω) → ℝ} (hh : Continuous h) (a b : ℝ) (W : Lk → Ω) :
    S.P l (fun V => a + b * h V) W = a + b * S.P l h W := by
  have e := S.lin l (f := fun _ => (1 : ℝ)) continuous_const hh a b W
  simp only [S.one, mul_one] at e
  exact e

#print axioms affine

/-- Linear combination plus a constant.

DERIVED: no numeral. -/
theorem lin_const (l : Lk) {f f' : (Lk → Ω) → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (a b c : ℝ) (W : Lk → Ω) :
    S.P l (fun V => a * f V + b * f' V + c) W = a * S.P l f W + b * S.P l f' W + c := by
  rw [S.add_const l (F := fun V => a * f V + b * f' V)
    (cadd (csmul a hf) (csmul b hf')) c W, S.lin l hf hf' a b W]

#print axioms lin_const

/-- **The kernel is a normalised average on the fibre**: functions within `c` of each other on the
fibre of `l` at `W` have kernel means within `c`.

DERIVED: no numeral. -/
theorem sub_le (l : Lk) {f f' : (Lk → Ω) → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (W : Lk → Ω) {c : ℝ}
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
theorem pull (l : Lk) {a f : (Lk → Ω) → ℝ} (ha : Continuous a) (hf : Continuous f)
    (har : ∀ V g, a (Function.update V l g) = a V) (W : Lk → Ω) :
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
theorem fix (l : Lk) {f : (Lk → Ω) → ℝ} (hf : Continuous f)
    (hr : ∀ V g, f (Function.update V l g) = f V) (W : Lk → Ω) : S.P l f W = f W := by
  rw [S.fibre_eq l hf continuous_const W (f' := fun _ => f W) (fun g => hr W g), S.const]

#print axioms fix

/-- **A kernel moves an observable by at most its oscillation at that link.**

DERIVED: no numeral. -/
theorem abs_sub_P_le (l : Lk) {f : (Lk → Ω) → ℝ} (hf : Continuous f) {v : Lk → ℝ}
    (hv : OscLe f v) (W : Lk → Ω) : |f W - S.P l f W| ≤ v l := by
  have h := S.sub_le l (f := fun _ => f W) continuous_const hf W (c := v l) (fun g => by
    show |f W - f (Function.update W l g)| ≤ v l
    rw [abs_sub_comm]
    exact hv W l g)
  rwa [S.const] at h

#print axioms abs_sub_P_le

/-- **The conditional covariance at one link**: `|P(f g) − P f · P g| ≤ v_f(l) v_g(l)`.

DERIVED: no numeral. -/
theorem condCov_le (l : Lk) {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {vf vg : Lk → ℝ} (hvf : OscLe f vf) (hvg : OscLe g vg) (W : Lk → Ω) :
    |S.P l (fun V => f V * g V) W - S.P l f W * S.P l g W| ≤ vf l * vg l := by
  obtain ⟨a, ha⟩ : ∃ a, a = S.P l f W := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = S.P l g W := ⟨_, rfl⟩
  have hfib : ∀ (F : (Lk → Ω) → ℝ), Continuous F → ∀ {u : Lk → ℝ}, OscLe F u → ∀ x,
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
def SInfl (S : Spec Ω Lk) (C : Lk → Lk → ℝ) : Prop :=
  ∀ l k, l ≠ k → ∀ (W : Lk → Ω) (x : Ω) (φ : Ω → ℝ), Continuous φ → (∀ e, 0 ≤ φ e) →
    (∀ e, φ e ≤ 1) →
    |S.P l (fun V => φ (V l)) (Function.update W k x) - S.P l (fun V => φ (V l)) W| ≤ C l k

/-- **Dobrushin's comparison for a general specification (Föllmer's step).** If `v` bounds the
single-link oscillations of a continuous `f` and `C` is a TV influence matrix of `S`, then
`oscStep C l v` bounds those of `P l f`.

DERIVED: `0` the sign of `C` and the oscillation at `l`; `1` the range of the rescaled fibre
function. -/
theorem osc_stepS {S : Spec Ω Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) {f : (Lk → Ω) → ℝ}
    (hf : Continuous f) {v : Lk → ℝ} (hv : OscLe f v) (l : Lk) :
    OscLe (S.P l f) (oscStep C l v) := by
  intro W k x
  unfold oscStep
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, S.upd, sub_self, abs_zero]
  rw [if_neg hkl]
  have hlk : l ≠ k := Ne.symm hkl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Ω → ℝ, ∀ g, ψ g = f (Function.update W l g) := ⟨_, fun _ => rfl⟩
  have hu : Continuous (fun g : Ω => Function.update W l g) :=
    continuous_const.update l continuous_id
  have hψc : Continuous ψ := by
    have : ψ = fun g => f (Function.update W l g) := funext hψ
    rw [this]; exact hf.comp hu
  have hF : Continuous (fun V : Lk → Ω => ψ (V l)) := hψc.comp (continuous_apply l)
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
      have e : (fun V : Lk → Ω => ψ (V l)) = fun V => ψ g0 + 0 * ψ (V l) := by
        funext V; rw [hconst]; ring
      rw [e, S.affine l hF, S.affine l hF]
      simp only [zero_mul, add_zero, sub_self, abs_zero]
      exact mul_nonneg hC0 hvl
    · obtain ⟨φ, hφ⟩ : ∃ φ : Ω → ℝ, ∀ g, φ g = (ψ g - ψ g0) / v l := ⟨_, fun _ => rfl⟩
      have hφc : Continuous φ := by
        have : φ = fun g => (ψ g - ψ g0) / v l := funext hφ
        rw [this]; exact (hψc.sub continuous_const).div_const _
      have hφ0 : ∀ g, 0 ≤ φ g := fun g => by
        rw [hφ]; exact div_nonneg (by linarith [hmin g]) hvl
      have hφ1 : ∀ g, φ g ≤ 1 := fun g => by
        rw [hφ, div_le_one hpos']; exact hrng g
      have e : (fun V : Lk → Ω => ψ (V l)) = fun V => ψ g0 + v l * φ (V l) := by
        funext V; rw [hφ]; field_simp; ring
      have hφF : Continuous (fun V : Lk → Ω => φ (V l)) := hφc.comp (continuous_apply l)
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
def sweepS (S : Spec Ω Lk) : List Lk → ((Lk → Ω) → ℝ) → ((Lk → Ω) → ℝ)
  | [], f => f
  | l :: L, f => sweepS S L (S.P l f)

omit [Fintype Lk] in
/-- A sweep keeps continuity.

DERIVED: no numeral. -/
theorem continuous_sweepS (S : Spec Ω Lk) :
    ∀ (L : List Lk) {f : (Lk → Ω) → ℝ}, Continuous f → Continuous (sweepS S L f)
  | [], _, hf => hf
  | l :: L, _, hf => continuous_sweepS S L (S.cont l hf)

#print axioms continuous_sweepS

omit [Fintype Lk] in
/-- **The vector form**: along any list, `oscRun C L v` bounds the oscillations of the swept
observable (`osc_stepS` at each step).

DERIVED: no numeral. -/
theorem osc_runS {S : Spec Ω Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) :
    ∀ (L : List Lk) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
      OscLe (sweepS S L f) (oscRun C L v)
  | [], _, _, _, hv => hv
  | l :: L, _, hf, _, hv => osc_runS hC L (S.cont l hf) (osc_stepS hC hf hv l)

#print axioms osc_runS

/-- **The oscillation budget along a sweep** (as `BoxDobrushinCoupling.osc_sweep`, for a general
specification).

DERIVED: `0` the sign; `1` the bound on `α`. -/
theorem osc_sweepS {S : Spec Ω Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k)
    {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) (v : Lk → ℝ) :
    ∀ (L : List Lk) (T : Finset Lk) (f : (Lk → Ω) → ℝ) (u : Lk → ℝ), Continuous f →
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
theorem osc_sweep_fullS {S : Spec Ω Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα1 : α ≤ 1) {L : List Lk}
    (hL : ∀ l, l ∈ L) {f : (Lk → Ω) → ℝ} (hf : Continuous f) {v : Lk → ℝ} (hv : OscLe f v) :
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
theorem osc_iterS {S : Spec Ω Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k)
    {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk}
    (hL : ∀ l, l ∈ L) :
    ∀ (n : ℕ) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
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
theorem sweep_mixingS {S : Spec Ω Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {L : List Lk} (hL : ∀ l, l ∈ L) (n : ℕ) {f : (Lk → Ω) → ℝ} (hf : Continuous f)
    {v : Lk → ℝ} (hv : OscLe f v) (W W' : Lk → Ω) :
    |(sweepS S L)^[n] f W - (sweepS S L)^[n] f W'| ≤ α ^ n * ∑ k, v k := by
  obtain ⟨u, hu, hus⟩ := osc_iterS hC hC0 hrow hα0 hα1 hL n hf hv
  exact (abs_sub_le_sum_osc hu W W').trans hus

#print axioms sweep_mixingS

omit [Fintype Lk] in
/-- The `n`-fold sweep is continuous.

DERIVED: `0`, `1` the recursion on `n`. -/
theorem continuous_iterS (S : Spec Ω Lk) (L : List Lk) :
    ∀ (n : ℕ) {f : (Lk → Ω) → ℝ}, Continuous f → Continuous ((sweepS S L)^[n] f)
  | 0, _, hf => hf
  | n + 1, _, hf => by
      rw [Function.iterate_succ_apply]
      exact continuous_iterS S L n (continuous_sweepS S L hf)

#print axioms continuous_iterS

/-- The `n`-fold full sweep as a map of continuous observables.

DERIVED: no numeral. -/
def sweepCS (S : Spec Ω Lk) (L : List Lk) (n : ℕ) (f : C(Lk → Ω, ℝ)) : C(Lk → Ω, ℝ) :=
  ⟨(sweepS S L)^[n] f, continuous_iterS S L n f.continuous⟩

/-- **A state consistent with the specification**: invariant under every single-link kernel.

DERIVED: no numeral. -/
def Invariant (S : Spec Ω Lk) (σ : DLRLimit.State (Lk → Ω)) : Prop :=
  ∀ l (f : C(Lk → Ω, ℝ)), σ ⟨S.P l f, S.cont l f.continuous⟩ = σ f

/-- An invariant state is invariant under every sweep.

DERIVED: no numeral. -/
theorem state_sweepS {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ) :
    ∀ (L : List Lk) (f : C(Lk → Ω, ℝ)),
      σ ⟨sweepS S L f, continuous_sweepS S L f.continuous⟩ = σ f
  | [], f => rfl
  | l :: L, f => by
    have h := state_sweepS hσ L ⟨S.P l f, S.cont l f.continuous⟩
    exact h.trans (hσ l f)

#print axioms state_sweepS

/-- An invariant state is invariant under every `n`-fold sweep.

DERIVED: `0`, `1` the recursion on `n`. -/
theorem state_iterS {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    (L : List Lk) : ∀ (n : ℕ) (f : C(Lk → Ω, ℝ)), σ (sweepCS S L n f) = σ f
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
theorem state_unique_of_inflS {S : Spec Ω Lk} {C : Lk → Lk → ℝ} (hC : SInfl S C)
    (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ} (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ν ν' : DLRLimit.State (Lk → Ω)} (hν : Invariant S ν) (hν' : Invariant S ν')
    (f : C(Lk → Ω, ℝ)) : ν f = ν' f := by
  obtain ⟨L, hL⟩ : ∃ L : List Lk, ∀ l, l ∈ L := ⟨Finset.univ.toList, fun l => by simp⟩
  have hdlr : ∀ σ : DLRLimit.State (Lk → Ω), Invariant S σ →
      DLRLimit.IsDLR (sweepCS S L) σ := fun σ hσ n g => state_iterS hσ L n g
  obtain ⟨v, hv⟩ := oscLe_of_continuous f.continuous
  refine DLRLimit.dlr_eq_at_of_kernel_near_const (fun ε hε => ?_) (hdlr ν hν) (hdlr ν' hν')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (|∑ k, v k| + 1) by positivity) hα1
  obtain ⟨W0⟩ : Nonempty (Lk → Ω) := ⟨fun _ => Classical.arbitrary Ω⟩
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
theorem sweep_to_stateS {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {L : List Lk} (hL : ∀ l, l ∈ L)
    (n : ℕ) (f : C(Lk → Ω, ℝ)) {v : Lk → ℝ} (hv : OscLe f v) (W : Lk → Ω) :
    |(sweepS S L)^[n] f W - σ f| ≤ α ^ n * ∑ k, v k := by
  set B := α ^ n * ∑ k, v k
  have hinv := state_iterS hσ L n f
  have hmix := fun V => sweep_mixingS hC hC0 hrow hα0 hα1 hL n f.continuous hv V W
  have hlo : ∀ V, (((sweepS S L)^[n] f W - B) • (1 : C(Lk → Ω, ℝ))) V
      ≤ sweepCS S L n f V := fun V => by
    have := (abs_le.mp (hmix V)).1
    simp only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    show _ ≤ (sweepS S L)^[n] f V
    linarith
  have hhi : ∀ V, sweepCS S L n f V
      ≤ (((sweepS S L)^[n] f W + B) • (1 : C(Lk → Ω, ℝ))) V := fun V => by
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

/-! ## 4. Covariance decay for a general specification -/

section Cov

variable {Lk : Type} [Fintype Lk] [DecidableEq Lk]

/-- Invariance in the `ex` form.

DERIVED: no numeral. -/
theorem ex_P {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ) (l : Lk)
    {F : (Lk → Ω) → ℝ} (hF : Continuous F) : ex σ (S.P l F) = ex σ F := by
  rw [ex_mk σ (S.cont l hF), ex_mk σ hF]
  exact hσ l ⟨F, hF⟩

#print axioms ex_P

/-- **One kernel in the covariance**: replacing `f` by `P l f` in `σ(f g)` costs at most
`v_f(l) v_g(l)`. The difference is `σ(P(f g) − P f · P g)`, the conditional covariance at `l`
(invariance and `pull`).

DERIVED: no numeral. -/
theorem cov_stepS {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ) (l : Lk)
    {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
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
theorem cov_runS {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) {g : (Lk → Ω) → ℝ} (hg : Continuous g)
    {vg : Lk → ℝ} (hvg : OscLe g vg) :
    ∀ (L : List Lk) {f : (Lk → Ω) → ℝ}, Continuous f → ∀ {v : Lk → ℝ}, OscLe f v →
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
theorem sweepS_append (S : Spec Ω Lk) :
    ∀ (L1 L2 : List Lk) (f : (Lk → Ω) → ℝ), sweepS S (L1 ++ L2) f = sweepS S L2 (sweepS S L1 f)
  | [], _, _ => rfl
  | l :: L1, L2, f => sweepS_append S L1 L2 (S.P l f)

#print axioms sweepS_append

omit [Fintype Lk] in
/-- `n` iterated sweeps along `L` are one sweep along `rep L n`.

DERIVED: `0`, `1` the recursion on `n`. -/
theorem sweepS_rep (S : Spec Ω Lk) (L : List Lk) :
    ∀ (n : ℕ) (f : (Lk → Ω) → ℝ), (sweepS S L)^[n] f = sweepS S (rep L n) f
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
theorem cov_le_weightedS {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1) (ψ : Lk → ℕ)
    (hloc : ∀ l k, C l k ≠ 0 → ψ l ≤ ψ k + 1) {f g : (Lk → Ω) → ℝ} (hf : Continuous f)
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
theorem cov_spatialS {S : Spec Ω Lk} {σ : DLRLimit.State (Lk → Ω)} (hσ : Invariant S σ)
    {C : Lk → Lk → ℝ} (hC : SInfl S C) (hC0 : ∀ l k, 0 ≤ C l k) {α θ : ℝ}
    (hrow : ∀ l, ∑ k, C l k ≤ α) (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1)
    {f g : (Lk → Ω) → ℝ} (hf : Continuous f) (hg : Continuous g) {vf vg : Lk → ℝ}
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

/-! ## 5. Truncated real spins -/

section Trunc

/-- **The spin space of the truncation at level `L`**: the interval `[-|L|, |L|]`.

DERIVED: no numeral. -/
abbrev Tsp (L : ℝ) : Type := Set.Icc (-|L|) |L|

/-- The truncated spin space is non-empty.

DERIVED: `0` the spin chosen. -/
instance (L : ℝ) : Nonempty (Tsp L) := ⟨⟨0, neg_nonpos.mpr (abs_nonneg L), abs_nonneg L⟩⟩

/-- **The truncation at level `L`**: `x` clamped to `[-|L|, |L|]`.

DERIVED: no numeral. -/
def clampL (L x : ℝ) : ℝ := max (-|L|) (min x |L|)

/-- The clamp lies in the truncated spin space.

DERIVED: `0` the sign of `|L|`. -/
theorem clampL_mem (L x : ℝ) : clampL L x ∈ Set.Icc (-|L|) |L| :=
  ⟨le_max_left _ _, max_le (by linarith [abs_nonneg L]) (min_le_right _ _)⟩

#print axioms clampL_mem

/-- The clamp is continuous.

DERIVED: no numeral. -/
theorem continuous_clampL (L : ℝ) : Continuous (clampL L) :=
  continuous_const.max (continuous_id.min continuous_const)

#print axioms continuous_clampL

/-- **The clamp moves toward zero**: `|clamp x| ≤ |x|`.

DERIVED: `0` the sign of `|L|` and `|x|`. -/
theorem abs_clampL_le (L x : ℝ) : |clampL L x| ≤ |x| := by
  unfold clampL
  have hL := abs_nonneg L
  have hx := abs_nonneg x
  rw [abs_le]
  constructor
  · exact (le_min (abs_le.mp le_rfl).1 (by linarith)).trans (le_max_right _ _)
  · exact max_le (by linarith) ((min_le_left _ _).trans (le_abs_self x))

#print axioms abs_clampL_le

/-- **The truncation error is controlled by the sixth power**: `(x − clamp x)² |L|⁴ ≤ x⁶`. Below the
level the clamp is the identity; above it `|x − clamp x| ≤ |x|` and `|L| ≤ |x|`.

DERIVED: `2`, `4`, `6 = 2 + 4` the powers; `0` the sign of `|L|`. -/
theorem sq_sub_clampL_mul_le (L x : ℝ) : (x - clampL L x) ^ 2 * |L| ^ 4 ≤ x ^ 6 := by
  have hL := abs_nonneg L
  by_cases h1 : x ≤ |L|
  · by_cases h2 : -|L| ≤ x
    · have e : clampL L x = x := by
        unfold clampL
        rw [min_eq_left h1, max_eq_right h2]
      rw [e, sub_self]
      have : (0 : ℝ) ≤ x ^ 6 := by positivity
      simpa using this
    · push_neg at h2
      have e : clampL L x = -|L| := by
        unfold clampL
        rw [min_eq_left h1, max_eq_left h2.le]
      rw [e]
      have ha : |L| ≤ -x := by linarith
      have hsq : (x - -|L|) ^ 2 ≤ x ^ 2 := by nlinarith
      have h4 : |L| ^ 4 ≤ x ^ 4 := by
        have := pow_le_pow_left₀ hL ha 4
        have e4 : (-x) ^ 4 = x ^ 4 := by ring
        rwa [e4] at this
      calc (x - -|L|) ^ 2 * |L| ^ 4 ≤ x ^ 2 * x ^ 4 :=
            mul_le_mul hsq h4 (by positivity) (by positivity)
        _ = x ^ 6 := by ring
  · push_neg at h1
    have e : clampL L x = |L| := by
      unfold clampL
      rw [min_eq_right h1.le, max_eq_right (by linarith)]
    rw [e]
    have hsq : (x - |L|) ^ 2 ≤ x ^ 2 := by nlinarith
    have h4 : |L| ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hL h1.le 4
    calc (x - |L|) ^ 2 * |L| ^ 4 ≤ x ^ 2 * x ^ 4 :=
          mul_le_mul hsq h4 (by positivity) (by positivity)
      _ = x ^ 6 := by ring

#print axioms sq_sub_clampL_mul_le

/-- The truncated spin of a real number.

DERIVED: no numeral. -/
def tspin (L x : ℝ) : Tsp L := ⟨clampL L x, clampL_mem L x⟩

/-- DERIVED: no numeral. -/
theorem continuous_tspin (L : ℝ) : Continuous (tspin L) :=
  (continuous_clampL L).subtype_mk _

#print axioms continuous_tspin

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type}

/-- **The truncated field**: each cell reading clamped at level `L`.

DERIVED: no numeral. -/
def truncMap (L : ℝ) (e : Cl → C(X, ℝ)) : C(X, Cl → Tsp L) :=
  ⟨fun U c => tspin L (e c U),
    continuous_pi fun c => (continuous_tspin L).comp (e c).continuous⟩

/-- **An affine reading of finitely many cells**: `b + Σ_{c ∈ A} w_c e_c`.

DERIVED: no numeral. -/
def affF (e : Cl → C(X, ℝ)) (A : Finset Cl) (w : Cl → ℝ) (b : ℝ) : C(X, ℝ) :=
  ⟨fun U => b + ∑ c ∈ A, w c * e c U,
    continuous_const.add (continuous_finset_sum _ fun c _ => continuous_const.mul (e c).continuous)⟩

/-- **The same affine reading of truncated spins**: `b + Σ_{c ∈ A} w_c x_c`.

DERIVED: no numeral. -/
def affT (L : ℝ) (A : Finset Cl) (w : Cl → ℝ) (b : ℝ) : C(Cl → Tsp L, ℝ) :=
  ⟨fun W => b + ∑ c ∈ A, w c * (W c : ℝ),
    continuous_const.add (continuous_finset_sum _ fun c _ =>
      continuous_const.mul (continuous_subtype_val.comp (continuous_apply c)))⟩

/-- An affine reading reads only the cells of `A`.

DERIVED: no numeral. -/
theorem affT_local (L : ℝ) (A : Finset Cl) (w : Cl → ℝ) (b : ℝ) (W W' : Cl → Tsp L)
    (h : ∀ c ∈ A, W c = W' c) : affT L A w b W = affT L A w b W' := by
  show b + ∑ c ∈ A, w c * (W c : ℝ) = b + ∑ c ∈ A, w c * (W' c : ℝ)
  rw [Finset.sum_congr rfl fun c hc => by rw [h c hc]]

#print axioms affT_local

/-- **A configuration of the box read as a configuration of the cells** through `ι`.

DERIVED: no numeral. -/
def pullC {L : ℝ} {B : Type} (ι : Cl → B) : C(B → Tsp L, Cl → Tsp L) :=
  ⟨fun W c => W (ι c), continuous_pi fun c => continuous_apply (ι c)⟩

/-- **The oscillation of an affine reading on the box**: changing the box spin at `k` moves
`b + Σ_c w_c W(ι c)` by at most `Σ_{c ∈ A, ι c = k} |w_c| · 2|L|`.

DERIVED: `2 |L|` the diameter of `[-|L|, |L|]`. -/
theorem oscLe_affPull {L : ℝ} {B : Type} [DecidableEq B] (ι : Cl → B) (A : Finset Cl)
    (w : Cl → ℝ) (b : ℝ) :
    OscLe (fun W : B → Tsp L => (affT L A w b).comp (pullC ι) W)
      (fun k => ∑ c ∈ A with ι c = k, |w c| * (2 * |L|)) := by
  intro W k g
  show |(b + ∑ c ∈ A, w c * (Function.update W k g (ι c) : ℝ))
      - (b + ∑ c ∈ A, w c * (W (ι c) : ℝ))| ≤ _
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not A (fun c => ι c = k)]
  have h0 : ∑ c ∈ A with ¬ ι c = k,
      (w c * (Function.update W k g (ι c) : ℝ) - w c * (W (ι c) : ℝ)) = 0 :=
    Finset.sum_eq_zero fun c hc => by
      rw [Function.update_of_ne (Finset.mem_filter.1 hc).2]
      ring
  rw [h0, add_zero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hx := (Function.update W k g (ι c)).2
  have hy := (W (ι c)).2
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

#print axioms oscLe_affPull

end Trunc

/-! ## 6. The truncated law and covariance decay of truncated readings -/

section Law

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

/-- **A truncated Dobrushin law of class `α` at level `L`.** Read through the field truncated at
level `L`, the state `ν` is the limit along a filter `𝒰` of states `σ_j` on finite boxes
`Fin (M j)` of truncated spins, read through cell maps `ι_j`; each `σ_j` is invariant under a
specification `S_j` with a non-negative TV influence matrix `C_j` of row sums `≤ α`; and influence
moves at most one unit of the cell distance `cd`: cells of `A` more than `d` from every cell of `A'`
lie, eventually along `𝒰`, outside the `d`-step influence neighbourhood of the image of `A'`. The
limit is asked only of readings of finitely many cells.

DERIVED: `0` the sign of `C`. -/
def TruncLaw (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (L α : ℝ) (cd : Cl → Cl → ℕ) : Prop :=
  ∃ (𝒰 : Filter ℕ) (M : ℕ → ℕ) (ι : (j : ℕ) → Cl → Fin (M j))
    (S : (j : ℕ) → Spec (Tsp L) (Fin (M j)))
    (σ : (j : ℕ) → DLRLimit.State (Fin (M j) → Tsp L))
    (Cm : (j : ℕ) → Fin (M j) → Fin (M j) → ℝ),
    𝒰.NeBot ∧ (∀ j, SInfl (S j) (Cm j)) ∧ (∀ j l k, 0 ≤ Cm j l k) ∧
    (∀ j l, ∑ k, Cm j l k ≤ α) ∧ (∀ j, Invariant (S j) (σ j)) ∧
    (∀ (A A' : Finset Cl) (d : ℕ), (∀ c ∈ A, ∀ c' ∈ A', d < cd c c') →
      ∀ᶠ j in 𝒰, ∀ c ∈ A, ι j c ∉ reach (Cm j) (A'.image (ι j)) d) ∧
    ∀ (A : Finset Cl) (H : C(Cl → Tsp L, ℝ)),
      (∀ W W' : Cl → Tsp L, (∀ c ∈ A, W c = W' c) → H W = H W') →
      Tendsto (fun j => σ j (H.comp (pullC (ι j)))) 𝒰 (𝓝 (ν (H.comp (truncMap L e))))

/-- **Covariance decay of truncated affine readings.** Under a truncated Dobrushin law of class
`α` at level `L`, for `α < θ ≤ 1`, affine readings `F = b_F + Σ_{A_F} w_F e`, `G = b_G + Σ_{A_G} w_G e`
of the truncated field with `Σ|w_F| ≤ W_F`, `Σ|w_G| ≤ W_G`, and every cell of `A_F` more than `d`
from every cell of `A_G`: `|ν(F G) − ν F ν G| ≤ W_G 2|L| θ/(θ − α) · θ^{d+1} · W_F 2|L|`
(`cov_spatialS` on each box, `oscLe_affPull`, passed to the limit).

DERIVED: `2 |L|` the diameter of the spin space; `1` the cap beyond `d` and the bound on `θ`; `0`
the signs. -/
theorem truncLaw_cov {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {L α : ℝ} {cd : Cl → Cl → ℕ}
    (hv : TruncLaw ν e L α cd) {θ : ℝ} (hα0 : 0 ≤ α) (hαθ : α < θ) (hθ1 : θ ≤ 1)
    (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ) {WF WG : ℝ}
    (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG) (d : ℕ)
    (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    |ν ((affT L AF wF bF * affT L AG wG bG).comp (truncMap L e))
      - ν ((affT L AF wF bF).comp (truncMap L e)) * ν ((affT L AG wG bG).comp (truncMap L e))|
      ≤ WG * (2 * |L|) * θ / (θ - α) * (θ ^ (d + 1) * (WF * (2 * |L|))) := by
  obtain ⟨𝒰, M, ι, S, σ, Cm, hU, hC, hC0, hrow, hinv, hrange, hL⟩ := hv
  haveI := hU
  have hθ0 : 0 ≤ θ := by linarith
  have hL0 : 0 ≤ 2 * |L| := by positivity
  have hWF0 : 0 ≤ WF := (Finset.sum_nonneg fun c _ => abs_nonneg (wF c)).trans hWF
  have hWG0 : 0 ≤ WG := (Finset.sum_nonneg fun c _ => abs_nonneg (wG c)).trans hWG
  have hlocFG : ∀ W W' : Cl → Tsp L, (∀ c ∈ AF ∪ AG, W c = W' c) →
      (affT L AF wF bF * affT L AG wG bG) W = (affT L AF wF bF * affT L AG wG bG) W' :=
    fun W W' h => by
      simp only [ContinuousMap.mul_apply]
      rw [affT_local L AF wF bF W W' fun c hc => h c (Finset.mem_union_left _ hc),
        affT_local L AG wG bG W W' fun c hc => h c (Finset.mem_union_right _ hc)]
  refine le_of_tendsto (((hL _ _ hlocFG).sub ((hL AF _ (affT_local L AF wF bF)).mul
    (hL AG _ (affT_local L AG wG bG)))).abs) ?_
  filter_upwards [hrange AF AG d hsep] with j hj
  set f : C(Fin (M j) → Tsp L, ℝ) := (affT L AF wF bF).comp (pullC (ι j)) with hfdef
  set g : C(Fin (M j) → Tsp L, ℝ) := (affT L AG wG bG).comp (pullC (ι j)) with hgdef
  have e0 : (affT L AF wF bF * affT L AG wG bG).comp (pullC (ι j)) = f * g := by
    rw [ContinuousMap.mul_comp]
  rw [e0]
  have e1 : σ j (f * g) = ex (σ j) (fun W => f W * g W) := (ex_mk (σ j) (cmul f.continuous
    g.continuous)).symm
  have e2 : σ j f = ex (σ j) f := (ex_mk (σ j) f.continuous).symm
  have e3 : σ j g = ex (σ j) g := (ex_mk (σ j) g.continuous).symm
  rw [e1, e2, e3]
  have hvf := oscLe_affPull (L := L) (ι j) AF wF bF
  have hvg := oscLe_affPull (L := L) (ι j) AG wG bG
  have hgB : ∀ k, k ∉ AG.image (ι j) → (∑ c ∈ AG with ι j c = k, |wG c| * (2 * |L|)) = 0 :=
    fun k hk => Finset.sum_eq_zero fun c hc => absurd
      (Finset.mem_image.2 ⟨c, (Finset.mem_filter.1 hc).1, (Finset.mem_filter.1 hc).2⟩) hk
  have hgV : ∀ k, (∑ c ∈ AG with ι j c = k, |wG c| * (2 * |L|)) ≤ WG * (2 * |L|) := by
    intro k
    calc (∑ c ∈ AG with ι j c = k, |wG c| * (2 * |L|))
        ≤ ∑ c ∈ AG, |wG c| * (2 * |L|) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun c _ _ => mul_nonneg (abs_nonneg _) hL0
      _ = (∑ c ∈ AG, |wG c|) * (2 * |L|) := (Finset.sum_mul _ _ _).symm
      _ ≤ WG * (2 * |L|) := mul_le_mul_of_nonneg_right hWG hL0
  have hfar : ∀ k, (∑ c ∈ AF with ι j c = k, |wF c| * (2 * |L|)) ≠ 0 →
      k ∉ reach (Cm j) (AG.image (ι j)) d := by
    intro k hk
    obtain ⟨c, hc, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    have hc' := Finset.mem_filter.1 hc
    rw [← hc'.2]
    exact hj c hc'.1
  have hc := cov_spatialS (hinv j) (hC j) (hC0 j) (hrow j) hα0 hαθ hθ1 f.continuous g.continuous
    hvf hvg (AG.image (ι j)) (mul_nonneg hWG0 hL0) hgB hgV d hfar
  refine hc.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 _))
    (div_nonneg (mul_nonneg (mul_nonneg hWG0 hL0) hθ0) (by linarith)))
  rw [Finset.sum_fiberwise AF (ι j) (fun c => |wF c| * (2 * |L|)), ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hWF hL0

#print axioms truncLaw_cov

end Law

/-! ## 7. Untruncated readings: truncation plus moments -/

section Unbounded

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {Cl : Type} [DecidableEq Cl]

open MassGap.ObserverEnergyCoarseN (state_mul_sq_le)

/-- **Cauchy–Schwarz with bounds**: `ν(f²) ≤ a²`, `ν(g²) ≤ b²` give `|ν(f g)| ≤ a b`.

DERIVED: `2` the power; `0` the signs. -/
theorem abs_state_mul_le (ν : DLRLimit.State X) (f g : C(X, ℝ)) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hf : ν (f * f) ≤ a ^ 2) (hg : ν (g * g) ≤ b ^ 2) : |ν (f * g)| ≤ a * b := by
  have h := state_mul_sq_le ν f g
  have hgg : 0 ≤ ν (g * g) := ν.nonneg _ fun x => by
    rw [ContinuousMap.mul_apply]; exact mul_self_nonneg _
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg ha hb)
  calc ν (f * g) ^ 2 ≤ ν (f * f) * ν (g * g) := h
    _ ≤ a ^ 2 * b ^ 2 := mul_le_mul hf hg hgg (sq_nonneg a)
    _ = (a * b) ^ 2 := by ring

#print axioms abs_state_mul_le

/-- **The covariance moves little under an `L²`-small change**: if `ν((f − f')²) ≤ ε_f²`,
`ν((g − g')²) ≤ ε_g²`, `ν(g²) ≤ Q_g²` and `ν(f'²) ≤ Q_f²`, the covariances of `(f, g)` and `(f', g')`
differ by at most `2 (ε_f Q_g + Q_f ε_g)`.

DERIVED: `2` counts the product term and the mean term; `1` the unit observable; `0` the signs. -/
theorem cov_perturb (ν : DLRLimit.State X) (f g f' g' : C(X, ℝ)) {εf εg Qf Qg : ℝ}
    (hεf : 0 ≤ εf) (hεg : 0 ≤ εg) (hQf : 0 ≤ Qf) (hQg : 0 ≤ Qg)
    (hdf : ν ((f - f') * (f - f')) ≤ εf ^ 2) (hdg : ν ((g - g') * (g - g')) ≤ εg ^ 2)
    (hg : ν (g * g) ≤ Qg ^ 2) (hf' : ν (f' * f') ≤ Qf ^ 2) :
    |(ν (f * g) - ν f * ν g) - (ν (f' * g') - ν f' * ν g')| ≤ 2 * (εf * Qg + Qf * εg) := by
  have h11 : ν ((1 : C(X, ℝ)) * 1) ≤ 1 ^ 2 := by rw [mul_one, ν.map_one]; norm_num
  have a1 := abs_state_mul_le ν (f - f') g hεf hQg hdf hg
  have a2 := abs_state_mul_le ν f' (g - g') hQf hεg hf' hdg
  have a3 := abs_state_mul_le ν (f - f') 1 hεf zero_le_one hdf h11
  have a4 := abs_state_mul_le ν g 1 hQg zero_le_one hg h11
  have a5 := abs_state_mul_le ν f' 1 hQf zero_le_one hf' h11
  have a6 := abs_state_mul_le ν (g - g') 1 hεg zero_le_one hdg h11
  rw [mul_one, mul_one] at a3 a4 a5 a6
  rw [ν.map_sub] at a3 a6
  have e1 : f * g = (f - f') * g + f' * (g - g') + f' * g' := by ring
  have e2 : ν (f * g) = ν ((f - f') * g) + ν (f' * (g - g')) + ν (f' * g') := by
    rw [e1, ν.map_add, ν.map_add]
  have e3 : ν f * ν g - ν f' * ν g' = (ν f - ν f') * ν g + ν f' * (ν g - ν g') := by ring
  have key : (ν (f * g) - ν f * ν g) - (ν (f' * g') - ν f' * ν g')
      = ν ((f - f') * g) + ν (f' * (g - g')) - ((ν f - ν f') * ν g + ν f' * (ν g - ν g')) := by
    rw [e2]; linarith [e3]
  rw [key]
  have b1 : |(ν f - ν f') * ν g| ≤ εf * Qg := by
    rw [abs_mul]; exact mul_le_mul a3 a4 (abs_nonneg _) hεf
  have b2 : |ν f' * (ν g - ν g')| ≤ Qf * εg := by
    rw [abs_mul]; exact mul_le_mul a5 a6 (abs_nonneg _) hQf
  calc |ν ((f - f') * g) + ν (f' * (g - g')) - ((ν f - ν f') * ν g + ν f' * (ν g - ν g'))|
      ≤ |ν ((f - f') * g)| + |ν (f' * (g - g'))|
        + (|(ν f - ν f') * ν g| + |ν f' * (ν g - ν g')|) := by
        refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ εf * Qg + Qf * εg + (εf * Qg + Qf * εg) := by linarith
    _ = 2 * (εf * Qg + Qf * εg) := by ring

#print axioms cov_perturb

/-- **Weighted Cauchy–Schwarz**: `(Σ_{c ∈ A} w_c y_c)² ≤ (Σ|w_c|)(Σ |w_c| y_c²)`.

DERIVED: `2` the power. -/
theorem sq_sum_mul_le (A : Finset Cl) (w y : Cl → ℝ) :
    (∑ c ∈ A, w c * y c) ^ 2 ≤ (∑ c ∈ A, |w c|) * ∑ c ∈ A, |w c| * y c ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A (fun c _ => abs_nonneg _)
    (fun c _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) fun c _ => by
      have : w c ^ 2 = |w c| * |w c| := by rw [← sq, sq_abs]
      nlinarith [this]

#print axioms sq_sum_mul_le

/-- **The second moment of an affine reading**: with `Σ|w| ≤ W`, `|b| ≤ B` and `ν(y_c²) ≤ μ²` for
the readings `y_c` with `|y_c| ≤ |e_c|`, `ν((b + Σ w y)²) ≤ (2 (B + W μ))²`.

DERIVED: `2` from `(b + s)² ≤ 2b² + 2s²` and its square root bound; `0` the signs. -/
theorem state_aff_sq_le (ν : DLRLimit.State X) (e y : Cl → C(X, ℝ)) (A : Finset Cl)
    (w : Cl → ℝ) (b : ℝ) {W B μ : ℝ} (hW : ∑ c ∈ A, |w c| ≤ W) (hB : |b| ≤ B) (hμ : 0 ≤ μ)
    (hy : ∀ c U, |y c U| ≤ |e c U|) (hm : ∀ c ∈ A, ν (e c * e c) ≤ μ ^ 2) :
    ν (affF y A w b * affF y A w b) ≤ (2 * (B + W * μ)) ^ 2 := by
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun c _ => abs_nonneg (w c)).trans hW
  have hB0 : 0 ≤ B := (abs_nonneg b).trans hB
  have hpt : ∀ U, (affF y A w b * affF y A w b) U
      ≤ (2 * B ^ 2 + 2 * W * ∑ c ∈ A, |w c| * (e c * e c) U) := by
    intro U
    rw [ContinuousMap.mul_apply]
    show (b + ∑ c ∈ A, w c * y c U) * (b + ∑ c ∈ A, w c * y c U) ≤ _
    have hs := sq_sum_mul_le A w (fun c => y c U)
    have hb2 : b ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg b) hB 2
    have hyy : ∑ c ∈ A, |w c| * (y c U) ^ 2 ≤ ∑ c ∈ A, |w c| * (e c * e c) U :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (by
        rw [ContinuousMap.mul_apply, ← sq, ← sq_abs (y c U), ← sq_abs (e c U)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hy c U) 2) (abs_nonneg _)
    have hS0 : 0 ≤ ∑ c ∈ A, |w c| * (e c * e c) U := Finset.sum_nonneg fun c _ =>
      mul_nonneg (abs_nonneg _) (by rw [ContinuousMap.mul_apply]; exact mul_self_nonneg _)
    have h3 : (∑ c ∈ A, w c * y c U) ^ 2 ≤ W * ∑ c ∈ A, |w c| * (e c * e c) U :=
      hs.trans (mul_le_mul hW hyy (Finset.sum_nonneg fun c _ =>
        mul_nonneg (abs_nonneg _) (sq_nonneg _)) hW0)
    nlinarith [sq_nonneg (b - ∑ c ∈ A, w c * y c U)]
  have hmono := ν.mono (f := affF y A w b * affF y A w b)
    (g := (2 * B ^ 2) • (1 : C(X, ℝ)) + (2 * W) • ∑ c ∈ A, |w c| • (e c * e c)) fun U => by
      have := hpt U
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one, ContinuousMap.coe_sum, Finset.sum_apply]
      linarith
  rw [ν.map_add, ν.map_smul, ν.map_one, ν.map_smul, ν.map_sum] at hmono
  simp only [ν.map_smul] at hmono
  have hsum : ∑ c ∈ A, |w c| * ν (e c * e c) ≤ W * μ ^ 2 :=
    calc ∑ c ∈ A, |w c| * ν (e c * e c) ≤ ∑ c ∈ A, |w c| * μ ^ 2 :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hm c hc) (abs_nonneg _)
      _ = (∑ c ∈ A, |w c|) * μ ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ W * μ ^ 2 := mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  calc ν (affF y A w b * affF y A w b) ≤ 2 * B ^ 2 * 1 + 2 * W * ∑ c ∈ A, |w c| * ν (e c * e c) :=
        hmono
    _ ≤ 2 * B ^ 2 + 2 * W * (W * μ ^ 2) := by nlinarith
    _ ≤ (2 * (B + W * μ)) ^ 2 := by nlinarith [mul_nonneg hB0 (mul_nonneg hW0 hμ)]

#print axioms state_aff_sq_le

/-- **The truncation error of an affine reading**: with `Σ|w| ≤ W`, `L ≠ 0` and `ν(e_c⁶) ≤ μ₆²`,
`ν((F − F_L)²) ≤ (W μ₆ / L²)²`, `F_L` the reading of the field truncated at `L`
(`sq_sub_clampL_mul_le`, `sq_sum_mul_le`).

DERIVED: `2`, `4`, `6` the powers; `0` the signs. -/
theorem state_trunc_err_le (ν : DLRLimit.State X) (e : Cl → C(X, ℝ)) (A : Finset Cl)
    (w : Cl → ℝ) (b : ℝ) {L W μ6 : ℝ} (hL : L ≠ 0) (hW : ∑ c ∈ A, |w c| ≤ W) (hμ : 0 ≤ μ6)
    (hm : ∀ c ∈ A, ν (e c ^ 6) ≤ μ6 ^ 2) :
    ν ((affF e A w b - (affT L A w b).comp (truncMap L e))
        * (affF e A w b - (affT L A w b).comp (truncMap L e)))
      ≤ (W * μ6 * (L ^ 2)⁻¹) ^ 2 := by
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun c _ => abs_nonneg (w c)).trans hW
  have hL4 : 0 < |L| ^ 4 := pow_pos (abs_pos.mpr hL) 4
  have hpt : ∀ U, ((affF e A w b - (affT L A w b).comp (truncMap L e))
      * (affF e A w b - (affT L A w b).comp (truncMap L e))) U
      ≤ (W / |L| ^ 4) * ∑ c ∈ A, |w c| * (e c ^ 6) U := by
    intro U
    have ed : (affF e A w b - (affT L A w b).comp (truncMap L e)) U
        = ∑ c ∈ A, w c * (e c U - clampL L (e c U)) := by
      show (b + ∑ c ∈ A, w c * e c U) - (b + ∑ c ∈ A, w c * clampL L (e c U)) = _
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [ContinuousMap.mul_apply, ed, ← sq]
    have hs := sq_sum_mul_le A w (fun c => e c U - clampL L (e c U))
    have hterm : ∀ c ∈ A, |w c| * (e c U - clampL L (e c U)) ^ 2
        ≤ |w c| * (e c ^ 6) U / |L| ^ 4 := fun c _ => by
      rw [le_div_iff₀ hL4, ContinuousMap.pow_apply, mul_assoc]
      exact mul_le_mul_of_nonneg_left (sq_sub_clampL_mul_le L (e c U)) (abs_nonneg _)
    have h2 : ∑ c ∈ A, |w c| * (e c U - clampL L (e c U)) ^ 2
        ≤ (∑ c ∈ A, |w c| * (e c ^ 6) U) / |L| ^ 4 := by
      rw [Finset.sum_div]; exact Finset.sum_le_sum hterm
    have h6 : 0 ≤ ∑ c ∈ A, |w c| * (e c ^ 6) U := Finset.sum_nonneg fun c _ =>
      mul_nonneg (abs_nonneg _) (by rw [ContinuousMap.pow_apply]; positivity)
    calc (∑ c ∈ A, w c * (e c U - clampL L (e c U))) ^ 2
        ≤ (∑ c ∈ A, |w c|) * ∑ c ∈ A, |w c| * (e c U - clampL L (e c U)) ^ 2 := hs
      _ ≤ W * ((∑ c ∈ A, |w c| * (e c ^ 6) U) / |L| ^ 4) :=
          mul_le_mul hW h2 (Finset.sum_nonneg fun c _ =>
            mul_nonneg (abs_nonneg _) (sq_nonneg _)) hW0
      _ = (W / |L| ^ 4) * ∑ c ∈ A, |w c| * (e c ^ 6) U := by ring
  have hmono := ν.mono (f := (affF e A w b - (affT L A w b).comp (truncMap L e))
      * (affF e A w b - (affT L A w b).comp (truncMap L e)))
    (g := (W / |L| ^ 4) • ∑ c ∈ A, |w c| • (e c ^ 6)) fun U => by
      have := hpt U
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.coe_sum, Finset.sum_apply]
      exact this
  rw [ν.map_smul, ν.map_sum] at hmono
  simp only [ν.map_smul] at hmono
  have hsum : ∑ c ∈ A, |w c| * ν (e c ^ 6) ≤ W * μ6 ^ 2 :=
    calc ∑ c ∈ A, |w c| * ν (e c ^ 6) ≤ ∑ c ∈ A, |w c| * μ6 ^ 2 :=
          Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left (hm c hc) (abs_nonneg _)
      _ = (∑ c ∈ A, |w c|) * μ6 ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ W * μ6 ^ 2 := mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  have hWL : 0 ≤ W / |L| ^ 4 := div_nonneg hW0 hL4.le
  have eL : |L| ^ 4 = (L ^ 2) ^ 2 := by rw [← sq_abs L]; ring
  calc _ ≤ W / |L| ^ 4 * ∑ c ∈ A, |w c| * ν (e c ^ 6) := hmono
    _ ≤ W / |L| ^ 4 * (W * μ6 ^ 2) := mul_le_mul_of_nonneg_left hsum hWL
    _ = (W * μ6 * (L ^ 2)⁻¹) ^ 2 := by
        rw [eL]
        have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
        field_simp

#print axioms state_trunc_err_le

/-- **Clustering of untruncated affine cell readings at one level.** If `ν` has a truncated Dobrushin
law of class `α` at level `L > 0`, `α < θ ≤ 1`, the readings `F = b_F + Σ_{A_F} w_F e` and
`G = b_G + Σ_{A_G} w_G e` have `Σ|w| ≤ W`, `|b| ≤ B`, cells separated by more than `d` in `cd`, and
every cell read has `ν(e_c²) ≤ μ₂²`, `ν(e_c⁶) ≤ μ₆²`, then
`|ν(F G) − ν F ν G| ≤ 4 W_F W_G θ²/(θ − α) · (L² θ^d) + 2 μ₆ (W_F Q_G + Q_F W_G) · L⁻²`,
`Q = 2 (B + W μ₂)` (`truncLaw_cov`, `cov_perturb`, `state_trunc_err_le`, `state_aff_sq_le`).

DERIVED: `4 = 2 · 2` the two spin diameters `2L`; `2` the power of `L`, of `θ` and the perturbation
count; `6` the moment order; `1` the bound on `θ`; `0` the signs. -/
theorem cov_affine_unbounded {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {L α : ℝ}
    {cd : Cl → Cl → ℕ} (hv : TruncLaw ν e L α cd) (hL : 0 < L) {θ : ℝ} (hα0 : 0 ≤ α)
    (hαθ : α < θ) (hθ1 : θ ≤ 1) (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ)
    {WF WG BF BG μ2 μ6 : ℝ} (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG)
    (hBF : |bF| ≤ BF) (hBG : |bG| ≤ BG) (hμ2 : 0 ≤ μ2) (hμ6 : 0 ≤ μ6)
    (hm2 : ∀ c ∈ AF ∪ AG, ν (e c * e c) ≤ μ2 ^ 2) (hm6 : ∀ c ∈ AF ∪ AG, ν (e c ^ 6) ≤ μ6 ^ 2)
    (d : ℕ) (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
      ≤ 4 * WF * WG * θ ^ 2 / (θ - α) * (L ^ 2 * θ ^ d)
        + 2 * μ6 * (WF * (2 * (BG + WG * μ2)) + 2 * (BF + WF * μ2) * WG) * (L ^ 2)⁻¹ := by
  have hWF0 : 0 ≤ WF := (Finset.sum_nonneg fun c _ => abs_nonneg (wF c)).trans hWF
  have hWG0 : 0 ≤ WG := (Finset.sum_nonneg fun c _ => abs_nonneg (wG c)).trans hWG
  have hBF0 : 0 ≤ BF := (abs_nonneg bF).trans hBF
  have hBG0 : 0 ≤ BG := (abs_nonneg bG).trans hBG
  have hθ0 : 0 < θ := lt_of_le_of_lt hα0 hαθ
  have hLi : 0 ≤ (L ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg L)
  have hmF2 : ∀ c ∈ AF, ν (e c * e c) ≤ μ2 ^ 2 := fun c hc => hm2 c (Finset.mem_union_left _ hc)
  have hmG2 : ∀ c ∈ AG, ν (e c * e c) ≤ μ2 ^ 2 := fun c hc => hm2 c (Finset.mem_union_right _ hc)
  have hmF6 : ∀ c ∈ AF, ν (e c ^ 6) ≤ μ6 ^ 2 := fun c hc => hm6 c (Finset.mem_union_left _ hc)
  have hmG6 : ∀ c ∈ AG, ν (e c ^ 6) ≤ μ6 ^ 2 := fun c hc => hm6 c (Finset.mem_union_right _ hc)
  have htr := truncLaw_cov hv hα0 hαθ hθ1 AF AG wF wG bF bG hWF hWG d hsep
  rw [ContinuousMap.mul_comp] at htr
  -- the truncated reading is the affine reading of the clamped cells
  have eT : ∀ (A : Finset Cl) (w : Cl → ℝ) (b : ℝ),
      (affT L A w b).comp (truncMap L e)
        = affF (fun c => (⟨fun U => clampL L (e c U),
            (continuous_clampL L).comp (e c).continuous⟩ : C(X, ℝ))) A w b := fun A w b => by
    ext U; rfl
  have hy : ∀ c U, |(⟨fun U => clampL L (e c U), (continuous_clampL L).comp (e c).continuous⟩ :
      C(X, ℝ)) U| ≤ |e c U| := fun c U => abs_clampL_le L (e c U)
  have hQG := state_aff_sq_le ν e e AG wG bG hWG hBG hμ2 (fun c U => le_rfl) hmG2
  have hQF' := state_aff_sq_le ν e _ AF wF bF hWF hBF hμ2 hy hmF2
  rw [← eT] at hQF'
  have hεF := state_trunc_err_le ν e AF wF bF hL.ne' hWF hμ6 hmF6
  have hεG := state_trunc_err_le ν e AG wG bG hL.ne' hWG hμ6 hmG6
  have hp := cov_perturb ν (affF e AF wF bF) (affF e AG wG bG)
    ((affT L AF wF bF).comp (truncMap L e)) ((affT L AG wG bG).comp (truncMap L e))
    (mul_nonneg (mul_nonneg hWF0 hμ6) hLi) (mul_nonneg (mul_nonneg hWG0 hμ6) hLi)
    (by positivity) (by positivity) hεF hεG hQG hQF'
  have e1 : WG * (2 * |L|) * θ / (θ - α) * (θ ^ (d + 1) * (WF * (2 * |L|)))
      = 4 * WF * WG * θ ^ 2 / (θ - α) * (L ^ 2 * θ ^ d) := by
    rw [pow_succ, ← sq_abs L]; ring
  rw [e1] at htr
  have e2 : 2 * (WF * μ6 * (L ^ 2)⁻¹ * (2 * (BG + WG * μ2))
      + 2 * (BF + WF * μ2) * (WG * μ6 * (L ^ 2)⁻¹))
      = 2 * μ6 * (WF * (2 * (BG + WG * μ2)) + 2 * (BF + WF * μ2) * WG) * (L ^ 2)⁻¹ := by ring
  rw [e2] at hp
  have := abs_sub_abs_le_abs_sub
    (ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG))
    (ν ((affT L AF wF bF).comp (truncMap L e) * (affT L AG wG bG).comp (truncMap L e))
      - ν ((affT L AF wF bF).comp (truncMap L e)) * ν ((affT L AG wG bG).comp (truncMap L e)))
  linarith

#print axioms cov_affine_unbounded

/-- **The level that balances truncation and tail**: with `u = √θ`, `t = √u` and `L = t^{−d}`,
`L² θ^d = u^d` and `L⁻² = u^d`.

DERIVED: `2`, `4` the powers of the square roots; `0` the sign of `θ`. -/
theorem level_balance {θ : ℝ} (hθ : 0 < θ) (d : ℕ) :
    ((Real.sqrt (Real.sqrt θ))⁻¹ ^ d) ^ 2 * θ ^ d = Real.sqrt θ ^ d ∧
      (((Real.sqrt (Real.sqrt θ))⁻¹ ^ d) ^ 2)⁻¹ = Real.sqrt θ ^ d := by
  have hu : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ
  have ht2 : Real.sqrt (Real.sqrt θ) ^ 2 = Real.sqrt θ := Real.sq_sqrt hu.le
  have hu2 : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ.le
  have eL : ((Real.sqrt (Real.sqrt θ))⁻¹ ^ d) ^ 2 = (Real.sqrt θ)⁻¹ ^ d := by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow, ht2]
  constructor
  · have hθu : (Real.sqrt θ)⁻¹ * θ = Real.sqrt θ := by
      rw [inv_mul_eq_iff_eq_mul₀ hu.ne', ← sq, hu2]
    rw [eL, ← mul_pow, hθu]
  · rw [eL, ← inv_pow, inv_inv]

#print axioms level_balance

/-- **Clustering of untruncated affine cell readings at rate `√θ`.** Under a truncated Dobrushin law
of class `α` at the level `L_d = θ^{−d/4}` (`(√√θ)^{−d}`), with the hypotheses of
`cov_affine_unbounded`, `|ν(F G) − ν F ν G| ≤ K (√θ)^d` with
`K = 4 W_F W_G θ²/(θ − α) + 2 μ₆ (W_F Q_G + Q_F W_G)`, independent of `d`.

DERIVED: `4`, `2` as in `cov_affine_unbounded`; `0` the sign of `θ`; `6` the sixth moment that controls
the truncation error (`sq_sub_clampL_mul_le`). -/
theorem cov_affine_rate {ν : DLRLimit.State X} {e : Cl → C(X, ℝ)} {α θ : ℝ}
    {cd : Cl → Cl → ℕ} (d : ℕ)
    (hv : TruncLaw ν e ((Real.sqrt (Real.sqrt θ))⁻¹ ^ d) α cd) (hα0 : 0 ≤ α)
    (hαθ : α < θ) (hθ1 : θ ≤ 1) (AF AG : Finset Cl) (wF wG : Cl → ℝ) (bF bG : ℝ)
    {WF WG BF BG μ2 μ6 : ℝ} (hWF : ∑ c ∈ AF, |wF c| ≤ WF) (hWG : ∑ c ∈ AG, |wG c| ≤ WG)
    (hBF : |bF| ≤ BF) (hBG : |bG| ≤ BG) (hμ2 : 0 ≤ μ2) (hμ6 : 0 ≤ μ6)
    (hm2 : ∀ c ∈ AF ∪ AG, ν (e c * e c) ≤ μ2 ^ 2) (hm6 : ∀ c ∈ AF ∪ AG, ν (e c ^ 6) ≤ μ6 ^ 2)
    (hsep : ∀ c ∈ AF, ∀ c' ∈ AG, d < cd c c') :
    |ν (affF e AF wF bF * affF e AG wG bG) - ν (affF e AF wF bF) * ν (affF e AG wG bG)|
      ≤ (4 * WF * WG * θ ^ 2 / (θ - α)
        + 2 * μ6 * (WF * (2 * (BG + WG * μ2)) + 2 * (BF + WF * μ2) * WG)) * Real.sqrt θ ^ d := by
  have hθ : 0 < θ := lt_of_le_of_lt hα0 hαθ
  have hL : 0 < (Real.sqrt (Real.sqrt θ))⁻¹ ^ d :=
    pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hθ))) d
  have h := cov_affine_unbounded hv hL hα0 hαθ hθ1 AF AG wF wG bF bG hWF hWG hBF hBG hμ2 hμ6
    hm2 hm6 d hsep
  obtain ⟨b1, b2⟩ := level_balance hθ d
  rw [b1, b2] at h
  linarith

#print axioms cov_affine_rate

end Unbounded

end MassGap.DobrushinUnbounded
