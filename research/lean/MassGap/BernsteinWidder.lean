import Mathlib
import MassGap.ShellMeasure
import MassGap.GNSHilbert

/-!
# MassGap.BernsteinWidder — a bounded continuous reflection-positive correlator is a Laplace transform

`ShellMeasure.laplace_reflPos` proves the elementary half of the Bernstein–Widder theorem,
`LaplaceRep C → ReflPos C`. This module proves the converse for a bare function, in the form
`ShellLorentz` step (c) reads: a function `C` that is continuous and bounded on `(0, ∞)` and
reflection positive (`Σᵢⱼ cᵢ cⱼ C(tᵢ + tⱼ) ≥ 0`) is, on `τ > 0`, the Laplace transform of a finite
positive measure on `[0, ∞)` (`bernsteinWidder`). Declarations are in the namespace
`MassGap.BernsteinWidder`.

Mathlib at this pin has no Bernstein–Widder theorem and no Hausdorff moment theorem
(`AbsolutelyMonotoneOn` is defined, its representation theorem is not). The proof here is the
Widder–Nelson operator route, built from the tree's own machinery.

## The route

1. The kernel `(s, t) ↦ C(s + t)` is a positive semidefinite form on finitely supported functions on
   the positive times (`kerSum`, `PK`); positivity is `ReflPos` re-indexed over a finite support
   (`reflPos_finset`). A one-dimensional summand carrying the form `x y` is added (`PV`), so the
   `GNSHilbert` construction, which asks for a unit vector fixed by the step, applies as it stands;
   the summand is fixed by every shift and orthogonal to the kernel part.
2. The shift by `a ≥ 0`, `δ_s ↦ δ_{s + a}` (`shT`), is symmetric for the form, and its Gram identity
   `⟨f, T_a f⟩ = ⟨T_{a/2} f, T_{a/2} f⟩` makes it positive (`positiveTransfer`).
3. It is a contraction (`kf_contract`): with `y_n = ⟨T_{2^n a} f, T_{2^n a} f⟩`, Cauchy–Schwarz gives
   `y_n² ≤ ⟨f, f⟩ y_{n+1}`, boundedness of `C` gives `y_n ≤ M (Σ|f|)²`, and a sequence with both
   properties has `y_0 ≤ ⟨f, f⟩` (`le_of_sq_le_mul`): otherwise `y_n ≥ ⟨f, f⟩ + 2ⁿ (y_0 − ⟨f, f⟩)`
   grows without bound. This is a doubling argument of the kind used by Widder and Nelson; boundedness enters through this
   contraction and, directly, in bounding `C(2/(n+1))` in `exists_vacuum`.
4. `GNSHilbert.opT` extends each shift to a positive self-adjoint contraction `O a` on one Hilbert
   space; `O a * O b = O (a + b)` (`O_mul`), so `O ((1/2)^m)` are the dyadic square roots of `O 1` and
   equal `(O 1)^((1/2)^m)` (`ContinuumTimeGroup.eq_powT_of_sq`, uniqueness of positive square roots).
5. The kernel is antitone (`antitone_C`), so `C(2/(n+1))` converges and the vectors `δ_{1/(n+1)}`
   are Cauchy; their limit `Ω` has `Re ⟪Ω, O a Ω⟫ = C(a)` for every `a > 0`, by continuity of `C`
   (`exists_vacuum`).
6. On dyadic times `Re ⟪Ω, (O 1)^τ Ω⟫ = C(τ)`; both sides are continuous on `τ > 0`
   (`ContinuumTimeGroup.continuousAt_powT`), so they agree on `τ > 0` (`eq_powT_inner`), and
   `ShellMeasure.powT_laplaceRep` (the spectral theorem for one vector, `cfc` with
   Riesz–Markov–Kakutani) gives the measure: the rate measure of `Ω` for `O 1`.

## Contents

* `bernsteinWidder`: `ReflPos C`, `C` continuous on `(0, ∞)` and bounded there ⇒ `LaplaceRep C`.
* `reflPos_iff_laplaceRep`: under the same two regularity hypotheses the two are equivalent.
* `laplaceRep_bounded`: a Laplace transform of a finite measure on `[0, ∞)` is bounded on `τ > 0`.
* Load tests. `expKernel_reflPos` and `expKernel_laplaceRep`: `e^{−Eτ}`, `E ≥ 0`, meets the three
  hypotheses (reflection positivity proved directly, as a square) and the theorem returns a
  representation; `expKernel_dirac` exhibits the Dirac measure `δ_E`. `bump_excluded`: `τ e^{−τ}` is
  continuous and bounded by `1` on `(0, ∞)`, fails `ReflPos`, and so has no representation; the
  theorem's exclusion of it is carried by reflection positivity alone. `growth_excluded`: `e^{τ}` is
  reflection positive and continuous but unbounded, and has no representation; boundedness is
  load-bearing.

## What does not follow, plainly

* Uniqueness of the representing measure is `SmallClose.laplaceRep_unique`, and at the exponential load test
  the measure is `δ_E` (`SmallClose.expKernel_measure_eq_dirac`).
* The theorem is about a bare real function. Identifying a momentum-`p` Schwinger function as such a
  function with the three hypotheses is not built here; that is the input `ShellLorentz` step (c)
  supplies to it.
* Continuity on `(0, ∞)` is used twice: to read `C(a)` as the limit of `C(2/(n+1) + a)` when building
  `Ω`, and to pass from dyadic times to all times. No version without it is stated.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.BernsteinWidder

open Real Filter Topology MeasureTheory Set
open scoped NNReal
open MassGap.ShellMeasure (ReflPos LaplaceRep laplace_reflPos powT_laplaceRep bumpKernel
  bumpKernel_not_reflPos integrable_exp_of_Iio)
open MassGap.ContinuumTimeGroup (powT powT_nat_mul eq_powT_of_sq continuousAt_powT)
open MassGap.GNSHilbert (Pre H opT)

noncomputable section

/-! ## 1. The kernel form on finitely supported functions of the positive times -/

/-- **The positive times.** DERIVED: `0` the open end. -/
abbrev Pt : Type := {t : ℝ // 0 < t}

/-- **The shift** of a positive time by `a ≥ 0`. DERIVED: no numeral. -/
def sh (a : ℝ≥0) (s : Pt) : Pt := ⟨s.1 + a, add_pos_of_pos_of_nonneg s.2 a.2⟩

/-- DERIVED: no numeral. -/
@[simp] theorem sh_val (a : ℝ≥0) (s : Pt) : (sh a s).1 = s.1 + a := rfl

/-- **Shifts compose by adding.** DERIVED: no numeral. -/
theorem sh_comp (a b : ℝ≥0) : sh a ∘ sh b = sh (a + b) := by
  funext s
  apply Subtype.ext
  simp only [Function.comp_apply, sh_val, NNReal.coe_add]
  ring

/-- **The zero shift is the identity.** DERIVED: `0` the shift. -/
theorem sh_zero : sh 0 = id := by
  funext s
  apply Subtype.ext
  simp

/-- **The kernel sum** `Σₛ Σₜ f(s) g(t) K(s, t)` over the supports. DERIVED: no numeral. -/
def kerSum (K : Pt → Pt → ℝ) (f g : Pt →₀ ℝ) : ℝ :=
  f.sum fun s x => g.sum fun t y => x * y * K s t

/-- DERIVED: no numeral. -/
theorem kerSum_add_left (K : Pt → Pt → ℝ) (f f' g : Pt →₀ ℝ) :
    kerSum K (f + f') g = kerSum K f g + kerSum K f' g := by
  unfold kerSum
  refine Finsupp.sum_add_index' (fun s => by simp) (fun s x x' => ?_)
  simp only [add_mul]
  exact Finsupp.sum_add

/-- DERIVED: no numeral. -/
theorem kerSum_smul_left (K : Pt → Pt → ℝ) (r : ℝ) (f g : Pt →₀ ℝ) :
    kerSum K (r • f) g = r * kerSum K f g := by
  unfold kerSum
  rw [Finsupp.sum_smul_index' (fun s => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun s _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun t _ => ?_
  rw [smul_eq_mul]
  ring

/-- DERIVED: no numeral. -/
theorem kerSum_symm {K : Pt → Pt → ℝ} (hK : ∀ s t, K s t = K t s) (f g : Pt →₀ ℝ) :
    kerSum K f g = kerSum K g f := by
  unfold kerSum
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun t _ => Finsupp.sum_congr fun s _ => ?_
  rw [hK]
  ring

/-- DERIVED: no numeral. -/
theorem kerSum_congr {K K' : Pt → Pt → ℝ} (h : ∀ s t, K s t = K' s t) (f g : Pt →₀ ℝ) :
    kerSum K f g = kerSum K' f g := by
  have : K = K' := funext fun s => funext fun t => h s t
  rw [this]

/-- DERIVED: `0` the zero function. -/
theorem kerSum_zero_left (K : Pt → Pt → ℝ) (g : Pt →₀ ℝ) : kerSum K 0 g = 0 := by
  unfold kerSum
  exact Finsupp.sum_zero_index

/-- **A shift on the left moves into the kernel.** DERIVED: no numeral. -/
theorem kerSum_mapDomain_left (K : Pt → Pt → ℝ) (φ : Pt → Pt) (f g : Pt →₀ ℝ) :
    kerSum K (Finsupp.mapDomain φ f) g = kerSum (fun s t => K (φ s) t) f g := by
  unfold kerSum
  refine Finsupp.sum_mapDomain_index (fun s => by simp) (fun s x x' => ?_)
  simp only [add_mul]
  exact Finsupp.sum_add

/-- **A shift on the right moves into the kernel.** DERIVED: no numeral. -/
theorem kerSum_mapDomain_right (K : Pt → Pt → ℝ) (φ : Pt → Pt) (f g : Pt →₀ ℝ) :
    kerSum K f (Finsupp.mapDomain φ g) = kerSum (fun s t => K s (φ t)) f g := by
  unfold kerSum
  refine Finsupp.sum_congr fun s _ => ?_
  exact Finsupp.sum_mapDomain_index (fun t => by simp) (fun t y y' => by ring)

/-- **Two point masses** read the kernel. DERIVED: `1` the unit mass. -/
theorem kerSum_single (K : Pt → Pt → ℝ) (p q : Pt) :
    kerSum K (Finsupp.single p 1) (Finsupp.single q 1) = K p q := by
  unfold kerSum
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  ring

/-- **`ReflPos` over a finite support**: the Gram sum at times `τ s > 0` indexed by a finset.
DERIVED: `0` the sign. -/
theorem reflPos_finset {C : ℝ → ℝ} (hC : ReflPos C) (S : Finset Pt) (w τ : Pt → ℝ)
    (hτ : ∀ s, 0 < τ s) : 0 ≤ ∑ s ∈ S, ∑ t ∈ S, w s * w t * C (τ s + τ t) := by
  have e : ∀ F : Pt → ℝ, ∑ s ∈ S, F s = ∑ i, F (S.equivFin.symm i) := fun F =>
    (Finset.sum_coe_sort S F).symm.trans (Equiv.sum_comp S.equivFin.symm (fun x : S => F x)).symm
  have key : ∑ s ∈ S, ∑ t ∈ S, w s * w t * C (τ s + τ t)
      = ∑ i, ∑ j, w (S.equivFin.symm i) * w (S.equivFin.symm j)
          * C (τ (S.equivFin.symm i) + τ (S.equivFin.symm j)) := by
    simp only [e]
  rw [key]
  exact hC S.card (fun i => w (S.equivFin.symm i)) (fun i => τ (S.equivFin.symm i)) fun i => hτ _

/-- **The kernel sum is positive semidefinite** at any positive time map. DERIVED: `0` the sign. -/
theorem kerSum_nonneg {C : ℝ → ℝ} (hC : ReflPos C) (τ : Pt → ℝ) (hτ : ∀ s, 0 < τ s)
    (f : Pt →₀ ℝ) : 0 ≤ kerSum (fun s t => C (τ s + τ t)) f f := by
  unfold kerSum Finsupp.sum
  exact reflPos_finset hC f.support f τ hτ

/-- **The kernel sum is bounded** by `M (Σ|f|)²` when the kernel is bounded by `M`.
DERIVED: `2` the square. -/
theorem kerSum_le {K : Pt → Pt → ℝ} {M : ℝ} (hK : ∀ s t, |K s t| ≤ M) (f : Pt →₀ ℝ) :
    kerSum K f f ≤ M * (∑ s ∈ f.support, |f s|) ^ 2 := by
  unfold kerSum Finsupp.sum
  calc ∑ s ∈ f.support, ∑ t ∈ f.support, f s * f t * K s t
      ≤ ∑ s ∈ f.support, ∑ t ∈ f.support, |f s| * |f t| * M := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => ?_
        calc f s * f t * K s t ≤ |f s * f t * K s t| := le_abs_self _
          _ = |f s| * |f t| * |K s t| := by rw [abs_mul, abs_mul]
          _ ≤ |f s| * |f t| * M := mul_le_mul_of_nonneg_left (hK s t) (by positivity)
    _ = M * (∑ s ∈ f.support, |f s|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring

/-- **The kernel** `C(s + t)`. DERIVED: no numeral. -/
def kf (C : ℝ → ℝ) : Pt → Pt → ℝ := fun s t => C (s.1 + t.1)

/-- **The shifted kernel** `C(s + t + c)`. DERIVED: no numeral. -/
def kc (C : ℝ → ℝ) (c : ℝ≥0) : Pt → Pt → ℝ := fun s t => C (s.1 + t.1 + c)

/-- DERIVED: no numeral. -/
theorem kf_shift_both (C : ℝ → ℝ) (a b : ℝ≥0) (f g : Pt →₀ ℝ) :
    kerSum (kf C) (Finsupp.mapDomain (sh a) f) (Finsupp.mapDomain (sh b) g)
      = kerSum (kc C (a + b)) f g := by
  rw [kerSum_mapDomain_left, kerSum_mapDomain_right]
  refine kerSum_congr (fun s t => ?_) f g
  simp only [kf, kc, sh_val, NNReal.coe_add]
  congr 1
  ring

/-- DERIVED: no numeral. -/
theorem kf_shift_right (C : ℝ → ℝ) (b : ℝ≥0) (f g : Pt →₀ ℝ) :
    kerSum (kf C) f (Finsupp.mapDomain (sh b) g) = kerSum (kc C b) f g := by
  rw [kerSum_mapDomain_right]
  refine kerSum_congr (fun s t => ?_) f g
  simp only [kf, kc, sh_val]
  congr 1
  ring

/-- DERIVED: no numeral. -/
theorem kf_shift_left (C : ℝ → ℝ) (a : ℝ≥0) (f g : Pt →₀ ℝ) :
    kerSum (kf C) (Finsupp.mapDomain (sh a) f) g = kerSum (kc C a) f g := by
  rw [kerSum_mapDomain_left]
  refine kerSum_congr (fun s t => ?_) f g
  simp only [kf, kc, sh_val]
  congr 1
  ring

/-- **The shifted kernel is positive semidefinite**: `C(s + t + c) = C((s + c/2) + (t + c/2))`.
DERIVED: `0` the sign; `2` halves the shift. -/
theorem kc_nonneg {C : ℝ → ℝ} (hC : ReflPos C) (c : ℝ≥0) (f : Pt →₀ ℝ) :
    0 ≤ kerSum (kc C c) f f := by
  rw [kerSum_congr (K := kc C c) (K' := fun s t => C ((s.1 + (c : ℝ) / 2) + (t.1 + (c : ℝ) / 2)))
    (fun s t => by simp only [kc]; congr 1; ring) f f]
  exact kerSum_nonneg hC (fun s => s.1 + (c : ℝ) / 2)
    (fun s => add_pos_of_pos_of_nonneg s.2 (by positivity)) f

/-- **The shifted kernel is bounded by `M`.** DERIVED: `0` the sign. -/
theorem kc_le {C : ℝ → ℝ} {M : ℝ} (hM : ∀ t, 0 < t → |C t| ≤ M) (c : ℝ≥0) (f : Pt →₀ ℝ) :
    kerSum (kc C c) f f ≤ M * (∑ s ∈ f.support, |f s|) ^ 2 :=
  kerSum_le (fun s t => hM _ (add_pos_of_pos_of_nonneg (add_pos s.2 t.2) c.2)) f

/-- **The kernel form** on `Pt →₀ ℝ`, a reflection form by `ReflPos`. DERIVED: no numeral. -/
def PK (C : ℝ → ℝ) (hC : ReflPos C) : Transfer.ReflForm (Pt →₀ ℝ) where
  form := kerSum (kf C)
  form_symm f g := kerSum_symm (fun s t => by simp only [kf, add_comm]) f g
  form_add_left := kerSum_add_left _
  form_smul_left := kerSum_smul_left _
  form_nonneg f := kerSum_nonneg hC (fun s => s.1) (fun s => s.2) f

/-! ## 2. The contraction (Widder–Nelson) -/

/-- **A sequence squared below a fixed multiple of its successor and bounded above starts below the
multiple**: `y_n² ≤ p y_{n+1}`, `0 ≤ y_n ≤ K` ⇒ `y_0 ≤ p`. Otherwise `y_n ≥ p + 2ⁿ (y_0 − p)`.
DERIVED: `0` the signs and the first index; `1` the successor; `2` the square and the doubling. -/
theorem le_of_sq_le_mul {y : ℕ → ℝ} {p K : ℝ} (hp : 0 ≤ p) (hy : ∀ n, 0 ≤ y n)
    (hK : ∀ n, y n ≤ K) (hrec : ∀ n, y n ^ 2 ≤ p * y (n + 1)) : y 0 ≤ p := by
  by_contra hlt
  push_neg at hlt
  have hp0 : 0 < p := by
    rcases hp.eq_or_lt with h | h
    · exfalso
      have h1 := hrec 0
      rw [← h, zero_mul] at h1
      nlinarith [hy 0]
    · exact h
  set d := y 0 - p with hd
  have hd0 : 0 < d := by linarith
  have grow : ∀ n : ℕ, p + 2 ^ n * d ≤ y n := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_mul]; linarith
    | succ n ih =>
      have h0 : 0 ≤ p + 2 ^ n * d := add_nonneg hp (mul_nonneg (by positivity) hd0.le)
      have h1 : (p + 2 ^ n * d) ^ 2 ≤ y n ^ 2 := pow_le_pow_left₀ h0 ih 2
      have e : (p + 2 ^ n * d) ^ 2 = p * (p + 2 ^ (n + 1) * d) + (2 ^ n * d) ^ 2 := by ring
      have h2 : p * (p + 2 ^ (n + 1) * d) ≤ p * y (n + 1) := by
        nlinarith [hrec n, sq_nonneg (2 ^ n * d)]
      exact le_of_mul_le_mul_left h2 hp0
  obtain ⟨n, hn⟩ := exists_nat_gt ((K - p) / d)
  have h3 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast n.lt_two_pow_self.le
  have h4 : (n : ℝ) * d ≤ 2 ^ n * d := mul_le_mul_of_nonneg_right h3 hd0.le
  rw [div_lt_iff₀ hd0] at hn
  linarith [grow n, hK n]

/-- **The shift is a contraction for the kernel form** (Widder, Nelson): with
`y_n = ⟨T_{2ⁿ a} f, T_{2ⁿ a} f⟩`, Cauchy–Schwarz and boundedness feed `le_of_sq_le_mul`.
DERIVED: `2` the doubling of the shift; `0`, `1` the first index and the successor. -/
theorem kf_contract {C : ℝ → ℝ} (hC : ReflPos C) {M : ℝ} (hM : ∀ t, 0 < t → |C t| ≤ M)
    (a : ℝ≥0) (f : Pt →₀ ℝ) :
    kerSum (kf C) (Finsupp.mapDomain (sh a) f) (Finsupp.mapDomain (sh a) f)
      ≤ kerSum (kf C) f f := by
  rw [kf_shift_both]
  set y : ℕ → ℝ := fun n => kerSum (kc C (2 ^ n * (a + a))) f f with hy
  have hy0 : y 0 = kerSum (kc C (a + a)) f f := by simp [hy]
  rw [← hy0]
  refine le_of_sq_le_mul ((PK C hC).form_nonneg f) (fun n => kc_nonneg hC _ f)
    (fun n => kc_le hM _ f) (fun n => ?_)
  have h1 : y n = (PK C hC).form f (Finsupp.mapDomain (sh (2 ^ n * (a + a))) f) := by
    show kerSum (kc C (2 ^ n * (a + a))) f f
      = kerSum (kf C) f (Finsupp.mapDomain (sh (2 ^ n * (a + a))) f)
    rw [kf_shift_right]
  have h2 : y (n + 1) = (PK C hC).form (Finsupp.mapDomain (sh (2 ^ n * (a + a))) f)
      (Finsupp.mapDomain (sh (2 ^ n * (a + a))) f) := by
    show kerSum (kc C (2 ^ (n + 1) * (a + a))) f f = kerSum (kf C) _ _
    rw [kf_shift_both]
    congr 2
    ring
  rw [h1, h2]
  exact (PK C hC).cauchy_schwarz f _

/-! ## 3. The reflection form with a vacuum summand, and the shift as a transfer -/

/-- **The carrier**: the kernel part and a one-dimensional vacuum summand. DERIVED: no numeral. -/
abbrev V : Type := (Pt →₀ ℝ) × ℝ

/-- **The form on the carrier**: the kernel form plus `x y` on the summand.
DERIVED: no numeral. -/
def PV (C : ℝ → ℝ) (hC : ReflPos C) : Transfer.ReflForm V where
  form v w := kerSum (kf C) v.1 w.1 + v.2 * w.2
  form_symm v w := by
    rw [kerSum_symm (fun s t => by simp only [kf, add_comm]) v.1 w.1, mul_comm]
  form_add_left u v w := by
    simp only [Prod.fst_add, Prod.snd_add, kerSum_add_left]
    ring
  form_smul_left r v w := by
    simp only [Prod.smul_fst, Prod.smul_snd, kerSum_smul_left, smul_eq_mul]
    ring
  form_nonneg v := add_nonneg (kerSum_nonneg hC (fun s => s.1) (fun s => s.2) v.1)
    (mul_self_nonneg _)

/-- **The shift on the carrier**: `mapDomain (sh a)` on the kernel part, identity on the summand.
DERIVED: no numeral. -/
def shT (a : ℝ≥0) : V →ₗ[ℝ] V := (Finsupp.lmapDomain ℝ ℝ (sh a)).prodMap LinearMap.id

/-- DERIVED: no numeral. -/
@[simp] theorem shT_apply (a : ℝ≥0) (v : V) :
    shT a v = (Finsupp.mapDomain (sh a) v.1, v.2) := rfl

/-- DERIVED: no numeral. -/
theorem shT_comp (a b : ℝ≥0) (v : V) : shT a (shT b v) = shT (a + b) v := by
  simp only [shT_apply, ← sh_comp, Finsupp.mapDomain_comp]

/-- DERIVED: `0` the shift. -/
theorem shT_zero (v : V) : shT 0 v = v := by
  simp [shT_apply, sh_zero, Finsupp.mapDomain_id]

/-- **The shift as a transfer**: symmetric, contractive (`kf_contract`), fixing the summand vector
`(0, 1)` of unit form. DERIVED: `0` the empty kernel part; `1` the unit summand vector. -/
def D (C : ℝ → ℝ) (hC : ReflPos C) {M : ℝ} (hM : ∀ t, 0 < t → |C t| ≤ M) (a : ℝ≥0) :
    Transfer.TransferData V where
  toReflForm := PV C hC
  T := shT a
  vac := (0, 1)
  T_symm v w := by
    show kerSum (kf C) (Finsupp.mapDomain (sh a) v.1) w.1 + v.2 * w.2
      = kerSum (kf C) v.1 (Finsupp.mapDomain (sh a) w.1) + v.2 * w.2
    rw [kf_shift_left, kf_shift_right]
  T_contract v := by
    show kerSum (kf C) (Finsupp.mapDomain (sh a) v.1) (Finsupp.mapDomain (sh a) v.1) + v.2 * v.2
      ≤ kerSum (kf C) v.1 v.1 + v.2 * v.2
    linarith [kf_contract hC hM a v.1]
  T_vac := by simp [shT_apply]
  vac_norm := by
    show kerSum (kf C) 0 0 + 1 * 1 = 1
    rw [kerSum_zero_left]
    ring

/-- **The shift is a positive transfer**: `⟨v, T_a v⟩ = ⟨T_{a/2} v, T_{a/2} v⟩`.
DERIVED: `2` halves the shift. -/
theorem positiveTransfer (C : ℝ → ℝ) (hC : ReflPos C) {M : ℝ} (hM : ∀ t, 0 < t → |C t| ≤ M)
    (a : ℝ≥0) : GNSHilbert.PositiveTransfer (D C hC hM a) := by
  refine GNSHilbert.positiveTransfer_of_gram (D C hC hM a) (shT (a / 2)) fun v => ?_
  show kerSum (kf C) v.1 (Finsupp.mapDomain (sh a) v.1) + v.2 * v.2
    = kerSum (kf C) (Finsupp.mapDomain (sh (a / 2)) v.1) (Finsupp.mapDomain (sh (a / 2)) v.1)
      + v.2 * v.2
  rw [kf_shift_right, kf_shift_both, add_halves]

/-! ## 4. The operators on one Hilbert space -/

section Operators

variable {C : ℝ → ℝ} (hC : ReflPos C) {M : ℝ} (hM : ∀ t, 0 < t → |C t| ≤ M)

/-- **The shift on the Hilbert space** `H (PV C hC)`: `GNSHilbert.opT` of the transfer `D a`.
All the `D a` share the form `PV C hC`, so all act on one space. DERIVED: no numeral. -/
def O (a : ℝ≥0) : H (PV C hC) →L[ℂ] H (PV C hC) := opT (D C hC hM a)

/-- **The shift on the pre-Hilbert space**, `GNSHilbert.cTL (D a)` typed on `Pre (PV C hC)`.
DERIVED: no numeral. -/
def cTP (a : ℝ≥0) : Pre (PV C hC) →L[ℂ] Pre (PV C hC) := GNSHilbert.cTL (D C hC hM a)

/-- DERIVED: no numeral. -/
theorem cTP_fst (a : ℝ≥0) (z : Pre (PV C hC)) :
    ((cTP hC hM a z : Pre (PV C hC)) : V × V).1 = shT a (z : V × V).1 := rfl

/-- DERIVED: no numeral. -/
theorem cTP_snd (a : ℝ≥0) (z : Pre (PV C hC)) :
    ((cTP hC hM a z : Pre (PV C hC)) : V × V).2 = shT a (z : V × V).2 := rfl

/-- DERIVED: no numeral. -/
theorem O_coe (a : ℝ≥0) (z : Pre (PV C hC)) :
    O hC hM a (z : H (PV C hC)) = ((cTP hC hM a z : Pre (PV C hC)) : H (PV C hC)) :=
  GNSHilbert.opT_coe (D C hC hM a) z

/-- **The semigroup law**: `O a * O b = O (a + b)`, by density. DERIVED: no numeral. -/
theorem O_mul (a b : ℝ≥0) : O hC hM a * O hC hM b = O hC hM (a + b) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((O hC hM a * O hC hM b).continuous) (O hC hM (a + b)).continuous
  | ih z =>
    rw [ContinuousLinearMap.mul_apply, O_coe, O_coe, O_coe]
    congr 1
    refine GNSHilbert.Pre.ext ?_ ?_
    · rw [cTP_fst, cTP_fst, cTP_fst]
      exact shT_comp a b _
    · rw [cTP_snd, cTP_snd, cTP_snd]
      exact shT_comp a b _

/-- DERIVED: `0` the shift; `1` the identity. -/
theorem O_zero : O hC hM 0 = 1 := by
  ext x
  exact GNSHilbert.opT_eq_id_of_T_eq_id (D C hC hM 0) shT_zero x

/-- DERIVED: `0` the order's bottom. -/
theorem O_nonneg (a : ℝ≥0) : 0 ≤ O hC hM a :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (GNSHilbert.isPositive_opT (D C hC hM a) (positiveTransfer C hC hM a))

/-- DERIVED: no numeral. -/
theorem O_selfAdjoint (a : ℝ≥0) : IsSelfAdjoint (O hC hM a) :=
  GNSHilbert.isSelfAdjoint_opT (D C hC hM a)

/-- **The spectrum lies in `[0, 1]`.** DERIVED: `0`, `1` the ends. -/
theorem spectrum_O (a : ℝ≥0) : spectrum ℝ (O hC hM a) ⊆ Icc 0 1 := fun x hx =>
  ⟨GNSHilbert.spectrum_opT_nonneg (D C hC hM a) (positiveTransfer C hC hM a) hx,
    (GNSHilbert.spectrum_opT_subset_unit_interval (D C hC hM a) hx).2⟩

/-- DERIVED: `0` the empty product. -/
theorem O_nat_mul (q : ℝ≥0) (n : ℕ) : O hC hM (n * q) = O hC hM q ^ n := by
  induction n with
  | zero => simp [O_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, ← O_mul, ih, pow_succ]

/-- **The dyadic shifts are real powers of `O 1`**: `O (n (1/2)^m) = (O 1)^(n (1/2)^m)`.
DERIVED: `1/2` the dyadic ratio; `1` the unit time. -/
theorem O_dyadic (m n : ℕ) :
    O hC hM ((n : ℝ≥0) * (1 / 2) ^ m) = powT (O hC hM 1) ((n : ℝ) * (1 / 2 : ℝ) ^ m) := by
  have hb : O hC hM ((1 / 2) ^ m) = powT (O hC hM 1) ((1 / 2 : ℝ) ^ m) := eq_powT_of_sq (O_selfAdjoint hC hM 1) (spectrum_O hC hM 1)
    (fun k => O hC hM ((1 / 2) ^ k)) (by simp) (fun k => O_nonneg hC hM _)
    (fun k => by
      rw [O_mul]
      congr 1
      apply NNReal.eq
      push_cast
      ring) m
  rw [O_nat_mul, hb, ← powT_nat_mul (O_selfAdjoint hC hM 1) (spectrum_O hC hM 1) (by positivity) n]

/-! ## 5. The point vectors and the limit vector -/

/-- **The point vector** `δ_p` in the Hilbert space. DERIVED: `1` the unit mass; `0` the empty
summand and imaginary part. -/
def e (p : Pt) : H (PV C hC) :=
  ((GNSHilbert.Pre.ofPair (A := V) (PV C hC) ((Finsupp.single p 1, 0) : V) (0 : V) : Pre (PV C hC))
    : H (PV C hC))

/-- **The shift moves the point.** DERIVED: no numeral. -/
theorem O_e (a : ℝ≥0) (p : Pt) : O hC hM a (e hC p) = e hC (sh a p) := by
  rw [e, O_coe, e]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · rw [cTP_fst]
    simp [shT_apply, Finsupp.mapDomain_single, GNSHilbert.Pre.ofPair]
  · rw [cTP_snd]
    exact map_zero _

/-- **Two point vectors read the kernel**: `Re ⟪δ_p, δ_q⟫ = C(p + q)`. DERIVED: no numeral. -/
theorem re_inner_e (p q : Pt) : RCLike.re (inner ℂ (e hC p) (e hC q)) = C (p.1 + q.1) := by
  rw [e, e, GNSHilbert.inner_coe, RCLike.re_to_complex, OSPositivity.cform_re]
  show (kerSum (kf C) (Finsupp.single p 1) (Finsupp.single q 1) + 0 * 0)
    + (kerSum (kf C) 0 0 + 0 * 0) = _
  rw [kerSum_single, kerSum_zero_left]
  simp [kf]

/-- **The kernel is antitone** on `(0, ∞)`: `C(t) ≤ C(s)` for `0 < s ≤ t`. From Cauchy–Schwarz and
the contraction. DERIVED: `2` halves the time; `0` the sign. -/
theorem antitone_C (hC : ReflPos C) (hM : ∀ t, 0 < t → |C t| ≤ M) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) : C t ≤ C s := by
  set p : Pt := ⟨s / 2, half_pos hs⟩ with hp
  set a : ℝ≥0 := ⟨t - s, sub_nonneg.mpr hst⟩ with ha
  have hq : (Finsupp.mapDomain (sh a) (Finsupp.single p 1) : Pt →₀ ℝ)
      = Finsupp.single (sh a p) 1 := Finsupp.mapDomain_single
  have k1 : (PK C hC).form (Finsupp.single p 1) (Finsupp.single p 1) = C s := by
    show kerSum (kf C) _ _ = _
    rw [kerSum_single]
    show C (s / 2 + s / 2) = C s
    congr 1
    ring
  have k2 : (PK C hC).form (Finsupp.single p 1) (Finsupp.single (sh a p) 1) = C t := by
    show kerSum (kf C) _ _ = _
    rw [kerSum_single]
    show C (s / 2 + (s / 2 + (t - s))) = C t
    congr 1
    ring
  have k3 : (PK C hC).form (Finsupp.single (sh a p) 1) (Finsupp.single (sh a p) 1) ≤ C s := by
    have h := kf_contract hC hM a (Finsupp.single p 1)
    rw [hq] at h
    rw [← k1]
    exact h
  have k5 := (PK C hC).form_nonneg (Finsupp.single p 1)
  have hcs := (PK C hC).cauchy_schwarz (Finsupp.single p 1) (Finsupp.single (sh a p) 1)
  rw [k1, k2] at hcs
  rw [k1] at k5
  nlinarith [mul_le_mul_of_nonneg_left k3 k5]

/-- **The squared distance of two point vectors**: `C(2p) − 2 C(p + q) + C(2q)`.
DERIVED: `2` the cross term and the square. -/
theorem dist_e_sq (p q : Pt) :
    dist (e hC p) (e hC q) ^ 2 = C (p.1 + p.1) - 2 * C (p.1 + q.1) + C (q.1 + q.1) := by
  rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    norm_sq_eq_re_inner (𝕜 := ℂ), re_inner_e,
    re_inner_e, re_inner_e]

/-- **The approach to time `0`**: `1/(n+1)`. DERIVED: `1` the unit and the shift of the index. -/
def εpt (n : ℕ) : Pt := ⟨1 / ((n : ℝ) + 1), Nat.one_div_pos_of_nat⟩

/-- **The limit vector**: the point vectors `δ_{1/(n+1)}` converge, and their limit `Ω` reads
`Re ⟪Ω, O a Ω⟫ = C(a)` at every `a > 0`. DERIVED: `0` the sign; `1`, `2` as in `εpt` and the
diagonal. -/
theorem exists_vacuum (hcont : ContinuousOn C (Ioi 0)) :
    ∃ Ω : H (PV C hC), ∀ a : ℝ≥0, 0 < (a : ℝ) →
      (inner ℂ Ω (O hC hM a Ω)).re = C a := by
  set u : ℕ → H (PV C hC) := fun n => e hC (εpt n)
  set c : ℕ → ℝ := fun n => C ((εpt n).1 + (εpt n).1)
  have hε_anti : ∀ {n m : ℕ}, n ≤ m → (εpt m).1 ≤ (εpt n).1 := by
    intro n m h
    show 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1)
    gcongr
  have hc_mono : Monotone c := fun n m h =>
    antitone_C hC hM (add_pos (εpt m).2 (εpt m).2) (by linarith [hε_anti h])
  have hc_bdd : BddAbove (range c) := ⟨M, by
    rintro _ ⟨n, rfl⟩
    exact (le_abs_self _).trans (hM _ (add_pos (εpt n).2 (εpt n).2))⟩
  have hc_cauchy : CauchySeq c := (tendsto_atTop_ciSup hc_mono hc_bdd).cauchySeq
  have hdist : ∀ n m, dist (u n) (u m) ^ 2 ≤ |c m - c n| := by
    intro n m
    rcases le_total n m with h | h
    · have hmid : c n ≤ C ((εpt n).1 + (εpt m).1) :=
        antitone_C hC hM (add_pos (εpt n).2 (εpt m).2)
          (by linarith [hε_anti h])
      have := dist_e_sq hC (εpt n) (εpt m)
      rw [abs_of_nonneg (by linarith [hc_mono h])]
      simp only [u, c] at hmid ⊢
      linarith
    · have hmid : c m ≤ C ((εpt n).1 + (εpt m).1) :=
        antitone_C hC hM (add_pos (εpt n).2 (εpt m).2)
          (by linarith [hε_anti h])
      have := dist_e_sq hC (εpt n) (εpt m)
      rw [abs_of_nonpos (by linarith [hc_mono h])]
      simp only [u, c] at hmid ⊢
      linarith
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff] at hc_cauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc_cauchy (ε ^ 2) (pow_pos hε 2)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hdist m n
    have h2 := hN n hn m hm
    rw [Real.dist_eq] at h2
    have h3 : dist (u m) (u n) ^ 2 < ε ^ 2 := lt_of_le_of_lt h1 h2
    nlinarith [dist_nonneg (x := u m) (y := u n)]
  obtain ⟨Ω, hΩ⟩ := cauchySeq_tendsto_of_complete hu
  refine ⟨Ω, fun a ha => ?_⟩
  have hlim1 : Tendsto (fun n => (inner ℂ (u n) (O hC hM a (u n))).re) atTop
      (𝓝 (inner ℂ Ω (O hC hM a Ω)).re) :=
    (Complex.continuous_re.tendsto _).comp
      (hΩ.inner (((O hC hM a).continuous.tendsto Ω).comp hΩ))
  have hval : ∀ n, (inner ℂ (u n) (O hC hM a (u n))).re
      = C ((εpt n).1 + (εpt n).1 + a) := by
    intro n
    simp only [u]
    rw [O_e, ← RCLike.re_to_complex, re_inner_e]
    simp only [sh_val]
    congr 1
    ring
  have hε0 : Tendsto (fun n => (εpt n).1 + (εpt n).1 + (a : ℝ)) atTop (𝓝 (a : ℝ)) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).add_const (a : ℝ)
    simpa [εpt] using h
  have hlim2 : Tendsto (fun n => (inner ℂ (u n) (O hC hM a (u n))).re) atTop (𝓝 (C a)) := by
    simp only [hval]
    exact ((hcont.continuousAt (Ioi_mem_nhds ha)).tendsto).comp hε0
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The kernel is a vector correlator of `O 1`**: `C(τ) = Re ⟪Ω, (O 1)^τ Ω⟫` for every `τ > 0`.
Dyadic times by `O_dyadic`, all times by continuity of both sides. DERIVED: `1/2` the dyadic ratio;
`0` the sign; `1` the unit time. -/
theorem eq_powT_inner (hcont : ContinuousOn C (Ioi 0)) :
    ∃ Ω : H (PV C hC), ∀ τ : ℝ, 0 < τ →
      C τ = (inner ℂ Ω (powT (O hC hM 1) τ Ω)).re := by
  obtain ⟨Ω, hΩ⟩ := exists_vacuum hC hM hcont
  refine ⟨Ω, fun τ hτ => ?_⟩
  set F : ℝ → ℝ := fun s => (inner ℂ Ω (powT (O hC hM 1) s Ω)).re
  have hdy : ∀ m n : ℕ, 0 < (n : ℝ) * (1 / 2 : ℝ) ^ m →
      F ((n : ℝ) * (1 / 2 : ℝ) ^ m) = C ((n : ℝ) * (1 / 2 : ℝ) ^ m) := by
    intro m n hpos
    have h := hΩ ((n : ℝ≥0) * (1 / 2) ^ m) (by exact_mod_cast hpos)
    rw [O_dyadic] at h
    simp only [F]
    rw [h]
    exact congrArg C (by norm_num)
  set d : ℕ → ℝ := fun k => (⌈τ / (1 / 2 : ℝ) ^ k⌉₊ : ℝ) * (1 / 2 : ℝ) ^ k
  have hlo : ∀ k, τ ≤ d k := by
    intro k
    have h := Nat.le_ceil (τ / (1 / 2 : ℝ) ^ k)
    rwa [div_le_iff₀ (by positivity)] at h
  have hup : ∀ k, d k ≤ τ + (1 / 2 : ℝ) ^ k := by
    intro k
    have h := Nat.ceil_lt_add_one (div_nonneg hτ.le (by positivity) : 0 ≤ τ / (1 / 2 : ℝ) ^ k)
    have hq : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have := mul_lt_mul_of_pos_right h hq
    rw [add_mul, div_mul_cancel₀ τ hq.ne', one_mul] at this
    exact this.le
  have hd : Tendsto d atTop (𝓝 τ) := by
    have hupper : Tendsto (fun k => τ + (1 / 2 : ℝ) ^ k) atTop (𝓝 τ) := by
      have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ) atTop (𝓝 τ)).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hlo hup
  have hFC : ∀ k, F (d k) = C (d k) := fun k =>
    hdy k _ (lt_of_lt_of_le hτ (hlo k))
  have hFcont : ContinuousAt F τ :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_const.inner ((continuousAt_powT (spectrum_O hC hM 1) hτ).clm_apply
        continuousAt_const))
  have hCcont : ContinuousAt C τ := hcont.continuousAt (Ioi_mem_nhds hτ)
  have h1 : Tendsto (fun k => F (d k)) atTop (𝓝 (F τ)) := hFcont.tendsto.comp hd
  have h2 : Tendsto (fun k => F (d k)) atTop (𝓝 (C τ)) := by
    simp only [hFC]
    exact hCcont.tendsto.comp hd
  exact (tendsto_nhds_unique h1 h2).symm

end Operators

/-! ## 6. The theorem -/

/-- **Bernstein–Widder**: a function continuous and bounded on `(0, ∞)` and reflection positive is,
on `τ > 0`, the Laplace transform of a finite positive measure on `[0, ∞)`. The measure is the rate
measure of the limit vector `Ω` for the unit shift `O 1`. DERIVED: `0` the sign; `1` the unit time. -/
theorem bernsteinWidder {C : ℝ → ℝ} (hC : ReflPos C) (hcont : ContinuousOn C (Ioi 0))
    (hbd : ∃ M, ∀ t, 0 < t → |C t| ≤ M) : LaplaceRep C := by
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨Ω, hΩ⟩ := eq_powT_inner hC hM hcont
  obtain ⟨σ, hfin, h0, hrep⟩ := powT_laplaceRep (spectrum_O hC hM 1) Ω
  exact ⟨σ, hfin, h0, fun τ hτ => (hΩ τ hτ).trans (hrep τ hτ)⟩

/-- **A Laplace transform of a finite measure on `[0, ∞)` is bounded** on `τ > 0`, by the total
mass. DERIVED: `0` the sign; `1` the bound of the integrand. -/
theorem laplaceRep_bounded {C : ℝ → ℝ} (h : LaplaceRep C) : ∃ M, ∀ t, 0 < t → |C t| ≤ M := by
  obtain ⟨σ, hfin, h0, hrep⟩ := h
  refine ⟨(σ univ).toReal, fun t ht => ?_⟩
  have hae : ∀ᵐ E ∂σ, 0 ≤ E := by
    rw [ae_iff]
    have : {E : ℝ | ¬ 0 ≤ E} = Iio 0 := by ext E; simp [not_le]
    rw [this]; exact h0
  have hb : ∀ᵐ E ∂σ, ‖Real.exp (-(t * E))‖ ≤ 1 := by
    filter_upwards [hae] with E hE
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have := norm_integral_le_of_norm_le_const hb
  rw [hrep t ht, ← Real.norm_eq_abs]
  simpa [Measure.real] using this

/-- **The equivalence**: for a function continuous and bounded on `(0, ∞)`, reflection positivity
and the Laplace form are the same. DERIVED: `0` the sign. -/
theorem reflPos_iff_laplaceRep {C : ℝ → ℝ} (hcont : ContinuousOn C (Ioi 0))
    (hbd : ∃ M, ∀ t, 0 < t → |C t| ≤ M) : ReflPos C ↔ LaplaceRep C :=
  ⟨fun h => bernsteinWidder h hcont hbd, laplace_reflPos⟩

/-! ## 7. Load tests -/

/-- **A single exponential** `e^{−τE}`. DERIVED: no numeral. -/
def expKernel (E τ : ℝ) : ℝ := Real.exp (-(τ * E))

/-- **It is reflection positive**, as a square: `Σᵢⱼ cᵢ cⱼ e^{−(tᵢ+tⱼ)E} = (Σᵢ cᵢ e^{−tᵢE})²`.
No measure is used. DERIVED: `0` the sign; `2` the square. -/
theorem expKernel_reflPos (E : ℝ) : ReflPos (expKernel E) := by
  intro n c t _
  have h : ∑ i, ∑ j, c i * c j * expKernel E (t i + t j)
      = (∑ i, c i * Real.exp (-(t i * E))) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [expKernel, show -((t i + t j) * E) = -(t i * E) + -(t j * E) by ring, Real.exp_add]
    ring
  rw [h]
  exact sq_nonneg _

/-- **The theorem applies to it** when `E ≥ 0`: continuous, bounded by `1`, reflection positive.
DERIVED: `0` the sign of `E`; `1` the bound. -/
theorem expKernel_laplaceRep {E : ℝ} (hE : 0 ≤ E) : LaplaceRep (expKernel E) :=
  bernsteinWidder (expKernel_reflPos E)
    (by show ContinuousOn (fun τ : ℝ => Real.exp (-(τ * E))) (Ioi 0); fun_prop) ⟨1, fun t ht => by
    rw [expKernel, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)⟩

/-- **Its Dirac representation** `δ_E`, exhibited directly. DERIVED: `0` the sign of `E`. -/
theorem expKernel_dirac {E : ℝ} (hE : 0 ≤ E) :
    (Measure.dirac E) (Iio 0) = 0 ∧
      ∀ τ, 0 < τ → expKernel E τ = ∫ x, Real.exp (-(τ * x)) ∂(Measure.dirac E) := by
  refine ⟨by simp [not_lt.mpr hE], fun τ _ => ?_⟩
  rw [integral_dirac]
  rfl

/-- **The bump kernel is excluded by reflection positivity alone**: `τ e^{−τ}` is continuous and
bounded by `1` on `(0, ∞)`, is not reflection positive, and has no Laplace representation.
DERIVED: `1` the bound (`τ ≤ e^τ`); `0` the sign. -/
theorem bump_excluded :
    ContinuousOn bumpKernel (Ioi 0) ∧ (∀ t, 0 < t → |bumpKernel t| ≤ 1) ∧
      ¬ ReflPos bumpKernel ∧ ¬ LaplaceRep bumpKernel := by
  have hcont : ContinuousOn bumpKernel (Ioi 0) := by
    show ContinuousOn (fun τ : ℝ => τ * Real.exp (-τ)) (Ioi 0); fun_prop
  have hbd : ∀ t, 0 < t → |bumpKernel t| ≤ 1 := by
    intro t ht
    have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
    have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-t)
    rw [bumpKernel, abs_of_pos (mul_pos ht h3)]
    nlinarith [mul_le_mul_of_nonneg_right h1 h3.le]
  refine ⟨hcont, hbd, bumpKernel_not_reflPos, fun h => ?_⟩
  exact bumpKernel_not_reflPos ((reflPos_iff_laplaceRep hcont ⟨1, hbd⟩).mpr h)

/-- **Boundedness is load-bearing**: `e^{τ}` (the exponential at `E = −1`) is reflection positive
and continuous but unbounded, and has no Laplace representation. DERIVED: `1` the rate `E = −1` is a
counterexample choice; `0` the sign. -/
theorem growth_excluded :
    ReflPos (expKernel (-1)) ∧ ContinuousOn (expKernel (-1)) (Ioi 0) ∧
      ¬ LaplaceRep (expKernel (-1)) := by
  refine ⟨expKernel_reflPos _,
    by show ContinuousOn (fun τ : ℝ => Real.exp (-(τ * -1))) (Ioi 0); fun_prop, fun h => ?_⟩
  obtain ⟨M, hM⟩ := laplaceRep_bounded h
  have ht : (0 : ℝ) < |M| + 1 := by positivity
  have h1 := hM _ ht
  rw [expKernel, abs_of_pos (Real.exp_pos _)] at h1
  have h2 : |M| + 1 + 1 ≤ Real.exp (|M| + 1) := Real.add_one_le_exp _
  have h3 : -((|M| + 1) * -1) = |M| + 1 := by ring
  rw [h3] at h1
  linarith [le_abs_self M]

end

end MassGap.BernsteinWidder

#print axioms MassGap.BernsteinWidder.reflPos_finset
#print axioms MassGap.BernsteinWidder.kerSum_nonneg
#print axioms MassGap.BernsteinWidder.kerSum_le
#print axioms MassGap.BernsteinWidder.le_of_sq_le_mul
#print axioms MassGap.BernsteinWidder.kf_contract
#print axioms MassGap.BernsteinWidder.positiveTransfer
#print axioms MassGap.BernsteinWidder.O_mul
#print axioms MassGap.BernsteinWidder.O_zero
#print axioms MassGap.BernsteinWidder.spectrum_O
#print axioms MassGap.BernsteinWidder.O_dyadic
#print axioms MassGap.BernsteinWidder.O_e
#print axioms MassGap.BernsteinWidder.re_inner_e
#print axioms MassGap.BernsteinWidder.antitone_C
#print axioms MassGap.BernsteinWidder.dist_e_sq
#print axioms MassGap.BernsteinWidder.exists_vacuum
#print axioms MassGap.BernsteinWidder.eq_powT_inner
#print axioms MassGap.BernsteinWidder.bernsteinWidder
#print axioms MassGap.BernsteinWidder.laplaceRep_bounded
#print axioms MassGap.BernsteinWidder.reflPos_iff_laplaceRep
#print axioms MassGap.BernsteinWidder.expKernel_reflPos
#print axioms MassGap.BernsteinWidder.expKernel_laplaceRep
#print axioms MassGap.BernsteinWidder.expKernel_dirac
#print axioms MassGap.BernsteinWidder.bump_excluded
#print axioms MassGap.BernsteinWidder.growth_excluded
