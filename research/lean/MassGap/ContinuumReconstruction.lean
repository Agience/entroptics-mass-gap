import Mathlib
import MassGap.ContinuumSchwinger
import MassGap.GNSHilbert
import MassGap.SchwarzIteration

noncomputable section

/-!
# MassGap.ContinuumReconstruction — Hilbert space, vacuum and transfer operators from the limit
Schwinger functions

The Osterwalder–Schrader reconstruction, run on the continuum Schwinger functions
`ContinuumSchwinger.contS hN ρ` through the axiom-free GNS construction of `GNSHilbert` (not through
`WightmanData.os_reconstruction_wightman`). The inputs are the renormalisation data `ρ`, the uniform
bound `hB : UniformBound hN ρ` (proved at bounded data, in particular for the bare fields, where the
limit is expected to be degenerate: `continuum_reconstruction_bare`) and the reflection
compatibility `hR : ρ.ReflCompat τ`.

## The construction

* `Amod N τ = PosMono N τ →₀ ℝ`: finite real combinations of positive-time monomials.
* `formFun hN ρ τ c d = ∑_{P,Q} c_P d_Q S(θP ∪ Q)`. `contReflForm`: a `Transfer.ReflForm` — bilinear
  from the `Finsupp` sums, symmetric from `kern_symm`, positive semidefinite from
  `contS_gram_nonneg` (reflection positivity of the limit).
* `Tm hN τ m`: translation of every positive-time monomial forward in time by the dyadic step
  `dySpacing N m` in direction `τ`. `Tm_symm`: `⟨Tc, d⟩ = ⟨c, Td⟩`, from dyadic translation
  invariance of the limit. `Tm_contract`: `⟨Tc, Tc⟩ ≤ ⟨c, c⟩`, by
  `SchwarzIteration.contract_of_bounded_orbit` with the translation-uniform bound
  `exists_abs_contS_le`.
* `contTransfer`: a `Transfer.TransferData`, with vacuum the empty monomial, of norm one since
  `S(∅) = 1`. `positiveTransfer`: `⟨c, T_m c⟩ = ⟨T_{m+1} c, T_{m+1} c⟩ ≥ 0`, because
  `T_m = T_{m+1} ∘ T_{m+1}` on `Amod` (`Tm_half`).

`GNSHilbert` gives the complete Hilbert space, the unit vacuum and the transfer operator for each
dyadic time step: self-adjoint, spectrum in `[0, 1]`, fixing the vacuum. `inner_vecOf`: the inner
product of the vectors of two monomials is the Schwinger function `S(θP ∪ Q)`.

## Scope

No Hamiltonian as a generator is built: the transfer operators are given at the dyadic times
`dySpacing N m`, with `T_m = T_{m+1}²` on the pre-Hilbert module. No bound on the spectrum of `opT`
off the vacuum is derived here. Clustering of the Schwinger functions follows from
`ContinuumSchwinger.UniformClustering` (`contS_cluster_tendsto`) or from
`WeakCouplingWindow.FixedWindowDecay`
(`ContinuumCluster.contS_cluster_of_fixedWindowDecay`), hypotheses not proved here. Rotation
covariance needs `ContinuumSchwinger.RotationInvariant`, not proved.
The statements do not assert that the Hilbert space has dimension above one.
-/

namespace MassGap.ContinuumReconstruction

open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger Filter
open scoped Topology

variable {N : ℕ}

/-! ## 1. Monomial geometry -/

section Geometry

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem timeVec_add (N m : ℕ) (τ : Fin 4) (a b : ℤ) :
    timeVec N m τ a + timeVec N m τ b = timeVec N m τ (a + b) := by
  unfold timeVec
  rw [site_add, axisVec_add]

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension; `0` is the zero vector. -/
theorem timeVec_zero (N m : ℕ) (τ : Fin 4) : timeVec N m τ 0 = 0 := by
  unfold timeVec
  rw [axisVec_zero, site_zero]

/-- DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem timeVec_self (N m : ℕ) (τ : Fin 4) (n : ℤ) : timeVec N m τ n τ = dySpacing N m * n := by
  simp [timeVec, site, axisVec]

/-- The time reflection of a time vector is the opposite time vector.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem reflR_timeVec (N m : ℕ) (τ : Fin 4) (n : ℤ) :
    reflR τ (timeVec N m τ n) = timeVec N m τ (-n) := by
  funext i
  by_cases h : i = τ
  · subst h
    simp [reflR, timeVec, site, axisVec]
  · simp [reflR, timeVec, site, axisVec, h, Function.update_of_ne h]

/-- Two successive half steps are one step.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is the unit time step; the half step is
level `m + 1`. -/
theorem timeVec_one_add (N m : ℕ) (τ : Fin 4) :
    timeVec N (m + 1) τ 1 + timeVec N (m + 1) τ 1 = timeVec N m τ 1 := by
  unfold timeVec
  funext i
  simp only [Pi.add_apply, site]
  rw [← dySpacing_mul_pow N (by omega : m ≤ m + 1), Nat.add_sub_cancel_left, pow_one]
  ring

/-- DERIVED: `0` is the zero vector. -/
theorem Mono.shift_zero (P : Mono N) : Mono.shift 0 P = P := by
  obtain ⟨n, F⟩ := P
  exact congrArg (Sigma.mk n) (funext fun i => by
    show ((F i).1, (F i).2.translate 0) = F i
    rw [TestFn.translate_zero])

/-- DERIVED: `4` in `Fin 4 → ℝ` is the spacetime dimension. -/
theorem Mono.shift_shift (v w : Fin 4 → ℝ) (P : Mono N) :
    Mono.shift w (Mono.shift v P) = Mono.shift (v + w) P := by
  obtain ⟨n, F⟩ := P
  exact congrArg (Sigma.mk n) (funext fun i => by
    show ((F i).1, ((F i).2.translate v).translate w) = ((F i).1, (F i).2.translate (v + w))
    rw [TestFn.translate_translate])

/-- The forward time step of a positive-time monomial by `dySpacing N m` in direction `τ`.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. The body steps
by one unit time step, whose time component is non-negative. -/
def PosMono.shift (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) (P : PosMono N τ) : PosMono N τ :=
  ⟨Mono.shift (timeVec N m τ 1) P.1, fun i => PosTime.translate (P.2 i) (by
    rw [timeVec_self]
    exact mul_nonneg (dySpacing_pos (one_le_of_ne_zero hN) m).le (by norm_num))⟩

/-- DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension. -/
theorem PosMono.shift_iterate (hN : N ≠ 0) (τ : Fin 4) (m n : ℕ) (P : PosMono N τ) :
    ((PosMono.shift hN τ m)^[n] P).1 = Mono.shift (timeVec N m τ n) P.1 := by
  induction n with
  | zero =>
    show P.1 = Mono.shift (timeVec N m τ ((0 : ℕ) : ℤ)) P.1
    rw [Nat.cast_zero, timeVec_zero, Mono.shift_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show Mono.shift (timeVec N m τ 1) ((PosMono.shift hN τ m)^[n] P).1 = _
    rw [ih, Mono.shift_shift, timeVec_add, Nat.cast_succ]

/-- Two half steps are one step, on positive-time monomials.

DERIVED: `0` is the excluded colour count; `4` in `Fin 4` is the spacetime dimension; `1` is the
half-step offset. -/
theorem PosMono.shift_half (hN : N ≠ 0) (τ : Fin 4) (m : ℕ) (P : PosMono N τ) :
    PosMono.shift hN τ (m + 1) (PosMono.shift hN τ (m + 1) P) = PosMono.shift hN τ m P := by
  apply Subtype.ext
  show Mono.shift (timeVec N (m + 1) τ 1) (Mono.shift (timeVec N (m + 1) τ 1) P.1)
    = Mono.shift (timeVec N m τ 1) P.1
  rw [Mono.shift_shift, timeVec_one_add]

/-- The reflected shifted monomial against `Q` is the unshifted pair with `Q` shifted, translated
back by one step.

DERIVED: `4` in `Fin 4` is the spacetime dimension; `1` is the unit step. -/
theorem pairFam_shift (m : ℕ) (τ : Fin 4) (P Q : Mono N) :
    pairFam τ (Mono.shift (timeVec N m τ 1) P) Q
      = fun x => ((pairFam τ P (Mono.shift (timeVec N m τ 1) Q) x).1,
          (pairFam τ P (Mono.shift (timeVec N m τ 1) Q) x).2.translate (timeVec N m τ (-1))) := by
  funext x
  cases x with
  | inl i =>
    show ((P.2 i).1.refl τ, ((P.2 i).2.translate (timeVec N m τ 1)).reflect τ)
      = ((P.2 i).1.refl τ, ((P.2 i).2.reflect τ).translate (timeVec N m τ (-1)))
    rw [TestFn.reflect_translate, reflR_timeVec]
  | inr j =>
    show Q.2 j
      = ((Q.2 j).1, ((Q.2 j).2.translate (timeVec N m τ 1)).translate (timeVec N m τ (-1)))
    rw [TestFn.translate_translate, timeVec_add, add_neg_cancel, timeVec_zero,
      TestFn.translate_zero]

/-- Both monomials shifted by `n` steps: a per-factor dyadic translate of the unshifted pair.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
theorem pairFam_shiftN (m : ℕ) (τ : Fin 4) (n : ℤ) (P Q : Mono N) :
    pairFam τ (Mono.shift (timeVec N m τ n) P) (Mono.shift (timeVec N m τ n) Q)
      = fun x => ((pairFam τ P Q x).1, (pairFam τ P Q x).2.translate
          (site (dySpacing N m)
            (Sum.elim (fun _ => axisVec τ (-n)) (fun _ => axisVec τ n) x))) := by
  funext x
  cases x with
  | inl i =>
    show ((P.2 i).1.refl τ, ((P.2 i).2.translate (timeVec N m τ n)).reflect τ)
      = ((P.2 i).1.refl τ, ((P.2 i).2.reflect τ).translate (timeVec N m τ (-n)))
    rw [TestFn.reflect_translate, reflR_timeVec]
  | inr j => rfl

end Geometry

/-! ## 2. The reflection form on positive-time combinations -/

section Form

variable (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)

/-- Finite real combinations of positive-time monomials.

DERIVED: `4` in `Fin 4` is the spacetime dimension. -/
abbrev Amod (N : ℕ) (τ : Fin 4) : Type := PosMono N τ →₀ ℝ

/-- The kernel on positive-time monomials.

DERIVED: no numeral. -/
noncomputable def kernP (P Q : PosMono N τ) : ℝ := kern hN ρ τ P.1 Q.1

/-- DERIVED: no numeral. -/
theorem kernP_symm (hR : ρ.ReflCompat τ) (P Q : PosMono N τ) :
    kernP hN ρ τ P Q = kernP hN ρ τ Q P :=
  kern_symm hN ρ τ hR P.1 Q.1

/-- **The time step is symmetric for the kernel**: `S(θ(TP) ∪ Q) = S(θP ∪ TQ)`, by dyadic
translation invariance of the limit.

DERIVED: `1` is the unit step. -/
theorem kernP_shift (m : ℕ) (P Q : PosMono N τ) :
    kernP hN ρ τ (PosMono.shift hN τ m P) Q = kernP hN ρ τ P (PosMono.shift hN τ m Q) := by
  show kern hN ρ τ (Mono.shift (timeVec N m τ 1) P.1) Q.1
    = kern hN ρ τ P.1 (Mono.shift (timeVec N m τ 1) Q.1)
  unfold kern
  rw [pairFam_shift]
  exact contS_translate hN ρ _ m (axisVec τ (-1))

#print axioms kernP_shift

/-- **The reflection form** `⟨c, d⟩ = ∑_{P,Q} c_P d_Q S(θP ∪ Q)`.

DERIVED: no numeral. -/
noncomputable def formFun (c d : Amod N τ) : ℝ :=
  c.sum (fun P a => d.sum (fun Q b => a * b * kernP hN ρ τ P Q))

/-- DERIVED: no numeral. -/
theorem formFun_add_left (c c' d : Amod N τ) :
    formFun hN ρ τ (c + c') d = formFun hN ρ τ c d + formFun hN ρ τ c' d := by
  unfold formFun
  exact Finsupp.sum_add_index' (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])

/-- DERIVED: no numeral. -/
theorem formFun_smul_left (r : ℝ) (c d : Amod N τ) :
    formFun hN ρ τ (r • c) d = r * formFun hN ρ τ c d := by
  unfold formFun
  have h1 : (r • c).sum (fun P a => d.sum (fun Q b => a * b * kernP hN ρ τ P Q))
      = c.sum (fun P a => d.sum (fun Q b => (r • a) * b * kernP hN ρ τ P Q)) :=
    Finsupp.sum_smul_index' (fun P => by simp)
  rw [h1, Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun P _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun Q _ => ?_)
  rw [smul_eq_mul]
  ring

/-- DERIVED: no numeral. -/
theorem formFun_symm (hR : ρ.ReflCompat τ) (c d : Amod N τ) :
    formFun hN ρ τ c d = formFun hN ρ τ d c := by
  unfold formFun
  rw [Finsupp.sum_comm c d (fun P a Q b => a * b * kernP hN ρ τ P Q)]
  refine Finsupp.sum_congr (fun Q _ => Finsupp.sum_congr (fun P _ => ?_))
  simp only [kernP_symm hN ρ τ hR P Q]
  ring

/-- **Positivity of the form** is the reflection positivity of the limit.

DERIVED: `0` is the sign. -/
theorem formFun_nonneg (hB : UniformBound hN ρ) (hR : ρ.ReflCompat τ) (c : Amod N τ) :
    0 ≤ formFun hN ρ τ c c := by
  show 0 ≤ ∑ P ∈ c.support, ∑ Q ∈ c.support, c P * c Q * kern hN ρ τ P.1 Q.1
  exact contS_gram_nonneg hN ρ hB τ hR c.support (fun P => c P)

/-- DERIVED: `0` is the zero combination. -/
theorem formFun_zero_left (d : Amod N τ) : formFun hN ρ τ 0 d = 0 := by
  unfold formFun
  exact Finsupp.sum_zero_index

/-- DERIVED: `0` is the zero combination. -/
theorem formFun_zero_right (c : Amod N τ) : formFun hN ρ τ c 0 = 0 := by
  simp [formFun]

/-- DERIVED: no numeral. -/
theorem formFun_single (P Q : PosMono N τ) (a b : ℝ) :
    formFun hN ρ τ (Finsupp.single P a) (Finsupp.single Q b) = a * b * kernP hN ρ τ P Q := by
  unfold formFun
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  all_goals simp

/-- **The continuum reflection form**, a `Transfer.ReflForm`.

DERIVED: no numeral. -/
noncomputable def contReflForm (hB : UniformBound hN ρ) (hR : ρ.ReflCompat τ) :
    Transfer.ReflForm (Amod N τ) where
  form := formFun hN ρ τ
  form_symm := formFun_symm hN ρ τ hR
  form_add_left := formFun_add_left hN ρ τ
  form_smul_left := formFun_smul_left hN ρ τ
  form_nonneg := formFun_nonneg hN ρ τ hB hR

/-- DERIVED: no numeral. -/
theorem formFun_mapDomain_left (g : PosMono N τ → PosMono N τ) (c d : Amod N τ) :
    formFun hN ρ τ (Finsupp.mapDomain g c) d
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernP hN ρ τ (g P) Q)) := by
  unfold formFun
  exact Finsupp.sum_mapDomain_index (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])

/-- DERIVED: no numeral. -/
theorem formFun_mapDomain_right (g : PosMono N τ → PosMono N τ) (c d : Amod N τ) :
    formFun hN ρ τ c (Finsupp.mapDomain g d)
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernP hN ρ τ P (g Q))) := by
  unfold formFun
  refine Finsupp.sum_congr (fun P _ => ?_)
  exact Finsupp.sum_mapDomain_index (fun Q => by simp)
    (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

/-- DERIVED: no numeral. -/
theorem formFun_mapDomain (g : PosMono N τ → PosMono N τ) (c d : Amod N τ) :
    formFun hN ρ τ (Finsupp.mapDomain g c) (Finsupp.mapDomain g d)
      = c.sum (fun P a => d.sum (fun Q b => a * b * kernP hN ρ τ (g P) (g Q))) := by
  rw [formFun_mapDomain_left]
  refine Finsupp.sum_congr (fun P _ => ?_)
  exact Finsupp.sum_mapDomain_index (fun Q => by simp)
    (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

end Form

/-! ## 3. The transfer operators -/

section TransferOp

variable (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4)

/-- **The time step at level `m`**: every positive-time monomial translated forward by
`dySpacing N m` in direction `τ`, extended linearly.

DERIVED: no numeral. -/
noncomputable def Tm (m : ℕ) : Amod N τ →ₗ[ℝ] Amod N τ :=
  Finsupp.lmapDomain ℝ ℝ (PosMono.shift hN τ m)

/-- DERIVED: no numeral. -/
theorem Tm_symm (m : ℕ) (c d : Amod N τ) :
    formFun hN ρ τ (Tm hN τ m c) d = formFun hN ρ τ c (Tm hN τ m d) := by
  show formFun hN ρ τ (Finsupp.mapDomain (PosMono.shift hN τ m) c) d
    = formFun hN ρ τ c (Finsupp.mapDomain (PosMono.shift hN τ m) d)
  rw [formFun_mapDomain_left, formFun_mapDomain_right]
  refine Finsupp.sum_congr (fun P _ => Finsupp.sum_congr (fun Q _ => ?_))
  simp only [kernP_shift]

#print axioms Tm_symm

/-- DERIVED: no numeral. -/
theorem Tm_iterate (m n : ℕ) (c : Amod N τ) :
    (⇑(Tm hN τ m))^[n] c = Finsupp.mapDomain ((PosMono.shift hN τ m)^[n]) c := by
  induction n with
  | zero => exact Finsupp.mapDomain_id.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ']
    show Finsupp.mapDomain (PosMono.shift hN τ m)
        (Finsupp.mapDomain ((PosMono.shift hN τ m)^[n]) c) = _
    rw [← Finsupp.mapDomain_comp]

/-- `T_m = T_{m+1} ∘ T_{m+1}` on `Amod`.

DERIVED: `1` is the half-step offset. -/
theorem Tm_half (m : ℕ) (c : Amod N τ) : Tm hN τ m c = Tm hN τ (m + 1) (Tm hN τ (m + 1) c) := by
  show Finsupp.mapDomain (PosMono.shift hN τ m) c
    = Finsupp.mapDomain (PosMono.shift hN τ (m + 1))
        (Finsupp.mapDomain (PosMono.shift hN τ (m + 1)) c)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext P
  exact (PosMono.shift_half hN τ m P).symm

/-- The kernel of iterated shifts is bounded uniformly in the number of shifts.

DERIVED: no numeral. -/
theorem kernP_iterate_bound (hB : UniformBound hN ρ) (m : ℕ) (P Q : PosMono N τ) :
    ∃ C : ℝ, ∀ n : ℕ,
      |kernP hN ρ τ ((PosMono.shift hN τ m)^[n] P) ((PosMono.shift hN τ m)^[n] Q)| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_contS_le hN ρ hB (pairFam τ P.1 Q.1)
  refine ⟨C, fun n => ?_⟩
  unfold kernP kern
  rw [PosMono.shift_iterate, PosMono.shift_iterate, pairFam_shiftN]
  exact hC m _

/-- The form of iterated shifts is bounded uniformly in the number of shifts.

DERIVED: no numeral. -/
theorem formFun_iterate_le (hB : UniformBound hN ρ) (m : ℕ) (c : Amod N τ) :
    ∃ B : ℝ, ∀ n : ℕ,
      formFun hN ρ τ ((⇑(Tm hN τ m))^[n] c) ((⇑(Tm hN τ m))^[n] c) ≤ B := by
  choose C hC using kernP_iterate_bound hN ρ τ hB m
  refine ⟨∑ P ∈ c.support, ∑ Q ∈ c.support, |c P| * |c Q| * C P Q, fun n => ?_⟩
  rw [Tm_iterate, formFun_mapDomain]
  show ∑ P ∈ c.support, ∑ Q ∈ c.support, c P * c Q
      * kernP hN ρ τ ((PosMono.shift hN τ m)^[n] P) ((PosMono.shift hN τ m)^[n] Q) ≤ _
  refine Finset.sum_le_sum (fun P _ => Finset.sum_le_sum (fun Q _ => ?_))
  calc c P * c Q * kernP hN ρ τ ((PosMono.shift hN τ m)^[n] P) ((PosMono.shift hN τ m)^[n] Q)
      ≤ |c P * c Q * kernP hN ρ τ ((PosMono.shift hN τ m)^[n] P)
          ((PosMono.shift hN τ m)^[n] Q)| := le_abs_self _
    _ = |c P| * |c Q| * |kernP hN ρ τ ((PosMono.shift hN τ m)^[n] P)
          ((PosMono.shift hN τ m)^[n] Q)| := by rw [abs_mul, abs_mul]
    _ ≤ |c P| * |c Q| * C P Q :=
        mul_le_mul_of_nonneg_left (hC P Q n) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **The time step contracts the form**: iterated Schwarz with the translation-uniform bound.

DERIVED: no numeral. -/
theorem Tm_contract (hB : UniformBound hN ρ) (hR : ρ.ReflCompat τ) (m : ℕ) (c : Amod N τ) :
    formFun hN ρ τ (Tm hN τ m c) (Tm hN τ m c) ≤ formFun hN ρ τ c c := by
  obtain ⟨B, hB'⟩ := formFun_iterate_le hN ρ τ hB m c
  exact SchwarzIteration.contract_of_bounded_orbit (contReflForm hN ρ τ hB hR) (⇑(Tm hN τ m))
    (Tm_symm hN ρ τ m) c B hB'

#print axioms Tm_contract

/-- The empty monomial, the vacuum before completion.

DERIVED: `4` in `Fin 4` is the spacetime dimension; the body's `0` is the number of factors. -/
def emptyPos (N : ℕ) (τ : Fin 4) : PosMono N τ := ⟨⟨0, Fin.elim0⟩, fun i => i.elim0⟩

/-- DERIVED: no numeral. -/
theorem shift_emptyPos (m : ℕ) : PosMono.shift hN τ m (emptyPos N τ) = emptyPos N τ :=
  Subtype.ext (congrArg (Sigma.mk 0) (funext fun i => i.elim0))

/-- `S(∅) = 1`: the empty Schwinger function is the constant sequence `1 · ν(1) = 1`.

DERIVED: `1` is the normalisation of a state. -/
theorem kern_empty : kern hN ρ τ (emptyPos N τ).1 (emptyPos N τ).1 = 1 := by
  haveI : ((ultra : Ultrafilter ℕ) : Filter ℕ).NeBot := ultra.neBot'
  have hconst : ∀ k, latSkR hN ρ k (pairFam τ (emptyPos N τ).1 (emptyPos N τ).1) = 1 := by
    intro k
    show (∏ x : Fin 0 ⊕ Fin 0, _) * stateK hN k (∏ x : Fin 0 ⊕ Fin 0, _) = 1
    rw [Fintype.prod_empty, Fintype.prod_empty, one_mul]
    exact (stateK hN k).map_one
  have hfun : (fun k => latSkR hN ρ k (pairFam τ (emptyPos N τ).1 (emptyPos N τ).1))
      = fun _ => (1 : ℝ) := funext hconst
  show limUnder (ultra : Filter ℕ)
      (fun k => latSkR hN ρ k (pairFam τ (emptyPos N τ).1 (emptyPos N τ).1)) = 1
  rw [hfun]
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨1, tendsto_const_nhds⟩) tendsto_const_nhds

/-- **The continuum transfer data at the dyadic step `dySpacing N m`.**

DERIVED: `1` is the coefficient of the vacuum. -/
noncomputable def contTransfer (hB : UniformBound hN ρ) (hR : ρ.ReflCompat τ) (m : ℕ) :
    Transfer.TransferData (Amod N τ) where
  toReflForm := contReflForm hN ρ τ hB hR
  T := Tm hN τ m
  vac := Finsupp.single (emptyPos N τ) 1
  T_symm := Tm_symm hN ρ τ m
  T_contract := Tm_contract hN ρ τ hB hR m
  T_vac := by
    show Finsupp.mapDomain (PosMono.shift hN τ m) (Finsupp.single (emptyPos N τ) 1)
      = Finsupp.single (emptyPos N τ) 1
    rw [Finsupp.mapDomain_single, shift_emptyPos]
  vac_norm := by
    show formFun hN ρ τ (Finsupp.single (emptyPos N τ) 1) (Finsupp.single (emptyPos N τ) 1) = 1
    rw [formFun_single, one_mul, one_mul]
    exact kern_empty hN ρ τ

/-- **Positivity of the transfer operator**: `⟨c, T_m c⟩ = ⟨T_{m+1} c, T_{m+1} c⟩ ≥ 0`.

DERIVED: `1` is the half-step offset. -/
theorem positiveTransfer (hB : UniformBound hN ρ) (hR : ρ.ReflCompat τ) (m : ℕ) :
    GNSHilbert.PositiveTransfer (contTransfer hN ρ τ hB hR m) := by
  intro c
  show 0 ≤ formFun hN ρ τ c (Tm hN τ m c)
  rw [Tm_half, ← Tm_symm hN ρ τ (m + 1)]
  exact formFun_nonneg hN ρ τ hB hR _

#print axioms positiveTransfer

end TransferOp

/-! ## 4. The reconstruction -/

section Reconstruction

variable (hN : N ≠ 0) (ρ : Renorm N) (τ : Fin 4) (hB : UniformBound hN ρ) (hR : ρ.ReflCompat τ)

/-- The vector of the positive-time monomial `P` in the reconstructed Hilbert space.

DERIVED: `1` the coefficient, `0` the imaginary component. -/
noncomputable def vecOf (m : ℕ) (P : PosMono N τ) :
    GNSHilbert.H (contTransfer hN ρ τ hB hR m).toReflForm :=
  ((GNSHilbert.Pre.ofPair (contTransfer hN ρ τ hB hR m).toReflForm (Finsupp.single P 1) 0
    : GNSHilbert.Pre (contTransfer hN ρ τ hB hR m).toReflForm)
    : GNSHilbert.H (contTransfer hN ρ τ hB hR m).toReflForm)

/-- **The reconstruction reads the Schwinger functions**: `⟪vecOf P, vecOf Q⟫ = S(θP ∪ Q)`.

DERIVED: `1` the coefficients, `0` the imaginary parts. -/
theorem inner_vecOf (m : ℕ) (P Q : PosMono N τ) :
    inner ℂ (vecOf hN ρ τ hB hR m P) (vecOf hN ρ τ hB hR m Q) = (kern hN ρ τ P.1 Q.1 : ℂ) := by
  unfold vecOf
  rw [GNSHilbert.inner_coe]
  refine OSPositivity.ceq ?_ ?_
  · rw [OSPositivity.cform_re, Complex.ofReal_re]
    show formFun hN ρ τ (Finsupp.single P 1) (Finsupp.single Q 1) + formFun hN ρ τ 0 0
      = kern hN ρ τ P.1 Q.1
    rw [formFun_single, formFun_zero_left, one_mul, one_mul, add_zero]
    rfl
  · rw [OSPositivity.cform_im, Complex.ofReal_im]
    show formFun hN ρ τ (Finsupp.single P 1) 0 - formFun hN ρ τ 0 (Finsupp.single Q 1) = 0
    rw [formFun_zero_right, formFun_zero_left, sub_zero]

#print axioms inner_vecOf

/-- **Requirement E, what is built.** At every `SU(N)`, `N ≠ 0`, every renormalisation `ρ` with the
uniform bound and reflection compatibility, every time direction `τ` and every dyadic time step
`dySpacing N m`, from the limit Schwinger functions of the periodic Wilson states with running
coupling:

1. a complete complex Hilbert space and a unit vector `Ω` (the empty monomial);
2. a self-adjoint transfer operator `T` with `T Ω = Ω` and spectrum in `[0, 1]`;
3. `⟪vecOf P, vecOf Q⟫ = S(θP ∪ Q)` for every pair of positive-time monomials.

Together with `ContinuumSchwinger`'s `tendsto_contS` (existence), `exists_abs_contS_le` (OS0),
`contS_comp_equiv` (symmetry), `contS_translate` (dyadic translations), `contS_gram_nonneg`
(reflection positivity) and, under `UniformClustering`, `contS_cluster_tendsto` (clustering), or,
under `FixedWindowDecay`, `ContinuumCluster.contS_cluster_of_fixedWindowDecay`. Rotation invariance
(`RotationInvariant`) is not derived.

Non-triviality is not part of the statement. When the Schwinger functions factorise,
`S(θP ∪ Q) = S(θP ∪ ∅) S(∅ ∪ Q)`, every `vecOf P` is a multiple of `Ω`, the space is spanned by `Ω`
and `opT` is the identity.

DERIVED: `1` is the vacuum norm and the top of the spectrum; `0` its bottom. -/
theorem continuum_reconstruction (m : ℕ) :
    CompleteSpace (GNSHilbert.H (contTransfer hN ρ τ hB hR m).toReflForm)
    ∧ ‖GNSHilbert.Omega (contTransfer hN ρ τ hB hR m).toReflForm
        (contTransfer hN ρ τ hB hR m).vac‖ = 1
    ∧ IsSelfAdjoint (GNSHilbert.opT (contTransfer hN ρ τ hB hR m))
    ∧ GNSHilbert.opT (contTransfer hN ρ τ hB hR m)
        (GNSHilbert.Omega (contTransfer hN ρ τ hB hR m).toReflForm
          (contTransfer hN ρ τ hB hR m).vac)
      = GNSHilbert.Omega (contTransfer hN ρ τ hB hR m).toReflForm
          (contTransfer hN ρ τ hB hR m).vac
    ∧ spectrum ℝ (GNSHilbert.opT (contTransfer hN ρ τ hB hR m)) ⊆ Set.Icc 0 1
    ∧ ∀ P Q : PosMono N τ,
        inner ℂ (vecOf hN ρ τ hB hR m P) (vecOf hN ρ τ hB hR m Q)
          = (kern hN ρ τ P.1 Q.1 : ℂ) :=
  ⟨GNSHilbert.complete_H _, GNSHilbert.norm_Omega_vac _, GNSHilbert.isSelfAdjoint_opT _,
    GNSHilbert.opT_Omega _,
    fun x hx => ⟨GNSHilbert.spectrum_opT_nonneg _ (positiveTransfer hN ρ τ hB hR m) hx,
      (GNSHilbert.spectrum_opT_subset_unit_interval _ hx).2⟩,
    inner_vecOf hN ρ τ hB hR m⟩

#print axioms continuum_reconstruction

/-- **The bare instance**: `continuum_reconstruction` at `Renorm.bare`, whose `UniformBound`
(`uniformBound_bare`) and `ReflCompat` (`Renorm.bare_reflCompat`) are proved, so the only hypothesis
left is the section's `hN : N ≠ 0`.

The bare limit. By translation invariance of the periodic state the one-field function at step `k`
is `ν_k(O) · a⁴ ∑ₓ f(a x)`, the expectation of `O` times a Riemann sum of `f`. Cauchy–Schwarz bounds
the variance of `smear a O f` by `(M (2R + 3)⁴)²` times the single-site variance
`ν_k(O²) − ν_k(O)²`. Wherever the single-site variances tend to zero along `ultra`, the bare smeared
fields converge to constants, every Schwinger function is the product of its one-field functions,
and the space built here is spanned by `Ω` with `opT` the identity. At weak coupling the Wilson
measure concentrates on flat connections, on which every local gauge-invariant field is constant, so
the bare limit is expected to be this degenerate one. The theorem shows the hypotheses of
`continuum_reconstruction` are jointly satisfiable; it does not supply a non-trivial instance.

DERIVED: `1` is the vacuum norm and the top of the spectrum; `0` its bottom. -/
theorem continuum_reconstruction_bare (m : ℕ) :
    CompleteSpace (GNSHilbert.H (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
      (Renorm.bare_reflCompat τ) m).toReflForm)
    ∧ ‖GNSHilbert.Omega (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
          (Renorm.bare_reflCompat τ) m).toReflForm
        (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
          (Renorm.bare_reflCompat τ) m).vac‖ = 1
    ∧ IsSelfAdjoint (GNSHilbert.opT (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
        (Renorm.bare_reflCompat τ) m))
    ∧ GNSHilbert.opT (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
          (Renorm.bare_reflCompat τ) m)
        (GNSHilbert.Omega (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
            (Renorm.bare_reflCompat τ) m).toReflForm
          (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
            (Renorm.bare_reflCompat τ) m).vac)
      = GNSHilbert.Omega (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
            (Renorm.bare_reflCompat τ) m).toReflForm
          (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
            (Renorm.bare_reflCompat τ) m).vac
    ∧ spectrum ℝ (GNSHilbert.opT (contTransfer hN (Renorm.bare N) τ (uniformBound_bare hN)
        (Renorm.bare_reflCompat τ) m)) ⊆ Set.Icc 0 1
    ∧ ∀ P Q : PosMono N τ,
        inner ℂ (vecOf hN (Renorm.bare N) τ (uniformBound_bare hN) (Renorm.bare_reflCompat τ) m P)
            (vecOf hN (Renorm.bare N) τ (uniformBound_bare hN) (Renorm.bare_reflCompat τ) m Q)
          = (kern hN (Renorm.bare N) τ P.1 Q.1 : ℂ) :=
  continuum_reconstruction hN (Renorm.bare N) τ (uniformBound_bare hN)
    (Renorm.bare_reflCompat τ) m

#print axioms continuum_reconstruction_bare

end Reconstruction

end MassGap.ContinuumReconstruction
