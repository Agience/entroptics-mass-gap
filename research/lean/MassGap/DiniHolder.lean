import Mathlib
import MassGap.ShellLorentz

/-!
# MassGap.DiniHolder — the dyadic Dini bound for Lipschitz-smeared vectors of the reconstruction

`ShellDensity.DyadicDini` (`Σ_k ‖U(2^{−k} e_j) u − u‖² < ∞`) carries the momentum identification
`ShellDensity.ae_char_eq_phase` and the rate marginal `ShellDensity.nu_fst`.
`ShellLorentz.dyadicDini_of_holder` reduces it to a Hölder bound. This module proves that bound, with
exponent `1/2`, for the vectors of the reconstruction whose test functions are Lipschitz. Declarations
are in the namespace `MassGap.DiniHolder`.

## The bound

* `abs_contSF_translate_le_mul`: for fields of `D` and Lipschitz test functions, translating factor
  `i` by `dᵢ` with `‖dᵢ‖ ≤ t ≤ 1` moves the limit Schwinger function by at most `A t`, with `A`
  independent of `d` and `t`. It is `ObserverOS.abs_contSF_energy0_sub_le` with the sup-norm distance
  `Kᵢ ‖dᵢ‖`; the cube is built as in `ShellTranslate.tendsto_contSF_translate` (radius `ΣR₀ + 1`, moment bounds from `hcube`).
* `realT_gvecT`: on a regular monomial the real translation is the translation of the test functions.
  `norm_realT_sub_sq`: `‖realT x u − u‖² = 2 (S(θP ∪ P) − S(θP ∪ shift_x P))`.
* `holderHalf_gvecT`: for `LipReg D P`, `‖realT (s e_j) u − u‖ ≤ L s^{1/2}` at every `s ≥ 0`. Below
  `s = 1` this is the two lines above. Above it the isometry gives `2 ‖u‖`.

## The class of vectors

`HolderHalf J u` is closed under sums and complex multiples, holds at every vector fixed by the
translations, and passes through every bounded operator commuting with them (`holderHalf_timeT`). So
it holds on the complex span of `lipVecs` (`holderHalf_span`), in particular at the vacuum complement
`u − c Ω` of a smeared vector (`holderHalf_sub_vac`).

## What follows at these vectors

`dyadicDini_span`, and through it, with no Dini hypothesis on `u`: `ae_char_eq_phase_lip`,
`inner_U_eq_momentum_lip`, `nu_fst_lip`.

`exists_lipReg`: for every `O ∈ D` the class contains a one-factor monomial of `O` with a non-zero
test function (a tent in sup norm placed beyond the margin), so the hypothesis `LipReg` is not empty.

## What does not follow

Plainly:

* The bound is relative to the hypotheses `hpos`, `hcube` that `realT` itself needs (the cube moments
  (E) on the class `D`). They are inputs here, not proved here.
* `L` depends on the vector, through the moment constant, the Lipschitz constants and the bounds of
  its test functions. No bound uniform on a set of vectors is claimed.
* Merely uniformly continuous test functions are not covered directly. `span lipVecs` is dense in the regular
  sector `V = range J` (`RegularDense.closure_span_lipVecs`), but `DyadicDini` is not closed under limits, so it
  is not shown on all of `V`.
* On `V⊥`, `realT` is the identity (`ShellTranslate.realT_orth`), so `DyadicDini` holds there trivially
  and says nothing about the physical translation.
* That `gvecT P` is non-zero for a given `P ∈ LipReg`, beyond the vacuum, is not shown: `exists_lipReg`
  places a non-zero test function, not a non-zero vector.
* Composite fields outside `D` are not reached. The template `ShellLorentz.KLJointRep` is untouched:
  this module removes the `DyadicDini` hypothesis, not the Källén–Lehmann form of `nu`.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.DiniHolder

open Filter Topology MeasureTheory
open scoped NNReal
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate
open MassGap.ShellMomentum (opS_coe cS_fst cS_snd)
open MassGap.ShellMeasure (rateMeasure)
open MassGap.ShellJoint (JointData jointMeasure treeData UB)
open MassGap.ShellDensity (DyadicDini ej momentum nu)

noncomputable section

/-! ## 1. Hölder vectors of a unitary representation -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {τ : Fin 4}
  (Jt : JointData E (spatial τ))

/-- The Hölder bound of exponent `1/2`: `‖U(s e_j) u − u‖ ≤ L s^{1/2}` for every direction and every
`s ≥ 0`. DERIVED: `0` the sign of `s`; `1/2` the square root of the first-order form bound (a form
Lipschitz in `s` gives the norm exponent `1/2`). -/
def HolderHalf (u : E) : Prop :=
  ∃ L : ℝ, ∀ (j : Fin 4) (s : ℝ), 0 ≤ s → ‖Jt.R.U (s • ej τ j) u - u‖ ≤ L * s ^ (1 / 2 : ℝ)

variable {Jt}

/-- A Hölder vector satisfies the dyadic Dini bound (`dyadicDini_of_holder`). DERIVED: `0` the sign
of the exponent; `1/2` as in `HolderHalf`. -/
theorem HolderHalf.dyadicDini {u : E} (hu : HolderHalf Jt u) : DyadicDini Jt u := by
  obtain ⟨L, h⟩ := hu
  exact MassGap.ShellLorentz.dyadicDini_of_holder Jt u (by norm_num) h

/-- The class is closed under sums. DERIVED: no numeral. -/
theorem HolderHalf.add {u v : E} (hu : HolderHalf Jt u) (hv : HolderHalf Jt v) :
    HolderHalf Jt (u + v) := by
  obtain ⟨L1, h1⟩ := hu
  obtain ⟨L2, h2⟩ := hv
  refine ⟨L1 + L2, fun j s hs => ?_⟩
  have e : Jt.R.U (s • ej τ j) (u + v) - (u + v)
      = (Jt.R.U (s • ej τ j) u - u) + (Jt.R.U (s • ej τ j) v - v) := by
    rw [map_add]
    abel
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h1 j s hs) (h2 j s hs))

/-- The class is closed under complex multiples. DERIVED: no numeral. -/
theorem HolderHalf.smul {u : E} (c : ℂ) (hu : HolderHalf Jt u) : HolderHalf Jt (c • u) := by
  obtain ⟨L, h⟩ := hu
  refine ⟨‖c‖ * L, fun j s hs => ?_⟩
  have e : Jt.R.U (s • ej τ j) (c • u) - c • u = c • (Jt.R.U (s • ej τ j) u - u) := by
    rw [map_smul, smul_sub]
  rw [e, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h j s hs) (norm_nonneg c)

/-- A vector fixed by the translations is in the class, with `L = 0`. DERIVED: `0` the constant. -/
theorem holderHalf_of_fixed {v : E} (h : ∀ x, Jt.R.U x v = v) : HolderHalf Jt v :=
  ⟨0, fun j s _ => by rw [h, sub_self, norm_zero, zero_mul]⟩

/-- A bounded operator commuting with the translations keeps the class. DERIVED: no numeral. -/
theorem HolderHalf.map {u : E} (T : E →L[ℂ] E) (hT : ∀ x, Commute (Jt.R.U x) T)
    (hu : HolderHalf Jt u) : HolderHalf Jt (T u) := by
  obtain ⟨L, h⟩ := hu
  refine ⟨‖T‖ * L, fun j s hs => ?_⟩
  have e : Jt.R.U (s • ej τ j) (T u) = T (Jt.R.U (s • ej τ j) u) := by
    have h1 := congrArg (fun F : E →L[ℂ] E => F u) (hT (s • ej τ j)).eq
    simpa only [ContinuousLinearMap.mul_apply] using h1
  rw [e, ← map_sub, mul_assoc]
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h j s hs) (norm_nonneg T))

/-- The vacuum complement of a Hölder vector: `v` fixed by the translations. DERIVED: no numeral. -/
theorem holderHalf_sub_vac {u v : E} (hu : HolderHalf Jt u) (hv : ∀ x, Jt.R.U x v = v) (c : ℂ) :
    HolderHalf Jt (u - c • v) := by
  have h := hu.add ((holderHalf_of_fixed hv).smul (-c))
  rwa [neg_smul, ← sub_eq_add_neg] at h

/-- A first-order bound on the squared displacement at `s ≤ 1` gives the Hölder bound at every `s`:
below `1` take the root, above `1` the isometry gives `2 ‖u‖`, and `s^{1/2} ≥ 1`. DERIVED: `0` the
sign of `s` and of `A`; `1` the range of the first-order bound and the threshold where the isometry
takes over; `1/2` the root; `2` the square and the two norms of the triangle inequality. -/
theorem holderHalf_of_sq_bound (Jt : JointData E (spatial τ)) (u : E) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ (j : Fin 4) (s : ℝ), 0 ≤ s → s ≤ 1 → ‖Jt.R.U (s • ej τ j) u - u‖ ^ 2 ≤ A * s) :
    HolderHalf Jt u := by
  have hnorm : ∀ x, ‖Jt.R.U x u‖ = ‖u‖ := fun x => by
    have h2 : ‖Jt.R.U x u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), Jt.R.inner_U]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  refine ⟨Real.sqrt A + 2 * ‖u‖, fun j s hs => ?_⟩
  have hs' : 0 ≤ s ^ (1 / 2 : ℝ) := Real.rpow_nonneg hs _
  rcases le_or_gt s 1 with h1 | h1
  · have h3 : ‖Jt.R.U (s • ej τ j) u - u‖ ≤ Real.sqrt (A * s) :=
      (le_abs_self _).trans (Real.abs_le_sqrt (h j s hs h1))
    rw [Real.sqrt_mul hA, Real.sqrt_eq_rpow s] at h3
    nlinarith [mul_nonneg (norm_nonneg u) hs']
  · have h2 : 1 ≤ s ^ (1 / 2 : ℝ) := Real.one_le_rpow h1.le (by norm_num)
    have h3 := norm_sub_le (Jt.R.U (s • ej τ j) u) u
    rw [hnorm] at h3
    nlinarith [mul_nonneg (Real.sqrt_nonneg A) hs',
      mul_nonneg (norm_nonneg u) (sub_nonneg.mpr h2)]

end Generic

/-- The step `s e_j` has sup norm at most `s`. DERIVED: `0` the sign of `s` and the entries of
`ej`; `1` the entry of `ej`; `4` in `Fin 4` the spacetime dimension. -/
theorem norm_smul_ej_le (τ j : Fin 4) {s : ℝ} (hs : 0 ≤ s) :
    ‖((s • ej τ j : spatial τ) : Fin 4 → ℝ)‖ ≤ s := by
  refine (pi_norm_le_iff_of_nonneg hs).mpr fun i => ?_
  show ‖s * (if i = τ then (0 : ℝ) else if i = j then 1 else 0)‖ ≤ s
  split_ifs <;> simp [abs_of_nonneg hs, hs]

/-! ## 2. Lipschitz monomials -/

section Lipschitz

variable {N : ℕ}

/-- A Lipschitz regular monomial: every field in `D`, every test function Lipschitz in the sup norm
of `ℝ⁴`. DERIVED: no numeral. -/
def LipReg (D : Set (LField (MassGap.SUN.SU N))) (P : Mono N) : Prop :=
  ∀ i, (P.2 i).1 ∈ D ∧ ∃ K : ℝ≥0, LipschitzWith K (P.2 i).2.1

/-- A Lipschitz monomial is regular. DERIVED: no numeral. -/
theorem LipReg.reg {D : Set (LField (MassGap.SUN.SU N))} {P : Mono N} (h : LipReg D P) : Reg D P :=
  fun i => ⟨(h i).1, (h i).2.choose_spec.uniformContinuous⟩

/-- A reflection keeps the Lipschitz constant (`dist_reflR_le`). DERIVED: `4` in `Fin 4` the
spacetime dimension. -/
theorem lipschitz_reflect {f : TestFn} {K : ℝ≥0} (hf : LipschitzWith K f.1) (τ : Fin 4) :
    LipschitzWith K (f.reflect τ).1 :=
  LipschitzWith.of_dist_le_mul fun a b =>
    (hf.dist_le_mul (reflR τ a) (reflR τ b)).trans
      (mul_le_mul_of_nonneg_left (dist_reflR_le τ a b) K.2)

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

include hpos hcube

/-- The Schwinger functions are Lipschitz in the translation vector. For fields of `D` and Lipschitz
test functions, one constant `A` bounds the change under every `d` with `‖dᵢ‖ ≤ t ≤ 1` by `A t`:
every translate stays in one cube (`1` in the cube radius, as in `tendsto_contSF_translate`), and is
within `(∑ᵢ Kᵢ) t` of its original in sup norm, so `abs_contSF_energy0_sub_le` applies.
DERIVED: `0` the sign of `A` and of the constants; `1` bounds `‖dᵢ‖`, keeping the translates in one
cube; `2` makes the moment even; `4` in `Fin 4` the spacetime dimension. -/
theorem abs_contSF_translate_le_mul {ι : Type} [Fintype ι] (F : ι → SField N)
    (hG : ∀ i, (F i).1 ∈ D) (K : ι → ℝ≥0) (hL : ∀ i, LipschitzWith (K i) (F i).2.1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (d : ι → Fin 4 → ℝ) (t : ℝ), (∀ i, ‖d i‖ ≤ t) → t ≤ 1 →
      |contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate (d i)))
        - contSF hN (energy0 W D hD) F| ≤ A * t := by
  classical
  have hB := uniformBoundF_energy0 hN W D hD hpos hcube
  have hex : ∀ i, ∃ R0 M : ℝ, IsTest (F i).2.1 R0 M := fun i => (F i).2.2
  choose R0 M hRM using hex
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, R0 i + 1 := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, R0 i := Finset.sum_nonneg (fun i _ => (hRM i).1)
  have hR0 : 0 ≤ R := by rw [hRdef]; linarith
  have hRi : ∀ i, R0 i + 1 ≤ R := fun i => by
    have h4 : R0 i ≤ ∑ i, R0 i :=
      Finset.single_le_sum (f := R0) (fun i _ => (hRM i).1) (Finset.mem_univ i)
    rw [hRdef]; linarith
  have hC : ∀ i, ∃ C : ℝ, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k (F i).1).1 ^ (2 * Fintype.card ι)) ≤ C :=
    fun i => hcube _ (hG i) R hR0 _
  choose C hC using hC
  have hc : ∀ i, ∀ᶠ k in atTop, stateK hN k (cubeSum (dySpacing N k) R
      (W.fieldMap k (F i).1).1 ^ (2 * Fintype.card ι)) ≤ ∑ i, |C i| := fun i =>
    (hC i).mono (fun k hk => hk.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))))
  have hc0 : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨Kt, hKt⟩ : ∃ Kt : ℝ, Kt = ∑ i, (K i : ℝ) := ⟨_, rfl⟩
  have hKt0 : 0 ≤ Kt := by
    rw [hKt]
    exact Finset.sum_nonneg fun i _ => (K i).2
  have hKi : ∀ i, (K i : ℝ) ≤ Kt := fun i => by
    rw [hKt]
    exact Finset.single_le_sum (f := fun i => (K i : ℝ)) (fun i _ => (K i).2) (Finset.mem_univ i)
  refine ⟨(1 + Fintype.card ι * ∑ i, |C i|) * Kt * ∑ a, ∏ i ∈ Finset.univ \ {a}, M i,
    mul_nonneg (mul_nonneg (by positivity) hKt0)
      (Finset.sum_nonneg (fun a _ => Finset.prod_nonneg (fun i _ => (hRM i).M_nonneg))),
    fun d t hd ht => ?_⟩
  have hF : ∀ i, IsTest (F i).2.1 R (M i) := fun i =>
    ⟨hR0, (hRM i).2.1, fun y hy j => ((hRM i).2.2 y hy j).trans (by linarith [hRi i])⟩
  have hF' : ∀ i, IsTest ((F i).2.translate (d i)).1 R (M i) := by
    intro i
    refine ⟨hR0, fun y => (hRM i).2.1 _, fun y hy j => ?_⟩
    have h1 : |(y - d i) j| ≤ R0 i := (hRM i).2.2 (y - d i) hy j
    have h2 : |d i j| ≤ ‖d i‖ := by
      have := norm_le_pi_norm (d i) j
      rwa [Real.norm_eq_abs] at this
    have h3 : |y j| ≤ |(y - d i) j| + |d i j| := by
      have h7 := abs_add_le ((y - d i) j) (d i j)
      have e : (y - d i) j + d i j = y j := by simp
      rw [e] at h7
      exact h7
    linarith [hRi i, (hd i).trans ht]
  have hclose : ∀ i y, |((F i).2.translate (d i)).1 y - (F i).2.1 y| ≤ Kt * t := by
    intro i y
    have h := (hL i).dist_le_mul (y - d i) y
    rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at h
    exact h.trans (mul_le_mul (hKi i) (hd i) (norm_nonneg _) hKt0)
  have hdiff := abs_contSF_energy0_sub_le hN W hD hpos hB F
    (fun i => ((F i).1, (F i).2.translate (d i))) (fun i => rfl) hG hR0 hc M hF hF' hclose
  calc |contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate (d i)))
        - contSF hN (energy0 W D hD) F|
      ≤ (1 + Fintype.card ι * ∑ i, |C i|) * ∑ a, Kt * t * ∏ i ∈ Finset.univ \ {a}, M i := hdiff
    _ = (1 + Fintype.card ι * ∑ i, |C i|) * Kt * (∑ a, ∏ i ∈ Finset.univ \ {a}, M i) * t := by
      rw [← Finset.mul_sum]
      ring

/-- The reflection kernel is Lipschitz in the translation of its second monomial, at `0`.
DERIVED: `0` the zero translation of the first block and the sign of `A`; `1` the range of `t`; `4`
in `Fin 4` the spacetime dimension. -/
theorem abs_kernF_shift_sub_le (τ : Fin 4) {P : Mono N} (hP : LipReg D P) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (v : Fin 4 → ℝ) (t : ℝ), ‖v‖ ≤ t → t ≤ 1 →
      |kernF hN (energy0 W D hD) τ P (Mono.shift v P) - kernF hN (energy0 W D hD) τ P P| ≤ A * t := by
  have hex : ∀ x : Fin P.1 ⊕ Fin P.1, ∃ K : ℝ≥0, LipschitzWith K (pairFam τ P P x).2.1 := by
    intro x
    cases x with
    | inl i =>
      obtain ⟨K, hK⟩ := (hP i).2
      exact ⟨K, lipschitz_reflect hK τ⟩
    | inr j => exact (hP j).2
  choose K hK using hex
  obtain ⟨A, hA, h⟩ := abs_contSF_translate_le_mul hN W hD hpos hcube (pairFam τ P P)
    (fun x => (reg_pairFam hD τ hP.reg hP.reg x).1) K hK
  refine ⟨A, hA, fun v t hv ht => ?_⟩
  have ht0 : 0 ≤ t := (norm_nonneg v).trans hv
  have hd : ∀ x : Fin P.1 ⊕ Fin P.1,
      ‖Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => v) x‖ ≤ t := by
    intro x
    cases x with
    | inl i =>
      show ‖(0 : Fin 4 → ℝ)‖ ≤ t
      rw [norm_zero]
      exact ht0
    | inr j => exact hv
  have hb := h (fun x => Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => v) x) t hd ht
  have e : kernF hN (energy0 W D hD) τ P (Mono.shift v P)
      = contSF hN (energy0 W D hD) (fun x => ((pairFam τ P P x).1,
          (pairFam τ P P x).2.translate (Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => v) x))) :=
    congrArg (fun G => contSF hN (energy0 W D hD) G) (pairFam_shift_right τ P P v)
  rw [e]
  exact hb

end Lipschitz

/-! ## 3. The translation of a regular vector -/

section Vectors

variable {N : ℕ}

/-- The inclusion of the regular sector sends a regular vector to its `gvecT`. DERIVED: `1` the
coefficient; `0` the imaginary component and the reference step. -/
theorem J_gVec (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r)
    (P : RMono N D τ r) :
    J hN Φ hB D τ hpp (gVec (rTransfer hN Φ hB D τ hpp 0) P) = gvecT hN Φ hB τ hpp P.1 := by
  unfold J gVec gvecT
  rw [opJ_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · simp only [cJ_fst, GNSHilbert.Pre.ofPair_fst]
    show Finsupp.mapDomain Subtype.val (Finsupp.single P 1) = Finsupp.single P.1 1
    exact Finsupp.mapDomain_single
  · simp only [cJ_snd, GNSHilbert.Pre.ofPair_snd]
    exact map_zero _

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
  (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

/-- `rU x` translates the regular vector of a monomial. DERIVED: `1` the coefficient; `0` the
imaginary component and the reference step. -/
theorem rU_gVec (x : spatial τ) (P : RMono N D τ r) :
    rU hN W hD hpos hcube hB τ hpp x (gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) P)
      = gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0)
          (rShift (x : Fin 4 → ℝ) (spatial_time x) P) := by
  unfold rU gVec
  rw [opS_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · simp only [cS_fst, GNSHilbert.Pre.ofPair_fst]
    show Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) (Finsupp.single P 1)
      = Finsupp.single (rShift (x : Fin 4 → ℝ) (spatial_time x) P) 1
    exact Finsupp.mapDomain_single
  · simp only [cS_snd, GNSHilbert.Pre.ofPair_snd]
    exact map_zero _

/-- On a regular monomial `realT x` is the translation of the test functions. DERIVED: `0` the
vanishing remainder. -/
theorem realT_gvecT (x : spatial τ) (P : RMono N D τ r) :
    realT hN W hD hpos hcube hB τ hpp x (gvecT hN (energy0 W D hD) hB τ hpp P.1)
      = gvecT hN (energy0 W D hD) hB τ hpp (rShift (x : Fin 4 → ℝ) (spatial_time x) P).1 := by
  rw [← J_gVec hN (energy0 W D hD) hB D τ hpp P, realT_apply, JdJ, sub_self, add_zero, rU_gVec]
  exact J_gVec hN (energy0 W D hD) hB D τ hpp _

/-- The displacement of a regular vector read on the kernel:
`‖realT x u − u‖² = 2 (S(θP ∪ P) − S(θP ∪ shift_x P))`. DERIVED: `2` the two cross terms and the
square; `0` the reference step. -/
theorem norm_realT_sub_sq (x : spatial τ) (P : RMono N D τ r) :
    ‖realT hN W hD hpos hcube hB τ hpp x (gvecT hN (energy0 W D hD) hB τ hpp P.1)
        - gvecT hN (energy0 W D hD) hB τ hpp P.1‖ ^ 2
      = 2 * (kernF hN (energy0 W D hD) τ P.1.1 P.1.1
          - kernF hN (energy0 W D hD) τ P.1.1 (Mono.shift (x : Fin 4 → ℝ) P.1.1)) := by
  set u := gvecT hN (energy0 W D hD) hB τ hpp P.1 with hu
  set T := realT hN W hD hpos hcube hB τ hpp x with hT
  have hK : ∀ A B : MarginMono N τ r,
      RCLike.re (inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp A)
        (gvecT hN (energy0 W D hD) hB τ hpp B)) = kernF hN (energy0 W D hD) τ A.1 B.1 := by
    intro A B
    have h : inner ℂ (gvecT hN (energy0 W D hD) hB τ hpp A) (gvecT hN (energy0 W D hD) hB τ hpp B)
        = (kernF hN (energy0 W D hD) τ A.1 B.1 : ℂ) :=
      (flow_reconstruction hN (energy0 W D hD) hB τ hpp 0).2 A B
    rw [h]
    simp
  have hn : ‖T u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hT, inner_realT]
  have hu2 : ‖u‖ ^ 2 = kernF hN (energy0 W D hD) τ P.1.1 P.1.1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hu]
    exact hK P.1 P.1
  have hcross : RCLike.re (inner ℂ u (T u))
      = kernF hN (energy0 W D hD) τ P.1.1 (Mono.shift (x : Fin 4 → ℝ) P.1.1) := by
    rw [hT, hu, realT_gvecT]
    exact hK P.1 _
  rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ), hn, hcross, hu2]
  ring

include hpos hcube in
/-- The Hölder bound at a Lipschitz regular vector: `‖realT (s e_j) u − u‖ ≤ L s^{1/2}` for every
`s ≥ 0`. DERIVED: `2` the two cross terms of `norm_realT_sub_sq`; `1/2` as in `HolderHalf`. -/
theorem holderHalf_gvecT (P : RMono N D τ r) (hP : LipReg D P.1.1) :
    HolderHalf (treeData hN W hD hpos hcube hB τ hpp) (gvecT hN (energy0 W D hD) hB τ hpp P.1) := by
  obtain ⟨A, hA, h⟩ := abs_kernF_shift_sub_le hN W hD hpos hcube τ hP
  refine holderHalf_of_sq_bound _ _ (A := 2 * A) (by positivity) fun j s hs hs1 => ?_
  show ‖realT hN W hD hpos hcube hB τ hpp (s • ej τ j) (gvecT hN (energy0 W D hD) hB τ hpp P.1)
      - gvecT hN (energy0 W D hD) hB τ hpp P.1‖ ^ 2 ≤ 2 * A * s
  rw [norm_realT_sub_sq]
  have hb := h ((s • ej τ j : spatial τ) : Fin 4 → ℝ) s (norm_smul_ej_le τ j hs) hs1
  have h1 := (abs_le.mp hb).1
  linarith

/-- The Lipschitz-smeared vectors of the reconstruction. DERIVED: no numeral. -/
def lipVecs (D : Set (LField (MassGap.SUN.SU N))) (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)),
      O.refl τ ∈ D ↔ O ∈ D) (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
    (hpp : (energy0 W D hD).PosPreserving τ r) :
    Set (FlowH hN (energy0 W D hD) hB τ hpp) :=
  {u | ∃ P : RMono N D τ r, LipReg D P.1.1 ∧ u = gvecT hN (energy0 W D hD) hB τ hpp P.1}

include hpos hcube in
/-- The Hölder bound on the complex span of the Lipschitz-smeared vectors. DERIVED: `0` the zero
vector of the span. -/
theorem holderHalf_span {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) :
    HolderHalf (treeData hN W hD hpos hcube hB τ hpp) u := by
  induction hu using Submodule.span_induction with
  | mem x h =>
    obtain ⟨P, hP, rfl⟩ := h
    exact holderHalf_gvecT hN W hD hpos hcube hB τ hpp P hP
  | zero => exact holderHalf_of_fixed fun x => map_zero _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

include hpos hcube in
/-- The vacuum complement of a vector of the span. DERIVED: no numeral. -/
theorem holderHalf_span_sub_vac {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) (c : ℂ) :
    HolderHalf (treeData hN W hD hpos hcube hB τ hpp)
      (u - c • vacT hN (energy0 W D hD) hB τ hpp) :=
  holderHalf_sub_vac (holderHalf_span hN W hD hpos hcube hB τ hpp hu)
    (fun x => realT_vac hN W hD hpos hcube hB τ hpp x) c

include hpos hcube in
/-- The time translations keep the class (`commute_realT_timeT`). DERIVED: no numeral. -/
theorem holderHalf_timeT (t : ℝ) {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : HolderHalf (treeData hN W hD hpos hcube hB τ hpp) u) :
    HolderHalf (treeData hN W hD hpos hcube hB τ hpp) (timeT hN (energy0 W D hD) hB τ hpp t u) :=
  hu.map _ fun x => commute_realT_timeT hN W hD hpos hcube hB τ hpp x t

/-! ## 4. What holds at these vectors, with no Dini hypothesis -/

include hpos hcube in
/-- The dyadic Dini bound on the span of the Lipschitz-smeared vectors. DERIVED: no numeral. -/
theorem dyadicDini_span {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) :
    DyadicDini (treeData hN W hD hpos hcube hB τ hpp) u :=
  (holderHalf_span hN W hD hpos hcube hB τ hpp hu).dyadicDini

include hpos hcube in
/-- The dyadic Dini bound at a Lipschitz regular vector. DERIVED: no numeral. -/
theorem dyadicDini_gvecT (P : RMono N D τ r) (hP : LipReg D P.1.1) :
    DyadicDini (treeData hN W hD hpos hcube hB τ hpp) (gvecT hN (energy0 W D hD) hB τ hpp P.1) :=
  (holderHalf_gvecT hN W hD hpos hcube hB τ hpp P hP).dyadicDini

include hpos hcube in
/-- The momentum identification on the span: `χ(U x) = e^{i p(χ)·x}` almost everywhere.
DERIVED: no numeral. -/
theorem ae_char_eq_phase_lip {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) (x : spatial τ) :
    ∀ᵐ χ ∂(jointMeasure (treeData hN W hD hpos hcube hB τ hpp) u),
      χ (UB (treeData hN W hD hpos hcube hB τ hpp) x)
        = Complex.exp ((phase (momentum (treeData hN W hD hpos hcube hB τ hpp) χ) x : ℂ)
            * Complex.I) :=
  MassGap.ShellDensity.ae_char_eq_phase _ (dyadicDini_span hN W hD hpos hcube hB τ hpp hu) x

include hpos hcube in
/-- `⟪u, realT x u⟫` is the characteristic function of the momentum measure, on the span.
DERIVED: no numeral. -/
theorem inner_U_eq_momentum_lip {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) (x : spatial τ) :
    inner ℂ u (realT hN W hD hpos hcube hB τ hpp x u)
      = ∫ p, Complex.exp ((phase p x : ℂ) * Complex.I)
        ∂((jointMeasure (treeData hN W hD hpos hcube hB τ hpp) u).map
          (momentum (treeData hN W hD hpos hcube hB τ hpp))) :=
  MassGap.ShellDensity.inner_U_eq_momentum _ (dyadicDini_span hN W hD hpos hcube hB τ hpp hu) x

include hpos hcube in
/-- The rate marginal of `nu` is the rate measure, on the span. DERIVED: `1` the unit time. -/
theorem nu_fst_lip {u : FlowH hN (energy0 W D hD) hB τ hpp}
    (hu : u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)) :
    (nu (treeData hN W hD hpos hcube hB τ hpp) u).map Prod.fst
      = rateMeasure (timeT hN (energy0 W D hD) hB τ hpp 1) u :=
  MassGap.ShellDensity.nu_fst _ (dyadicDini_span hN W hD hpos hcube hB τ hpp hu)

end Vectors

/-! ## 5. Load test: the class is not empty -/

section Load

variable {N : ℕ}

/-- For every field of `D` there is a one-factor Lipschitz regular margin monomial with a non-zero
test function: the sup-norm tent `y ↦ max (1 − ‖y − c‖) 0` of height `1` at the point `c`, of time
coordinate `max r 0 + 2`. DERIVED: `0` the floor of the tent and the sign of the margin; `1` the
height and width of the tent, and the Lipschitz constant, the one factor; `2` puts the tent one width
past the margin `max r 0 + 1`; `4` in `Fin 4` the spacetime dimension. -/
theorem exists_lipReg {D : Set (LField (MassGap.SUN.SU N))} (τ : Fin 4) (r : ℝ)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) :
    ∃ P : RMono N D τ r, LipReg D P.1.1 ∧ P.1.1.1 = 1 ∧
      ∀ i, (P.1.1.2 i).1 = O ∧ (P.1.1.2 i).2.1 ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℝ, c = Pi.single τ (max r 0 + 2) := ⟨_, rfl⟩
  have hcτ : c τ = max r 0 + 2 := by rw [hc, Pi.single_eq_same]
  have hL : LipschitzWith 1 (fun y : Fin 4 → ℝ => max (1 - ‖y - c‖) 0) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have e : (1 - ‖a - c‖) - (1 - ‖b - c‖) = ‖b - c‖ - ‖a - c‖ := by ring
    rw [e]
    have h := abs_norm_sub_norm_le (b - c) (a - c)
    rw [sub_sub_sub_cancel_right] at h
    rw [dist_comm, dist_eq_norm]
    exact h
  have hsupp : ∀ y, max (1 - ‖y - c‖) 0 ≠ 0 → ‖y - c‖ < 1 := by
    intro y hy
    by_contra hge
    exact hy (max_eq_right (by linarith [not_lt.mp hge]))
  have htest : IsTest (fun y : Fin 4 → ℝ => max (1 - ‖y - c‖) 0) (‖c‖ + 1) 1 := by
    refine ⟨by positivity, fun y => ?_, fun y hy i => ?_⟩
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [norm_nonneg (y - c)]) zero_le_one
    · have h1 := hsupp y hy
      have h2 : ‖y‖ ≤ ‖y - c‖ + ‖c‖ := by
        simpa using norm_add_le (y - c) c
      have h3 := norm_le_pi_norm y i
      rw [Real.norm_eq_abs] at h3
      linarith
  let f : TestFn := ⟨fun y => max (1 - ‖y - c‖) 0, ‖c‖ + 1, 1, htest⟩
  let Q : Mono N := ⟨1, fun _ => (O, f)⟩
  have hpa : posAt τ (max r 0 + 1) Q := by
    intro _ y hy
    have h1 : ‖y - c‖ < 1 := hsupp y hy
    have h2 := norm_le_pi_norm (y - c) τ
    rw [Real.norm_eq_abs, Pi.sub_apply, hcτ] at h2
    have h3 := (abs_lt.mp (h2.trans_lt h1)).1
    linarith
  have hlip : LipReg D Q := fun _ => ⟨hO, 1, hL⟩
  refine ⟨⟨⟨Q, max r 0 + 1, by linarith [le_max_right r 0], by linarith [le_max_left r 0], hpa⟩,
    hlip.reg⟩, hlip, rfl, fun _ => ⟨rfl, fun h0 => ?_⟩⟩
  have h1 := congrFun h0 c
  have h2 : max (1 - ‖c - c‖) 0 = (0 : ℝ) := h1
  rw [sub_self, norm_zero, sub_zero, max_eq_left zero_le_one] at h2
  exact one_ne_zero h2

end Load

end

end MassGap.DiniHolder

#print axioms MassGap.DiniHolder.HolderHalf.dyadicDini
#print axioms MassGap.DiniHolder.HolderHalf.add
#print axioms MassGap.DiniHolder.HolderHalf.smul
#print axioms MassGap.DiniHolder.HolderHalf.map
#print axioms MassGap.DiniHolder.holderHalf_of_fixed
#print axioms MassGap.DiniHolder.holderHalf_sub_vac
#print axioms MassGap.DiniHolder.holderHalf_of_sq_bound
#print axioms MassGap.DiniHolder.norm_smul_ej_le
#print axioms MassGap.DiniHolder.LipReg.reg
#print axioms MassGap.DiniHolder.lipschitz_reflect
#print axioms MassGap.DiniHolder.abs_contSF_translate_le_mul
#print axioms MassGap.DiniHolder.abs_kernF_shift_sub_le
#print axioms MassGap.DiniHolder.J_gVec
#print axioms MassGap.DiniHolder.rU_gVec
#print axioms MassGap.DiniHolder.realT_gvecT
#print axioms MassGap.DiniHolder.norm_realT_sub_sq
#print axioms MassGap.DiniHolder.holderHalf_gvecT
#print axioms MassGap.DiniHolder.holderHalf_span
#print axioms MassGap.DiniHolder.holderHalf_span_sub_vac
#print axioms MassGap.DiniHolder.holderHalf_timeT
#print axioms MassGap.DiniHolder.dyadicDini_span
#print axioms MassGap.DiniHolder.dyadicDini_gvecT
#print axioms MassGap.DiniHolder.ae_char_eq_phase_lip
#print axioms MassGap.DiniHolder.inner_U_eq_momentum_lip
#print axioms MassGap.DiniHolder.nu_fst_lip
#print axioms MassGap.DiniHolder.exists_lipReg
