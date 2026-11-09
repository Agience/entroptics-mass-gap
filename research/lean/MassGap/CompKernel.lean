import Mathlib
import MassGap.ShellTranslate
import MassGap.BernsteinWidder

/-!
# MassGap.CompKernel — the two-point form of the observer's composites as a kernel in the separation

`ShellLorentz` step (b) asks that the two-point form of a composite be given by a function of the
separation. This module builds the smeared two-point kernel `kern2` (not the pointwise function of step (b))
for the observer's energy-density composites on the
regular class (fields in the reflection-closed class `D`, uniformly continuous test functions), in
the smeared form, and feeds its time slice to `BernsteinWidder.bernsteinWidder`. Declarations are in
the namespace `MassGap.CompKernel`.

DERIVED: `Fin 4` the spacetime index; `Fin 2` the two factors of a two-point form.

## 1. The two-point kernel (proved)

For two smeared fields `A = (O, f)`, `B = (O', g)` of the regular class, `kern2 A B z` is the
continuum Schwinger function of `A` and `B` translated by `z`.

* `kern2_eq`: the form at `(x, y)`, `S((O, f(· − x)), (O', g(· − y)))`, is `kern2 A B (y − x)`
  (real translation invariance, `ObserverOS.contSF_energy0_translate_real`).
* `continuous_kern2`: `kern2 A B` is continuous on `ℝ⁴` (`ShellTranslate.continuous_contSF_translate`).

## 2. The time slice (proved)

`tVec τ t` is the vector `t e_τ`. For a monomial `P`, `timeKernel P t = S(θP ∪ shift_{t e_τ} P)`, the
reflection kernel of `P` against its time translate.

* `timeKernel_single`: for a one-factor monomial `A`, `timeKernel A t = kern2 (θA) A (t e_τ)`: the
  time slice of the two-point kernel of `θA` and `A`.
* `kernF_tshift`: `S(θ shift_a P ∪ shift_b Q) = S(θP ∪ shift_{a+b} Q)` for real times `a`, `b`
  (the time reflection sends `shift_a` to `shift_{−a}`; then real translation invariance).
* `continuous_timeKernel`: continuous on `ℝ`.
* `timeKernel_reflPos`: for a regular margin monomial, `ReflPos (timeKernel P)`: the sum
  `Σᵢⱼ cᵢ cⱼ C(tᵢ + tⱼ)` is `‖Σᵢ cᵢ gvecT(shift_{tᵢ} P)‖²` in the tree's reconstruction
  (`ContinuumFlow.flow_reconstruction`, which rests on `contSF_gram_nonneg`).
* `timeKernel_dyadic`: at a dyadic time `n a_m`, `C = Re⟪g, stepT_m^n g⟫`, `g = gvecT P`.
* `abs_timeKernel_le`: `|C(t)| ≤ ‖g‖²` for every `t ≥ 0`: at dyadic times from `‖stepT_m^n‖ ≤ 1`
  (`timeT_dyadic`, `timeT_nonneg_norm`), at every other time from continuity of `C` and
  `a_m ⌊t/a_m⌋ → t`.
* `timeKernel_laplaceRep`: `LaplaceRep (timeKernel P)` by `bernsteinWidder`: a finite positive
  measure `σ` on `[0, ∞)` with `C(t) = ∫ e^{−tE} dσ(E)` for `t > 0`.

## What does not follow, plainly

* `kern2` is the smeared kernel `(f, g, z) ↦ ∫∫ f(x) g(y − z) S(x − y)`, not the pointwise
  distribution kernel `S` of `ShellLorentz` step (b). A function `S` continuous off `0` with
  `kern2 = ∫∫ f g S` needs the distribution to be a function, which is not built; nor is it shown that
  `kern2` determines such an `S`.
* `kern2` is proved translation invariant and continuous; its `O(4)` covariance is `KernRadial.kern2_cov`,
  conditional on `KernRadial.O4Inv`. `covC_twoPoint`
  gives `O(4)` invariance of `contC` for a family of composites under `CovC`; that is a different form
  from the energy-density form here, and no rotation of `ℝ⁴` acts on the regular class in the tree.
  So `radial_iff_orthInv` does not yet apply to `kern2`.
* `timeKernel_laplaceRep` is step (c) at zero spatial separation only: one measure per monomial, along
  one time axis. The Stieltjes step (radiality makes the measures of all momenta come from one `ρ`),
  the identification of the measure with `klSec ρ`, and step (d) (the rate × momentum measure of
  `φ(f)Ω` is `klJoint τ ρ |f̂|²`, uniqueness of a measure from its Laplace–Fourier transform) remain.
  Uniqueness of the Bernstein–Widder measure is `SmallClose.laplaceRep_unique`.
* The margin `r` with `(energy0 W D hD).PosPreserving τ r` is a hypothesis of the time-slice results;
  `Flow.posPreserving_of_physRange` supplies it from a physical range.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.CompKernel

open Filter Topology MeasureTheory Set
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate (Reg reg_shift reg_pairFam uniformContinuous_translate
  pairFam_shift_right)
open MassGap.ShellMeasure (ReflPos LaplaceRep)

noncomputable section

variable {N : ℕ} (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

/-! ## 1. The two-point kernel -/

/-- **The two-point kernel**: the continuum Schwinger function of `A` and of `B` translated by `z`.
DERIVED: `Fin 2` the two factors. -/
def kern2 (A B : SField N) (z : Fin 4 → ℝ) : ℝ :=
  contSF hN (energy0 W D hD) ![A, (B.1, B.2.translate z)]

include hpos hcube

/-- **The form at `(x, y)` is the kernel at `y − x`**: real translation invariance of the observer's
Schwinger functions on the regular class. DERIVED: `Fin 2` the two factors. -/
theorem kern2_eq (A B : SField N) (hA : A.1 ∈ D) (hB : B.1 ∈ D) (hAu : UniformContinuous A.2.1)
    (hBu : UniformContinuous B.2.1) (x y : Fin 4 → ℝ) :
    contSF hN (energy0 W D hD) ![(A.1, A.2.translate x), (B.1, B.2.translate y)]
      = kern2 hN W hD A B (y - x) := by
  have h := contSF_energy0_translate_real hN W hD hpos hcube
    (![A, (B.1, B.2.translate (y - x))] : Fin 2 → SField N)
    (Fin.forall_fin_two.mpr ⟨hA, hB⟩)
    (Fin.forall_fin_two.mpr ⟨hAu, uniformContinuous_translate hBu (y - x)⟩) x
  unfold kern2
  rw [← h]
  congr 1
  funext i
  fin_cases i
  · rfl
  · show (B.1, B.2.translate y) = (B.1, (B.2.translate (y - x)).translate x)
    rw [TestFn.translate_translate, sub_add_cancel]

/-- **The kernel is continuous** in the separation. DERIVED: `0` the untranslated first factor;
`Fin 2` the two factors. -/
theorem continuous_kern2 (A B : SField N) (hA : A.1 ∈ D) (hB : B.1 ∈ D)
    (hAu : UniformContinuous A.2.1) (hBu : UniformContinuous B.2.1) :
    Continuous (kern2 hN W hD A B) := by
  have h := ShellTranslate.continuous_contSF_translate hN W hD hpos hcube
    (![A, B] : Fin 2 → SField N) (Fin.forall_fin_two.mpr ⟨hA, hB⟩)
    (Fin.forall_fin_two.mpr ⟨hAu, hBu⟩)
  have hc : Continuous (fun z : Fin 4 → ℝ => (![0, z] : Fin 2 → Fin 4 → ℝ)) :=
    continuous_pi (Fin.forall_fin_two.mpr ⟨continuous_const, continuous_id⟩)
  refine (h.comp hc).congr fun z => ?_
  show contSF hN (energy0 W D hD) (fun i => (((![A, B] : Fin 2 → SField N) i).1,
      ((![A, B] : Fin 2 → SField N) i).2.translate ((![0, z] : Fin 2 → Fin 4 → ℝ) i)))
    = kern2 hN W hD A B z
  unfold kern2
  congr 1
  funext i
  fin_cases i
  · show (A.1, A.2.translate 0) = A
    rw [TestFn.translate_zero]
  · rfl

omit hpos hcube

/-! ## 2. The time slice -/

/-- **The time vector** `t e_τ`. DERIVED: `0` the other components. -/
def tVec (τ : Fin 4) (t : ℝ) : Fin 4 → ℝ := fun j => if j = τ then t else 0

/-- DERIVED: no numeral. -/
theorem tVec_self (τ : Fin 4) (t : ℝ) : tVec τ t τ = t := by simp [tVec]

/-- DERIVED: no numeral. -/
theorem tVec_add (τ : Fin 4) (s t : ℝ) : tVec τ s + tVec τ t = tVec τ (s + t) := by
  funext j
  by_cases h : j = τ <;> simp [tVec, h]

/-- **The time reflection reverses a time vector.** DERIVED: no numeral. -/
theorem reflR_tVec (τ : Fin 4) (t : ℝ) : reflR τ (tVec τ t) = tVec τ (-t) := by
  funext j
  by_cases h : j = τ
  · subst h; simp [reflR, tVec]
  · simp [reflR, tVec, h, Function.update_of_ne h]

/-- DERIVED: no numeral. -/
theorem continuous_tVec (τ : Fin 4) : Continuous (tVec τ) :=
  continuous_pi fun j => by
    show Continuous (fun t : ℝ => if j = τ then t else 0)
    split_ifs
    · exact continuous_id
    · exact continuous_const

/-- **The dyadic time vectors are time vectors**: `timeVec N m τ n = (a_m n) e_τ`. DERIVED: `0` the
other components. -/
theorem timeVec_eq_tVec (m : ℕ) (τ : Fin 4) (n : ℤ) :
    timeVec N m τ n = tVec τ (dySpacing N m * n) := by
  funext j
  by_cases h : j = τ
  · subst h; simp [timeVec, site, axisVec, tVec]
  · simp [timeVec, site, axisVec, tVec, h]

/-- **The time kernel of a monomial**: `S(θP ∪ shift_{t e_τ} P)`. DERIVED: no numeral. -/
def timeKernel (τ : Fin 4) (P : Mono N) (t : ℝ) : ℝ :=
  kernF hN (energy0 W D hD) τ P (Mono.shift (tVec τ t) P)

/-- **For one factor it is the time slice of the two-point kernel**: `timeKernel A t =
kern2 (θA) A (t e_τ)`. DERIVED: `1` the one factor; `Fin 2` the two factors of the form. -/
theorem timeKernel_single (τ : Fin 4) (A : SField N) (t : ℝ) :
    timeKernel hN W hD τ ⟨1, ![A]⟩ t = kern2 hN W hD (SField.refl τ A) A (tVec τ t) := by
  unfold timeKernel kernF kern2
  rw [← contSF_comp_equiv hN (energy0 W D hD) finSumFinEquiv]
  congr 1
  funext x
  rcases x with i | j
  · fin_cases i; rfl
  · fin_cases j; rfl

include hpos hcube

/-- **Real time shifts move across the reflection**: `S(θ shift_a P ∪ shift_b Q) =
S(θP ∪ shift_{a+b} Q)` for regular monomials. DERIVED: no numeral. -/
theorem kernF_tshift (τ : Fin 4) {P Q : Mono N} (hP : Reg D P) (hQ : Reg D Q) (a b : ℝ) :
    kernF hN (energy0 W D hD) τ (Mono.shift (tVec τ a) P) (Mono.shift (tVec τ b) Q)
      = kernF hN (energy0 W D hD) τ P (Mono.shift (tVec τ (a + b)) Q) := by
  have hR := reg_pairFam hD τ hP (reg_shift hQ (tVec τ (a + b)))
  have h := contSF_energy0_translate_real hN W hD hpos hcube
    (pairFam τ P (Mono.shift (tVec τ (a + b)) Q)) (fun x => (hR x).1) (fun x => (hR x).2)
    (tVec τ (-a))
  unfold kernF
  rw [← h]
  congr 1
  funext x
  rcases x with i | j
  · show ((P.2 i).1.refl τ, ((P.2 i).2.translate (tVec τ a)).reflect τ)
      = ((P.2 i).1.refl τ, ((P.2 i).2.reflect τ).translate (tVec τ (-a)))
    rw [TestFn.reflect_translate, reflR_tVec]
  · show ((Q.2 j).1, (Q.2 j).2.translate (tVec τ b))
      = ((Q.2 j).1, ((Q.2 j).2.translate (tVec τ (a + b))).translate (tVec τ (-a)))
    rw [TestFn.translate_translate, tVec_add]
    congr 3
    ring

/-- **The time kernel is continuous.** DERIVED: `0` the untranslated reflected block. -/
theorem continuous_timeKernel (τ : Fin 4) {P : Mono N} (hP : Reg D P) :
    Continuous (timeKernel hN W hD τ P) := by
  have hR := reg_pairFam hD τ hP hP
  have h := ShellTranslate.continuous_contSF_translate hN W hD hpos hcube (pairFam τ P P)
    (fun x => (hR x).1) (fun x => (hR x).2)
  have hc : Continuous (fun t : ℝ => fun x : Fin P.1 ⊕ Fin P.1 =>
      Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => tVec τ t) x) :=
    continuous_pi fun x => by
      cases x with
      | inl i => exact continuous_const
      | inr j => exact continuous_tVec τ
  refine (h.comp hc).congr fun t => ?_
  exact congrArg (fun G => contSF hN (energy0 W D hD) G) (pairFam_shift_right τ P P (tVec τ t)).symm

omit hpos hcube

/-- **A margin monomial shifted forward in time** is a margin monomial. DERIVED: `0` the sign of the
shift. -/
def mshift (τ : Fin 4) {r : ℝ} (t : ℝ) (ht : 0 ≤ t) (P : MarginMono N τ r) : MarginMono N τ r :=
  ⟨Mono.shift (tVec τ t) P.1, by
    obtain ⟨d, hd, hrd, hP⟩ := P.2
    exact ⟨d, hd, hrd, posAt_shift hP (by rw [tVec_self]; exact ht)⟩⟩

/-- **The reconstruction reads the kernel** (`flow_reconstruction` at step `0`). DERIVED: `0` the
reference step. -/
theorem inner_gvecT (Φ : Flow N) (hB : UniformBoundF hN Φ) (τ : Fin 4) {r : ℝ}
    (hpp : Φ.PosPreserving τ r) (A B : MarginMono N τ r) :
    inner ℂ (gvecT hN Φ hB τ hpp A) (gvecT hN Φ hB τ hpp B) = (kernF hN Φ τ A.1 B.1 : ℂ) :=
  (flow_reconstruction hN Φ hB τ hpp 0).2 A B

include hpos hcube

/-- **The time kernel is reflection positive**: `Σᵢⱼ cᵢ cⱼ C(tᵢ + tⱼ) = ‖Σᵢ cᵢ gᵢ‖²` with
`gᵢ = gvecT (shift_{tᵢ} P)`. DERIVED: `0` the sign. -/
theorem timeKernel_reflPos (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) : ReflPos (timeKernel hN W hD τ P.1) := by
  intro n c t ht
  set hB := uniformBoundF_energy0 hN W D hD hpos hcube
  let g : Fin n → FlowH hN (energy0 W D hD) hB τ hpp := fun i =>
    gvecT hN (energy0 W D hD) hB τ hpp (mshift τ (t i) (ht i).le P)
  have key : ∀ i j, timeKernel hN W hD τ P.1 (t i + t j) = (inner ℂ (g i) (g j)).re := by
    intro i j
    rw [inner_gvecT, Complex.ofReal_re]
    exact (kernF_tshift hN W hD hpos hcube τ hP hP (t i) (t j)).symm
  set v := ∑ i, (c i : ℂ) • g i
  have hv : 0 ≤ (inner ℂ v v).re := by
    have := inner_self_nonneg (𝕜 := ℂ) (x := v)
    simpa using this
  have hexpC : inner ℂ v v = ∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * inner ℂ (g i) (g j) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right]
    push_cast
    ring
  have hexp : (inner ℂ v v).re = ∑ i, ∑ j, c i * c j * (inner ℂ (g i) (g j)).re := by
    rw [hexpC, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul]
  calc (0 : ℝ) ≤ _ := hv
    _ = _ := hexp
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [key]

/-- **At dyadic times the time kernel is a matrix element of the step**: `C(a_m n) =
Re⟪g, stepT_m^n g⟫`. DERIVED: `0` the base of the induction. -/
theorem timeKernel_dyadic (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (m n : ℕ) :
    timeKernel hN W hD τ P.1 (dySpacing N m * n)
      = (inner ℂ (gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp P)
          ((stepT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp m ^ n)
            (gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp P))).re := by
  set hB := uniformBoundF_energy0 hN W D hD hpos hcube
  have hit : ∀ (k : ℕ) (Q : MarginMono N τ r),
      (stepT hN (energy0 W D hD) hB τ hpp m ^ k) (gvecT hN (energy0 W D hD) hB τ hpp Q)
        = gvecT hN (energy0 W D hD) hB τ hpp ((MarginMono.shift hN τ m)^[k] Q) := by
    intro k
    induction k with
    | zero => intro Q; rfl
    | succ k ih =>
      intro Q
      rw [pow_succ, ContinuousLinearMap.mul_apply, stepT_gvecT, ih, Function.iterate_succ_apply]
  rw [hit, inner_gvecT, Complex.ofReal_re, MarginMono.shift_iterate, timeVec_eq_tVec]
  unfold timeKernel
  push_cast
  rfl

/-- **The time kernel is bounded by the norm of the vector** on `[0, ∞)`. DERIVED: `0` the sign of
the time; `1` the norm bound of the step and the floor offset; `2` the square. -/
theorem abs_timeKernel_le (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) {t : ℝ} (ht : 0 ≤ t) :
    |timeKernel hN W hD τ P.1 t|
      ≤ ‖gvecT hN (energy0 W D hD) (uniformBoundF_energy0 hN W D hD hpos hcube) τ hpp P‖ ^ 2 := by
  set hB := uniformBoundF_energy0 hN W D hD hpos hcube
  set g := gvecT hN (energy0 W D hD) hB τ hpp P
  have hdy : ∀ m n : ℕ, |timeKernel hN W hD τ P.1 (dySpacing N m * n)| ≤ ‖g‖ ^ 2 := by
    intro m n
    rw [timeKernel_dyadic hN W hD hpos hcube τ hpp P m n]
    have hT : ‖stepT hN (energy0 W D hD) hB τ hpp m ^ n‖ ≤ 1 := by
      rw [← timeT_dyadic]
      exact (timeT_nonneg_norm hN (energy0 W D hD) hB τ hpp _
        (mul_nonneg (Nat.cast_nonneg n) (dySpacing_pos (one_le_of_ne_zero hN) m).le)).2.2
    calc |(inner ℂ g ((stepT hN (energy0 W D hD) hB τ hpp m ^ n) g)).re|
        ≤ ‖inner ℂ g ((stepT hN (energy0 W D hD) hB τ hpp m ^ n) g)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖g‖ * ‖(stepT hN (energy0 W D hD) hB τ hpp m ^ n) g‖ := norm_inner_le_norm _ _
      _ ≤ ‖g‖ * (‖stepT hN (energy0 W D hD) hB τ hpp m ^ n‖ * ‖g‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖g‖ * (1 * ‖g‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT (norm_nonneg _)) (norm_nonneg _)
      _ = ‖g‖ ^ 2 := by ring
  set s : ℕ → ℝ := fun m => dySpacing N m * (⌊t / dySpacing N m⌋₊ : ℝ)
  have hs_le : ∀ m, s m ≤ t := fun m => by
    have ha := dySpacing_pos (one_le_of_ne_zero hN) m
    have h1 : (⌊t / dySpacing N m⌋₊ : ℝ) ≤ t / dySpacing N m := Nat.floor_le (div_nonneg ht ha.le)
    calc s m ≤ dySpacing N m * (t / dySpacing N m) := mul_le_mul_of_nonneg_left h1 ha.le
      _ = t := by field_simp
  have hs_ge : ∀ m, t - dySpacing N m ≤ s m := fun m => by
    have ha := dySpacing_pos (one_le_of_ne_zero hN) m
    have h1 : t / dySpacing N m < (⌊t / dySpacing N m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : t < dySpacing N m * ((⌊t / dySpacing N m⌋₊ : ℝ) + 1) := by
      have := mul_lt_mul_of_pos_left h1 ha
      rwa [show dySpacing N m * (t / dySpacing N m) = t by field_simp] at this
    show t - dySpacing N m ≤ dySpacing N m * (⌊t / dySpacing N m⌋₊ : ℝ)
    nlinarith
  have hlow : Tendsto (fun m => t - dySpacing N m) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub (tendsto_dySpacing N)
  have hst : Tendsto s atTop (𝓝 t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_ge hs_le
  have hC := ((continuous_abs.comp (continuous_timeKernel hN W hD hpos hcube τ hP)).tendsto t).comp hst
  exact le_of_tendsto' hC fun m => hdy m _

/-- **The time kernel is a Laplace transform** (`BernsteinWidder.bernsteinWidder`): for a regular
margin monomial, a finite positive measure `σ` on `[0, ∞)` with `C(t) = ∫ e^{−tE} dσ(E)` for every
`t > 0`. DERIVED: `0` the sign of the time. -/
theorem timeKernel_laplaceRep (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) : LaplaceRep (timeKernel hN W hD τ P.1) :=
  BernsteinWidder.bernsteinWidder (timeKernel_reflPos hN W hD hpos hcube τ hpp P hP)
    (continuous_timeKernel hN W hD hpos hcube τ hP).continuousOn
    ⟨_, fun _ ht => abs_timeKernel_le hN W hD hpos hcube τ hpp P hP ht.le⟩

/-- **For one regular factor**: the time slice `t ↦ kern2 (θA) A (t e_τ)` of the two-point kernel is
a Laplace transform. DERIVED: `1` the one factor. -/
theorem kern2_time_laplaceRep (τ : Fin 4) {r : ℝ} (hpp : (energy0 W D hD).PosPreserving τ r)
    (P : MarginMono N τ r) (hP : Reg D P.1) (A : SField N) (hPA : P.1 = ⟨1, ![A]⟩) :
    LaplaceRep (fun t => kern2 hN W hD (SField.refl τ A) A (tVec τ t)) := by
  have h := timeKernel_laplaceRep hN W hD hpos hcube τ hpp P hP
  rw [hPA] at h
  have e : timeKernel hN W hD τ ⟨1, ![A]⟩ = fun t => kern2 hN W hD (SField.refl τ A) A (tVec τ t) :=
    funext (timeKernel_single hN W hD τ A)
  rw [e] at h
  exact h

end

end MassGap.CompKernel

#print axioms MassGap.CompKernel.kern2_eq
#print axioms MassGap.CompKernel.continuous_kern2
#print axioms MassGap.CompKernel.tVec_self
#print axioms MassGap.CompKernel.tVec_add
#print axioms MassGap.CompKernel.reflR_tVec
#print axioms MassGap.CompKernel.continuous_tVec
#print axioms MassGap.CompKernel.timeVec_eq_tVec
#print axioms MassGap.CompKernel.timeKernel_single
#print axioms MassGap.CompKernel.kernF_tshift
#print axioms MassGap.CompKernel.continuous_timeKernel
#print axioms MassGap.CompKernel.inner_gvecT
#print axioms MassGap.CompKernel.timeKernel_reflPos
#print axioms MassGap.CompKernel.timeKernel_dyadic
#print axioms MassGap.CompKernel.abs_timeKernel_le
#print axioms MassGap.CompKernel.timeKernel_laplaceRep
#print axioms MassGap.CompKernel.kern2_time_laplaceRep
