import Mathlib
import MassGap.DiniHolder

/-!
# MassGap.RegularDense — the regular sector as a reconstruction of its own, and the Lipschitz vectors dense in it

`ShellTranslate` builds the real translations only on the regular sector `V = range J` of `FlowH` and
sets `realT` to the identity on `V⊥`. `DiniHolder` proves the Hölder bound on the span of the Lipschitz
vectors. This module works on `RH` itself, so neither caveat applies there; on `FlowH` the identity on `V⊥` stays. Declarations are in the namespace
`MassGap.RegularDense`.

## Density of the Lipschitz vectors (proved)

* `exists_lipschitz_approx`: a bounded uniformly continuous function is a sup-norm limit of Lipschitz
  functions, by the infimal convolution `g x = ⨅ y, f y + K dist x y`.
* `exists_lipFn`: for a uniformly continuous test function the approximant is a test function with
  `|h| ≤ |f|` pointwise. The soft threshold of `g` at the sup-norm error gives this, so `h` keeps the
  support of `f`: the same cube, the same bound and the same time margin.
* `tendsto_contSF_of_sup`, `tendsto_kernF_mod`, `tendsto_gVec_lip`: form-norm continuity, from
  `ObserverOS.abs_contSF_energy0_sub_le`.
* `dense_span_rLipVecs`: the complex span of the Lipschitz vectors is dense in `RH`.
  `closure_span_lipVecs`: on `FlowH`, the closure of `span lipVecs` is exactly `V`. This closes the
  density caveat of `DiniHolder` within `V`; it says nothing about `V⊥`.

## The reduced reconstruction (proved)

`SubSector X R`: an isometry `J : R → X.H` with a vacuum, whose range projection commutes with the unit
step of the `OSDataS` `X`, and a non-zero vector orthogonal to that vacuum. `reduce Y : OSDataS` is the
reconstruction on `R`: the Schwinger functions and growth of `X`, the vacuum of `R`, the compressed
time `J† (X.time t) J`, and the gap of `X`. Because `reduce Y` is an `OSDataS`, every theorem of
`ShellGap` and `ShellMomentum` about an arbitrary `OSDataS` applies to it as stated, in particular
`gap_iff_rateBottom`, `gap_rateBottom`, `gap_le_of_specBottom` and `clay_zero_momentum_sector`.
`J_reduce_time`, `norm_reduce_time`: `J` intertwines the two times. `reduce_rateBottom_iff`: a rate
bottom of `u` in `reduce Y` is a rate bottom of `J u` in `X`.

`observerReduced`: the instance on `RH`, on the inputs of `observerOSDataS` with `FlowConnectedNonzero`
replaced by `RegConnectedNonzero`, its witness taken regular. `RegConnectedNonzero.flow`: this implies
the input it replaces. `exists_lip_connected`: the witness can always be taken Lipschitz.

`regSpatial`: the `SpatialData` of `observerReduced` with `rU`. There is no complement in `RH`, so
there is no identity branch: `mem_zeroMom_regSpatial_iff` identifies its zero-momentum space with the
vectors of `V` that `realT` fixes, and the `V⊥` part of `observerRealSpatial`'s zero-momentum space
is gone. `regRep`, `regData`, `holderHalf_reg`, `dyadicDini_reg`: the representation, the joint data
and the Dini bound on `RH`.

## What does not follow

Plainly:

* Option (a), `V = FlowH`, is neither proved nor refuted. `FlowH` is built on every local field and
  every bounded test function of bounded support. A uniform limit of uniformly continuous functions is
  uniformly continuous, so a test function that is not uniformly continuous is not a sup-norm limit of
  regular ones, and the continuity of the Schwinger functions in their test functions available here,
  `abs_contSF_energy0_sub_le`, is in sup norm. For a field outside `D`, `energy0` does not scale it, and
  `hpos`, `hcube` say nothing about it; its smeared moments are bounded directly
  (`RegularFull.allMom_energy0`), so the sup-norm estimates hold at every local field. Whether `V⊥` is zero
  is not decided.
* `reduce Y` uses the gap of `X`. The gap of `FlowH` is a lower bound for the gap on `RH`; the converse
  does not follow, and `reduce_rateBottom_iff` is for vectors of `R` only.
* `RegConnectedNonzero` is stronger than `FlowConnectedNonzero`: it is not derived from it. It is an
  input here, with the same lattice route (`ObserverNontrivial.flowConnectedNonzero_of_lattice` at a
  regular `Q`), and it is not discharged.
* The reduced object is an `OSDataS`, not an `OSDataSLinked`, and `ClayFull`, `ClayStatement` still
  name `observerOSDataS` on `FlowH`.
* Density does not extend `DyadicDini` to all of `RH`: it is not closed under limits, and `L` in
  `holderHalf_reg` depends on the vector. The bound is relative to `hpos`, `hcube`.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.RegularDense

open Filter Topology MeasureTheory
open scoped NNReal
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellTranslate
open MassGap.ShellMeasure (rateMeasure)
open MassGap.ShellMomentum (SpatialData zeroMom)
open MassGap.ShellJoint (JointData treeData)
open MassGap.ShellDensity (DyadicDini)
open MassGap.DiniHolder (HolderHalf LipReg lipVecs holderHalf_span)
open MassGap.ShellGap (time_eq_powT time_isSelfAdjoint spectrum_time bound_iff_rateBottom
  spectrum_Icc_of_nonneg)
open MassGap.ObserverOSReconstructionS (OSDataS observerOSDataS)

noncomputable section

/-! ## 1. Lipschitz approximation of test functions -/

section Approx

/-- **A bounded uniformly continuous function is a sup-norm limit of Lipschitz functions**: the
infimal convolution `g x = ⨅ y, f y + K dist x y`, with `K = (2 M + 1)/η`, `η` the modulus of `f` at
`δ`. It lies below `f`, and above `f − δ`: at `dist x y < η` by the modulus, at `dist x y ≥ η` because
the slope pays for the whole range `2 M` of `f`. DERIVED: `0` the sign of `δ`, `M`, `K`; `2` the range
`[−M, M]`; `1` keeps `K` positive at `M = 0`. -/
theorem exists_lipschitz_approx {E : Type*} [PseudoMetricSpace E] [Nonempty E] {f : E → ℝ}
    (hf : UniformContinuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℝ≥0) (g : E → ℝ), LipschitzWith K g ∧ ∀ y, |g y - f y| ≤ δ := by
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuous_iff.mp hf δ hδ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary E))
  have hKpos : 0 ≤ (2 * M + 1) / η := by positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, (K : ℝ) = (2 * M + 1) / η := ⟨⟨_, hKpos⟩, rfl⟩
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hbd : ∀ x, BddBelow (Set.range fun y => f y + K * dist x y) := fun x => ⟨-M, by
    rintro _ ⟨y, rfl⟩
    have h1 := (abs_le.mp (hM y)).1
    have h2 : 0 ≤ (K : ℝ) * dist x y := mul_nonneg hK0 dist_nonneg
    show -M ≤ f y + K * dist x y
    linarith⟩
  let g : E → ℝ := fun x => ⨅ y, f y + K * dist x y
  have hle : ∀ x y, g x ≤ f y + K * dist x y := fun x y => ciInf_le (hbd x) y
  have hup : ∀ x, g x ≤ f x := fun x => by simpa using hle x x
  have hlo : ∀ x, f x - δ ≤ g x := fun x => by
    refine le_ciInf fun y => ?_
    have h2 : 0 ≤ (K : ℝ) * dist x y := mul_nonneg hK0 dist_nonneg
    by_cases hxy : dist x y < η
    · have h3 := hmod hxy
      rw [Real.dist_eq] at h3
      linarith [(abs_lt.mp h3).2]
    · have h3 : (2 * M + 1) ≤ (K : ℝ) * dist x y := by
        have h4 : (K : ℝ) * η = 2 * M + 1 := by rw [hK]; field_simp
        rw [← h4]
        exact mul_le_mul_of_nonneg_left (not_lt.mp hxy) hK0
      linarith [(abs_le.mp (hM y)).1, (abs_le.mp (hM x)).2]
  refine ⟨K, g, LipschitzWith.of_le_add_mul K fun x x' => ?_, fun y => ?_⟩
  · have hc : g x - K * dist x x' ≤ g x' := le_ciInf fun y => by
      have h1 := hle x y
      have h2 : (K : ℝ) * dist x y ≤ K * (dist x x' + dist x' y) :=
        mul_le_mul_of_nonneg_left (dist_triangle _ _ _) hK0
      nlinarith
    linarith
  · exact abs_le.mpr ⟨by linarith [hlo y], by linarith [hup y, hδ]⟩

/-- **A uniformly continuous test function is a sup-norm limit of Lipschitz test functions below it.**
Take `g` within `δ/2` of `f`, and `h = max (g − δ/2) 0 + min (g + δ/2) 0`, its soft threshold. Then
`|h| ≤ |f|` pointwise, so `h` has the support of `f`, and `|h − f| ≤ δ`. DERIVED: `2` the half of the
error given to `g`; `0` the floor of the threshold; `1` the Lipschitz constant of the threshold. -/
theorem exists_lipFn (f : TestFn) (hf : UniformContinuous f.1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : TestFn, (∃ K : ℝ≥0, LipschitzWith K h.1) ∧ (∀ y, |h.1 y| ≤ |f.1 y|)
      ∧ ∀ y, |h.1 y - f.1 y| ≤ δ := by
  obtain ⟨R, M, hRM⟩ := f.2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = δ / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨K, g, hg, hgf⟩ := exists_lipschitz_approx hf hRM.2.1 hc0
  let h0 : (Fin 4 → ℝ) → ℝ := fun y => max (g y - c) 0 + min (g y + c) 0
  have hdom : ∀ y, |h0 y| ≤ |f.1 y| := fun y => by
    obtain ⟨h1, h2⟩ := abs_le.mp (hgf y)
    have a1 := le_abs_self (f.1 y)
    have a2 := neg_abs_le (f.1 y)
    have a3 := abs_nonneg (f.1 y)
    show |max (g y - c) 0 + min (g y + c) 0| ≤ _
    rcases max_cases (g y - c) 0 with ⟨e1, c1⟩ | ⟨e1, c1⟩ <;>
      rcases min_cases (g y + c) 0 with ⟨e2, c2⟩ | ⟨e2, c2⟩ <;> rw [e1, e2] <;>
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  have hclose : ∀ y, |h0 y - f.1 y| ≤ δ := fun y => by
    obtain ⟨h1, h2⟩ := abs_le.mp (hgf y)
    show |max (g y - c) 0 + min (g y + c) 0 - f.1 y| ≤ _
    rcases max_cases (g y - c) 0 with ⟨e1, c1⟩ | ⟨e1, c1⟩ <;>
      rcases min_cases (g y + c) 0 with ⟨e2, c2⟩ | ⟨e2, c2⟩ <;> rw [e1, e2] <;>
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  have hsupp : ∀ y, h0 y ≠ 0 → f.1 y ≠ 0 := fun y hy h0y => hy (by
    have := hdom y
    rw [h0y, abs_zero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
  refine ⟨⟨h0, R, M, hRM.1, fun y => (hdom y).trans (hRM.2.1 y),
    fun y hy => hRM.2.2 y (hsupp y hy)⟩, ?_, hdom, hclose⟩
  have h1 : LipschitzWith K fun y => max (g y - c) 0 := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have e : (g a - c) - (g b - c) = g a - g b := by ring
    rw [e, ← Real.dist_eq]
    exact hg.dist_le_mul a b
  have h2 : LipschitzWith K fun y => min (g y + c) 0 := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq]
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    have e : (g a + c) - (g b + c) = g a - g b := by ring
    have e0 : |(0 : ℝ) - 0| = 0 := by simp
    rw [e, e0, max_eq_left (abs_nonneg _), ← Real.dist_eq]
    exact hg.dist_le_mul a b
  exact ⟨K + K, h1.add h2⟩

/-- The `k`-th error. DERIVED: `1` the unit; the shift by `1` keeps it positive. -/
def err (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- DERIVED: `0` the sign. -/
theorem err_pos (k : ℕ) : 0 < err k := by unfold err; positivity

/-- DERIVED: `0` the limit. -/
theorem tendsto_err : Tendsto err atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- The `k`-th Lipschitz approximant of a uniformly continuous test function. DERIVED: no numeral. -/
def lipFn (k : ℕ) (f : TestFn) (hf : UniformContinuous f.1) : TestFn :=
  Classical.choose (exists_lipFn f hf (err_pos k))

/-- DERIVED: no numeral. -/
theorem lipFn_lip (k : ℕ) (f : TestFn) (hf : UniformContinuous f.1) :
    ∃ K : ℝ≥0, LipschitzWith K (lipFn k f hf).1 :=
  (Classical.choose_spec (exists_lipFn f hf (err_pos k))).1

/-- DERIVED: no numeral. -/
theorem lipFn_dom (k : ℕ) (f : TestFn) (hf : UniformContinuous f.1) (y : Fin 4 → ℝ) :
    |(lipFn k f hf).1 y| ≤ |f.1 y| :=
  (Classical.choose_spec (exists_lipFn f hf (err_pos k))).2.1 y

/-- DERIVED: no numeral. -/
theorem lipFn_close (k : ℕ) (f : TestFn) (hf : UniformContinuous f.1) (y : Fin 4 → ℝ) :
    |(lipFn k f hf).1 y - f.1 y| ≤ err k :=
  (Classical.choose_spec (exists_lipFn f hf (err_pos k))).2.2 y

end Approx

/-! ## 2. Form-norm continuity -/

section FormNorm

variable {N : ℕ}

/-- A monomial with the same fields and new test functions. DERIVED: no numeral. -/
def modMono (P : Mono N) (a : Fin P.1 → TestFn) : Mono N := ⟨P.1, fun i => ((P.2 i).1, a i)⟩

/-- The `k`-th Lipschitz approximant of a regular monomial. DERIVED: no numeral. -/
def lipMono {D : Set (LField (MassGap.SUN.SU N))} (k : ℕ) (P : Mono N) (hP : Reg D P) : Mono N :=
  modMono P fun i => lipFn k (P.2 i).2 (hP i).2

/-- DERIVED: no numeral. -/
theorem lipMono_lipReg {D : Set (LField (MassGap.SUN.SU N))} (k : ℕ) {P : Mono N} (hP : Reg D P) :
    LipReg D (lipMono k P hP) :=
  fun i => ⟨(hP i).1, lipFn_lip k (P.2 i).2 (hP i).2⟩

/-- The `k`-th Lipschitz approximant of a regular margin monomial: the support, hence the margin, is
kept. DERIVED: `0` the excluded value. -/
def lipR {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ} (k : ℕ) (P : RMono N D τ r) :
    RMono N D τ r :=
  ⟨⟨lipMono k P.1.1 P.2, by
    obtain ⟨d, hd, hrd, hp⟩ := P.1.2
    refine ⟨d, hd, hrd, fun i y hy => hp i y fun h0 => hy ?_⟩
    have h1 := lipFn_dom k (P.1.1.2 i).2 (P.2 i).2 y
    rw [h0, abs_zero] at h1
    exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))⟩, (lipMono_lipReg k P.2).reg⟩

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

include hpos hcube

/-- **Sup-norm convergence of the test functions gives convergence of the limit Schwinger function**,
for fields of `D` and approximants dominated by `|fᵢ|`, which keeps every approximant in one cube at
one bound. `abs_contSF_energy0_sub_le` gives the rate `A δₖ`, `A` the moment constant; the cube is built
as in `tendsto_contSF_translate`. DERIVED: `0` the limit and the signs; `1` the cube margin and the
coefficient; `2` makes the moment even; `4` in `Fin 4` the spacetime dimension. -/
theorem tendsto_contSF_of_sup {ι : Type} [Fintype ι] (F : ι → SField N) (hG : ∀ i, (F i).1 ∈ D)
    (G : ℕ → ι → SField N) (hfield : ∀ k i, (G k i).1 = (F i).1)
    (hdom : ∀ k i y, |(G k i).2.1 y| ≤ |(F i).2.1 y|) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k i y, |(G k i).2.1 y - (F i).2.1 y| ≤ δ k) :
    Tendsto (fun k => contSF hN (energy0 W D hD) (G k)) atTop
      (𝓝 (contSF hN (energy0 W D hD) F)) := by
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
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = (1 + Fintype.card ι * ∑ i, |C i|) * ∑ a, ∏ i ∈ Finset.univ \ {a}, M i := ⟨_, rfl⟩
  have hF : ∀ i, IsTest (F i).2.1 R (M i) := fun i =>
    ⟨hR0, (hRM i).2.1, fun y hy j => ((hRM i).2.2 y hy j).trans (by linarith [hRi i])⟩
  have hF' : ∀ k i, IsTest (G k i).2.1 R (M i) := fun k i =>
    ⟨hR0, fun y => (hdom k i y).trans ((hF i).2.1 y), fun y hy j => (hF i).2.2 y (fun h0 => hy (by
      have h1 := hdom k i y
      rw [h0, abs_zero] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _)))) j⟩
  have hbound : ∀ k, |contSF hN (energy0 W D hD) (G k) - contSF hN (energy0 W D hD) F| ≤ δ k * A := by
    intro k
    have h := abs_contSF_energy0_sub_le hN W hD hpos hB F (G k) (hfield k) hG hR0 hc M hF (hF' k)
      (hclose k)
    have hsum : (1 + Fintype.card ι * ∑ i, |C i|) * ∑ a, δ k * ∏ i ∈ Finset.univ \ {a}, M i
        = δ k * A := by
      rw [hAdef, ← Finset.mul_sum]
      ring
    rwa [hsum] at h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) (g := fun k => δ k * A)
    (by simpa using hδ.mul_const A)
  rw [Real.dist_eq]
  exact hbound k

/-- **The reflection kernel converges** when both monomials converge in the sense of
`tendsto_contSF_of_sup`. DERIVED: `0` the limit; `4` in `Fin 4` the spacetime dimension. -/
theorem tendsto_kernF_mod (τ : Fin 4) {P Q : Mono N} (hP : Reg D P) (hQ : Reg D Q)
    (a : ℕ → Fin P.1 → TestFn) (b : ℕ → Fin Q.1 → TestFn)
    (ha : ∀ k i y, |(a k i).1 y| ≤ |(P.2 i).2.1 y|) (hb : ∀ k i y, |(b k i).1 y| ≤ |(Q.2 i).2.1 y|)
    (ha' : ∀ k i y, |(a k i).1 y - (P.2 i).2.1 y| ≤ err k)
    (hb' : ∀ k i y, |(b k i).1 y - (Q.2 i).2.1 y| ≤ err k) :
    Tendsto (fun k => kernF hN (energy0 W D hD) τ (modMono P (a k)) (modMono Q (b k))) atTop
      (𝓝 (kernF hN (energy0 W D hD) τ P Q)) :=
  tendsto_contSF_of_sup hN W hD hpos hcube (pairFam τ P Q)
    (fun x => (reg_pairFam hD τ hP hQ x).1)
    (fun k => pairFam τ (modMono P (a k)) (modMono Q (b k)))
    (fun k x => by cases x <;> rfl)
    (fun k x y => by
      cases x with
      | inl i => exact ha k i _
      | inr j => exact hb k j _)
    tendsto_err
    (fun k x y => by
      cases x with
      | inl i => exact ha' k i _
      | inr j => exact hb' k j _)

omit hpos hcube in
/-- A fixed family as a constant approximation. DERIVED: `0` the distance. -/
theorem self_close (f : TestFn) (k : ℕ) (y : Fin 4 → ℝ) : |f.1 y - f.1 y| ≤ err k := by
  rw [sub_self, abs_zero]
  exact (err_pos k).le

variable (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

/-- **The Lipschitz approximants converge in the form norm**: `‖u_k − u‖² = K(P_k, P_k) −
2 K(P_k, P) + K(P, P) → 0`. DERIVED: `0` the limit and the reference step; `2` the square and the cross
term. -/
theorem tendsto_gVec_lip (P : RMono N D τ r) :
    Tendsto (fun k => gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) (lipR k P)) atTop
      (𝓝 (gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) P)) := by
  have hin : ∀ A B : RMono N D τ r,
      inner ℂ (gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) A)
        (gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) B)
        = (kernF hN (energy0 W D hD) τ A.1.1 B.1.1 : ℂ) := fun A B =>
    inner_gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) (rKern hN (energy0 W D hD) τ)
      (fun _ _ => rfl) A B
  have hre : ∀ A B : RMono N D τ r,
      RCLike.re (inner ℂ (gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) A)
        (gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) B))
        = kernF hN (energy0 W D hD) τ A.1.1 B.1.1 := fun A B => by
    rw [hin]; exact Complex.ofReal_re _
  have hsq : ∀ k, ‖gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) (lipR k P)
        - gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) P‖ ^ 2
      = kernF hN (energy0 W D hD) τ (lipR k P).1.1 (lipR k P).1.1
        - 2 * kernF hN (energy0 W D hD) τ (lipR k P).1.1 P.1.1
        + kernF hN (energy0 W D hD) τ P.1.1 P.1.1 := fun k => by
    rw [norm_sub_sq (𝕜 := ℂ), hre, ← inner_self_eq_norm_sq (𝕜 := ℂ),
      ← inner_self_eq_norm_sq (𝕜 := ℂ), hre, hre]
  have h1 : Tendsto (fun k => kernF hN (energy0 W D hD) τ (lipR k P).1.1 (lipR k P).1.1) atTop
      (𝓝 (kernF hN (energy0 W D hD) τ P.1.1 P.1.1)) :=
    tendsto_kernF_mod hN W hD hpos hcube τ P.2 P.2 _ _
      (fun k i y => lipFn_dom k _ _ y) (fun k i y => lipFn_dom k _ _ y)
      (fun k i y => lipFn_close k _ _ y) (fun k i y => lipFn_close k _ _ y)
  have h2 : Tendsto (fun k => kernF hN (energy0 W D hD) τ (lipR k P).1.1 P.1.1) atTop
      (𝓝 (kernF hN (energy0 W D hD) τ P.1.1 P.1.1)) :=
    tendsto_kernF_mod hN W hD hpos hcube τ P.2 P.2 _ (fun _ i => (P.1.1.2 i).2)
      (fun k i y => lipFn_dom k _ _ y) (fun _ _ _ => le_rfl)
      (fun k i y => lipFn_close k _ _ y) (fun k i y => self_close _ k y)
  have h3 : Tendsto (fun k => ‖gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) (lipR k P)
        - gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) P‖ ^ 2) atTop (𝓝 0) := by
    have h4 := (h1.sub (h2.const_mul 2)).add_const (kernF hN (energy0 W D hD) τ P.1.1 P.1.1)
    have e : kernF hN (energy0 W D hD) τ P.1.1 P.1.1
        - 2 * kernF hN (energy0 W D hD) τ P.1.1 P.1.1
        + kernF hN (energy0 W D hD) τ P.1.1 P.1.1 = 0 := by ring
    rw [e] at h4
    exact h4.congr fun k => (hsq k).symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h5 := (Real.continuous_sqrt.tendsto 0).comp h3
  rw [Real.sqrt_zero] at h5
  exact h5.congr fun k => Real.sqrt_sq (norm_nonneg _)

end FormNorm

/-! ## 3. Density -/

section Density

variable {N : ℕ} (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
  (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

/-- The Lipschitz vectors of the regular sector. DERIVED: `0` the reference step. -/
def rLipVecs : Set (RH hN (energy0 W D hD) hB D τ hpp) :=
  {u | ∃ P : RMono N D τ r, LipReg D P.1.1 ∧
    u = gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) P}

include hpos hcube

/-- **The Lipschitz vectors are dense in the regular sector**: `gVec (lipR k P) → gVec P`, every real
combination of regular monomials is a limit of the span, and every vector of `RH` is a limit of those
pairs. DERIVED: `0` the reference step, the zero vector and the imaginary component; `1` the
coefficient. -/
theorem dense_span_rLipVecs :
    Dense ((Submodule.span ℂ (rLipVecs hN W hD hB τ hpp) :
      Submodule ℂ (RH hN (energy0 W D hD) hB D τ hpp)) : Set (RH hN (energy0 W D hD) hB D τ hpp)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  obtain ⟨S, hS⟩ : ∃ S, S = (Submodule.span ℂ (rLipVecs hN W hD hB τ hpp)).topologicalClosure :=
    ⟨_, rfl⟩
  rw [← hS]
  have hclosed : IsClosed (S : Set (RH hN (energy0 W D hD) hB D τ hpp)) := by
    rw [hS]; exact Submodule.isClosed_topologicalClosure _
  have hg : ∀ P : RMono N D τ r, gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) P ∈ S :=
    fun P => hclosed.mem_of_tendsto (tendsto_gVec_lip hN W hD hpos hcube hB τ hpp P)
      (Eventually.of_forall fun k => by
        rw [hS]
        exact Submodule.le_topologicalClosure _
          (Submodule.subset_span ⟨lipR k P, lipMono_lipReg k P.2, rfl⟩))
  have hf : ∀ a : RMono N D τ r →₀ ℝ,
      ((GNSHilbert.Pre.ofPair (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm a 0
        : GNSHilbert.Pre (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm)
        : RH hN (energy0 W D hD) hB D τ hpp) ∈ S := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero =>
      have e : GNSHilbert.Pre.ofPair (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm 0 0 = 0 :=
        rfl
      rw [e, UniformSpace.Completion.coe_zero]
      exact S.zero_mem
    | add a b ha hb =>
      have e : GNSHilbert.Pre.ofPair (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm (a + b) 0
          = GNSHilbert.Pre.ofPair _ a 0 + GNSHilbert.Pre.ofPair _ b 0 :=
        GNSHilbert.Pre.ext rfl (by simp)
      rw [e, UniformSpace.Completion.coe_add]
      exact S.add_mem ha hb
    | single P c =>
      have e : GNSHilbert.Pre.ofPair (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm
            (Finsupp.single P c) 0
          = (c : ℂ) • GNSHilbert.Pre.ofPair _ (Finsupp.single P 1) 0 :=
        GNSHilbert.Pre.ext (by rw [GNSHilbert.Pre.smul_fst]; simp) (by rw [GNSHilbert.Pre.smul_snd]; simp)
      rw [e, UniformSpace.Completion.coe_smul]
      exact S.smul_mem _ (hg P)
  refine (Submodule.eq_top_iff').mpr fun y => ?_
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih z =>
    have e : z = GNSHilbert.Pre.ofPair _ (z : _ × _).1 0
        + Complex.I • GNSHilbert.Pre.ofPair _ (z : _ × _).2 0 :=
      GNSHilbert.Pre.ext (by simp) (by simp)
    rw [e, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul]
    exact S.add_mem (hf _) (S.smul_mem _ (hf _))

omit hpos hcube in
/-- **`J` is norm-preserving.** DERIVED: `2` the square. -/
theorem norm_J (Φ : Flow N) (hB : UniformBoundF hN Φ) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4)
    {r : ℝ} (hpp : Φ.PosPreserving τ r) (y : RH hN Φ hB D τ hpp) : ‖J hN Φ hB D τ hpp y‖ = ‖y‖ := by
  have h : ‖J hN Φ hB D τ hpp y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_J]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

omit hpos hcube in
/-- **`J` carries the span of the Lipschitz vectors of `RH` into that of `FlowH`.** DERIVED: no
numeral. -/
theorem J_mem_span {u : RH hN (energy0 W D hD) hB D τ hpp}
    (hu : u ∈ Submodule.span ℂ (rLipVecs hN W hD hB τ hpp)) :
    J hN (energy0 W D hD) hB D τ hpp u ∈ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp) := by
  have h : (Submodule.span ℂ (rLipVecs hN W hD hB τ hpp)).map
      (J hN (energy0 W D hD) hB D τ hpp).toLinearMap
      ≤ Submodule.span ℂ (lipVecs hN W D hD hB τ hpp) := by
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    exact ⟨P, hP, MassGap.DiniHolder.J_gVec hN (energy0 W D hD) hB D τ hpp P⟩
  exact h (Submodule.mem_map_of_mem hu)

/-- **The closure of the span of the Lipschitz vectors of `FlowH` is exactly `V = range J`.** This
closes the density caveat of `DiniHolder`. DERIVED: no numeral. -/
theorem closure_span_lipVecs :
    closure ((Submodule.span ℂ (lipVecs hN W D hD hB τ hpp) :
      Submodule ℂ (FlowH hN (energy0 W D hD) hB τ hpp)) : Set (FlowH hN (energy0 W D hD) hB τ hpp))
      = Set.range (J hN (energy0 W D hD) hB D τ hpp) := by
  have hiso : Isometry (J hN (energy0 W D hD) hB D τ hpp) :=
    AddMonoidHomClass.isometry_of_norm _ (norm_J hN _ hB D τ hpp)
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ hiso.isClosedEmbedding.isClosed_range
    have h : Submodule.span ℂ (lipVecs hN W D hD hB τ hpp)
        ≤ LinearMap.range (J hN (energy0 W D hD) hB D τ hpp).toLinearMap := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨P, _, rfl⟩
      exact ⟨gVec (rTransfer hN (energy0 W D hD) hB D τ hpp 0) P,
        MassGap.DiniHolder.J_gVec hN (energy0 W D hD) hB D τ hpp P⟩
    intro x hx
    obtain ⟨y, hy⟩ := h hx
    exact ⟨y, hy⟩
  · rintro _ ⟨y, rfl⟩
    exact map_mem_closure (J hN (energy0 W D hD) hB D τ hpp).continuous
      (dense_span_rLipVecs hN W hD hpos hcube hB τ hpp y)
      (fun z hz => J_mem_span hN W hD hB τ hpp hz)

end Density

/-! ## 4. The reduced reconstruction -/

section Reduce

open ContinuousLinearMap (adjoint)

/-- **A sub-reconstruction of an `OSDataS`**: an isometry into its Hilbert space with a vacuum, whose
range projection commutes with the unit step, and a non-zero vector orthogonal to the vacuum.
DERIVED: `1` the unit step; `0` the vanishing pairing and the zero vector. -/
structure SubSector (X : OSDataS) (R : Type) [NormedAddCommGroup R] [InnerProductSpace ℂ R]
    [CompleteSpace R] where
  /-- The isometry. -/
  J : R →L[ℂ] X.H
  inner_J : ∀ x y, inner ℂ (J x) (J y) = inner ℂ x y
  /-- The vacuum. -/
  vac : R
  J_vac : J vac = X.vac
  comm : Commute (J.comp (adjoint J)) (X.time 1)
  nontrivial : ∃ u : R, inner ℂ vac u = 0 ∧ u ≠ 0

variable {X : OSDataS} {R : Type} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  (Y : SubSector X R)

namespace SubSector

/-- DERIVED: `1` the identity. -/
theorem adj_J (y : R) : adjoint Y.J (Y.J y) = y :=
  ext_inner_right ℂ fun v => by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact Y.inner_J y v

/-- DERIVED: `2` the square. -/
theorem norm_J (y : R) : ‖Y.J y‖ = ‖y‖ := by
  have h : ‖Y.J y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), Y.inner_J]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- DERIVED: no numeral. -/
theorem J_inj {x y : R} (h : Y.J x = Y.J y) : x = y := by
  rw [← Y.adj_J x, ← Y.adj_J y, h]

/-- **The range is invariant under every time.** DERIVED: `0` the sign of `t`. -/
theorem J_adj_time {t : ℝ} (ht : 0 ≤ t) (y : R) :
    Y.J (adjoint Y.J (X.time t (Y.J y))) = X.time t (Y.J y) := by
  have c : Commute (Y.J.comp (adjoint Y.J)) (X.time t) := by
    rw [time_eq_powT X ht]
    exact (Commute.cfc_real Y.comm.symm (fun x : ℝ => x ^ t)).symm
  have h := congrArg (fun F => F (Y.J y)) c.eq
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, Y.adj_J] at h
  exact h

end SubSector

/-- **The compressed time.** DERIVED: no numeral. -/
def redTime (t : ℝ) : R →L[ℂ] R := (adjoint Y.J).comp ((X.time t).comp Y.J)

/-- **`J` intertwines the two times.** DERIVED: `0` the sign of `t`. -/
theorem J_redTime {t : ℝ} (ht : 0 ≤ t) (y : R) : Y.J (redTime Y t y) = X.time t (Y.J y) :=
  Y.J_adj_time ht y

/-- **The reduced reconstruction**: the Euclidean side and the gap of `X`, the vacuum of `R`, the
compressed time. DERIVED: `0` the time origin and the signs; `1` the identity and the norm bound. -/
def reduce : OSDataS where
  S := X.S
  α := X.α
  γ := X.γ
  growth := X.growth
  os3 := X.os3
  H := R
  vac := Y.vac
  time := redTime Y
  gap := X.gap
  gap_pos := X.gap_pos
  time_zero := ContinuousLinearMap.ext fun y => by
    show adjoint Y.J (X.time 0 (Y.J y)) = y
    rw [X.time_zero, ContinuousLinearMap.one_apply, Y.adj_J]
  time_add s t hs ht := ContinuousLinearMap.ext fun y => Y.J_inj (by
    rw [J_redTime Y (add_nonneg hs ht), X.time_add s t hs ht, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, J_redTime Y hs, J_redTime Y ht])
  time_selfAdjoint t ht := by
    refine ⟨(X.time_selfAdjoint t ht).1.adjoint_conj Y.J, ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul, ← Y.norm_J, J_redTime Y ht, ← Y.norm_J y]
    exact ((X.time t).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (X.time_selfAdjoint t ht).2)
  time_cont y := (adjoint Y.J).continuous.comp_continuousOn (X.time_cont (Y.J y))
  time_vac t ht := Y.J_inj (by rw [J_redTime Y ht, Y.J_vac, X.time_vac t ht])
  time_gap t ht u hu := by
    have hJ : inner ℂ X.vac (Y.J u) = 0 := by rw [← Y.J_vac, Y.inner_J]; exact hu
    rw [← Y.norm_J (redTime Y t u), J_redTime Y ht, ← Y.norm_J u]
    exact X.time_gap t ht _ hJ
  nontrivial := Y.nontrivial

/-- The reduced time acts through `J`. DERIVED: `0` the sign of `t`. -/
theorem J_reduce_time {t : ℝ} (ht : 0 ≤ t) (y : R) :
    Y.J ((reduce Y).time t y) = X.time t (Y.J y) := J_redTime Y ht y

/-- DERIVED: `0` the sign of `t`. -/
theorem norm_reduce_time {t : ℝ} (ht : 0 ≤ t) (y : R) :
    ‖(reduce Y).time t y‖ = ‖X.time t (Y.J y)‖ := by
  show ‖redTime Y t y‖ = _
  rw [← Y.norm_J, J_redTime Y ht]

/-- **The rate bottoms agree**: `u` has rate bottom `g` in the reduced reconstruction exactly when
`J u` has it in `X`, since `‖a^t u‖` is the same on both sides (`bound_iff_rateBottom`). DERIVED: `0`
the sign of `t`; `1` the unit step. -/
theorem reduce_rateBottom_iff (u : R) (g : ℝ) :
    rateMeasure ((reduce Y).time 1) u (Set.Iio g) = 0
      ↔ rateMeasure (X.time 1) (Y.J u) (Set.Iio g) = 0 := by
  rw [← bound_iff_rateBottom (time_isSelfAdjoint (reduce Y) zero_le_one)
      (spectrum_time (reduce Y) zero_le_one) u g,
    ← bound_iff_rateBottom (time_isSelfAdjoint X zero_le_one) (spectrum_time X zero_le_one) (Y.J u) g]
  refine forall₂_congr fun t ht => ?_
  rw [← time_eq_powT (reduce Y) ht, ← time_eq_powT X ht, Y.norm_J]
  show ‖(reduce Y).time t u‖ ≤ _ ↔ _
  rw [norm_reduce_time Y ht]
  exact Iff.rfl

/-- **`ShellGap.gap_iff_rateBottom` on the reduced reconstruction.** DERIVED: `0` the vanishing
pairing and the sign of `t`; `1` the unit step. -/
theorem reduce_gap_iff_rateBottom (g : ℝ) :
    (∀ t, 0 ≤ t → ∀ u : R, inner ℂ Y.vac u = 0 →
        ‖(reduce Y).time t u‖ ≤ Real.exp (-(g * t)) * ‖u‖)
      ↔ ∀ u : R, inner ℂ Y.vac u = 0 → rateMeasure ((reduce Y).time 1) u (Set.Iio g) = 0 :=
  MassGap.ShellGap.gap_iff_rateBottom (reduce Y) g

/-- **`ShellGap.gap_rateBottom` on the reduced reconstruction**, at the gap of `X`. DERIVED: `0` the
vanishing pairing; `1` the unit step. -/
theorem reduce_gap_rateBottom (u : R) (hu : inner ℂ Y.vac u = 0) :
    rateMeasure ((reduce Y).time 1) u (Set.Iio X.gap) = 0 :=
  MassGap.ShellGap.gap_rateBottom (reduce Y) u hu

end Reduce

/-! ## 5. The observer's regular sector -/

section Observer

variable {N : ℕ}

/-- **Regular non-triviality**: `FlowConnectedNonzero` with a regular witness. DERIVED: `0` the
excluded value; `2` the square; `4` in `Fin 4` the spacetime dimension. -/
def RegConnectedNonzero (hN : N ≠ 0) (Φ : Flow N) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4)
    (r : ℝ) : Prop :=
  ∃ Q : RMono N D τ r,
    kernF hN Φ τ Q.1.1 Q.1.1 - kernF hN Φ τ (emptyMargin N τ r).1 Q.1.1 ^ 2 ≠ 0

/-- **It implies the input it replaces.** DERIVED: no numeral. -/
theorem RegConnectedNonzero.flow {hN : N ≠ 0} {Φ : Flow N} {D : Set (LField (MassGap.SUN.SU N))}
    {τ : Fin 4} {r : ℝ} (h : RegConnectedNonzero hN Φ D τ r) : FlowConnectedNonzero hN Φ τ r := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q.1, hQ⟩

/-- **A regular vector orthogonal to the vacuum.** DERIVED: `0` the vanishing pairing, the zero vector
and the reference step; `1` the coefficient; `2` the square. -/
theorem exists_orth_rH (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r)
    (h : RegConnectedNonzero hN Φ D τ r) :
    ∃ u : RH hN Φ hB D τ hpp, inner ℂ (rVac hN Φ hB D τ hpp) u = 0 ∧ u ≠ 0 := by
  obtain ⟨Q, hQ⟩ := h
  refine ContinuumSep.exists_orth_ne_zero (rTransfer hN Φ hB D τ hpp 0) (Finsupp.single Q 1) ?_
  show gForm (rKern hN Φ τ) (Finsupp.single Q 1) (Finsupp.single Q 1)
      - gForm (rKern hN Φ τ) (Finsupp.single Q 1) (Finsupp.single (rEmpty N D τ r) 1) ^ 2 ≠ 0
  rw [gForm_single, gForm_single]
  simp only [one_mul]
  show kernF hN Φ τ Q.1.1 Q.1.1 - kernF hN Φ τ Q.1.1 (emptyMargin N τ r).1 ^ 2 ≠ 0
  rw [← kernF_symm hN Φ τ (emptyMargin N τ r).1 Q.1.1]
  exact hQ

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

include hpos hcube in
/-- **The regular witness can always be taken Lipschitz.** The connected kernel is continuous along
`lipR`, so it is non-zero at a large step. A lattice lower bound for `RegConnectedNonzero` need only
be read at a Lipschitz monomial. DERIVED: `0` the excluded value; `2` the square. -/
theorem exists_lip_connected {τ : Fin 4} {r : ℝ}
    (h : RegConnectedNonzero hN (energy0 W D hD) D τ r) :
    ∃ Q : RMono N D τ r, LipReg D Q.1.1 ∧
      kernF hN (energy0 W D hD) τ Q.1.1 Q.1.1
        - kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 Q.1.1 ^ 2 ≠ 0 := by
  obtain ⟨Q, hQ⟩ := h
  have h1 : Tendsto (fun k => kernF hN (energy0 W D hD) τ (lipR k Q).1.1 (lipR k Q).1.1) atTop
      (𝓝 (kernF hN (energy0 W D hD) τ Q.1.1 Q.1.1)) :=
    tendsto_kernF_mod hN W hD hpos hcube τ Q.2 Q.2 _ _
      (fun k i y => lipFn_dom k _ _ y) (fun k i y => lipFn_dom k _ _ y)
      (fun k i y => lipFn_close k _ _ y) (fun k i y => lipFn_close k _ _ y)
  have h2 : Tendsto (fun k => kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 (lipR k Q).1.1) atTop
      (𝓝 (kernF hN (energy0 W D hD) τ (emptyMargin N τ r).1 Q.1.1)) :=
    tendsto_kernF_mod hN W hD hpos hcube τ (rEmpty N D τ r).2 Q.2
      (fun _ i => ((rEmpty N D τ r).1.1.2 i).2) (fun k i => lipFn k (Q.1.1.2 i).2 (Q.2 i).2)
      (fun _ _ _ => le_rfl) (fun k i y => lipFn_dom k _ _ y)
      (fun k i y => self_close _ k y) (fun k i y => lipFn_close k _ _ y)
  obtain ⟨k, hk⟩ := ((h1.sub (h2.pow 2)).eventually_ne hQ).exists
  exact ⟨lipR k Q, lipMono_lipReg k Q.2, hk⟩

variable (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

/-- `realT` on `V` is `rU`. DERIVED: `0` the vanishing remainder. -/
theorem realT_J (x : spatial τ) (y : RH hN (energy0 W D hD) hB D τ hpp) :
    realT hN W hD hpos hcube hB τ hpp x (J hN (energy0 W D hD) hB D τ hpp y)
      = J hN (energy0 W D hD) hB D τ hpp (rU hN W hD hpos hcube hB τ hpp x y) := by
  rw [realT_apply, JdJ, sub_self, add_zero]

omit hpos hcube in
/-- **The range projection commutes with the steps.** DERIVED: `0` the reference step. -/
theorem commute_proj_stepT :
    Commute ((J hN (energy0 W D hD) hB D τ hpp).comp (Jd hN (energy0 W D hD) hB D τ hpp))
      (stepT hN (energy0 W D hD) hB τ hpp 0) := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
  rw [Jd_step, ← J_step]

omit hpos hcube in
/-- **So does it with every time.** DERIVED: `0` the reference step. -/
theorem commute_proj_timeT (t : ℝ) :
    Commute ((J hN (energy0 W D hD) hB D τ hpp).comp (Jd hN (energy0 W D hD) hB D τ hpp))
      (timeT hN (energy0 W D hD) hB τ hpp t) :=
  (Commute.cfc_real (commute_proj_stepT hN W hD hB τ hpp).symm
    (fun s : ℝ => s ^ (t / dySpacing N 0))).symm

/-- **The time of the regular sector.** DERIVED: no numeral. -/
def rTimeT (t : ℝ) : RH hN (energy0 W D hD) hB D τ hpp →L[ℂ] RH hN (energy0 W D hD) hB D τ hpp :=
  (Jd hN (energy0 W D hD) hB D τ hpp).comp
    ((timeT hN (energy0 W D hD) hB τ hpp t).comp (J hN (energy0 W D hD) hB D τ hpp))

omit hpos hcube in
/-- DERIVED: no numeral. -/
theorem J_rTimeT (t : ℝ) (y : RH hN (energy0 W D hD) hB D τ hpp) :
    J hN (energy0 W D hD) hB D τ hpp (rTimeT hN W hD hB τ hpp t y)
      = timeT hN (energy0 W D hD) hB τ hpp t (J hN (energy0 W D hD) hB D τ hpp y) := by
  have h := congrArg (fun F => F (J hN (energy0 W D hD) hB D τ hpp y))
    (commute_proj_timeT hN W hD hB τ hpp t).eq
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, JdJ] at h
  exact h

/-- **`rU` commutes with the time of the regular sector.** DERIVED: no numeral. -/
theorem commute_rU_rTimeT (x : spatial τ) (t : ℝ) :
    Commute (rU hN W hD hpos hcube hB τ hpp x) (rTimeT hN W hD hB τ hpp t) := by
  refine ContinuousLinearMap.ext fun y => ?_
  have hinj : ∀ {a b : RH hN (energy0 W D hD) hB D τ hpp},
      J hN (energy0 W D hD) hB D τ hpp a = J hN (energy0 W D hD) hB D τ hpp b → a = b :=
    fun {a b} h => by
      rw [← JdJ hN (energy0 W D hD) hB D τ hpp a, ← JdJ hN (energy0 W D hD) hB D τ hpp b, h]
  refine hinj ?_
  have hc := congrArg (fun F => F (J hN (energy0 W D hD) hB D τ hpp y))
    (commute_realT_timeT hN W hD hpos hcube hB τ hpp x t).eq
  simp only [ContinuousLinearMap.mul_apply] at hc ⊢
  rw [← realT_J hN W hD hpos hcube hB τ hpp, J_rTimeT, J_rTimeT,
    ← realT_J hN W hD hpos hcube hB τ hpp]
  exact hc

/-- **The representation of `spatial τ` on `RH`**: no identity branch. DERIVED: no numeral. -/
def regRep : UnitaryRep (spatial τ) (RH hN (energy0 W D hD) hB D τ hpp) where
  U := rU hN W hD hpos hcube hB τ hpp
  map_zero := rU_zero hN W hD hpos hcube hB τ hpp
  map_add := rU_add hN W hD hpos hcube hB τ hpp
  inner_U := inner_rU hN W hD hpos hcube hB τ hpp
  cont := continuous_rU hN W hD hpos hcube hB τ hpp

/-- **The joint data on `RH`.** DERIVED: `0` the sign of the unit time; `1` the unit time. -/
def regData : JointData (RH hN (energy0 W D hD) hB D τ hpp) (spatial τ) where
  a := rTimeT hN W hD hB τ hpp 1
  sa := (timeT_nonneg_norm hN (energy0 W D hD) hB τ hpp 1 zero_le_one).2.1.adjoint_conj
    (J hN (energy0 W D hD) hB D τ hpp)
  hsp := spectrum_Icc_of_nonneg
    (ContinuousLinearMap.nonneg_iff_isPositive _ |>.mpr
      (((ContinuousLinearMap.nonneg_iff_isPositive _).mp
        (timeT_nonneg_norm hN (energy0 W D hD) hB τ hpp 1 zero_le_one).1).adjoint_conj
        (J hN (energy0 W D hD) hB D τ hpp)))
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      rw [one_mul, ← norm_J hN _ hB D τ hpp, J_rTimeT, ← norm_J hN _ hB D τ hpp y]
      exact ((timeT hN (energy0 W D hD) hB τ hpp 1).le_opNorm _).trans
        (mul_le_of_le_one_left (norm_nonneg _)
          (timeT_nonneg_norm hN (energy0 W D hD) hB τ hpp 1 zero_le_one).2.2))
  R := regRep hN W hD hpos hcube hB τ hpp
  comm x := commute_rU_rTimeT hN W hD hpos hcube hB τ hpp x 1

/-- **The Hölder bound on `RH`**, on the dense span of the Lipschitz vectors. DERIVED: `0` the sign of
`s`; `1/2` as in `HolderHalf`. -/
theorem holderHalf_reg {u : RH hN (energy0 W D hD) hB D τ hpp}
    (hu : u ∈ Submodule.span ℂ (rLipVecs hN W hD hB τ hpp)) :
    HolderHalf (regData hN W hD hpos hcube hB τ hpp) u := by
  obtain ⟨L, h⟩ := holderHalf_span hN W hD hpos hcube hB τ hpp (J_mem_span hN W hD hB τ hpp hu)
  refine ⟨L, fun j s hs => ?_⟩
  have e := h j s hs
  show ‖rU hN W hD hpos hcube hB τ hpp _ u - u‖ ≤ _
  rw [← norm_J hN _ hB D τ hpp, map_sub, ← realT_J hN W hD hpos hcube hB τ hpp]
  exact e

/-- DERIVED: no numeral. -/
theorem dyadicDini_reg {u : RH hN (energy0 W D hD) hB D τ hpp}
    (hu : u ∈ Submodule.span ℂ (rLipVecs hN W hD hB τ hpp)) :
    DyadicDini (regData hN W hD hpos hcube hB τ hpp) u :=
  (holderHalf_reg hN W hD hpos hcube hB τ hpp hu).dyadicDini

end Observer

section ObserverData

variable {N : ℕ}

/-- **The regular sector of `observerOSDataS` as a sub-reconstruction.** DERIVED: `0` the excluded
colour count and the reference step; `1` the top of `ρ` and the unit step. -/
def observerSubSector (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, ObserverEnergyBox.CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (ObserverOS.energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (ObserverOS.energy0 W D hD)
      (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (ObserverOS.energy0 W D hD) D τ r) :
    SubSector (observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR.flow)
      (RH hN (ObserverOS.energy0 W D hD) (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) D τ
        (Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ)) :=
  let hB := ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ
  { J := J hN (ObserverOS.energy0 W D hD) hB D τ hpp
    inner_J := inner_J hN (ObserverOS.energy0 W D hD) hB D τ hpp
    vac := rVac hN (ObserverOS.energy0 W D hD) hB D τ hpp
    J_vac := J_vac hN (ObserverOS.energy0 W D hD) hB D τ hpp
    comm := commute_proj_timeT hN W hD hB τ hpp 1
    nontrivial := exists_orth_rH hN (ObserverOS.energy0 W D hD) hB D τ hpp hR }

/-- **The observer's reconstruction on the regular sector**: an `OSDataS` on `RH`, with the
Schwinger functions and the gap of `observerOSDataS`. The inputs are those of `observerOSDataS` with
`FlowConnectedNonzero` read at a regular witness. DERIVED: `0`, `1` as in `observerSubSector`. -/
def observerReduced (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, ObserverEnergyBox.CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (ObserverOS.energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (ObserverOS.energy0 W D hD)
      (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (ObserverOS.energy0 W D hD) D τ r) : OSDataS :=
  reduce (observerSubSector hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR)

/-- **The real translations of the reduced reconstruction**: `rU`, on `RH`. DERIVED: `-1` the sign of
the inverse translation; `0`, `1` as in `observerSubSector`. -/
def regSpatial (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, ObserverEnergyBox.CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (ObserverOS.energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (ObserverOS.energy0 W D hD)
      (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (ObserverOS.energy0 W D hD) D τ r) :
    SpatialData (observerReduced hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR) :=
  let hB := ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ
  { ι := spatial τ
    U := fun x => rU hN W hD hpos hcube hB τ hpp x
    Uinv := fun x => rU hN W hD hpos hcube hB τ hpp (-x)
    inner_U := fun x z w => inner_rU hN W hD hpos hcube hB τ hpp x z w
    U_Uinv := fun x => by
      have h1 := rU_add hN W hD hpos hcube hB τ hpp x (-x)
      rw [add_neg_cancel, rU_zero] at h1
      exact h1.symm
    Uinv_U := fun x => by
      have h1 := rU_add hN W hD hpos hcube hB τ hpp (-x) x
      rw [neg_add_cancel, rU_zero] at h1
      exact h1.symm
    commute := fun x => commute_rU_rTimeT hN W hD hpos hcube hB τ hpp x 1
    U_vac := fun x => rU_vac hN W hD hpos hcube hB τ hpp x }

/-- **Its zero-momentum space is the part of `V` that `realT` fixes.** The zero-momentum space of
`observerRealSpatial` also contains all of `V⊥`; this one does not meet it. DERIVED: `0`, `1` as in
`observerSubSector`. -/
theorem mem_zeroMom_regSpatial_iff (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, ObserverEnergyBox.CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (ObserverOS.energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (ObserverOS.energy0 W D hD)
      (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hR : RegConnectedNonzero hN (ObserverOS.energy0 W D hD) D τ r)
    (u : RH hN (ObserverOS.energy0 W D hD) (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) D τ
      (Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ)) :
    u ∈ zeroMom (regSpatial hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hR)
      ↔ ∀ x : spatial τ, realT hN W hD hpos hcube
          (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) τ
          (Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ) x
          (J hN (ObserverOS.energy0 W D hD) (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) D τ
            (Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ) u)
        = J hN (ObserverOS.energy0 W D hD) (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) D τ
            (Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ) u := by
  refine forall_congr' fun x => ?_
  rw [realT_J hN W hD hpos hcube]
  constructor
  · intro e
    exact congrArg _ e
  · intro e
    have e' := congrArg (Jd hN (ObserverOS.energy0 W D hD)
      (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) D τ
      (Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ)) e
    rwa [JdJ, JdJ] at e'

end ObserverData

end

end MassGap.RegularDense

#print axioms MassGap.RegularDense.exists_lipschitz_approx
#print axioms MassGap.RegularDense.exists_lipFn
#print axioms MassGap.RegularDense.err_pos
#print axioms MassGap.RegularDense.tendsto_err
#print axioms MassGap.RegularDense.lipFn_lip
#print axioms MassGap.RegularDense.lipFn_dom
#print axioms MassGap.RegularDense.lipFn_close
#print axioms MassGap.RegularDense.lipMono_lipReg
#print axioms MassGap.RegularDense.tendsto_contSF_of_sup
#print axioms MassGap.RegularDense.tendsto_kernF_mod
#print axioms MassGap.RegularDense.self_close
#print axioms MassGap.RegularDense.tendsto_gVec_lip
#print axioms MassGap.RegularDense.dense_span_rLipVecs
#print axioms MassGap.RegularDense.norm_J
#print axioms MassGap.RegularDense.J_mem_span
#print axioms MassGap.RegularDense.closure_span_lipVecs
#print axioms MassGap.RegularDense.SubSector.adj_J
#print axioms MassGap.RegularDense.SubSector.norm_J
#print axioms MassGap.RegularDense.SubSector.J_inj
#print axioms MassGap.RegularDense.SubSector.J_adj_time
#print axioms MassGap.RegularDense.J_redTime
#print axioms MassGap.RegularDense.reduce
#print axioms MassGap.RegularDense.J_reduce_time
#print axioms MassGap.RegularDense.norm_reduce_time
#print axioms MassGap.RegularDense.reduce_rateBottom_iff
#print axioms MassGap.RegularDense.reduce_gap_iff_rateBottom
#print axioms MassGap.RegularDense.reduce_gap_rateBottom
#print axioms MassGap.RegularDense.RegConnectedNonzero.flow
#print axioms MassGap.RegularDense.exists_orth_rH
#print axioms MassGap.RegularDense.exists_lip_connected
#print axioms MassGap.RegularDense.realT_J
#print axioms MassGap.RegularDense.commute_proj_stepT
#print axioms MassGap.RegularDense.commute_proj_timeT
#print axioms MassGap.RegularDense.J_rTimeT
#print axioms MassGap.RegularDense.commute_rU_rTimeT
#print axioms MassGap.RegularDense.regRep
#print axioms MassGap.RegularDense.regData
#print axioms MassGap.RegularDense.holderHalf_reg
#print axioms MassGap.RegularDense.dyadicDini_reg
#print axioms MassGap.RegularDense.observerSubSector
#print axioms MassGap.RegularDense.observerReduced
#print axioms MassGap.RegularDense.regSpatial
#print axioms MassGap.RegularDense.mem_zeroMom_regSpatial_iff
