import Mathlib
import MassGap.ShellMomentum

/-!
# MassGap.ShellTranslate — real spatial translations of the observer's reconstruction

`ShellMomentum` builds the dyadic spatial translations `spT` on the reconstruction space `FlowH`.
This module extends them to every real spatial vector: a strongly continuous unitary representation
of `ℝ³` (the vectors with zero time component), commuting with the time translations and fixing the
vacuum, on the sector of `FlowH` where the tree proves real translation invariance. Declarations are
in the namespace `MassGap.ShellTranslate`.

## What the tree has

* `ContinuumFlow.contSF_translate`: for every flow, the continuum Schwinger functions are invariant
  under the dyadic translations `site (dySpacing N m) n` of all test functions; real translations are
  not proved for a general flow.
* `ObserverOS.contSF_energy0_translate_real` (OS1 on `ℝ⁴` for the observer's energy density, from
  the cube moments (E)): invariance under every real `v ∈ ℝ⁴` for families whose fields lie in the
  reflection-closed class `D` and whose test functions are uniformly continuous. Its proof runs
  through `abs_contSF_energy0_sub_le`, the sup-norm Lipschitz bound of the Schwinger functions in
  their test functions (same class, one cube). `observer_os` packages it as clause 3.
* `ObserverOSEuclidS.schwSFM_translate`, `schwCML_translate`: the same OS1 carried to decaying and
  Schwartz test functions; they act on the Schwartz-function Schwinger functions `X.S`, not on the
  reconstruction space.
* The reconstruction space `FlowH` of `observerOSDataS` is the GNS space of the reflection form on
  all margin monomials: any local gauge-invariant field and any bounded test function of bounded
  support. For a field outside `D` or a test function that is not uniformly continuous the tree has
  neither real translation invariance nor continuity in the translation. Plainly, a real translation
  group on all of `FlowH` that agrees with `spT` on dyadic vectors does not follow from the tree.
* Mathlib (at this pin) has no Stone theorem for unitary groups of `ℝⁿ`, no SNAG theorem and no
  Bochner theorem on positive-definite functions; it has characteristic functions of measures and
  their uniqueness (`Measure.ext_of_charFun`).

## 3. Continuity of the Schwinger functions in the translation vector (proved)

`tendsto_contSF_translate`: for a family of fields of `D` with uniformly continuous test functions,
`d ↦ S(fᵢ(· − dᵢ))` is continuous at `d = 0` in `(ℝ⁴)ⁿ`, one translation per factor
(`abs_contSF_energy0_sub_le` with the uniform continuity of each `fᵢ`); `continuous_contSF_translate`
gives continuity at every `d`. `tendsto_kernF_shift`: the reflection kernel `S(θP ∪ shift_v Q)` is
continuous in `v` at `0` for regular monomials. `kernF_shift_real`: `S(θ shift_v P ∪ shift_v Q) =
S(θP ∪ Q)` for every real `v` with `v τ = 0` (`contSF_energy0_translate_real`, the time reflection
fixing `v`).

## 5. The regular sector (proved)

`Reg D P`: every field of `P` is in `D` and every test function is uniformly continuous; it is kept by
every translation, real or dyadic, and by the time step. `RMono N D τ r`: the regular margin
monomials. `rTransfer`: the tree's `gTransfer` on them, the same kernel `kernF` (positivity from
`contSF_gram_nonneg`, the iterate bound from `kernF_iterate_bound`); `rTransfer_positive`,
`rReconstructed`. `RH` is its Hilbert space, `rStep m` its transfers, `rVac` its vacuum.

`J : RH → FlowH` is the isometry induced by the inclusion of regular monomials (`inner_J`); it maps
`rVac` to the vacuum (`J_vac`) and intertwines the steps (`J_step`, `Jd_step` for its adjoint `Jd`).
Its range `V` is the image of the isometry `J` (closed, as the image of an isometry on a complete space;
not stated as a lemma here); `inner_J_add` and `Jd_sub` give the orthogonal decomposition
`FlowH = V ⊕ ker Jd`.

## 6. Real translations (proved)

`spatial τ`: the vectors of `ℝ⁴` with zero `τ` component (the kernel of the `τ` coordinate; its
dimension, three, is not used or proved here).

* On `RH`: `rU x` is `ShellMomentum.opS` of the translation of every test function by `x`. It
  preserves the inner product (`inner_rU`), `rU 0 = 1`, `rU (x + y) = rU x · rU y` (`rU_add`), fixes
  the vacuum (`rU_vac`), commutes with every step (`commute_rU_rStep`) and is strongly continuous
  (`continuous_rU`): for a vector of the pre-Hilbert space, `‖rU x z − z‖² = 2(⟨a, a⟩ − ⟨a, S_x a⟩) +
  2(⟨b, b⟩ − ⟨b, S_x b⟩)` (`norm_opS_sub`) tends to `0` by the kernel continuity, and the bound
  `‖rU x‖ = 1` carries this to the completion (`tendsto_opS_of_coe`).
* On `FlowH`: `realT x = J rU x Jd + (1 − J Jd)`. It preserves the inner product (`inner_realT`),
  `realT 0 = 1`, `realT (x + y) = realT x · realT y`, fixes the vacuum (`realT_vac`), commutes with every
  `stepT m` (`commute_realT_stepT`) and every `timeT t` (`commute_realT_timeT`), and is strongly
  continuous (`continuous_realT`). `realT_dyadic`: on `V` it agrees with `ShellMomentum.spT` at every
  dyadic spatial vector. `realT_orth`: on `V⊥` it is the identity; plainly, it does not agree with
  `spT` there, and nothing in the tree says how `spT` acts on `V⊥`.
* `rU_vac`, `realT_vac`, `norm_rVac`: the regular sector contains the unit vacuum, which both
  translation groups fix.
* `observerRealSpatial`: the `ShellMomentum.SpatialData` of `observerOSDataS` indexed by `spatial τ`.
  The fixed space of `realT` is the fixed space of `rU` inside `V` together with all of `V⊥`, because
  `realT` is the identity on `V⊥` and is not the physical translation there. The zero-momentum
  projection `ShellMomentum.P0` of this data therefore contains every component in `V⊥`, whether or not
  the physical translation fixes it. `clay_zero_momentum_sector` for this data speaks about that sector.
* `realRep`: the package `UnitaryRep (spatial τ) FlowH`.

## 7. Positive definiteness (proved); the joint spectral measure (not formalized)

`UnitaryRep.posDef`: for any unitary representation and vector `u`,
`Σᵢⱼ c̄ᵢ cⱼ ⟪u, U(xⱼ − xᵢ) u⟫ = ‖Σⱼ cⱼ U(xⱼ) u‖²`, so `x ↦ ⟪u, U(x) u⟫` is positive definite
(`UnitaryRep.posDef_re_nonneg`) and continuous (the field `cont`). The joint spectral measure of `(timeT, realT)` for one
vector, a finite measure on `[0, ∞) × (ℝ³)'`, would follow from Bochner's theorem on `ℝ³` applied to
`x ↦ ⟪u, timeT t realT x u⟫` for each `t` together with the Laplace representation in `t`
(`ShellMeasure.flow_time_laplace`). Plainly, Bochner's theorem is not in Mathlib at this pin, so the
joint measure is not built here.

## 8. Load tests (proved)

* `planeWave p`: the representation `x ↦ e^{i p·x}` on `ℂ`, read as the translations of a free
  one-particle state of momentum `p` (the reading is argued, not derived); it is a
  `UnitaryRep (spatial τ) ℂ`. `planeWave_nontrivial`: it is not the trivial representation when `p` has
  a non-zero spatial component. The `UnitaryRep` structure admits a non-trivial instance. Whether
  `realRep` acts non-trivially on `FlowH` is not shown here.

Foundational footprint only (`#print axioms` at the end).
-/

namespace MassGap.ShellTranslate

open Filter Topology
open MassGap MassGap.InfiniteLattice MassGap.ContinuumField MassGap.ContinuumSchwinger
  MassGap.ContinuumReconstruction MassGap.ContinuumFlow MassGap.ContinuumTimeGroup
  MassGap.OSPositivity MassGap.ObserverOS MassGap.ObserverEnergyBox
open MassGap.ShellMomentum (cS cS_fst cS_snd opS opS_coe inner_opS opS_mul opS_eq_one opS_Omega
  opS_commute_opT reflR_of_zero site_time_zero gForm_mapDomain_inv spShift spT SpatialData)
open MassGap.ObserverOSReconstructionS (OSDataS observerOSDataS)

noncomputable section

/-! ## 1. Test functions -/

section TestFns

/-- **The axis reflection does not increase distances.** DERIVED: `4` in `Fin 4` the spacetime
dimension. -/
theorem dist_reflR_le (τ : Fin 4) (a b : Fin 4 → ℝ) : dist (reflR τ a) (reflR τ b) ≤ dist a b := by
  refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
  have h : reflR τ a i - reflR τ b i = reflR τ (a - b) i := by rw [reflR_sub]; rfl
  rw [Real.dist_eq, h, abs_reflR, Pi.sub_apply, ← Real.dist_eq]
  exact dist_le_pi_dist a b i

/-- DERIVED: `4` in `Fin 4` the spacetime dimension. -/
theorem uniformContinuous_reflR (τ : Fin 4) : UniformContinuous (reflR τ) :=
  Metric.uniformContinuous_iff.mpr fun ε hε => ⟨ε, hε, fun {a b} h => (dist_reflR_le τ a b).trans_lt h⟩

/-- **A translate of a uniformly continuous test function is uniformly continuous.** DERIVED: `4` in
`Fin 4` the spacetime dimension. -/
theorem uniformContinuous_translate {f : TestFn} (hf : UniformContinuous f.1) (v : Fin 4 → ℝ) :
    UniformContinuous (f.translate v).1 :=
  hf.comp (uniformContinuous_id.sub uniformContinuous_const)

/-- **So is a reflection.** DERIVED: `4` in `Fin 4` the spacetime dimension. -/
theorem uniformContinuous_reflect {f : TestFn} (hf : UniformContinuous f.1) (τ : Fin 4) :
    UniformContinuous (f.reflect τ).1 :=
  hf.comp (uniformContinuous_reflR τ)

end TestFns

/-! ## 2. Regular monomials -/

section Regular

variable {N : ℕ}

/-- **A regular monomial**: every field in `D`, every test function uniformly continuous. These are
the families on which the tree proves real translation invariance. DERIVED: no numeral. -/
def Reg (D : Set (LField (MassGap.SUN.SU N))) (P : Mono N) : Prop :=
  ∀ i, (P.2 i).1 ∈ D ∧ UniformContinuous (P.2 i).2.1

/-- **Translations keep regularity.** DERIVED: no numeral. -/
theorem reg_shift {D : Set (LField (MassGap.SUN.SU N))} {P : Mono N} (hP : Reg D P)
    (v : Fin 4 → ℝ) : Reg D (Mono.shift v P) :=
  fun i => ⟨(hP i).1, uniformContinuous_translate (hP i).2 v⟩

/-- **The reflected pair of regular monomials is regular.** DERIVED: `4` in `Fin 4` the spacetime
dimension. -/
theorem reg_pairFam {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D) (τ : Fin 4)
    {P Q : Mono N} (hP : Reg D P) (hQ : Reg D Q) (x : Fin P.1 ⊕ Fin Q.1) :
    (pairFam τ P Q x).1 ∈ D ∧ UniformContinuous (pairFam τ P Q x).2.1 := by
  cases x with
  | inl i => exact ⟨(hD τ _).mpr (hP i).1, uniformContinuous_reflect (hP i).2 τ⟩
  | inr j => exact hQ j

/-- **Translating the second monomial** translates the second block of the pair, the first by `0`.
DERIVED: `0` the zero translation; `4` in `Fin 4` the spacetime dimension. -/
theorem pairFam_shift_right (τ : Fin 4) (P Q : Mono N) (v : Fin 4 → ℝ) :
    pairFam τ P (Mono.shift v Q) = fun x => ((pairFam τ P Q x).1,
      (pairFam τ P Q x).2.translate (Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => v) x)) := by
  funext x
  cases x with
  | inl i =>
    show SField.refl τ (P.2 i)
      = ((SField.refl τ (P.2 i)).1, (SField.refl τ (P.2 i)).2.translate 0)
    rw [TestFn.translate_zero]
  | inr j => rfl

/-- **Translating both monomials by a spatial vector** translates every factor of the pair.
DERIVED: `0` the time component; `4` in `Fin 4` the spacetime dimension. -/
theorem pairFam_shift_both (τ : Fin 4) {v : Fin 4 → ℝ} (hv : v τ = 0) (P Q : Mono N) :
    pairFam τ (Mono.shift v P) (Mono.shift v Q)
      = fun x => ((pairFam τ P Q x).1, (pairFam τ P Q x).2.translate v) := by
  funext x
  cases x with
  | inl i =>
    show ((P.2 i).1.refl τ, ((P.2 i).2.translate v).reflect τ)
      = ((P.2 i).1.refl τ, ((P.2 i).2.reflect τ).translate v)
    rw [TestFn.reflect_translate, reflR_of_zero hv]
  | inr j => rfl

end Regular

/-! ## 3. Continuity in the translation vector and real invariance of the kernel -/

section Continuity

variable {N : ℕ} (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)

include hpos hcube

/-- **Continuity at zero translation.** For fields of `D` with uniformly continuous test functions,
translating the factor `i` by `dᵢ` changes the limit Schwinger function continuously at `d = 0`:
for `ε > 0`, every `dᵢ` with `‖dᵢ‖` below the modulus of continuity of `fᵢ` and below `1` keeps every
translate in one cube within `ε/(A + 1)` of `fᵢ` in sup norm, and `abs_contSF_energy0_sub_le` bounds
the change by `ε A/(A + 1) < ε`. DERIVED: `0` the zero translation, the excluded colour count and the
signs; `1` bounds `‖dᵢ‖`, keeping the translates in one cube, and makes `A + 1` positive; `2` makes the
moment even; `4` in `Fin 4` the spacetime dimension. -/
theorem tendsto_contSF_translate {ι : Type} [Fintype ι] (F : ι → SField N)
    (hG : ∀ i, (F i).1 ∈ D) (hU : ∀ i, UniformContinuous (F i).2.1) :
    Tendsto (fun d : ι → Fin 4 → ℝ =>
        contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate (d i))))
      (𝓝 0) (𝓝 (contSF hN (energy0 W D hD) F)) := by
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
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = (1 + Fintype.card ι * ∑ i, |C i|) * ∑ a, ∏ i ∈ Finset.univ \ {a}, M i := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun a _ => Finset.prod_nonneg (fun i _ => (hRM i).M_nonneg)))
  have hF : ∀ i, IsTest (F i).2.1 R (M i) := fun i =>
    ⟨hR0, (hRM i).2.1, fun y hy j => ((hRM i).2.2 y hy j).trans (by linarith [hRi i])⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hA1 : 0 < A + 1 := by linarith
  have hδ : 0 < ε / (A + 1) := div_pos hε hA1
  have hη : ∀ i, ∃ η : ℝ, 0 < η ∧
      ∀ a b : Fin 4 → ℝ, dist a b < η → dist ((F i).2.1 a) ((F i).2.1 b) < ε / (A + 1) := by
    intro i
    obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp (hU i) _ hδ
    exact ⟨η, hη, fun a b hab => h hab⟩
  choose η hη0 hηf using hη
  have hev : ∀ᶠ d : ι → Fin 4 → ℝ in 𝓝 0, ∀ i, ‖d i‖ < η i ∧ ‖d i‖ < 1 := by
    rw [Filter.eventually_all]
    intro i
    have ht : Tendsto (fun d : ι → Fin 4 → ℝ => ‖d i‖) (𝓝 0) (𝓝 0) := by
      have h := ((continuous_apply i).tendsto (0 : ι → Fin 4 → ℝ)).norm
      simpa using h
    exact (ht.eventually (gt_mem_nhds (hη0 i))).and (ht.eventually (gt_mem_nhds one_pos))
  filter_upwards [hev] with d hd
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
    linarith [hRi i, (hd i).2]
  have hclose : ∀ i y, |((F i).2.translate (d i)).1 y - (F i).2.1 y| ≤ ε / (A + 1) := by
    intro i y
    have h := hηf i (y - d i) y (by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact (hd i).1)
    rw [Real.dist_eq] at h
    exact h.le
  have hdiff := abs_contSF_energy0_sub_le hN W hD hpos hB F
    (fun i => ((F i).1, (F i).2.translate (d i))) (fun i => rfl) hG hR0 hc M hF hF' hclose
  have hsum : (1 + Fintype.card ι * ∑ i, |C i|)
      * ∑ a, ε / (A + 1) * ∏ i ∈ Finset.univ \ {a}, M i = ε / (A + 1) * A := by
    rw [hAdef, ← Finset.mul_sum]
    ring
  rw [hsum] at hdiff
  rw [Real.dist_eq]
  calc |contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate (d i)))
        - contSF hN (energy0 W D hD) F| ≤ ε / (A + 1) * A := hdiff
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hA1]
      nlinarith

/-- **Continuity in the translation vector** at every point: at `d₀` the family translated by `d₀`
is again regular, and `(f(· − d₀))(· − (d − d₀)) = f(· − d)`. DERIVED: no numeral. -/
theorem continuous_contSF_translate {ι : Type} [Fintype ι] (F : ι → SField N)
    (hG : ∀ i, (F i).1 ∈ D) (hU : ∀ i, UniformContinuous (F i).2.1) :
    Continuous (fun d : ι → Fin 4 → ℝ =>
        contSF hN (energy0 W D hD) (fun i => ((F i).1, (F i).2.translate (d i)))) := by
  rw [continuous_iff_continuousAt]
  intro d0
  have h := tendsto_contSF_translate hN W hD hpos hcube
    (fun i => ((F i).1, (F i).2.translate (d0 i))) hG
    (fun i => uniformContinuous_translate (hU i) (d0 i))
  have h1 : Tendsto (fun d : ι → Fin 4 → ℝ => d - d0) (𝓝 d0) (𝓝 0) :=
    (continuous_id.sub continuous_const).tendsto' d0 0 (sub_self d0)
  unfold ContinuousAt
  refine (h.comp h1).congr fun d => ?_
  refine congrArg (fun G : ι → SField N => contSF hN (energy0 W D hD) G) (funext fun i => ?_)
  show ((F i).1, ((F i).2.translate (d0 i)).translate ((d - d0) i))
    = ((F i).1, (F i).2.translate (d i))
  rw [TestFn.translate_translate]
  simp

/-- **The reflection kernel is continuous in the translation of its second monomial**, at `0`, for
regular monomials. DERIVED: `0` the zero translation; `4` in `Fin 4` the spacetime dimension. -/
theorem tendsto_kernF_shift (τ : Fin 4) {P Q : Mono N} (hP : Reg D P) (hQ : Reg D Q) :
    Tendsto (fun v : Fin 4 → ℝ => kernF hN (energy0 W D hD) τ P (Mono.shift v Q)) (𝓝 0)
      (𝓝 (kernF hN (energy0 W D hD) τ P Q)) := by
  have ht := tendsto_contSF_translate hN W hD hpos hcube (pairFam τ P Q)
    (fun x => (reg_pairFam hD τ hP hQ x).1) (fun x => (reg_pairFam hD τ hP hQ x).2)
  have hc : Continuous (fun v : Fin 4 → ℝ => fun x : Fin P.1 ⊕ Fin Q.1 =>
      Sum.elim (fun _ => (0 : Fin 4 → ℝ)) (fun _ => v) x) :=
    continuous_pi fun x => by
      cases x with
      | inl i => exact continuous_const
      | inr j => exact continuous_id
  have h0 : (fun x : Fin P.1 ⊕ Fin Q.1 => Sum.elim (fun _ => (0 : Fin 4 → ℝ))
      (fun _ => (0 : Fin 4 → ℝ)) x) = 0 := funext fun x => by cases x <;> rfl
  refine (ht.comp (hc.tendsto' 0 0 h0)).congr fun v => ?_
  exact congrArg (fun G => contSF hN (energy0 W D hD) G) (pairFam_shift_right τ P Q v).symm

/-- **OS1 for the reflection kernel at every real spatial vector**, regular monomials:
`S(θ shift_v P ∪ shift_v Q) = S(θP ∪ Q)` for `v τ = 0`. DERIVED: `0` the time component; `4` in
`Fin 4` the spacetime dimension. -/
theorem kernF_shift_real (τ : Fin 4) {v : Fin 4 → ℝ} (hv : v τ = 0) {P Q : Mono N}
    (hP : Reg D P) (hQ : Reg D Q) :
    kernF hN (energy0 W D hD) τ (Mono.shift v P) (Mono.shift v Q)
      = kernF hN (energy0 W D hD) τ P Q := by
  unfold kernF
  rw [pairFam_shift_both τ hv]
  exact contSF_energy0_translate_real hN W hD hpos hcube (pairFam τ P Q)
    (fun x => (reg_pairFam hD τ hP hQ x).1) (fun x => (reg_pairFam hD τ hP hQ x).2) v

end Continuity

/-! ## 4. Generic GNS facts: a cross isometry and strong continuity of `opS` -/

section GNSCross

variable {A B : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  (P : Transfer.ReflForm A) (P' : Transfer.ReflForm B)

/-- **A real-linear map between two observable modules, complexified.** DERIVED: no numeral. -/
def cJ (S : A →ₗ[ℝ] B) : GNSHilbert.Pre P →ₗ[ℂ] GNSHilbert.Pre P' where
  toFun z := GNSHilbert.Pre.ofPair P' (S (z : A × A).1) (S (z : A × A).2)
  map_add' z w := by refine GNSHilbert.Pre.ext ?_ ?_ <;> simp [map_add]
  map_smul' c z := by refine GNSHilbert.Pre.ext ?_ ?_ <;> simp [map_add, map_smul]

@[simp] theorem cJ_fst (S : A →ₗ[ℝ] B) (z : GNSHilbert.Pre P) :
    ((cJ P P' S z : GNSHilbert.Pre P') : B × B).1 = S (z : A × A).1 := rfl

@[simp] theorem cJ_snd (S : A →ₗ[ℝ] B) (z : GNSHilbert.Pre P) :
    ((cJ P P' S z : GNSHilbert.Pre P') : B × B).2 = S (z : A × A).2 := rfl

variable {P P'}

/-- **A form-preserving map preserves the complex form.** DERIVED: no numeral. -/
theorem cform_cJ {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y)
    (z w : GNSHilbert.Pre P) :
    cform P'.toPreForm ((cJ P P' S z : GNSHilbert.Pre P') : B × B)
        ((cJ P P' S w : GNSHilbert.Pre P') : B × B)
      = cform P.toPreForm (z : A × A) (w : A × A) := by
  refine ceq ?_ ?_
  · simp only [cform_re, cJ_fst, cJ_snd]
    rw [hS, hS]
  · simp only [cform_im, cJ_fst, cJ_snd]
    rw [hS, hS]

/-- DERIVED: no numeral. -/
theorem norm_cJ {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y)
    (z : GNSHilbert.Pre P) : ‖cJ P P' S z‖ = ‖z‖ := by
  have h : ‖cJ P P' S z‖ * ‖cJ P P' S z‖ = ‖z‖ * ‖z‖ := by
    rw [GNSHilbert.Pre.norm_mul_norm, GNSHilbert.Pre.norm_mul_norm, cJ_fst, cJ_snd, hS, hS]
  rw [← Real.sqrt_mul_self (norm_nonneg (cJ P P' S z)), h, Real.sqrt_mul_self (norm_nonneg z)]

/-- DERIVED: `1` the isometry constant. -/
def cJL {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y) :
    GNSHilbert.Pre P →L[ℂ] GNSHilbert.Pre P' :=
  LinearMap.mkContinuous (cJ P P' S) 1 fun z => by rw [one_mul]; exact (norm_cJ hS z).le

/-- **The isometry between the Hilbert spaces** induced by a form-preserving map. DERIVED: no
numeral. -/
def opJ {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y) :
    GNSHilbert.H P →L[ℂ] GNSHilbert.H P' :=
  (cJL hS).completion

/-- DERIVED: no numeral. -/
theorem opJ_coe {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y)
    (z : GNSHilbert.Pre P) :
    opJ hS (z : GNSHilbert.H P) = ((cJ P P' S z : GNSHilbert.Pre P') : GNSHilbert.H P') :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- **It preserves the inner product.** DERIVED: no numeral. -/
theorem inner_opJ {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y)
    (x y : GNSHilbert.H P) : inner ℂ (opJ hS x) (opJ hS y) = inner ℂ x y := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
      exact isClosed_eq (Continuous.inner ((opJ hS).continuous.comp continuous_fst)
        ((opJ hS).continuous.comp continuous_snd)) (Continuous.inner continuous_fst continuous_snd)
  | ih z w =>
      rw [opJ_coe, opJ_coe, GNSHilbert.inner_coe, GNSHilbert.inner_coe]
      exact cform_cJ hS z w

/-- **It intertwines two transfers** whose steps the map intertwines. DERIVED: no numeral. -/
theorem opJ_opT (Dt : Transfer.TransferData A) (Dt' : Transfer.TransferData B) {S : A →ₗ[ℝ] B}
    (hS : ∀ x y, Dt'.toReflForm.form (S x) (S y) = Dt.toReflForm.form x y)
    (hST : ∀ x, S (Dt.T x) = Dt'.T (S x)) (x : GNSHilbert.H Dt.toReflForm) :
    opJ hS (GNSHilbert.opT Dt x) = GNSHilbert.opT Dt' (opJ hS x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq ((opJ hS).continuous.comp (GNSHilbert.opT Dt).continuous)
        ((GNSHilbert.opT Dt').continuous.comp (opJ hS).continuous)
  | ih z =>
      rw [GNSHilbert.opT_coe, opJ_coe, opJ_coe, GNSHilbert.opT_coe]
      congr 1
      refine GNSHilbert.Pre.ext ?_ ?_
      · simp only [cJ_fst, GNSHilbert.cTL_apply, GNSHilbert.cT_fst]; exact hST _
      · simp only [cJ_snd, GNSHilbert.cTL_apply, GNSHilbert.cT_snd]; exact hST _

/-- **It intertwines two symmetries** that the map intertwines. DERIVED: no numeral. -/
theorem opJ_opS {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y)
    {T : A →ₗ[ℝ] A} {T' : B →ₗ[ℝ] B} (hT : ∀ x y, P.form (T x) (T y) = P.form x y)
    (hT' : ∀ x y, P'.form (T' x) (T' y) = P'.form x y) (h : ∀ x, S (T x) = T' (S x))
    (x : GNSHilbert.H P) : opJ hS (opS hT x) = opS hT' (opJ hS x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq ((opJ hS).continuous.comp (opS hT).continuous)
        ((opS hT').continuous.comp (opJ hS).continuous)
  | ih z =>
      rw [opS_coe, opJ_coe, opJ_coe, opS_coe]
      congr 1
      refine GNSHilbert.Pre.ext ?_ ?_
      · simp only [cJ_fst, cS_fst]; exact h _
      · simp only [cJ_snd, cS_snd]; exact h _

/-- **It maps vacuum to vacuum** when the map does. DERIVED: `0` the imaginary component. -/
theorem opJ_Omega {S : A →ₗ[ℝ] B} (hS : ∀ x y, P'.form (S x) (S y) = P.form x y) {v : A} {v' : B}
    (hv : S v = v') : opJ hS (GNSHilbert.Omega P v) = GNSHilbert.Omega P' v' := by
  unfold GNSHilbert.Omega
  rw [opJ_coe]
  congr 1
  refine GNSHilbert.Pre.ext ?_ ?_
  · simp only [cJ_fst, GNSHilbert.Pre.ofPair_fst]; exact hv
  · simp only [cJ_snd, GNSHilbert.Pre.ofPair_snd]; exact map_zero S

/-- **A form-preserving symmetry preserves the norm.** DERIVED: `2` the square. -/
theorem norm_opS {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y)
    (x : GNSHilbert.H P) : ‖opS hS x‖ = ‖x‖ := by
  have h : ‖opS hS x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_opS]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The displacement of a pre-Hilbert vector**: `‖S z − z‖² = 2(⟨a, a⟩ − ⟨a, S a⟩) +
2(⟨b, b⟩ − ⟨b, S b⟩)` for `z = (a, b)`. DERIVED: `2` the two cross terms; `-1` the coefficient of the
subtracted vector. -/
theorem norm_opS_sub {S : A →ₗ[ℝ] A} (hS : ∀ x y, P.form (S x) (S y) = P.form x y)
    (z : GNSHilbert.Pre P) :
    ‖opS hS (z : GNSHilbert.H P) - z‖
      = Real.sqrt (2 * (P.form (z : A × A).1 (z : A × A).1 - P.form (z : A × A).1 (S (z : A × A).1))
        + 2 * (P.form (z : A × A).2 (z : A × A).2 - P.form (z : A × A).2 (S (z : A × A).2))) := by
  have key : ∀ u, P.form (S u - u) (S u - u) = 2 * (P.form u u - P.form u (S u)) := fun u => by
    have h := P.toPreForm.form_quad u (S u) (-1)
    rw [neg_one_smul, neg_add_eq_sub] at h
    rw [h, hS]
    ring
  rw [opS_coe, ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe,
    ← Real.sqrt_mul_self (norm_nonneg _), GNSHilbert.Pre.norm_mul_norm]
  congr 1
  exact congrArg₂ (· + ·) (key (z : A × A).1) (key (z : A × A).2)

/-- **Strong continuity on the pre-Hilbert space from the form.** If `⟨a, S_i a⟩ → ⟨a, a⟩` for both
components of `z`, then `opS (S_i) z → z`. DERIVED: `0` the limit; `2` as in `norm_opS_sub`. -/
theorem tendsto_opS_coe {ι : Type*} {l : Filter ι} {S : ι → A →ₗ[ℝ] A}
    (hS : ∀ i x y, P.form (S i x) (S i y) = P.form x y) (z : GNSHilbert.Pre P)
    (h1 : Tendsto (fun i => P.form (z : A × A).1 (S i (z : A × A).1)) l
      (𝓝 (P.form (z : A × A).1 (z : A × A).1)))
    (h2 : Tendsto (fun i => P.form (z : A × A).2 (S i (z : A × A).2)) l
      (𝓝 (P.form (z : A × A).2 (z : A × A).2))) :
    Tendsto (fun i => opS (hS i) (z : GNSHilbert.H P)) l (𝓝 (z : GNSHilbert.H P)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun i => 2 * (P.form (z : A × A).1 (z : A × A).1
        - P.form (z : A × A).1 (S i (z : A × A).1))
        + 2 * (P.form (z : A × A).2 (z : A × A).2 - P.form (z : A × A).2 (S i (z : A × A).2))) l
      (𝓝 (2 * (P.form (z : A × A).1 (z : A × A).1 - P.form (z : A × A).1 (z : A × A).1)
        + 2 * (P.form (z : A × A).2 (z : A × A).2 - P.form (z : A × A).2 (z : A × A).2))) :=
    ((tendsto_const_nhds.sub h1).const_mul 2).add ((tendsto_const_nhds.sub h2).const_mul 2)
  rw [sub_self, sub_self, mul_zero, add_zero] at h
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h3
  exact h3.congr fun i => (norm_opS_sub (hS i) z).symm

/-- **Strong continuity on the completion**: a family of isometries converging to the identity on the
dense pre-Hilbert space converges to it everywhere (`ε/3`). DERIVED: `3` the three thirds. -/
theorem tendsto_opS_of_coe {ι : Type*} {l : Filter ι} {S : ι → A →ₗ[ℝ] A}
    (hS : ∀ i x y, P.form (S i x) (S i y) = P.form x y)
    (h : ∀ z : GNSHilbert.Pre P,
      Tendsto (fun i => opS (hS i) (z : GNSHilbert.H P)) l (𝓝 (z : GNSHilbert.H P)))
    (y : GNSHilbert.H P) : Tendsto (fun i => opS (hS i) y) l (𝓝 y) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨z, hz⟩ := Metric.denseRange_iff.mp UniformSpace.Completion.denseRange_coe y (ε / 3)
    (by positivity)
  have hz' := Metric.tendsto_nhds.mp (h z) (ε / 3) (by positivity)
  filter_upwards [hz'] with i hi
  have hd : dist (opS (hS i) y) (opS (hS i) (z : GNSHilbert.H P)) = dist y (z : GNSHilbert.H P) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_opS]
  calc dist (opS (hS i) y) y
      ≤ dist (opS (hS i) y) (opS (hS i) (z : GNSHilbert.H P))
        + dist (opS (hS i) (z : GNSHilbert.H P)) (z : GNSHilbert.H P)
        + dist (z : GNSHilbert.H P) y := dist_triangle4 _ _ _ _
    _ < ε := by rw [hd, dist_comm (z : GNSHilbert.H P) y]; linarith

end GNSCross

/-- **A self-adjoint operator is symmetric.** DERIVED: no numeral. -/
theorem inner_sa {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {a : E →L[ℂ] E} (ha : IsSelfAdjoint a) (x y : E) : inner ℂ (a x) y = inner ℂ x (a y) := by
  have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha) x y
  simpa using h

/-! ## 5. The regular sector of the reconstruction -/

section RegularSector

variable {N : ℕ}

/-- **Regular margin monomials.** DERIVED: no numeral. -/
abbrev RMono (N : ℕ) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) (r : ℝ) : Type :=
  {P : MarginMono N τ r // Reg D P.1}

/-- **The time step on regular monomials.** DERIVED: `1` the unit step; `4` in `Fin 4` the spacetime
dimension. -/
def rTime (hN : N ≠ 0) {D : Set (LField (MassGap.SUN.SU N))} (τ : Fin 4) (m : ℕ) {r : ℝ}
    (P : RMono N D τ r) : RMono N D τ r :=
  ⟨MarginMono.shift hN τ m P.1, reg_shift P.2 (timeVec N m τ 1)⟩

/-- **The empty monomial is regular.** DERIVED: `0` the number of factors. -/
def rEmpty (N : ℕ) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) (r : ℝ) : RMono N D τ r :=
  ⟨emptyMargin N τ r, fun i => i.elim0⟩

/-- **The kernel on regular monomials**: the tree's `kernF`. DERIVED: no numeral. -/
abbrev rKern (hN : N ≠ 0) (Φ : Flow N) {D : Set (LField (MassGap.SUN.SU N))} (τ : Fin 4) {r : ℝ} :
    RMono N D τ r → RMono N D τ r → ℝ :=
  fun P Q => kernF hN Φ τ P.1.1 Q.1.1

/-- **Gram positivity on regular monomials**, from `contSF_gram_nonneg` on their images. DERIVED: `0`
the sign and the coefficient off the image. -/
theorem rGram (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r)
    (s : Finset (RMono N D τ r)) (c : RMono N D τ r → ℝ) :
    0 ≤ ∑ P ∈ s, ∑ Q ∈ s, c P * c Q * rKern hN Φ τ P Q := by
  classical
  let c' : MarginMono N τ r → ℝ := fun P => if h : Reg D P.1 then c ⟨P, h⟩ else 0
  have e : ∀ P : RMono N D τ r, c' P.1 = c P := fun P => dif_pos P.2
  have h := contSF_gram_nonneg hN Φ hB τ hpp (s.map (Function.Embedding.subtype _)) c'
  calc (0 : ℝ) ≤ _ := h
    _ = _ := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun Q _ => ?_
      show c' P.1 * c' Q.1 * kernF hN Φ τ P.1.1 Q.1.1 = c P * c Q * rKern hN Φ τ P Q
      rw [e, e]

/-- DERIVED: no numeral. -/
theorem rTime_iterate (hN : N ≠ 0) {D : Set (LField (MassGap.SUN.SU N))} (τ : Fin 4) (m n : ℕ)
    {r : ℝ} (P : RMono N D τ r) :
    ((rTime hN τ m)^[n] P).1 = (MarginMono.shift hN τ m)^[n] P.1 := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => exact ih (rTime hN τ m P)

/-- DERIVED: no numeral. -/
theorem rIter (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (m : ℕ) (P Q : RMono N D τ r) :
    ∃ C : ℝ, ∀ n : ℕ, |rKern hN Φ τ ((rTime hN τ m)^[n] P) ((rTime hN τ m)^[n] Q)| ≤ C := by
  obtain ⟨C, hC⟩ := kernF_iterate_bound hN Φ hB τ m P.1 Q.1
  refine ⟨C, fun n => ?_⟩
  show |kernF hN Φ τ ((rTime hN τ m)^[n] P).1.1 ((rTime hN τ m)^[n] Q).1.1| ≤ C
  rw [rTime_iterate, rTime_iterate]
  exact hC n

/-- DERIVED: no numeral. -/
theorem rTime_empty (hN : N ≠ 0) (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) (m : ℕ)
    {r : ℝ} : rTime hN τ m (rEmpty N D τ r) = rEmpty N D τ r :=
  Subtype.ext (shift_emptyMargin hN τ m)

/-- DERIVED: `1` the half-step offset. -/
theorem rTime_half (hN : N ≠ 0) {D : Set (LField (MassGap.SUN.SU N))} (τ : Fin 4) (m : ℕ) {r : ℝ}
    (P : RMono N D τ r) : rTime hN τ (m + 1) (rTime hN τ (m + 1) P) = rTime hN τ m P :=
  Subtype.ext (MarginMono.shift_half hN τ m P.1)

/-- **The transfer data of the regular sector at the step `dySpacing N m`**: `gTransfer` with the
tree's kernel on regular margin monomials. DERIVED: no numeral of its own. -/
def rTransfer (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r)
    (m : ℕ) : Transfer.TransferData (RMono N D τ r →₀ ℝ) :=
  gTransfer (rKern hN Φ τ) (fun P Q => kernF_symm hN Φ τ P.1.1 Q.1.1) (rGram hN Φ hB D τ hpp)
    (rTime hN τ m) (fun P Q => kernF_shift hN Φ τ m P.1.1 Q.1.1) (rIter hN Φ hB D τ m)
    (rEmpty N D τ r) (rTime_empty hN D τ m) (kernF_empty hN Φ τ r)

/-- **The regular transfer is positive.** DERIVED: `1` the half-step offset. -/
theorem rTransfer_positive (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) (m : ℕ) :
    GNSHilbert.PositiveTransfer (rTransfer hN Φ hB D τ hpp m) :=
  gPositive (rKern hN Φ τ) (fun P Q => kernF_symm hN Φ τ P.1.1 Q.1.1) (rGram hN Φ hB D τ hpp)
    (rTime hN τ m) (fun P Q => kernF_shift hN Φ τ m P.1.1 Q.1.1) (rIter hN Φ hB D τ m)
    (rEmpty N D τ r) (rTime_empty hN D τ m) (kernF_empty hN Φ τ r)
    (rTime hN τ (m + 1)) (fun P Q => kernF_shift hN Φ τ (m + 1) P.1.1 Q.1.1)
    (fun P => rTime_half hN τ m P)

/-- **The regular sector reconstructs**: complete, unit vacuum, self-adjoint transfer fixing it,
spectrum in `[0, 1]`. DERIVED: `0`, `1` the spectrum interval. -/
theorem rReconstructed (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) (m : ℕ) :
    Reconstructed (rTransfer hN Φ hB D τ hpp m) :=
  reconstructed_of_positive _ (rTransfer_positive hN Φ hB D τ hpp m)

/-- **The Hilbert space of the regular sector.** DERIVED: `0` the reference step. -/
abbrev RH (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) : Type :=
  GNSHilbert.H (rTransfer hN Φ hB D τ hpp 0).toReflForm

/-- **Its step-`m` transfer.** DERIVED: no numeral. -/
def rStep (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) (m : ℕ) :
    RH hN Φ hB D τ hpp →L[ℂ] RH hN Φ hB D τ hpp :=
  GNSHilbert.opT (rTransfer hN Φ hB D τ hpp m)

/-- DERIVED: no numeral. -/
theorem isSelfAdjoint_rStep (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) (m : ℕ) :
    IsSelfAdjoint (rStep hN Φ hB D τ hpp m) :=
  GNSHilbert.isSelfAdjoint_opT _

/-- **Its vacuum.** DERIVED: `0` the reference step. -/
def rVac (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) :
    RH hN Φ hB D τ hpp :=
  GNSHilbert.Omega (rTransfer hN Φ hB D τ hpp 0).toReflForm (rTransfer hN Φ hB D τ hpp 0).vac

/-- **The vacuum is a unit vector**: the regular sector is not zero. DERIVED: `1` the norm. -/
theorem norm_rVac (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) :
    ‖rVac hN Φ hB D τ hpp‖ = 1 :=
  GNSHilbert.norm_Omega_vac _

/-- **The inclusion preserves the form**: the regular kernel is the restriction of `kernF`.
DERIVED: `0` the reference step. -/
theorem form_val (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r)
    (c d : RMono N D τ r →₀ ℝ) :
    (flowTransfer hN Φ hB τ hpp 0).toReflForm.form
        (Finsupp.lmapDomain ℝ ℝ (Subtype.val : RMono N D τ r → MarginMono N τ r) c)
        (Finsupp.lmapDomain ℝ ℝ (Subtype.val : RMono N D τ r → MarginMono N τ r) d)
      = (rTransfer hN Φ hB D τ hpp 0).toReflForm.form c d := by
  show gForm (fun P Q : MarginMono N τ r => kernF hN Φ τ P.1 Q.1)
      (Finsupp.mapDomain Subtype.val c) (Finsupp.mapDomain Subtype.val d)
    = gForm (rKern hN Φ τ) c d
  unfold gForm
  rw [Finsupp.sum_mapDomain_index (fun P => by simp)
    (fun P a₁ a₂ => by simp only [add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr fun P _ => ?_
  exact Finsupp.sum_mapDomain_index (fun Q => by simp) (fun Q b₁ b₂ => by simp only [mul_add, add_mul])

/-- **The isometry of the regular sector into `FlowH`.** DERIVED: no numeral. -/
def J (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) :
    RH hN Φ hB D τ hpp →L[ℂ] FlowH hN Φ hB τ hpp :=
  opJ (form_val hN Φ hB D τ hpp)

/-- **Its adjoint.** DERIVED: no numeral. -/
def Jd (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
    (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r) :
    FlowH hN Φ hB τ hpp →L[ℂ] RH hN Φ hB D τ hpp :=
  ContinuousLinearMap.adjoint (J hN Φ hB D τ hpp)

variable (hN : N ≠ 0) (Φ : Flow N) (hB : UniformBoundF hN Φ)
  (D : Set (LField (MassGap.SUN.SU N))) (τ : Fin 4) {r : ℝ} (hpp : Φ.PosPreserving τ r)

/-- DERIVED: no numeral. -/
theorem inner_J (x y : RH hN Φ hB D τ hpp) :
    inner ℂ (J hN Φ hB D τ hpp x) (J hN Φ hB D τ hpp y) = inner ℂ x y :=
  inner_opJ _ x y

/-- **`Jd J = 1`.** DERIVED: `1` the identity. -/
theorem JdJ (y : RH hN Φ hB D τ hpp) : Jd hN Φ hB D τ hpp (J hN Φ hB D τ hpp y) = y := by
  refine ext_inner_right ℂ fun v => ?_
  rw [Jd, ContinuousLinearMap.adjoint_inner_left]
  exact inner_J hN Φ hB D τ hpp y v

/-- **The range of `J` is orthogonal to the kernel of `Jd`.** DERIVED: `0` the vanishing pairing. -/
theorem inner_J_of_Jd (c : RH hN Φ hB D τ hpp) {q : FlowH hN Φ hB τ hpp}
    (hq : Jd hN Φ hB D τ hpp q = 0) : inner ℂ (J hN Φ hB D τ hpp c) q = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  show inner ℂ c (Jd hN Φ hB D τ hpp q) = 0
  rw [hq, inner_zero_right]

/-- DERIVED: `0` the vanishing image. -/
theorem Jd_sub (q : FlowH hN Φ hB τ hpp) :
    Jd hN Φ hB D τ hpp (q - J hN Φ hB D τ hpp (Jd hN Φ hB D τ hpp q)) = 0 := by
  rw [map_sub, JdJ, sub_self]

/-- **The orthogonal decomposition of the inner product** along `range J ⊕ ker Jd`.
DERIVED: `0` the cross terms. -/
theorem inner_J_add (c c' : RH hN Φ hB D τ hpp) {q q' : FlowH hN Φ hB τ hpp}
    (hq : Jd hN Φ hB D τ hpp q = 0) (hq' : Jd hN Φ hB D τ hpp q' = 0) :
    inner ℂ (J hN Φ hB D τ hpp c + q) (J hN Φ hB D τ hpp c' + q') = inner ℂ c c' + inner ℂ q q' := by
  rw [inner_add_left, inner_add_right, inner_add_right, inner_J, inner_J_of_Jd hN Φ hB D τ hpp c hq',
    inner_eq_zero_symm.mp (inner_J_of_Jd hN Φ hB D τ hpp c' hq), zero_add, add_zero]

/-- **`J` maps the vacuum to the vacuum.** DERIVED: `1` the vacuum coefficient. -/
theorem J_vac : J hN Φ hB D τ hpp (rVac hN Φ hB D τ hpp) = vacT hN Φ hB τ hpp := by
  unfold J rVac vacT
  refine opJ_Omega _ ?_
  show Finsupp.mapDomain Subtype.val (Finsupp.single (rEmpty N D τ r) 1)
    = Finsupp.single (emptyMargin N τ r) 1
  exact Finsupp.mapDomain_single

/-- **`J` intertwines the steps.** DERIVED: no numeral. -/
theorem J_step (m : ℕ) (y : RH hN Φ hB D τ hpp) :
    stepT hN Φ hB τ hpp m (J hN Φ hB D τ hpp y) = J hN Φ hB D τ hpp (rStep hN Φ hB D τ hpp m y) := by
  unfold J rStep stepT
  refine (opJ_opT (rTransfer hN Φ hB D τ hpp m) (flowTransfer hN Φ hB τ hpp m)
    (form_val hN Φ hB D τ hpp) (fun c => ?_) y).symm
  show Finsupp.mapDomain Subtype.val (Finsupp.mapDomain (rTime hN τ m) c)
    = Finsupp.mapDomain (MarginMono.shift hN τ m) (Finsupp.mapDomain Subtype.val c)
  have hf : (Subtype.val : RMono N D τ r → MarginMono N τ r) ∘ rTime hN τ m
      = MarginMono.shift hN τ m ∘ Subtype.val := rfl
  rw [← Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_comp]

/-- **So does its adjoint.** DERIVED: no numeral. -/
theorem Jd_step (m : ℕ) (z : FlowH hN Φ hB τ hpp) :
    Jd hN Φ hB D τ hpp (stepT hN Φ hB τ hpp m z) = rStep hN Φ hB D τ hpp m (Jd hN Φ hB D τ hpp z) := by
  refine ext_inner_right ℂ fun v => ?_
  rw [Jd, ContinuousLinearMap.adjoint_inner_left, inner_sa (isSelfAdjoint_stepT hN Φ hB τ hpp m),
    J_step, ← ContinuousLinearMap.adjoint_inner_left (J hN Φ hB D τ hpp),
    ← inner_sa (isSelfAdjoint_rStep hN Φ hB D τ hpp m)]

end RegularSector

/-! ## 6. Real spatial translations -/

section Spatial

variable {N : ℕ}

/-- **The spatial vectors** for the time direction `τ`: the kernel of the `τ` coordinate.
DERIVED: `4` in `Fin 4` the spacetime dimension. -/
def spatial (τ : Fin 4) : Submodule ℝ (Fin 4 → ℝ) :=
  LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) τ)

/-- DERIVED: `0` the time component. -/
theorem spatial_time {τ : Fin 4} (x : spatial τ) : (x : Fin 4 → ℝ) τ = 0 :=
  LinearMap.mem_ker.mp x.2

/-- DERIVED: `0` the time component. -/
theorem mem_spatial {τ : Fin 4} {v : Fin 4 → ℝ} (hv : v τ = 0) : v ∈ spatial τ :=
  LinearMap.mem_ker.mpr hv

/-- **A real spatial translation of a regular margin monomial.** DERIVED: `0` the time component. -/
def rShift {D : Set (LField (MassGap.SUN.SU N))} {τ : Fin 4} {r : ℝ} (v : Fin 4 → ℝ)
    (hv : v τ = 0) (P : RMono N D τ r) : RMono N D τ r :=
  ⟨⟨Mono.shift v P.1.1, by
    obtain ⟨d, hd, hrd, hP⟩ := P.1.2
    exact ⟨d, hd, hrd, posAt_shift hP hv.symm.le⟩⟩, reg_shift P.2 v⟩

/-- **The linear translation** on combinations of regular monomials. DERIVED: no numeral. -/
def rLin (D : Set (LField (MassGap.SUN.SU N))) {τ : Fin 4} (r : ℝ) (x : spatial τ) :
    (RMono N D τ r →₀ ℝ) →ₗ[ℝ] (RMono N D τ r →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ (rShift (x : Fin 4 → ℝ) (spatial_time x))

variable (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
  (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
  (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
  (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
  (hpp : (energy0 W D hD).PosPreserving τ r)

include hpos hcube

/-- **A real spatial translation preserves the regular form** (`kernF_shift_real`). DERIVED: `0` the
reference step. -/
theorem form_rLin (x : spatial τ) (a b : RMono N D τ r →₀ ℝ) :
    (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm.form (rLin D r x a) (rLin D r x b)
      = (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm.form a b := by
  show gForm (rKern hN (energy0 W D hD) τ)
      (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) a)
      (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) b)
    = gForm (rKern hN (energy0 W D hD) τ) a b
  exact gForm_mapDomain_inv _ _
    (fun (P Q : RMono N D τ r) => kernF_shift_real hN W hD hpos hcube τ (spatial_time x) P.2 Q.2) a b

/-- **The real spatial translation on the regular sector.** DERIVED: no numeral. -/
def rU (x : spatial τ) : RH hN (energy0 W D hD) hB D τ hpp →L[ℂ] RH hN (energy0 W D hD) hB D τ hpp :=
  opS (form_rLin hN W hD hpos hcube hB τ hpp x)

/-- DERIVED: no numeral. -/
theorem inner_rU (x : spatial τ) (y z : RH hN (energy0 W D hD) hB D τ hpp) :
    inner ℂ (rU hN W hD hpos hcube hB τ hpp x y) (rU hN W hD hpos hcube hB τ hpp x z)
      = inner ℂ y z :=
  inner_opS _ y z

/-- **The group law.** DERIVED: no numeral. -/
theorem rU_add (x y : spatial τ) :
    rU hN W hD hpos hcube hB τ hpp (x + y)
      = rU hN W hD hpos hcube hB τ hpp x * rU hN W hD hpos hcube hB τ hpp y := by
  unfold rU
  refine (opS_mul _ _ _ fun c => ?_).symm
  show Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x))
      (Finsupp.mapDomain (rShift (y : Fin 4 → ℝ) (spatial_time y)) c)
    = Finsupp.mapDomain (rShift ((x + y : spatial τ) : Fin 4 → ℝ) (spatial_time (x + y))) c
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext P
  refine Subtype.ext (Subtype.ext ?_)
  show Mono.shift (x : Fin 4 → ℝ) (Mono.shift (y : Fin 4 → ℝ) P.1.1)
    = Mono.shift ((x : Fin 4 → ℝ) + y) P.1.1
  rw [Mono.shift_shift, add_comm]

/-- **The zero translation is the identity.** DERIVED: `0` the zero vector; `1` the identity. -/
theorem rU_zero : rU hN W hD hpos hcube hB τ hpp 0 = 1 := by
  unfold rU
  refine opS_eq_one _ fun c => ?_
  show Finsupp.mapDomain (rShift ((0 : spatial τ) : Fin 4 → ℝ) (spatial_time (0 : spatial τ))) c = c
  have h : rShift ((0 : spatial τ) : Fin 4 → ℝ) (spatial_time (0 : spatial τ))
      = (id : RMono N D τ r → RMono N D τ r) :=
    funext fun P => Subtype.ext (Subtype.ext (Mono.shift_zero P.1.1))
  rw [h, Finsupp.mapDomain_id]

/-- **It fixes the vacuum.** DERIVED: `1` the vacuum coefficient; `0` the number of factors. -/
theorem rU_vac (x : spatial τ) :
    rU hN W hD hpos hcube hB τ hpp x (rVac hN (energy0 W D hD) hB D τ hpp)
      = rVac hN (energy0 W D hD) hB D τ hpp := by
  unfold rU rVac
  refine opS_Omega _ ?_
  show Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) (Finsupp.single (rEmpty N D τ r) 1)
    = Finsupp.single (rEmpty N D τ r) 1
  rw [Finsupp.mapDomain_single]
  congr 1
  exact Subtype.ext (Subtype.ext (congrArg (Sigma.mk 0) (funext fun i => i.elim0)))

/-- **It commutes with every step.** DERIVED: `1` the unit step. -/
theorem commute_rU_rStep (x : spatial τ) (m : ℕ) :
    Commute (rU hN W hD hpos hcube hB τ hpp x) (rStep hN (energy0 W D hD) hB D τ hpp m) := by
  unfold rU rStep
  exact opS_commute_opT (rTransfer hN (energy0 W D hD) hB D τ hpp m)
    (form_rLin hN W hD hpos hcube hB τ hpp x) fun c => by
      show Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x))
          (Finsupp.mapDomain (rTime hN τ m) c)
        = Finsupp.mapDomain (rTime hN τ m)
          (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) c)
      rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      congr 1
      funext P
      refine Subtype.ext (Subtype.ext ?_)
      show Mono.shift (x : Fin 4 → ℝ) (Mono.shift (timeVec N m τ 1) P.1.1)
        = Mono.shift (timeVec N m τ 1) (Mono.shift (x : Fin 4 → ℝ) P.1.1)
      rw [Mono.shift_shift, Mono.shift_shift, add_comm]

/-- DERIVED: no numeral. -/
theorem rU_rStep_apply (x : spatial τ) (m : ℕ) (y : RH hN (energy0 W D hD) hB D τ hpp) :
    rU hN W hD hpos hcube hB τ hpp x (rStep hN (energy0 W D hD) hB D τ hpp m y)
      = rStep hN (energy0 W D hD) hB D τ hpp m (rU hN W hD hpos hcube hB τ hpp x y) := by
  have h := congrArg (fun F => F y) (commute_rU_rStep hN W hD hpos hcube hB τ hpp x m).eq
  simp only [ContinuousLinearMap.mul_apply] at h
  exact h

/-- **The form against the translate tends to the form** as the translation tends to `0`
(`tendsto_kernF_shift` in every term of the finite double sum). DERIVED: `0` the zero translation and
the reference step. -/
theorem tendsto_form_rLin (a : RMono N D τ r →₀ ℝ) :
    Tendsto (fun x : spatial τ =>
        (rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm.form a (rLin D r x a)) (𝓝 0)
      (𝓝 ((rTransfer hN (energy0 W D hD) hB D τ hpp 0).toReflForm.form a a)) := by
  show Tendsto (fun x : spatial τ => gForm (rKern hN (energy0 W D hD) τ) a
      (Finsupp.mapDomain (rShift (x : Fin 4 → ℝ) (spatial_time x)) a)) (𝓝 0)
    (𝓝 (gForm (rKern hN (energy0 W D hD) τ) a a))
  simp only [gForm_mapDomain_right]
  unfold gForm
  simp only [Finsupp.sum]
  refine tendsto_finset_sum _ fun P _ => tendsto_finset_sum _ fun Q _ => tendsto_const_nhds.mul ?_
  exact (tendsto_kernF_shift hN W hD hpos hcube τ P.2 Q.2).comp
    (continuous_subtype_val.tendsto' (0 : spatial τ) 0 rfl)

/-- **Strong continuity at the identity.** DERIVED: `0` the zero translation. -/
theorem tendsto_rU (y : RH hN (energy0 W D hD) hB D τ hpp) :
    Tendsto (fun x : spatial τ => rU hN W hD hpos hcube hB τ hpp x y) (𝓝 0) (𝓝 y) :=
  tendsto_opS_of_coe (fun x => form_rLin hN W hD hpos hcube hB τ hpp x)
    (fun z => tendsto_opS_coe (fun x => form_rLin hN W hD hpos hcube hB τ hpp x) z
      (tendsto_form_rLin hN W hD hpos hcube hB τ hpp _)
      (tendsto_form_rLin hN W hD hpos hcube hB τ hpp _)) y

/-- **Strong continuity**: `x ↦ rU x y` is continuous on `spatial τ`. DERIVED: no numeral. -/
theorem continuous_rU (y : RH hN (energy0 W D hD) hB D τ hpp) :
    Continuous (fun x : spatial τ => rU hN W hD hpos hcube hB τ hpp x y) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have h1 : Tendsto (fun x : spatial τ => x - x0) (𝓝 x0) (𝓝 0) :=
    (continuous_id.sub continuous_const).tendsto' x0 0 (sub_self x0)
  have h2 := ((rU hN W hD hpos hcube hB τ hpp x0).continuous.tendsto y).comp
    ((tendsto_rU hN W hD hpos hcube hB τ hpp y).comp h1)
  unfold ContinuousAt
  refine h2.congr fun x => ?_
  show rU hN W hD hpos hcube hB τ hpp x0 (rU hN W hD hpos hcube hB τ hpp (x - x0) y)
    = rU hN W hD hpos hcube hB τ hpp x y
  rw [← ContinuousLinearMap.mul_apply, ← rU_add, show x0 + (x - x0) = x by abel]

/-- **The real translation on `FlowH`**: `J rU Jd` on the regular sector `V = range J`, the identity
on `V⊥`. DERIVED: `1` the identity. -/
def realT (x : spatial τ) : FlowH hN (energy0 W D hD) hB τ hpp →L[ℂ] FlowH hN (energy0 W D hD) hB τ hpp :=
  (J hN (energy0 W D hD) hB D τ hpp).comp ((rU hN W hD hpos hcube hB τ hpp x).comp
      (Jd hN (energy0 W D hD) hB D τ hpp))
    + (1 - (J hN (energy0 W D hD) hB D τ hpp).comp (Jd hN (energy0 W D hD) hB D τ hpp))

/-- DERIVED: no numeral. -/
theorem realT_apply (x : spatial τ) (z : FlowH hN (energy0 W D hD) hB τ hpp) :
    realT hN W hD hpos hcube hB τ hpp x z
      = J hN (energy0 W D hD) hB D τ hpp (rU hN W hD hpos hcube hB τ hpp x
          (Jd hN (energy0 W D hD) hB D τ hpp z))
        + (z - J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp z)) := rfl

/-- **The group law on `FlowH`.** DERIVED: no numeral. -/
theorem realT_add (x y : spatial τ) :
    realT hN W hD hpos hcube hB τ hpp (x + y)
      = realT hN W hD hpos hcube hB τ hpp x * realT hN W hD hpos hcube hB τ hpp y := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.mul_apply, realT_apply, map_add, map_sub, JdJ, sub_self, add_zero,
    rU_add]
  abel

/-- DERIVED: `0` the zero vector; `1` the identity. -/
theorem realT_zero : realT hN W hD hpos hcube hB τ hpp 0 = 1 := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [realT_apply, rU_zero, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]
  abel

/-- **It preserves the inner product.** DERIVED: no numeral. -/
theorem inner_realT (x : spatial τ) (z w : FlowH hN (energy0 W D hD) hB τ hpp) :
    inner ℂ (realT hN W hD hpos hcube hB τ hpp x z) (realT hN W hD hpos hcube hB τ hpp x w)
      = inner ℂ z w := by
  have hz : z = J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp z)
      + (z - J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp z)) := by abel
  have hw : w = J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp w)
      + (w - J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp w)) := by abel
  have hrhs : inner ℂ z w = inner ℂ (Jd hN (energy0 W D hD) hB D τ hpp z)
      (Jd hN (energy0 W D hD) hB D τ hpp w)
      + inner ℂ (z - J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp z))
        (w - J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp w)) := by
    conv_lhs => rw [hz, hw]
    exact inner_J_add hN (energy0 W D hD) hB D τ hpp _ _ (Jd_sub hN (energy0 W D hD) hB D τ hpp z)
      (Jd_sub hN (energy0 W D hD) hB D τ hpp w)
  rw [realT_apply, realT_apply, inner_J_add hN (energy0 W D hD) hB D τ hpp _ _
    (Jd_sub hN (energy0 W D hD) hB D τ hpp z) (Jd_sub hN (energy0 W D hD) hB D τ hpp w),
    inner_rU, hrhs]

/-- **It fixes the vacuum.** DERIVED: `0` the vanishing remainder. -/
theorem realT_vac (x : spatial τ) :
    realT hN W hD hpos hcube hB τ hpp x (vacT hN (energy0 W D hD) hB τ hpp)
      = vacT hN (energy0 W D hD) hB τ hpp := by
  rw [realT_apply, ← J_vac hN (energy0 W D hD) hB D τ hpp, JdJ, rU_vac, sub_self, add_zero]

/-- **On `V⊥` it is the identity.** DERIVED: `0` the vanishing image. -/
theorem realT_orth (x : spatial τ) {z : FlowH hN (energy0 W D hD) hB τ hpp}
    (hz : Jd hN (energy0 W D hD) hB D τ hpp z = 0) : realT hN W hD hpos hcube hB τ hpp x z = z := by
  rw [realT_apply, hz]
  simp only [map_zero, sub_zero, zero_add]

/-- **It commutes with every time step.** DERIVED: no numeral. -/
theorem commute_realT_stepT (x : spatial τ) (m : ℕ) :
    Commute (realT hN W hD hpos hcube hB τ hpp x) (stepT hN (energy0 W D hD) hB τ hpp m) := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, realT_apply, realT_apply,
    Jd_step, rU_rStep_apply, ← J_step, ← J_step, map_add, map_sub]

/-- **It commutes with every time translation** `timeT t`. DERIVED: `0` the reference step. -/
theorem commute_realT_timeT (x : spatial τ) (t : ℝ) :
    Commute (realT hN W hD hpos hcube hB τ hpp x) (timeT hN (energy0 W D hD) hB τ hpp t) :=
  (Commute.cfc_real (commute_realT_stepT hN W hD hpos hcube hB τ hpp x 0).symm
    (fun s : ℝ => s ^ (t / dySpacing N 0))).symm

/-- **Strong continuity on `FlowH`.** DERIVED: no numeral. -/
theorem continuous_realT (z : FlowH hN (energy0 W D hD) hB τ hpp) :
    Continuous (fun x : spatial τ => realT hN W hD hpos hcube hB τ hpp x z) := by
  show Continuous (fun x : spatial τ => J hN (energy0 W D hD) hB D τ hpp
      (rU hN W hD hpos hcube hB τ hpp x (Jd hN (energy0 W D hD) hB D τ hpp z))
    + (z - J hN (energy0 W D hD) hB D τ hpp (Jd hN (energy0 W D hD) hB D τ hpp z)))
  exact ((J hN (energy0 W D hD) hB D τ hpp).continuous.comp
    (continuous_rU hN W hD hpos hcube hB τ hpp _)).add continuous_const

/-- **`J` carries the dyadic real translation to `spT`.** DERIVED: `0` the time component. -/
theorem J_rU_dyadic (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0)
    (y : RH hN (energy0 W D hD) hB D τ hpp) :
    J hN (energy0 W D hD) hB D τ hpp
        (rU hN W hD hpos hcube hB τ hpp ⟨site (dySpacing N m) n, mem_spatial (site_time_zero _ hn)⟩ y)
      = spT hN (energy0 W D hD) hB τ hpp m n hn (J hN (energy0 W D hD) hB D τ hpp y) := by
  unfold J rU spT
  refine opJ_opS _ _ _ (fun c => ?_) y
  show Finsupp.mapDomain Subtype.val
      (Finsupp.mapDomain (rShift (site (dySpacing N m) n) (site_time_zero _ hn)) c)
    = Finsupp.mapDomain (spShift τ m n hn) (Finsupp.mapDomain Subtype.val c)
  have hf : (Subtype.val : RMono N D τ r → MarginMono N τ r)
      ∘ rShift (site (dySpacing N m) n) (site_time_zero _ hn) = spShift τ m n hn ∘ Subtype.val := rfl
  rw [← Finsupp.mapDomain_comp, hf, Finsupp.mapDomain_comp]

/-- **Agreement with `ShellMomentum.spT` on the regular sector** at every dyadic spatial vector.
DERIVED: `0` the time component and the vanishing remainder. -/
theorem realT_dyadic (m : ℕ) {n : Fin 4 → ℤ} (hn : n τ = 0)
    (y : RH hN (energy0 W D hD) hB D τ hpp) :
    realT hN W hD hpos hcube hB τ hpp ⟨site (dySpacing N m) n, mem_spatial (site_time_zero _ hn)⟩
        (J hN (energy0 W D hD) hB D τ hpp y)
      = spT hN (energy0 W D hD) hB τ hpp m n hn (J hN (energy0 W D hD) hB D τ hpp y) := by
  rw [realT_apply, JdJ, sub_self, add_zero]
  exact J_rU_dyadic hN W hD hpos hcube hB τ hpp m hn y

end Spatial

/-! ## 7. Unitary representations, positive definiteness, the tree's instance -/

section Rep

/-- **A strongly continuous unitary representation** of an additive topological group on a complex
inner product space. DERIVED: `0` the identity element; `1` the identity operator. -/
structure UnitaryRep (G : Type*) [AddCommGroup G] [TopologicalSpace G] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The operators. -/
  U : G → E →L[ℂ] E
  map_zero : U 0 = 1
  map_add : ∀ x y, U (x + y) = U x * U y
  inner_U : ∀ x z w, inner ℂ (U x z) (U x w) = inner ℂ z w
  cont : ∀ z, Continuous fun x => U x z

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]

/-- **Positive definiteness**: `Σᵢⱼ c̄ᵢ cⱼ ⟪u, U(xⱼ − xᵢ) u⟫ = ‖Σⱼ cⱼ U(xⱼ) u‖²` as an inner product.
DERIVED: `-1` the sign in the translation difference. -/
theorem UnitaryRep.posDef (R : UnitaryRep G E) (u : E) {ι : Type*} (s : Finset ι) (x : ι → G)
    (c : ι → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, starRingEnd ℂ (c i) * c j * inner ℂ u (R.U (x j - x i) u)
      = inner ℂ (∑ i ∈ s, c i • R.U (x i) u) (∑ j ∈ s, c j • R.U (x j) u) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  have e : R.U (x j) = R.U (x i) * R.U (x j - x i) := by
    rw [← R.map_add]
    congr 1
    abel
  rw [e, ContinuousLinearMap.mul_apply, R.inner_U]
  ring

/-- **The real part of the positive-definite sum is non-negative.** DERIVED: `0` the sign; `-1` the sign in the translation difference. -/
theorem UnitaryRep.posDef_re_nonneg (R : UnitaryRep G E) (u : E) {ι : Type*} (s : Finset ι)
    (x : ι → G) (c : ι → ℂ) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, starRingEnd ℂ (c i) * c j * inner ℂ u (R.U (x j - x i) u)).re := by
  rw [R.posDef u s x c]
  exact inner_self_nonneg (𝕜 := ℂ)

variable {N : ℕ}

/-- **The tree's real translations as a unitary representation of `spatial τ` on `FlowH`.**
DERIVED: no numeral. -/
def realRep (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U) (hcube : ∀ O ∈ D, CubeMomentBound hN W O)
    (hB : UniformBoundF hN (energy0 W D hD)) (τ : Fin 4) {r : ℝ}
    (hpp : (energy0 W D hD).PosPreserving τ r) :
    UnitaryRep (spatial τ) (FlowH hN (energy0 W D hD) hB τ hpp) where
  U := realT hN W hD hpos hcube hB τ hpp
  map_zero := realT_zero hN W hD hpos hcube hB τ hpp
  map_add := realT_add hN W hD hpos hcube hB τ hpp
  inner_U := inner_realT hN W hD hpos hcube hB τ hpp
  cont := continuous_realT hN W hD hpos hcube hB τ hpp

/-- **Real spatial data on `observerOSDataS`**: the real translations of `spatial τ`, for
`ShellMomentum`'s zero-momentum projection. The fixed space of `realT` is the fixed space of `rU`
inside `V` together with all of `V⊥`, because `realT` is the identity on `V⊥` and is not the physical
translation there. The zero-momentum projection `ShellMomentum.P0` of this data therefore contains every
component in `V⊥`, whether or not the physical translation fixes it. `clay_zero_momentum_sector` for
this data speaks about that sector. DERIVED: `0` the excluded colour count, the reference step and the
time component; `1` the top of `ρ` and the unit step; `-1` the sign of the inverse translation; `4` in
`Fin 4` the spacetime dimension. -/
def observerRealSpatial (hN : N ≠ 0) (W : ConfFlow N) {D : Set (LField (MassGap.SUN.SU N))}
    (hD : ∀ (τ : Fin 4) (O : LField (MassGap.SUN.SU N)), O.refl τ ∈ D ↔ O ∈ D)
    (hpos : ∀ O ∈ D, ∀ U, 0 ≤ O.1 U)
    (hcube : ∀ O ∈ D, ObserverEnergyBox.CubeMomentBound hN W O)
    {O : LField (MassGap.SUN.SU N)} (hO : O ∈ D) (h : ObserverOSGrowth.UnitCubeExpBound hN W O)
    (τ : Fin 4) {r : ℝ} (hphys : (ObserverOS.energy0 W D hD).PhysRange r) (m0 : ℕ) {L : ℝ}
    (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hg : TransferGap.GapAt (ObserverEnergyReductionsN.transferN hN (ObserverOS.energy0 W D hD)
      (ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube) τ hphys m0) ρ)
    (hNT : FlowConnectedNonzero hN (ObserverOS.energy0 W D hD) τ r) :
    SpatialData (observerOSDataS hN W hD hpos hcube hO h τ hphys m0 hL hρ0 hρ1 hg hNT) :=
  let hB := ObserverOS.uniformBoundF_energy0 hN W D hD hpos hcube
  let hpp := Flow.posPreserving_of_physRange hN (ObserverOS.energy0 W D hD) hphys τ
  { ι := spatial τ
    U := fun x => realT hN W hD hpos hcube hB τ hpp x
    Uinv := fun x => realT hN W hD hpos hcube hB τ hpp (-x)
    inner_U := fun x z w => inner_realT hN W hD hpos hcube hB τ hpp x z w
    U_Uinv := fun x => by
      have h1 := realT_add hN W hD hpos hcube hB τ hpp x (-x)
      rw [add_neg_cancel, realT_zero] at h1
      exact h1.symm
    Uinv_U := fun x => by
      have h1 := realT_add hN W hD hpos hcube hB τ hpp (-x) x
      rw [neg_add_cancel, realT_zero] at h1
      exact h1.symm
    commute := fun x => commute_realT_timeT hN W hD hpos hcube hB τ hpp x 1
    U_vac := fun x => realT_vac hN W hD hpos hcube hB τ hpp x }

end Rep

/-! ## 8. Load test: the plane wave of a free particle -/

section Load

/-- **The phase `p · x`** read on a spatial vector. DERIVED: `4` in `Fin 4` the spacetime
dimension. -/
def phase {τ : Fin 4} (p : Fin 4 → ℝ) (x : spatial τ) : ℝ := ∑ j, p j * (x : Fin 4 → ℝ) j

/-- DERIVED: no numeral. -/
theorem phase_add {τ : Fin 4} (p : Fin 4 → ℝ) (x y : spatial τ) :
    phase p (x + y) = phase p x + phase p y := by
  simp only [phase, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- DERIVED: `0` the zero vector. -/
theorem phase_zero {τ : Fin 4} (p : Fin 4 → ℝ) : phase p (0 : spatial τ) = 0 := by
  simp [phase]

/-- **The translations of a free one-particle state of momentum `p`**, as argued, not derived: for a
state of momentum `p`, `U x = e^{i p·x}` on `ℂ`.
DERIVED: `1` the identity operator; the imaginary unit is the generator's phase. -/
def planeWave (τ : Fin 4) (p : Fin 4 → ℝ) : UnitaryRep (spatial τ) ℂ where
  U x := Complex.exp ((phase p x : ℂ) * Complex.I) • (1 : ℂ →L[ℂ] ℂ)
  map_zero := by simp [phase_zero]
  map_add x y := by
    refine ContinuousLinearMap.ext fun z => ?_
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul, phase_add, Complex.ofReal_add, add_mul,
      Complex.exp_add]
    ring
  inner_U x z w := by
    have he : starRingEnd ℂ (Complex.exp ((phase p x : ℂ) * Complex.I))
        * Complex.exp ((phase p x : ℂ) * Complex.I) = 1 := by
      rw [Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
      simp
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_left,
      inner_smul_right]
    linear_combination (inner ℂ z w) * he
  cont z := by
    have hφ : Continuous (phase (τ := τ) p) :=
      continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp
        continuous_subtype_val)
    show Continuous fun x : spatial τ => Complex.exp ((phase p x : ℂ) * Complex.I) * z
    exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hφ).mul
      continuous_const)).mul continuous_const

/-- **The plane wave is not the trivial representation** when `p` has a non-zero spatial component
`j ≠ τ`: at the half-period vector `(π / p_j) e_j` the phase is `π` and `U = −1`. DERIVED: `1` the
identity and the unit vector's entry; `-1` the value of `e^{iπ}`. CHOSEN: the half-period vector; every
vector whose phase is not a multiple of `2π` serves. -/
theorem planeWave_nontrivial {τ : Fin 4} (p : Fin 4 → ℝ) {j : Fin 4} (hj : j ≠ τ) (hp : p j ≠ 0) :
    ∃ x : spatial τ, (planeWave τ p).U x ≠ 1 := by
  have hmem : (Real.pi / p j) • (Pi.single j 1 : Fin 4 → ℝ) ∈ spatial τ :=
    mem_spatial (by simp [Ne.symm hj])
  refine ⟨⟨_, hmem⟩, fun h => ?_⟩
  have hph : phase p (⟨_, hmem⟩ : spatial τ) = Real.pi := by
    unfold phase
    rw [Finset.sum_eq_single j]
    · show p j * (((Real.pi / p j) • (Pi.single j 1 : Fin 4 → ℝ)) j) = Real.pi
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      field_simp
    · intro k _ hk
      show p k * (((Real.pi / p j) • (Pi.single j 1 : Fin 4 → ℝ)) k) = 0
      rw [Pi.smul_apply, Pi.single_eq_of_ne hk, smul_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have h1 := congrArg (fun F : ℂ →L[ℂ] ℂ => F 1) h
  simp only [planeWave, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul,
    mul_one, hph, Complex.exp_pi_mul_I] at h1
  norm_num at h1

end Load

end

end MassGap.ShellTranslate

#print axioms MassGap.ShellTranslate.dist_reflR_le
#print axioms MassGap.ShellTranslate.uniformContinuous_reflR
#print axioms MassGap.ShellTranslate.uniformContinuous_translate
#print axioms MassGap.ShellTranslate.uniformContinuous_reflect
#print axioms MassGap.ShellTranslate.reg_shift
#print axioms MassGap.ShellTranslate.reg_pairFam
#print axioms MassGap.ShellTranslate.pairFam_shift_right
#print axioms MassGap.ShellTranslate.pairFam_shift_both
#print axioms MassGap.ShellTranslate.tendsto_contSF_translate
#print axioms MassGap.ShellTranslate.continuous_contSF_translate
#print axioms MassGap.ShellTranslate.tendsto_kernF_shift
#print axioms MassGap.ShellTranslate.kernF_shift_real
#print axioms MassGap.ShellTranslate.cform_cJ
#print axioms MassGap.ShellTranslate.norm_cJ
#print axioms MassGap.ShellTranslate.opJ_coe
#print axioms MassGap.ShellTranslate.inner_opJ
#print axioms MassGap.ShellTranslate.opJ_opT
#print axioms MassGap.ShellTranslate.opJ_opS
#print axioms MassGap.ShellTranslate.opJ_Omega
#print axioms MassGap.ShellTranslate.norm_opS
#print axioms MassGap.ShellTranslate.norm_opS_sub
#print axioms MassGap.ShellTranslate.tendsto_opS_coe
#print axioms MassGap.ShellTranslate.tendsto_opS_of_coe
#print axioms MassGap.ShellTranslate.inner_sa
#print axioms MassGap.ShellTranslate.rGram
#print axioms MassGap.ShellTranslate.rTime_iterate
#print axioms MassGap.ShellTranslate.rIter
#print axioms MassGap.ShellTranslate.rTime_empty
#print axioms MassGap.ShellTranslate.rTime_half
#print axioms MassGap.ShellTranslate.rTransfer
#print axioms MassGap.ShellTranslate.rTransfer_positive
#print axioms MassGap.ShellTranslate.isSelfAdjoint_rStep
#print axioms MassGap.ShellTranslate.rReconstructed
#print axioms MassGap.ShellTranslate.norm_rVac
#print axioms MassGap.ShellTranslate.form_val
#print axioms MassGap.ShellTranslate.inner_J
#print axioms MassGap.ShellTranslate.JdJ
#print axioms MassGap.ShellTranslate.inner_J_of_Jd
#print axioms MassGap.ShellTranslate.Jd_sub
#print axioms MassGap.ShellTranslate.inner_J_add
#print axioms MassGap.ShellTranslate.J_vac
#print axioms MassGap.ShellTranslate.J_step
#print axioms MassGap.ShellTranslate.Jd_step
#print axioms MassGap.ShellTranslate.spatial_time
#print axioms MassGap.ShellTranslate.mem_spatial
#print axioms MassGap.ShellTranslate.form_rLin
#print axioms MassGap.ShellTranslate.inner_rU
#print axioms MassGap.ShellTranslate.rU_add
#print axioms MassGap.ShellTranslate.rU_zero
#print axioms MassGap.ShellTranslate.rU_vac
#print axioms MassGap.ShellTranslate.commute_rU_rStep
#print axioms MassGap.ShellTranslate.rU_rStep_apply
#print axioms MassGap.ShellTranslate.tendsto_form_rLin
#print axioms MassGap.ShellTranslate.tendsto_rU
#print axioms MassGap.ShellTranslate.continuous_rU
#print axioms MassGap.ShellTranslate.realT_apply
#print axioms MassGap.ShellTranslate.realT_add
#print axioms MassGap.ShellTranslate.realT_zero
#print axioms MassGap.ShellTranslate.inner_realT
#print axioms MassGap.ShellTranslate.realT_vac
#print axioms MassGap.ShellTranslate.realT_orth
#print axioms MassGap.ShellTranslate.commute_realT_stepT
#print axioms MassGap.ShellTranslate.commute_realT_timeT
#print axioms MassGap.ShellTranslate.continuous_realT
#print axioms MassGap.ShellTranslate.J_rU_dyadic
#print axioms MassGap.ShellTranslate.realT_dyadic
#print axioms MassGap.ShellTranslate.UnitaryRep.posDef
#print axioms MassGap.ShellTranslate.UnitaryRep.posDef_re_nonneg
#print axioms MassGap.ShellTranslate.realRep
#print axioms MassGap.ShellTranslate.observerRealSpatial
#print axioms MassGap.ShellTranslate.phase_add
#print axioms MassGap.ShellTranslate.phase_zero
#print axioms MassGap.ShellTranslate.planeWave
#print axioms MassGap.ShellTranslate.planeWave_nontrivial
